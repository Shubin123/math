import Hesper

/-!
# gpu-sat: a memcomputing-style dynamical 3-SAT solver on the GPU (incomplete: finds solutions only)

The dynamics are those of `3sat_v2.py` of github.com/jkgoodworks/lightspeed-3-SAT-solver (after
arXiv:2011.06551), with its tuned constants: variables v ∈ [-1,1], per clause a short memory
x_s ∈ [0,1] and a long memory x_l ∈ [1, 10^4·M], C_m = ½·min_i (1 − q_i·v_{var_i}), and

  dx_s = β(x_s + ε)·sin³(C_m − γ),  dx_l = α(C_m − δ),
  dv_k = Σ_{(m,i) ∋ k} q_{m,i}·C_m·(x_l·x_s + [i = argmin]·(1 + ζ·x_l)(1 − x_s)),

Euler steps with momentum μ on v, an adaptive step dt = clamp(1.185345 / max|derivative|, 2^-7,
10^5) recomputed every 10 steps, and α, β, γ, ζ, μ adapted from the mean of C_m and the step count.
It can find satisfying assignments; it can never show that a formula is unsatisfiable.

Parallelization, as in lightspeed: one GPU thread per clause, then one per variable. One change:
WGSL has no floating-point atomics, so instead of scattering clause contributions to variables
with atomicAdd (lightspeed, CUDA), each variable gathers them through a precomputed occurrence list
(CSR). Max-reductions use atomicMax on the bit patterns of non-negative floats, whose order as u32
is the order of the floats; the mean of C_m is a two-level workgroup reduction.

Input file (little-endian, written by /math/sat-kernel/gpu_sat.py): u32 N, M, maxSteps, checkEvery and
the byte lengths of three blobs, then the blobs: the initialised prefixes of the buffers iv
(litVar[3M] | occOff[N+1] | occ[3M]), cf (q[3M] | x_s = 0.5 | x_l = 1) and vf (v0 | v0). Clauses
of fewer than 3 literals are padded by repeating a literal. Output: the line
`RESULT SAT|UNKNOWN steps ms` (time after set-up), and the final v (N f32) in the output file.
-/

open Hesper.WebGPU

namespace GpuSat

/-- The WGSL source, with the sizes of the instance filled in for the `__..__` placeholders. -/
def wgslTemplate : String := "
const N: u32 = __N__u;
const M: u32 = __M__u;
const W: u32 = __W__u;
// iv (u32): litVar[3M] | occOff[N+1] | occ[3M] | mi[M]
const O_OFF: u32 = __3_M__u;
const O_OCC: u32 = __3_M_N_1__u;
const O_MI: u32 = __6_M_N_1__u;
// cf (f32): q[3M] | xs[M] | xl[M] | C[M] | A[M] | B[M] | dxs[M] | dxl[M]
const O_XS: u32 = __3_M__u;
const O_XL: u32 = __4_M__u;
const O_C: u32 = __5_M__u;
const O_A: u32 = __6_M__u;
const O_B: u32 = __7_M__u;
const O_DXS: u32 = __8_M__u;
const O_DXL: u32 = __9_M__u;
// vf (f32): v[N] | vprev[N] | dv[N];  pf (f32): dt alpha beta gamma delta eps zeta mu | partial[W]
const O_VP: u32 = __N__u;
const O_DV: u32 = __2_N__u;
const O_PART: u32 = 16u;

const ALPHA0: f32 = 7.264952; const BETA0: f32 = 19.706215; const GAMMA0: f32 = 0.290741;
const DELTA0: f32 = 0.190131; const EPS: f32 = 0.008693; const ZETA0: f32 = 0.143817;
const DT_FACTOR: f32 = 1.185345; const AVG_FACTOR: f32 = 2.075337; const AVG_THRESHOLD: f32 = 0.161275;
const GAMMA_DECAY: f32 = 0.229501; const MU_MIN: f32 = 0.634689; const MU_GROWTH: f32 = 0.2268;
const MU_MAX: f32 = 0.946342;

@group(0) @binding(0) var<storage, read_write> iv: array<u32>;
@group(0) @binding(1) var<storage, read_write> cf: array<f32>;
@group(0) @binding(2) var<storage, read_write> vf: array<f32>;
@group(0) @binding(3) var<storage, read_write> pf: array<f32>;
@group(0) @binding(4) var<storage, read_write> st: array<u32>;
@group(0) @binding(5) var<storage, read_write> at: array<atomic<u32>>;

var<workgroup> red: array<f32, 256>;

fn amax(slot: u32, x: f32) { atomicMax(&at[slot], bitcast<u32>(abs(x))); }

// 1. per clause: C_m, argmin, and the workgroup sums of C_m
@compute @workgroup_size(256)
fn clause_c(@builtin(global_invocation_id) g: vec3<u32>, @builtin(local_invocation_id) l: vec3<u32>,
            @builtin(workgroup_id) w: vec3<u32>) {
  let m = g.x;
  var c: f32 = 0.0;
  if (m < M) {
    var best: f32 = 3.0;
    var bi: u32 = 0u;
    for (var i: u32 = 0u; i < 3u; i = i + 1u) {
      let t = 1.0 - cf[3u * m + i] * vf[iv[3u * m + i]];
      if (t < best) { best = t; bi = i; }
    }
    c = 0.5 * best;
    cf[O_C + m] = c;
    iv[O_MI + m] = bi;
  }
  red[l.x] = c;
  workgroupBarrier();
  for (var s: u32 = 128u; s > 0u; s = s >> 1u) {
    if (l.x < s) { red[l.x] = red[l.x] + red[l.x + s]; }
    workgroupBarrier();
  }
  if (l.x == 0u) { pf[O_PART + w.x] = red[0]; }
}

// 2. one workgroup: the mean of C_m, and the adapted parameters
@compute @workgroup_size(256)
fn params(@builtin(local_invocation_id) l: vec3<u32>) {
  var s: f32 = 0.0;
  for (var j: u32 = l.x; j < W; j = j + 256u) { s = s + pf[O_PART + j]; }
  red[l.x] = s;
  workgroupBarrier();
  for (var k: u32 = 128u; k > 0u; k = k >> 1u) {
    if (l.x < k) { red[l.x] = red[l.x] + red[l.x + k]; }
    workgroupBarrier();
  }
  if (l.x == 0u) {
    let cmean = red[0] / f32(M);
    let sf = min(1.0, f32(st[0]) / 5000.0);
    let avg = 1.0 + max(0.0, min(2.0, AVG_FACTOR * (cmean - AVG_THRESHOLD)));
    pf[1] = ALPHA0 * sqrt(avg);
    pf[2] = BETA0 * avg;
    pf[3] = GAMMA0 * (1.0 - GAMMA_DECAY * sf);
    pf[4] = DELTA0;
    pf[5] = EPS;
    pf[6] = ZETA0 * (1.0 + sf);
    pf[7] = min(MU_MAX, MU_MIN + MU_GROWTH * sf);
  }
}

// 3. per clause: memory derivatives, and the two factors each literal passes to its variable
@compute @workgroup_size(256)
fn clause_d(@builtin(global_invocation_id) g: vec3<u32>) {
  let m = g.x;
  if (m >= M) { return; }
  let c = cf[O_C + m];
  let xs = cf[O_XS + m];
  let xl = cf[O_XL + m];
  let sn = sin(c - pf[3]);
  let dxs = pf[2] * (xs + pf[5]) * sn * sn * sn;
  let dxl = pf[1] * (c - pf[4]);
  cf[O_DXS + m] = dxs;
  cf[O_DXL + m] = dxl;
  cf[O_A + m] = c * xl * xs;
  cf[O_B + m] = c * (1.0 + pf[6] * xl) * (1.0 - xs);
  amax(0u, dxs);
  amax(0u, dxl);
}

// 4. per variable: gather the clause contributions (no float atomics in WGSL)
@compute @workgroup_size(256)
fn var_d(@builtin(global_invocation_id) g: vec3<u32>) {
  let k = g.x;
  if (k >= N) { return; }
  var d: f32 = 0.0;
  for (var j: u32 = iv[O_OFF + k]; j < iv[O_OFF + k + 1u]; j = j + 1u) {
    let e = iv[O_OCC + j];
    let m = e / 3u;
    var f = cf[O_A + m];
    if (iv[O_MI + m] == e % 3u) { f = f + cf[O_B + m]; }
    d = d + cf[e] * f;
  }
  vf[O_DV + k] = d;
  amax(0u, d);
}

// 5. one thread: dt every 10 steps from the largest derivative, then the next step
@compute @workgroup_size(1)
fn step_dt() {
  if (st[0] % 10u == 0u) {
    let md = bitcast<f32>(atomicLoad(&at[0]));
    if (md > 0.0) { pf[0] = clamp(DT_FACTOR / md, 0.0078125, 100000.0); } else { pf[0] = 100000.0; }
  }
  atomicStore(&at[0], 0u);
  st[0] = st[0] + 1u;
}

// 6. per variable: Euler step with momentum, clamped to [-1, 1]
@compute @workgroup_size(256)
fn update_v(@builtin(global_invocation_id) g: vec3<u32>) {
  let k = g.x;
  if (k >= N) { return; }
  let v = vf[k];
  vf[k] = clamp(v + vf[O_DV + k] * pf[0] + pf[7] * (v - vf[O_VP + k]), -1.0, 1.0);
  vf[O_VP + k] = v;
}

// 7. per clause: memory updates
@compute @workgroup_size(256)
fn update_x(@builtin(global_invocation_id) g: vec3<u32>) {
  let m = g.x;
  if (m >= M) { return; }
  cf[O_XS + m] = clamp(cf[O_XS + m] + cf[O_DXS + m] * pf[0], 0.0, 1.0);
  cf[O_XL + m] = clamp(cf[O_XL + m] + cf[O_DXL + m] * pf[0], 1.0, 10000.0 * f32(M));
}

// check: clauses not satisfied by the assignment v > 0
@compute @workgroup_size(256)
fn count_unsat(@builtin(global_invocation_id) g: vec3<u32>) {
  let m = g.x;
  if (m >= M) { return; }
  for (var i: u32 = 0u; i < 3u; i = i + 1u) {
    if (cf[3u * m + i] * vf[iv[3u * m + i]] > 0.0) { return; }
  }
  atomicAdd(&at[1], 1u);
}
"

def wgsl (N M W : Nat) : String :=
  wgslTemplate
    |>.replace "__N__" (toString (N))
    |>.replace "__M__" (toString (M))
    |>.replace "__W__" (toString (W))
    |>.replace "__3_M__" (toString (3 * M))
    |>.replace "__3_M_N_1__" (toString (3 * M + N + 1))
    |>.replace "__6_M_N_1__" (toString (6 * M + N + 1))
    |>.replace "__4_M__" (toString (4 * M))
    |>.replace "__5_M__" (toString (5 * M))
    |>.replace "__6_M__" (toString (6 * M))
    |>.replace "__7_M__" (toString (7 * M))
    |>.replace "__8_M__" (toString (8 * M))
    |>.replace "__9_M__" (toString (9 * M))
    |>.replace "__2_N__" (toString (2 * N))

def u32Bytes (xs : Array UInt32) : ByteArray := Id.run do
  let mut b := ByteArray.empty
  for x in xs do
    b := (((b.push (x &&& 0xff).toUInt8).push ((x >>> 8) &&& 0xff).toUInt8).push
      ((x >>> 16) &&& 0xff).toUInt8).push ((x >>> 24) &&& 0xff).toUInt8
  return b

def readU32 (b : ByteArray) (o : Nat) : UInt32 :=
  b[o]!.toUInt32 ||| (b[o + 1]!.toUInt32 <<< 8) ||| (b[o + 2]!.toUInt32 <<< 16) ||| (b[o + 3]!.toUInt32 <<< 24)

def ceilDiv (a b : Nat) : Nat := (a + b - 1) / b

end GpuSat

open GpuSat in
def main (args : List String) : IO UInt32 := do
  match args with
  | [inPath, outPath] =>
    Hesper.Logging.setVerbose false
    let bytes ← IO.FS.readBinFile inPath
    let h (i : Nat) : Nat := (readU32 bytes (4 * i)).toNat
    let N := h 0; let M := h 1; let maxSteps := h 2; let checkEvery := h 3
    let oIv := 28; let oCf := oIv + h 4; let oVf := oCf + h 5; let oEnd := oVf + h 6
    let W := ceilDiv M 256
    let t0 ← IO.monoNanosNow
    let inst ← Hesper.init
    let device ← getDevice inst
    let name ← try mtlDeviceName device catch _ => pure "?"
    IO.eprintln s!"device: {name}"
    let sm ← createShaderModule device (wgsl N M W)
    let entries : Array BindGroupLayoutEntry := (#[0, 1, 2, 3, 4, 5] : Array UInt32).map fun i =>
      { binding := i, visibility := .compute, bindingType := .buffer false }
    let layout ← createBindGroupLayout device entries
    let mk (e : String) : IO ComputePipeline :=
      createComputePipeline device { shaderModule := sm, entryPoint := e, bindGroupLayout := layout }
    let pC ← mk "clause_c"; let pP ← mk "params"; let pD ← mk "clause_d"; let pV ← mk "var_d"
    let pT ← mk "step_dt"; let pUV ← mk "update_v"; let pUX ← mk "update_x"; let pU ← mk "count_unsat"
    -- WebGPU buffers start zeroed; the input holds the initialised prefixes (see gpu_sat.py).
    let mkBuf (n : Nat) (init : ByteArray) : IO Buffer := do
      let b ← createBuffer device { size := n.toUSize, usage := [.storage, .copyDst, .copySrc], mappedAtCreation := false }
      if init.size > 0 then writeBuffer device b 0 init
      return b
    let iv ← mkBuf (4 * (7 * M + N + 1)) (bytes.extract oIv oCf)
    let cf ← mkBuf (4 * 10 * M) (bytes.extract oCf oVf)
    let vf ← mkBuf (4 * 3 * N) (bytes.extract oVf oEnd)
    let pf ← mkBuf (4 * (16 + W)) ⟨#[0x00, 0x00, 0x80, 0x3f]⟩  -- dt = 1.0
    let st ← mkBuf 16 ByteArray.empty
    let atm ← mkBuf 16 ByteArray.empty
    let bg ← createBindGroup device layout #[
      { binding := 0, buffer := iv, offset := 0, size := 0 }, { binding := 1, buffer := cf, offset := 0, size := 0 },
      { binding := 2, buffer := vf, offset := 0, size := 0 }, { binding := 3, buffer := pf, offset := 0, size := 0 },
      { binding := 4, buffer := st, offset := 0, size := 0 }, { binding := 5, buffer := atm, offset := 0, size := 0 }]
    let gm := (ceilDiv M 256).toUInt32
    let gn := (ceilDiv N 256).toUInt32
    let t1 ← IO.monoNanosNow
    IO.eprintln s!"setup {(t1 - t0) / 1000000} ms"
    let mut steps := 0
    let mut solved := false
    while steps < maxSteps && !solved do
      let enc ← createCommandEncoder device
      for _ in [0:checkEvery] do
        recordDispatch enc pC bg gm 1 1
        recordDispatch enc pP bg 1 1 1
        recordDispatch enc pD bg gm 1 1
        recordDispatch enc pV bg gn 1 1
        recordDispatch enc pT bg 1 1 1
        recordDispatch enc pUV bg gn 1 1
        recordDispatch enc pUX bg gm 1 1
      recordDispatch enc pU bg gm 1 1
      submitAndWait device enc
      steps := steps + checkEvery
      let a ← mapBufferRead device atm 0 8
      if readU32 a 4 == 0 then
        solved := true
      else
        writeBuffer device atm 4 (u32Bytes #[0])
    let t2 ← IO.monoNanosNow
    let v ← mapBufferRead device vf 0 (4 * N).toUSize
    IO.FS.writeBinFile outPath v
    IO.println s!"RESULT {if solved then "SAT" else "UNKNOWN"} {steps} {(t2 - t1).toFloat / 1000000.0}"
    return 0
  | _ =>
    IO.eprintln "usage: gpu-sat <input.bin> <output-v.bin>"
    return 1
