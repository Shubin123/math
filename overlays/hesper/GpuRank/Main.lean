import Hesper

/-!
# gpu-rank: the rank of integer matrices modulo a prime p < 2^16, on the GPU

Input: a binary file of records, each `nr nc p` as little-endian u32 followed by the nr·nc entries
of the matrix, row by row, as little-endian u32 already reduced modulo p. Output: one line per
record, `RANK rank milliseconds`, where the time covers upload, elimination and readback (not process
start-up or WebGPU initialisation, which is printed once to stderr).

The elimination runs entirely on the GPU, column by column, with no readback in between: the
current rank r and column c live in a storage buffer, and each column is five dispatches recorded
into one command encoder:
1. `find_pivot`: atomicMin over the rows i ≥ r with A[i][c] ≠ 0;
2. `swap_rows`:  swap the pivot row with row r (columns ≥ c; the columns < c of rows ≥ r are 0);
3. `factors`:    f[i] = A[i][c] / A[r][c] for the rows i > r;
4. `eliminate`:  A[i][j] -= f[i]·A[r][j] for i > r, j ≥ c;
5. `advance`:    r += 1 if a pivot was found; c += 1.
p < 2^16 keeps every product below 2^32, since WGSL has no 64-bit integers. A rank modulo p is at
most the rank over ℚ, and equals it unless p divides the matrix's invariant factors; the caller
compares primes, and against an exact CPU rank.
-/

open Hesper.WebGPU

namespace GpuRank

def wgsl : String := "
@group(0) @binding(0) var<storage, read_write> A: array<u32>;
@group(0) @binding(1) var<storage, read_write> st: array<u32>;
@group(0) @binding(2) var<storage, read_write> piv: array<atomic<u32>>;
@group(0) @binding(3) var<storage, read_write> f: array<u32>;

const NONE: u32 = 0xffffffffu;

fn powmod(a: u32, e: u32, p: u32) -> u32 {
  var r: u32 = 1u;
  var b: u32 = a % p;
  var k: u32 = e;
  loop {
    if (k == 0u) { break; }
    if ((k & 1u) == 1u) { r = (r * b) % p; }
    b = (b * b) % p;
    k = k >> 1u;
  }
  return r;
}

@compute @workgroup_size(256)
fn find_pivot(@builtin(global_invocation_id) g: vec3<u32>) {
  let r = st[0]; let c = st[1]; let nr = st[4]; let nc = st[5];
  let i = g.x;
  if (c >= nc || r >= nr || i < r || i >= nr) { return; }
  if (A[i * nc + c] != 0u) { atomicMin(&piv[0], i); }
}

@compute @workgroup_size(256)
fn swap_rows(@builtin(global_invocation_id) g: vec3<u32>) {
  let r = st[0]; let c = st[1]; let nc = st[5];
  let pr = atomicLoad(&piv[0]);
  if (pr == NONE || pr == r) { return; }
  let j = g.x + c;
  if (j >= nc) { return; }
  let t = A[pr * nc + j];
  A[pr * nc + j] = A[r * nc + j];
  A[r * nc + j] = t;
}

@compute @workgroup_size(256)
fn factors(@builtin(global_invocation_id) g: vec3<u32>) {
  let r = st[0]; let c = st[1]; let nr = st[4]; let nc = st[5]; let p = st[6];
  let pr = atomicLoad(&piv[0]);
  if (pr == NONE) { return; }
  let i = g.x;
  if (i <= r || i >= nr) { return; }
  let inv = powmod(A[r * nc + c], p - 2u, p);
  f[i] = (A[i * nc + c] * inv) % p;
}

@compute @workgroup_size(16, 16)
fn eliminate(@builtin(global_invocation_id) g: vec3<u32>) {
  let r = st[0]; let c = st[1]; let nr = st[4]; let nc = st[5]; let p = st[6];
  let pr = atomicLoad(&piv[0]);
  if (pr == NONE) { return; }
  let j = g.x + c;
  let i = g.y + r + 1u;
  if (j >= nc || i >= nr) { return; }
  let fi = f[i];
  if (fi == 0u) { return; }
  let v = A[i * nc + j];
  A[i * nc + j] = (v + p - (fi * A[r * nc + j]) % p) % p;
}

@compute @workgroup_size(1)
fn advance() {
  let pr = atomicLoad(&piv[0]);
  if (st[1] < st[5]) {
    if (pr != NONE) { st[0] = st[0] + 1u; }
    st[1] = st[1] + 1u;
  }
  atomicStore(&piv[0], NONE);
}
"

structure Kernels where
  layout : BindGroupLayout
  findPivot : ComputePipeline
  swapRows : ComputePipeline
  factors : ComputePipeline
  eliminate : ComputePipeline
  advance : ComputePipeline

def build (device : Device) : IO Kernels := do
  let sm ← createShaderModule device wgsl
  let entries : Array BindGroupLayoutEntry := (#[0, 1, 2, 3] : Array UInt32).map fun i =>
    { binding := i, visibility := .compute, bindingType := .buffer false }
  let layout ← createBindGroupLayout device entries
  let mk (entry : String) : IO ComputePipeline :=
    createComputePipeline device { shaderModule := sm, entryPoint := entry, bindGroupLayout := layout }
  return { layout, findPivot := ← mk "find_pivot", swapRows := ← mk "swap_rows",
           factors := ← mk "factors", eliminate := ← mk "eliminate", advance := ← mk "advance" }

def u32Bytes (xs : Array UInt32) : ByteArray := Id.run do
  let mut b := ByteArray.empty
  for x in xs do
    b := (((b.push (x &&& 0xff).toUInt8).push ((x >>> 8) &&& 0xff).toUInt8).push
      ((x >>> 16) &&& 0xff).toUInt8).push ((x >>> 24) &&& 0xff).toUInt8
  return b

def readU32 (b : ByteArray) (o : Nat) : UInt32 :=
  b[o]!.toUInt32 ||| (b[o + 1]!.toUInt32 <<< 8) ||| (b[o + 2]!.toUInt32 <<< 16) ||| (b[o + 3]!.toUInt32 <<< 24)

def ceilDiv (a b : Nat) : Nat := (a + b - 1) / b

/-- The rank modulo p of the nr × nc matrix whose entries, reduced modulo p, are `data`. -/
def rank (device : Device) (k : Kernels) (nr nc p : Nat) (data : ByteArray) (flushEvery : Nat := 64) :
    IO Nat := do
  if nr == 0 || nc == 0 then return 0
  let mkBuf (bytes : Nat) : IO Buffer :=
    createBuffer device { size := bytes.toUSize, usage := [.storage, .copyDst, .copySrc], mappedAtCreation := false }
  let a ← mkBuf (4 * nr * nc)
  writeBuffer device a 0 data
  let st ← mkBuf 32
  writeBuffer device st 0 (u32Bytes #[0, 0, 0, 0, nr.toUInt32, nc.toUInt32, p.toUInt32, 0])
  let piv ← mkBuf 16
  writeBuffer device piv 0 (u32Bytes #[0xFFFFFFFF, 0, 0, 0])
  let f ← mkBuf (4 * nr)
  let bg ← createBindGroup device k.layout #[
    { binding := 0, buffer := a, offset := 0, size := 0 },
    { binding := 1, buffer := st, offset := 0, size := 0 },
    { binding := 2, buffer := piv, offset := 0, size := 0 },
    { binding := 3, buffer := f, offset := 0, size := 0 }]
  let mut enc ← createCommandEncoder device
  for c in [0:nc] do
    recordDispatch enc k.findPivot bg (ceilDiv nr 256).toUInt32 1 1
    recordDispatch enc k.swapRows bg (ceilDiv (nc - c) 256).toUInt32 1 1
    recordDispatch enc k.factors bg (ceilDiv nr 256).toUInt32 1 1
    recordDispatch enc k.eliminate bg (ceilDiv (nc - c) 16).toUInt32 (ceilDiv nr 16).toUInt32 1
    recordDispatch enc k.advance bg 1 1 1
    -- Dawn on Metal drops inter-pass barriers in very large encoders (Hesper's `flushBatch`).
    if (c + 1) % flushEvery == 0 then
      submitNoWait device enc
      enc ← createCommandEncoder device
  submitAndWait device enc
  let out ← mapBufferRead device st 0 32
  return (readU32 out 0).toNat

end GpuRank

def main (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
    -- Hesper logs every buffer operation unless told otherwise (HESPER_LOG_LEVEL unset).
    Hesper.Logging.setVerbose false
    let t0 ← IO.monoNanosNow
    let inst ← Hesper.init
    let device ← getDevice inst
    let k ← GpuRank.build device
    let t1 ← IO.monoNanosNow
    IO.eprintln s!"init {(t1 - t0) / 1000000} ms"
    let bytes ← IO.FS.readBinFile path
    let mut off := 0
    while off + 12 ≤ bytes.size do
      let nr := (GpuRank.readU32 bytes off).toNat
      let nc := (GpuRank.readU32 bytes (off + 4)).toNat
      let p := (GpuRank.readU32 bytes (off + 8)).toNat
      let len := 4 * nr * nc
      let data := bytes.extract (off + 12) (off + 12 + len)
      let s ← IO.monoNanosNow
      let r ← GpuRank.rank device k nr nc p data
      let e ← IO.monoNanosNow
      IO.println s!"RANK {r} {(e - s).toFloat / 1000000.0}"
      off := off + 12 + len
    return 0
  | _ =>
    IO.eprintln "usage: gpu-rank <batch-file>"
    return 1
