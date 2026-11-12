# 3-SAT time bounds: Lean-checked results, a search for better "pieces", and a GPU rank kernel

This repository builds on two upstream projects, pinned to exact commits and patched by
`setup.sh`:

- [`anthropics/formal-math`](https://github.com/anthropics/formal-math) (`eth/`): a Lean 4
  formalization of a 2^O(n·log log n/√log n) algorithm for #k-SAT, which refutes the Exponential
  Time Hypothesis;
- [`Verilean/hesper`](https://github.com/Verilean/hesper): GPU programming from Lean 4 through
  WebGPU (Metal on macOS).

[`openai/math`](https://github.com/openai/math) was read for comparison; nothing in it is built.

It adds three things.

1. **Lean: the sharpest 3-SAT bounds the formalization supports**, stated in
   `formal-math/eth/BestThreeSat.lean` and proved with only Lean's three standard axioms. One
   Turing machine decides every 3-CNF with n variables and m clauses within
   - c·(n+2)^c·2^(c·min{m/√log m, n·log log n/√log n}) steps;
   - c·2^(c·n·log log n/√log n) steps;
   - c·2^(c·n/(log n)^α) steps, for **every** α < 1/2 (the upstream proofs state only α = 3/19);
   - c·2^(c·n/√log n) steps on formulas with at most D·n clauses, for every D;
   - c·2^(δn) steps, for every δ > 0.

   `PolyTime` states polynomial-time 3-SAT, which is open (it is equivalent to P = NP); a proved
   sanity check shows it would refute ETH. `PolyChallenge.lean` holds it with `sorry`.
2. **`piece-search/`: a search for better pieces.** Lean's Theorem A (`GeneralPieces.thmRunningTime`)
   turns *pieces with parameter ρ* (integer decompositions of the bit-string SWAP tensor into
   terms with small row rank × column rank) into #k-SAT in 2^O(n·log log n/(log n)^log₂(1/ρ)).
   The paper's pieces have ρ = 1/√2. The search scores candidate gadgets by exact ranks.
3. **`gpu-rank`: the search's exact-rank step on the GPU**, written with Hesper, and benchmarks
   showing whether it is faster. It is, from matrix size 1024 up: scoring a gadget at k = 6 takes
   12 s instead of 116 s (9.7×), with identical ranks (see below).
4. **`sat-kernel/`: SAT solvers as the search kernel.** The fastest solvers of SAT Competition
   2025, built from the competition archives, find pieces through a SAT encoding, and a GPU solver
   (`gpu-sat`, Hesper) runs the parallel dynamics of
   [lightspeed-3-SAT-solver](https://github.com/jkgoodworks/lightspeed-3-SAT-solver). A race
   between the two returns the first verified answer (see [the SAT kernel](#the-sat-kernel)).

## What has and has not been found

- **No polynomial-time algorithm.** Nothing here comes close: every bound above is
  superpolynomial, and `PolyTime` is unproved.
- **The pieces framework has a ceiling.** SWAP on λ-bit strings has rank 4^λ, rank is
  subadditive, and there are only polynomially many pieces, so some piece has row rank at least
  4^λ/poly(λ). That forces ρ ≥ 1/2 (the definition in `AppRunningTimeStatement.lean` assumes it),
  so the best this route could ever give is 2^O(n·log log n/log n). This argument is not
  formalized here.
- **No gadget beats the baseline asymptotically.** The paper's singlet decomposition (SWAP = I − S)
  scores ρ̂ = 0.711, 0.758, 0.764 at k = 3, 4, 5. A random search over 20,000 three-term gadgets with
  entries in [−1, 1] found nothing below 0.9255 at k = 3. Small-k scores also understate the
  asymptotic value (the singlet's rises from 0.50 at k = 1 to 0.79 at k = 6), so a candidate must
  beat the baseline at every k it is scored at.
- **The SAT kernel beats the singlet at one size, but not under tensor powers.** On 2-bit strings,
  three pieces of rank 6 × 6 sum to SWAP (the singlet's grouping needs 7 × 7); the solver finds
  them in 0.2 s and they pass an exact check. Raised to tensor powers they lose: ρ̂ = 0.646, 0.738,
  0.818 at λ = 2, 4, 6 against the singlet's 0.702, 0.758, 0.787.
- **The fastest SAT solvers are exponential, as expected.** On random 3-SAT at ratio 4.26 all three
  go from under 0.3 s at n = 200 to timing out (120 s) on 3 of 5 instances at n = 350.

## Reproducing everything

Tested on an Apple M4 (macOS 27, arm64), by running these steps in a fresh clone. Needs about 15 GB of disk.

### Prerequisites

- [elan](https://github.com/leanprover/elan) (Lean's toolchain manager; the pinned Lean versions are
  fetched automatically): `curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none`
- git, a C++17 compiler, CMake ≥ 3.16 and Ninja (`brew install cmake ninja`), for Hesper's Dawn
- Python ≥ 3.10

### 1. Fetch and patch the upstream projects

```sh
git clone https://github.com/Shubin123/math.git && cd math
./setup.sh
```

This clones `formal-math` and `hesper` at the commits pinned in `setup.sh`, copies `overlays/` over
them, applies `patches/`, and creates `piece-search/.venv`. Add `--with-openai-math` for a sparse
checkout of `openai/math` to read.

### 2. Check the Lean proofs (about 9 minutes on 10 cores, including the Mathlib download)

```sh
scripts/verify-lean.sh
```

The last lines must be:

```
'MainResults.ethIsFalse' depends on axioms: [propext, Classical.choice, Quot.sound]
'MainResults.mainTheorem' depends on axioms: [propext, Classical.choice, Quot.sound]
'BestThreeSat.statement_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'BestThreeSat.polyTime_ethIsFalse' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The build prints two `declaration uses 'sorry'` warnings, both from upstream `Challenge.lean`,
which states the two upstream theorems without proofs on purpose. To see the open target:
`cd formal-math/eth && lake build PolyChallenge` (one `sorry`).

What to read: `formal-math/eth/BestThreeSat.lean` (the statements; it imports only upstream
`MainResults.lean`, which imports only Mathlib), then `proof/maintheorem/BestRate/Main.lean` (the
proofs).

### 3. Build the GPU kernel (about 5 minutes the first time, mostly Dawn)

```sh
scripts/build-gpu.sh
```

On macOS 27, Lean's bundled linker cannot read the SDK's library stubs (they list the `arm64e.x1`
architecture), so the script links against the newest installed SDK that does not, through the
`HESPER_MACOS_SDK` variable that `patches/hesper.patch` adds. Override it by setting the variable
yourself.

### 4. Run the benchmarks and the search

```sh
scripts/bench.sh                                   # writes piece-search/bench_results.md
cd piece-search
.venv/bin/python search.py --samples 20000 --terms 3 --bound 1 --seed 1
```

### 5. The SAT kernel (solvers build in about 15 seconds)

```sh
sat-kernel/build_solvers.sh                        # AE-Kissat-MAB, Kissat-public, CaDiCaL-SC2025
cd sat-kernel
PY=../piece-search/.venv/bin/python
$PY scaling.py --timeout 120                       # ~25 min; writes scaling_results.md
$PY kernel_bench.py --timeout 900                  # ~30 min; writes kernel_results.md
$PY gpu_bench.py --timeout 120                     # ~15 min; needs gpu-sat; writes gpu_results.md
$PY score_found.py                                 # ~1 min; needs gpu-rank; writes found_results.md
```

`scripts/build-gpu.sh` (step 3) also builds `gpu-sat`.

## Does Hesper speed things up?

Only the rank computations, and only for large matrices. Nothing here speeds up Lean: proof
checking runs on the CPU.

The CPU baseline is [FLINT](https://flintlib.org) (Fast Library for Number Theory), a heavily
optimized C library for exact arithmetic, through its Python binding `python-flint`, on one core.
Its `nmod_mat` type gives the exact rank modulo a prime; `fmpz_mat` gives the exact rank over the
integers.

Measured on an Apple M4 (10-core GPU) with `scripts/bench.sh`; the full output is
[`piece-search/bench_results.md`](piece-search/bench_results.md).

**End to end: scoring the singlet gadget** (every group, rowwise and colwise, two primes each):

| k | matrix size | CPU, primes < 2^62 (default) | CPU, same primes as GPU | GPU (Hesper) | GPU vs CPU, same primes | same ranks |
|---|---|---|---|---|---|---|
| 3 | 64 | 0.01 s | 0.01 s | 0.12 s | 0.06× (slower) | yes |
| 4 | 256 | 0.16 s | 0.16 s | 0.15 s | 1.06× | yes |
| 5 | 1024 | 4.16 s | 3.70 s | 0.47 s | **7.8×** | yes |
| 6 | 4096 | 130.1 s | 116.0 s | 12.0 s | **9.7×** | yes |

**One rank modulo 65521** (same matrix, same prime; GPU time includes upload and readback):

| matrix | n | rank | flint rank | GPU | speedup | speedup counting flint's matrix build |
|---|---|---|---|---|---|---|
| search matrix, k=5, rowwise | 1024 | 106 | 24.0 ms | 18.3 ms | 1.3× | 7.2× |
| search matrix, k=5, colwise | 1024 | 376 | 62.8 ms | 12.9 ms | 4.9× | 13.1× |
| search matrix, k=6, rowwise | 4096 | 694 | 1693 ms | 348 ms | 4.9× | 9.7× |
| search matrix, k=6, colwise | 4096 | 694 | 2091 ms | 354 ms | 5.9× | 10.6× |
| random, rank 128 | 512 | 128 | 8.7 ms | 5.7 ms | 1.5× | 6.6× |
| random, full rank | 1024 | 1024 | 90.7 ms | 30.2 ms | 3.0× | 6.9× |
| random, full rank | 2048 | 2048 | 705 ms | 228 ms | 3.1× | 5.2× |
| random, full rank | 4096 | 4096 | 4772 ms | 2041 ms | 2.3× | 3.3× |

How to read this:

- Every GPU rank equals flint's at the same prime, and end-to-end scores match on all three paths.
- The GPU wins from matrix size 1024 up; at 64 and 256 it loses, because starting the process and
  WebGPU (about 0.1–0.3 s) costs more than the whole CPU computation.
- `gpu vs cpu16` is the like-for-like comparison (same primes). `gpu vs cpu` compares with the
  default CPU path, which uses primes below 2^62 and so is slower still.
- The GPU works modulo primes below 2^16, because WGSL has no 64-bit integers. A rank modulo p can
  only be too low, never too high, and only when p divides the matrix's invariant factors. So
  `pieces.score` takes the larger rank over two primes on either backend, and a candidate that
  looks good should be rechecked with `score(..., exact=True)` (exact rank over the integers).

## The SAT kernel

### Which solver is fastest

Best solvers of the last three SAT Competitions (sequential main track, PAR-2 score, lower is
better): 2025 from the official [results slides](https://satcompetition.github.io/2025/satcomp25slides.pdf);
2023 and 2024 from sorting the score columns of the
[2023](https://satcompetition.github.io/2023/results.html) and
[2024](https://satcompetition.github.io/2024/results.html) results pages. The benchmark sets differ
by year, so the solved counts do not compare across years:

| Year | Overall | Satisfiable | Unsatisfiable | Parallel |
|---|---|---|---|---|
| 2023 | SBVA-CaDiCaL (284 solved) | SBVA-CaDiCaL | KissatMabProp | PRS |
| 2024 | kissat-sc2024 (306) | kissat-sc2024 | kissat-sc2024 | painless (Saoudi et al.) |
| 2025 | **AE-Kissat-MAB** (327) | AE-Kissat-MAB | CaDiCaL-SC2025 | MallobSat |

All are CDCL solvers of the Kissat/CaDiCaL family. `sat-kernel/build_solvers.sh` builds the top
three of 2025 (AE-Kissat-MAB, Kissat-public, CaDiCaL-SC2025) from the competition archives, checked
by SHA-256. On the hard piece instance below, AE-Kissat-MAB was also the fastest (563 s against
896 s for Kissat-public; CaDiCaL timed out at 900 s), so it is the CPU engine of the kernel.

MallobSat, the 2025 parallel winner, is described in
[Schreiber, Rigi-Luperti and Biere, SAT 2025](https://drops.dagstuhl.de/storage/00lipics/lipics-vol341-sat2025/LIPIcs.SAT.2025.27/LIPIcs.SAT.2025.27.pdf):
pure CDCL threads with light diversification and clause sharing, preprocessing once next to the
search, on up to 3072 CPU cores. It notes that GPU attempts at CDCL reached speedups of about 1.5
because SAT solving's program flow is irregular.

### Pieces as SAT (`encode_pieces.py`, `kernel_bench.py`)

Pieces A_1 … A_J summing to SWAP, each given by explicit row-wise and column-wise factorizations
with entries in {−1, 0, 1} (the shape of Lean's `FactorsThrough`), become CNF through product gates
and totalizers. Every SAT answer is checked by exact ranks; every λ = 1 case with a known answer
comes out right. At λ = 2 with 3 pieces (timeout 900 s):

| shapes (R_j, C_j) | largest rank product | result |
|---|---|---|
| (16,1), (8,8), (1,16): the singlet's shape | 64 | all solvers time out |
| (6,6), (6,6), (6,6) | 36 | found in 0.2 s, verified |
| (5,5), (5,5), (6,6) | 36 | found in 0.2 s, verified |
| (8,4), (4,8), (6,6) | 36 | found by AE-Kissat-MAB in 563 s, verified |
| (5,5), (5,5), (5,5) | 25 | impossible by rank, but no solver proves it in 900 s |

The last row is CDCL's known blind spot: rank arguments have no short resolution proofs.
`score_found.py` then scores the found decompositions as gadgets on 2-bit blocks under tensor
powers, with the GPU rank kernel; the table is in `sat-kernel/found_results.md`.

### The GPU solver (`gpu-sat`, `gpu_sat.py`)

[lightspeed-3-SAT-solver](https://github.com/jkgoodworks/lightspeed-3-SAT-solver) integrates a
memcomputing-style dynamical system (after arXiv:2011.06551): continuous variables in [−1, 1], a
short and a long memory per clause, Euler steps with momentum and an adaptive time step. It
parallelizes one CUDA thread per clause (scattering to variables with float `atomicAdd`) and one
per variable. `hesper/GpuSat/Main.lean` runs the same dynamics, with lightspeed's tuned constants,
in WGSL through Hesper. WGSL has no float atomics, so each variable gathers its clause terms
through an occurrence list instead, which also makes runs deterministic. The GPU trajectory matches
a NumPy copy of the dynamics (`gpu_sat.reference`) to 1.4×10⁻⁶ after 20 steps, with identical signs.

Two things to know about these dynamics:

- **They are incomplete.** They can find a satisfying assignment, never prove that none exists.
- **Lightspeed's benchmark instances are easy.** Its generator plants a solution and flips each
  literal away from it with probability 0.35, so majority voting alone satisfies 98.5% of the
  clauses. On uniform random 3-SAT the dynamics solve ratio 4.0 up to n = 100,000, but at 4.2 they
  fail from n = 10,000 on; they also fail on every piece instance tried, which CDCL solves in
  under 0.1 s.

### Does the GPU help? (`gpu_bench.py`, full output in `sat-kernel/gpu_results.md`)

**Same algorithm, CPU (NumPy) vs GPU (Hesper).** The GPU is 4–5× faster from n = 100,000 on. At
n = 10,000 starting the process and WebGPU costs more than the whole computation. On uniform
instances the two runs drift apart in float rounding and take different numbers of steps, so the
time per step is the fair comparison there:

| instance | CPU (NumPy) | GPU (Hesper), wall | speedup |
|---|---|---|---|
| planted, n = 100,000 (50 steps each) | 0.72 s | 0.15 s | 4.8× |
| planted, n = 500,000 (60 steps each) | 4.38 s | 1.05 s | 4.2× |
| uniform 4.0, n = 10,000 | 1.20 ms/step | 0.17 ms/step | 7.0× per step |

**GPU dynamics vs AE-Kissat-MAB on the CPU, and the race** (timeout 120 s; every SAT answer
checked against every clause):

| instance | AE-Kissat-MAB alone | GPU dynamics alone | race (winner) |
|---|---|---|---|
| planted, n = 100,000 | 1.68 s | 0.27 s | 0.56 s (GPU) |
| planted, n = 500,000 | 14.87 s | 2.96 s | 5.02 s (GPU) |
| uniform 4.0, n = 10,000 | 12.55 s | 0.45 s | 0.49 s (GPU) |
| uniform 4.0, n = 100,000 | timeout | 34.02 s | 35.36 s (GPU) |
| uniform 4.2, n = 1,000 | 23.09 s | 0.19 s | 0.26 s (GPU) |
| uniform 4.2, n = 10,000 | 109.47 s | timeout | 111.59 s (CPU) |
| piece instance, λ = 1, (4,1), (1,4) | 0.04 s | timeout | 0.05 s (CPU) |
| piece instance, λ = 1, (2,2), (2,2) | 0.02 s | timeout | 0.01 s (CPU) |

So the GPU wins on random-like satisfiable formulas, sometimes by more than 20×. The CPU winner
wins near the threshold at n = 10,000 and on the structured piece formulas, and it alone can
answer UNSAT. The race costs a little over the faster engine alone, mostly because `kernel.py`
writes the CPU's DIMACS file before starting the GPU.

None of this bears on polynomial time: the GPU dynamics are a heuristic that fails on harder
formulas, and both engines slow down sharply as n grows.

## Layout

| Path | What it is |
|---|---|
| `setup.sh` | Pinned commits; clones, overlays, patches, Python environment |
| `overlays/formal-math/eth/` | New Lean files: `BestThreeSat.lean` (statements), `BestThreeSatSolution.lean`, `PolyChallenge.lean`, `proof/maintheorem/BestRate/{Defs,Main}.lean`, `scripts/PrintAxiomsBest.lean` |
| `patches/formal-math.patch` | Registers the new Lean libraries in `eth/lakefile.toml` |
| `overlays/hesper/GpuRank/Main.lean` | The GPU kernel: modular Gaussian elimination in WGSL, run through Hesper |
| `patches/hesper.patch` | Adds the `gpu-rank` executable and the `HESPER_MACOS_SDK` setting to Hesper's lakefile |
| `piece-search/pieces.py` | Gadgets, grouped tensor powers, exact ranks (CPU or GPU), the score ρ̂(k) |
| `piece-search/search.py` | Random search over gadgets, compared with the singlet baseline at each k |
| `piece-search/gpu_rank.py` | Python wrapper for `gpu-rank` |
| `piece-search/bench.py`, `bench_score.py` | The benchmarks; results in `bench_results.md` |
| `overlays/hesper/GpuSat/Main.lean` | The GPU SAT solver: lightspeed's dynamics in WGSL, run through Hesper |
| `sat-kernel/build_solvers.sh` | Downloads (SHA-256 checked) and builds the top 2025 competition solvers |
| `sat-kernel/satlib.py`, `scaling.py` | Instance generators, solver runner; scaling on random 3-SAT and pigeonhole |
| `sat-kernel/encode_pieces.py`, `kernel_bench.py`, `score_found.py` | Pieces as SAT; solvers compared on them; tensor-power scores of what they find |
| `sat-kernel/gpu_sat.py`, `kernel.py`, `gpu_bench.py` | GPU solver wrapper and NumPy reference; the CPU/GPU race; its benchmark |
| `scripts/` | `verify-lean.sh`, `build-gpu.sh` (builds `gpu-rank` and `gpu-sat`), `bench.sh` |

## Licences

This repository is Apache-2.0 (see `LICENSE`), as are the projects it builds on: `formal-math`
(Anthropic), `hesper` (Verilean) and `openai/math` (OpenAI). Their code is not redistributed here;
`setup.sh` fetches it from upstream.
