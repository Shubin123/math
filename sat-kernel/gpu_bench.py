"""Is the search kernel really using the GPU, and does the GPU help?

1. Same algorithm, CPU vs GPU: the lightspeed dynamics in NumPy (gpu_sat.reference) against the
   same dynamics on the GPU (Hesper gpu-sat), time to a verified solution.
2. GPU dynamics vs the SAT Competition 2025 winner on the CPU, each alone, and the race (kernel.py).

    python gpu_bench.py --timeout 300        # writes gpu_results.md
"""

from __future__ import annotations

import argparse
import time

import numpy as np

import gpu_sat
import kernel
from encode_pieces import encode


def instances():
    out = []
    for n in (10_000, 100_000, 500_000):
        out.append((f"lightspeed planted, n={n:,}, ratio 4.262", *gpu_sat.planted_lightspeed(n, int(n * 4.262), 61546989), n))
    for ratio, ns in ((4.0, (1_000, 10_000, 100_000)), (4.2, (1_000, 10_000))):
        for n in ns:
            out.append((f"uniform random, n={n:,}, ratio {ratio}", *gpu_sat.uniform_random(n, int(n * ratio), 1), n))
    for lam, shapes in [(1, [(4, 1), (1, 4)]), (1, [(2, 2), (2, 2)])]:
        cnf, _ = encode(lam, shapes)
        out.append((f"piece instance lam={lam} {shapes}", *gpu_sat.as_arrays(cnf.clauses), cnf.nvars))
    return out


def fmt(status, engine, secs):
    return f"{secs:.2f} s" if status in ("SAT", "UNSAT") else "timeout"


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--timeout", type=float, default=300)
    a = ap.parse_args()
    lines = ["# The GPU search kernel (Hesper gpu-sat) against the CPU", ""]

    lines += ["## 1. Same algorithm (lightspeed dynamics): NumPy on the CPU vs Hesper on the GPU", "",
              "| instance | steps to solution | CPU (NumPy) | GPU (Hesper) | GPU speedup |", "|---|---|---|---|---|"]
    for name, var, q, n in instances()[:5]:
        t0 = time.perf_counter()
        _, steps_c, ok = gpu_sat.reference(var, q, n, gpu_sat.initial_v(n, 4), 20000, check_every=10)
        tc = time.perf_counter() - t0
        st, steps_g, ms, wall, _ = gpu_sat.run_gpu(var, q, n, max_steps=20000, check_every=10)
        lines.append(f"| {name} | {steps_c} (CPU), {steps_g} (GPU) | {tc:.2f} s | {wall:.2f} s ({ms / 1000:.2f} s on the GPU) | "
                     f"{tc / wall:.1f}× |" if ok and st == "SAT" else f"| {name} | not solved | {tc:.2f} s | {wall:.2f} s | — |")
        print(lines[-1], flush=True)

    lines += ["", f"## 2. GPU dynamics vs the competition winner {kernel.CPU_SOLVER} on the CPU (timeout {a.timeout:.0f} s)", "",
              "| instance | CPU solver alone | GPU dynamics alone | race: answer, winner, time |", "|---|---|---|---|"]
    for name, var, q, n in instances():
        cpu = kernel.solve(var, q, n, timeout=a.timeout, use_gpu=False)
        gpu = kernel.solve(var, q, n, timeout=a.timeout, use_cpu=False)
        race = kernel.solve(var, q, n, timeout=a.timeout)
        lines.append(f"| {name} | {cpu[0]} {fmt(*cpu[:3])} | {gpu[0]} {fmt(*gpu[:3])} | {race[0]}, {race[1] or '—'}, {fmt(*race[:3])} |")
        print(lines[-1], flush=True)
    text = "\n".join(lines)
    open("gpu_results.md", "w").write(text + "\n")
    print(text)


if __name__ == "__main__":
    main()
