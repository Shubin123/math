"""End to end: the time to score a gadget at size k (every group, rowwise and colwise, two primes
each), with the ranks computed three ways, and a check that all three give the same ranks:

* cpu:   flint, two primes below 2^62 (the default of pieces.score);
* cpu16: flint, the GPU's two primes below 2^16 (like for like with the GPU);
* gpu:   Hesper gpu-rank, two primes below 2^16, one process per prime (start-up and WebGPU
         initialisation included).

    .venv/bin/python bench_score.py          # appends to bench_results.md
"""

from __future__ import annotations

import time

from pieces import identity1, score, singlet1


def timed(gadget, k, backend):
    t0 = time.perf_counter()
    s = score(gadget, k, backend=backend)
    return s, time.perf_counter() - t0


def main() -> None:
    gadget = [identity1(), -singlet1()]
    lines = ["", "## End to end: scoring the singlet gadget (all groups, rowwise and colwise, two primes each)", "",
             "| k | matrix size | groups | cpu s (2^62 primes) | cpu16 s (2^16 primes) | gpu s | gpu vs cpu | gpu vs cpu16 | same ranks |",
             "|---|---|---|---|---|---|---|---|---|"]
    for k in (3, 4, 5, 6):
        cpu, tc = timed(gadget, k, "cpu")
        cpu16, t16 = timed(gadget, k, "cpu16")
        gpu, tg = timed(gadget, k, "gpu")
        same = cpu.groups == cpu16.groups == gpu.groups
        lines.append(f"| {k} | {4**k} | {len(cpu.groups)} | {tc:.2f} | {t16:.2f} | {tg:.2f} | {tc / tg:.2f}× | {t16 / tg:.2f}× | {'yes' if same else 'NO'} |")
        print(lines[-1], flush=True)
    with open("bench_results.md", "a") as fh:
        fh.write("\n".join(lines) + "\n")


if __name__ == "__main__":
    main()
