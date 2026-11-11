"""Does the GPU (Hesper) speed up the exact-rank step of the piece search? Same matrices, same
prime, CPU (python-flint) against GPU (gpu-rank); every GPU rank is checked against flint's.

    .venv/bin/python bench.py            # writes bench_results.md
"""

from __future__ import annotations

import platform
import time

import flint
import numpy as np

import gpu_rank
from pieces import PRIMES, colwise, grouped, identity1, rowwise, singlet1

P = gpu_rank.GPU_PRIME


def flint_rank(m: np.ndarray, p: int) -> tuple[int, float, float]:
    """Rank mod p with flint; seconds to build the flint matrix, seconds for the rank itself."""
    t0 = time.perf_counter()
    M = flint.nmod_mat(m.shape[0], m.shape[1], np.mod(m, p).ravel().tolist(), p)
    t1 = time.perf_counter()
    r = M.rank()
    return r, t1 - t0, time.perf_counter() - t1


def cases() -> list[tuple[str, np.ndarray]]:
    rng = np.random.default_rng(0)
    out = []
    singlet = [identity1(), -singlet1()]
    for k in (5, 6):
        rows = grouped([rowwise(b).astype(np.int64) for b in singlet], k)
        cols = grouped([colwise(b).astype(np.int64) for b in singlet], k)
        t = (k // 2, k - k // 2)
        out.append((f"singlet k={k} group {t} rowwise", rows[t]))
        out.append((f"singlet k={k} group {t} colwise", cols[t]))
    for n in (512, 1024, 2048, 4096):
        for r in (n // 4, n):
            m = (rng.integers(0, P, (n, r)) @ rng.integers(0, P, (r, n)) % P) if r < n else rng.integers(0, P, (n, n))
            out.append((f"random {n}x{n} rank<={r}", m.astype(np.int64)))
    return out


def main() -> None:
    if not gpu_rank.available():
        raise SystemExit(f"gpu-rank not built at {gpu_rank.EXE}; see the README")
    cs = cases()
    gpu_ranks, gpu_ms, wall = gpu_rank.ranks([m for _, m in cs])
    rows = []
    all_match = True
    for (name, m), gr, gms in zip(cs, gpu_ranks, gpu_ms):
        cr, conv, rk = flint_rank(m, P)
        exact = max(flint_rank(m, q)[0] for q in PRIMES) if name.startswith("singlet") else None
        match = gr == cr
        all_match &= match
        rows.append((name, m.shape[0], cr, gr, match, exact, conv * 1e3, rk * 1e3, gms))
    lines = [
        "# GPU (Hesper) vs CPU (python-flint): rank modulo 65521",
        "",
        f"Machine: {platform.machine()} {platform.mac_ver()[0] or platform.system()}; flint {flint.__version__}.",
        f"GPU wall time for the whole batch, including process start-up and WebGPU init: {wall:.2f} s.",
        "",
        "| matrix | n | rank (flint) | rank (GPU) | equal | rank mod 2^62-size primes | flint build ms | flint rank ms | GPU ms | speedup vs flint rank | speedup vs flint build+rank |",
        "|---|---|---|---|---|---|---|---|---|---|---|",
    ]
    for name, n, cr, gr, match, exact, conv, rk, gms in rows:
        lines.append(f"| {name} | {n} | {cr} | {gr} | {'yes' if match else 'NO'} | {exact if exact is not None else '—'} | "
                     f"{conv:.1f} | {rk:.1f} | {gms:.1f} | {rk / gms:.2f}× | {(conv + rk) / gms:.2f}× |")
    lines += ["", f"All GPU ranks equal flint's: {'yes' if all_match else 'NO'}."]
    text = "\n".join(lines)
    print(text)
    with open("bench_results.md", "w") as fh:
        fh.write(text + "\n")


if __name__ == "__main__":
    main()
