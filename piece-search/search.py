"""Random search over one-position gadgets d*SWAP = B_1 + ... + B_J with small integer entries.

Each candidate is screened by rho_hat at k = SCREEN_K, the best are rescored at larger k, and every
score is printed next to the singlet baseline (SWAP = I - S, the paper's key idea) at the same k.
A candidate is interesting only if it beats the baseline at every k it was scored at, and the trend
in k matters more than any single value (see the module docstring of pieces.py).

    .venv/bin/python search.py --samples 20000 --terms 3 --seed 1
"""

from __future__ import annotations

import argparse
import multiprocessing as mp

import numpy as np

from pieces import check_decomposition, identity1, score, singlet1, swap1

SCREEN_K = 3


def random_gadget(rng: np.random.Generator, terms: int, bound: int) -> list[np.ndarray]:
    d = int(rng.integers(1, 3))
    free = [rng.integers(-bound, bound + 1, size=(2, 2, 2, 2)).astype(object) for _ in range(terms - 1)]
    last = d * swap1() - sum(free)
    gadget = free + [last]
    assert check_decomposition(gadget, d)
    return gadget


def screen(args: tuple[int, int, int]) -> tuple[float, int]:
    seed, terms, bound = args
    gadget = random_gadget(np.random.default_rng(seed), terms, bound)
    return score(gadget, SCREEN_K).rho_hat, seed


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--samples", type=int, default=20000)
    ap.add_argument("--terms", type=int, default=3)
    ap.add_argument("--bound", type=int, default=1)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--keep", type=int, default=8)
    ap.add_argument("--max-k", type=int, default=5)
    a = ap.parse_args()

    baseline = [identity1(), -singlet1()]
    base = {k: score(baseline, k).rho_hat for k in range(SCREEN_K, a.max_k + 1)}

    jobs = [(a.seed * 10**9 + i, a.terms, a.bound) for i in range(a.samples)]
    with mp.Pool() as pool:
        results = pool.map(screen, jobs, chunksize=64)
    results.sort()
    print(f"screened {len(results)} gadgets with {a.terms} terms, entries in [-{a.bound}, {a.bound}], at k={SCREEN_K}")
    print(f"baseline (singlet) rho_hat: " + ", ".join(f"k={k}: {v:.4f}" for k, v in base.items()))
    print(f"best screened rho_hat at k={SCREEN_K}: {results[0][0]:.4f}; median {results[len(results)//2][0]:.4f}")

    print("\nrescoring the best:")
    for rho3, seed in results[: a.keep]:
        gadget = random_gadget(np.random.default_rng(seed), a.terms, a.bound)
        row = []
        for k in range(SCREEN_K, a.max_k + 1):
            s = score(gadget, k)
            row.append(f"k={k}: {s.rho_hat:.4f} ({'<' if s.rho_hat < base[k] - 1e-9 else '≥'} base)")
        print(f"  seed {seed}: " + "  ".join(row))


if __name__ == "__main__":
    main()
