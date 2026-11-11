"""Score candidate "pieces" for the SWAP-decomposition step of the ETH-refutation algorithm.

Background (formal-math/eth, proof/statements/PiecesStatement.lean, Definition 7):
pieces with parameter rho at size lam are integer tensors A_i on four lam-bit strings x, y, u, v with

    sum_i A_i = d * SWAP,   SWAP(x, y, u, v) = [x = v][y = u],

polynomially many of them, and for every i

    log2 rowrank(A_i) + log2 colrank(A_i) <= 4 * rho * lam + O(log lam),

where "rowwise" reads A_i as a matrix (x, y) -> (u, v) and "colwise" as (x, u) -> (y, v).
Lean's Theorem A (`GeneralPieces.thmRunningTime`) turns pieces with parameter rho into #k-SAT in
2^O(n log log n / (log n)^alpha) with alpha = log2(1/rho). The paper's pieces have rho = 1/sqrt(2)
(alpha = 1/2). Rank subadditivity forces rho >= 1/2, so alpha <= 1 within this framework.

This module scores one family of candidates: a one-position gadget d*SWAP_1 = sum_j B_j, raised to
the k-th tensor power and grouped by how often each B_j occurs. That is the shape of the paper's
key idea (SWAP = I - 2*singlet, grouped by the number of singlets). The grouped operators number
C(k+J-1, J-1), polynomially many, and their rowwise / colwise matrices are sums of Kronecker
products of the gadget's 4x4 matrices. Ranks are computed modulo two large primes; the larger value
is a lower bound on the true rank that is exact with high probability, and `exact=True` rechecks
over the integers.

The score at k is rho_hat(k) = max over groups of log2(rowrank * colrank) / (4k). It is a
finite-size number, not a theorem: at k = 1 every exact decomposition can look like rho = 1/2, and
the value only settles as k grows. Compare candidates at equal k, and against the baselines.
"""

from __future__ import annotations

import itertools
import math
from dataclasses import dataclass

import flint
import numpy as np

PRIMES = (4611686018427387847, 2305843009213693951)  # two primes below 2^62, so numpy int64 can reduce


def swap1() -> np.ndarray:
    """SWAP on one position, as a tensor T[x, y, u, v] = [x = v][y = u]."""
    t = np.zeros((2, 2, 2, 2), dtype=object)
    for x, y in itertools.product((0, 1), repeat=2):
        t[x, y, y, x] = 1
    return t


def identity1() -> np.ndarray:
    """I[x, y, u, v] = [x = u][y = v]."""
    t = np.zeros((2, 2, 2, 2), dtype=object)
    for x, y in itertools.product((0, 1), repeat=2):
        t[x, y, x, y] = 1
    return t


def singlet1() -> np.ndarray:
    """2 * |psi-><psi-| with psi- = (|01> - |10>)/sqrt(2): S[x, y, u, v] = s(x, y) s(u, v)."""
    s = {(0, 1): 1, (1, 0): -1}
    t = np.zeros((2, 2, 2, 2), dtype=object)
    for x, y, u, v in itertools.product((0, 1), repeat=4):
        t[x, y, u, v] = s.get((x, y), 0) * s.get((u, v), 0)
    return t


def rowwise(t: np.ndarray) -> np.ndarray:
    """Rows (x, y), columns (u, v)."""
    return t.reshape(4, 4)


def colwise(t: np.ndarray) -> np.ndarray:
    """Rows (x, u), columns (y, v)."""
    return t.transpose(0, 2, 1, 3).reshape(4, 4)


def rank(m: np.ndarray, exact: bool = False, primes: tuple[int, ...] = PRIMES) -> int:
    rows, cols = m.shape
    if exact:
        return flint.fmpz_mat(rows, cols, [int(e) for e in m.flat]).rank()
    return max(flint.nmod_mat(rows, cols, np.mod(m, p).ravel().tolist(), p).rank() for p in primes)


def compositions(k: int, parts: int):
    """All count vectors (t_1, ..., t_parts) of nonnegative integers with sum k."""
    if parts == 1:
        yield (k,)
        return
    for first in range(k + 1):
        for rest in compositions(k - first, parts - 1):
            yield (first,) + rest


def grouped(local: list[np.ndarray], k: int) -> dict[tuple[int, ...], np.ndarray]:
    """For each count vector t, the sum over all words with those counts of the Kronecker products
    of the local 4x4 matrices: G_t = sum_j G_{t - e_j} (x) local_j."""
    J = len(local)
    level = {tuple([0] * J): np.ones((1, 1), dtype=np.int64)}
    for step in range(1, k + 1):
        nxt: dict[tuple[int, ...], np.ndarray] = {}
        for t in compositions(step, J):
            acc = None
            for j in range(J):
                if t[j] == 0:
                    continue
                prev = list(t)
                prev[j] -= 1
                term = np.kron(level[tuple(prev)], local[j])
                acc = term if acc is None else acc + term
            nxt[t] = acc
        level = nxt
    return level


@dataclass
class Score:
    k: int
    rho_hat: float
    worst_group: tuple[int, ...]
    per_position_product: float
    groups: list[tuple[tuple[int, ...], int, int]]


def check_decomposition(gadget: list[np.ndarray], d: int = 1) -> bool:
    return bool(np.all(sum(gadget) == d * swap1()))


GPU_PRIMES = (65521, 65519)  # the two largest primes below 2^16, for gpu-rank


def gpu_ranks(matrices: list[np.ndarray]) -> list[int]:
    """Ranks on the GPU (Hesper, see gpu_rank.py): the larger rank modulo the two GPU_PRIMES, in one
    gpu-rank process per prime."""
    import gpu_rank

    per_prime = [gpu_rank.ranks(matrices, p)[0] for p in GPU_PRIMES]
    return [max(rs) for rs in zip(*per_prime)]


def score(gadget: list[np.ndarray], k: int, exact: bool = False, backend: str = "cpu") -> Score:
    """`backend="gpu"` computes the ranks with gpu-rank instead of flint (`exact` is then ignored);
    `backend="cpu16"` uses flint with the GPU's primes, the like-for-like CPU comparison."""
    rows = grouped([rowwise(b).astype(np.int64) for b in gadget], k)
    cols = grouped([colwise(b).astype(np.int64) for b in gadget], k)
    ts = list(rows)
    if backend == "gpu":
        rk = gpu_ranks([rows[t] for t in ts] + [cols[t] for t in ts])
        pairs = list(zip(rk[: len(ts)], rk[len(ts):]))
    elif backend == "cpu16":
        pairs = [(rank(rows[t], primes=GPU_PRIMES), rank(cols[t], primes=GPU_PRIMES)) for t in ts]
    else:
        pairs = [(rank(rows[t], exact), rank(cols[t], exact)) for t in ts]
    groups = []
    worst, worst_t = -math.inf, None
    for t, (r, c) in zip(ts, pairs):
        groups.append((t, r, c))
        if r == 0 or c == 0:  # a zero operator is no piece
            continue
        val = math.log2(r) + math.log2(c)
        if val > worst:
            worst, worst_t = val, t
    return Score(k, worst / (4 * k), worst_t, 2 ** (worst / k), groups)
