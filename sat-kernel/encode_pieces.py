"""Pieces as a SAT problem: a SAT solver as the search kernel of piece-search.

Find integer tensors A_1, ..., A_J on four lam-bit strings with

    A_1 + ... + A_J = d * SWAP,          SWAP(x, y, u, v) = [x = v][y = u],

where each A_j is given twice, by explicit factorizations with entries in {-1, 0, 1}:

    A_j(x, y, u, v) = sum_{t < R_j} F_j[(x,y), t] * G_j[(u,v), t]      (row-wise, R_j terms)
                    = sum_{t < C_j} H_j[(x,u), t] * K_j[(y,v), t]      (column-wise, C_j terms)

so rowrank(A_j) <= R_j and colrank(A_j) <= C_j. This is the shape of `Pieces.FactorsThrough` in
formal-math/eth/proof/statements/PiecesStatement.lean (an explicit integer factorization), with
entries restricted to {-1, 0, 1}. A SAT answer is a decomposition, checked independently by
`verify`; UNSAT means no decomposition with these shapes and entries exists.

Encoding: a ternary value is two Booleans (p, n), value p - n, never both; a product of ternaries
is two gates; each sum constraint is an equality of two cardinalities, encoded with totalizers.
"""

from __future__ import annotations

import itertools

import numpy as np


class CNF:
    def __init__(self) -> None:
        self.nvars = 0
        self.clauses: list[list[int]] = []
        self.true = self.var()
        self.add([self.true])

    def var(self) -> int:
        self.nvars += 1
        return self.nvars

    def add(self, clause: list[int]) -> None:
        self.clauses.append(clause)

    def and2(self, a: int, b: int) -> int:
        r = self.var()
        self.add([-r, a]); self.add([-r, b]); self.add([r, -a, -b])
        return r

    def or2(self, a: int, b: int) -> int:
        r = self.var()
        self.add([r, -a]); self.add([r, -b]); self.add([-r, a, b])
        return r

    def ternary(self) -> tuple[int, int]:
        p, n = self.var(), self.var()
        self.add([-p, -n])
        return p, n

    def mul(self, a: tuple[int, int], b: tuple[int, int]) -> tuple[int, int]:
        """(+1 literal, -1 literal) of the product of two ternaries."""
        pos = self.or2(self.and2(a[0], b[0]), self.and2(a[1], b[1]))
        neg = self.or2(self.and2(a[0], b[1]), self.and2(a[1], b[0]))
        return pos, neg

    def totalizer(self, lits: list[int]) -> list[int]:
        """Unary count: out[k-1] <=> at least k of lits are true (both directions)."""
        if not lits:
            return []
        if len(lits) == 1:
            return [lits[0]]
        a = self.totalizer(lits[: len(lits) // 2])
        b = self.totalizer(lits[len(lits) // 2:])
        r = [self.var() for _ in range(len(a) + len(b))]
        A = [self.true] + a + [-self.true]
        B = [self.true] + b + [-self.true]
        R = [self.true] + r + [-self.true]
        for i in range(len(a) + 1):
            for j in range(len(b) + 1):
                if i + j > 0:
                    self.add([-A[i], -B[j], R[i + j]])           # >= i and >= j  =>  >= i+j
                if i + j < len(r):
                    self.add([A[i + 1], B[j + 1], -R[i + j + 1]])  # < i+1 and < j+1  =>  < i+j+1
        return r

    def count_eq(self, xs: list[int], ys: list[int], offset: int = 0) -> None:
        """#true(xs) = #true(ys) + offset."""
        ox, oy = self.totalizer(xs), self.totalizer(ys)
        at_least = lambda o, k: self.true if k <= 0 else (o[k - 1] if k <= len(o) else -self.true)
        for k in range(min(0, offset) + 1, max(len(xs), len(ys) + offset) + 1):
            l, r = at_least(ox, k), at_least(oy, k - offset)
            self.add([-l, r]); self.add([l, -r])

    def dimacs(self) -> str:
        return f"p cnf {self.nvars} {len(self.clauses)}\n" + "".join(" ".join(map(str, c)) + " 0\n" for c in self.clauses)


def encode(lam: int, shapes: list[tuple[int, int]], d: int = 1):
    """CNF for: pieces with (R_j, C_j) = shapes[j] summing to d * SWAP on lam-bit strings."""
    cnf = CNF()
    N = 2 ** lam
    pairs = list(itertools.product(range(N), repeat=2))
    idx = {p: i for i, p in enumerate(pairs)}
    fac = []
    for R, C in shapes:
        F = [[cnf.ternary() for _ in range(R)] for _ in pairs]
        G = [[cnf.ternary() for _ in range(R)] for _ in pairs]
        H = [[cnf.ternary() for _ in range(C)] for _ in pairs]
        K = [[cnf.ternary() for _ in range(C)] for _ in pairs]
        fac.append((F, G, H, K))
    for x, y, u, v in itertools.product(range(N), repeat=4):
        all_pos, all_neg = [], []
        for (R, C), (F, G, H, K) in zip(shapes, fac):
            row = [cnf.mul(F[idx[x, y]][t], G[idx[u, v]][t]) for t in range(R)]
            col = [cnf.mul(H[idx[x, u]][t], K[idx[y, v]][t]) for t in range(C)]
            # row value = col value:  #row+ + #col- = #row- + #col+
            cnf.count_eq([p for p, _ in row] + [n for _, n in col], [n for _, n in row] + [p for p, _ in col])
            all_pos += [p for p, _ in row]
            all_neg += [n for _, n in row]
        target = d if (x == v and y == u) else 0
        cnf.count_eq(all_pos, all_neg, target)
    return cnf, fac


def decode(model: set[int], lam: int, shapes, fac) -> list[np.ndarray]:
    """The pieces A_j as arrays indexed [x, y, u, v], from the row-wise factorizations."""
    N = 2 ** lam
    pairs = list(itertools.product(range(N), repeat=2))
    val = lambda t: (t[0] in model) - (t[1] in model)
    pieces = []
    for (R, C), (F, G, H, K) in zip(shapes, fac):
        Fm = np.array([[val(F[i][t]) for t in range(R)] for i in range(len(pairs))], dtype=np.int64).reshape(len(pairs), R)
        Gm = np.array([[val(G[i][t]) for t in range(R)] for i in range(len(pairs))], dtype=np.int64).reshape(len(pairs), R)
        pieces.append((Fm @ Gm.T).reshape(N, N, N, N))
    return pieces


def verify(pieces: list[np.ndarray], lam: int, shapes, d: int = 1) -> bool:
    """Independent check of a decoded answer: exact sum, and exact ranks within the shapes."""
    import flint

    N = 2 ** lam
    swap = np.zeros((N, N, N, N), dtype=np.int64)
    for x, y in itertools.product(range(N), repeat=2):
        swap[x, y, y, x] = 1
    if not np.array_equal(sum(pieces), d * swap):
        return False
    for A, (R, C) in zip(pieces, shapes):
        rowm = A.reshape(N * N, N * N)
        colm = A.transpose(0, 2, 1, 3).reshape(N * N, N * N)
        rk = lambda m: flint.fmpz_mat(m.shape[0], m.shape[1], [int(e) for e in m.flat]).rank()
        if rk(rowm) > R or rk(colm) > C:
            return False
    return True
