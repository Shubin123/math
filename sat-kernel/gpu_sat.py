"""The GPU search kernel: lightspeed-style dynamical 3-SAT solving on the GPU, through Hesper's
`gpu-sat` (../hesper/GpuSat/Main.lean), plus a NumPy reference of the same dynamics to check it.

The dynamics can only find satisfying assignments; a formula on which they fail may still be
satisfiable, and they never prove unsatisfiability. Every assignment returned is checked against
every clause here.
"""

from __future__ import annotations

import os
import struct
import subprocess
import tempfile
import time
from pathlib import Path

import numpy as np

HESPER = Path(os.environ.get("HESPER_DIR", Path(__file__).resolve().parent.parent / "hesper"))
EXE = HESPER / ".lake" / "build" / "bin" / "gpu-sat"

# lightspeed 3sat_v2.py constants (also in GpuSat/Main.lean)
A0, B0, G0, D0, EPS, Z0 = 7.264952, 19.706215, 0.290741, 0.190131, 0.008693, 0.143817
DTF, AF, AT, GD, MUMIN, MUG, MUMAX = 1.185345, 2.075337, 0.161275, 0.229501, 0.634689, 0.2268, 0.946342


def as_arrays(clauses: list[list[int]]) -> tuple[np.ndarray, np.ndarray]:
    """(var, q): (M, 3) variable indices and signs; shorter clauses repeat their first literal."""
    lit = np.array([(c * 3)[:3] for c in clauses], dtype=np.int64)
    return (np.abs(lit) - 1).astype(np.uint32), np.sign(lit).astype(np.float32)


def planted_lightspeed(n: int, m: int, seed: int, noise: float = 0.35) -> tuple[np.ndarray, np.ndarray]:
    """`generate_hard_clauses` of lightspeed 3sat_v2.py, line for line: a planted assignment, and
    each literal's sign flipped away from it with probability `noise` (at least one kept)."""
    rng = np.random.RandomState(seed)
    var1 = rng.randint(0, n, size=m, dtype=np.int32)
    var2 = rng.randint(0, n - 1, size=m, dtype=np.int32)
    var2 = np.where(var2 >= var1, var2 + 1, var2)
    var3 = rng.randint(0, n - 2, size=m, dtype=np.int32)
    s = np.sort(np.stack([var1, var2], axis=1), axis=1)
    a, b = s[:, 0], s[:, 1]
    var3 = np.where(var3 < a, var3, np.where(var3 < (b - 1), var3 + 1, var3 + 2))
    solution = rng.choice([-1, 1], size=n)
    vs = np.stack([var1, var2, var3], axis=1)
    mask = rng.random(size=(m, 3)) < noise
    allf = np.all(mask, axis=1)
    mask[allf, rng.randint(0, 3, size=int(np.sum(allf)))] = False
    q = solution[vs] * np.where(mask, -1, 1)
    return vs.astype(np.uint32), q.astype(np.float32)


def uniform_random(n: int, m: int, seed: int) -> tuple[np.ndarray, np.ndarray]:
    """Uniform random 3-SAT: three distinct variables per clause, uniform signs."""
    rng = np.random.default_rng(seed)
    vs = np.argsort(rng.random((m, n)), axis=1)[:, :3] if n <= 64 else _distinct3(rng, n, m)
    q = rng.choice(np.array([-1.0, 1.0], dtype=np.float32), size=(m, 3))
    return vs.astype(np.uint32), q


def _distinct3(rng, n, m):
    vs = rng.integers(0, n, size=(m, 3))
    bad = (vs[:, 0] == vs[:, 1]) | (vs[:, 0] == vs[:, 2]) | (vs[:, 1] == vs[:, 2])
    while bad.any():
        vs[bad] = rng.integers(0, n, size=(int(bad.sum()), 3))
        bad = (vs[:, 0] == vs[:, 1]) | (vs[:, 0] == vs[:, 2]) | (vs[:, 1] == vs[:, 2])
    return vs


def satisfied(var: np.ndarray, q: np.ndarray, assignment: np.ndarray) -> np.ndarray:
    """Per clause: does the ±1 assignment satisfy it?"""
    return np.any(q * assignment[var] > 0, axis=1)


def majority_vote(var: np.ndarray, q: np.ndarray, n: int) -> np.ndarray:
    """Each variable set to the sign it carries most often (ties: +1)."""
    w = np.bincount(var.ravel(), weights=q.ravel().astype(np.float64), minlength=n)
    return np.where(w >= 0, 1.0, -1.0)


def initial_v(n: int, seed: int) -> np.ndarray:
    return np.random.RandomState(seed).uniform(-1, 1, n).astype(np.float32)


def pack(var: np.ndarray, q: np.ndarray, n: int, v0: np.ndarray, max_steps: int, check_every: int) -> bytes:
    m = var.shape[0]
    flat = var.ravel().astype(np.int64)
    order = np.argsort(flat, kind="stable").astype(np.uint32)       # occurrences e = 3m+i by variable
    off = np.concatenate([[0], np.cumsum(np.bincount(flat, minlength=n))]).astype(np.uint32)
    iv = np.concatenate([var.ravel().astype(np.uint32), off, order]).astype("<u4").tobytes()
    cf = np.concatenate([q.ravel(), np.full(m, 0.5, np.float32), np.ones(m, np.float32)]).astype("<f4").tobytes()
    vf = np.concatenate([v0, v0]).astype("<f4").tobytes()
    head = struct.pack("<7I", n, m, max_steps, check_every, len(iv), len(cf), len(vf))
    return head + iv + cf + vf


def run_gpu(var, q, n, *, seed=4, max_steps=100000, check_every=10, timeout=None):
    """(status, steps, gpu_ms, wall_s, v): status "SAT" (assignment verified) or "UNKNOWN"."""
    with tempfile.TemporaryDirectory() as d:
        inp, out = Path(d) / "in.bin", Path(d) / "v.bin"
        inp.write_bytes(pack(var, q, n, initial_v(n, seed), max_steps, check_every))
        env = dict(os.environ, HESPER_LOG_LEVEL=os.environ.get("HESPER_LOG_LEVEL", "error"))
        t0 = time.perf_counter()
        p = subprocess.run([str(EXE), str(inp), str(out)], cwd=HESPER, capture_output=True, text=True,
                           env=env, timeout=timeout, check=True)
        wall = time.perf_counter() - t0
        line = next(l for l in p.stdout.splitlines() if l.startswith("RESULT "))
        _, status, steps, ms = line.split()
        v = np.frombuffer(out.read_bytes(), dtype="<f4").copy()
    if status == "SAT" and not satisfied(var, q, np.where(v > 0, 1.0, -1.0)).all():
        status = "WRONG"
    return status, int(steps), float(ms), wall, v


def reference(var, q, n, v0, steps, check_every=None):
    """NumPy float32 copy of the GPU dynamics (same order of operations, same parameter schedule).
    With `check_every`, stops at the first check where v > 0 satisfies every clause and returns
    (v, steps taken, solved); otherwise returns v after `steps` steps."""
    m = var.shape[0]
    v, vp = v0.copy(), v0.copy()
    xs, xl = np.full(m, 0.5, np.float32), np.ones(m, np.float32)
    dt = np.float32(1.0)
    rows = np.arange(m)
    f32 = np.float32
    for step in range(steps):
        t = f32(1) - q * v[var]
        mi = np.argmin(t, axis=1)
        C = f32(0.5) * t[rows, mi]
        sf = min(1.0, step / 5000.0)
        avg = 1.0 + max(0.0, min(2.0, AF * (float(C.astype(np.float64).mean()) - AT)))
        alpha, beta = f32(A0 * np.sqrt(avg)), f32(B0 * avg)
        gamma, zeta, mu = f32(G0 * (1 - GD * sf)), f32(Z0 * (1 + sf)), f32(min(MUMAX, MUMIN + MUG * sf))
        sn = np.sin(C - gamma)
        dxs = beta * (xs + f32(EPS)) * sn * sn * sn
        dxl = alpha * (C - f32(D0))
        A = C * xl * xs
        B = C * (f32(1) + zeta * xl) * (f32(1) - xs)
        contrib = q * (A[:, None] + (np.arange(3)[None, :] == mi[:, None]) * B[:, None])
        dv = np.bincount(var.ravel().astype(np.int64), weights=contrib.ravel(), minlength=n).astype(np.float32)
        if step % 10 == 0:
            md = max(np.abs(dv).max(), np.abs(dxs).max(), np.abs(dxl).max())
            dt = f32(np.clip(DTF / md, 2.0 ** -7, 1e5)) if md > 0 else f32(1e5)
        v, vp = np.clip(v + dv * dt + mu * (v - vp), -1, 1).astype(np.float32), v
        xs = np.clip(xs + dxs * dt, 0, 1).astype(np.float32)
        xl = np.clip(xl + dxl * dt, 1, 1e4 * m).astype(np.float32)
        if check_every and (step + 1) % check_every == 0 and satisfied(var, q, np.where(v > 0, 1.0, -1.0)).all():
            return v, step + 1, True
    return (v, steps, False) if check_every else v
