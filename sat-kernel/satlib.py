"""Instance generators and a runner for competition SAT solvers.

Solvers follow the competition conventions: exit code 10 = satisfiable, 20 = unsatisfiable. Binaries
are looked up in $SAT_SOLVERS_DIR (default: ./solvers/bin, filled by build_solvers.sh).
"""

from __future__ import annotations

import os
import random
import subprocess
import tempfile
import time
from dataclasses import dataclass
from pathlib import Path

SOLVERS_DIR = Path(os.environ.get("SAT_SOLVERS_DIR", Path(__file__).resolve().parent / "solvers" / "bin"))
SOLVERS = ("AE_kissat2025_MAB", "kissat-public", "cadical-sc2025")

Clause = list[int]


def dimacs(nvars: int, clauses: list[Clause]) -> str:
    lines = [f"p cnf {nvars} {len(clauses)}"]
    lines += [" ".join(map(str, c)) + " 0" for c in clauses]
    return "\n".join(lines) + "\n"


def random_ksat(n: int, ratio: float, seed: int, k: int = 3) -> tuple[int, list[Clause]]:
    """Uniform random k-SAT: round(ratio*n) clauses, k distinct variables each, random signs."""
    rng = random.Random(seed)
    clauses = []
    for _ in range(round(ratio * n)):
        vs = rng.sample(range(1, n + 1), k)
        clauses.append([v if rng.random() < 0.5 else -v for v in vs])
    return n, clauses


def pigeonhole(n: int) -> tuple[int, list[Clause]]:
    """PHP(n+1, n): n+1 pigeons in n holes, unsatisfiable. Variable p*n + h + 1 = pigeon p in hole h."""
    var = lambda p, h: p * n + h + 1
    clauses = [[var(p, h) for h in range(n)] for p in range(n + 1)]
    for h in range(n):
        for p in range(n + 1):
            for q in range(p + 1, n + 1):
                clauses.append([-var(p, h), -var(q, h)])
    return (n + 1) * n, clauses


@dataclass
class Run:
    solver: str
    status: str  # "SAT", "UNSAT", "TIMEOUT", "ERROR"
    seconds: float
    model: set[int] | None = None


def solve(solver: str, cnf_text: str, timeout: float) -> Run:
    with tempfile.NamedTemporaryFile("w", suffix=".cnf", delete=False) as fh:
        fh.write(cnf_text)
        path = fh.name
    try:
        t0 = time.perf_counter()
        try:
            p = subprocess.run([str(SOLVERS_DIR / solver), path], capture_output=True, text=True, timeout=timeout)
            dt = time.perf_counter() - t0
            status = {10: "SAT", 20: "UNSAT"}.get(p.returncode, "ERROR")
        except subprocess.TimeoutExpired:
            return Run(solver, "TIMEOUT", timeout)
    finally:
        os.unlink(path)
    model = None
    if status == "SAT":
        model = {int(t) for line in p.stdout.splitlines() if line.startswith("v ") for t in line.split()[1:] if int(t) > 0}
    return Run(solver, status, dt, model)
