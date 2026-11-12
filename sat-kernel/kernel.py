"""The search kernel: race the SAT Competition 2025 winner (CPU, complete) against the lightspeed-
style dynamics (GPU through Hesper, incomplete) on the same formula; first verified answer wins.

    status, engine, seconds, assignment = solve(var, q, n, timeout=300)

`var`, `q` are (M, 3) arrays as in gpu_sat.py. SAT answers from either engine are checked against
every clause; UNSAT can only come from the CPU solver, with its proof obligations as in the
competition (the solver is trusted here; it is not asked for a proof).
"""

from __future__ import annotations

import os
import subprocess
import tempfile
import time
from pathlib import Path

import numpy as np

import gpu_sat
from satlib import SOLVERS_DIR

CPU_SOLVER = os.environ.get("KERNEL_CPU_SOLVER", "AE_kissat2025_MAB")


def write_dimacs(path: Path, var: np.ndarray, q: np.ndarray, n: int) -> None:
    lits = ((var.astype(np.int64) + 1) * q.astype(np.int64))
    with open(path, "w") as fh:
        fh.write(f"p cnf {n} {lits.shape[0]}\n")
        np.savetxt(fh, np.concatenate([lits, np.zeros((lits.shape[0], 1), np.int64)], axis=1), fmt="%d")


def cpu_model(stdout: str, n: int) -> np.ndarray:
    a = -np.ones(n)
    for line in stdout.splitlines():
        if line.startswith("v "):
            for t in line.split()[1:]:
                x = int(t)
                if x > 0:
                    a[x - 1] = 1.0
    return a


def solve(var, q, n, *, timeout=300.0, use_cpu=True, use_gpu=True, gpu_steps=200000, seed=4):
    """(status, engine, seconds, ±1 assignment or None); status SAT, UNSAT or TIMEOUT."""
    with tempfile.TemporaryDirectory() as d:
        d = Path(d)
        procs = {}
        # Output goes to files, not pipes: a solver printing a large model would block on a full
        # pipe that is only read after it exits.
        outs = {name: open(d / f"{name}.out", "w+") for name in ("cpu", "gpu")}
        t0 = time.perf_counter()
        if use_cpu:
            write_dimacs(d / "f.cnf", var, q, n)
            procs["cpu"] = subprocess.Popen([str(SOLVERS_DIR / CPU_SOLVER), str(d / "f.cnf")],
                                            stdout=outs["cpu"], stderr=subprocess.DEVNULL)
        if use_gpu:
            (d / "in.bin").write_bytes(gpu_sat.pack(var, q, n, gpu_sat.initial_v(n, seed), gpu_steps, 50))
            env = dict(os.environ, HESPER_LOG_LEVEL="error")
            procs["gpu"] = subprocess.Popen([str(gpu_sat.EXE), str(d / "in.bin"), str(d / "v.bin")],
                                            cwd=gpu_sat.HESPER, stdout=outs["gpu"], stderr=subprocess.DEVNULL,
                                            env=env)
        result = ("TIMEOUT", None, timeout, None)
        try:
            while procs and time.perf_counter() - t0 < timeout:
                for name, p in list(procs.items()):
                    if p.poll() is None:
                        continue
                    outs[name].seek(0)
                    out = outs[name].read()
                    del procs[name]
                    dt = time.perf_counter() - t0
                    if name == "cpu" and p.returncode in (10, 20):
                        a = cpu_model(out, n) if p.returncode == 10 else None
                        if a is None or gpu_sat.satisfied(var, q, a).all():
                            result = ("SAT" if a is not None else "UNSAT", "cpu", dt, a)
                            return result
                    if name == "gpu" and "RESULT SAT" in out:
                        v = np.frombuffer((d / "v.bin").read_bytes(), dtype="<f4")
                        a = np.where(v > 0, 1.0, -1.0)
                        if gpu_sat.satisfied(var, q, a).all():
                            result = ("SAT", "gpu", dt, a)
                            return result
                time.sleep(0.01)
            return result
        finally:
            for p in procs.values():
                p.kill()
                p.wait()
            for f in outs.values():
                f.close()
