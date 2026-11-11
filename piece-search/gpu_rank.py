"""Ranks modulo a prime p < 2^16 on the GPU, through the `gpu-rank` executable built in the Hesper
checkout (../hesper/GpuRank/Main.lean, see the README).

All matrices of one call go to one process, so WebGPU is initialised once per call.
"""

from __future__ import annotations

import os
import struct
import subprocess
import tempfile
import time
from pathlib import Path

import numpy as np

GPU_PRIME = 65521  # the largest prime below 2^16
HESPER = Path(os.environ.get("HESPER_DIR", Path(__file__).resolve().parent.parent / "hesper"))
EXE = HESPER / ".lake" / "build" / "bin" / "gpu-rank"


def available() -> bool:
    return EXE.exists()


def ranks(matrices: list[np.ndarray], p: int = GPU_PRIME) -> tuple[list[int], list[float], float]:
    """Ranks modulo p of integer matrices; also the GPU time of each (ms) and the wall time of the
    whole call (s), which includes process start-up and WebGPU initialisation."""
    if not 2 < p < 2**16:
        raise ValueError("gpu-rank needs a prime 2 < p < 2^16")
    with tempfile.NamedTemporaryFile(suffix=".bin", delete=False) as fh:
        for m in matrices:
            nr, nc = m.shape
            fh.write(struct.pack("<III", nr, nc, p))
            fh.write(np.mod(np.asarray(m, dtype=np.int64), p).astype("<u4").tobytes())
        path = fh.name
    try:
        t0 = time.perf_counter()
        env = dict(os.environ, HESPER_LOG_LEVEL=os.environ.get("HESPER_LOG_LEVEL", "error"))
        out = subprocess.run([str(EXE), path], cwd=HESPER, check=True, capture_output=True, text=True, env=env)
        wall = time.perf_counter() - t0
    finally:
        os.unlink(path)
    lines = [line.split()[1:] for line in out.stdout.splitlines() if line.startswith("RANK ")]
    if len(lines) != len(matrices):
        raise RuntimeError(f"gpu-rank returned {len(lines)} results for {len(matrices)} matrices:\n{out.stderr[-2000:]}")
    return [int(r) for r, _ in lines], [float(ms) for _, ms in lines], wall
