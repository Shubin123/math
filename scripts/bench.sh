#!/usr/bin/env bash
# Measure whether the GPU (Hesper gpu-rank) speeds up the rank step of the piece search, and the
# end-to-end scoring time. Writes piece-search/bench_results.md.
set -euo pipefail
cd "$(dirname "$0")/../piece-search"
.venv/bin/python bench.py
.venv/bin/python bench_score.py
