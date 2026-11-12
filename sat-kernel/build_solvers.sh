#!/usr/bin/env bash
# Download the top SAT Competition 2025 sequential solvers (exact archives, checked by SHA-256) and
# build them into sat-kernel/solvers/bin.
#   AE_kissat2025_MAB  main track winner (overall and SAT)
#   kissat-public      main track 2nd overall
#   cadical-sc2025     main track winner on UNSAT
set -euo pipefail
cd "$(dirname "$0")"
URL=https://satcompetition.github.io/2025/downloads/solvers/main
mkdir -p solvers/src solvers/bin

fetch() {  # name sha256
  local name=$1 sum=$2
  [ -f "solvers/src/$name.tar.xz" ] || curl -sSfL -o "solvers/src/$name.tar.xz" "$URL/$name.tar.xz"
  echo "$sum  solvers/src/$name.tar.xz" | shasum -a 256 -c -
  rm -rf "solvers/src/$name" && mkdir -p "solvers/src/$name"
  tar -xJf "solvers/src/$name.tar.xz" -C "solvers/src/$name"
}

fetch AE_kissat2025_MAB 069cc73be6ca20e2d1f22cf63dec858026deab041bf3b98bfa20c6676697013c
fetch kissat-public     89a07d496eca8ca1676590dbfd9714bc5c6f706095f0d56370e372583025b9fc
fetch cadical-sc2025    1041526e6d8e8dff609a0a5c502146f6043b5d659af2ba3d2ad73793ee8efdfa

for s in AE_kissat2025_MAB kissat-public; do
  d=solvers/src/$s/$s
  # The archives ship a stale src/makefile symlink that makes configure fail.
  rm -f "$d/src/makefile"
  (cd "$d" && ./configure --competition >/dev/null && make -j"$(sysctl -n hw.ncpu 2>/dev/null || nproc)" >/dev/null)
  cp "$d/build/kissat" "solvers/bin/$s"
done
d=solvers/src/cadical-sc2025/cadical-sc2025
(cd "$d" && ./configure >/dev/null && make -j"$(sysctl -n hw.ncpu 2>/dev/null || nproc)" >/dev/null)
cp "$d/build/cadical" solvers/bin/cadical-sc2025

for s in solvers/bin/*; do echo "$s: $("$s" --version 2>&1 | head -1)"; done
