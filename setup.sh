#!/usr/bin/env bash
# Clone the pinned upstream projects next to this script, apply this repository's additions to
# them, and create the Python environment for piece-search.
#
#   ./setup.sh                    # formal-math + hesper + Python env
#   ./setup.sh --with-openai-math # also a sparse checkout of openai/math (read only, nothing built)
#
# Re-running is safe: each checkout is reset to its pinned commit (local edits to tracked upstream
# files are discarded) and the additions are applied again.
set -euo pipefail
cd "$(dirname "$0")"
ROOT=$PWD

FORMAL_MATH_REV=16a5ce41304fcdaea4e0be7c132e1c361dc26da5
HESPER_REV=38fba72000a0d39a0421c5911378df9d28f6aca9
OPENAI_MATH_REV=4eaee87548250b2682affda7d05d947c05554bae

with_openai=0
for arg in "$@"; do
  case $arg in
    --with-openai-math) with_openai=1 ;;
    *) echo "unknown option: $arg" >&2; exit 2 ;;
  esac
done

# clone_at URL DIR REV: a shallow checkout of exactly REV.
clone_at() {
  local url=$1 dir=$2 rev=$3
  if [ ! -d "$dir/.git" ]; then
    git init -q "$dir"
    git -C "$dir" remote add origin "$url"
  fi
  git -C "$dir" fetch -q --depth 1 origin "$rev"
  git -C "$dir" checkout -q --force FETCH_HEAD
  echo "$dir at $(git -C "$dir" rev-parse --short HEAD)"
}

# apply NAME: copy overlays/NAME over the checkout, then apply patches/NAME.patch.
apply() {
  local name=$1
  cp -R "overlays/$name/." "$name/"
  git -C "$name" apply "$ROOT/patches/$name.patch"
  echo "  applied overlays/$name and patches/$name.patch"
}

clone_at https://github.com/anthropics/formal-math.git formal-math "$FORMAL_MATH_REV"
apply formal-math
clone_at https://github.com/Verilean/hesper.git hesper "$HESPER_REV"
apply hesper

if [ "$with_openai" = 1 ]; then
  if [ ! -d openai-math/.git ]; then
    git clone -q --filter=blob:none --sparse --no-checkout https://github.com/openai/math.git openai-math
  fi
  git -C openai-math sparse-checkout set --no-cone '/*.md' '/lean/ComparatorChallenges/' '/lean/docs/378.md' \
    '/lean/lakefile.lean' '/lean/lean-toolchain' '/lean/lake-manifest.json' '/lean/*.md'
  git -C openai-math checkout -q "$OPENAI_MATH_REV"
  echo "openai-math at $(git -C openai-math rev-parse --short HEAD) (sparse)"
fi

PY=${PYTHON:-python3}
if ! "$PY" -c 'import sys; sys.exit(sys.version_info < (3, 10))'; then
  echo "need Python >= 3.10 (set PYTHON=/path/to/python3.x)" >&2
  exit 1
fi
[ -d piece-search/.venv ] || "$PY" -m venv piece-search/.venv
piece-search/.venv/bin/pip install -q -r piece-search/requirements.txt
echo "piece-search/.venv ready ($("$PY" --version))"
