#!/usr/bin/env bash
# Build Hesper (Dawn and its native bridge on first use) and the gpu-rank and gpu-sat executables.
#
# Lean's bundled lld cannot read the .tbd stubs of macOS SDKs that list the arm64e.x1
# architecture (macOS 27 SDKs). If the default SDK is such an SDK and HESPER_MACOS_SDK is unset,
# link against the newest installed SDK that does not list it.
set -euo pipefail
cd "$(dirname "$0")/../hesper"

if [ "$(uname)" = Darwin ] && [ -z "${HESPER_MACOS_SDK:-}" ]; then
  default_sdk=$(xcrun --show-sdk-path)
  if grep -q 'arm64e\.x1' "$default_sdk/usr/lib/libc++.tbd" 2>/dev/null; then
    for cand in $(ls -dr "$(dirname "$default_sdk")"/MacOSX[0-9]*.sdk 2>/dev/null); do
      if ! grep -q 'arm64e\.x1' "$cand/usr/lib/libc++.tbd" 2>/dev/null; then
        export HESPER_MACOS_SDK=$cand
        break
      fi
    done
    if [ -z "${HESPER_MACOS_SDK:-}" ]; then
      echo "every installed macOS SDK lists arm64e.x1; install an older one (e.g. the macOS 26 SDK)" >&2
      exit 1
    fi
  fi
fi
echo "HESPER_MACOS_SDK=${HESPER_MACOS_SDK:-<default>}"
lake build gpu-rank gpu-sat
ls -la .lake/build/bin/gpu-rank .lake/build/bin/gpu-sat
