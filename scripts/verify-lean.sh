#!/usr/bin/env bash
# Build the ETH formalization with this repository's additions and print the axioms of every
# headline theorem. Expected: each line ends in [propext, Classical.choice, Quot.sound], and the
# only `sorry` warnings come from formal-math's own Challenge.lean (statements without proofs, by
# design). PolyChallenge.lean (the open target) is not a default target and is not built here.
set -euo pipefail
cd "$(dirname "$0")/../formal-math/eth"
lake exe cache get
lake build
lake env lean scripts/PrintAxioms.lean
lake env lean scripts/PrintAxiomsBest.lean
