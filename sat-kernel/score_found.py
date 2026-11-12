"""Do the decompositions the SAT kernel found at lam = 2 keep their advantage under tensor powers?

The SAT kernel (kernel_bench.py) finds 3 pieces of rank 6 x 6 summing to SWAP on 2-bit strings,
where the singlet construction needs 7 x 7. That is one size only; Lean's Theorem A needs pieces for
every lam. Here each found decomposition is used as a gadget on 2-bit blocks: its k-th tensor power,
grouped by how often each piece occurs (C(k+2, 2) groups, polynomially many), acts on lam = 2k bits,
and is scored like the singlet with pieces.score (ranks on the GPU through Hesper gpu-rank).

    python score_found.py            # writes found_results.md
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "piece-search"))

from encode_pieces import decode, encode, verify  # noqa: E402
from pieces import identity1, score, singlet1  # noqa: E402
from satlib import solve  # noqa: E402


def main() -> None:
    singlet = [identity1(), -singlet1()]
    lines = ["# Tensor powers of the decompositions found by the SAT kernel", "",
             "rho_hat at lam bits (lower is better); the singlet construction at the same lam for comparison.", "",
             "| gadget | lam = 2 | lam = 4 | lam = 6 |", "|---|---|---|---|"]
    base = [score(singlet, lam, backend="gpu").rho_hat for lam in (2, 4, 6)]
    lines.append("| singlet (paper), 1-bit gadget | " + " | ".join(f"{r:.4f}" for r in base) + " |")
    for shapes in ([(6, 6), (6, 6), (6, 6)], [(5, 5), (5, 5), (6, 6)]):
        cnf, fac = encode(2, shapes)
        r = solve("AE_kissat2025_MAB", cnf.dimacs(), 600)
        assert r.status == "SAT"
        pieces = decode(r.model, 2, shapes, fac)
        assert verify(pieces, 2, shapes)
        rho = [score(pieces, k, backend="gpu").rho_hat for k in (1, 2, 3)]
        lines.append(f"| found at lam = 2, shapes {shapes} | " + " | ".join(f"{x:.4f}" for x in rho) + " |")
        print(lines[-1], flush=True)
    text = "\n".join(lines)
    print(text)
    open("found_results.md", "w").write(text + "\n")


if __name__ == "__main__":
    main()
