"""The SAT solver as the search kernel of piece-search: which 2025 solver is fastest on piece
instances, and what do they find?

Each instance asks for J pieces with shapes (R_j, C_j) summing to SWAP on lam-bit strings (see
encode_pieces.py). At lam = 2 with J = 3 = lam + 1 pieces (the number of groups of the paper's
singlet construction), the singlet gives shapes (16,1), (7,7), (1,16) in rational rank, so a
largest rank product of 49; rank subadditivity needs sum R_j >= 16 and sum C_j >= 16.

    python kernel_bench.py --timeout 900       # writes kernel_results.md
"""

from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor

from encode_pieces import decode, encode, verify
from satlib import SOLVERS, solve

INSTANCES = [
    (2, [(16, 1), (8, 8), (1, 16)], "singlet shape, middle group with 8 terms of +-1 entries"),
    (2, [(16, 1), (7, 7), (1, 16)], "singlet shape at its rational rank 7"),
    (2, [(6, 6), (6, 6), (6, 6)], "every product 36 < 49: would beat the singlet at lam = 2"),
    (2, [(5, 5), (5, 5), (6, 6)], "products 25, 25, 36; sum of ranks exactly 16"),
    (2, [(8, 4), (4, 8), (6, 6)], "products 32, 32, 36"),
    (2, [(5, 5), (5, 5), (5, 5)], "sum of row ranks 15 < 16: UNSAT by rank subadditivity"),
]


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--timeout", type=float, default=900)
    ap.add_argument("--jobs", type=int, default=9)
    a = ap.parse_args()

    built = []
    for lam, shapes, note in INSTANCES:
        cnf, fac = encode(lam, shapes)
        built.append((lam, shapes, note, cnf.dimacs(), fac, cnf.nvars, len(cnf.clauses)))
        print(f"encoded lam={lam} {shapes}: {cnf.nvars} vars, {len(cnf.clauses)} clauses", flush=True)

    jobs = [(i, s) for i in range(len(built)) for s in SOLVERS]
    with ThreadPoolExecutor(a.jobs) as pool:
        runs = list(pool.map(lambda j: (j[0], solve(j[1], built[j[0]][3], a.timeout)), jobs))

    lines = [f"# Piece instances: SAT Competition 2025 solvers as the search kernel (timeout {a.timeout:.0f} s)", "",
             "| lam | shapes (R_j, C_j) | vars | clauses | " + " | ".join(SOLVERS) + " | answer | note |",
             "|---|---|---|---|" + "---|" * len(SOLVERS) + "---|---|"]
    for i, (lam, shapes, note, _, fac, nv, nc) in enumerate(built):
        rs = {r.solver: r for j, r in runs if j == i}
        answers = {r.status for r in rs.values()} - {"TIMEOUT"}
        verdict = "/".join(sorted(answers)) or "unknown"
        if "SAT" in answers:
            r = next(r for r in rs.values() if r.status == "SAT")
            verdict += " (verified)" if verify(decode(r.model, lam, shapes, fac), lam, shapes) else " (FAILED CHECK)"
        cells = [f"{rs[s].seconds:.1f} s" if rs[s].status != "TIMEOUT" else "timeout" for s in SOLVERS]
        lines.append(f"| {lam} | {shapes} | {nv} | {nc} | " + " | ".join(cells) + f" | {verdict} | {note} |")
    text = "\n".join(lines)
    print(text)
    open("kernel_results.md", "w").write(text + "\n")


if __name__ == "__main__":
    main()
