"""How do the fastest SAT Competition 2025 solvers scale? Median time over seeds on random 3-SAT at
clause/variable ratio 4.26 (the hardest region) and on the pigeonhole formulas PHP(n+1, n), for
growing n. A polynomial-time method would show times growing like a power of n; CDCL solvers are
known to need 2^Omega(n) on both families (Chvatal-Szemeredi 1988; Haken 1985).

    python scaling.py --timeout 120          # writes scaling_results.md
"""

from __future__ import annotations

import argparse
import statistics
from concurrent.futures import ThreadPoolExecutor

from satlib import SOLVERS, dimacs, pigeonhole, random_ksat, solve


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--timeout", type=float, default=120)
    ap.add_argument("--seeds", type=int, default=5)
    ap.add_argument("--jobs", type=int, default=9)
    a = ap.parse_args()

    jobs = []
    for n in (100, 150, 200, 250, 300, 350, 400):
        for seed in range(a.seeds):
            nv, cl = random_ksat(n, 4.26, seed)
            jobs += [("random 3-SAT, ratio 4.26", n, s, dimacs(nv, cl)) for s in SOLVERS]
    for n in (7, 8, 9, 10, 11, 12):
        nv, cl = pigeonhole(n)
        jobs += [("pigeonhole PHP(n+1,n)", n, s, dimacs(nv, cl)) for s in SOLVERS]

    with ThreadPoolExecutor(a.jobs) as pool:
        runs = list(pool.map(lambda j: (j[0], j[1], solve(j[2], j[3], a.timeout)), jobs))

    table: dict[tuple[str, int, str], list] = {}
    for fam, n, r in runs:
        table.setdefault((fam, n, r.solver), []).append(r)
    lines = [f"# Scaling of the SAT Competition 2025 solvers (timeout {a.timeout:.0f} s, median over instances)", ""]
    for fam in dict.fromkeys(f for f, _, _ in table):
        lines += [f"## {fam}", "", "| n | " + " | ".join(SOLVERS) + " |", "|---|" + "---|" * len(SOLVERS)]
        for n in sorted({n for f, n, _ in table if f == fam}):
            cells = []
            for s in SOLVERS:
                rs = table[(fam, n, s)]
                med = statistics.median(r.seconds for r in rs)
                to = sum(r.status == "TIMEOUT" for r in rs)
                bad = sum(r.status == "ERROR" for r in rs)
                cells.append(f"{med:.2f} s" + (f" ({to}/{len(rs)} timeouts)" if to else "") + (f" ({bad} errors)" if bad else ""))
            lines.append(f"| {n} | " + " | ".join(cells) + " |")
        lines.append("")
    text = "\n".join(lines)
    print(text)
    open("scaling_results.md", "w").write(text + "\n")


if __name__ == "__main__":
    main()
