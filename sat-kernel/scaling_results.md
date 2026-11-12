# Scaling of the SAT Competition 2025 solvers (timeout 120 s, median over instances)

## random 3-SAT, ratio 4.26

| n | AE_kissat2025_MAB | kissat-public | cadical-sc2025 |
|---|---|---|---|
| 100 | 0.02 s | 0.02 s | 0.01 s |
| 150 | 0.05 s | 0.04 s | 0.02 s |
| 200 | 0.26 s | 0.16 s | 0.17 s |
| 250 | 3.45 s | 1.30 s | 2.41 s |
| 300 | 0.07 s | 0.06 s | 0.95 s |
| 350 | 120.00 s (3/5 timeouts) | 120.00 s (3/5 timeouts) | 120.00 s (3/5 timeouts) |
| 400 | 4.24 s (1/5 timeouts) | 1.15 s (1/5 timeouts) | 4.02 s (1/5 timeouts) |

## pigeonhole PHP(n+1,n)

| n | AE_kissat2025_MAB | kissat-public | cadical-sc2025 |
|---|---|---|---|
| 7 | 0.02 s | 0.02 s | 0.02 s |
| 8 | 0.12 s | 0.12 s | 0.02 s |
| 9 | 0.40 s | 0.27 s | 0.03 s |
| 10 | 4.14 s | 2.22 s | 0.06 s |
| 11 | 37.61 s | 44.16 s | 0.24 s |
| 12 | 120.00 s (1/1 timeouts) | 120.00 s (1/1 timeouts) | 0.67 s |

