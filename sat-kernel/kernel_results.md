# Piece instances: SAT Competition 2025 solvers as the search kernel (timeout 900 s)

| lam | shapes (R_j, C_j) | vars | clauses | AE_kissat2025_MAB | kissat-public | cadical-sc2025 | answer | note |
|---|---|---|---|---|---|---|---|---|
| 2 | [(16, 1), (8, 8), (1, 16)] | 244865 | 1308769 | timeout | timeout | timeout | unknown | singlet shape, middle group with 8 terms of +-1 entries |
| 2 | [(16, 1), (7, 7), (1, 16)] | 233473 | 1227297 | timeout | timeout | timeout | unknown | singlet shape at its rational rank 7 |
| 2 | [(6, 6), (6, 6), (6, 6)] | 164097 | 767137 | 0.2 s | 0.2 s | 0.3 s | SAT (verified) | every product 36 < 49: would beat the singlet at lam = 2 |
| 2 | [(5, 5), (5, 5), (6, 6)] | 141313 | 635937 | 0.2 s | 0.2 s | 0.2 s | SAT (verified) | products 25, 25, 36; sum of ranks exactly 16 |
| 2 | [(8, 4), (4, 8), (6, 6)] | 164097 | 767137 | 562.6 s | 895.9 s | timeout | SAT (verified) | products 32, 32, 36 |
| 2 | [(5, 5), (5, 5), (5, 5)] | 130433 | 572897 | timeout | timeout | timeout | unknown | sum of row ranks 15 < 16: UNSAT by rank subadditivity |
