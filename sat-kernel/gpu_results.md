# The GPU search kernel (Hesper gpu-sat) against the CPU

## 1. Same algorithm (lightspeed dynamics): NumPy on the CPU vs Hesper on the GPU

| instance | steps to solution | CPU (NumPy) | GPU (Hesper) | GPU speedup |
|---|---|---|---|---|
| lightspeed planted, n=10,000, ratio 4.262 | 50 (CPU), 50 (GPU) | 0.07 s | 0.17 s (0.01 s on the GPU) | 0.4× |
| lightspeed planted, n=100,000, ratio 4.262 | 50 (CPU), 50 (GPU) | 0.72 s | 0.15 s (0.10 s on the GPU) | 4.8× |
| lightspeed planted, n=500,000, ratio 4.262 | 60 (CPU), 60 (GPU) | 4.38 s | 1.05 s (0.98 s on the GPU) | 4.2× |
| uniform random, n=1,000, ratio 4.0 | 3330 (CPU), 1850 (GPU) | 0.47 s | 0.28 s (0.24 s on the GPU) | 1.7× |
| uniform random, n=10,000, ratio 4.0 | 12220 (CPU), 5140 (GPU) | 14.72 s | 0.93 s (0.88 s on the GPU) | 15.9× |

## 2. GPU dynamics vs the competition winner AE_kissat2025_MAB on the CPU (timeout 120 s)

| instance | CPU solver alone | GPU dynamics alone | race: answer, winner, time |
|---|---|---|---|
| lightspeed planted, n=10,000, ratio 4.262 | SAT 0.12 s | SAT 0.07 s | SAT, gpu, 0.10 s |
| lightspeed planted, n=100,000, ratio 4.262 | SAT 1.68 s | SAT 0.27 s | SAT, gpu, 0.56 s |
| lightspeed planted, n=500,000, ratio 4.262 | SAT 14.87 s | SAT 2.96 s | SAT, gpu, 5.02 s |
| uniform random, n=1,000, ratio 4.0 | SAT 1.06 s | SAT 0.12 s | SAT, gpu, 0.14 s |
| uniform random, n=10,000, ratio 4.0 | SAT 12.55 s | SAT 0.45 s | SAT, gpu, 0.49 s |
| uniform random, n=100,000, ratio 4.0 | TIMEOUT timeout | SAT 34.02 s | SAT, gpu, 35.36 s |
| uniform random, n=1,000, ratio 4.2 | SAT 23.09 s | SAT 0.19 s | SAT, gpu, 0.26 s |
| uniform random, n=10,000, ratio 4.2 | SAT 109.47 s | TIMEOUT timeout | SAT, cpu, 111.59 s |
| piece instance lam=1 [(4, 1), (1, 4)] | SAT 0.04 s | TIMEOUT timeout | SAT, cpu, 0.05 s |
| piece instance lam=1 [(2, 2), (2, 2)] | SAT 0.02 s | TIMEOUT timeout | SAT, cpu, 0.01 s |
