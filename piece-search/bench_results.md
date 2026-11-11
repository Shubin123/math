# GPU (Hesper) vs CPU (python-flint): rank modulo 65521

Machine: arm64 27.0.1; flint 0.9.0.
GPU wall time for the whole batch, including process start-up and WebGPU init: 4.68 s.

| matrix | n | rank (flint) | rank (GPU) | equal | rank mod 2^62-size primes | flint build ms | flint rank ms | GPU ms | speedup vs flint rank | speedup vs flint build+rank |
|---|---|---|---|---|---|---|---|---|---|---|
| singlet k=5 group (2, 3) rowwise | 1024 | 106 | 106 | yes | 106 | 107.4 | 24.0 | 18.3 | 1.32× | 7.20× |
| singlet k=5 group (2, 3) colwise | 1024 | 376 | 376 | yes | 376 | 105.7 | 62.8 | 12.9 | 4.87× | 13.08× |
| singlet k=6 group (3, 3) rowwise | 4096 | 694 | 694 | yes | 694 | 1679.7 | 1693.4 | 348.1 | 4.86× | 9.69× |
| singlet k=6 group (3, 3) colwise | 4096 | 694 | 694 | yes | 694 | 1659.6 | 2091.0 | 354.3 | 5.90× | 10.59× |
| random 512x512 rank<=128 | 512 | 128 | 128 | yes | — | 29.1 | 8.7 | 5.7 | 1.52× | 6.60× |
| random 512x512 rank<=512 | 512 | 512 | 512 | yes | — | 29.0 | 13.7 | 7.5 | 1.83× | 5.70× |
| random 1024x1024 rank<=256 | 1024 | 256 | 256 | yes | — | 117.6 | 56.8 | 21.2 | 2.67× | 8.21× |
| random 1024x1024 rank<=1024 | 1024 | 1024 | 1024 | yes | — | 116.4 | 90.7 | 30.2 | 3.00× | 6.86× |
| random 2048x2048 rank<=512 | 2048 | 512 | 512 | yes | — | 474.6 | 416.0 | 165.9 | 2.51× | 5.37× |
| random 2048x2048 rank<=2048 | 2048 | 2048 | 2048 | yes | — | 470.2 | 705.1 | 227.5 | 3.10× | 5.17× |
| random 4096x4096 rank<=1024 | 4096 | 1024 | 1024 | yes | — | 1893.0 | 2831.1 | 1369.2 | 2.07× | 3.45× |
| random 4096x4096 rank<=4096 | 4096 | 4096 | 4096 | yes | — | 1909.4 | 4771.8 | 2041.1 | 2.34× | 3.27× |

All GPU ranks equal flint's: yes.

## End to end: scoring the singlet gadget (all groups, rowwise and colwise, two primes each)

| k | matrix size | groups | cpu s (2^62 primes) | cpu16 s (2^16 primes) | gpu s | gpu vs cpu | gpu vs cpu16 | same ranks |
|---|---|---|---|---|---|---|---|---|
| 3 | 64 | 4 | 0.01 | 0.01 | 0.12 | 0.07× | 0.06× | yes |
| 4 | 256 | 5 | 0.16 | 0.16 | 0.15 | 1.09× | 1.06× | yes |
| 5 | 1024 | 6 | 4.16 | 3.70 | 0.47 | 8.82× | 7.83× | yes |
| 6 | 4096 | 7 | 130.13 | 116.02 | 12.02 | 10.82× | 9.65× | yes |
