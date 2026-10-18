# Log-normalization native measurements

All values below are nanoseconds per call. Spread is the minimum–maximum of nine retained rounds, not a confidence interval. Ratios pair methods by round before taking the median. These measurements describe the recorded shared host; they do not assert statistical equivalence or globally optimal performance.

## Independent repeated calls

| Build | Input | K | Checked median [min, max] | Paired checked/scratch median [min, max] |
| --- | --- | ---: | ---: | ---: |
| scalar | ordinary | 1 | 6.32 [5.66, 8.35] | 0.204 [0.160, 0.227] |
| scalar | ordinary | 2 | 69.97 [54.65, 74.25] | 0.808 [0.588, 0.950] |
| scalar | ordinary | 3 | 115.90 [102.74, 131.70] | 0.884 [0.735, 1.133] |
| scalar | ordinary | 8 | 274.81 [271.22, 283.76] | 0.932 [0.879, 0.954] |
| scalar | ordinary | 32 | 1060.43 [1022.13, 1118.50] | 0.947 [0.871, 1.047] |
| scalar | ordinary | 128 | 4243.61 [4088.76, 4378.88] | 0.951 [0.871, 0.976] |
| scalar | ordinary | 1024 | 35194.66 [34617.50, 35824.12] | 0.938 [0.901, 0.946] |
| scalar | ordinary | 65536 | 2181147.88 [2144603.62, 2265670.12] | 0.918 [0.863, 0.978] |
| scalar | zeros_tails | 1 | 8.26 [6.28, 8.92] | 0.227 [0.210, 0.320] |
| scalar | zeros_tails | 2 | 541.48 [539.49, 546.42] | 0.942 [0.927, 0.949] |
| scalar | zeros_tails | 3 | 1131.91 [1117.28, 1142.87] | 0.985 [0.962, 1.008] |
| scalar | zeros_tails | 8 | 2793.66 [2784.65, 2806.13] | 0.984 [0.982, 0.995] |
| scalar | zeros_tails | 32 | 5859.90 [5811.99, 5875.98] | 0.979 [0.960, 0.990] |
| scalar | zeros_tails | 128 | 24230.00 [23780.14, 24582.70] | 0.983 [0.957, 0.994] |
| scalar | zeros_tails | 1024 | 188575.29 [186532.27, 195148.43] | 0.982 [0.975, 1.007] |
| scalar | zeros_tails | 65536 | 11998437.25 [11950463.81, 12140029.94] | 0.981 [0.974, 0.991] |
| scalar | common_offset | 1 | 7.47 [6.18, 8.90] | 0.213 [0.180, 0.283] |
| scalar | common_offset | 2 | 63.92 [54.63, 73.68] | 0.647 [0.563, 0.835] |
| scalar | common_offset | 3 | 113.88 [98.46, 131.69] | 0.886 [0.700, 1.146] |
| scalar | common_offset | 8 | 275.40 [270.68, 286.68] | 0.932 [0.893, 0.958] |
| scalar | common_offset | 32 | 1068.06 [1020.83, 1103.99] | 0.920 [0.861, 1.016] |
| scalar | common_offset | 128 | 4367.23 [4310.27, 4456.26] | 0.938 [0.911, 0.950] |
| scalar | common_offset | 1024 | 34392.23 [33567.39, 35391.98] | 0.937 [0.878, 0.983] |
| scalar | common_offset | 65536 | 2169305.75 [2111562.62, 2233328.38] | 0.906 [0.883, 0.947] |
| simd | ordinary | 1 | 6.16 [5.40, 8.65] | 0.185 [0.162, 0.222] |
| simd | ordinary | 2 | 73.09 [60.05, 76.73] | 0.782 [0.626, 0.949] |
| simd | ordinary | 3 | 137.84 [129.08, 151.64] | 0.941 [0.808, 1.105] |
| simd | ordinary | 8 | 313.05 [311.11, 317.39] | 0.956 [0.936, 0.979] |
| simd | ordinary | 32 | 1001.52 [993.16, 1011.06] | 0.929 [0.924, 0.944] |
| simd | ordinary | 128 | 3704.51 [3678.39, 3727.17] | 0.928 [0.909, 0.931] |
| simd | ordinary | 1024 | 28477.49 [28274.85, 28826.87] | 0.916 [0.907, 0.936] |
| simd | ordinary | 65536 | 1801965.44 [1786511.44, 1827992.19] | 0.906 [0.892, 0.930] |
| simd | zeros_tails | 1 | 7.09 [5.96, 8.18] | 0.193 [0.176, 0.232] |
| simd | zeros_tails | 2 | 553.83 [540.78, 560.39] | 0.957 [0.926, 0.977] |
| simd | zeros_tails | 3 | 1191.05 [1187.27, 1196.85] | 0.988 [0.977, 1.002] |
| simd | zeros_tails | 8 | 3142.28 [3114.74, 3216.76] | 0.995 [0.976, 1.010] |
| simd | zeros_tails | 32 | 7362.90 [7339.43, 7380.76] | 0.990 [0.984, 0.992] |
| simd | zeros_tails | 128 | 29890.44 [29827.53, 30000.62] | 0.989 [0.984, 0.991] |
| simd | zeros_tails | 1024 | 228903.80 [227856.01, 229836.66] | 0.989 [0.985, 0.991] |
| simd | zeros_tails | 65536 | 14614512.44 [14598827.94, 14663971.50] | 0.988 [0.984, 0.992] |
| simd | common_offset | 1 | 6.57 [6.28, 8.01] | 0.178 [0.174, 0.210] |
| simd | common_offset | 2 | 68.83 [56.01, 74.08] | 0.809 [0.592, 0.888] |
| simd | common_offset | 3 | 139.57 [119.42, 150.98] | 0.928 [0.731, 1.074] |
| simd | common_offset | 8 | 312.16 [310.46, 318.34] | 0.960 [0.934, 0.980] |
| simd | common_offset | 32 | 1003.96 [996.31, 1010.17] | 0.932 [0.918, 0.944] |
| simd | common_offset | 128 | 3701.78 [3676.08, 3726.58] | 0.923 [0.913, 0.936] |
| simd | common_offset | 1024 | 28626.13 [28319.38, 28829.81] | 0.927 [0.911, 0.940] |
| simd | common_offset | 65536 | 1807169.12 [1790261.62, 1831852.44] | 0.907 [0.890, 0.925] |

## Component and dependent-call diagnostics

`profile-log-normalize` runs separately from the paired throughput harness. A warm-up round precedes nine retained rounds for each case. The dependent chain feeds the preceding normalized first component into the next pair’s common offset; the input gap remains fixed. This includes pair construction and output consumption. Component inputs are prepared outside timing. Costs are not additive: inlining, instruction overlap and host conditions differ.

| Build | Gap | Method | Median [min, max] |
| --- | ---: | --- | ---: |
| scalar | 0 | checked_chain | 80.34 [58.94, 82.39] |
| scalar | 0 | checked_pair | 79.24 [59.59, 81.31] |
| scalar | 0 | exp | 17.24 [12.83, 18.32] |
| scalar | 0 | legacy_chain | 92.09 [77.66, 111.16] |
| scalar | 0 | ln_1p | 18.29 [18.22, 18.32] |
| scalar | 4.625 | checked_chain | 79.26 [58.82, 81.60] |
| scalar | 4.625 | checked_pair | 79.92 [59.23, 81.34] |
| scalar | 4.625 | exp | 18.07 [16.78, 19.86] |
| scalar | 4.625 | legacy_chain | 92.90 [78.66, 111.30] |
| scalar | 4.625 | ln_1p | 18.27 [18.24, 20.72] |
| scalar | 741 | checked_chain | 581.01 [536.43, 612.26] |
| scalar | 741 | checked_pair | 578.00 [531.43, 610.64] |
| scalar | 741 | exp | 542.79 [527.98, 579.35] |
| scalar | 741 | legacy_chain | 611.28 [535.04, 626.91] |
| scalar | 741 | ln_1p | 13.07 [11.58, 14.91] |
| scalar | 756 | checked_chain | 35.88 [33.34, 42.39] |
| scalar | 756 | checked_pair | 37.04 [33.23, 39.37] |
| scalar | 756 | exp | 7.49 [6.66, 8.99] |
| scalar | 756 | legacy_chain | 51.89 [42.58, 59.45] |
| scalar | 756 | ln_1p | 12.27 [10.24, 14.36] |
| simd | 0 | checked_chain | 57.22 [55.25, 67.54] |
| simd | 0 | checked_pair | 50.58 [50.50, 57.55] |
| simd | 0 | exp | 7.81 [7.80, 7.85] |
| simd | 0 | legacy_chain | 95.91 [75.60, 97.10] |
| simd | 0 | ln_1p | 10.13 [10.11, 10.16] |
| simd | 4.625 | checked_chain | 75.30 [70.40, 81.40] |
| simd | 4.625 | checked_pair | 76.62 [69.06, 80.14] |
| simd | 4.625 | exp | 17.03 [16.71, 18.19] |
| simd | 4.625 | legacy_chain | 90.34 [86.11, 101.83] |
| simd | 4.625 | ln_1p | 23.41 [20.37, 23.90] |
| simd | 741 | checked_chain | 622.03 [563.53, 630.57] |
| simd | 741 | checked_pair | 621.32 [582.12, 626.33] |
| simd | 741 | exp | 575.23 [531.75, 583.15] |
| simd | 741 | legacy_chain | 706.10 [654.00, 711.62] |
| simd | 741 | ln_1p | 9.35 [8.53, 11.28] |
| simd | 756 | checked_chain | 39.74 [33.28, 40.84] |
| simd | 756 | checked_pair | 39.28 [33.25, 40.62] |
| simd | 756 | exp | 8.58 [8.32, 9.44] |
| simd | 756 | legacy_chain | 111.79 [108.33, 116.59] |
| simd | 756 | ln_1p | 12.90 [11.20, 15.58] |

At gap 741, the isolated exponential costs about 543 ns (scalar) / 575 ns (SIMD build), against about 578 / 621 ns for checked normalization. This supports the inherited subnormal exponential as the material tail cost; it does not measure the accurate-path frequency of general workloads. Gap 756 reaches the existing underflow result quickly. The normalized finite log tail is preserved in both cases.

The initial general-loop implementation and samples remain in commit `93115b9c467560e6677c2a9ef662cc0f062babb5`. Its short-vector overhead motivated the exact singleton and finite-pair specializations. The general shifted-scratch alternative uses an extra O(K) buffer and a second public reduction call; its exact-shift test domain is narrower than the new API. The fused pair API has different numerical and failure contracts. No external implementation with all matching guarantees has been qualified here.

No wrapper/FFI is involved. SIMD dispatch and remainder handling are included in the whole-call slice samples; they are not isolated cycle measurements. The new implementation has four general passes, zero dynamic allocation, no new lookup table and no new accurate fallback; it inherits the elementary paths. Native ARM timings, exclusive frequency/thermal control and statistical inference about equivalence are not established by these x86 samples.
