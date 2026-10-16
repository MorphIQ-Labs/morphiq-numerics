# Native x86 scalar FMA comparison

Intel Core i9-10920X, Rust 1.97.1, CPU 14, performance governor. Both
variants use `3abc8c1` with `simd,std`; variant 0 builds with `-fma`,
variant 1 with `+fma`. The benchmark executable enables FMA so inlined
candidate operations also use hardware instructions. The baseline library
has already selected the Dekker implementation through its compile-time
configuration. Neither build permits implicit floating-point contraction.

The paired executable links distinct library and arch crate identities,
checks scalar and batch result bits before timing, and alternates variant
order. Each process retains 33 rounds after warm-up, at least 10 ms per
sample: 99 samples per function/range/mode over three processes. Each
4,096-value pool uses the fixed seed in `paired.rs`. `summary.csv` retains
sample counts, medians and extrema; `comparison.csv` compares medians.

Other CI jobs shared the machine. The benchmark is pinned to CPU 14;
`host-load.csv` samples whole-host and sibling CPU 2 activity every five
seconds. These are same-process comparisons under recorded host load,
not measurements from an otherwise idle machine. They establish local
before/after effects, not fastest-alternative parity or cross-host timing.

| Scalar workload | Dekker ns | FMA ns | Change |
| --- | ---: | ---: | ---: |
| PDF ordinary | 12.666 | 11.051 | -12.7% |
| CDF ordinary | 59.157 | 49.276 | -16.7% |
| CCDF ordinary | 56.983 | 46.697 | -18.1% |
| Centered CDF ordinary | 58.758 | 48.583 | -17.3% |
| Log-CDF ordinary | 144.626 | 130.264 | -9.9% |
| erfcx table | 21.098 | 18.592 | -11.9% |
| erfcx positive common | 19.840 | 17.284 | -12.9% |
| erfcx asymptotic | 31.010 | 18.089 | -41.7% |
| erfcx reciprocal | 14.478 | 10.109 | -30.2% |
| erfcx negative | 24.614 | 23.037 | -6.4% |

Batch samples are included to quantify the remaining scalar/batch gap.
Vector backends already use hardware FMA; their timings change little.
For the five normal-family workloads, the scalar saving closes 29–41% of
the baseline scalar-minus-batch gap. For nonnegative erfcx workloads it
closes 33–47%. FMA removes part of scalar arithmetic cost, while vector
parallelism, scalar first-stage decisions and batch dispatch remain
different costs.

Reproduce from the repository root, compiling before timing:

```sh
python3 crates/reference/measurements/scalar-fma-x86-i9-10920x/build_paired.py target/fma-x86-paired
for run in 0 1 2; do
  taskset -c 14 target/fma-x86-paired/paired > "paired-$run.csv"
done
python3 crates/reference/measurements/scalar-fma-x86-i9-10920x/summarize.py target/fma-x86-summary paired-0.csv paired-1.csv paired-2.csv
```

`check_fma.sh` separately passed full workspace tests and matched 48,000
public and 760,127 internal corpus lines on this host. The benchmark's
bit comparisons supplement that gate; they are not an independent oracle.
