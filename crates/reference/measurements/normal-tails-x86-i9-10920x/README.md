# Native x86 finite-tail and log-table measurements

Intel Core i9-10920X, Rust 1.97.1, CPU 14, performance governor.
Baseline `76825af`; combined #180/#183/#188 candidate `c1344c7`.
The standard benchmark is the candidate's `normal_local_performance` in both
archives, so workload definitions match. Numerical baseline sources are
unchanged. `tail-fma` additionally uses `-C target-feature=+fma`.

Three alternating process pairs cover seven ranges and all five normal
functions, including scalar, batch, dependency-chain and accurate-path
counts. `workloads.csv` summarizes their medians; the `.log` files retain
every original row. On the 1,024 evenly spaced inputs in [-38,-37]:

| Function | Baseline scalar ns | Candidate scalar ns | Candidate batch ns |
| --- | ---: | ---: | ---: |
| PDF | 1163.878 | 77.711 | 13.460 |
| CDF | 3677.495 | 125.867 | 20.524 |
| log-CDF | 14697.286 | 13.793 | 7.930 |

All three change from 1,023 accurate-path calls to zero in this pool. The
underflow workload also has zero candidate accurate-path calls, versus
808 baseline PDF calls and 759 CCDF/log-CDF calls. These are measured pools,
not claims of zero fallback over the complete binary64 domain.

With scalar FMA enabled, far-tail log-CDF measures 12.478 ns scalar,
8.322 ns batch and 34.262 ns dependency-chain. The black-box SciPy 1.16.3
`log_ndtr` samples measure about 15.4, 16.7 and 43.7 ns. Rust permits inlining
and stores slice outputs; SciPy scalar calls use a Cython capsule through a
C function pointer with a volatile result, and batch calls use its ufunc.
The chain includes input indexing. These interface differences and the
shared host preclude treating this as exhaustive fastest-library parity.
No external implementation source was consulted.

The paired harness links distinct library identities, rotates variants and
retains 33 samples per cell (three processes, 11 rounds after warm-up, at
least 5 ms each). It covers lengths 1, 2, 8 and 1,024. Each variant's batches
must equal its scalar results; cross-version equality is required for
ordinary, mixed and positive-tail pools. The old bounded far-tail Q256
result need not equal the newly proved rounded result.

Paired ordinary/mixed long batches show no >4% median regression. Short
length-two cases retain modest overhead: saturated positive CDF is
3.513 → 3.990 ns, centered CDF 3.861 → 4.536 ns, and PDF ordinary
21.424 → 22.467 ns. These absolute sub-nanosecond to 1 ns differences are
recorded alongside the tail gains; they are not hidden as universal wins.

Other CI jobs shared the host. Environment and sampled load files record
that limitation; these timings are neither emulated nor CI job timings.

Reproduce paired measurements from the repository root:

```sh
python3 crates/reference/measurements/normal-tails-x86-i9-10920x/build_paired.py target/tail-paired
for run in 0 1 2; do
  taskset -c 14 target/tail-paired/paired > "tail-paired-$run.csv"
done
python3 crates/reference/measurements/normal-tails-x86-i9-10920x/summarize.py target/tail-summary tail-paired-0.csv tail-paired-1.csv tail-paired-2.csv
```

The standard workload command is:

```sh
MORPHIQ_NORMAL_BENCH_WORKLOAD=negative_far_tail cargo test --release --locked -p morphiq-numerics --features simd,std normal_local_performance -- --ignored --nocapture --test-threads=1
```

Repeat for `negative_first_table`, `negative_wide_tail`, `underflow`,
`ordinary`, `mixed`, `positive_tail`, and with `RUSTFLAGS='-C target-feature=+fma'`.
The adjacent `log-tail-table-m1pro/README.md` documents the black-box SciPy
harness; use its Linux compilation command. Versions are SciPy 1.16.3 and
NumPy 2.5.4. Compile and install dependencies before timing.
