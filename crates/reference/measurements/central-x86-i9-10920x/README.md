# Native x86 central first-stage comparison

Intel Core i9-10920X, Rust 1.97.1, CPU 14, performance governor.
Before: #184 `42e3a8e`; after: #186 `bd1aa06`, default `simd,std` build.
The scalar stage and all SIMD backends evaluate the same proved operation
sequence. SIMD returns early for a homogeneous eligible chunk only when
all lanes decide; otherwise the existing composition owns the whole chunk.
Keeping partially accepted vectors live across that composition had caused
unnecessary fallback work and register/buffer overhead, including on tiny
inputs. The whole-chunk decision removes that state.

The harness links distinct library identities and alternates their order.
It checks all result bits against the baseline before timing. Three
processes each retain 11 rounds after warm-up, at least 5 ms per sample:
33 samples per cell. Fixed-seed 4,096-input pools cover tiny, central,
ordinary and mixed inputs, scalar and batch, with lengths 1, 2, 3, 4, 8,
17 and 1,024. PDF and log-CDF are controls. Full samples, medians, extrema,
environment and host-load observations are retained.

| Workload, length 1,024 | Scalar before/after ns | Batch before/after ns |
| --- | ---: | ---: |
| central CDF | 111.297 / 25.275 | 15.816 / 7.702 |
| central CCDF | 109.619 / 25.169 | 16.575 / 7.866 |
| central centered CDF | 105.890 / 26.952 | 13.530 / 8.489 |
| ordinary CDF | 60.563 / 53.681 | 35.338 / 34.562 |
| ordinary CCDF | 58.147 / 51.468 | 31.618 / 31.374 |
| ordinary centered CDF | 59.613 / 54.025 | 33.913 / 34.769 |
| tiny CDF | 12.504 / 12.693 | 5.083 / 5.000 |
| tiny CCDF | 11.756 / 11.871 | 4.568 / 4.806 |
| tiny centered CDF | 9.071 / 9.397 | 4.001 / 4.071 |

Central scalar calls improve about fourfold and central batches 1.6–2.1x.
Ordinary scalar calls improve 9–11%; ordinary batch medians range from
2.2% faster to 2.5% slower. Tiny inputs retain sub-nanosecond costs (the
largest long-batch difference here is 0.238 ns for CCDF). These limits are
reported rather than claiming every length and workload improves.

Other CI jobs shared the host. CPU 14 was pinned and CPU 2 is its sibling;
recorded load is not an idle-host guarantee. Same-process alternation
reduces between-process drift. These results establish local effects, not
fastest-alternative parity or a cross-host speed claim.

Reproduce from the repository root, compiling before timing:

```sh
python3 crates/reference/measurements/central-x86-i9-10920x/build_paired.py target/central-paired
for run in 0 1 2; do
  taskset -c 14 target/central-paired/paired > "paired-$run.csv"
done
python3 crates/reference/measurements/central-x86-i9-10920x/summarize.py target/central-summary paired-0.csv paired-1.csv paired-2.csv
```

Full all-feature workspace tests and Clippy pass on this implementation.
Native SSE2, AVX2 and AVX-512 tests compare both intermediate words and
rounding decisions at the first-stage boundaries and neighboring encodings,
then public results over mixed inputs and slice remainders. Independent
mpmath fixtures, extracted Coq cross-checks and determinism CI provide
assurance beyond the benchmark's cross-version result comparisons.
