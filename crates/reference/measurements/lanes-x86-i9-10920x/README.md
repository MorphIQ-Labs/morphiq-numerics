# Native x86-64 measurements: Intel i9-10920X

Native timing of every lane kernel on SSE2, AVX2+FMA and AVX-512F, of the
standard-normal family, of the log-space compositions and of the existing
reference benchmarks, at `c6d5fff` plus the summarizer fix `49467c4` (#124).
Everything here describes this one host. No other x86 microarchitecture was
measured, and no conclusion is drawn for one.

## Host and conditions

`environment.txt` is the complete record: `lscpu`, kernel, toolchain, revision,
pinning, frequency settings and the load average before every process.

- Intel Core i9-10920X (Cascade Lake-X), 12 cores and 24 threads; L1d 32 KiB,
  L2 1 MiB per core, L3 19.3 MiB. SSE2, AVX2, FMA and AVX-512F are all present,
  so every backend was timed natively on the same machine.
- Fedora 44, Linux 7.2.8, `rustc` 1.99.0, release profile, no `RUSTFLAGS`.
- Every process pinned to logical CPU 2 with `taskset`. Its SMT sibling, CPU 14,
  ran nothing of this benchmark. Governor `performance`, EPP `performance`,
  turbo enabled. Frequency was not fixed.
- The host's GitLab runner was stopped for the run. The 1-minute load average
  was 1.1–1.6 throughout, except that repetition 1's lane sweep began at 4.9
  while the runner's last builds drained. Desktop sessions stayed open.

Timing is wall-clock (`Instant`). Comparisons are within one executable and
one host. No timing is a CI threshold.

## Reproduce

```sh
crates/reference/measurements/run_native.sh OUT_DIR 3       # ~50 minutes
python3 -I crates/reference/measurements/summarize_lanes.py OUT_DIR OUT_DIR/lanes-?.csv.gz
python3 -I crates/reference/measurements/summarize_native.py OUT_DIR
```

`run_native.sh` compiles everything first. It then runs each repetition as
separate pinned processes: the `native_performance` lane sweep, every
`normal_local_performance` workload (1,024 elements, then `ordinary` and
`mixed` at 1, 2, 3, 8 and 17), `log_space` `measure_cost`, `bench-batched`,
`bench-erfcx`, `bench-exp-stages` and the external-consumer normal benchmark
(`../normal-m1pro/consumer-inlining/benchmark.rs`).

The lane sweep (`crates/morphiq-numerics/src/lanes/tests/bench.rs`) times each
function on fixed-seed workloads in several modes:
- the scalar loop;
- the dispatched cascade (`map`);
- each backend forced alone, then the scalar function for the remainder;
- the scalar dependency chain, and the same chain through the identity.

Lengths are 1–17, 32, 64, 256, 4096 and 65536. A length below 4096 is timed as
the 4,096-element pool in consecutive calls of that length. Each run has 11
rounds after one discarded warm-up, and the order of the cells rotates every
round. Before timing, every mode's output is checked bit for bit against the
scalar function. Each function's classifier, itself checked against the same
bits, counts which stage decided each argument.

## Files

| File | Contents |
|---|---|
| `lanes-{1,2,3}.csv.gz` | Every timed lane record, plus path, table and backend records |
| `summary.csv` | Median, minimum and maximum ns per element of all 33 lane samples, ns per call, speed-up over the scalar loop |
| `paths.csv` | Which stage decided each pooled argument (identical across runs), table sizes, backends |
| `cache.csv` | The competing-working-set experiment |
| `normal-*.txt`, `normal-summary.csv` | `normal_local_performance`, raw and pooled |
| `consumer-*.txt`, `consumer-summary.csv` | The external-crate scalar and slice calls |
| `log-space-*.txt`, `log-space-summary.csv` | The log-space compositions |
| `bench-*-{1,2,3}.*`, `bench-*-summary.csv` | The existing reference benchmarks |

All times below are medians of the three repetitions, in ns per element unless
stated. `summary.csv` has every cell's spread. Most are 8–20% from minimum to
maximum; `exp` `common` at 4,096 reached 69% from a single outlying round.

## Bulk throughput, 4,096 elements

| Function | Workload | Scalar | SSE2 | AVX2 | AVX-512F | Dispatched | Speed-up | Scalar chain latency |
|---|---|---:|---:|---:|---:|---:|---:|---:|
| `exp` | `[−30, 0)` | 6.06 | 4.80 | 4.23 | 3.39 | 3.42 | 1.77× | 20.0 |
| `exp2` | `[−30, 0)` | 8.37 | 5.53 | 4.00 | 2.86 | 2.80 | 2.99× | 20.6 |
| `expm1` | `[−30, 0)` | 11.11 | 9.06 | 6.25 | 3.83 | 3.83 | 2.90× | 22.2 |
| `expm1` | `[−1/32, 1/32)` | 20.23 | 14.49 | 7.86 | 4.36 | 4.42 | 4.58× | 31.3 |
| `ln` | `[0.5, 2)` | 9.08 | **12.49** | 7.88 | 7.13 | 7.17 | 1.27× | 19.4 |
| `ln` | `1 ± 2^−47` | 89.40 | 64.56 | **245.43** | **172.90** | **171.90** | **0.52×** | 91.4 |
| `ln_1p` | `e^d`, `d ∈ [−30, 0)` | 8.48 | 5.79 | 4.65 | 3.30 | 3.35 | 2.53× | 18.5 |
| `ln_1p` | `[2^1020, MAX]` | 99.34 | 66.31 | **277.29** | **185.63** | **184.78** | **0.54×** | 101.3 |
| `erfcx` | `[−0.5, 16)` | 17.64 | 10.47 | 10.38 | 11.13 | 11.02 | 1.60× | 20.7 |
| `erfcx` | `[16, 512)` | 30.98 | 13.34 | 7.25 | 4.84 | 4.89 | 6.33× | 40.8 |
| `erfcx` | `[−26.6, −0.5)` | 24.44 | 19.94 | 20.03 | 18.47 | 18.21 | 1.34× | 34.4 |
| `norm_pdf` | `[−5, 5)` | 37.32 | 20.37 | 11.01 | 8.66 | 8.61 | 4.33× | 53.4 |
| `norm_cdf` | `[−5, 5)` | 70.80 | 48.31 | 35.05 | 28.99 | 28.56 | 2.48× | 85.5 |
| `log_norm_cdf` | `[−5, 5)` | 195.08 | 175.82 | 168.06 | 158.50 | 157.16 | 1.24× | 212.9 |

Every workload, including the broad, screened, subnormal, mixed and
fallback-only ones, is in `summary.csv`. The dispatched cascade runs AVX-512F
on whole chunks of 8, then AVX2, then SSE2, so at 4,096 elements it matches
AVX-512F.

## Observations

These are observations on this host, not general claims.

- **Exponential family.** The exponential family and `ln_1p`'s common range
  gain 1.8–4.6× dispatched, and each wider backend is faster.
- **`ln` and `ln_1p` fallbacks on AVX2 and AVX-512F.** Arguments decided by
  the shared double-word fallback run 2–3× *slower* than scalar on AVX2 and
  AVX-512F (`ln` near 1, `ln_1p` beyond `2^1020`), while SSE2 is faster than
  scalar. In this build those fallbacks are `#[inline(never)]` functions
  outside the backend's target-feature wrapper. On AVX2 and AVX-512F, the
  disassembly shows about 200–300 out-of-line calls to the backends' lane
  helpers per chunk. SSE2 is enabled for the whole x86-64 target, so its
  helpers inline. Results are bit-identical, so no test saw this.
  Tracked in #162.
- **`ln` common path.** It gains little (1.27×), and SSE2 is slower than
  scalar. Unlike `ln_1p`'s, `ln`'s screen is per lane and builds its lane mask
  by storing words and reloading them as one vector. Tracked in #162.
- **Fallback-dominated workloads on AVX-512F.** When the work is almost all
  scalar fallback (`*_fallback`, `exp`/`exp2` subnormal, the normal
  underflow), AVX-512F dispatch is about 15% slower than SSE2 or the scalar
  loop, for every function. Examples: `exp` fallback 283 ns scalar against
  327 ns AVX-512F; `norm_cdf` fallback 3,727 against 4,359 ns. The lane work
  there is negligible. Cascade Lake lowers its clock while 512-bit
  floating-point instructions run, which would slow the scalar fallback that
  follows. That is a hypothesis: frequency was not recorded per sample.
- **`erfcx`.** The table region gains 1.6× on every backend. AVX-512F is
  within noise of AVX2 (`table` spread 25%), because the per-lane reduction
  and 13 coefficient loads dominate. Its negative region gains 1.34×.
- **Screened inputs.** When every lane is NaN, infinite, zero or otherwise
  screened, dispatch runs the vector stage anyway before the scalar function.
  That costs 2–11 ns per element where scalar takes 1–3. Mixed workloads
  include such lanes.
- **Standard-normal family, 1,024 ordinary inputs.** `pdf` 3.58×, `cdf` 3.92×,
  `ccdf` 3.58×, `centered` 3.39×, `log_cdf` 2.17×; mixed 1.58–4.41×
  (`normal-summary.csv`). Accurate-fallback counts are as on NEON.
  Underflow workloads, which are dominated by Q256, run at 0.85×.

## Short slices and dispatch overhead

The ratio is ns per call, dispatched over scalar loop:

| Length | 1 | 2 | 3 | 4 | 8 | 16 | 17 |
|---|---:|---:|---:|---:|---:|---:|---:|
| `exp` | 1.27 | 0.81 | 0.90 | 0.85 | 0.75 | 0.65 | 0.75 |
| `exp2` | 1.23 | 0.86 | 0.90 | 0.64 | 0.46 | 0.40 | 0.48 |
| `ln` | 1.27 | 1.23 | 1.22 | 1.04 | 0.94 | 0.86 | 0.90 |
| `ln_1p` | 1.35 | 1.12 | 1.08 | 0.77 | 0.52 | 0.50 | 0.55 |
| `erfcx` | 1.13 | 0.70 | 0.84 | 0.71 | 0.68 | 0.65 | 0.67 |
| `norm_cdf` | 1.03 | 0.69 | 0.80 | 0.55 | 0.44 | 0.41 | 0.46 |

- A one-element slice costs 2.1–2.8 ns more than one scalar call, for every
  function. This is the dispatch and call overhead.
- From two elements up, the cascade's SSE2 pairs beat the scalar loop for
  every function except `ln` and `ln_1p`, whose SSE2 lanes are slower than
  scalar here.
- Odd lengths pay one scalar remainder.
- The standard-normal short lengths are in `normal-summary.csv`. Length 1
  costs 0.88–1.00×. Length 2 gains 1.3–1.7× on ordinary inputs, but mixed
  pairs fall back to scalar (0.92–0.95×).

## Fallback rates

`paths.csv` counts the deciding stage for each workload's 4,096 pooled
arguments. Examples:

- `exp` `[−30, 0)`: stage A decides 4,069 and stage B 26; 1 goes to the
  accurate path.
- `ln` `1 ± 2^−47`: 3,655 fast, 318 accurate.
- `ln_1p` beyond `2^1020`: 4,089 fast, 7 accurate.
- `erfcx` table region: 1 of 4,096 accurate.
- The `fallback` workloads are 4,096 of 4,096 accurate by construction. Each
  is drawn from an argument search of up to 2^27 candidates; `paths.csv`
  records how many distinct ones it found.

The timings above are of uninstrumented builds. The classifiers run outside
timing.

## Compositions

`log-space-summary.csv`, with `simd` and `std`, per call or pair:

| Workload | ns |
|---|---:|
| `log_sum_exp`, `n = 2` | 37.1 |
| `log_sum_exp_pairs`, `N = 2` | 34.7 per pair |
| `log_sum_exp_and_normalize`, `N = 1` | 48.9 per pair |
| `log_sum_exp` and a separate normalization | 64.8 per pair |
| `log_diff_exp` | 30.9 |
| `log_sum_exp`, `n = 1000` | 12.8 per element |

The fused sum-and-normalize is 1.33× faster than the separate pair here.

The external-consumer benchmark (`consumer-summary.csv`) calls the public
scalar and slice APIs from a separate crate on 1,024 ordinary inputs:

| Function | Scalar | Slice |
|---|---:|---:|
| `pdf` | 38.3 | 9.1 |
| `cdf` | 68.8 | 16.7 |
| `ccdf` | 68.5 | 17.6 |
| `centered` | 72.0 | 19.7 |
| `log_cdf` | 153.9 | 69.4 |

These match the in-crate kernel timings within a few percent, so the public
cross-crate call adds no visible cost on this host. Compiler flags were
`-O -C codegen-units=1` with no target features.

## Tables and cache

The table footprints measured at this revision (`paths.csv`, `table` records)
total 70,152 bytes. On the fast paths:
- `exp`: `S_T` 8 KiB and `T_BITS` 2 KiB;
- `ln`: `stage_tables::T` 8 KiB, `R` 4 KiB and `EL` 2 KiB;
- `erfcx`: `T` 18 KiB.

The accurate-path tables add `exp`'s `T_Q128` 2 KiB, `ln`'s `NEG_LN_R_Q128`
4 KiB and `erfcx`'s 16 KiB.

`cache.csv` times `exp`, `ln` and `erfcx` on 64-element calls, alone and
interleaved. Each call is followed by a walk of 64 cache lines (4 KiB) through
a competing buffer of 0 to 32 MiB. The walk alone costs about 3.5 ns per
element from 16 KiB to 4 MiB and 4.6 ns at 32 MiB, which is beyond L3. Beyond
the walk's own cost, the kernels lost:

- `exp` and `ln`: 0.2–0.4 ns per element;
- `erfcx`: 0.85 ns, with the largest table;
- interleaved: about 0.2 ns.

That difference was flat from 16 KiB to 4 MiB, with no step at the L1 or L2
size. With this much competing traffic per call, table eviction is a small
cost on this host. More traffic per call, or other cache hierarchies, were not
measured.

## Outstanding

- **Other x86 microarchitectures.** Only Cascade Lake was measured.
  AVX-512F behaviour in particular differs on other cores.
- **The AVX-512F frequency hypothesis** needs per-sample frequency counters.
- **The proposed changes** are tracked separately: #162 covers the defects
  above, and #163 the remaining costs (all-screened chunks, one-element
  dispatch, AVX-512F on fallback-heavy work, `erfcx`'s table reduction, other
  cores).
