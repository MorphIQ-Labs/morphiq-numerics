# Native x86-64 measurements after #162: Intel i9-10920X

This is the same harness, host, pinning and method as
[`lanes-x86-i9-10920x`](../lanes-x86-i9-10920x/README.md), at `d1e32d5`. That
commit's library and arch sources are byte-identical to the merged #162
change. It is three repetitions, taken a little over an hour after the
baseline with the host's CI runner still stopped; the 1-minute load average
was 1.0–1.8. `environment.txt` has the full record, and the files and
summaries have the same layout as the baseline's.

The change keeps `ln`'s and `ln_1p`'s uncommon paths inside the backend's
target-feature wrapper (`lanes::cold`), and computes lane masks in lanes
(`ln`'s screen, `mask_from`). Every result is unchanged: the bit-equality
checks ran before every timed mode, and `paths.csv` is identical to the
baseline's, workload by workload.

## Before and after, dispatched, 4,096 elements

All values are medians of 33 samples in ns per element (`summary.csv`
against the baseline's).

| Function | Workload | Scalar | Before | After | After/before | After vs scalar |
|---|---|---:|---:|---:|---:|---:|
| `ln` | `[0.5, 2)` | 9.05 | 7.17 | **3.07** | 0.43 | 2.95× |
| `ln` | positive encodings | 8.99 | 7.25 | **3.08** | 0.42 | 2.92× |
| `ln` | `1 ± 2^−47` | 86.9 | 171.9 | **36.5** | 0.21 | 2.38× |
| `ln` | subnormal | 48.1 | 11.63 | **7.94** | 0.68 | 6.06× |
| `ln` | mixed | 16.8 | 14.60 | 11.69 | 0.80 | 1.44× |
| `ln` | fallback only | 279.4 | 428.8 | 278.3 | 0.65 | 1.00× |
| `ln_1p` | `[2^1020, MAX]` | 96.8 | 184.8 | **27.3** | 0.15 | 3.55× |
| `ln_1p` | `e^d`, `d ∈ [−30, 0)` | 8.25 | 3.35 | 3.22 | 0.96 | 2.56× |
| `ln_1p` | fallback only | 345.8 | 521.6 | 341.4 | 0.65 | 1.01× |
| `ln_1p` | mixed | 7.0 | 8.35 | 8.63 | **1.03** | 0.81× |
| `ln_1p` | all screened | 3.0 | 10.19 | 10.72 | **1.05** | 0.28× |
| `expm1` | `[−30, 0)` | 11.16 | 3.83 | 3.56 | 0.93 | 3.13× |
| `expm1` | mixed | 11.2 | 7.20 | 6.46 | 0.90 | 1.74× |
| `exp` | fallback only | 274.3 | 335.7 | 316.3 | 0.94 | 0.87× |
| `erfcx` | `[−26.6, −0.5)` | 24.0 | 18.21 | 18.00 | 0.99 | 1.34× |
| `log_norm_cdf` | `[−0.5, 0.5)` | 209.3 | 57.62 | 59.73 | **1.04** | 3.50× |

On SSE2 alone, `ln` `[0.5, 2)` went from 12.49 to 6.87 ns, so it is now faster
than scalar. Two-element slices now beat the scalar loop for every function,
`ln` (0.91 of the scalar loop's time per call) and `ln_1p` (0.97) included.
The standard-normal functions other than `log_norm_cdf` central moved by 2%
or less.

## Every cell

Across all 6,864 timed lane cells (each function, workload, length and
backend), 1,045 got more than 5% faster and 119 more than 5% slower. For 93
of those 119, the minimum–maximum ranges before and after overlap. The 119
fall into these groups:

| Group | Cells |
|---|---:|
| All-screened workloads, where the code still runs the vector stage (#163) | 25 |
| Forced backends wider than the slice, which run only the scalar function, which did not change | 20 |
| Fallback- or underflow-dominated workloads, which are scalar Q256 work | 18 |
| Sub-nanosecond cells | 17 |
| Lengths up to 3 | 5 |
| Other | 34 |

The "other" cells are mostly short `exp` and `exp2` slices of 4–16 elements.
Their lane code did not change: they use `mask_from` only in stage B, on
under 1% of chunks. These differences are in the noise or layout of an
unchanged path, not a measured cost of the change. The `ln_1p` mixed, all
screened and `log_norm_cdf` central rows above are reported as small
slowdowns: they take the uncommon path on most chunks and pay `lanes::cold`'s
array conversions.

## Other benchmarks

- **`log_space`:** `log_sum_exp` at `n = 1000` went from 12.5 to 10.9 ns per
  element. The pair and normalization compositions moved by 1% or less.
- **`bench-batched`:**
  - `ln` `[0.5, 2)` went from 7.20 to 3.49 ns, `ln` `1 ± 2^−47` from 177 to
    45.7 ns, and `ln_1p` beyond `2^1020` from 180 to 29.3 ns.
  - Its `ln_1p` `e^d` median rose from 3.43 to 3.95 ns, but its three
    processes measured 3.39, 4.61 and 3.95 ns. The same processes' unchanged
    scalar loops also ran slower (`z²/4` at 11.39 against 8.7–9.0 ns), so this
    is drift between processes. The in-process sweep, which alternates modes
    within every round, measured 3.35 → 3.22 ns.
- **External-consumer standard-normal calls:** within 2%
  (`consumer-summary.csv`).
