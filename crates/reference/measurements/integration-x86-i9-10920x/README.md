# Native x86 integration comparison

Intel Core i9-10920X, Rust 1.97.1, CPU 14, performance governor,
2026-10-16. SIMD dispatch selects native SSE2/AVX2/AVX-512; scalar builds
use their default non-FMA path. Other CI jobs share the host. The local
proof build is restricted to CPUs 4–7; sampled load and CPU 2/14 counters
record contention rather than assuming an idle sibling.

Two separate controls are necessary: `472c0367` is the validated central
stack, while `2f5ae140` is the validated finite-tail/log-table stack. Neither
contains the complete integration. `503a7ea` combines those stacks with
cold-lane dispatch. Each executable links distinct library/arch identities,
alternates variants within each round, and checks scalar/batch result bits
before timing. Three processes retain eleven rounds per cell after warm-up,
with at least 5 ms per sample. Central lengths are 1, 2, 3, 4, 8, 17 and
1,024; tail lengths are 1, 2, 8 and 1,024. Both scalar and batch modes are
included. Tail comparisons now require cross-variant equality in every pool,
not just ordinary inputs, since both revisions contain the same tail paths.

The initial `central/` comparison exposed a repeatable central CCDF batch
cost: 7.267 to 8.030 ns at length 1,024. The integrated kernel did far-tail
routing and scalar lane screening before its central first stage. The
`dispatch/` experiment (`b7728d0`) moves the fully guarded, all-or-nothing
central decision to vector entry. `ed639c4` also skips tail-mask setup when
no lane has magnitude above 37. Both preserve the original arithmetic and
fall back for the whole central chunk when any lane rejects. The shared
CDF/CCDF/centered entry and PDF/CDF/log-CDF routing cover the sibling paths.

Final comparison, nanoseconds per input at length 1,024:

| Control | Function/workload | Mode | Before | Integrated |
| --- | --- | --- | ---: | ---: |
| central | CDF / central | batch | 7.725 | 6.073 |
| central | CCDF / central | batch | 7.910 | 5.334 |
| central | centered / central | batch | 8.894 | 7.483 |
| tails | PDF / negative far tail | batch | 23.197 | 23.185 |
| tails | CDF / negative far tail | batch | 31.806 | 31.934 |
| tails | log-CDF / negative far tail | batch | 7.734 | 7.723 |
| tails | log-CDF / negative far tail | scalar | 13.876 | 14.163 |

The complete matrices include costs as well as gains. Against the central
control, length-two tiny log-CDF is 72.724 to 76.827 ns and length-four
central PDF is 14.641 to 17.105 ns. Long ordinary CDF/CCDF batches are 0.5%
and 2.7% slower. Against the tail control, saturated scalar CCDF is 1.682
to 3.119 ns. Unchanged scalar paths also vary across linked builds and
sample groups (including opposing shifts in ordinary centered CDF), so
these measurements do not isolate every small difference to the vector
routing change. They establish the central dispatch improvement and retain
the observed short-batch and saturation costs; they do not establish
uniform performance parity or close the broader performance issues.

All six final runs pass every scalar/batch bit comparison. The final source
passes full workspace tests, Clippy and the code-generation gate: 29 AVX2
and 29 AVX-512 kernels, no out-of-line lane arithmetic. Full cross-target,
certificate and formal CI must pass on the landing head separately.

`central/` and `tails/` retain the initial integration measurements;
`dispatch/` retains the intermediate experiment. `final-central/` and
`final-tails/` measure `ed639c4`. Exact revisions are in `environment.json`.
Every directory contains its build script, harness, raw samples and summary.
Compilation completed before timing. `host-load.csv` covers the initial
comparisons; `dispatch/host-load.csv` covers the intermediate experiment;
`final-host-load.csv` covers the final comparisons.

Reproduce from the repository root, fetching the original PR heads if the
historical objects are absent:

```sh
git fetch origin pull/165/head pull/186/head pull/188/head
python3 crates/reference/measurements/integration-x86-i9-10920x/final-central/build_paired.py target/integration-central
for run in 0 1 2; do
  taskset -c 14 target/integration-central/paired > "central-$run.csv"
done
python3 crates/reference/measurements/integration-x86-i9-10920x/summarize.py target/integration-summary central-0.csv central-1.csv central-2.csv
```

Use the corresponding directory's build script for the other comparisons.
Remove generated archive/build directories after measurement.
