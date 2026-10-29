# QdFp-driven fast primitive observations, 27 October 2026

Preliminary native Apple M1 Pro observations, Rust 1.97.1, macOS 27.0.1.
`manifest.json` binds the measured source files, binary, build mode and archived
observations. The base is b131d7c4491f090e181c935154fa31f4a65e9e9d; the measured
source snapshot contains the new APIs, not that base commit alone.

`observations.tar.gz` retains exact inputs, independent rounded fixtures,
scalar/slice results, unsuccessful builds, previous candidates, raw packet
samples, host observations and consumer summaries. `primitive-summary.json`
reports medians and observed ranges. Timing modes are strong scalar, fast
scalar, strong slice and fast slice (0–3); each packet has 52 values.

| Primitive | Strong slice | Fast slice | Fast target in accelerated domain |
| --- | ---: | ---: | --- |
| exp | 112.7 ns | 86.8 ns | Relative error 2^-51 |
| erfcx | 287.9 ns | 236.7 ns | Relative error 2^-51 |
| CDF | 906.3 ns | 367.2 ns | Absolute error 2^-49 |

Domains and derivations are in [fast.md](../../fast.md). These workloads use
exp discount arguments [-0.2,0.2], erfcx [0,6], and CDF [-3,3]; they do not
establish whole-domain or competitor parity. The measured scalar/slice grids
have 65,537 inputs per workload. Exact fixture observations include 4,286 exp,
2,626 erfcx and 4,501 CDF rows, with no sampled accelerated-domain bound failures
including rounded-reference uncertainty. CDF's maximum observed error is
1.67e-16 absolute; a 16-ULP observation illustrates why its declared metric
matters. A separate 32,812-point consumer MPFR audit also stays within that
absolute maximum. Scalar/slice observations agree on the measured host.

The shared consumer experiment in Risk draft MR !707 replaces only FP-B CDF
packets and geometry discounts. Its final paired campaign measures 73.4 µs
ordinary prices versus 84.8 µs with the internal primitives, and passes all
323 independent screened price references. A live QuantLib 1.41 comparison
on 12 ordinary cases measures 79.4 µs versus 163.3 µs for matched six-sweep
parameters, with maximum price difference 1.15e-14. Calling interfaces differ:
native Rust warm prices versus Python-bound C++ forced recalculation. QuantLib
agreement is separate from independent oracle qualification.

The shared erfcx lane kernel formerly materialized a second coefficient array.
Consumer profiling resolved 23.35% of sampled CPU to an out-of-line 208-byte
copy. Direct coefficient loads remove that helper while retaining the same
arithmetic and all 465 measured price/refusal identities; ordinary consumer
latency falls 21.7% in the paired comparison. Full traces, instruction/symbol
resolution and all per-case price/error/timing data are retained in Risk's
`crates/morphiq-risk/docs/qdfp-prototype-evidence/shared-numerics.tar.gz` and its
manifest. This is why primitive and consumer timings are separate evidence.

No local CI ran. This draft is not release-qualified: formal entry proofs and
source bindings, explicit fast cross-target digest coverage, remote correctness
gates and the complete native comparator matrix remain required. The existing
strong API contracts are unchanged. Bounds are derived candidate contracts,
not claims proved by the sampled maxima. Production consumers retain release
pins; the experiment uses an isolated archive of unreleased source.

Reproduction: build `bench-fast-primitives` with the manifest's command; run
it without arguments for packet timings or with `fast-reference-inputs.txt`
for observations. `analyze.py expected.json observed.csv summary.json` compares
the retained independent rounded references including uncertainty. The archive
keeps prior experiments explicitly named; `fast-direct-load-*` is the retained
implementation.
