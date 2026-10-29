# Numerics adapter for the shared benchmarking program

## Ownership decision

`ai-program` owns the [canonical benchmarking program](https://gitlab.com/prophetizo/morphiq-labs/org/ai-program/-/blob/925c77178941ec86bdfe5eb13c4c666890b46ce6/BENCHMARKING.md),
shared cost tooling and cloud-provider integration. Numerics supplies a workload
adapter. The public native runners and correctness evidence remain independently
usable; private program material and consumer workloads are not dependencies of
the library, its builds or local benchmark reproduction.

`scripts/bench_fast` owns exact input generation, native call interfaces,
calibration, pairing and qualification statistics. `scripts/bench_campaign`
orchestrates this domain-specific preparation and observation flow, records
source/reference identities, selects declared cells and preserves evidence. It
does not introduce another timing engine, statistical rule, cloud scheduler or
VM manager. Full cloud delivery is tracked in
[ai-program #17](https://gitlab.com/prophetizo/morphiq-labs/org/ai-program/-/issues/17);
Numerics adapter adoption and remaining native coverage are tracked in
[#245](https://github.com/MorphIQ-Labs/morphiq-numerics/issues/245).
#150 retains numerical methodology ownership and #243 release qualification.

For shared cloud lifecycle the selected substrate is external
[PerfKit Benchmarker at commit
`50bbc173d75696c867dc0be5a742e9906445f5e9`](https://github.com/GoogleCloudPlatform/PerfKitBenchmarker/tree/50bbc173d75696c867dc0be5a742e9906445f5e9).
Its provider lifecycle already covers temporary benchmark hosts. A handwritten
gcloud provision/poll/delete loop would duplicate that ownership; declarative
infrastructure alone would still need a campaign execution lifecycle. PKB stays
external, with its own licence, outside this repository and published crates.
There is no implemented provider launcher or upload/teardown guarantee here.

## Adapter contract

A bootstrap compiles wrappers and freezes the complete input/cell inventory.
It can supply several fresh attempts on the same configured host. The copy is
path-bound: native loader paths can still refer to original build outputs.
Keep the bootstrap and source/reference checkouts until dependent runs finish.

Choose `full`, `smoke`, or explicit `subset` coverage before observations and
freezing. Preserve the full matrix and its hash, original cell IDs, requested
filters, selected IDs and intentionally excluded IDs. Subset success never
claims full qualification. Each attempt recalibrates and keeps its own samples;
a bootstrap containing timing output cannot be reused as a fresh experiment.

Canonical references and baseline controls are separate comparisons. Each names
its source/version, actual binary identity, numerical guarantee, special values
and calling interface. Input domains, populations and backends travel with the
cell. Independent correctness observations precede timings; reference agreement
and sampled error do not establish a whole-domain proof.

The current matrix covers fast exp, erfcx and CDF versus canonical references
and x86 unchanged strong-path baseline controls. It does not establish a complete
strong-versus-canonical or general fast-before/after matrix. Strong and fast
contracts retain their own acceptance rules; no global 3% spread tolerance,
weaker numerical contract or favorable average replaces required per-cell
decisions.

The controller rejects changed frozen inputs/binaries, missing selected results,
duplicate cells, unsupported hosts and failed stages. Failed/partial attempts
remain inspectable. Stage process groups terminate on timeout/interruption.
SIGKILL, host loss or disk failure can prevent final receipts; an unfinished
receipt never becomes a successful result. Prepared state, selected success and
full qualification remain distinct in both records and documentation.

## Current platform boundary

The full x86 adapter requires native Linux with SSE2, AVX2/FMA and AVX-512F;
subset timing still uses the same prepared backend set. The ARM adapter requires
Apple Silicon/macOS, retains its scheduling limitations and uses original cell
IDs through selected groups. This does not establish ARM Linux support.

The shared cost estimator is maintained in ai-program; this repository retains
only a [pointer and adapter-specific usage](../../scripts/bench_campaign/COSTS.md).
Runtime budgets must come from selected work and measured overhead. The earlier
eight-hour example was an allocation scenario, not a harness requirement.
