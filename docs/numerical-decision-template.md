# Numerical decision: <function / path / change>

<!-- Fill in the owning derivation or retained evidence record; this form is
not an implementation plan or a second policy. AGENTS.md's Explicit
Approximation APIs and Performance Evidence sections own the requirements.
For prose-only work, state why no numerical result or runtime cost changes. -->

## Contract and consumer purpose

- Function, exact definition, required outputs and supported regions:
- Existing guarantee preserved or explicit new `fast` API contract:
- Practical consumer need and justification for the selected accuracy:

| Region / output | Absolute, relative or ULP bound | Special values / determinism | Cost budget and comparator | Justification |
| --- | --- | --- | --- | --- |
| <region> | <units and behavior near zero> | <including scalar/SIMD agreement> | <latency/throughput/work, hardware> | <mathematics and consumer needs> |

Record acceptance criteria before measuring: workload/hardware cells,
repetitions, stability/uncertainty rule and stopping condition. Identify what
consumer composition must be qualified separately; primitive accuracy alone
does not establish derivative, inverse or end-to-end accuracy.

## Fast path and escalation

| Path | Domain or acceptance certificate | Guaranteed contract | Refinement limit and next action | Unestablished-result behavior |
| --- | --- | --- | --- | --- |
| <path> | <proof/source binding> | <strong or explicit fast contract> | <bounded work> | <documented semantics> |

Identify runtime checks versus offline validation. Explain any added check,
additional precision or fallback using the contract obligation it establishes.

## Paired evidence

- Profiled hotspot, share of consumer cost and investigation stopping condition:
- Specialization assumptions (constants, input bounds), boundary/overflow behavior and proof:
- Exact source/toolchain/features/backend/comparator versions and input bits:
- Generated-code inspection commands, actual call context and findings by target:
- Separate throughput/latency criteria where applicable; consumer measurement used to select the candidate:
- Independent reference, provenance and reference uncertainty:
- Bound certificates, generated constants, worst-case and boundary witnesses:
- Versioned reproduction commands/input generators; source/comparator pins and host state:
- Raw timing/error results and failed attempts available through review (outside Git):

| Candidate / region | Proved bound | Observed error | Latency/spread and throughput | Fast-path/fallback rate and cost | Outcome |
| --- | --- | --- | --- | --- | --- |
| <strong/fast candidate> | <domain and certificate> | <with reference uncertainty> | <scalar, batch, interface> | <ordinary, difficult and mixed lanes> | <meets both / rejected / unestablished> |

Retain refusals and failed attempts through review; record the decision and
limitations in the owning issue/PR. Raw runs need not be permanently committed.
Separate dependent latency from throughput,
instrumented diagnostics from native timings, and unlike contracts/interfaces.
Include consumer results separately when a consumer adoption is claimed.

## Selection and review

- Selected implementation/settings and why further accuracy is unnecessary or required:
- Rejected alternatives, limitations and re-evaluation trigger:
- Compatibility/default implications; no implicit change to an existing API:
- Existing APIs benefiting from exact-result optimization; justification for any new backend variant:
- Exact CI witnesses and native measurement/review evidence; missing evidence:
- Reviewer/owner disposition, date and source revision:

This form does not expose a new API or certify a result by itself. The exported
API remains the library's `lib.rs`; guarantees remain those of each function.
