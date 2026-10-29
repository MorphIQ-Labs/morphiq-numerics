# Shared benchmark cost tooling

The maintained GCP cost model, rate card and analysis moved to
[ai-program/scripts/benchmarking](https://gitlab.com/prophetizo/morphiq-labs/org/ai-program/-/blob/925c77178941ec86bdfe5eb13c4c666890b46ce6/scripts/benchmarking/COSTS.md)
under the [canonical benchmarking program](https://gitlab.com/prophetizo/morphiq-labs/org/ai-program/-/blob/925c77178941ec86bdfe5eb13c4c666890b46ce6/BENCHMARKING.md).
[ai-program !81](https://gitlab.com/prophetizo/morphiq-labs/org/ai-program/-/merge_requests/81)
owns that change; [ai-program #17](https://gitlab.com/prophetizo/morphiq-labs/org/ai-program/-/issues/17)
owns shared cloud delivery. Numerics does not maintain a second rate card or
cloud lifecycle implementation.

From an authorized checkout of that reviewed revision:

```sh
python scripts/benchmarking/cost.py --machine c3-standard-8 --hours 8
```

Eight hours is only an illustrative allocation, not a requirement or measured
ETA. Use this adapter's `bootstrap` once and `plan` for `full`, `smoke` or an
explicit subset. The plan reports selected cells and target timed work; measure
preparation, calibration, observation and runtime overhead before choosing the
whole-VM budget. Canonical comparisons remain part of the selected workload.

The organizational estimator is optional. The public native runner, project
inputs, contracts and qualification evidence work without private repository
access. No resources are provisioned by the estimator or this adapter.
