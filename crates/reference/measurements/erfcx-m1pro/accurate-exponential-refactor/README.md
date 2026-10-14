# Accurate reflected-exponential helper

The baseline is `5451204`; the candidate factors the unchanged Q256 exponential
operation sequence into `reflected_exponential` so its proof transcription can
be compared directly with Rust. `environment.json` binds the candidate source.

Both variants force the complete accurate negative path on 4,096 evenly spaced
inputs from -0.5 toward -26.6. Each process warms the same inputs once before
measuring a single pass. `rounds.csv` contains 31 alternating baseline/candidate
process pairs; timing excludes process startup. `benchmark.rs` is the exact
ignored unit benchmark appended to `erfcx/tests.rs` in isolated snapshots.
Both use `cargo test --release --locked -p morphiq-numerics --lib --features
simd,std --no-run`; invoke the resulting test binary with
`erfcx::tests::measure_accurate_negative --ignored --exact --nocapture
--test-threads=1`.

Median nanoseconds per argument: baseline 3743.90; candidate 3747.28 (+0.09%).
Task-owned proof processes were paused during measurement. Unrelated host
activity and frequency/power settings were not controlled. These observations
establish no native x86 performance claim.

The refactor changes AArch64 register allocation and reduces the affected
accurate-path stack frame from 432 to 400 bytes. Instruction identity is not
claimed. Correctness is checked independently by fixtures, determinism, and
extracted Q256-field comparisons.
