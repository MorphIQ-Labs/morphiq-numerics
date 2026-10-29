# Fast primitive benchmark methodology

The reproducible ARM and x86 procedure, harnesses, deterministic input generators,
reference pins and decision rule live in
[`scripts/bench_fast`](../../scripts/bench_fast/README.md).

Generate measurements under ignored `target/`; retain complete runs through
review. Record conclusions and limitations in the owning issue/PR, including
[#194](https://github.com/MorphIQ-Labs/morphiq-numerics/issues/194) and
[#240](https://github.com/MorphIQ-Labs/morphiq-numerics/pull/240).
Historical run files remain accessible in Git history; this cleanup does not
rewrite history or change any numerical contract, fixture or proof.
