# Combined quartic-source ARM qualification

Source **`c9cb6814a2c693f3ea4835e6ab27e7da8dba7b6a`** passes **125/125 required cells** in the declared 163-cell matrix; all 38 diagnostic cells were measured. Every one of 6,520 timed observations exceeds 250 ms; the minimum is **309.223 ms**. There are 6,520 excluded warmups and 1,630 fresh measured processes. No sample was discarded or replaced. The largest required one-sided 95% upper time ratio is **0.987524515**, for length-nine erfcx slice. Total campaign wall time including calibration and block gaps was 69.65 minutes.

The owner selected the latest published code available at launch: ec1 plus both Gaussian structural fixes. Upstream subsequently added a direct-domain CDF exp entry (`043047f`) and then a new 1024-entry constrained-cubic exp algorithm (`d32c2d7`). **This packet qualifies neither later source.** Its numerical and timing results remain tied to the frozen combined quartic candidate. Integration/source synchronization is tracked in #194.

| Ordinary 52-value public call | Reference | Paired speedup | Upper95 time ratio |
| --- | --- | ---: | ---: |
| prod_exp_slice | sleef_exp_neon | 2.182x | 0.471999 |
| prod_erfcx_slice | libcerf_erfcx | 1.331x | 0.784019 |
| prod_norm_cdf_slice | sleef_cdf_neon | 5.939x | 0.170602 |
| prod_exp | core_math_exp | 1.508x | 0.669739 |
| prod_exp | sleef_exp_scalar_fma | 1.616x | 0.635638 |
| prod_erfcx | libcerf_erfcx | 1.159x | 0.865815 |
| prod_norm_cdf | scipy_ndtr | 1.335x | 0.750938 |

The full matrix, same-host pinned references, numerical contracts and diagnostic classifications are the parent packet's. Scheduling places exp lengths 14/15/16 alongside the prior 21 critical Gaussian/latency cells (24 first), then 139 remaining. The acceptance rule is unchanged: ten fresh processes per cell in two blocks of five; two alternating paired rounds/process; process-median log ratio; one-sided Student-t 95% upper bound at most 1.0 for every required cell; 350ms calibration target, 250ms minimum measured duration. Absolute spread/block drift are diagnostic, not a 3% gate. Confidence bounds are pointwise rather than simultaneous familywise claims. Raw data and all diagnostic losses remain in the archive.

The previously flagged exp length 15 passes with mean time ratio 0.524531 and upper95 ratio 0.526296; its earlier short-screen anomaly and separate diagnostic attempts remain preserved in the sibling integration-screen packet. The closest dependent CDF pair passes with upper ratio 0.983816. This is an actual completed qualification run, not conversion of a short-screen result to acceptance.

All 64,496 retained independent 256-bit mathematical oracle cases and 16,116 expanded-bank cases pass unchanged bounds with no scalar/slice mismatch. Maximum replay errors are exp 3.0793794411e-16 relative, erfcx 2.8432637882e-16 relative and CDF 3.9085126779e-16 absolute, below relative 2^-51 and absolute 2^-49. Historical x86 outputs differ for 12,021 exp and 983 CDF cases following the deliberate reconstruction change; erfcx has zero changes. Those old bits are diagnostic, not a same-source target comparison. Matching-source full cross-target assurance is separate.

Separate instrumentation reports zero Rust heap allocation calls in 156 cases, 211 matching strong-fallback observations and passing composition/dependency-chain checks. After timing, independent sampler captures for exp length 15, erfcx length 3 and dependent CDF all succeeded. Their full records are retained. Profiling, oracle checks and builds were outside timed windows. Whole-wrapper section/symbol footprint is recorded without attributing std/wrapper/strong-owner overhead to a single primitive.

Source, exact input, harness, production and actual linked composition dependency hashes were captured before calibration and verified unchanged after completion. This corrects the manifest-ordering defect documented in the preceding 3cb campaign. Native Apple M1 Pro/macOS, same pinned compiler/features/references and AC/QoS settings as the parent record. The OS remained unbound and user processes were untouched. Host load varied, with desktop activity and Spotlight indexing prominent in snapshots; no thermal/performance warning was reported by the sampled macOS command. No claim of isolation, fixed core/frequency or universal workload speed is made.

`observations.tar.gz` retains the entire frozen harness and exact inputs, calibration/warmup/timing samples, host snapshots, numerical observations, allocation wrapper source/build log, profiles, manifest, decision record and completed summary. `wrapper-receipt.tar.gz` retains the production wrapper source and separate build receipt. No dylibs, build products, external implementation source or Python environment are bundled. Reproduction uses the parent packet's pinned references and packages, the archived wrapper with its local dependency path adjusted to the exact clean source, and fresh output directories. Run freeze-manifest.py before timing; its recorded source/path must be updated for a new declared candidate. Keep every original result. The runner stops after a completed group if any required cost or duration criterion fails.
