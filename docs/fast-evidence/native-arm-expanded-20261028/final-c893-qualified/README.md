# Completed combined-source ARM qualification

Source **`c89351345ca83006ab0f9926b957e72daefeb356`** passes **125/125 required decisions across all 163 cells**. All 38 diagnostic cells are retained, including unfavorable ratios. Every one of 6,520 timed observations exceeds 250 ms; the shortest is **587.775 ms**. There are 6,520 excluded warmups and 1,630 fresh measured processes. No measured sample was removed or replaced. The largest required one-sided 95% upper time ratio is **0.981221522**, for dependent scalar CDF versus SciPy ndtr (cell 157). Timing lasted **115.81 minutes**, including calibration and block gaps. All 30 GitHub checks passed on this exact source, including formal proofs and cross-target determinism.

| Ordinary 52-value public call | Reference | Paired speedup | Upper95 time ratio |
| --- | --- | ---: | ---: |
| prod_exp_slice | sleef_exp_neon | 2.521x | 0.398137 |
| prod_erfcx_slice | libcerf_erfcx | 1.295x | 0.779414 |
| prod_norm_cdf_slice | sleef_cdf_neon | 6.337x | 0.158204 |
| prod_exp | core_math_exp | 1.470x | 0.704542 |
| prod_exp | sleef_exp_scalar_fma | 1.639x | 0.614835 |
| prod_erfcx | libcerf_erfcx | 1.174x | 0.863537 |
| prod_norm_cdf | scipy_ndtr | 1.472x | 0.711853 |

The complete matrix is in cells.csv; raw observations and exact bank inputs are in observations.tar.gz. References, contracts and declared diagnostic classifications follow the parent manifest: pinned CORE-MATH, SLEEF 3.9.0, libcerf 3.1 and SciPy 1.16.3 on the same native Apple M1 Pro host. The cellwise acceptance rule is ten fresh processes in two blocks of five, two alternating paired rounds per process, process-median log ratios and a one-sided 95% Student-t upper ratio <=1.0 for every required cell. These are pointwise intervals, not a simultaneous familywise guarantee. Absolute spread and block drift are retained diagnostics; there is no 3% gate or allowed slowdown.

## Calibration correction and retained failures

The preceding 7b76da5 run could not qualify because calibration under contention reduced iteration counts, then lower contention produced measurements below 250ms. That complete failed attempt remains in the sibling cubic-7b76-duration-failure packet. The earlier 460315a interruption remains separately retained. Neither run's samples are used in this acceptance estimate.

The declared correction targets 600ms, takes iteration floors from the fastest call rates across every retained timed observation in the failed run, then uses three approximately 100ms pilots and a confirmation that can only increase counts. Historical data supplies a duration floor only. The source rows, their hashes, formula, every pilot/confirmation and each frozen count are retained. Counts remain fixed during measurement. A duration failure would stop at the next completed process round; confidence decisions occur only after full declared groups. The unchanged 250ms minimum and confidence rule both pass here. This is a materially corrected protocol on the reconciled source, not an unchanged-protocol retry-to-pass.

## Numerical and implementation observations

All 64,496 independent 256-bit oracle cases and 22,290 expanded-bank cases pass the unchanged per-function bounds, with no scalar/slice mismatch. Exp boundaries cover the 1024-entry reduction. The oracle summary distinguishes old x86 bits from same-source target evidence: historical output changes are diagnostic only. Independent samples supplement, rather than replace, the whole-domain proofs and CI. Separate allocation instrumentation reports zero calls in 156 cases; 211 strong-fallback comparisons, composition and dependency-chain checks pass. Three post-timing profiles (exp length 15, erfcx length 3 and dependent CDF) completed successfully. Builds, oracles and profilers ran outside timed windows; no local full CI suite was run.

## Source and host scope

This candidate combines a8cc587's exp/oracle work with the previously disclosed Gaussian structural fixes. Those fixes preserve arithmetic but may change x86 code generation too. The subsequently published x86 runtime source fe6af560/evidence head b1bb429 is not automatically qualified by this packet. Source and compiled-target effects must be reconciled before declaring a single combined release candidate qualified. Native platform evidence is not substituted across different source/binary versions.

Source, inputs, harness, production library, actual linked composition dependency and allocation wrapper hashes verified unchanged after timing and again at packaging. All 30 GitHub checks passed on c893513; receipts are retained. Native Apple M1 Pro/macOS, pinned Rust toolchain and same features/interfaces as the parent record. Successful launch preflight did not isolate the host: later desktop, indexing, testing and OS activity remains in the host snapshots and in the measurements. No core/frequency pinning or universal-workload speed claim is made. Unrelated processes were not stopped.

The archive includes wrapper sources/build receipts, frozen harness, numerical observations, all calibration/warmup/timing rows, host records, post-timing profiles and CI receipts. It excludes binary/build trees, environments and external implementation sources. Runner stdout was streamed to execution session 58045; per-cell start/end metadata and host timestamps retain the complete phase chronology. Reproduction requires the pinned references/packages, an exact clean source checkout, adjusted local paths and fresh outputs; preserve original evidence and declare any protocol/source change before timing.
