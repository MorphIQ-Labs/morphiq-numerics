# Native ARM canonical-reference comparison, 28 October 2026

All seven frozen 52-value comparison pairs pass: the one-sided 95% upper confidence bound on every paired time ratio is below one. All 560 timed observations exceed 250 ms. No observations were discarded and no campaign retry was performed. Absolute spread/block drift are diagnostic under the owner's current decision; all happen to satisfy the historical 3% threshold in this campaign.

| Public fast API | Reference | Median ns / 52 (ours / reference) | Paired speedup | Upper 95% time ratio |
| --- | --- | ---: | ---: | ---: |
| prod_exp | core_math_exp | 150.46 / 225.89 | 1.502x | 0.666209 |
| prod_exp | sleef_exp_scalar_fma | 150.44 / 247.28 | 1.646x | 0.608829 |
| prod_exp_slice | sleef_exp_neon | 70.55 / 154.48 | 2.190x | 0.456811 |
| prod_erfcx | libcerf_erfcx | 153.25 / 177.82 | 1.161x | 0.861980 |
| prod_erfcx_slice | libcerf_erfcx | 138.09 / 177.81 | 1.287x | 0.777486 |
| prod_norm_cdf | scipy_ndtr | 339.04 / 406.16 | 1.198x | 0.835707 |
| prod_norm_cdf_slice | sleef_cdf_neon | 260.08 / 1524.73 | 5.866x | 0.170613 |

Shortest timed observation: 490.429 ms.

Speedup is the reciprocal of the paired geometric mean time ratio, not the ratio of separately reported medians. Lower time ratios favor Numerics. Ten fresh processes run in two blocks of five with a 30-second gap; each process has four paired rounds with alternating pair/implementation order. Per-implementation counts are frozen after excluded calibration targeting 500 ms, and an excluded half-count warmup precedes each observation. The uncertainty unit is the process: median four paired log ratios, then a one-sided Student-t bound across ten processes (9 degrees of freedom). Every pair must pass independently. These are pointwise bounds, not a simultaneous familywise confidence claim.

Source: `5aa5d4a116c8f8da3835d46d1cef94687ab26646`. Host: Apple M1 Pro, eight performance and two efficiency cores, 16 GiB RAM, macOS 27.0.1 / 26A434. Native Rust 1.97.1 with `simd,std`, release thin LTO and one codegen unit; cleared ambient Rust flags/wrappers. References use Apple clang 21.0.0 and upstream Release builds, with exact commands and hashes retained. AC power, low-power mode off, scoped idle-sleep prevention. The timing thread requests `QOS_CLASS_USER_INITIATED` successfully but remains unbound under macOS scheduling. There is no claim of fixed core, frequency, active temperature or an isolated OS. Host snapshots record load, power, thermal-warning status and process CPU activity outside timing. No builds, CI, numerical oracle or profiler ran concurrently with measurements; unrelated user services were not stopped.

The exact input bits are the preceding x86 packet: 52 values per primitive. SLEEF uses native two-lane NEON and explicit scalar remainders; scalar uses the FMA variants. CDF composition includes rounded scaling by `-1/sqrt(2)` and multiplication by 0.5. Measurements call the public Rust wrapper or pinned native reference through the native timer. Scalar C references use the same function-pointer loop; SciPy uses its native capsule with the extra dispatch argument fixed to one. Calling-interface and dispatch differences are included in the comparison.

Reference revisions and commands are in `manifest.json`. CORE-MATH has the stronger correctly-rounded exp contract; SLEEF exp uses u10 and erfc u15. Libcerf, SciPy and composed SLEEF are practical references with recorded sampled error observations; their guarantees do not establish Numerics' proved bounds, target identity or special-value semantics. No reference implementation source or binary is bundled.

After timing, the ARM build was replayed against the retained independent 256-bit mpmath references: 45,212 exp, 9,731 erfcx and 9,553 CDF cases. All 64,496 pass the unchanged relative 2^-51 exp/erfcx and absolute 2^-49 CDF bounds. Maximum observed errors are 2.1673e-16 relative, 2.8433e-16 relative and 3.9086e-16 absolute. ARM outputs match the retained x86 output bits on all these cases, and scalar/slice outputs agree, including additional boundary, special-value and remainder probes. This is sampled evidence, not a replacement for proof or full cross-target CI. No local CI/tests/lint/determinism suite was run.

`observations.tar.gz` contains raw calibration, warmup and timing observations; host snapshots; executed ARM harness/replay scripts; build logs (including corrected configuration/adapter build errors); library hashes; exact input bits; and numerical observations. Binary/reference/venv build products remain outside the archive. To reproduce, rebuild the pinned references and Rust wrapper, adjust its recorded local dependency path, and place the dylibs under `campaign/bin/` with the SLEEF major-version symlink. Use the recorded Python package versions. Extract the prior x86 observations alongside `campaign` as `upstream-packet` for accuracy replay. Start a new output directory for each campaign; `paired.py` refuses to overwrite existing process directories. Commands: `python run-campaign.py prepare`, then `caffeinate -i python -u run-campaign.py`, then `python replay-accuracy.py`. Recalibrate on the new host; preserve the original run.

The result is limited to these fast APIs, inputs, interfaces and native ARM host. It does not establish other distributions, batch lengths, dependency-chain latency, every backend, fallback-heavy populations, compositions or consumer performance. Those obligations remain in [#194](https://github.com/MorphIQ-Labs/morphiq-numerics/issues/194). No release or merge qualification is inferred from this packet alone.
