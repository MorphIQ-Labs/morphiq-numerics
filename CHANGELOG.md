# Changelog

All notable changes to this project are documented in this file. Release
sections are written by the release automation (release-plz) from
conventional-commit subjects; never edit a released section by hand.

Releases before 0.1 are git tags only (`v0.0.N`), for consumers to pin; 0.1.0
is reserved for the first crates.io release
([#90](https://github.com/MorphIQ-Labs/morphiq-numerics/issues/90)).

## [Unreleased]

## [0.0.6](https://github.com/MorphIQ-Labs/morphiq-numerics/compare/v0.0.5...v0.0.6) - 2026-10-14

### Added

- *(normal)* add erfcx scalar and SIMD kernels ([#145](https://github.com/MorphIQ-Labs/morphiq-numerics/pull/145))

## [0.0.5](https://github.com/MorphIQ-Labs/morphiq-numerics/compare/v0.0.4...v0.0.5) - 2026-10-13

### Performance

- *(log-space)* specialize scalar two-term log-sum-exp ([#143](https://github.com/MorphIQ-Labs/morphiq-numerics/pull/143))

## [0.0.4](https://github.com/MorphIQ-Labs/morphiq-numerics/compare/v0.0.3...v0.0.4) - 2026-10-13

### Added

- *(ln)* prove fallback kernels and vectorize their evaluation ([#140](https://github.com/MorphIQ-Labs/morphiq-numerics/pull/140))

## [0.0.3](https://github.com/MorphIQ-Labs/morphiq-numerics/compare/v0.0.2...v0.0.3) - 2026-10-13

### Added

- *(formal)* complete expm1 small paths and entry proofs ([#138](https://github.com/MorphIQ-Labs/morphiq-numerics/pull/138))

## [0.0.2](https://github.com/MorphIQ-Labs/morphiq-numerics/compare/v0.0.1...v0.0.2) - 2026-10-12

### Added

- *(simd)* batch exp2 and expm1 with scalar-equivalent lanes ([#137](https://github.com/MorphIQ-Labs/morphiq-numerics/pull/137))
- *(formal)* prove expm1 general fallback bounds ([#136](https://github.com/MorphIQ-Labs/morphiq-numerics/pull/136))
- *(formal)* prove exp2 entry and fallback rounding ([#135](https://github.com/MorphIQ-Labs/morphiq-numerics/pull/135))
- *(formal)* prove exp2 fallback accurate value ([#133](https://github.com/MorphIQ-Labs/morphiq-numerics/pull/133))

### Performance

- *(elementary)* prove exp2 and expm1 exponential stages ([#131](https://github.com/MorphIQ-Labs/morphiq-numerics/pull/131))
- *(ln)* prove and vectorize the reciprocal first stage ([#130](https://github.com/MorphIQ-Labs/morphiq-numerics/pull/130))

## [0.0.1](https://github.com/MorphIQ-Labs/morphiq-numerics/releases/tag/v0.0.1) - 2026-10-12

### Added

- *(formal)* prove ln's accurate path end to end ([#117](https://github.com/MorphIQ-Labs/morphiq-numerics/pull/117))
- *(logspace)* log_sum_exp_pairs, log_sum_exp_and_normalize, and a lane backend cascade ([#116](https://github.com/MorphIQ-Labs/morphiq-numerics/pull/116))
- *(simd)* lane evaluation that returns the scalar bits ([#115](https://github.com/MorphIQ-Labs/morphiq-numerics/pull/115))
- *(formal)* prove ln's reduction ([#113](https://github.com/MorphIQ-Labs/morphiq-numerics/pull/113))
- *(formal)* prove exp's small-argument path end to end ([#112](https://github.com/MorphIQ-Labs/morphiq-numerics/pull/112))
- *(formal)* prove exp's accurate path end to end ([#111](https://github.com/MorphIQ-Labs/morphiq-numerics/pull/111))
- *(normal)* log_norm_pdf ([#109](https://github.com/MorphIQ-Labs/morphiq-numerics/pull/109))
- *(logspace)* log_sum_exp and log_diff_exp ([#106](https://github.com/MorphIQ-Labs/morphiq-numerics/pull/106))
- *(formal)* prove exp's fast path end to end ([#105](https://github.com/MorphIQ-Labs/morphiq-numerics/pull/105))
- *(formal)* prove exp's argument reduction ([#103](https://github.com/MorphIQ-Labs/morphiq-numerics/pull/103))
- *(formal)* prove the rounding test every kernel shares ([#102](https://github.com/MorphIQ-Labs/morphiq-numerics/pull/102))
- *(formal)* prove the Q128 and Q256 contracts ([#86](https://github.com/MorphIQ-Labs/morphiq-numerics/pull/86))
- *(random)* Box–Muller normal pairs, with a correctly rounded sqrt ([#83](https://github.com/MorphIQ-Labs/morphiq-numerics/pull/83))
- *(elementary)* sin, cos, sincos and tan, correctly rounded where the worst cases reach ([#82](https://github.com/MorphIQ-Labs/morphiq-numerics/pull/82))
- *(elementary)* expm1 within a proved bound, accurate as x → 0 ([#81](https://github.com/MorphIQ-Labs/morphiq-numerics/pull/81))
- *(elementary)* correctly rounded exp2 and log2, and log10 within its proved bound ([#80](https://github.com/MorphIQ-Labs/morphiq-numerics/pull/80))
- *(elementary)* correctly rounded ln and ln_1p ([#73](https://github.com/MorphIQ-Labs/morphiq-numerics/pull/73))
- *(exp)* correctly rounded exp ([#71](https://github.com/MorphIQ-Labs/morphiq-numerics/pull/71))
- *(double-word)* checked operations bound to each theorem's hypotheses ([#77](https://github.com/MorphIQ-Labs/morphiq-numerics/pull/77))
- *(reduce)* sums, dot products and sums of squares in a specified order, with Sum2 and Dot2 ([#69](https://github.com/MorphIQ-Labs/morphiq-numerics/pull/69))
- *(formal)* prove no double-word operation overflows, in IEEE 754 arithmetic ([#65](https://github.com/MorphIQ-Labs/morphiq-numerics/pull/65))
- *(formal)* prove the double-word divisions' bounds in binary64 ([#68](https://github.com/MorphIQ-Labs/morphiq-numerics/pull/68))
- *(formal)* prove the double-word products' bounds in binary64 ([#63](https://github.com/MorphIQ-Labs/morphiq-numerics/pull/63))
- *(formal)* prove the additive double-word bounds in binary64 ([#60](https://github.com/MorphIQ-Labs/morphiq-numerics/pull/60))
- *(formal)* machine-checked double-word bounds and two_prod exactness ([#58](https://github.com/MorphIQ-Labs/morphiq-numerics/pull/58))
- *(random)* SplitMix64 and xoshiro256++ streams with exact unit uniforms ([#53](https://github.com/MorphIQ-Labs/morphiq-numerics/pull/53))
- *(eft)* error-free transforms and double-word arithmetic ([#52](https://github.com/MorphIQ-Labs/morphiq-numerics/pull/52))
- *(ulp)* units in the last place and ordered-bits distance ([#51](https://github.com/MorphIQ-Labs/morphiq-numerics/pull/51))

### Other

- release tagging with release-plz ([#122](https://github.com/MorphIQ-Labs/morphiq-numerics/pull/122))
- remove PLAN.md; GitHub issues, epics and milestones are the record ([#101](https://github.com/MorphIQ-Labs/morphiq-numerics/pull/101))
- *(eft)* two_prod's domain is the proof's sufficient hypothesis ([#59](https://github.com/MorphIQ-Labs/morphiq-numerics/pull/59))
- determinism digest over every public function ([#55](https://github.com/MorphIQ-Labs/morphiq-numerics/pull/55))
- initial commit

### Performance

- *(elementary)* ln_1p fast path with an exact reduction and no division ([#119](https://github.com/MorphIQ-Labs/morphiq-numerics/pull/119))
- *(elementary)* exp fast path in binary64 with a constant-bound rounding test ([#118](https://github.com/MorphIQ-Labs/morphiq-numerics/pull/118))
- mark the primitives inline for cross-crate callers ([#54](https://github.com/MorphIQ-Labs/morphiq-numerics/pull/54))
