# morphiq-numerics

Target-independent binary64 numerics for Rust, with explicit numerical
contracts: correctly rounded results where established, proved error bounds
elsewhere, and a separate `fast` namespace for bounded approximations.

The library provides elementary and probability functions, log-space and
double-word arithmetic, seeded random streams, reductions, finite intervals,
and checked tridiagonal solves. It is `no_std`, allocates no heap memory,
forbids `unsafe`, and never calls a platform math library. Optional SIMD
backends preserve each API's scalar result bits.

> **Status: pre-release.** Nothing is on crates.io yet. Releases before 0.1
> are git tags only ([releases](https://github.com/MorphIQ-Labs/morphiq-numerics/releases)).
> 0.1.0 is reserved for the first crates.io release; its scope and the
> remaining work are tracked in its
> [epic](https://github.com/MorphIQ-Labs/morphiq-numerics/issues/100) and the
> repository's [milestones](https://github.com/MorphIQ-Labs/morphiq-numerics/milestones).

## Getting started

Rust **1.89 or later** is required. Pin a tagged release in `Cargo.toml`:

```toml
[dependencies]
morphiq-numerics = { git = "https://github.com/MorphIQ-Labs/morphiq-numerics", tag = "v0.0.22" }
```

```rust
use morphiq_numerics::{elementary, fast, normal};

// Strong APIs retain their individual numerical contracts.
assert_eq!(elementary::exp(0.0), 1.0);
assert_eq!(normal::norm_cdf(0.0), 0.5);

// Choose an approximation explicitly when its bound fits your error budget.
// fast::elementary::exp has relative error <= 2^-51 for |x| < 704.
let x = [-1.0, 0.0, 1.0];
let mut out = [0.0; 3];
fast::elementary::exp_slice(&x, &mut out);
for (input, output) in x.into_iter().zip(out) {
    assert_eq!(output.to_bits(), fast::elementary::exp(input).to_bits());
}
```

Slice functions are available without SIMD. To enable SIMD with runtime CPU
detection, add `features = ["simd", "std"]` to the dependency. Generate local
API documentation with `cargo doc -p morphiq-numerics --all-features --no-deps --open`.

## Available capabilities

The public modules are listed in [lib.rs](crates/morphiq-numerics/src/lib.rs).
The linked derivations state each API's domain, special values, bounds and
assurance limits.

| Module | Capabilities and contracts |
| --- | --- |
| `elementary` | `exp`, `exp2`, `expm1`, `ln`, `ln_1p`, `log2`, `log10`, `sin`, `cos`, `sincos`, `tan`, `sqrt`, `asin`, `asinh`, `atan2`; correct rounding on the established domains, stated bounds elsewhere. See the [API and derivation links](crates/morphiq-numerics/src/elementary.rs). |
| `normal` | Density, CDF, complementary and centered CDF, log-density, log-CDF, and scaled complementary error function `erfcx`; accepted rounding tests are correctly rounded, with bounded fallbacks. [Normal family](docs/normal.md), [log-density](docs/log_norm_pdf.md), [erfcx](docs/erfcx.md). |
| `fast` | Explicit bounded `exp`, `exp_coarse`, `ln`, `erfcx`, `norm_cdf`, and `log_norm_cdf`, each with a matching slice API. [Domains and bounds](docs/fast.md). |
| `bivariate_normal` | Bivariate normal CDF, bounded and batched forms, and a reusable per-correlation evaluator; an absolute error contract with explicit tail limitations. [Contract](docs/bivariate_normal.md). |
| `log_space` | Log-sums, log-differences, paired operations, and checked log-weight normalization with a returned error bound. [Arithmetic](docs/log_space.md), [normalization](docs/log_normalize.md). |
| `eft`, `double_word` | Error-free transforms on their stated domains, double-word arithmetic with proved bounds, and `DoubleWord::exp_split` with a separate binary exponent. [Contracts](docs/double-word.md). |
| `random` | Seeded SplitMix64 and xoshiro256++ streams, jump operations, exact unit uniforms, and Box–Muller normal pairs. [Contract](docs/random.md). |
| `reduce`, `ulp` | Ordered sums, dot products and sums of squares, compensated variants, and ULP utilities. [Reductions](docs/reduce.md), [ULPs](docs/ulp.md). |
| `interval` | Finite conservative outward enclosures and checked arithmetic, `ln`, `exp`, and `sqrt`, with typed domain/range failures. [Contract and proof boundary](docs/interval.md). |
| `linalg::tridiagonal` | Reusable Thomas factors and scalar/batched solves for dominant, sign-domain, and general checked unpivoted matrices; residual and solution-error certificates where supported. [Admission rules and certificates](docs/tridiagonal.md). |

## Choosing a numerical contract

Correct rounding means the nearest binary64 result, ties to even. It is claimed
only for the functions and domains where the evidence establishes it. Other
APIs publish absolute, relative or ULP bounds; the library does not promise
correct rounding for every operation.

The `fast::elementary` and `fast::normal` modules let callers choose bounded
approximations without changing the existing strong APIs. For example, on
`|x| < 704`, `fast::elementary::exp` guarantees relative error at most `2^-51`,
while `exp_coarse` admits `2^-38` for a shorter dependency chain. Outside an
accelerated domain, an entry delegates to its corresponding strong API and
inherits that API's bound and special-value behavior. See the full
[per-function contract table](docs/fast.md).

Scalar and SIMD results are bit-identical within each API; fast and strong
APIs may return different bits. Feature flags never weaken a numerical
contract. Choose bounds using the error budget of the composed computation,
including cancellation, tails and inverses.

## Features and platforms

| Features | Behavior |
| --- | --- |
| None (default) | `no_std`, no dependencies, scalar slice evaluation. |
| `simd` | Adds the first-party `morphiq-numerics-arch` dependency and lane backends enabled by compile-time target features. |
| `std` | Enables runtime CPU detection, including SIMD backend selection when combined with `simd`; requires the standard library. |

Lane backends cover ARM NEON and x86-64 SSE2, AVX2+FMA and AVX-512F, with scalar
fallbacks. The library forbids `unsafe`; the dependency-free
[architecture crate](docs/arch.md) confines intrinsics behind a safe,
CPU-capability-gated interface. No third-party dependency enters either
library crate.

The numerical operation sequences, specified fused multiply-adds and software
fallbacks preserve results across targets. Callers must retain the documented
[floating-point environment](docs/arch.md).
The [determinism corpus](docs/determinism.md) checks result bits on Linux,
macOS, Windows, musl, WebAssembly and bare-metal ARM, with additional SIMD
backend checks. These checks complement the per-function proofs and tests.

Performance targets are native aarch64 and x86-64 builds with hardware FMA
(`x86-64-v3` or later). Baseline x86-64, embedded and WebAssembly paths retain
their numerical contracts but are not performance targets. Measurements apply
only to the recorded host, workload, calling interface and contract; an API
name or SIMD backend does not establish universal speed or competitor parity.
See the [native benchmark procedure](scripts/bench_fast/README.md) and
[campaign harness](scripts/bench_campaign/README.md). Per-function evidence
records identify missing qualification, including native ARM measurements for
the latest [fast CDF implementation](docs/fast_cdf.md).

## Evidence and provenance

Independent oracle tests use MPFR/mpmath, exact integer or rational arithmetic,
and published worst cases. Approximation and rounding bounds use Sollya,
Gappa and Coq where specified by each derivation. Proof artifacts are bound
to their source inputs by hashes, and generators reproduce coefficients,
constants and fixtures.

Proof coverage is explicit: many kernels have extracted Coq transcriptions
compared bit for bit with Rust; other components combine mathematical proofs
with reviewed correspondence and independent tests. For example, the interval
propagation proof is not an extracted verification of Rust control flow.
Sampling and cross-target digests do not replace whole-domain error proofs.

Algorithms come from published mathematics or compatible licensed code with
its notices retained. See the [provenance policy](docs/PROVENANCE.md),
[contributor guide](CONTRIBUTING.md), and [engineering contract](AGENTS.md).
Scope and remaining work live in GitHub issues and milestones.

## License

Licensed under either of [Apache License, Version 2.0](LICENSE-APACHE) or
[MIT license](LICENSE-MIT), at your option.

The adapted Thomas recurrence retains its original MIT notice in
[THIRD_PARTY_NOTICES.md](crates/morphiq-numerics/THIRD_PARTY_NOTICES.md).

Unless you explicitly state otherwise, any contribution intentionally
submitted for inclusion in this project by you, as defined in the Apache-2.0
license, is dual licensed as above, without any additional terms or
conditions.
