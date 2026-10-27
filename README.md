# morphiq-numerics

Correctly rounded, target-independent binary64 numerics for Rust:
elementary functions, seeded random streams and the normal family. Every
function is derived from first principles, with machine-checked error
bounds.

> **Status: pre-release.** Nothing is on crates.io yet. Releases before 0.1
> are git tags only ([releases](https://github.com/MorphIQ-Labs/morphiq-numerics/releases)),
> which a consumer pins:
> `morphiq-numerics = { git = "https://github.com/MorphIQ-Labs/morphiq-numerics", tag = "v0.0.1" }`.
> 0.1.0 is reserved for the first crates.io release; its scope and the
> remaining work are tracked in its
> [epic](https://github.com/MorphIQ-Labs/morphiq-numerics/issues/100) and the
> repository's [milestones](https://github.com/MorphIQ-Labs/morphiq-numerics/milestones).

## Why

The platform math library's `ln`, `exp`, `sin` and `cos` are only faithfully
rounded, and glibc, macOS and musl round them differently. So:
- a seeded simulation doesn't reproduce across machines;
- results can't be checked bit for bit against an independent reference.

A correctly rounded function has exactly one right answer: the binary64
value nearest the exact result. Every target, and every independent
reference, returns the same bits.

## Principles

- **Accuracy and performance together:** each numerical API is evaluated
  against its declared error and cost requirements. Existing guarantees stay
  intact; the policy for explicit bounded-error `fast` APIs and the distinction
  from internal fast paths are in [AGENTS.md](AGENTS.md#explicit-approximation-apis).
  Numerical changes use an [accuracy/performance decision record](docs/numerical-decision-template.md).
  This policy does not imply that additional fast APIs are already exported.
- **Correctly rounded:** the result is the nearest binary64, ties to even,
  over the whole domain. Where that isn't yet proved, the proved bound is
  stated instead.
- **Target-independent:**
  - `no_std`, with no third-party dependencies and no platform libm;
  - batched functions that return the scalar functions' bits, in SIMD lanes
    with the opt-in `simd` feature ([docs/lanes.md](docs/lanes.md)), whose only
    `unsafe` code is the first-party `morphiq-numerics-arch` crate;
  - error-free transforms that are exact with or without FMA;
  - a determinism digest checked on every supported target
    ([docs/determinism.md](docs/determinism.md)).
- **Clean provenance:** everything here ships under MIT OR Apache-2.0 and
  lives in this repository. Algorithms come from published mathematics, or from
  vendored code under a compatible license with its notices kept, and every
  constant from a versioned generator. No copyleft code; see the
  [provenance policy](docs/PROVENANCE.md).
- **Evidence:**
  - bit-exact tests against an interval-arithmetic oracle (mpmath), exact
    integer arithmetic and published worst cases;
  - Sollya approximation bounds and Gappa error certificates, the Gappa
    certificates checked in Coq;
  - Coq proofs of the arithmetic contracts, each tied to the Rust code by an
    extracted transcription compared bit for bit;
  - every proof bound by hash to the source it describes.

## Tridiagonal systems

Reusable, allocation-free tridiagonal factorization and solves are available
under `linalg::tridiagonal` for strictly row-diagonally-dominant matrices.
`solve_many_into` batches interleaved right-hand sides with scalar-identical
SIMD across columns when the `simd` feature is enabled.
An optional certificate bounds the absolute residual and solution error;
see [the domain, ownership and numerical contract](docs/tridiagonal.md).

## License

Licensed under either of [Apache License, Version 2.0](LICENSE-APACHE) or
[MIT license](LICENSE-MIT), at your option.

The adapted Thomas recurrence retains its original MIT notice in
[THIRD_PARTY_NOTICES.md](crates/morphiq-numerics/THIRD_PARTY_NOTICES.md).

Unless you explicitly state otherwise, any contribution intentionally
submitted for inclusion in this project by you, as defined in the Apache-2.0
license, is dual licensed as above, without any additional terms or
conditions.
