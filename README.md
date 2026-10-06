# morphiq-numerics

Correctly rounded, target-independent binary64 numerics for Rust:
elementary functions, seeded random streams and the normal family. Every
function is derived from first principles, with machine-checked error
bounds.

> **Status: pre-release.** Nothing is published yet. The scope of release 0.1
> and the remaining work are tracked in its
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

- **Correctly rounded:** the result is the nearest binary64, ties to even,
  over the whole domain. Where that isn't yet proved, the proved bound is
  stated instead.
- **Target-independent:**
  - `no_std`, with no dependencies and no platform libm;
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

## License

Licensed under either of [Apache License, Version 2.0](LICENSE-APACHE) or
[MIT license](LICENSE-MIT), at your option.

Unless you explicitly state otherwise, any contribution intentionally
submitted for inclusion in this project by you, as defined in the Apache-2.0
license, is dual licensed as above, without any additional terms or
conditions.
