# morphiq-numerics

Correctly rounded, target-independent binary64 numerics for Rust:
elementary functions, seeded random streams and the normal family. Every
function is derived from first principles, with machine-checked error
bounds.

> **Status: pre-release (milestone M1).** The library provides error-free
> transforms, double-word arithmetic, ULP utilities and seeded streams so far;
> nothing is published yet. The
> [project plan](docs/PLAN.md) describes what release 0.1 will contain and how
> it is built and verified.

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
  - bit-exact tests against MPFR and mpmath;
  - Sollya and Gappa certificates checked by Coq, bound to the source they
    describe;
  - mutation testing and fuzzing.

## License

Licensed under either of [Apache License, Version 2.0](LICENSE-APACHE) or
[MIT license](LICENSE-MIT), at your option.

Unless you explicitly state otherwise, any contribution intentionally
submitted for inclusion in this project by you, as defined in the Apache-2.0
license, is dual licensed as above, without any additional terms or
conditions.
