# Project plan

`morphiq-numerics` is a Rust library of binary64 numerical primitives whose
results are **correctly rounded** and **identical on every target**. It exists
because numerical engines keep hitting the same defects:

- **The platform libm leaks into seeded results.** Seeded results depend on
  the host's `ln`, `exp`, `sin` and `cos`. glibc, macOS libSystem and musl
  round these differently, so a seed reproduces only on the host that
  recorded it. A Box–Muller noise stream, for example, diverges by one ulp
  between macOS and Linux.
- **Faithful functions can't be checked bit for bit.** A function that is only
  faithfully rounded has no single right answer. An independent reference can
  then only be compared within a tolerance, and determinism has to be pinned
  from the implementation's own output instead of following from the
  specification.
- **Borrowed provenance can't be redistributed.** Kernels adapted from
  published code (AS241, Cody's CALERF, QD) carry unresolved redistribution
  rights. morphiq-risk-ml found this and chose to replace them.

A correctly rounded function has exactly one right answer: the binary64 value
nearest the exact result. Any independent reference (MPFR, mpmath, another
language) then reproduces it bit for bit, and so does every target. That makes
the specification itself the determinism contract.

This document is the plan. It describes intent, not shipped behavior. Each
section moves into a current-state contract document when the work it describes
lands.

## Decisions

| Decision | Choice | Recorded |
|---|---|---|
| Hosting | GitHub, `MorphIQ-Labs/morphiq-numerics`, public | 2026-10-05 |
| License | MIT OR Apache-2.0 | 2026-10-05 |
| Accuracy | Correctly rounded (round-to-nearest-even) for every elementary and normal-family function | 2026-10-05 |
| Provenance | Own derivations from mathematical definitions; no adapted implementations ([PROVENANCE.md](PROVENANCE.md)) | 2026-10-05 |
| `no_std` | Default; `core` only, no allocation | 2026-10-05 |
| First release scope | Elementary functions, seeded random streams, the normal family | 2026-10-05 |

## Contracts

### Correct rounding

For every finite argument in a function's domain, the result is the binary64
value nearest the exact mathematical result, ties to even. Special values follow
IEEE 754-2019 §9.2 (recommended correctly rounded operations):
- NaN propagates.
- Signed zeros, infinities and the domain's poles have their standard results.
- Subnormal results are produced, not flushed.

The guarantee covers the whole binary64 domain. It is not limited to a
convenient interval.

### Target independence

Every function returns the same bits on every target. That follows from correct
rounding, and it is enforced, not assumed:
- **No platform libm.** The crate is `no_std`, and `core` has no `f64::ln`.
  Clippy's `disallowed-methods` also denies the `std` transcendentals in every
  target, tests included. The only exceptions are oracle-generation tools,
  which run outside the crate.
- **No implicit contraction.** Rust never fuses `a * b + c`. A fused operation
  appears only as an explicit, exact error-free transform.
- **FMA is optional and exact.** Error-free products (TwoProd) use Dekker and
  Veltkamp splitting, which is exact without FMA, or a hardware FMA where one
  exists. Both give the identical exact result, so FMA availability cannot
  change any output.
- **SIMD follows the scalar order.** A SIMD path must run the scalar operation
  sequence on each lane, so it returns the scalar result bit for bit.

A determinism digest pins this in CI on every supported target. It hashes the
outputs over a fixed corpus and is reproduced bit for bit everywhere.

### Seeded streams

Integer generators are specified bit for bit by their published definitions:
- **SplitMix64:** Steele, Lea & Flood, OOPSLA 2014.
- **xoshiro256++ and its jump functions:** Blackman & Vigna, ACM TOMS 47(4), 2021.

Stream splitting is part of the specification:
- `SplitMix64` seeding for member streams;
- `jump` and `long_jump` for parallel streams.

Variates are defined in terms of the correctly rounded functions:
- **Normal deviates:** Box–Muller, with correctly rounded `ln`, `sincos` and an
  IEEE `sqrt`.
- **Uniforms:** an exact `k · 2⁻⁵³` mapping.

So a seed produces the same stream on every target, and in any other language
that implements the same specification.

## Release 0.1 scope

| Area | Functions |
|---|---|
| Error-free transforms | `two_sum`, `fast_two_sum`, `two_prod`, a double-word (`f64 + f64`) type with documented bounds |
| ULP utilities | `ulp`, `next_up`/`next_down` (core), ordered-bits distance |
| Elementary | `exp`, `expm1`, `exp2`, `ln`, `ln_1p`, `log2`, `log10`, `sin`, `cos`, `sincos`, `tan` |
| Seeded streams | `SplitMix64`, `Xoshiro256PlusPlus` (`jump`, `long_jump`), open/closed unit uniforms, Box–Muller normal pairs |
| Normal family | `erf`, `erfc`, `erfcx`, `norm_pdf`, `norm_cdf`, `norm_ccdf`, `log_norm_cdf`, `norm_inv` |

`pow`, `atan2`, the inverse trigonometric and hyperbolic functions, `lgamma`,
`digamma` and `incomplete gamma` are planned for later releases (see
[Later work](#later-work)).

## How a correctly rounded function is built here

Each function follows the same documented pipeline. The derivation is the
deliverable as much as the code:

1. **Specification.** Domain, special values, overflow and underflow thresholds
   (derived, not copied), and the exact mathematical definition.
2. **Argument reduction.** Derived from the function's algebra, for example
   `exp(x) = 2^k · exp(r)`, or Payne–Hanek reduction for large trigonometric
   arguments. Its constants are generated at stated precision, with their
   rounding error accounted for.
3. **Fast path.** A polynomial or rational approximation, evaluated in
   double-word arithmetic where the budget needs it. Its approximation error is
   certified (Sollya `supnorm`) and its evaluation error bounded (Gappa).
4. **Rounding test.** Ziv's strategy: if the fast result's error interval
   doesn't straddle a rounding boundary, it's returned. Otherwise an
   accurate path is taken.
5. **Accurate path.** A higher-precision evaluation (triple-word or a longer
   expansion) whose error bound is proved small enough to decide every
   remaining case. The bound comes from the published worst cases for
   correctly rounding that function in binary64 (Lefèvre & Muller's search
   method, and the published hardest-to-round tables). Those cases are cited,
   recorded and tested. Where no such result exists for a function and domain,
   correct rounding there isn't claimed until an exhaustive or proved
   argument is.
6. **Generators.** Every coefficient and constant is produced by a versioned
   generator under `generators/`, with pinned tools (Sollya, mpmath) and a
   recorded precision. CI regenerates them and fails if a committed value
   differs.

## Assurance

| Lane | What it establishes | When it runs |
|---|---|---|
| Unit and property tests | Special values, monotonicity and symmetry; identities checked bit for bit where they are exact | Every PR |
| Reference tests | Bit-exact agreement with MPFR or mpmath on committed fixtures (random, near-boundary, worst-case and special inputs) | Every PR |
| Determinism digest | Identical output hashes on x86-64 Linux, aarch64 Linux, aarch64 macOS, x86-64 Windows, musl, `wasm32` and a `no_std` embedded target | Every PR |
| Generator replay | Committed coefficients and constants equal their regenerated values | Every PR |
| Proof binding | Each Gappa, Sollya, Coq or Lean artifact is bound by hash to the source it describes in a committed manifest. An edit fails until the proof is rerun | Every PR |
| Formal | Sollya approximation bounds, Gappa rounding bounds kernel-checked by Coq, and Lean for exact-real identities | Every PR to `main` |
| Mutation | A required catalog of numerical faults, each with a named witness, plus a whole-crate inventory floor | Every PR to `main` |
| Fuzzing | cargo-fuzz against MPFR on each function | Short budget per PR, long campaigns scheduled |
| Exhaustive sweeps | Every binary64 in chosen sub-intervals, plus all inputs of `f32` analogues used as cross-checks | Scheduled |
| Dependencies | `cargo-deny` licenses and RustSec advisories | Every PR and `main` |

MPFR (`rug`, LGPL) is used only by test and tooling crates that are never
published. The library crate has no dependencies.

## Repository layout (target)

```text
crates/morphiq-numerics/   the published library: no_std, no dependencies
crates/reference/          test-only MPFR oracle and fixture loaders (unpublished)
generators/                Sollya and mpmath generators for coefficients and fixtures
formal/                    Sollya, Gappa and Coq certificates, Lean, and the proof-binding manifest
fuzz/                      cargo-fuzz targets (own workspace)
docs/                      contracts, derivations and this plan (mdBook site)
scripts/                   gate logic that CI and contributors run identically
```

## Repository and release settings

- **Inherited organization rulesets:**
  - **Default branch policy:** pull requests required, linear history, signed
    commits, no force-push or deletion, and review threads resolved.
  - **Release tag protection:** for `v*` tags.
  - **Repository lifecycle:** guards against transfer and deletion.
- **Repository ruleset ("Main branch protection"):**
  - squash-only merges;
  - every CI job a strict required status check, so the branch is up to date
    with `main`;
  - no bypass actors.

  A job is added to the required list in the same change that adds it to CI.
- **Merging:** squash only. The pull request title becomes the commit subject
  and is checked as a conventional commit. Branches are deleted after merge.
- **Security:** secret scanning with push protection, private vulnerability
  reporting, Dependabot alerts, and third-party actions pinned to commit SHAs.
- **Releases:** the MorphIQ Labs release model.
  - `prepare` opens the `chore/release` PR from conventional commits through
    the release GitHub App.
  - `tag` cuts `v{version}` when that PR lands.
  - `publish` releases to crates.io through Trusted Publishing.
  - The crate stays `publish = false` until the 0.1 contracts are met.

## Milestones

| | Milestone | Exit criterion |
|---|---|---|
| M0 | Repository, governance, CI skeleton, rulesets | This PR; then required checks enabled |
| M1 | Error-free transforms, double-word, ULP utilities; integer streams | Bit-exact against MPFR; proofs for the EFT bounds; determinism digest on all targets. **Met:** exact integer-arithmetic oracle (stronger than MPFR for exact operations), Coq proofs bound in `formal/`, digest on seven targets |
| M2 | `exp`, `expm1`, `exp2`, `ln`, `ln_1p`, `log2`, `log10` | Correctly rounded over the whole domain; worst cases tested; certificates bound |
| M3 | `sin`, `cos`, `sincos`, `tan` (Payne–Hanek for large arguments) | As M2 |
| M4 | Box–Muller normal stream on M2/M3 | Bit-exact against an independent reference implementation of the specification |
| M5 | `erf`, `erfc`, `erfcx`, normal pdf/cdf/ccdf/log-cdf, `norm_inv` | Correct rounding where the worst-case analysis supports it. Any function and domain where it doesn't yet is reported with its proved bound and isn't claimed as correctly rounded. This is the riskiest milestone |
| M6 | 0.1 release; first consumers migrate | Published; consumers below adopt a pinned release |

## Consumers and migration

- **MorphIQ Labs' Rust engines:** replace their platform-libm and
  general-purpose special-function dependencies in seeded and reproducibility-
  critical paths with pinned releases of this crate. Existing in-house kernels
  are replaced by this crate's derivations, never moved here (see
  [PROVENANCE.md](PROVENANCE.md)).
- **morphiq-risk-ml (OCaml):** cannot link a Rust crate. Its #64 replacements
  can adopt this project's published derivations and generated coefficients
  (same license and owner), and each project serves as the other's
  cross-language oracle.

Consumers take a pinned release, never a branch.

## Later work

- **More functions:** `pow`, `hypot`, `atan`, `atan2`, `asin`, `acos`,
  `sinh`, `cosh`, `tanh`, `asinh`, `acosh`, `atanh`, `cbrt`.
- **Special functions:** `lgamma`, `digamma`, the incomplete gamma and beta
  functions, and Student-t and chi-square distribution functions.
- **Quasi-random sequences:** Sobol and Halton.
- **Performance:** vectorized evaluation of the fast paths, keeping the
  scalar-equal lane rule.
- **Other languages:** C ABI bindings, so non-Rust consumers share one
  implementation.

## Risks

- **Effort:** correct rounding over the full domain is substantial work. The
  normal family is the hardest part, and there's little published worst-case
  data for `erfc` tails and `norm_inv`. Mitigation: M5 states what's proved
  per function and domain, rather than claiming correct rounding early.
- **Performance:** accurate paths are slow but rare. Fast-path rates are
  measured and reported per function, and callers that need throughput get the
  same results either way.
- **Provenance discipline:** consulting a prior implementation contaminates a
  derivation. The policy in [PROVENANCE.md](PROVENANCE.md) applies from the
  first commit.
