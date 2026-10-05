# Repository Guidelines

**Correctness, performance, and clean architecture are first-class features of every MorphIQ Labs project**, not qualities traded away for delivery speed or deferred to a follow-up. Each is held to evidence, and this document is how: correctness is *proven* — by the invariants, their enforcement ladder, and the assurance gates, never asserted; performance is *designed* — the complexity class, the data structure, the allocation, and any vectorization chosen deliberately at design time, then measured wherever measurement applies; architecture is *enforced* — boundaries checked mechanically, and complexity removed rather than accumulated. What each demands concretely differs by project; that all three stay top of mind does not. A change that erodes any of the three is incomplete however quickly it ships, and "it works" is not evidence for any of them.

This file is the repository's engineering contract for human and agent contributors. `CLAUDE.md` contains only `@AGENTS.md`.

## Purpose and Architecture

`morphiq-numerics` provides binary64 numerical primitives whose results are **correctly rounded** and **identical on every target**: elementary functions, seeded random streams and the normal family. It is the shared numerics substrate for MorphIQ Labs' engines and is published openly under MIT OR Apache-2.0. Read [the plan](docs/PLAN.md) and [the provenance policy](docs/PROVENANCE.md) before any change.

The repository is at milestone M0: governance, CI and an empty library crate. The library has no public API yet; documentation must not describe functions that are not in the source tree.

- `crates/morphiq-numerics` is the published library. It is `#![no_std]`, has no dependencies, forbids `unsafe`, and never calls a platform math library. A `std` feature, if one is ever added, may only add conveniences, never a different numerical result.
- Test oracles (MPFR, mpmath), generators, proofs and fuzzing live outside the published crate and are never its dependencies.
- Consumers take pinned releases. A defect found by a consumer is fixed here and consumed back at a released version.

## Design Constraints

- **Correct rounding is the contract.** For every finite argument in its domain, a function returns the binary64 value nearest the exact result, ties to even, with IEEE 754-2019 §9.2 special-value semantics. A function is claimed correctly rounded only over a domain where its accurate path is proved sufficient against the published worst cases; anywhere else its proved bound is stated instead. Never claim more than the artifacts establish.
- **Target independence is enforced, not assumed.** No platform libm (the crate is `no_std`; Clippy's `disallowed-methods` denies the `std` transcendentals in every target, tests included). No implicit contraction. Error-free transforms are exact with or without FMA. A vectorized path performs the scalar operation sequence per lane and returns the scalar result bit for bit. The determinism digest proves this on every supported target.
- **Provenance is clean.** Algorithms come from mathematical definitions and published mathematics; every coefficient and constant comes from a versioned generator. No code, tables or structure from another implementation (see [PROVENANCE.md](docs/PROVENANCE.md)).
- **Expected values come from outside the implementation.** Test oracles are MPFR, mpmath and published worst-case data, never a rearrangement of the function under test and never a tolerance wide enough to accept a wrong rounding. For a correctly rounded function the assertion is bit equality.
- **Performance is designed.** Each function's fast path is chosen for its operation count and branch behaviour; the accurate path's rate is measured and reported. Performance claims are local same-host measurements, never CI timing.

## Invariants and Trust Boundaries

Every invariant names its enforcement, chosen from this ladder: (1) unrepresentable by construction (types, `no_std`, the absence of a dependency), (2) enforced inside the owning function, (3) only then a tested convention hardened by mutation gates. Never assert source text, byte offsets or statement order in a test. A proof artifact is bound by hash to the source it describes; changing that source fails the gate until the proof is rerun. Escape hatches (an allowed lint, a skipped gate) ship with their reason and exit condition.

## Engineering and Review Principles

- Finish the job in the change that surfaces it: fix the defect pattern, not the instance, search the crate for siblings, and say what the search found, including when it found none. If completing the pattern would make one change unreviewable, split it into stacked pull requests that land together.
- Root-cause every regression: how it entered, why the safeguards missed it, and what prevents recurrence.
- Documentation ships in the change that invalidates it. Standards and contract documents describe the current tree only; the plan records intent and is updated as milestones land.
- Prefer simple, auditable code. Every function's derivation is a document, and the code follows it.

## Build, Test, and Development Commands

```sh
cargo fmt --all -- --check
cargo clippy --workspace --all-targets --all-features --locked -- -D warnings
cargo test --workspace --all-features --locked
cargo doc --workspace --all-features --no-deps --locked      # RUSTDOCFLAGS="-D warnings"
cargo build -p morphiq-numerics --locked --target thumbv7em-none-eabihf   # no_std
./scripts/check_advisories.sh
cargo deny --locked check licenses
```

Gate logic lives in `scripts/` and tool pins in `.cargo/*-version`, never only in the workflow file, so a contributor runs exactly what CI runs. `rust-toolchain.toml` pins the development toolchain; the `msrv` job checks the declared `rust-version`.

## Security, Safety, and Dependencies

`unsafe` is forbidden in the library. The library takes no dependencies; a proposal to add one needs a written justification against this file. Test and tooling dependencies are declared in `[workspace.dependencies]`, checked by `cargo-deny` for licenses and RustSec advisories, and kept out of the published crate. Third-party GitHub Actions are pinned to full commit SHAs. Never commit secrets.

## Coding Style and Testing

rustfmt defaults; `snake_case` functions, `UpperCamelCase` types, `SCREAMING_SNAKE_CASE` constants. Name tests for the observable behaviour they check. A reference fixture carries its provenance: the generator, its tool versions and its precision.

## Pull Requests and Releases

Every change lands through a pull request; `main` accepts no direct pushes. The pull request title is a conventional commit (`feat(elementary): correctly rounded exp`), checked by CI, and becomes the squash commit's subject, which release automation reads. A pull request states what changed and why, its numerical impact (which functions' results can change, and why that is correct), and closes the issues it resolves (`Closes #N`).

Releases follow the MorphIQ Labs model: after each merge a release pull request bumps the version and writes `CHANGELOG.md`; merging it tags `v{version}` and publishes to crates.io through Trusted Publishing. The crate stays `publish = false` until the 0.1 contracts in the plan are met.

## Repository and Branch Settings

| Setting | Value | Why |
| --- | --- | --- |
| Default branch | `main` | One long-lived branch. |
| Organization ruleset "Default branch policy" | PR required, linear history, signed commits, no force-push or deletion, threads resolved | Inherited; GitHub signs the squash commits it creates. |
| Organization rulesets | `v*` tag protection; repository transfer and deletion blocked | Inherited. |
| Repository ruleset "Main branch protection" | squash only; every CI job a strict required check; no bypass | GitHub reports a job skipped behind a failed one as passing, so every job must itself be required. A job is added here in the same change that adds it to CI. |
| Merge method | squash only; title from the PR | Release automation reads the subject. |
| Delete branch on merge | on | |
| Security | secret scanning and push protection, private vulnerability reporting, Dependabot alerts | Public repository. |

Check them with `gh api repos/MorphIQ-Labs/morphiq-numerics/rulesets` rather than assuming.

## Definition of Done

A change is complete when its contract is stated, its implementation follows a documented derivation with generated constants, its results match the independent oracle bit for bit wherever correct rounding is claimed, its proofs are rerun and bound, every gate passes on every target, the determinism digest is unchanged or deliberately updated with the reason, documentation describes the new current state, and every same-pattern sibling is fixed.
