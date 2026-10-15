# Repository Guidelines

**Correctness, performance, and clean architecture are first-class features of every MorphIQ Labs project**, not qualities traded away for delivery speed or deferred to a follow-up. Correctness and performance are the primary concerns, in that order: correctness is never traded for speed, and speed is given up for nothing but correctness. Each is held to evidence, and this document is how: correctness is *proven* — by the invariants, their enforcement ladder, and the assurance gates, never asserted; performance is *designed* — the complexity class, the data structure, the allocation, and any vectorization chosen deliberately at design time, then measured against the best implementation that exists; architecture is *enforced* — boundaries checked mechanically, and complexity removed rather than accumulated. What each demands concretely differs by project; that all three stay top of mind does not. A change that erodes any of the three is incomplete however quickly it ships, and "it works" is not evidence for any of them.

This file is the repository's engineering contract for human and agent contributors. `CLAUDE.md` contains only `@AGENTS.md`.

## Purpose and Architecture

`morphiq-numerics` provides binary64 numerical primitives: elementary functions, seeded random streams and the normal family. The required standard is **correctly rounded** results that are **identical on every target**, computed **at least as fast as the best available implementation** of each function. This is a requirement, not a claim that every current implementation meets it. Correctness claims are limited to the domains established by the proofs, and performance claims to the hosts, workloads and comparisons established by measurements. An unmet requirement remains incomplete work. It is the shared numerics substrate for MorphIQ Labs' engines and is published openly under MIT OR Apache-2.0. Read [the provenance policy](docs/PROVENANCE.md) before any change. Scope, intent and progress are recorded in GitHub issues, epics and milestones, never in repository documents.

The library's public API is what `crates/morphiq-numerics/src/lib.rs` lists, and each function's contract and derivation is a document in `docs/`; documentation must not describe functions that are not in the source tree.

- `crates/morphiq-numerics` is the published library. It is `#![no_std]`, forbids `unsafe`, and never calls a platform math library. Its one dependency is `morphiq-numerics-arch`, first-party, optional and behind the `simd` feature. Its `std` feature turns on runtime CPU detection for `simd`; like any feature, it may change speed or add conveniences, never a numerical result.
- `crates/morphiq-numerics-arch` holds the SIMD lane intrinsics behind a safe, token-gated API ([arch.md](docs/arch.md)). It is `no_std`, takes no dependencies, and is the only crate allowed `unsafe` code: every `unsafe` block carries its `SAFETY:` proof, which Clippy enforces.
- Test oracles (MPFR, mpmath), generators, proofs and fuzzing live outside the published crate and are never its dependencies.
- Consumers take pinned releases. A defect found by a consumer is fixed here and consumed back at a released version.

```text
crates/morphiq-numerics/   the published library: no_std, forbids unsafe; optionally depends on the arch crate
crates/morphiq-numerics-arch/  safe SIMD lanes (NEON, SSE2, AVX2+FMA, AVX-512F): the only unsafe code, no dependencies
crates/reference/          reference tests against the fixtures, and the cross-check corpus writer (unpublished)
crates/digest/             the determinism digest, and digest-embedded for the no_std target
generators/                Sollya and mpmath generators for constants, certificates and fixtures
formal/                    Gappa certificates, Coq proofs, the axiom audit and the proof-binding manifests
docs/                      each function's contract and derivation, and the provenance policy
scripts/                   gate logic that CI and contributors run identically
```

## Design Constraints

- **Correct rounding is the contract.** For every finite argument in its domain, a function returns the binary64 value nearest the exact result, ties to even, with IEEE 754-2019 §9.2 special-value semantics. A function is claimed correctly rounded only over a domain where its accurate path is proved sufficient against the published worst cases; anywhere else its proved bound is stated instead. Never claim more than the artifacts establish.
- **Target independence is enforced, not assumed.** No platform libm (the crate is `no_std`; Clippy's `disallowed-methods` denies the `std` transcendentals in every target, tests included). No implicit contraction. Error-free transforms are exact with or without FMA; a lane kernel uses a fused multiply-add only for `two_prod`'s error term, only on a backend with hardware FMA, and only on `two_prod`'s proved domain, where it gives Dekker's bits ([lanes.md](docs/lanes.md) §2). A vectorized path performs the scalar operation sequence per lane and returns the scalar result bit for bit. The determinism digest proves this on every supported target.
- **Expected values come from outside the implementation.** Test oracles are MPFR, mpmath and published worst-case data, never a rearrangement of the function under test and never a tolerance wide enough to accept a wrong rounding. For a correctly rounded function the assertion is bit equality.
- **Performance has a bar.** Every function is at least as fast as the implementation it replaces in a MorphIQ Labs consumer, and as fast as or faster than the best available alternatives (the canonical algorithm, platform libms, Rust crates, published correctly rounded libraries), scalar and batched, on the same host. The bar holds whatever the alternative's contract: a weaker contract elsewhere does not excuse a slower function here, and the bar is met without weakening this crate's. Optimization lessons learned in a consumer, such as domain partitioning, argument splitting or dispatch structure, are brought here rather than left behind. Performance claims are local same-host measurements, never CI timing.
- **The canonical algorithm is the reference.** Each function starts from the best-of-breed algorithm in the literature, such as Cody's rational approximations for `erfcx` or CORE-MATH's designs for correctly rounded elementary functions. An in-house design replaces it only when measured at least as fast under this crate's contract; an in-house algorithm slower than the canonical one does not ship.
- **Provenance is clean.** Everything here can ship under MIT OR Apache-2.0 and lives in this repository. Algorithms come from published mathematics or from vendored code under a compatible license, recorded with its notices; every generated coefficient and constant comes from a versioned generator. No copyleft or unclear-license code, and an agent is never given such source ([PROVENANCE.md](docs/PROVENANCE.md), [AI-assisted contributions](docs/PROVENANCE.md#ai-assisted-contributions)).

## How a Correctly Rounded Function Is Built

Each function follows the same pipeline, which secures correct rounding first and speed second; its derivation document is as much the deliverable as its code:

1. **Specification:** domain, special values, overflow and underflow thresholds (derived, not copied), the exact mathematical definition, and the implementations it is measured against: the canonical algorithm, the fastest available alternatives and any consumer implementation it replaces.
2. **Argument reduction:** derived from the function's algebra, with constants generated at stated precision and their rounding error accounted for; Payne–Hanek for large trigonometric arguments.
3. **Fast path:** an approximation evaluated in binary64 or double-word arithmetic, following the canonical algorithm's structure and domain splits unless an in-house design measures at least as fast, and chosen for its operation count and branch behaviour. Its approximation error is certified by Sollya `supnorm`, its evaluation error by Gappa, and it is accurate enough that the rounding test almost never fails.
4. **Rounding test:** Ziv's strategy. The fast result is returned only when its error interval provably cannot straddle a rounding boundary.
5. **Accurate path:** `Q128` or `Q256` integer-significand arithmetic (no fused multiply-add needed), with an error bound proved small enough for the published worst cases of that function. Where no worst-case result covers a domain, correct rounding there is not claimed; the proved bound is stated instead. Its rate is measured and reported; an input region that always reaches it is a performance defect unless shown to be unavoidable.
6. **Generators:** every coefficient and constant comes from a versioned generator under `generators/`, with pinned tools and a recorded precision, and CI replays it. A canonical algorithm's coefficients are regenerated here to the fast path's required accuracy.
7. **Measurement:** same-host scalar and batched throughput and latency against the step 1 references, with the accurate-path rate. The function must meet the performance bar before it is complete or ships. A shortfall is diagnosed and recorded on its issue, which remains open until measurements demonstrate that the shortfall is resolved. Recording a shortfall does not satisfy the bar.

## Invariants and Trust Boundaries

Every invariant names its enforcement, chosen from this ladder: (1) unrepresentable by construction (types, `no_std`, the absence of a dependency), (2) enforced inside the owning function, (3) only then a tested convention hardened by mutation gates. Never assert source text, byte offsets or statement order in a test. A proof artifact is bound by hash to the source it describes; changing that source fails the gate until the proof is rerun. Escape hatches (an allowed lint, a skipped gate) ship with their reason and exit condition.

## Engineering and Review Principles

- Finish the job in the change that surfaces it: fix the defect pattern, not the instance, search the crate for siblings, and say what the search found, including when it found none. If completing the pattern would make one change unreviewable, split it into stacked pull requests that land together.
- Root-cause every regression: how it entered, why the safeguards missed it, and what prevents recurrence.
- Documentation ships in the change that invalidates it. Standards and contract documents describe the current tree only; intent and progress live in GitHub issues and milestones.
- Prefer simple, auditable code. Every function's derivation is a document, and the code follows it.

## Build, Test, and Development Commands

```sh
cargo fmt --all -- --check
cargo clippy --workspace --all-targets --all-features --locked -- -D warnings
cargo test --workspace --all-features --locked
cargo doc --workspace --all-features --no-deps --locked      # RUSTDOCFLAGS="-D warnings"
cargo build -p morphiq-numerics --locked --target thumbv7em-none-eabihf   # no_std
cargo build -p morphiq-numerics --locked --target thumbv7em-none-eabihf --features simd
./scripts/check_lanes_sde.sh       # AVX-512F lanes under Intel SDE (scripts/install_sde.sh), x86-64 Linux
./scripts/check_advisories.sh
./scripts/check_generators.sh
cargo run --locked -p morphiq-numerics-reference --bin crosscheck-corpus > target/crosscheck.txt
MORPHIQ_INTERNAL_CORPUS=$PWD/target/internal-crosscheck.txt cargo test --locked -p morphiq-numerics --lib internal_crosscheck -- --ignored
# in the pinned Debian image (see the formal job): ./scripts/write_gappa_proofs.sh target/gappa-proofs
# then, in the pinned Coq image (.cargo/coq-image): ./scripts/check_formal.sh target/crosscheck.txt target/internal-crosscheck.txt target/gappa-proofs
#   (--build DIR keeps the proof build in DIR and reuses it next time; see the script's header)
# after a passing cached build, in the same image: ./scripts/check_formal_negative.sh binding /path/to/coq-deps.tar.gz DIR target/crosscheck.txt target/internal-crosscheck.txt target/gappa-proofs
#   (repeat for admitted, axiom, certificate, crosscheck, internal-crosscheck; each uses an isolated copy)
# and, in the pinned Debian image (see the certificates job): ./scripts/check_certificates.sh
cargo deny --locked check licenses
```

Gate logic lives in `scripts/` and tool pins in `.cargo/*-version`, never only in the workflow file, so a contributor runs exactly what CI runs. `rust-toolchain.toml` pins the development toolchain; the `msrv` job checks the declared `rust-version`.

## Security, Safety, and Dependencies

`unsafe` is forbidden in every crate but `morphiq-numerics-arch`, whose lint table is the workspace's one exception: the `core::arch` intrinsics are `unsafe` without a proof that the CPU has them, and that crate makes the proof, a detection token per backend, behind a safe API ([arch.md](docs/arch.md)). Exit condition: none while the intrinsics are `unsafe`. The library takes no third-party dependencies; its one dependency is that first-party crate, optional behind `simd`, which itself takes none. A proposal to add any other needs a written justification against this file. Test and tooling dependencies are declared in `[workspace.dependencies]`, checked by `cargo-deny` for licenses and RustSec advisories, and kept out of the published crate. Third-party GitHub Actions are pinned to full commit SHAs. Never commit secrets.

## Coding Style and Testing

rustfmt defaults; `snake_case` functions, `UpperCamelCase` types, `SCREAMING_SNAKE_CASE` constants. Name tests for the observable behaviour they check. A reference fixture carries its provenance: the generator, its tool versions and its precision.

## Pull Requests and Releases

Every change lands through a pull request; `main` accepts no direct pushes. Only the repository owner merges: contributors and agents open and update pull requests, and never merge one, enable auto-merge or approve on the owner's behalf. The pull request title is a conventional commit (`feat(elementary): correctly rounded exp`), checked by CI, and becomes the squash commit's subject, which release automation reads. A pull request states what changed and why, its numerical impact (which functions' results can change, and why that is correct), and closes the issues it resolves (`Closes #N`).

Releases follow the MorphIQ Labs model, driven by release-plz (`.github/workflows/release.yml`, `release-plz.toml`). After each merge to `main` it opens or refreshes a `chore: release` pull request that bumps the workspace version and writes the `CHANGELOG.md` section from the conventional-commit subjects since the last tag. That pull request is reviewed, checked and squash-merged like any other; merging it tags `v{version}`, one tag for the workspace, and creates the GitHub release. Never hand-cut a tag, hand-edit a released changelog section or bump the version outside the release pull request.

- **Until 0.1, releases are git tags only.** `morphiq-numerics` and `morphiq-numerics-arch` keep `publish = false`, and consumers pin `tag = "v0.0.N"`. The 0.0.x series exists so consumers can pin a release rather than a commit; 0.1.0 is reserved for the first crates.io release, through Trusted Publishing, once the 0.1 contracts are met (milestone M6, #90).
- **Only the library and its lane crate are released.** The digest, the embedded digest and the reference oracles are never released; release-plz manages an allowlist that excludes them.
- **A tag equals the version.** Every `vX.Y.Z` points at a commit whose workspace version, and so every released crate's version, is exactly X.Y.Z: one workspace version, tag `v{{ version }}`, no per-crate tags. `scripts/check_release_version.sh` enforces it (the `release / version` job on every pull request, push to `main` and tag push, and the release workflow after tagging); on the release pull request it checks the proposed tag is new and matches `CHANGELOG.md` and the title.
- **The release workflow needs the `RELEASE_PLZ_TOKEN` secret.** A pull request opened with the workflow's own `GITHUB_TOKEN` would not trigger the required checks, so it could never merge.

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
| Interaction limit | collaborators only, renewed every six months | Only the owner opens issues and pull requests or comments; GitHub caps the limit at six months, so it is renewed before it expires. |

Check them with `gh api repos/MorphIQ-Labs/morphiq-numerics/rulesets` rather than assuming.

## Definition of Done

A change is complete when its contract is stated, its implementation follows a documented derivation with generated constants, its results match the independent oracle bit for bit wherever correct rounding is claimed, its proofs are rerun and bound, same-host measurements show it meets the performance bar, every gate passes on every target, the determinism digest is unchanged or deliberately updated with the reason, documentation describes the new current state, and every same-pattern sibling is fixed.

A known shortfall in correctness, performance or architecture keeps the affected work incomplete until it is fixed and the required evidence establishes that. Passing CI, merging code, documenting the shortfall or moving it to a follow-up issue does not make that work complete. Missing evidence also leaves the corresponding requirement unestablished; it is never reported as satisfied.
