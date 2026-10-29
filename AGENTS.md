# Repository Guidelines

**Correctness, performance, and clean architecture are first-class features of every MorphIQ Labs project**, not qualities traded away for delivery speed or deferred to a follow-up. Correctness means satisfying the selected numerical contract; performance is optimized within that contract, never by silently weakening it. Each is held to evidence, and this document is how: correctness is *proven* — by the invariants, their enforcement ladder, and the assurance gates, never asserted; performance is *designed* — the complexity class, the data structure, the allocation, and any vectorization chosen deliberately at design time, then measured against relevant implementations with explicit contracts; architecture is *enforced* — boundaries checked mechanically, and complexity removed rather than accumulated. What each demands concretely differs by project; that all three stay top of mind does not. A change that erodes any of the three is incomplete however quickly it ships, and "it works" is not evidence for any of them.

This file is the repository's engineering contract for human and agent contributors. `CLAUDE.md` contains only `@AGENTS.md`.

## Strategic Pragmatism

Be strategically pragmatic in all MorphIQ Labs work. Choose the simplest solution that delivers the intended outcome and meets its correctness, performance, and operational contracts.

- **Keep the outcome and scope explicit.** Resist speculative features, general-purpose frameworks, and adjacent problems that are not needed for the agreed result. Added scope must earn its implementation, maintenance, and opportunity cost.
- **Challenge direction constructively.** Treat proposed approaches, including the owner's, as proposals to evaluate. Raise concerns early, explain the tradeoffs, and recommend a simpler or better-supported alternative when one exists. Agreement is not a substitute for judgment.
- **Respect ownership boundaries.** Prefer established libraries and supported provider capabilities. Do not turn a third-party limitation or a problem outside our domain into a subsystem we must build and maintain. Establish our boundary, surface the limitation, and recommend an upstream fix, a supported alternative, or an explicit scope reduction; custom machinery needs a clear domain benefit.
- **Bound investigations.** Name the question, the evidence needed to decide, and a stopping condition. When further investigation or engineering costs substantially more than its expected value, stop expanding the work and recommend a decision or rescope. Do not chase exhaustive explanations that cannot change that decision.
- **Prefer explicit failure to speculative recovery.** Reject unsupported inputs or conditions with an actionable error or exception at the owning boundary rather than adding fallbacks for every conceivable edge case. Preserve valid state and required cleanup; never silently approximate, discard data, or report success. Required supported cases and recovery guarantees still have to work.

Pragmatism governs which guarantees we undertake, not whether we honor them. If an existing commitment is disproportionate, make the tradeoff and proposed contract change explicit to the owner before narrowing it; do not disguise unfinished work as completion.

## Prose-only CI

Changes confined to the root `AGENTS.md`, `CLAUDE.md`, `CONTRIBUTING.md`,
`README.md`, or Markdown files directly under `docs/adr/` use lightweight prose
checks. This is an explicit exception to the general every-change build, test,
assurance and dependency-audit rules. Keep applicable title, repository-hygiene,
secret and whitespace checks, and a required successful pipeline/check result.
Do not use a blanket CI-skip marker or leave required checks pending.

The allowlist is deliberately narrow. Any mixed change or other path retains
its existing CI gates, including unfamiliar files, code, dependencies, build/CI
configuration, release metadata, examples, notebooks, fixtures, generated inputs
and proof-related documentation. Review consumers before extending the allowlist;
Markdown is not automatically inert. Preserve focused checks that read an
allowlisted file as a policy input. Scheduled/operational pipelines and release
automation retain their existing responsibilities. CI-rule changes themselves
run full CI and exercise prose, mixed, renamed and unknown-path cases.

## Purpose and Architecture

`morphiq-numerics` provides binary64 numerical primitives: elementary functions, seeded random streams and the normal family. Existing APIs retain their strong numerical contracts: correctly rounded where established, with their stated proved bounds elsewhere, and identical results on every target. They must be as performant as the evidence and credible algorithm choices allow without weakening those contracts; parity with weaker-contract competitors is not required. Explicit bounded-approximation APIs have a separate performance target, defined below. Correctness claims are limited to the domains established by the proofs, and performance claims to the hosts, workloads and comparisons established by measurements. An unmet requirement remains incomplete work. It is the shared numerics substrate for MorphIQ Labs' engines and is published openly under MIT OR Apache-2.0. Read [the provenance policy](docs/PROVENANCE.md) before any change. Scope, intent and progress are recorded in GitHub issues, epics and milestones, never in repository documents.

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

- **Every API has an explicit numerical contract.** Correct rounding means the binary64 value nearest the exact result, ties to even, with IEEE 754-2019 §9.2 special-value semantics. Existing APIs keep their guarantees: a function is claimed correctly rounded only over a domain where its accurate path is proved sufficient against the published worst cases; anywhere else its proved bound is stated instead. An explicitly approximate API must instead satisfy its published per-function, per-domain bound and special-value semantics. Never claim more than the artifacts establish; sampled maximum error is not a proved bound.
- **Target independence is enforced, not assumed.** No platform libm (the crate is `no_std`; Clippy's `disallowed-methods` denies the `std` transcendentals in every target, tests included). No implicit contraction. Error-free transforms are exact with or without FMA; a lane kernel on a backend with hardware FMA, or a scalar kernel in a build that targets FMA (`eft::two_prod_d`), uses a fused multiply-add for `two_prod`'s error term only on `two_prod`'s proved domain, where it gives Dekker's bits ([lanes.md](docs/lanes.md) §2); `scripts/check_fma.sh` requires the FMA build's cross-check corpora byte-identical to the default build's. The ln reciprocal stage may additionally use hardware FMA for its proved-exact residual `y*R-1`, only on the domain where the result is representable and bit-identical to the existing split reduction, including positive zero at exact cancellation; that split remains the non-FMA reference and fallback. Operations IEEE 754 requires to be correctly rounded (square root, fused multiply-add) may run on the hardware where the build has them, through `exact::sqrt` and `eft::two_prod_d`, because every conforming implementation returns the same bits ([sqrt.md](docs/sqrt.md)); the integer or error-free-transform implementation stays the reference and the fallback, and anything the standard does not fix (the transcendentals, a NaN's payload) is never taken from the platform. A vectorized path performs the scalar operation sequence per lane, apart from the proved-exact ln FMA substitution above, and returns the scalar result bit for bit. The determinism digest proves this on every supported target.
- **Expected values come from outside the implementation.** Test oracles are MPFR, mpmath and published worst-case data, never a rearrangement of the function under test. Assert bit equality wherever correct rounding is claimed; elsewhere assert the actual published bound, including its domain and special values. A tolerance must never conceal a contract violation.
- **Performance is assessed within the selected contract.** Strong APIs require same-host scalar and batched throughput/latency comparisons with the best relevant implementations of comparable contracts, profiles and explanations for material costs, investigation of credible faster algorithms, and evidence-backed review of regressions. "As performant as possible" requires this work; it is not a claim of globally optimal code or an automatic equality threshold. Weaker-contract implementations are useful diagnostic references, not mandatory parity gates for strong APIs. Fast APIs must meet or beat selected competitors with comparable numerical guarantees on declared workloads, without weakening their own bounds or determinism. Name comparator versions, domains, accuracy and special-value semantics, backends, flags and calling interfaces; do not impose parity with an arbitrarily weaker approximation. Any unmatched guarantee or unavailable comparison is explicit. Consumer call sites choose a contract using their error budgets and qualify the composed result and cost; no blanket no-slowdown promise overrides that choice. Bring generic optimization lessons such as domain partitioning, argument splitting or dispatch structure back here. Performance claims are local same-host measurements, never CI timing.
- **Algorithm choices carry evidence.** Start from relevant best-of-breed published mathematics, such as rational approximations for `erfcx` or correctly rounded elementary-function designs, subject to provenance policy. Compare runnable implementations under declared contracts and investigate credible faster structures. A weaker-contract reference's speed alone neither mandates its adoption nor rejects a stronger implementation. Document operation counts, domain splits, bounds, measurements and material tradeoffs for the selected design.
- **Provenance is clean.** Everything here can ship under MIT OR Apache-2.0 and lives in this repository. Algorithms come from published mathematics or from vendored code under a compatible license, recorded with its notices; every generated coefficient and constant comes from a versioned generator. No copyleft or unclear-license code, and an agent is never given such source ([PROVENANCE.md](docs/PROVENANCE.md), [AI-assisted contributions](docs/PROVENANCE.md#ai-assisted-contributions)).

## Explicit Approximation APIs

The architectural boundary for bounded-approximation APIs is a `fast` namespace in the existing library crate, mirroring the elementary and normal modules. Such APIs must coexist with existing APIs; no feature flag may silently change an existing function's accuracy. Share internal arithmetic, generated tables, reductions and SIMD infrastructure where their contracts permit it. A separate crate needs a concrete dependency, platform or release-lifecycle reason. This is an API design constraint, not a statement that fast APIs are implemented; the public API remains the list in `lib.rs`.

Each fast primitive must define justified per-domain absolute, relative or ULP bounds as appropriate, including zeros, cancellation, tails, underflow/overflow, NaNs and infinities. Faithful rounding is a candidate contract for individual functions, not a universal promise. Generated constants, certified/proved bounds, independent oracle tests, worst-case witnesses, source bindings and cross-target determinism remain required. Scalar and SIMD paths must return the same bits within the selected API; fast and strong APIs need not return the same bits. Dropping a rounding test or accurate fallback is valid only when the remaining implementation is proved sufficient for the fast API's entire stated contract.

Select accuracy and performance together. Before implementing a fast primitive or tightening an existing numerical path, record the consumer purpose, per-domain error bound, cost budget and acceptance rule in its derivation/evidence record using [the decision form](docs/numerical-decision-template.md). Choose the least costly candidate that satisfies both budgets and the required semantics; extra digits alone do not justify extra runtime. A generic primitive's public bound comes from its mathematical contract; the consumer separately qualifies whether that bound is sufficient for derivatives, inverses and composed results. Input noise or quote precision alone cannot justify a primitive bound. Existing correctly rounded APIs retain their guarantees and never switch to a weaker contract implicitly.

Each path records its selection domain or acceptance certificate, maximum refinement work, and the specified outcome if its bound cannot be established. An internal fast path returns only under the existing API's guarantee; a public `fast` API returns only under its own published guarantee. Use only the precision and checks needed to establish the selected contract. A fallback is justified by evidence that the contract needs it, not by a blanket preference for more precision. Work limits never turn an unestablished result into success or silently narrow a promised domain. Preserve existing special-value and error behavior; changes are explicit API decisions.

## Performance Evidence

Use pinned implementations and exact input bits on the same native host. Record CPU/ISA, OS/toolchain, features/flags, power/frequency/thermal conditions and host contention. Warm up, alternate paired runs, retain raw samples and rejected attempts through review, and report medians and spread. Separate independent throughput, dependency-chain latency, public wrapper/FFI overhead, dispatch/remainders, allocations, memory passes, table/code footprints and fallback rates. Keep oracle checks and profiling/allocation instrumentation outside uninstrumented timings. CI and emulation establish correctness, not native speed; structural code-generation checks remain useful CI gates.

Cover ordinary, boundary, cancellation, subnormal/overflow, screened/mixed-lane and fallback-heavy inputs; distinguish adversarial cases from representative frequencies. Include short slices and SIMD remainders as well as large batches, native ARM/x86 coverage, unchanged control workloads, and compositions as well as primitives. Consumer end-to-end qualification is distinct from a public synthetic workload. No reduced work, changed seed/reduction order or unannounced accuracy change counts as a speedup.

Before declaring parity or accepting a regression, the owning issue must specify the comparator/workload/hardware matrix and decision rule: repetitions and stability controls, uncertainty or equivalence treatment, and whether every required cell must pass or a justified aggregation applies. Do not infer a universal nanosecond budget, fallback ceiling or permitted slowdown from one experiment. Missing criteria or missing measurements leave the corresponding performance claim unestablished.

The decision record presents error and cost together for the same source, settings, exact inputs and output set. Report proved bounds separately from observed maxima and reference uncertainty. Show fast-path coverage, fallback frequency and fallback latency/cost by input region and for representative mixtures, including mixed SIMD lanes. Compare strong and fast APIs as distinct contracts; benchmark both when the choice changes a consumer's decision. Tightening a tolerance or adding a runtime check requires its consumer benefit and measured cost in the same review. Loosening a bound requires an independently justified contract change, never fitting the bound to failing samples. Stop investigating once the predeclared decision is supported; a missing required measurement is still unestablished. The record and PR template are review controls, not an automated timing gate; CI proof/oracle and native performance enforcement remain as specified above.

### Hotspot optimization review

Start with a profile identifying the costly operation and its contribution to
the consumer workload. For a proposed hotspot change, inspect the generated
code for the actual calling context, target, compiler and flags. Check dependency
chains, constant materialization, widening, spills, dispatch and vectorization;
source brevity or instruction counts alone do not establish a speedup. Preserve
the commands needed to reproduce the inspection and record the relevant findings.

Consider compile-time specialization using established constants and input
bounds. State and prove the assumptions, including rounding, overflow and boundary
behavior; preserve the defined outcome outside any specialized domain. An
optimization preserving an existing API's complete contract belongs in that API
when qualified; it need not introduce a separate approximate API. Qualify affected
strong and fast consumers separately where they share the optimized machinery.

Declare independent throughput and dependent latency criteria separately wherever
both matter to the consumer. Select implementations using measured consumer cost
on each supported target; a throughput win cannot stand in for a latency result.
Keep specialization and backend variants proportional to demonstrated benefit.
Do not create a general-purpose optimization subsystem without a measured need.

### Benchmark record retention

Commit the methodology: runnable harnesses, deterministic input generators,
comparator/tool pins, build flags, host requirements and acceptance rules. Keep
new generated timing samples, profiles, logs, binaries and run archives under
ignored `target/` or temporary CI artifacts. Preserve all samples and failed
attempts through review; never filter outliers or retry until a pass. Record the
source revision, host, decision and limitations in the owning issue/PR. Once
review is complete, permanent raw-run retention is optional, not a Git gate.
Correctness fixtures, worst-case witnesses, coefficient generators, certificates
and proof inputs remain versioned. Existing historical measurement directories
are not migrated incidentally. See [the native fast benchmark procedure](scripts/bench_fast/README.md).

## How a Correctly Rounded Function Is Built

Each correctly rounded function follows this pipeline, optimizing performance within its numerical contract; its derivation document is as much the deliverable as its code:

1. **Specification:** domain, special values, overflow and underflow thresholds (derived, not copied), the exact mathematical definition, and the implementations it is measured against. Distinguish comparable-contract competitors from weaker-contract diagnostic references and record the consumer contract being replaced.
2. **Argument reduction:** derived from the function's algebra, with constants generated at stated precision and their rounding error accounted for; Payne–Hanek for large trigonometric arguments.
3. **Fast path:** an approximation evaluated in binary64 or double-word arithmetic, with its algorithm, domain splits, operation count and branch behaviour justified by evidence. Its approximation error is certified by Sollya `supnorm`, its evaluation error by Gappa, and its accuracy is chosen to keep rounding-test rejection rare on the declared workloads. Measure the rate; there is no implicit universal rejection threshold. This internal fast path is distinct from an explicitly approximate public API.
4. **Rounding test:** Ziv's strategy. The fast result is returned only when its error interval provably cannot straddle a rounding boundary.
5. **Accurate path:** `Q128` or `Q256` integer-significand arithmetic (no fused multiply-add needed), with an error bound proved small enough for the published worst cases of that function. Where no worst-case result covers a domain, correct rounding there is not claimed; the proved bound is stated instead. Its rate is measured and reported; an input region that always reaches it is a performance defect unless shown to be unavoidable.
6. **Generators:** every coefficient and constant comes from a versioned generator under `generators/`, with pinned tools and a recorded precision, and CI replays it. A canonical algorithm's coefficients are regenerated here to the fast path's required accuracy.
7. **Measurement:** same-host scalar and batched throughput and latency against the step 1 references, with the accurate-path rate. Complete the contract-specific performance evaluation and regression review before declaring the work complete or shipping it. Investigate material costs and credible faster alternatives. An unresolved required criterion stays open; merely recording a shortfall does not satisfy it. A gap against a weaker-contract reference is diagnostic evidence, not by itself a failed strong-API acceptance criterion.

## Invariants and Trust Boundaries

Every invariant names its enforcement, chosen from this ladder: (1) unrepresentable by construction (types, `no_std`, the absence of a dependency), (2) enforced inside the owning function, (3) only then a tested convention hardened by mutation gates. Never assert source text, byte offsets or statement order in a test. A proof artifact is bound by hash to the source it describes; changing that source fails the gate until the proof is rerun. Escape hatches (an allowed lint, a skipped gate) ship with their reason and exit condition.

## Engineering and Review Principles

- Treat technical debt as a code-review concern: fix the defect pattern, not just its first instance. Search the affected crate or module for same-pattern siblings and report what was checked and found. Check other implementations of the same contract when there is evidence they share the defect; do not turn a local repair into an unrelated cross-repository audit. Fix siblings required by the agreed contract in the same change, coordinating with in-flight work where necessary. If that scope reveals disproportionate cost, a new design decision, or a third-party responsibility, apply Strategic Pragmatism before expanding implementation. Any accepted deferral or scope reduction remains explicit and is not reported as a completed fix. Split genuinely necessary large changes into reviewable dependent PRs; do not manufacture extra PRs for incidental refinements.
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
./scripts/check_fma.sh             # scalar FMA: tests, digest, identical corpora; x86-64 FMA or aarch64 NEON
./scripts/check_lane_codegen.sh    # no AVX2/AVX-512F lane operation compiled out of line, x86-64 Linux
./scripts/check_advisories.sh
./scripts/check_generators.sh
cargo run --locked -p morphiq-numerics-reference --bin crosscheck-corpus > target/crosscheck.txt
MORPHIQ_INTERNAL_CORPUS=$PWD/target/internal-crosscheck.txt cargo test --locked -p morphiq-numerics --lib internal_crosscheck -- --ignored
# in the pinned Debian image (see the formal job): ./scripts/write_gappa_proofs.sh target/gappa-proofs
# then, in the pinned Coq image (.cargo/coq-image): ./scripts/check_formal.sh target/crosscheck.txt target/internal-crosscheck.txt target/gappa-proofs
#   (--build DIR keeps the proof build in DIR and reuses it next time; see the script's header)
#   (--changed FILE --base-audit FILE audits only the kernel proofs a change can affect, as CI does on pull requests; the whole audit runs without them, and on every push to main; a pull request that touches no proof, bound file, library source or lane file skips the lane, see scripts/formal_relevant.py, and the Gappa proofs are cached and rewritten only for changed certificates, see scripts/write_gappa_proofs.sh)
# after a passing cached build, in the same image: ./scripts/check_formal_negative.sh binding /path/to/coq-deps.tar.gz DIR target/crosscheck.txt target/internal-crosscheck.txt target/gappa-proofs
#   (repeat for admitted, axiom, certificate, crosscheck, internal-crosscheck, bvn-crosscheck; each uses an isolated copy)
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

A change is complete when its contract is stated, its implementation follows a documented derivation with generated constants, independent oracles confirm bit equality wherever correct rounding is claimed and the actual bound elsewhere, its proofs are rerun and bound, its contract-specific performance evaluation and regression review are complete (including the declared parity criterion for fast APIs), its numerical decision record establishes the selected error and cost budgets together, every gate passes on every target, the determinism digest is unchanged or deliberately updated with the reason, documentation describes the new current state, and same-pattern siblings required by the agreed contract are fixed.

Explicitly accepted scope changes are recorded with their remaining limitations; deferred work is not counted as delivered. Untracked debt or a green test suite alone does not make a change complete.

A known shortfall in correctness, performance or architecture within the agreed contract keeps the affected work incomplete until it is fixed and the required evidence establishes that. Passing CI, merging code, documenting the shortfall or moving it to a follow-up issue does not make that work complete. Missing evidence also leaves the corresponding requirement unestablished; it is never reported as satisfied.
