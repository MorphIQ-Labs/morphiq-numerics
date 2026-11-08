# Contributing to morphiq-numerics

**[`AGENTS.md`](AGENTS.md) is the working contract for this repository**:
- the correct-rounding and target-independence contracts;
- the invariants and their enforcement;
- the assurance gates;
- the pull-request and release rules;
- the definition of done.

It applies to human and agent contributors alike. Read it and the
[provenance policy](docs/PROVENANCE.md) before your first change. Scope and
progress are tracked in the repository's
[milestones](https://github.com/MorphIQ-Labs/morphiq-numerics/milestones) and issues.

## Provenance comes first

Everything here must be distributable under MIT OR Apache-2.0 and live in
this repository. Code from another library is welcome under a compatible
license (MIT, BSD, ISC, Zlib, BSL-1.0; not Apache-2.0 alone): vendor it, keep its
notices, and record it in `THIRD_PARTY_NOTICES.md`. Copyleft (GPL, LGPL, MPL,
APSL) and unlicensed code can't come in.

If you consulted a copyleft or unlicensed implementation while working on a
function, say so in the pull request: which one, which version, and what you
read. See [PROVENANCE.md](docs/PROVENANCE.md).

If a language model assisted your change, its rules are in
[AI-assisted contributions](docs/PROVENANCE.md#ai-assisted-contributions): what
it may be given, and what the pull request discloses.

## Running the gates locally

```sh
cargo fmt --all -- --check
rustup target add aarch64-unknown-linux-gnu thumbv7em-none-eabihf
./scripts/check_clippy.sh
cargo test --workspace --all-features --locked
RUSTDOCFLAGS="-D warnings" cargo doc --workspace --all-features --no-deps --locked
rustup target add thumbv7em-none-eabihf
cargo build -p morphiq-numerics --locked --target thumbv7em-none-eabihf
cargo build -p morphiq-numerics --locked --target thumbv7em-none-eabihf --features simd
cargo install --locked cargo-audit --version "$(cat .cargo/audit-version)"
./scripts/check_advisories.sh
cargo install --locked cargo-deny --version "$(cat .cargo/deny-version)"
cargo deny --locked check licenses
cargo install --locked cargo-mutants --version "$(cat .cargo/mutants-version)"
python3 -m unittest scripts.test_numerical_mutations
python3 scripts/check_numerical_mutations.py target/numerical-mutations
./scripts/check_fuzz_licenses.sh
./scripts/install_fuzz.sh
./scripts/check_fuzz.sh 60
```

The [numerical mutation gate](scripts/mutations/README.md) runs on macOS and
Linux. Use a fresh output directory for each run so earlier receipts survive.

The [MPFR fuzzing guide](fuzz/README.md) describes the strong and fast elementary contracts,
seed corpus, scalar/SIMD campaigns and failure replay. MPFR remains in the
independent unpublished `fuzz/` workspace.

## Pull requests

- **Title:** a [conventional commit](https://www.conventionalcommits.org/),
  for example `feat(elementary): correctly rounded exp` or
  `fix(rng): xoshiro256++ long_jump constants`. It becomes the squash commit
  that release automation reads.
- **Description:** what changed and why, and the numerical impact (which
  results can change, and why the new ones are correct).
- **Numerical decisions:** link the derivation/evidence record using
  [the decision form](docs/numerical-decision-template.md). The PR template
  prompts for the evidence required by [AGENTS.md](AGENTS.md); prose-only
  changes can state that no numerical result or cost changes.
- **Issues:** close the ones it resolves with `Closes #N`.

Every CI job is a required check, and `main` accepts changes only through
squash-merged pull requests.

## Releases

Releases are automated by release-plz. After each merge it keeps a
`chore: release` pull request open with the version bump and the
`CHANGELOG.md` section written from the squash subjects; a maintainer merges
it like any other pull request once its checks pass, and that merge tags
`v{version}` and creates the GitHub release. Never push a tag, bump the
version or edit a released changelog section by hand. A tag always equals
the workspace version at its commit; `scripts/check_release_version.sh`
enforces it.

The independent `fuzz/` workspace has its own lockfile, which release-plz does
not update. After each version bump the release workflow refreshes it on the
release branch (`scripts/sync_release_fuzz_lock.sh`), committing through
GitHub's API so that GitHub signs the commit: `main` admits only verified
signatures. The required license check uses `--locked` and rejects a stale fuzz
lockfile. If the step fails, refresh it by hand with a signed commit, checking
that only the local library and arch package versions changed:

```sh
cargo update --manifest-path fuzz/Cargo.toml --workspace
./scripts/check_fuzz_licenses.sh
```

Until 0.1 a release is a git tag only (`v0.0.N`); 0.1.0 is reserved for the
first crates.io release ([#90](https://github.com/MorphIQ-Labs/morphiq-numerics/issues/90)).

## License

By contributing, you agree that your contributions are dual licensed under
MIT OR Apache-2.0, as described in the [README](README.md#license).

## Release package verification

From a clean committed checkout, run `python3 scripts/check_packages.py` with
the pinned toolchain. Use `--out target/package-check-2` for a subsequent run;
the output directory must be new. The command keeps its archives, build output
and verification receipt under that directory and never uploads a package.

Before first publication, Cargo cannot resolve the optional architecture crate
from crates.io while both source manifests have `publish = false`. The check
archives the committed tree and enables only those two flags in an isolated
copy. Like Tollgate, the check runs `cargo publish --locked --workspace --dry-run`
and requires the publishable set to match the release allowlist. Cargo supplies
its temporary registry and verifies both normalized archives. The source manifests and release-plz
publication guards stay unchanged.

The check verifies packaged licenses, notices, README links and dependency
metadata. An external consumer uses only the unpacked archives, with an offline
patch for the packaged architecture dependency. It runs with default, `std`,
`simd` and combined features and builds dependency documentation with warnings
denied. This tests package consumption; the complete oracle/proof/mutation
suite still runs from the repository with its unpublished tooling and fixtures.
Packaging success does not establish numerical or performance qualification.

Initial crates.io publication requires token authentication before Trusted
Publishing can be configured for each crate. Registry enablement and the
bootstrap authentication belong in the reviewed release change after #90's
acceptance is met; this preflight does not enable either. Keep the normal
release-plz version/tag workflow and publish the architecture dependency before
the library. Subsequent Trusted Publishing uses the configured repository and
workflow identity with job-scoped `id-token: write`, as described in the
[release-plz setup](https://release-plz.dev/docs/github/quickstart).

## Formal families

The full local gate remains `scripts/check_formal.sh` with the public corpus,
internal corpus and generated Gappa proof directory as its three arguments.
Run it in the pinned Coq image, with the pinned dependency archive as described
in `AGENTS.md`.

`--plan-only --plan-out target/formal-plan.json` writes the check ownership and
`coqdep` closures without building proofs or claiming a passing gate.
`--family bivariate --build target/formal-bivariate` builds only that family's
closure, audits its owned kernel/certificate entries and runs its extraction.
The complete source-binding and no-admission checks still run. Omit `--family`
to run the full gate. `--build-only` never establishes assurance by itself.

Families follow proof-source ownership. The base audit stays together in
`shared`. The public and internal extraction models remain composite units
(`crosscheck` and `internal-crosscheck`); their dependency closures include the
transcriptions they actually import. Bivariate owns its separate extraction.
The planner requires every kernel entry, certificate and extraction to have
one owner. No proof or axiom allowlist is weakened by selecting a family.

CI prepares identical corpora/generated proofs once. When all families are
selected, one unsplit full gate builds and audits their shared dependencies
once. A proper subset runs as family jobs, with separate caches keyed by
their dependency content and pinned controls. The full gate retains its own
cache and can restore the existing unsplit build cache. All restored builds
are checked against the current sources and toolchain; audits always rerun.
Known proof/certificate changes select their owning and dependent families;
shared, toolchain, gate, removed or unclassified paths select all. Main pushes
always select all. The required `formal (coq)` aggregate checks prerequisite
outcomes and the exact completion evidence: one full-gate receipt for an
all-family selection, or one receipt per selected family for a proper subset,
including their source and corpus identities. Mixed execution evidence fails. Missing, duplicate, stale, failed or skipped selected work
cannot pass. Prose-only handling retains the repository's narrow allowlist.
Build/audit/extraction timings and failure logs are retained as CI artifacts.

For a reproducible cold/warm comparison, run `scripts/bench_formal.sh` in the
same pinned Coq image. Its five arguments are the dependency archive, public
corpus, internal corpus, generated Gappa proof directory and a new output
directory under `target/`. Add `--family NAME` to measure one family; omitting
it measures the full gate. It records the host, source/input hashes, separate
build and audit wall times, exit statuses and raw logs. The cold pass requires
an unused directory; the warm pass reuses its compiled proofs and repeats all
audits and extractions. Keep failed and interrupted attempts through review.
For a parallel CI matrix, report elapsed time from planning through aggregation
separately from the sum of runner times; summing parallel stage times does not
give the feedback latency.
