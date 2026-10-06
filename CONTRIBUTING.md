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
cargo clippy --workspace --all-targets --all-features --locked -- -D warnings
cargo test --workspace --all-features --locked
RUSTDOCFLAGS="-D warnings" cargo doc --workspace --all-features --no-deps --locked
rustup target add thumbv7em-none-eabihf
cargo build -p morphiq-numerics --locked --target thumbv7em-none-eabihf
cargo install --locked cargo-audit --version "$(cat .cargo/audit-version)"
./scripts/check_advisories.sh
cargo install --locked cargo-deny --version "$(cat .cargo/deny-version)"
cargo deny --locked check licenses
```

## Pull requests

- **Title:** a [conventional commit](https://www.conventionalcommits.org/),
  for example `feat(elementary): correctly rounded exp` or
  `fix(rng): xoshiro256++ long_jump constants`. It becomes the squash commit
  that release automation reads.
- **Description:** what changed and why, and the numerical impact (which
  results can change, and why the new ones are correct).
- **Issues:** close the ones it resolves with `Closes #N`.

Every CI job is a required check, and `main` accepts changes only through
squash-merged pull requests.

## License

By contributing, you agree that your contributions are dual licensed under
MIT OR Apache-2.0, as described in the [README](README.md#license).
