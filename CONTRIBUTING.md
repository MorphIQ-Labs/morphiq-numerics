# Contributing to morphiq-numerics

**[`AGENTS.md`](AGENTS.md) is the working contract for this repository**:
- the correct-rounding and target-independence contracts;
- the invariants and their enforcement;
- the assurance gates;
- the pull-request and release rules;
- the definition of done.

It applies to human and agent contributors alike. Read it, the
[plan](docs/PLAN.md) and the [provenance policy](docs/PROVENANCE.md) before
your first change.

## Provenance comes first

Every algorithm and constant here must be ours to license under
MIT OR Apache-2.0. Don't copy or adapt code, coefficient tables or
implementation structure from any other math library, however permissive its
license.

If you consulted another implementation while working on a function, say so in
the pull request: which one, which version, and what you read. See
[PROVENANCE.md](docs/PROVENANCE.md).

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
