#!/usr/bin/env sh
# The same exact tools locally and in CI; no floating nightly.
set -eu
cd "$(dirname "$0")/.."
rustup toolchain install "$(cat .cargo/fuzz-nightly-version)" --profile minimal
cargo install --locked cargo-fuzz --version "$(cat .cargo/fuzz-version)"
