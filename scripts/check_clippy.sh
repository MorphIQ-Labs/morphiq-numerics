#!/usr/bin/env sh
# Lint the native workspace, ARM NEON, and the no_std scalar fallback.
# Cross-target Clippy checks compilation without linking or executing binaries.
# Install the targets with:
#   rustup target add aarch64-unknown-linux-gnu thumbv7em-none-eabihf
set -eu
cd "$(dirname "$0")/.."

cargo clippy --workspace --all-targets --all-features --locked -- -D warnings
cargo clippy --workspace --all-targets --all-features --locked \
  --target aarch64-unknown-linux-gnu -- -D warnings
cargo clippy -p morphiq-numerics --lib --features simd --locked \
  --target thumbv7em-none-eabihf -- -D warnings
