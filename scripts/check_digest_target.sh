#!/usr/bin/env sh
# Runs the reference suite, the determinism digest included, on one target:
#   x86_64-unknown-linux-musl, aarch64-unknown-linux-musl  natively on Linux;
#   wasm32-wasip1                                         under wasmtime (install_wasmtime.sh).
# The digest must equal crates/reference/determinism.sha256 there too.
set -eu
cd "$(dirname "$0")/.."
target=${1:?usage: check_digest_target.sh TARGET}
case "$target" in
  wasm32-wasip1)
    command -v wasmtime >/dev/null || { echo "wasmtime is required; see scripts/install_wasmtime.sh" >&2; exit 127; }
    export CARGO_TARGET_WASM32_WASIP1_RUNNER=wasmtime
    ;;
  x86_64-unknown-linux-musl | aarch64-unknown-linux-musl) ;;
  *) echo "unsupported digest target: $target" >&2; exit 1 ;;
esac
rustup target add "$target" >/dev/null
cargo test --locked -p morphiq-numerics-reference --target "$target"
echo "digest on $target: OK"
