#!/usr/bin/env sh
# Runs the reference suite, the determinism digest included, on one target:
#   x86_64-unknown-linux-musl, aarch64-unknown-linux-musl  natively on Linux;
#   wasm32-wasip1                                         under wasmtime (install_wasmtime.sh);
#   thumbv7em-none-eabihf                                 bare metal, on QEMU's mps2-an386
#                                                         (Cortex-M4F), digest only.
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
  thumbv7em-none-eabihf)
    command -v qemu-system-arm >/dev/null || { echo "qemu-system-arm is required" >&2; exit 127; }
    rustup target add "$target" >/dev/null
    # The binary prints the digest over semihosting and exits nonzero on a mismatch.
    CARGO_TARGET_THUMBV7EM_NONE_EABIHF_RUNNER="qemu-system-arm -cpu cortex-m4 -machine mps2-an386 -nographic -semihosting-config enable=on,target=native -kernel" \
      cargo run --locked --release -p morphiq-numerics-digest-embedded --target "$target"
    echo "digest on $target: OK"
    exit 0
    ;;
  *) echo "unsupported digest target: $target" >&2; exit 1 ;;
esac
rustup target add "$target" >/dev/null
cargo test --locked -p morphiq-numerics-reference --target "$target"
echo "digest on $target: OK"
