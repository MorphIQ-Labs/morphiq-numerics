#!/usr/bin/env sh
# Exercise scalar hardware FMA and compare every corpus word with Dekker.
# On aarch64, NEON supplies binary64 FMA; no_std selects the Dekker baseline.
# On x86-64, both builds use std and only the FMA build enables +fma.
set -eu
cd "$(dirname "$0")/.."

case "$(uname -m)" in
  arm64|aarch64)
    baseline_flags=""
    baseline_features=""
    fused_flags=""
    ;;
  x86_64)
    if ! grep -qw fma /proc/cpuinfo; then
      echo "this host has no FMA; the FMA build cannot be exercised here" >&2
      exit 1
    fi
    baseline_flags="-C target-feature=-fma"
    baseline_features="std"
    fused_flags="-C target-feature=+fma"
    ;;
  *) echo "unsupported scalar FMA host" >&2; exit 1 ;;
esac

unset CARGO_ENCODED_RUSTFLAGS
out=target/fma-check
mkdir -p "$out"
corpora() {
  cargo run --locked -q -p morphiq-numerics-reference --no-default-features --features "$2" --bin crosscheck-corpus > "$out/$1.txt"
  MORPHIQ_INTERNAL_CORPUS="$PWD/$out/$1-internal.txt" \
    cargo test --locked -q -p morphiq-numerics --no-default-features --features "$2" --lib internal_crosscheck -- --ignored >/dev/null
}

RUSTFLAGS="$baseline_flags" CARGO_TARGET_DIR=target/dekker corpora default "$baseline_features"
RUSTFLAGS="$fused_flags" CARGO_TARGET_DIR=target/fma cargo test --locked --workspace --all-features
RUSTFLAGS="$fused_flags" CARGO_TARGET_DIR=target/fma corpora fma std

cmp "$out/default.txt" "$out/fma.txt"
cmp "$out/default-internal.txt" "$out/fma-internal.txt"
echo "fma: $(wc -l < "$out/fma.txt") public and $(wc -l < "$out/fma-internal.txt") internal cross-check lines identical"
