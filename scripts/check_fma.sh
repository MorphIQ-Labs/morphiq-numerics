#!/usr/bin/env sh
# The scalar kernels' FMA build (eft::two_prod_d, docs/lanes.md §2).
#
# On an x86-64 host with FMA:
#   1. build with -C target-feature=+fma and run the workspace tests: the
#      oracle fixtures (bit equality) and the determinism digest;
#   2. write both cross-check corpora with and without FMA and require them
#      byte-identical: on every input they cover, each fused error term is
#      Dekker's, so every intermediate and result keeps its bits.
set -eu
cd "$(dirname "$0")/.."

if ! grep -qw fma /proc/cpuinfo; then
  echo "this host has no FMA; the FMA build cannot be exercised here" >&2
  exit 1
fi

out=target/fma-check
mkdir -p "$out"
# std is part of two_prod_d's FMA gate. Keep it enabled in both corpora;
# changing RUSTFLAGS alone would otherwise compare two Dekker builds.
corpora() {
  cargo run --locked -q -p morphiq-numerics-reference --features std --bin crosscheck-corpus > "$out/$1.txt"
  MORPHIQ_INTERNAL_CORPUS="$PWD/$out/$1-internal.txt" \
    cargo test --locked -q -p morphiq-numerics --features std --lib internal_crosscheck -- --ignored >/dev/null
}

corpora default
RUSTFLAGS="-C target-feature=+fma" CARGO_TARGET_DIR=target/fma cargo test --locked --workspace --all-features
RUSTFLAGS="-C target-feature=+fma" CARGO_TARGET_DIR=target/fma corpora fma

cmp "$out/default.txt" "$out/fma.txt"
cmp "$out/default-internal.txt" "$out/fma-internal.txt"
echo "fma: $(wc -l < "$out/fma.txt") public and $(wc -l < "$out/fma-internal.txt") internal cross-check lines identical"
