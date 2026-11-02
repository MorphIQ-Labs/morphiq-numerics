#!/usr/bin/env bash
# Replay versioned elementary inputs, then mutate them with libFuzzer.
# Usage: ./scripts/check_fuzz.sh [seconds-per-target-and-mode, default 60]
set -euo pipefail
cd "$(dirname "$0")/.."
seconds=${1:-60}
if [[ ! "$seconds" =~ ^[1-9][0-9]*$ ]]; then
  echo 'fuzz duration must be a positive integer in seconds' >&2
  exit 2
fi
nightly=$(cat .cargo/fuzz-nightly-version)
required=$(cat .cargo/fuzz-version)
if [[ "$(cargo fuzz --version)" != "cargo-fuzz $required" ]]; then
  echo 'Install pinned tools with ./scripts/install_fuzz.sh' >&2
  exit 127
fi
mkdir -p target/fuzz/logs
for target in elementary fast_elementary; do
  python3 scripts/seed_elementary_fuzz.py "target/fuzz/seeds-$target" --target "$target"
done
# Includes planted wrong results, boundary violations and oracle midpoint tests.
cargo fmt --manifest-path fuzz/Cargo.toml -- --check
cargo clippy --manifest-path fuzz/Cargo.toml --all-targets --all-features --locked -- -D warnings
cp fuzz/Cargo.lock target/fuzz/Cargo.lock.before
for mode in scalar simd; do
  features=()
  fuzz_features=fuzzing
  if [[ "$mode" == simd ]]; then
    features=(--features simd)
    fuzz_features=fuzzing,simd
  fi
  cargo test --manifest-path fuzz/Cargo.toml --locked "${features[@]}" --lib
  for target in elementary fast_elementary; do
    max_len=257
    if [[ "$target" == fast_elementary ]]; then max_len=1041; fi
    seeds="target/fuzz/seeds-$target"
    regressions="fuzz/regressions/$target"
    cargo run --release --manifest-path fuzz/Cargo.toml --locked "${features[@]}" \
      --bin replay -- "$target" "$seeds" "$regressions" \
      > "target/fuzz/logs/replay-$target-$mode.log" 2>&1
    corpus="target/fuzz/corpus-$target-$mode"
    artifacts="target/fuzz/artifacts/$target/$mode/"
    mkdir -p "$corpus" "$artifacts"
    # Separate writable corpora preserve seeds, regressions and target identity.
    CARGO_NET_OFFLINE=true cargo +"$nightly" fuzz run "$target" "$corpus" "$seeds" "$regressions" \
      --features "$fuzz_features" -- \
      -max_total_time="$seconds" -max_len="$max_len" -timeout=30 -rss_limit_mb=4096 \
      -artifact_prefix="$artifacts" -print_final_stats=1 \
      2>&1 | tee "target/fuzz/logs/campaign-$target-$mode.log"
    cmp fuzz/Cargo.lock target/fuzz/Cargo.lock.before
  done
done
