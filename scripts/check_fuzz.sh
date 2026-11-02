#!/usr/bin/env bash
# Replay all versioned elementary inputs, then mutate them with libFuzzer.
# Usage: ./scripts/check_fuzz.sh [seconds-per-feature-mode, default 60]
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
mkdir -p target/fuzz/seeds target/fuzz/artifacts target/fuzz/logs
python3 scripts/seed_elementary_fuzz.py target/fuzz/seeds
# Tests include planted wrong results and a >2000-bit subnormal midpoint.
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
  cargo run --release --manifest-path fuzz/Cargo.toml --locked "${features[@]}" \
    --bin replay -- target/fuzz/seeds fuzz/regressions \
    > "target/fuzz/logs/replay-$mode.log" 2>&1
  corpus="target/fuzz/corpus-$mode"
  mkdir -p "$corpus"
  # A separate writable corpus keeps generated seeds and retained regressions
  # intact. Logs, minimized failures and evolved corpora survive failed runs.
  CARGO_NET_OFFLINE=true cargo +"$nightly" fuzz run elementary "$corpus" target/fuzz/seeds fuzz/regressions \
    --features "$fuzz_features" -- \
    -max_total_time="$seconds" -max_len=257 -timeout=30 -rss_limit_mb=4096 \
    -artifact_prefix=target/fuzz/artifacts/ -print_final_stats=1 \
    2>&1 | tee "target/fuzz/logs/campaign-$mode.log"
  cmp fuzz/Cargo.lock target/fuzz/Cargo.lock.before
done
