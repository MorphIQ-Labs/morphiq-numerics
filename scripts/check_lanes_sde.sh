#!/usr/bin/env sh
# Runs the lane tests on AVX-512F under Intel's Software Development Emulator
# (scripts/install_sde.sh puts sde64 on PATH), emulating a Sapphire Rapids CPU:
# the arch crate's operation tests, the lane kernels against the scalar
# functions on every backend (AVX-512F, AVX2, SSE2, scalar), and the
# determinism digest with the batched functions in lanes. Release builds keep
# the emulated run short; MORPHIQ_LANE_CASES scales the random corpora.
set -eu
cd "$(dirname "$0")/.."
command -v sde64 >/dev/null || { echo "sde64 is required; see scripts/install_sde.sh" >&2; exit 127; }
export CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUNNER="sde64 -spr --"
export MORPHIQ_REQUIRE_BACKENDS=avx512,avx2,sse2,scalar
export MORPHIQ_LANE_CASES="${MORPHIQ_LANE_CASES:-16384}"
cargo test --locked --release -p morphiq-numerics-arch --features std -- --nocapture
cargo test --locked --release -p morphiq-numerics --features simd,std --lib lanes -- --nocapture
cargo test --locked --release -p morphiq-numerics-reference --features simd,std --test determinism
echo "lanes on AVX-512F (SDE): OK"
