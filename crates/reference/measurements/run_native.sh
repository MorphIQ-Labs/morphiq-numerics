#!/usr/bin/env bash
# Native same-host measurements of the lane kernels and their compositions
# (docs/lanes.md §7). A local measurement, never a CI step or gate.
#
#   crates/reference/measurements/run_native.sh OUT_DIR [REPETITIONS]
#
# Run from the repository root on an otherwise idle host. Everything is
# compiled first; each repetition then runs, as separate pinned processes:
# the native_performance tests (every kernel, mode, backend and length, and the
# cache experiment), normal_local_performance (all workloads at 1,024, then
# ordinary and mixed at 1, 2, 3, 8 and 17), log_space measure_cost,
# bench-batched, bench-erfcx, bench-exp-stages and the external-consumer
# normal benchmark (normal-m1pro/consumer-inlining/benchmark.rs). The host,
# toolchain, revision, frequency settings and load are written to
# OUT_DIR/environment.txt, the load also before and after every process.
#
# MORPHIQ_BENCH_CPU (default 2) is the logical CPU every process is pinned
# to. Any MORPHIQ_LANES_BENCH_* variable is passed through to the lanes
# benchmark. Summarize with summarize_lanes.py.
set -euo pipefail

out=${1:?usage: run_native.sh OUT_DIR [REPETITIONS]}
repetitions=${2:-2}
cpu=${MORPHIQ_BENCH_CPU:-2}
root=$(git rev-parse --show-toplevel)
cd "$root"
mkdir -p "$out"
pin=(taskset -c "$cpu")

echo "== building" >&2
cargo test --release --locked -p morphiq-numerics --all-features --lib --no-run 2>"$out/build.log"
cargo build --release --locked -p morphiq-numerics --all-features 2>>"$out/build.log"
cargo build --release --locked -p morphiq-numerics-reference --features simd,std \
    --bin bench-batched --bin bench-erfcx --bin bench-exp-stages 2>>"$out/build.log"
lib_test=$(cargo test --release --locked -p morphiq-numerics --all-features --lib --no-run \
    --message-format=json 2>/dev/null | python3 -I -c '
import json, sys
for line in sys.stdin:
    m = json.loads(line)
    if m.get("reason") == "compiler-artifact" and m.get("executable") and m["target"]["name"] == "morphiq_numerics":
        print(m["executable"])')
consumer="$out/normal-consumer-bench"
rustc -O -C codegen-units=1 --edition=2024 \
    crates/reference/measurements/normal-m1pro/consumer-inlining/benchmark.rs \
    --extern morphiq_numerics=target/release/libmorphiq_numerics.rlib \
    -L dependency=target/release/deps -o "$consumer"

{
    echo "date: $(date -u +%Y-%m-%dT%H:%M:%SZ)"
    echo "revision: $(git rev-parse HEAD)"
    echo "worktree_clean: $(git diff --quiet HEAD && echo yes || echo no)"
    echo "pinned_cpu: $cpu"
    echo "repetitions: $repetitions"
    echo "lib_test: $lib_test"
    echo "rustflags: ${RUSTFLAGS:-unset}"
    env | grep '^MORPHIQ_' | sed 's/^/env: /' || true
    echo "kernel: $(uname -srm)"
    echo "os: $(. /etc/os-release && echo "$PRETTY_NAME")"
    echo "governor: $(cat /sys/devices/system/cpu/cpu"$cpu"/cpufreq/scaling_governor 2>/dev/null || echo unknown)"
    echo "epp: $(cat /sys/devices/system/cpu/cpu"$cpu"/cpufreq/energy_performance_preference 2>/dev/null || echo unknown)"
    echo "intel_no_turbo: $(cat /sys/devices/system/cpu/intel_pstate/no_turbo 2>/dev/null || echo unknown)"
    echo "smt_sibling: $(cat /sys/devices/system/cpu/cpu"$cpu"/topology/thread_siblings_list)"
    rustc -vV | sed 's/^/rustc: /'
    lscpu | sed 's/^/lscpu: /'
} >"$out/environment.txt"

load() { echo "load $1: $(cut -d' ' -f1-3 /proc/loadavg)" >>"$out/environment.txt"; }

for r in $(seq 1 "$repetitions"); do
    echo "== repetition $r" >&2
    load "before lanes $r"
    "${pin[@]}" "$lib_test" native_performance --ignored --nocapture --test-threads=1 \
        >"$out/lanes-$r.csv" 2>"$out/lanes-$r.log"
    load "before normal $r"
    {
        "${pin[@]}" "$lib_test" normal_local_performance --ignored --nocapture --test-threads=1
        for workload in ordinary mixed; do
            for length in 1 2 3 8 17; do
                MORPHIQ_NORMAL_BENCH_WORKLOAD=$workload MORPHIQ_NORMAL_BENCH_LENGTH=$length \
                    "${pin[@]}" "$lib_test" normal_local_performance --ignored --nocapture --test-threads=1
            done
        done
    } >"$out/normal-$r.txt" 2>&1
    load "before log_space $r"
    "${pin[@]}" "$lib_test" log_space::tests::measure_cost --ignored --nocapture --test-threads=1 \
        >"$out/log-space-$r.txt" 2>&1
    load "before reference bins $r"
    "${pin[@]}" target/release/bench-batched >"$out/bench-batched-$r.md"
    "${pin[@]}" target/release/bench-erfcx >"$out/bench-erfcx-$r.csv"
    "${pin[@]}" target/release/bench-exp-stages >"$out/bench-exp-stages-$r.md"
    load "before consumer $r"
    "${pin[@]}" "$consumer" >"$out/consumer-$r.txt"
    load "after repetition $r"
done
echo "== done: $out" >&2
