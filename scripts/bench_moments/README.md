# Native moment accumulator comparison

This is a direct Rust-call comparison, compiled with the repository's pinned
Rust toolchain. The implementation and original comparison recurrences live in
`crates/morphiq-numerics/src/reduce/moments/performance.rs`. No third-party
implementation source is used. Pin the repository revision and retain the
binary/source hashes with every attempt. Timing output belongs under ignored
`target/`; never overwrite an attempt.

## Contracts and matrix

- `moments`: the public checked, compensated accumulator, including its finite
  absolute error certificate and final variance readout; constant storage.
- `checked_welford`: first-sample-shifted Welford using the same checked
  double-word primitives and error propagation; constant storage. Its error
  radius can differ. This is an alternative algorithm, not an oracle.
- `ordinary_welford`: binary64 Welford without a certificate; diagnostic only.
- `corrected_two_pass`: `sum2`, a retained centered buffer, `sum_squares2`, and
  the residual correction; no returned certificate. Timing includes allocation
  and four physical traversals: the original mean sum, centering into a buffer,
  the residual sum, and the squared-deviation sum. This represents the storage
  tradeoff, not equivalent guarantees.

Exact inputs use a fixed integer xorshift seed, with lengths 3, 65, and 4096:
ordinary nonnegative observations, large means/small spreads, a first-observation
outlier, and mixed signs. One dependent state measures streaming latency; four
independent states measure throughput. Each state sees the same fixed sequence.
Mean, variance, standard-error readouts and repeated ordered merges are measured
separately. Empty, constant, subnormal/overflow and rejected operations are
correctness cases, not representative throughput populations; there is no
fallback or SIMD dispatch in this API. Existing reduction controls are unchanged.

Use native aarch64 and native x86-64-v3 or later. Run correctness/oracle tests
before timing. The independent exact-integer and MPFR tests qualify the public
API; timing does not establish accuracy. Archive their logs with the attempt.

## Protocol and decision

The test emits all 18 rounds, including three warmups. The four implementations
rotate position each round. Retain all remaining 15 samples; do not trim outliers
or retry an unchanged failing campaign. Each cell processes at least 65,536
observations per round (eight repetitions minimum). Report medians, quartiles,
all paired ratios, and the min/max ratio. Record any unstable or interrupted
attempt as such; do not call it acceptance evidence.

The primary decision cells are lengths 65 and 4096, every input population,
separately for dependent latency and independent throughput, on each host.
Select anchored sums when their paired median cost is below checked Welford in
every primary cell and at least 12 of 15 paired rounds favor them in each cell.
Otherwise investigate the specific cost and leave that cell unqualified. The
three-observation cells and separate merge/readout costs explain fixed overhead;
no aggregate can conceal a failed primary cell. Weaker-contract references have
no parity requirement. This is a local algorithm-selection rule, not a universal
nanosecond budget or a consumer end-to-end qualification.

## Run and retain

Finish other local builds/tests before timing. Capture CPU/ISA/topology,
OS/toolchain, power mode, thermal/frequency information, affinity and contention
before and after. Record unavailable telemetry explicitly. On Linux pin to a
physical core with its SMT sibling idle, or use a VM configured with one thread
per core. Do not terminate unrelated processes. This is a VM measurement when
run in a VM; hardware sharing/noisy neighbors remain a limitation.

```sh
# aarch64; choose a fresh attempt directory first
mkdir target/moments-arm-attempt-1
cargo test --release --locked -p morphiq-numerics --lib --all-features \
  native_moments_performance --no-run
cargo test --release --locked -p morphiq-numerics --lib --all-features \
  native_moments_performance -- --ignored --nocapture --test-threads=1 \
  > target/moments-arm-attempt-1/raw.log 2>&1

# native x86 (same protocol and inputs), with observed CPU 0 available
RUSTFLAGS='-C target-cpu=x86-64-v3' cargo test --release --locked \
  -p morphiq-numerics --lib --all-features native_moments_performance --no-run
RUSTFLAGS='-C target-cpu=x86-64-v3' taskset -c 0 cargo test --release --locked \
  -p morphiq-numerics --lib --all-features native_moments_performance \
  -- --ignored --nocapture --test-threads=1 > target/moments-x86-attempt-1/raw.log 2>&1
```

Inspect the built test executable's generated code for the actual target and
flags (LLVM objdump or the native disassembler). Record checked-operation calls,
divisions, spills and the interleaving of independent states. Keep profiles and
allocation instrumentation outside the uninstrumented measurement. The public
state has fixed fields and no allocator access; two-pass allocations are explicit
in the reference. Retain source revision, commands, observations, raw rounds,
summary, executable hash, and any failed attempts through review. Results and
limitations belong in issue #285 / its PR.

Summarize a complete attempt with
`python3 scripts/bench_moments/summarize.py ATTEMPT/raw.log > ATTEMPT/summary.json`.
The parser refuses missing/duplicated/unknown cells, incorrect repetition counts,
and nonfinite/nonpositive measurements. It reports every paired ratio and the
predeclared primary-cell decision. Host stability and code-generation review
remain explicit review evidence, not claims made by the parser.

Before timing, run the separate ignored `moment_benchmark_observations` test with
`--ignored --nocapture --test-threads=1`, saving its output in the attempt.
`python3 scripts/bench_moments/check_observations.py ATTEMPT/observations.log`
checks every recorded certificate against exact rational variance computed from
the recorded input bits. It reports observed error and the returned bound for
the same populations timed above. Ordinary Welford/two-pass errors are reported
without claiming a certificate. Run observation and timing tests from the same
frozen executable; retain its hash. Oracle work is outside timing.
