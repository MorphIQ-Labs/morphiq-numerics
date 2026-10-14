# Standard-normal scalar and NEON measurements

`run-1.csv` through `run-3.csv` retain three same-host repetitions on Apple
M1 Pro at `755326c`, before the consumer-inlining adjustment. The
[current consumer comparison](consumer-inlining/README.md) records that
adjustment separately. `summary.csv` gives medians and min/max spread; its speedup is the
ratio of median scalar throughput time to median batch time. All times are
nanoseconds per argument. `environment.json` records the host, toolchain,
base revision and hashes of the measured implementation/harness sources.

Reproduce a full 1,024-element run from the repository root:

```sh
cargo test --release --locked -p morphiq-numerics --all-features --lib normal_local_performance -- --ignored --nocapture --test-threads=1
```

Compile before measuring. Warm up once with
`MORPHIQ_NORMAL_BENCH_WORKLOAD=ordinary`, then repeat the full command three
times. Each recorded repetition also includes both `ordinary` and `mixed`
with `MORPHIQ_NORMAL_BENCH_LENGTH` set to each of 1, 2, 3, 8 and 17. The
harness defines all input bits; shorter arrays sample the 1,024-element
workload evenly, preserving both endpoints when length exceeds one.

Each path is measured for at least 150 ms, sequentially: scalar loop, batch,
scalar dependency chain, identity dependency chain. No other local build or
proof job ran concurrently; desktop activity and OS frequency management
were not controlled. Three repetitions describe observed variation, not a
statistical confidence interval. Comparisons are within the same executable
and host; these are not before/after measurements or comparisons with other
libraries.

`scalar_ns` and `batch_ns` process the same uniform corpus. `accurate_count`
is the number requiring Q256 in that corpus, excluding direct special-value
screens. Counting runs outside timing. The scalar chain chooses its next
input index from the preceding output's bits. Its input frequencies therefore
differ from the throughput corpus, and it includes index/lookup overhead.
`chain_overhead_ns` uses the identity function with the same recurrence; do
not subtract it as if it were a constant cost of every function's chain.
The result-dependent index may simplify differently for different functions.

The library kernels allocate nothing: the published library does not import
`alloc`. Input/output vectors are allocated by the benchmark before timing;
no allocation is included in a measured kernel invocation.

## Observations

For 1,024 ordinary inputs spanning [-5,5], median throughput is:

| Function | Scalar ns/value | NEON ns/value | Speedup | Accurate count |
|---|---:|---:|---:|---:|
| pdf | 20.09 | 12.605 | 1.594× | 2/1024 |
| cdf | 36.93 | 26.645 | 1.386× | 0/1024 |
| ccdf | 36.876 | 23.035 | 1.601× | 0/1024 |
| centered | 40.984 | 25.942 | 1.58× | 2/1024 |
| log_cdf | 124.602 | 89.923 | 1.386× | 3/1024 |

Mixed 1,024-element speedups, in the same function order: 1.606×, 1.101×, 0.924×, 1.12×, 1.079×.

Short batches retain dispatch and scalar-remainder costs. A one-element
slice has no vectorizable pair. Two-lane chunks that straddle central/outer
regions or opposite log-tail branches use scalar evaluation to avoid running
both vector approximations. The mixed corpus repeatedly triggers these cases;
its gains are smaller and some cases are slower. This is an explicit cost of
the allocation-free, order-preserving dispatch. The raw data retains those
slowdowns; the implementation does not promise a gain for every mixture or
slice length. Underflow workloads are dominated by the shared Q256 fallback,
so their SIMD speedup is near one.

Native x86 hardware was unavailable. SSE2, AVX2+FMA and AVX-512F measurements
for all five functions are outstanding in
[#124](https://github.com/MorphIQ-Labs/morphiq-numerics/issues/124).
Rosetta and Intel SDE validate correctness only. No native x86 performance
claim follows from these ARM results.
