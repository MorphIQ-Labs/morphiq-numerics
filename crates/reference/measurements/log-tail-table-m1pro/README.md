# Log-tail table diagnostic on Apple M1 Pro

The measurements are from the table stage at `c353042`, before integration
with the finite-tail branch. These samples preceded the
commit's documentation, proof packaging and fixture expansion; its numerical
operations are identical. `environment.txt` records the host and versions.
This is a single diagnostic pair on a shared host, not evidence that the
complete performance bar is met. Native x86 and repeated quiet-host
comparisons remain necessary. No CI or emulated timing is used.

For 1,024 inputs spanning [-38,-37], the table implementation measures
7.585 ns scalar, 6.002 ns batched, and 35.631 ns in the dependency chain,
with zero Q256 fallbacks. SciPy 1.16.3 `log_ndtr` measures 8.053, 8.916 and
46.368 ns respectively. The chain includes input-index arithmetic and array
lookup; it is not a pure instruction-latency number. `morphiq.log` also
contains unchanged sibling functions whose far tails that measured revision does not
optimize. The current stack includes the finite-tail change; final combined
performance measurements are still required.

The Rust measurement writes a slice of outputs and permits inlining. SciPy's
scalar measurement calls its exported Cython capsule through a C function
pointer and stores a volatile result; its batch measurement uses the ufunc
with a preallocated output array. Thus the interfaces and loop overhead are
recorded differences, not assumed identical. SciPy was used only as a black
box: no implementation source was consulted or copied.

To reproduce on macOS from the repository root (use `-shared -fPIC` in place
of `-dynamiclib` and a `.so` suffix on Linux):

```sh
MORPHIQ_NORMAL_BENCH_WORKLOAD=negative_far_tail cargo test --release --locked -p morphiq-numerics --features simd,std normal_local_performance -- --ignored --nocapture
MORPHIQ_NORMAL_BENCH_WORKLOAD=negative_first_table cargo test --release --locked -p morphiq-numerics --features simd,std normal_local_performance -- --ignored --nocapture
python3 -m venv target/log-tail-comparison
 target/log-tail-comparison/bin/pip install scipy==1.16.3 numpy==2.5.4
cc -O3 -dynamiclib crates/reference/measurements/log-tail-table-m1pro/scipy_measure.c -o target/scipy-measure.dylib
 target/log-tail-comparison/bin/python crates/reference/measurements/log-tail-table-m1pro/scipy_compare.py "$PWD/target/scipy-measure.dylib"
```

Both harnesses use the same 1,024 input values and the same dependency-chain
index rule. The second workload spans every first-stage table cell, including
the boundary at 64, which uses the normalized fallback. Absolute numbers from
different hosts, builds or input pools are not compared.
