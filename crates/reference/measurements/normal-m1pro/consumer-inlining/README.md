# Standard-normal calls from a separate consumer crate

The baseline is `755326c`. The candidate adds `#[inline]` to the private
`special`, `fast` and `evaluate` helpers, allowing the public inline wrappers
to specialize their fixed operation across the crate boundary. No arithmetic,
threshold, guard, fallback or branch condition changes. `environment.json`
binds the candidate source and this exact standalone benchmark by hash.

`benchmark.rs` links the library as an external crate and calls all five
public scalar and slice APIs. It uses 1,024 identical ordinary inputs,
`10*(i/1023)-5`, with the division performed first. Before timing each
function it checks scalar/SIMD output bits on those inputs. Input/output
vectors are allocated before timing; the library kernels allocate nothing.

Build the library in baseline and candidate checkouts separately:

```sh
cargo build --release --locked -p morphiq-numerics --all-features
```

For each checkout, compile this benchmark against that checkout's rlib:

```sh
rustc -O -C codegen-units=1 --edition=2024 /path/to/benchmark.rs \
  --extern morphiq_numerics=/path/to/checkout/target/release/libmorphiq_numerics.rlib \
  -L dependency=/path/to/checkout/target/release/deps \
  -o /path/to/normal-consumer-bench
```

Use separate executable names for the two variants. Run each once to warm up,
then run seven process pairs, alternating baseline/candidate order by pair.
Each process reports three samples per function; each scalar and batch sample
runs for at least 150 ms. `rounds.csv` retains all 21 samples per function and
variant; `summary.csv` records medians and min/max spread in ns/argument.
Timing excludes process startup and the pre-timing bit comparisons.

Unrelated CPU-intensive jobs and VM activity were present. No task-owned
compiler or proof process overlapped these retained measurements. Frequency,
power settings and affinity were not controlled. The spread is substantial;
these are observations on this host under load, not confidence intervals or
universal speed claims. The same benchmark on one native x86 host is in
[`lanes-x86-i9-10920x`](../../lanes-x86-i9-10920x/README.md#compositions).

Median scalar ns/argument (all samples retained):

| Function | Baseline | Inline | Baseline / inline |
|---|---:|---:|---:|
| pdf | 29.031 | 23.785 | 1.221× |
| cdf | 49.694 | 42.088 | 1.181× |
| ccdf | 46.741 | 44.928 | 1.040× |
| centered | 52.803 | 44.888 | 1.176× |
| log_cdf | 126.608 | 127.253 | 0.995× |

These measurements support exposing the fixed operation to consumer code
generation. The log-CDF median is essentially unchanged; the data does not
establish a gain for every function. Batch measurements are retained too,
with the same host-load limitations.


The candidate passes the independent normal oracle/SIMD-word tests and
preserves the committed determinism digest. The consumer LLVM IR reduces shared `evaluate` call sites from ten to two
(`codegen.json`): the validation and timing loops for PDF, CDF, CCDF and
centered CDF inline the dispatch; log-CDF retains its helper calls. The helper
is available inside the consumer module after the change. This establishes
cross-crate optimization visibility, not an instruction-count or speed guarantee.
