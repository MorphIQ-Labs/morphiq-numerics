# Scalar FMA on Apple M1 Pro

Before/after measurements of `eft::two_prod_d`: baseline `74f7dee`, candidate
`48ab0c9`. Both builds enable `simd,std`. The baseline selects Dekker for
scalar kernels on aarch64; the candidate uses hardware FMA on the same proved
domain. Public `two_prod` and `DoubleWord` operations remain unchanged.

`environment.json` records the toolchain and sampling. The normal harness is
`benchmark-normal.rs`, compiled with `rustc --edition=2024 -O`, linked to each
`cargo build --release --locked -p morphiq-numerics --features simd,std`
library using `--extern morphiq_numerics=target/release/libmorphiq_numerics.rlib`
and `-L dependency=target/release/deps`. Three alternating process pairs each
record three samples per function; inputs are 1,024 equally spaced values
in [-5,5]. Columns are function, scalar ns/call, batched ns/value.

The erfcx harness is `crates/reference/src/bin/bench-erfcx.rs`, built with
`cargo build --release --locked -p morphiq-numerics-reference --features simd,std --bin bench-erfcx`.
Its CSV includes 31 samples per workload and mode, with a warm-up and rotated
mode order. Each timed mode first checks scalar/batch result bits.

These measurements compare this implementation before and after FMA. They
do not establish parity with the fastest alternative. Apple Silicon thread
placement is not pinned. Small timing differences require repeated process
pairs; raw samples are retained rather than treated as pass/fail tests.

The native ARM correctness gate compares all 48,000 public and 760,127
internal corpus lines against the no-std Dekker build, with no differences.
The full workspace all-feature tests, Clippy, rustdoc and embedded build
pass locally. Release assembly contains scalar fused instructions and no
call to a software FMA function. The proof models retain the identical
Dekker words; docs/lanes.md section 2 supplies the domain argument.

## Same-process paired comparison

`build_paired.py` builds both revisions with distinct internal crate names
(the numerical sources and features are unchanged), then links them into
`paired.rs`. This permits alternate timing in the same process on the same
inputs. Run from the repository root with:

```sh
python3 crates/reference/measurements/scalar-fma-m1pro/build_paired.py /tmp/morphiq-fma-paired
```

Each process records 33 paired rounds after warm-up; `paired-0.csv` through
`paired-2.csv` contain 99 samples per variant. Variant 0 is Dekker, 1 is FMA.
Inputs are fixed-seed uniform samples; each pair first checks all result bits.
This workload differs from the equally spaced normal-only harness above.

Median scalar ns/call in the paired run:

| Function/range | Dekker | FMA |
| --- | ---: | ---: |
| PDF ordinary | 9.097 | 8.124 |
| CDF ordinary | 39.836 | 37.348 |
| CCDF ordinary | 38.144 | 35.747 |
| Centered CDF ordinary | 37.939 | 35.551 |
| log-CDF ordinary | 101.997 | 99.963 |
| erfcx table | 12.175 | 11.956 |
| erfcx positive common | 11.265 | 11.214 |
| erfcx asymptotic | 15.100 | 11.657 |
| erfcx reciprocal | 8.567 | 7.876 |
| erfcx negative | 15.885 | 15.086 |

The original separate-process table measurement moved by about 1.5% in the
opposite direction. This paired run does not reproduce that slowdown. The
table kernel has no FMA call; large speedups are confined to paths that use
the changed helper. Native x86 performance is not established by ARM results.
