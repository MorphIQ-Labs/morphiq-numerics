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
