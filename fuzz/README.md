# MPFR elementary fuzzing

This independent, unpublished workspace checks the strong elementary API against
MPFR through `rug`. Neither MPFR nor the fuzzer is a dependency of the published
crates. The root dependency license policy stays permissive-only; the separate
oracle graph has exact package/version exceptions in
[`check_fuzz_licenses.sh`](../scripts/check_fuzz_licenses.sh).

## Contracts

`elementary` covers all 14 scalar elementary functions, `sincos` equivalence,
and all eight slice wrappers, with scalar and `simd,std` builds. The oracle
compares exact binary64 bits for correctly rounded results, including signed
zero, subnormals and infinities. NaNs are checked by classification; slice and
`sincos` equivalence compare their exact bits as well.

| Functions | Oracle acceptance |
| --- | --- |
| `exp`, `exp2`, `ln`, `log2`, `sqrt`, `asin`, `asinh` | Correct rounding over their entire domains, including specified exceptional inputs |
| `expm1` | Correct rounding for `abs(x) < 2^-54`; otherwise `(1/2 + 2^-65)` ulp |
| `ln_1p` | Correct rounding for `abs(x) < 2^-54`; otherwise `(1/2 + 2^-70)` ulp |
| `log10` | `(1/2 + 2^-69)` ulp |
| `sin` | Correct rounding for `abs(x) <= 0x1.7137449123ef6p-26` and `2^-24 <= abs(x) <= 2 + 4675/8192`; otherwise `(1/2 + 2^-144)` ulp |
| `cos` | Correct rounding for `abs(x) <= 12867/8192`; otherwise `(1/2 + 2^-144)` ulp |
| `tan` | Correct rounding for `abs(x) <= 0x1.d12ed0af1a27ep-27` and `2^-25 <= abs(x) <= atan(2)`; otherwise `(1/2 + 2^-142)` ulp |
| `atan2` | Correct rounding for special values and tiny ratios below `2^-900`; otherwise `(1/2 + 2^-137)` ulp |

These are the contracts in [exp](../docs/exp.md), [exp2](../docs/exp2.md),
[expm1](../docs/expm1.md), [ln](../docs/ln.md), [log2/log10](../docs/log2.md),
[trig](../docs/sin_cos.md), [sqrt](../docs/sqrt.md), [asin](../docs/asin.md),
[asinh](../docs/asinh.md) and [atan2](../docs/atan2.md). The public oracle cannot
observe internal rounding-test decisions: outside the stated CR domains it
checks the published bound, including results returned by those tests. Existing
internal proof and decision checks remain responsible for that stronger path
invariant. This target does not cover the separate `fast`, normal, random,
double-word or linear-algebra APIs.

MPFR evaluates each exact input with rounding down and up, starting at 256 bits
and doubling through 8192. Both endpoints must round to the same binary64 value
before it is used as the correctly rounded reference. This avoids double
rounding at subnormal midpoints. If the tested bounded result differs, directed
MPFR arithmetic must establish its error against `(1/2 + 2^-k) * ulp(exact)`;
the small term is never rounded away in binary64. An interval spanning a binade
boundary is refined. ULP is clamped to `2^-1074` for subnormals. Unresolved
oracle comparisons fail explicitly at the precision limit.

The oracle tests plant wrong results, signed-zero errors and bound violations,
and check that a valid non-CR value inside the bound is accepted. The retained
`atan2-subnormal-midpoint` input exercises `atan(3*2^-1074 / 2)`: its result is
just below the midpoint, requiring more than 2000 bits to settle. This is an
oracle regression witness, not a known library defect.

## Run and replay

On Apple Silicon macOS or native x86-64 Linux, with the repository toolchain,
Python 3, a C/C++ compiler and make installed:

```sh
./scripts/install_fuzz.sh
./scripts/check_fuzz.sh 60
```

The installer uses `.cargo/fuzz-version` and `.cargo/fuzz-nightly-version`.
`fuzz/Cargo.lock` pins `rug`, its bundled GMP/MPFR provider, and libFuzzer. Cargo
checks and replay use `--locked`. cargo-fuzz 0.13.2 has no `--locked` option, so
its build runs offline after the locked checks, and the gate rejects any lockfile
change. AddressSanitizer and coverage instrumentation are enabled for fuzz runs.

Each run replays all inputs from the versioned elementary reference fixtures,
then mutates them for the requested number of seconds **per feature mode**.
Expected fixture outputs are not imported. The seed encoder adds both signs of
every binary64 binade boundary and its adjacent encodings, NaN payloads,
infinities, subnormal edges, and slice lengths 0 through 16. The fixture
sources retain the provenance of worst-case and reduction-boundary inputs.

The corpus format is one selector byte modulo 14, followed by up to sixteen
pairs of little-endian `u64` input encodings. IDs follow the table's source order
in `Operation::ALL`: exp, exp2, expm1, ln, ln_1p, log2, log10, sin, cos, tan,
sqrt, asin, asinh, atan2. Unary functions ignore the second word; atan2 calls
`atan2(first, second)`. Incomplete trailing pairs are ignored.

Generated seeds, evolving corpora, failure artifacts and logs live under
`target/fuzz/`. CI runs 60 seconds per mode in the existing required Linux and
macOS test jobs. The weekly/manual workflow runs 1800 seconds per mode on both
hosts. Artifacts are retained for 14 days, including on failure. A passing
campaign is sampled evidence, not an exhaustive proof or a performance result.

Replay a failure without nightly instrumentation:

```sh
cargo run --release --locked --manifest-path fuzz/Cargo.toml --features simd \
  --bin replay -- target/fuzz/artifacts/crash-HASH
```

Minimize it with the pinned cargo-fuzz tool, diagnose whether it is an oracle
or library defect, fix the owning component, and commit the minimized binary
under `fuzz/regressions/` with a named regression test and its explanation. The
gate replays every retained input in both feature modes. Never turn a discovered
violation into a weaker tolerance or a discarded input.

Oracle API documentation: [rug Float](https://docs.rs/rug/1.30.0/rug/struct.Float.html).
Fuzzer usage: [Rust Fuzz Book](https://rust-fuzz.github.io/book/cargo-fuzz.html).
No external numerical implementation source is used by this harness.
