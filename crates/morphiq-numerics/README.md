# MorphIQ Numerics

`morphiq-numerics` is a standalone, general-purpose Rust library for reproducible
binary64 numerics, available under MIT OR Apache-2.0.

Each API has an explicit numerical contract: correct rounding on established
domains, stated error bounds elsewhere, and a separate `fast` namespace for
bounded approximations.

The library provides elementary and normal-family functions, bivariate normal
CDFs, log-space and double-word arithmetic, seeded random streams, reductions,
finite intervals and checked tridiagonal solves. It requires Rust 1.89 or later.

It is `no_std`, allocates no heap memory, forbids `unsafe` and never calls a
platform math library. Its default configuration has no dependencies. The
optional first-party `morphiq-numerics-arch` dependency supplies SIMD intrinsics
behind a safe CPU-capability API.

```rust
use morphiq_numerics::{elementary, fast, normal};

assert_eq!(elementary::exp(0.0), 1.0);
assert_eq!(normal::norm_cdf(0.0), 0.5);

let inputs = [-1.0, 0.0, 1.0];
let mut outputs = [0.0; 3];
fast::elementary::exp_slice(&inputs, &mut outputs);
for (x, y) in inputs.into_iter().zip(outputs) {
    assert_eq!(y.to_bits(), fast::elementary::exp(x).to_bits());
}
```

Slice APIs also work without SIMD. The `simd` feature enables available
compile-time backends; adding `std` enables runtime CPU detection. Supported
backends include ARM NEON and x86-64 SSE2, AVX2+FMA and AVX-512F, with scalar
fallbacks. Features change speed, never an API's result bits. Fast and strong
APIs have separate contracts and may return different bits.

Consult each API's rustdoc for its domain, special values and accuracy. The
[repository documentation](https://github.com/MorphIQ-Labs/morphiq-numerics/tree/main/docs)
contains the derivations, numerical qualifications and floating-point environment
requirements. For version-matched evidence, select the corresponding release tag
and read its `docs/` directory. Full oracle, generator and formal checks run from
that repository checkout; their tooling and fixtures are not library dependencies.

Native performance evidence is specific to its recorded source, host, workload
and numerical contract. An API name or SIMD backend does not imply universal
competitor parity.

Dual licensed under MIT OR Apache-2.0. Both license texts and the applicable
third-party notices are included in this package.
