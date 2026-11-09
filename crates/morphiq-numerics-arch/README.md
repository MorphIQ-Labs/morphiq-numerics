# morphiq-numerics-arch

Safe binary64 SIMD lanes for
[morphiq-numerics](https://github.com/MorphIQ-Labs/morphiq-numerics), supporting
ARM NEON and x86-64 SSE2, AVX2+FMA and AVX-512F, plus scalar lanes.

Most callers use the main library with its `simd` feature. This crate confines
the workspace's unsafe intrinsics behind a safe API: backend operations require
a detection token establishing that the processor supports their instructions.
The operations preserve the numerical sequences required by the library.

The crate has no dependencies, supports `no_std` and requires Rust 1.89 or later.
Its optional `std` feature enables runtime CPU detection. Without `std`, backend
availability follows compile-time target features.

See rustdoc and the
[architecture contract](https://github.com/MorphIQ-Labs/morphiq-numerics/blob/main/docs/arch.md)
for capability detection and the required floating-point environment. Select
the corresponding repository release tag for version-matched documentation.

Dual licensed under MIT OR Apache-2.0; both license texts are included.
