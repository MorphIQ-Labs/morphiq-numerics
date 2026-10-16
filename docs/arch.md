# `morphiq-numerics-arch`: safe SIMD lanes

`crates/morphiq-numerics-arch` gives `morphiq-numerics` binary64 SIMD lanes
behind a safe API. It is the workspace's only crate with `unsafe` code: the
`core::arch` intrinsics are `unsafe` to call unless the caller proves the CPU
has the instructions, and this crate is where that proof is made, once per
backend. `morphiq-numerics` keeps `forbid(unsafe_code)` and depends on this
crate only behind its opt-in `simd` feature ([lanes.md](lanes.md)).

The crate is `no_std`, has no dependencies and allocates nothing. Its `std`
feature turns on runtime CPU detection.

## API

A **backend** is a zero-sized token type implementing the sealed trait `Simd`.

| Backend | Target | Lanes | Fused multiply-add | Available when |
|---|---|---|---|---|
| `Scalar` | every target | 1 | no | always |
| `Neon` | aarch64 | 2 | yes (`FMLA`) | the target enables `neon` (every aarch64 target with an FPU) |
| `Sse2` | x86-64 | 2 | no | the target enables `sse2` (every hosted x86-64 target) |
| `Avx2` | x86-64 | 4 | yes (`VFMADD`, the FMA extension) | AVX2 and FMA are detected |
| `Avx512` | x86-64 | 8 | yes (`VFMADD`) | AVX-512F is detected |

**Detection.** With the `std` feature, `Avx2::try_new` and `Avx512::try_new`
ask `std::arch::is_x86_feature_detected!`, which checks the CPU's CPUID bits
and that the operating system saves the wider registers (`XGETBV`). Without
it, they return a token only when the target enables the features at compile
time (`-C target-feature`, `-C target-cpu`). `Neon` and `Sse2` exist only on
targets that enable them, so they need no detection. `dispatch` picks the
widest available backend: AVX-512F, AVX2, SSE2 on x86-64; NEON on aarch64;
`Scalar` elsewhere.

**Operations.** Each takes the token by value and acts on every lane as the
scalar operation it names: `add`, `sub`, `mul`, `div` (IEEE 754 binary64,
round-to-nearest-even), `abs` and `neg` (the sign bit), the ordered
comparisons `lt` and `le` (false on NaN), the lane masks' `and_m`, `or_m`,
`not_m`, `mask_bits`, `mask_from_bits` and `select`, the reinterpretations `to_bits` and
`to_float`, the 64-bit word operations `and_u`, `or_u`, `sub_u` (wrapping),
`shr_u` (logical, zero for a count of 64 or more) and `eq_u`, `splat` and `splat_bits`, and `load`, `load_bits` and `store` on
`[f64; LANES]` and `[u64; LANES]` arrays. `mul_add(a, b, c)` returns `a·b + c`
rounded once on a backend with a hardware fused multiply-add (`Simd::FMA`),
and `None` on one without; it is never emulated.

**Running a kernel.** A generic kernel implements `WithSimd` and runs through
`Simd::vectorize` or `dispatch`. `vectorize` calls it inside a function
compiled with the backend's target features (`#[target_feature]`), so with the
kernel and the lane operations marked `#[inline(always)]`, each operation
inlines to one instruction or a short fixed sequence (SSE2's 64-bit
`eq_u` and `select`, which it lacks as single instructions).

## Safety argument

The crate has three kinds of `unsafe` operation. Each `unsafe` block holds
exactly one and states its justification in a `SAFETY:` comment; Clippy's
`undocumented_unsafe_blocks` and `multiple_unsafe_ops_per_block` deny any
other, and `unsafe_op_in_unsafe_fn` is denied. No public function is
`unsafe`.

1. **Calling a `#[target_feature]` function** from code compiled without
   those features: an instruction helper, or `vectorize`'s wrapper. The only
   precondition is that the CPU has the features. The proof is the token the
   calling method receives:
   - the token types have a private field, so outside the crate a token comes
     only from its constructor;
   - `Avx2::try_new` and `Avx512::try_new` return one only after detection
     (above), or when the target enables the features, which the target
     specification guarantees of every CPU that runs the binary;
   - `Neon::new` and `Sse2::new` exist only where the target enables the
     feature (`cfg(target_feature)`), which is the same guarantee;
   - `Simd` is sealed, so no other type can claim a backend's features.

   Each backend method calls one helper of the same name. The helpers
   (`neon.rs` `helpers`, `x86_64.rs` `helpers::{sse2, avx2, avx512}`) are
   compiled with the backend's features, so the intrinsics inside them are
   safe calls since Rust 1.87. A macro, `forward!`, writes the methods, so the
   argument is stated once per backend and cannot drift between methods.
2. **Unaligned loads and stores** (`vld1q_f64`, `_mm256_loadu_pd`, …): the
   pointer comes from an `[f64; LANES]` or `[u64; LANES]` array owned by the
   function, which is exactly the bytes the instruction reads or writes; the
   unaligned forms need only the element's alignment.
3. Nothing else: there are no raw-pointer slices, transmutes or `static mut`.

**Masks.** Each backend's mask type (`NeonMask`, `Sse2Mask`, `Avx2Mask`,
`Avx512Mask`) is a newtype with a private field, constructed only by the
comparisons and mask operations. So every NEON, SSE2 and AVX2 mask lane is all
ones or all zeros, which `select` (bitwise on SSE2 and NEON, the sign bit on
AVX2) relies on for its meaning. That is a correctness property, not a safety
one: any bit pattern is a valid vector. `mask_from_bits` ignores bits above
the lane count. It constructs canonical vector lanes by comparison on NEON,
SSE2 and AVX2; AVX-512F uses the low eight bits directly as its native mask.

**The floating-point environment.** Every lane operation rounds to nearest,
ties to even, with subnormals kept: the default MXCSR on x86-64 and FPCR on
aarch64, which Rust assumes for scalar `f64` too and which this crate never
changes. A lane operation is then the scalar operation, bit for bit.

## Checked by

`crates/morphiq-numerics-arch/src/tests.rs`, on every backend the CPU has:
- every operation on every lane against the scalar operation it names, on the
  special values (signed zeros, subnormals, infinities, NaNs), every pairing of
  them, and 4,000 random encodings; NaN payloads are compared only for the
  bit operations;
- `mul_add(a, b, −RN(a·b))` against the exact product in integer arithmetic,
  on 20,000 operand pairs, wherever the backend has FMA;
- `mul_add` is `None` on `Scalar` and `Sse2`.

The `test` CI job runs them on x86-64 (SSE2, AVX2) and aarch64 (NEON) hosts,
and the `simd (avx512, sde)` job on AVX-512F under Intel's Software
Development Emulator ([lanes.md](lanes.md) §6).
