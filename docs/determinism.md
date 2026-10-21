# Determinism digest

Every function returns the same bits on every target. The digest makes that
claim checkable: one SHA-256 over the output bits of every public function on a
fixed corpus, compared with the value committed in
`crates/reference/determinism.sha256`.

## The corpus

`crates/digest/src/lib.rs` builds the corpus from integers only (a
seeded xorshift and literal bit patterns), so the inputs are identical
everywhere. Each section is labelled in the hash, so an output can't move between
functions unnoticed.

| Section | Inputs | Outputs hashed |
|---|---|---|
| `ulp` | NaN, ±0, ±∞, ±max finite, every binade's least and greatest encoding, 20,000 random encodings | `ulp`, `ordered_bits`, and `ulps_between` of neighbours |
| `eft` | 20,000 pairs with exponents in `[−500, 500]` | `two_sum`, `fast_two_sum` (larger operand first), `two_prod` |
| `double_word` | 20,000 triples of double-word and binary64 operands | every double-word operation, and `DoubleWord::product` |
| `double_word_checked` | 20,000 triples with exponents in `[−1020, 1020)`, past every operation's domain | every checked operation: the result's words, or a code for the error |
| `reduce` | slices of every length from 0 to 32, exponents in `[−100, 100]`, mixed signs; one slice holding a NaN | `sum`, `sum2`, `dot`, `dot2`, `sum_squares`, `sum_squares2`, `max_abs` |
| `exp` | NaN, ±∞, ±0, the extreme encodings, each threshold of [exp.md](exp.md) §1 with its neighbour; 20,000 arguments in `[−746, 710)`; 64 of each binade from `2^−60` to `2^−1`, both signs | `exp` |
| `ln` | NaN, ±∞, ±0, −1, the extreme encodings, 1 and its neighbours; 20,000 positive encodings, subnormals included; 4,000 arguments in `[0.5, 2)` | `ln` |
| `ln_1p` | NaN, ±∞, ±0, −1 and its neighbour, −2, each branch edge of [ln.md](ln.md) §7, the largest finite; 20,000 arguments with magnitudes from `2^−60` to `2^1023`, either sign | `ln_1p` |
| `exp2` | NaN, ±∞, ±0, each threshold of [exp2.md](exp2.md) §1 with its neighbour; every integer from −1076 to 1025; 20,000 arguments in `[−1077, 1026)`; 64 of each binade from `2^−60` to `2^−1`, both signs | `exp2` |
| `expm1` | NaN, ±∞, ±0, each threshold of [expm1.md](expm1.md) §1 with its neighbour, both sides of `±2^−5`; 20,000 arguments in `[−38, 710)`; 64 of each binade from `2^−60` to `2^−1`, both signs | `expm1` |
| `log2`, `log10` | NaN, ±∞, ±0, −1, the extreme encodings, 1 and its neighbours; `10^n` for `0 ≤ n ≤ 22`; every power of two from `2^−1074` to `2^1023`; 20,000 positive encodings; 4,000 arguments in `[0.5, 2)` | `log2`, then `log10` |
| `sin_cos` | NaN, ±∞, ±0, each small-argument threshold of [sin_cos.md](sin_cos.md) §1 with its neighbour, `RN(π/2)`, `RN(π)`, the closest approach to a multiple of `π/2`, the largest finite; 10,000 encodings across every binade, both signs; 10,000 arguments in `[−2π, 2π)` | `sin`, `cos`, and both halves of `sincos` |
| `tan` | NaN, ±∞, ±0, [sin_cos.md](sin_cos.md) §8's threshold with its neighbour, `2^−26`, `RN(π/2)` and its successor, `RN(π)`, the closest approach to a multiple of `π/2`, the largest finite; 10,000 encodings across every binade, both signs; 10,000 arguments in `[−π, π)` | `tan` |
| `asin`, `asin_slice` | NaN, ±∞, ±0, the least subnormal, [asin.md](asin.md)'s `ASIN_IS_X` and `SPLIT` with neighbours, ±1 and neighbours, every `k/128` shifter edge with neighbours; 10,000 arguments in `[−1, 1]`, 5,000 in `[0.7, 1]`, 64 of each binade from `2^−60` to `2^0`, both signs; 1,000 slices of each length from 1 to 17 mixing the edges and `[−1.1, 1.1]` | `asin`, and every element of each `asin_slice` result |
| `asinh`, `asinh_slice` | NaN, ±∞, ±0, the least subnormal, [asinh.md](asinh.md)'s threshold and region edges with neighbours, the largest finite; 10,000 arguments over every binade from `2^−30` to `2^1023`, both signs, 5,000 in `[−8, 8]`; 1,000 slices of each length from 1 to 17 mixing the edges and `[−8, 8]` | `asinh`, and every element of each `asinh_slice` result |
| `sqrt` | 10,000 arbitrary encodings, both signs, subnormals, infinities and NaNs; 10,000 positive encodings | `sqrt` |
| `normal_pair` | `w1` in `{0, 2^64 − 1, 2^63}` against `w2` in `{0, 2^64 − 1}` and every octant boundary `o·2^61`; 10,000 pairs of words | both deviates of `normal_pair` |
| `random` | four seeds | 4,096 words of each stream, both uniforms of each SplitMix64 word, and a word after `jump` and after `long_jump` |
| `log_sum_exp` | the special values and zero-mass cases of [log_space.md](log_space.md) §1, overflow and `±max` pairs; 1,000 slices of each length from 1 to 8, gaps below their maximum from `2^−40` to `2^11`; 4,000 pairs with exponents in `[−1022, 1023]`; 20 slices of each length from 9 to 100, with `−∞` and underflowing terms among them | `log_sum_exp` |
| `log_sum_exp_pairs` | every pairing of ten special values; 1,000 batches each of 1, 2, 3, 8 and 17 pairs, gaps from `2^−40` to `2^11`, the maximum first or second | every element of each result |
| `log_sum_exp_and_normalize` | the same kinds of input as `log_sum_exp_pairs`, drawn afresh | each log-sum, and each normalized pair's entries; an absent pair and a NaN entry (payload unspecified) as codes |
| `log_diff_exp` | the special values of [log_space.md](log_space.md) §1, the region boundary `T`, underflow and overflow; 10,000 pairs with gaps from `2^−60` to `2^12`; 4,000 ordered pairs with exponents in `[−1022, 1023]` | `log_diff_exp` |
| `log_norm_pdf` | NaN, ±∞, ±0, the least subnormal, each regime boundary of [log_norm_pdf.md](log_norm_pdf.md) §1 (`2^−27`, `2^500`, `2^512`, `2^513`), the overflow threshold and its successor, all with both signs, and a regime-L tie; 20,000 arguments with exponents in `[−40, 512]`; 10,000 in `[−8, 8)` | `log_norm_pdf` |
| `erfcx`, `erfcx_slice` | special values, neighbors of the overflow/one/subnormal boundaries, all region boundaries, random encodings and inputs in `[-27, 520)`; 20,000 scalar inputs and 1,000 slices of each length 1–17 | each scalar and batched output |
| `norm_pdf`, `norm_cdf`, `norm_ccdf`, `norm_cdf_centered`, `log_norm_cdf` and matching slices | special values and signed threshold neighbors; 512 scalar inputs per function mixing random encodings and `[-40, 40)`; eight slices of every length 0–17 | every scalar and batched output |
| `exp_slice`, `ln_slice`, `ln_1p_slice` | 1,000 slices of each length from 1 to 17, each element in turn a special value or branch edge of the function, a random encoding, or an argument in `[−746, 710)`, `[0, 4)` or `[−1, 9)` respectively | every element of each output slice |
| `exp2_slice`, `expm1_slice` | 1,000 slices of each length from 1 to 17, mixing special values, screen edges, random encodings, and arguments in `[−1076, 1025)` or `[−38, 710)`; an additional `expm1_slice_small` section samples `[−1/32, 1/32)` | every output element, scalar and SIMD builds alike |

| `finite_interval` | every pair of 16 edge values, then random encodings, 4,096 iterations | constructors, membership, negation, absolute value, maximum, every checked arithmetic/elementary operation; endpoint bits or typed error codes |

## Where it is checked

The test `every_output_matches_the_committed_digest` runs:
- in the `test` job on x86-64 Linux, aarch64 Linux, aarch64 macOS and x86-64
  Windows, with every feature, so the batched functions run in SIMD lanes
  (AVX2 or wider, NEON; [lanes.md](lanes.md));
- in the `simd (avx512, sde)` job, in AVX-512F lanes under Intel's emulator;
- in the `digest` job:
  - on x86-64 Linux with musl (`x86_64-unknown-linux-musl`), without and with
    the `simd` feature;
  - on WebAssembly (`wasm32-wasip1`, under the wasmtime pinned in
    `.cargo/wasmtime-version` and checked against `.cargo/wasmtime-sha256`);
  - on bare metal (`thumbv7em-none-eabihf`), from reset on QEMU's `mps2-an386`
    Cortex-M4F. That FPU is single-precision only, so every binary64 operation
    there runs in the compiler's software floating point: a different arithmetic
    path that must still give the same bits.

The corpus lives in the `no_std`, allocation-free `crates/digest`, so every
target computes the same one. `crates/digest-embedded` runs it on bare metal,
printing over semihosting and exiting with the comparison's status.

`scripts/check_digest_target.sh TARGET` runs the same check locally.

## Changing it

A change that alters any output fails the test, which prints the new digest.
- **If the change is wrong,** fix the change.
- **If it is deliberate** (a function corrected, or the corpus extended), update
  `crates/reference/determinism.sha256` in the same pull request and give the
  reason there. The new value must then pass on every target, which is the
  determinism claim itself.
