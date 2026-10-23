# `sqrt`

`morphiq_numerics::elementary::sqrt` (`crates/morphiq-numerics/src/sqrt.rs`) is
IEEE 754's `squareRoot` (§5.4.1) in binary64, rounded to nearest with ties to
even. The crate is `no_std` and never calls a platform library, so it computes
the root in integer arithmetic.

## Specification

| Input | Result |
|---|---|
| NaN, `−∞`, any `x < 0` | NaN |
| `±0` | `±0` |
| `+∞` | `+∞` |
| finite `x > 0` | `RN(√x)` |

## Derivation

1. **Normalize.** Finite `x > 0` is `m·2^e` with `2^52 ≤ m < 2^53`; a subnormal
   is shifted into that range. If `e` is odd, `m` doubles and `e` drops by one,
   so `e` is even and `2^52 ≤ m < 2^54`.
2. **Integer root.** `R = m·2^54` lies in `[2^106, 2^108)`. The binary
   digit-by-digit method gives `s = ⌊√R⌋` and the remainder `R − s²` exactly,
   in `u128`. `s` lies in `[2^53, 2^54)`, so `√x = (√R)·2^((e − 54)/2)` has
   `s`'s 54 bits as its leading bits.
3. **Round.** The top 53 bits of `s` are kept. The last bit of `s` is the
   rounding bit, and a nonzero remainder is the sticky bit. A tie would need
   `s` odd with `s² = R`, but `R` is even, so there are no ties; the rule is
   implemented whole anyway. A carry to `2^53` moves to the next binade.
4. **Range.** `√(2^−1074) = 2^−537` and `√(2^1024) = 2^512`, so the result is
   always normal and finite.

## Hardware

The integer derivation above is the reference and the whole implementation of the
public `sqrt`, which is a `const fn`. Inside the crate, kernels that take a square
root of a finite nonnegative number (`asin`'s complement, `asinh`'s logarithmic
form, and their lanes) call `exact::sqrt`, which is the hardware instruction when
`std` is on and the target has one (x86-64 `sqrtsd`, aarch64 `fsqrt`, WebAssembly
`f64.sqrt`), and this module otherwise.

This costs the determinism claim nothing, and the rule is general: IEEE 754
requires `squareRoot` (§5.4.1), `fusedMultiplyAdd` and the other operations of §5
to be correctly rounded, so every conforming implementation returns the same bits.
Only the transcendental functions differ between platforms, and those the crate
never takes from one. An operation the standard fixes may therefore run on
hardware where the build has it, with the integer or error-free-transform
implementation as the reference and the fallback; one the standard does not fix may
not. A NaN's sign and payload are not fixed by the standard, so the hardware path
is for arguments that are never NaN.

### Survey

Every operation IEEE 754 §5 fixes, against what the crate does in software:

| Operation | In the crate | Disposition |
|---|---|---|
| `+ − × ÷` | the platform's | nothing to change |
| `squareRoot` | the integer root; now `exact::sqrt` in `asin`, `asinh`, their lanes, `normal_pair` and `FiniteInterval::checked_sqrt` | hardware where the build has it; the public `sqrt` stays the `const fn` integer root |
| `fusedMultiplyAdd` | Dekker's product in `eft::two_prod`; `eft::two_prod_d` (hardware on aarch64 and FMA builds) in `asin`, `asinh`, `atan2`, `erfcx`, the normal functions | each further site needs its own proof that its arguments are in `two_prod`'s domain (§2 of [lanes.md](lanes.md)); about 15 modules still call the public `two_prod` or `DoubleWord::mul`/`mul_f64`/`product`, listed by `grep two_prod`, and are the next candidates |
| `roundToIntegralTiesToEven` | the `1.5·2^52` shifter in `exp`, `exp2`, `expm1`, `trig`, `erfcx`, the normal functions, `asin` and `atan2` | kept: x86-64 has no baseline instruction (`roundsd` is SSE4.1), the lane backends have no such operation, and the shifter is two additions on every target with the same bits |
| `scaleB`, `copySign`, `abs`, `negate` | powers of two built from their bits; bit operations | no baseline hardware instruction, or already one operation |
| `nextUp`, `nextDown`, `logB` | bit operations in `ulp` | exact and trivial; `core` has `next_up`/`next_down` |
| conversions to and from integers | `as` | native |
| `remainder`, `minNum`, `maxNum` | not used | |

No other operation the standard fixes is implemented in software. Everything else in
the crate that is not a binary64 operation (`Q128`, `Q256`, the Coq-checked integer
limbs) is not one IEEE 754 defines.

Checked by `exact::tests`, which compares the hardware root with the integer one
on 800,000 encodings (every binade, the neighbourhood of exact squares, subnormals,
infinity), and by the determinism digest, whose value is the same with and without
the hardware path on aarch64 and x86-64
([determinism.md](determinism.md)).

## Proof

The derivation is machine-checked in Coq (`formal/binary64`, run by
`scripts/check_formal.sh`):

- **`Isqrt.v`**: `isqrt_correct`. The transcribed digit-by-digit loop, with its
  starting-bit search, returns `⌊√r⌋` and `r − ⌊√r⌋²` for every
  `0 < r < 2^128`. The loop invariant: before the digit of weight `4^k`, the
  root register holds `y·4^(k+1)` and the remainder `r − y²·4^(k+1)`, for
  `y = ⌊√(r / 4^(k+1))⌋`.
- **`SqrtRound.v`**: `round_sqrt`. For `2^52 ≤ m < 2^54` and even `e`, rounding
  `√(m·2^e)` to nearest-even gives step 3's significand at exponent
  `(e − 54)/2 + 1`.
- **`SqrtAlgorithm.v`**: `sqrt_rs_ieee`. The transcription of `sqrt.rs`
  (`sqrt_rs`: normalize, root, round, assemble) equals Flocq's correctly
  rounded `b64_sqrt` at `mode_NE` for every binary64 input. The special
  values are taken from `b64_sqrt` in the transcription, and the cross-check
  compares the Rust code with them.
- **`IEEE64Sqrt.v`**: `sqrt_ieee`. `b64_sqrt` is the binary64 rounding of `√x`,
  finite exactly for finite `x ≥ 0`.

All four are in the axiom audit, which requires exactly the classical axioms of
`formal/axioms.expected`.

## Checked by

- **Cross-check:** `scripts/check_formal.sh` extracts the transcription
  `sqrt_rs` to OCaml and compares it with the Rust `sqrt` bit for bit on the
  cross-check corpus: 4,000 arbitrary encodings (both signs, subnormals,
  infinities, NaNs) and 4,000 positive arguments. That ties the proved
  transcription to the code that ships.
- **Exact rounding tests** (`src/sqrt/tests.rs`): `(r − ulp/2)² < x < (r + ulp/2)²`
  in exact arithmetic on 100,000 random encodings and on 120,000 arguments next
  to `y²` and `y·next_up(y)`, where the root lies just beside a binary64
  number or a midpoint; exact squares return their root; special values.
- **Binding:** `formal/binding.sha256` covers `sqrt.rs` and the proofs, so a
  change to either fails until the proofs are rerun.
- **Determinism digest:** the `sqrt` section on every target.
