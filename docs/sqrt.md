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
