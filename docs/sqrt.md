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

## Checked by

- **Proof of the reference definition:** `formal/binary64/IEEE64Sqrt.v` proves
  that Flocq's `b64_sqrt` at `mode_NE` is the binary64 rounding of `√x` for
  every `x`, finite exactly for finite `x ≥ 0` (`sqrt_ieee`, in the axiom
  audit).
- **Cross-check:** `scripts/check_formal.sh` extracts that definition to OCaml
  and compares it with the Rust `sqrt` bit for bit on the cross-check corpus:
  4,000 arbitrary encodings (both signs, subnormals, infinities, NaNs) and
  4,000 positive arguments.
- **Exact rounding tests** (`src/sqrt/tests.rs`): `(r − ulp/2)² < x < (r + ulp/2)²`
  in exact arithmetic on 100,000 random encodings and on 120,000 arguments next
  to `y²` and `y·next_up(y)`, where the root lies just beside a binary64
  number or a midpoint; exact squares return their root; special values.
- **Determinism digest:** the `sqrt` section on every target.
