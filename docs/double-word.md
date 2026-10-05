# Error-free transforms and double-word arithmetic

`morphiq_numerics::eft` provides the rounded sum or product of two binary64
numbers together with its exact rounding error. `morphiq_numerics::double_word`
builds an unevaluated sum of two binary64 numbers on those transforms, with
proved relative error bounds. Later functions' accurate paths are built from
these.

Every algorithm here is fully specified by its source, operation by operation.
The code follows the cited statement line for line, and nothing in it is a design
choice of this crate. `u = 2^−53` is the unit roundoff and `RN` is
round-to-nearest, ties-to-even.

## Sources

- T. J. Dekker, "A floating-point technique for extending the available
  precision", *Numerische Mathematik* 18, 1971: the splitting (§6, (6.1)–(6.3)),
  and Veltkamp's exact product (end of §5).
- M. Joldes, J.-M. Muller, V. Popescu, "Tight and rigorous error bounds for
  basic building blocks of double-word arithmetic", *ACM TOMS* 44(2), 2017:
  Fast2Sum and 2Sum (Algorithms 1 and 2), and the double-word algorithms.
- J.-M. Muller, L. Rideau, "Formalization of double-word arithmetic, and
  comments on …", *ACM TOMS* 48(1), 2022: Coq proofs of every bound, and the
  improved bound for the double-word product.

## Error-free transforms

| Function | Algorithm | Exact when |
|---|---|---|
| `two_sum(a, b)` | 2Sum (Knuth, Møller): Joldes et al. Algorithm 2 | the sum doesn't overflow |
| `fast_two_sum(a, b)` | Fast2Sum (Dekker): Joldes et al. Algorithm 1 | additionally `a = 0`, `b = 0`, or `e_a ≥ e_b` (`\|a\| ≥ \|b\|` suffices) |
| `two_prod(a, b)` | Veltkamp's product on Dekker's splitting | the domain below |

Each returns `(r, e)` with `r` the rounded result and `r + e` the exact sum or
product.

Addition can't underflow inexactly: every sum of two binary64 numbers is a
multiple of `2^−1074`, so a subnormal sum is exact. So 2Sum and Fast2Sum need
only the absence of overflow.

### `two_prod` without a fused multiply-add

`core` has no fused multiply-add, so the product's error is computed by
splitting.
- **The split** (Dekker (6.1), with `c = 2^27 + 1` from (6.2)): `p = RN(x·c)`,
  `q = RN(x − p)`, `head = RN(q + p)`, `tail = x − head`. The head carries at
  most 26 significant bits and the tail at most 26 (Dekker (5.5)–(5.7)).
- **The product** (Veltkamp, as Dekker states it at the end of §5): `p = RN(a·b)`,
  `e = (((a_h·b_h − p) + a_h·b_t) + a_t·b_h) + a_t·b_t`. The first word is
  `RN(a·b)`, which double-word arithmetic requires. Dekker's own `mul12` doesn't
  guarantee that.

Dekker proves exactness without overflow or underflow. In binary64 the result is
exact when `a` or `b` is zero, or when all of these hold, writing `e_x` for the
exponent of `x` (`2^e_x ≤ |x| < 2^(e_x+1)`):

1. **`a` and `b` are normal, with `|a|, |b| ≤ 2^996`.**
   - Then `|x·c| ≤ 2^996·(2^27 + 1) < 2^1024`, so the split's first product
     doesn't overflow.
   - Since `|x| ≥ 2^−1022`, `x·c` is normal, so its rounding is the one Dekker's
     model performs.
   - For a subnormal `x`, `x·c` can be subnormal and therefore exact, which isn't
     the rounding the split depends on.
2. **`e_a + e_b ≥ −970`.**
   - Every head and tail of `x` is a multiple of `ulp(x) = 2^(e_x − 52)`, so
     every partial product, `p`, and every intermediate sum is a multiple of
     `2^(e_a + e_b − 104) ≥ 2^−1074`.
   - Since Dekker's argument makes each of them exact with at most 53 significant
     bits, the subnormal grid can represent each one.
   - It also gives `|a·b| ≥ 2^−970`, so `p = RN(a·b)` is a normal rounding.
   - This is the condition Joldes et al. state for the existence of the
     product's error (`e_a + e_b ≥ e_min + p − 1`).
3. **`e_a + e_b ≤ 1021`.** Then `|a·b| < 2^1023`, and the partial products, at
   most `|a·b|·(1 + 2^−26)²`, stay below `2^1024`.

Outside this domain `two_prod` returns what the arithmetic produces, and exactness
isn't claimed.

## Double-word numbers

A double-word number is an unevaluated sum `hi + lo` of binary64 numbers with
`hi = RN(hi + lo)` (Joldes et al. Definition 1.4). The type admits only such
pairs:
- `from_parts` checks the condition;
- `sum` and `product` produce exact ones;
- every operation returns one.

| Operation | Algorithm | Relative error bound (Muller–Rideau Table 1) |
|---|---|---|
| `add_f64` | DWPlusFP, Joldes et al. Algorithm 4 | `2u²` |
| `add`, `sub` | AccurateDWPlusDW, Algorithm 6 | `3u² + 13u³` (asymptotically optimal, M–R Property 2.1) |
| `mul_f64` | DWTimesFP1, Algorithm 7 | `1.5u² + 4u³` |
| `mul` | DWTimesDW1, Algorithm 10 | `5u²/(1 + u)² < 5u²` under ties-to-even (M–R Theorem 2.6; 7u² in the 2017 paper) |
| `div_f64` | DWDivFP3, Algorithm 15 | `3u²` |
| `div` | DWDivDW2, Algorithm 17 (same results as Algorithm 16) | `15u² + 56u³` |

`sub` is `add` of the exact negation. The FMA-based variants (Algorithms 9, 11,
12 and 18) aren't used, since `core` has no fused multiply-add, and Algorithm 5
(the "sloppy" sum) has no relative bound.

**Domain.** The bounds are proved for an unbounded exponent range. They hold in
binary64 whenever every operation of the algorithm returns what it would there:
- no intermediate overflows;
- no rounded intermediate is subnormal;
- each exact product is within `two_prod`'s domain.

## Checked by

The oracle is exact integer arithmetic (`num-bigint` in the unpublished
`crates/reference`), decoding each binary64 from its bits. It shares no
arithmetic with the library.
- **2Sum:** 200,000 pairs with exponent gaps up to ±60, both orders; plus the
  subnormal range and zero.
- **Fast2Sum:** 200,000 pairs with `e_a ≥ e_b`.
- **2Prod:**
  - 200,000 normal pairs across the whole domain;
  - every edge of the domain (`e_a + e_b = −970` and `1021`, `|x| = 2^996`),
    with all-ones and power-of-two significands;
  - a split tie;
  - zeros.
- **Each double-word operation:** 100,000 random double-word operands, checked
  against its bound with the bound's denominator cleared, and checked to return
  a double-word number.
- **Published worst cases:**
  - DWPlusFP reaches above `1.99u²` on Joldes et al.'s example after Theorem 2.2.
  - AccurateDWPlusDW reaches above `2.99u²` on Muller and Rideau's Property 2.1.
    No random sample approaches that, so it shows the code is the published
    algorithm, not merely within its bound.
- **Oracle self-check:** a test confirms the oracle sees inexact sums and
  products, so each check can fail.
