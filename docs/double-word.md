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

**Domain.** `two_prod(a, b)` is exact when `a · b = 0` or
`|a · b| ≥ 2^−969`, provided no operation overflows, which holds when
`|a|, |b| ≤ 2^996` and `|a · b| < 2^1023`.

- **Underflow:** machine-checked. This is Flocq's `Dekker` theorem (Boldo's
  formalization, `Flocq.Pff.Pff2Flocq`), whose algorithm is exactly this one:
  the same split with `s = 53 − ⌊53/2⌋ = 27`, the same rounded partial products,
  and the same summation order. It is instantiated for binary64 (radix 2,
  precision 53, minimum exponent −1074) with ties-to-even in
  `formal/two-prod/TwoProdBinary64.v`. Its hypothesis
  `|a · b| ≥ 2^(emin + 2·prec − 1) = 2^−969` covers subnormal operands.
- **Overflow:** argued, not checked. Flocq's model has gradual underflow and no
  overflow, so binary64 agrees with it as long as no operation overflows:
  - `|x·c| ≤ 2^996·(2^27 + 1) < 2^1024` for the split;
  - the partial products and sums are at most `|a · b|·(1 + 2^−26)² < 2^1024`.

These conditions are sufficient, not necessary: `2^−969` is the theorem's
hypothesis, not the boundary of exactness. Outside the domain, exactness is
neither claimed nor ruled out; `two_prod` returns what the arithmetic produces.
In particular, an earlier hand derivation of this domain included products in
`[2^−970, 2^−969)` and excluded subnormal operands. No proof covers that range, so
it isn't claimed. The proved domain admits subnormal operands, so they are
covered.

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

**Domain.** The bounds are proved (in Coq, see below) for an unbounded exponent range. They hold in
binary64 whenever every operation of the algorithm returns what it would there:
- no intermediate overflows;
- no rounded intermediate is subnormal;
- each exact product is within `two_prod`'s domain.

## Machine-checked proofs

`scripts/check_formal.sh` (the `formal (coq)` CI job) checks these, on Coq 8.15.2
with Flocq 3.4.3 and math-comp ssreflect 1.14.0, in an image pinned by digest.

**What is machine-checked:**
- **The double-word bounds.** `formal/double-word` is Muller and Rideau's Coq
  development, vendored unchanged under its MIT license (`PROVENANCE.md` there),
  which builds with no admitted goal. It proves each bound in the table above in
  Flocq's unbounded-exponent model, given an exact 2Prod (its `F2Mult_correct`
  hypothesis).
- **`two_prod`'s exactness.** `formal/two-prod/TwoProdBinary64.v` proves
  `two_prod_exact`: for binary64 with ties-to-even, `a · b = p + e` on the
  domain above. That discharges the 2Prod hypothesis, and the theorem rests
  only on Coq's four classical-reals axioms (`formal/axioms.expected`).
- **The binding.** `formal/binding.sha256` binds the proofs to `eft.rs` and
  `double_word.rs` by hash. Editing either source, or a proof, fails the lane
  until the proofs are rerun and the manifest is updated with them.

**What is argued, not machine-checked:**
- **The models agree:** binary64 coincides with the unbounded-exponent model when
  no operation overflows or rounds a subnormal (the domain stated above).
- **The transcription:** each Rust function is the Coq definition operation for
  operation. Where the paper proves an operation exact, the Coq definition leaves
  it unrounded and the Rust rounds it, which gives the same value.

| Rust | Coq definition | Theorem |
|---|---|---|
| `add_f64` | `DWPlusFP` (`DWPlus.v`) | Muller–Rideau Table 1, `2u²` |
| `add`, `sub` | `AccurateDWPlusDW` (`DWPlus.v`) | `3u² + 13u³` |
| `mul_f64` | `DWTimesFP` (`DWTimesFP.v`) | `DWTimesFP_correct`, `3/2·u² + 4u³` |
| `mul` | `DWTimesDW1` (`DWTimesDW.v`) | `DWTimesDW1_correct_even`, `< 5u²` under ties-to-even |
| `div_f64` | `DWDivFP3` (`DWDivFP.v`) | `DWDFP3_correct`, `3u²` (`dh`, `dt` exact) |
| `div` | `DWDivDW2` (`DWDivDW.v`) | `DWDDW_correct`, `15u² + 56u³` (`pih` exact) |
| `two_prod` | `Dekker` (Flocq), via `TwoProdBinary64.v` | `two_prod_exact` |

## Checked by

The oracle is exact integer arithmetic (`num-bigint` in the unpublished
`crates/reference`), decoding each binary64 from its bits. It shares no
arithmetic with the library.
- **2Sum:** 200,000 pairs with exponent gaps up to ±60, both orders; plus the
  subnormal range and zero.
- **Fast2Sum:** 200,000 pairs with `e_a ≥ e_b`.
- **2Prod:**
  - 200,000 normal pairs across the whole domain;
  - every edge of the domain (`e_a + e_b = −969` and `1021`, `|x| = 2^996`),
    with all-ones and power-of-two significands;
  - subnormal operands, which the proved domain admits;
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
