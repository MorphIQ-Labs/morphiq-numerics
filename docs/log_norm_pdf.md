# `log_norm_pdf`: the logarithm of the standard normal density

`morphiq_numerics::normal::log_norm_pdf`
(`crates/morphiq-numerics/src/log_norm_pdf/`) computes
`ln φ(x) = −x²/2 − ln √(2π)` for binary64 `x`.

This document is the contract and derivation the implementation follows. Each
numbered **decision** is a design choice open to review. Here `u = 2^−53`,
`RN` is round-to-nearest-even, and `C = ln √(2π) = 0.91893853320467274178…`.

## Sources

- **[DW]** `morphiq-numerics`' error-free transforms and double-word
  arithmetic ([double-word.md]):
  - `two_prod` is exact when `a·b = 0` or `|a·b| ≥ 2^−969`, and
    `|a| ≤ 2^e_a`, `|b| ≤ 2^e_b` with `e_a, e_b ≤ 994` and `e_a + e_b ≤ 1020`;
  - `DoubleWord::add` (AccurateDWPlusDW, Joldes, Muller & Popescu 2017,
    Algorithm 6) has relative error at most `3u² + 13u³` for operands up to
    `2^1016`.
- **[exp §5]** `morphiq-numerics`' rounding test ([exp.md] §5), machine-checked
  in `formal/binary64/RoundingTest.v` (`decide_with_ok`) for error bounds
  `2^−80 ≤ ε₁ ≤ 2^−60`.
- **[gen]** `generators/log_norm_pdf_constants.py`: `C` as the double-word
  `C_HI + C_LO`, with `|C − C_HI − C_LO| < 2^−109·C`, from a rigorous mpmath
  enclosure.

No published worst-case results exist for this function.

## 1. Specification

| Input | Result | Why |
|---|---|---|
| NaN | that NaN | |
| `±∞` | `−∞` | `−x²/2 → −∞` |
| `|x| < 2^−27`, `±0` included | `−C_HI = RN(−C)` | §2: `x²/2` cannot move `C` past a midpoint |
| `2^−27 ≤ |x| ≤ 2^500` | §3 | |
| `2^500 < |x| < 2^513` | §4 | |
| `|x| ≥ 2^513` | `−∞` | overflow: `x²/2 ≥ 2^1025` |

The result depends on `|x|` only, so `log_norm_pdf(−x) = log_norm_pdf(x)` bit
for bit. Every finite result is at most `−RN(C)`. Both terms are negative, so
there is no cancellation, and no result is subnormal or zero.

**Overflow.** `RN(v) = −∞` exactly when `|v| ≥ 2^1024 − 2^970`, that is
`f64::MAX` plus half its ulp. `|x| ≥ 2^513` gives `x²/2 ≥ 2^1025`, past the
threshold. For `2^512 ≤ |x| < 2^513` the result may or may not overflow, and §4
decides it exactly.

**Decision 1: correctly rounded where the rounding test decides; otherwise
within `(1/2 + 2^−50)` ulp.** This is the contract `ln_1p` states. With no
published worst cases, correct rounding everywhere is not claimed. The
fallback is expected on about one argument in `2^26` (§3). An accurate path,
as in `ln`, could make it unconditional. Regimes S (§2) and L
(§4) are correctly rounded everywhere.

## 2. Regime S: `|x| < 2^−27`

[gen] asserts that `C` lies more than `2^−55` below `C_HI + 2^−54`, the
rounding midpoint above it. For `|x| < 2^−27`, `x²/2 < 2^−55`, so
`RN(C + x²/2) = C_HI`, and the result is `−C_HI`.

## 3. Regime M: `2^−27 ≤ |x| ≤ 2^500`

With `a = |x|`:

1. **Square.** `X = DoubleWord::product(a, a/2) = a²/2`, exactly.
   - `a/2` is exact, since `a` is normal.
   - The product is at least `2^−55 ≥ 2^−969`.
   - `a ≤ 2^500` and `a/2 ≤ 2^499` meet `e_a + e_b = 999 ≤ 1020` [DW].
2. **Sum.** `Z = X.add(C_DW)`, where `C_DW = DoubleWord::sum(C_HI, C_LO)`. The
   sum is exact because `|C_LO| ≤ ulp(C_HI)/2`. `Z` approximates
   `S = a²/2 + C`:

   ```text
   |Z − S| ≤ (3u² + 13u³)·(S + 2^−109·S) + 2^−109·S = ε·S,   ε < 2^−103
   ```

   That is [DW]'s bound on `X + C_HI + C_LO`, plus [gen]'s truncation. Both
   operands are below `2^1000`, within `add`'s domain.
3. **Round.** `Z_hi = RN(Z)`, since `Z` is normalized. The rounding test
   decides whether `RN(S) = Z_hi`. If it passes, the result is `−Z_hi`, which
   is correctly rounded.

**Decision 2: reuse the machine-checked rounding test at `ε₁ = 2^−80`.**
Because `ε < 2^−103 ≤ 2^−80`, the test of [exp §5] with `ε₁ = 2^−80`, its
proved range's lower end, is valid as it stands:

```text
g = ulp(Z_hi), halved when Z_hi is a power of two
decided  ⇔  RN(|Z_lo| + RN(EPS·Z_hi)) < g/2,   EPS = 2^−80·(1 + 2^−50)
```

A smaller `ε₁` would decide more arguments but would need a new proof. With
`ε₁ = 2^−80`, the test fails only when `S` lies within about `2^−80·S` of a
midpoint: about one argument in `2^26`.

**The test is not run.** Whether it passes or fails, the result is the same
`−Z_hi`. The test only decides which results carry the correct-rounding
guarantee. Running it would matter only with an accurate path to fall back to,
and that path would sit behind `decide_with`. Until then the tests call
`ln`'s `decide_with` as the predicate that would justify a result that is not
correctly rounded.

**Fallback.** When the test fails, the result is still `−Z_hi`.
`|Z_hi − S| ≤ |Z_lo| + ε·S`, and `|Z_lo| ≤ ulp(Z_hi)/2`. Since
`S ≤ |Z_hi|·(1 + u)(1 + ε)/(1 − ε)` and `ulp(v) > u·|v|`,
`ε·S ≤ ε·(1 + u)(1 + ε)/((1 − ε)·u)·ulp(Z_hi) < 2^−51.3·ulp(Z_hi)`.
`generators/log_norm_pdf_bounds.py` checks this constant exactly.

## 4. Regime L: `2^500 < |x| < 2^513`

`a²/2` alone would leave `two_prod`'s domain, so the square is scaled:

1. `a' = a·2^−16`, exactly. Then `X' = DoubleWord::product(a', a'/2)` gives
   `a'²/2 = h' + l'` exactly: `a' < 2^497`, and `a'²/2 > 2^967`.
2. `a²/2 = 2^32·(h' + l')`, and `S = a²/2 + C`.

**Why `C` matters only at ties.** For `a > 2^500`:
- `ulp(a) ≥ 2^448`, so `a²/2` is a multiple of `2^895`;
- `S ≥ 2^999`, so every rounding midpoint is a multiple of `2^946`.

So `a²/2` either is a midpoint or lies at least `2^895` from every midpoint,
and `C < 1` cannot cross one. `RN(S) = RN(a²/2)`, except at a tie. There, `C`
breaks it away from zero rather than to even.

**Decision 3: the tie rule.** `h' = RN(a'²/2)` ties to even, and `l'` is the
exact remainder:
- If `l' = +ulp(h')/2`, the square is the midpoint above `h'`. `C` pushes `S`
  past it, so `RN(S') = h' + ulp(h')`.
- In every other case, ties below `h'` included, `RN(S') = h'`. Those ties are
  `l' = −ulp(h')/2`, or `−ulp(h')/4` when `h'` is a power of two, and `C`
  pushes towards `h'`.

Here `S' = S·2^−32`. The result is `−(r'·2^32)`, where `r'` is that value.
Scaling by `2^32` is exact unless the result overflows. IEEE 754 decides
overflow on the result rounded with unbounded exponent, which is `2^32·r'`, so
the multiplication gives `−∞` exactly when `RN(S)` overflows. Regime L is
correctly rounded everywhere.

## 5. Cost

**Regime M.** One `two_prod` and one double-word addition, about 20
floating-point operations, with no transcendental function.
**Regimes S and L.** Cheaper: a comparison, or one `two_prod` and a scaling.

**Local measurement** (Apple M1 Pro, release build, Rust 1.97.1;
`cargo test --release measure_cost -- --ignored --nocapture`; one run, not a
gate): 5.8 ns per call for `x` uniform in `[−8, 8]`.

## 6. Evidence plan

1. **Constants.** `generators/log_norm_pdf_constants.py` writes `C_HI` and
   `C_LO` and asserts §2's gap and [gen]'s truncation. The correctly rounded
   `C_HI` is `0.9189385332046728`. The platform's `ln(2π)/2` gives
   `…727`, one ulp low.
2. **Bounds.** `generators/log_norm_pdf_bounds.py` checks `ε < 2^−103`,
   `ε ≤ ε₁`, and the fallback constant `2^−50`, in exact rationals.
3. **Fixtures.** `generators/log_norm_pdf_reference.py` writes
   `crates/reference/fixtures/log_norm_pdf.json`: 6,543 correctly rounded
   references from `morphiq-numerics`' oracle.
   - **119 hand-picked cases:**
     - every regime boundary (`2^−27`, `2^500`, `2^512`, `2^513`) with its
       neighbours, both signs;
     - regime S far below its boundary: the least subnormal, the least
       normal, `2^−600`, and `2^−484` with its neighbours;
     - the overflow threshold, `1.8961503816218352e154`, the largest `x` with a
       finite result (found by bisection on the oracle), and its successor;
     - 12 ties in regime L and their neighbours. `a = m·2^k` with `m` odd and
       `m²` exactly 54 bits, so `a²/2` is a rounding midpoint, for example
       `(2^27 − 1)·2^478`.
   - **6,424 SplitMix64 cases:** 8 per binade from `2^−40` to `2^513`, both
     signs, and 2,000 in `[−8, 8]`.
   - **Validation.** An independent recomputation with plain mpmath at 1,400
     bits agrees on all 6,543 cases. 400 bits is not enough: at the ties,
     `C ≈ 0.92` beside `a²/2 ≈ 2^1000` needs about 1,050 bits to resolve. All
     24 tie results are the neighbour away from zero.
4. **Tests.** `crates/morphiq-numerics/src/log_norm_pdf/tests.rs` checks that
   every result matches its reference bit for bit. Decision 1's exception is
   allowed only where `decide_with` does not decide, and then within its
   bound. In the fixture, the test decides every case, and every result is
   correctly rounded. Other tests check symmetry in `x`, and that every finite
   result is at most `−C_HI`.
5. **Determinism.** `log_norm_pdf` is in the determinism digest
   ([determinism.md](determinism.md)).
6. **Mutation.** cargo-mutants 27.1.0 over `log_norm_pdf/mod.rs` catches 22 of
   24 mutants. The other two, `a < 2^−27` against `a ≤ 2^−27` or
   `a = 2^−27`, are equivalent: regime S is a shortcut, and below `2^−27`
   regime M returns the same `−C_HI` (§2's gap argument covers its sum).
