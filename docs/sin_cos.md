# `sin`, `cos` and `sincos`

`morphiq_numerics::elementary::{sin, cos, sincos}` (`crates/morphiq-numerics/src/trig/`)
follow this derivation:
- an exact Payne–Hanek reduction, sized by a closest-approach bound derived
  here;
- a table-driven double-word fast path;
- the rounding test;
- an accurate path in `Q256`, a 256-bit significand type with `Q128`'s contract.

Every bound is certified (§7).

- **Correctly rounded** wherever [LM]'s worst cases reach, and wherever the
  rounding test decides. [LM]'s worst cases reach `sin` for
  `|x| ≤ 1.4422·2^−26` and `2^−24 ≤ |x| ≤ 2 + 4675/8192`, and `cos` for
  `|x| ≤ 12867/8192`.
- **Otherwise** within `(1/2 + 2^−144)` ulp.
- **`sincos(x)`** returns exactly `(sin(x), cos(x))`.

## Sources

- **[LM]** V. Lefèvre, J.-M. Muller, "Worst cases for correct rounding of the
  elementary functions in double precision", revised 2003: Table 2 (small
  arguments), Table 8 and Property 5 (`sin`), Table 10 (`cos`).
- **[PH]** M. H. Payne, R. N. Hanek, "Radian reduction for trigonometric
  functions", *SIGNUM Newsletter* 18(1), 1983: the reduction's structure, keeping
  only the bits of `2/π` that matter.
- **[K]** A. Ya. Khinchin, *Continued Fractions*, Theorem 17: best approximations,
  for the closest-approach bound.
- **[ln]** [ln.md](ln.md) §5: the rounding test.

## 1. Specification

| Input | `sin` | `cos` |
|---|---|---|
| NaN, `±∞` | NaN | NaN |
| `\|x\| ≤ 0x1.7137449123ef6p−26` | `x`, exactly ([LM] Table 2's `1.4422·2^−26`; *generated*) | — |
| `\|x\| < 2^−25` | — | `1 − k·2^−53`, by four *generated* thresholds |
| otherwise | §3–§6 | §3–§6 |

**`cos` for small arguments.**
- For `|x| < 2^−25`, `cos x` lies within `2^−51` below 1. Its correctly rounded
  value is `1 − k·2^−53`, with `k` a non-decreasing step function of `|x|`
  ([LM] §2.3).
- `generators/sin_cos_reference.py` finds each step's last argument by bisection
  with the interval oracle (*generated*). The function compares `|x|` against
  the four thresholds.
- `cos` is monotone there, so the thresholds decide every argument exactly.

`generators/sin_cos_reference.py` writes the fixture
`crates/reference/fixtures/sin_cos.json`.

## 2. Accuracy needed

- **`sin`** on `2^−24 ≤ |x| ≤ 2 + 4675/8192`: mantissa distance `2^−126` ([LM]
  Property 5), so relative error below `2^−127`.
- **`cos`** on `2^−25 ≤ |x| ≤ 12867/8192`: `2^−142` ([LM] §6), so relative error
  below `2^−143`.
- **Elsewhere** there are no published worst cases, so the claim is a proved
  bound (§6).

Both requirements are past `Q128`'s reach, about `2^−123`, so the accurate path
uses `Q256` (§5).

## 3. Reduction

`|x| = k·π/2 + r`, `|r| ≤ π/4`. Then `sin`, `cos` is one of `±sin r` or `±cos r`,
by `k mod 4`, with `sin`'s sign from `x`.

**The closest approach** (*generated*: `generators/trig_reduction.py`).
- For `x = m·2^E` with `2^52 ≤ m < 2^53`, the quantity `x·(2/π) − k` equals
  `m·α_E` minus an integer, where `α_E = frac(2^E·2/π)`.
- Let `q_n` be the largest continued-fraction denominator of `α_E` below `2^53`.
  By best approximation [K], `‖m·α_E‖ ≥ ‖q_n·α_E‖` for every such `m`.
- The minimum over every exponent with `x ≥ π/4` is `2^−61.54`, at
  `x = 6381956970095103·2^797`. That is the classic worst case, derived here
  rather than cited.

**Payne–Hanek** ([PH]), in integer arithmetic.
- Bits of `2/π` of weight above `2^(1−E)` add only multiples of 4 to `x·(2/π)`,
  so they are skipped.
- The window down to weight `2^−(E+F)`, `F = 315`, is multiplied exactly by `m`.
  The truncation errs by less than `2^(53−F)`, which is `2^−200` relative to the
  closest approach. That is how `F` is chosen.
- `2/π` is stored to 1,408 bits (*generated*).
- The product's integer part gives `k mod 4`. Its 315-bit fraction `f` is
  rounded to the nearest multiple, so `f ∈ [−1/2, 1/2)`, and `r = f·π/2` in
  `Q256`.
- `r` is within `2^−199` of the exact `r`, relatively. That is checked on 607
  arguments, including the closest approach and the largest binary64, against
  references computed at 2,400 bits.
- Below `π/4`, `r = x` exactly.

## 4. Fast path

**Decision 1: a table at `a = i/64`, `i = 0..50`, and short polynomials in
`t = r − a`, `|t| ≤ 1/128`.**
1. From `Q256`'s `r`: `r_hi = RN(r)` and `r_lo = RN(r − r_hi)`, both relative to
   `|r|`. Their error against `r` is below `2^−106` relatively; its effect on the
   value enters as `2^−104`.
2. `i = RN_int(64·r_hi)`, and `t = (r_hi − i/64) + r_lo` exactly. The difference
   is exact by Sterbenz's lemma for `i ≥ 1`, and `t = r` for `i = 0`.
3. `sin t = t + t³·Ps(t²)` and `cos t − 1 = −t²/2 + t⁴·Pc(t²)`:
   - `Ps` and `Pc` have degree 2 in `t²`, with binary64 coefficients from Sollya's
     `fpminimax`. Each is fitted to its tail's series and bounded against it,
     plus the remainder, since the tails have removable singularities. Both are
     within `2^−54` relatively (*generated*: `generators/trig_poly.sollya`).
   - The tails are evaluated in binary64, within `2^−50` (*certified*:
     `formal/trig/sin_tail.g`, `cos_tail.g`).
   - The results are assembled as double-words: `sin t` within `2^−65` (proves
     `2^−66.06`) and `cos t − 1` within `2^−65` (proves `2^−66.83`)
     (*certified*: `sin_t.g`, `cos_t.g`).
   - **Below `|t| = 2^−60`,** `t` is `r_lo` alone, since `r_hi` equals the table
     point, and `t⁴` may underflow. A tail is then only known to lie within
     `[0, 3]` times its value, and the bounds still hold (*certified*:
     `sin_t_tiny.g`, `cos_t_tiny.g`).
   - `t` is 0 or at least `2^−317` in magnitude, since it's a difference on
     `Q256`'s grid.
4. `sin(a + t) = S + (S·(cos t − 1) + C·sin t)` and
   `cos(a + t) = C + (C·(cos t − 1) − S·sin t)`:
   - `S` and `C` are the table's double-words (*generated*, within `2^−107.1`).
   - They are combined with the proved `mul` and `add`/`sub` [DW].
   - The relative errors use each term's ratio to the result. Those are enclosed
     in interval arithmetic over every table interval (*generated*). The
     largest `S/sin(a+t)` is 2.0.
   - `sin` is within `2^−62` (proves `2^−64.98`) and `cos` within `2^−62`
     (proves `2^−71.99`) (*certified*: `fast_sin.g`, `fast_cos.g`).

## 5. Accurate path

**Decision 2: `Q256`, `Q128`'s contract at 256 bits.**
- Multiplication is truncated, with relative error in `[−2^−255, 0]`.
- Addition errs by at most `2^−254·max(|a|, |b|)`.
- Conversion from and rounding to binary64 are exact.
- `src/q256/tests.rs` checks the contract in exact big-integer arithmetic.

`sin r = r·H_1` and `cos r = G_1`, in `s = r²`:
- `H_n = 1 − (s/((2n)(2n+1)))·H_(n+1)` and `G_n = 1 − (s/((2n−1)(2n)))·G_(n+1)`,
  each starting from 1.
- The degrees, 22 and 23, are the least whose first omitted term is at most
  `2^−210` relatively (*generated*: `generators/trig_constants.py`, with the
  factors in `Q256`).
- Each level's error is bounded from the next (*certified*:
  `formal/trig/sin_level_*.g`, `cos_level_*.g`).
- End to end, with the truncation, the product and the reduction's `2^−199`
  through the mean value theorem, each result is within `2^−198` of the true
  value relatively (*certified*: `accurate_sin.g`, `accurate_cos.g`).

## 6. Rounding test and claims

**Decision 3: `ε₁ = 2^−62`** in [ln] §5's test, with `EPS = 2^−62·(1 + 2^−50)`.
- The proof needs the value not to be a breakpoint. `sin x` and `cos x` are
  transcendental for rational `x ≠ 0` (Lindemann).
- At that `ε₁` the test sends about one argument in 2^8.4 to the accurate path
  (measured: `3.0·10^−3` for each function; the analytic rate is at most `2^−8`).

**Claims:**
- Where [LM] covers the argument (§2), the accurate path's `2^−198` is far
  inside the requirement, so the result is correctly rounded.
- Elsewhere, when the test passes, the result is `RN(f(x))`. Otherwise it is
  within `(1/2 + 2^−144)` ulp. It is correctly rounded unless `f(x)` lies within
  mantissa distance `2^−197` of a breakpoint, which no published search excludes.
- `sin` on `1.4422·2^−26 < |x| < 2^−24` is in that case: [LM] covers neither
  side of it with a worst case.

`sincos` reduces once and finishes each value with the same code `sin` and `cos`
use, so its pair is theirs bit for bit.

## 7. Certificates, generators and tests

| Artifact | Establishes |
|---|---|
| `generators/trig_reduction.py` | the closest approach, `F`, `2/π` to 1,408 bits and `π/2` in `Q256` (`src/trig/reduction.rs`) |
| `generators/trig_poly.sollya` (Sollya 8.0) | `Ps`, `Pc` and their bounds, in `generators/trig_poly.out` |
| `generators/trig_constants.py` | `src/trig/tables.rs`: the table, the polynomials, the series factors and degrees; the enclosed ratios |
| `generators/trig_certificates.py` | writes every certificate in `formal/trig` (55) |
| `formal/trig/*` (Gappa 1.4.1, at 400 bits) | §4's tails, compositions and fast results; §5's levels and accurate results |
| `generators/sin_cos_reference.py` | the fixture: [LM] Tables 8 and 10, the small-argument thresholds, arguments near `k·π/2`, random arguments in every binade, 1,200 values to 256 bits, and 607 reductions |

The binding `formal/trig/binding.sha256` covers this document, the Sollya script
and output, the generated tables and every certificate. It also covers the
source: `trig/mod.rs` and `q256.rs`.

**Checked by:**
- `crates/reference/tests/sin_cos.rs`: 4,066 cases, bit for bit, for `sin`,
  `cos` and both halves of `sincos`.
- `src/trig/tests.rs`:
  - the reduction against its references;
  - every unrounded result within its bound;
  - the fast paths against the accurate paths, with the rates above.
- `src/q256/tests.rs`: `Q256`'s contract.
- The determinism digest's `sin_cos` section on every target.
