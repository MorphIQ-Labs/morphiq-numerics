# `exp`: correctly rounded exponential (derivation, draft for review)

> **Status: design under review.** This document is the derivation the kernel is
> written from. Under the [provenance policy](PROVENANCE.md#ai-assisted-contributions),
> the kernel is written by a person from this document. It lands in the same pull
> request as the kernel, so the document never describes code that doesn't exist.
> Each numbered **decision** below is a design choice open to review. Each value
> marked *generated* or *certified* comes from a committed generator or
> certificate, never typed in by hand.

`exp(x)` returns `e^x` rounded to nearest, ties to even, for every binary64 `x`.
Subnormal results are rounded once. Here `u = 2^−53`, `RN` is round-to-nearest-even,
and `L = ln 2 / 128`.

## Sources

- **[Tang]** P. T. P. Tang, "Table-driven implementation of the exponential function
  in IEEE floating-point arithmetic", *ACM TOMS* 15(2), 1989: the table-driven
  reduction and reconstruction (§3, §4).
- **[LM]** V. Lefèvre, J.-M. Muller, "Worst cases for correct rounding of the
  elementary functions in double precision", revised 2003: the accuracy that
  decides every case (Property 1, Tables 2 and 4).
- **[Ziv]** A. Ziv, "Fast evaluation of elementary mathematical functions with
  correctly rounded last bit", *ACM TOMS* 17(3), 1991: a fast path that returns
  only when its result provably rounds correctly, with a slower accurate path
  otherwise.
- **[DW]** This crate's double-word arithmetic ([double-word.md](double-word.md)):
  its operations have machine-checked error bounds in IEEE 754 arithmetic.

## 1. Specification

| Input | Result | Why |
|---|---|---|
| NaN | NaN | |
| `x ≥ X_OVERFLOW` | `+∞` | `X_OVERFLOW` is the least `x` whose exponential rounds to `+∞` (*generated*) |
| `x ≤ X_ZERO` | `+0` | `X_ZERO` is the greatest `x` whose exponential rounds to `+0` (*generated*) |
| `−2^−54 ≤ x < 2^−53` | `1` | the exponential rounds to 1 exactly there ([LM] Table 2; *generated* and checked) |
| otherwise | `RN(e^x)` | the rest of this document |

Covered by those rows: `+∞` (first row), `−∞` (second) and `±0` (third).

The thresholds come from `generators/exp_reference.py`, which derives them by
bisection with a rigorous interval oracle. That generator is already on `main`,
and its fixture `crates/reference/fixtures/exp.json` is the test reference:
- `X_OVERFLOW = 709.7827128933841` (`0x40862E42FEFA39F0`);
- `X_ZERO = −745.1332191019412` (`0xC0874910D52D3052`).

## 2. Accuracy needed

[LM] Property 1 bounds how close `e^x` can come to a rounding breakpoint, over the
whole binary64 range. The bound is a *mantissa distance*: the distance between
significands in `[1, 2)`.
- **`|x| ≥ 2^−30`:** an approximation within `2^−113` of `e^x` rounds correctly.
- **`2^−54 ≤ |x| < 2^−30`:** within `2^−158`.
- **`|x| < 2^−54`:** the table in §1 applies.

**Subnormal results** (`X_ZERO < x < X_SUBNORMAL ≈ −708.396`). Their breakpoints,
the midpoints `(2m + 1)·2^−1075`, are among the 54-bit test numbers of their
binade, which [LM]'s search covers. Its first interval in Table 4 starts at
`ln(2^−1074)`. So the `2^−113` bound applies to them as well.
- **Review point:** this argument should be checked by a second reader.

## 3. Argument reduction (after [Tang] §4, Step 2)

**Decision 1: a table of `N = 128` entries `T_j = 2^(j/128)`.** This keeps
`|r| ≤ L/2 ≈ 2^−8.53`, so a degree-6 polynomial meets the fast path's budget,
with a table of 2 KiB for the fast path and 2 KiB for the accurate path.
[Tang] uses 32 entries for a 0.54-ulp result; correct rounding needs a tighter
fast path.

1. `t = RN(x · INV_L)`, with `INV_L = RN(128 / ln 2)` (*generated*).
2. `n = RN_int(t)`, as `(t + S) − S` with `S = 1.5·2^52`. This is exact while
   `|t| < 2^51`, and here `|t| < 137,700 < 2^18`.
3. `j = n mod 128` (0 to 127) and `k = (n − j) / 128`, with `−1,076 ≤ k ≤ 1,024`.
4. `r = x − n·L`, with `L` split into four binary64 constants, named as in [Tang]
   (*generated*):
   - `L1`: `L` rounded to 35 significant bits, so `n·L1` is exact for `|n| < 2^18`;
   - `L2 = RN(L − L1)`;
   - `L3 = RN(L − L1 − L2)`;
   - `L4 = RN(L − L1 − L2 − L3)`.

   So `|L − (L1 + L2 + L3 + L4)| < 2^−206` (*generated*).
   - **Fast path:** `r1 = x − n·L1` is exact (Sterbenz, as in [Tang] §5.1, for
     `n ≠ 0`; `r1 = x` for `n = 0`). `(p2, e2) = two_prod(n, L2)` is exact.
     Then `r` is the double-word `(r_hi, r_lo)`:
     ```
     (s, t) = two_sum(r1, −p2)
     r_lo   = t − e2 − RN(n·L3)
     (r_hi, r_lo) = fast_two_sum(s, r_lo)
     ```
     Its absolute error is below `2^−90` (*certified*, §7).
   - **Accurate path:** `r1`, `p2`, `e2`, `(p3, e3) = two_prod(n, L3)` and
     `RN(n·L4)` are summed in 128-bit arithmetic (§5).

Then `e^x = 2^k · T_j · e^r`.

## 4. Fast path

**Decision 2: everything after the polynomial uses the crate's proved
double-word operations,** so the only new error analysis is the polynomial's.

1. **Polynomial.** `q = r_hi² · (½ + r_hi·(c3 + r_hi·(c4 + r_hi·(c5 + r_hi·c6))))`
   in binary64, Horner order.
   - `c3`–`c6` are binary64 coefficients from Sollya's `fpminimax` for
     `e^r − 1 − r − r²/2` on `|r| ≤ 0.0027077` (*generated*).
   - The approximation error `|e^r − 1 − r − q*(r)|` is certified with Sollya's
     `supnorm`: below `2^−77.2` (*generated*; target `2^−72`).
2. `P = DoubleWord(r_hi, r_lo).add_f64(q)`: `e^r − 1`. The terms `q` omits by using
   `r_hi` for `r` are below `|r_lo|·|r| ≤ 2^−70`.
3. `E = DoubleWord::from_f64(1.0).add(P)`: `e^r`.
4. `Y = T_j.mul(E)`, where `T_j` is a double-word table entry, `T_j` rounded to
   double-word (*generated*, error below `2^−106`).

**Fast-path error bound `ε₁`:** the relative error of `Y` against `T_j·e^r`. It
combines four terms:
- the polynomial's approximation and evaluation error (Gappa, *certified*);
- the reduction error;
- the double-word bounds (`2u²`, `3u²/(1 − 4u)`, `5u²`);
- the table's error.

Target: `ε₁ ≤ 2^−66`. That lets about 99.9% of arguments return from the fast
path; the measured rate is to be reported.

**Decision 3: the fast path doesn't handle results that may be subnormal**
(`k < −1021`). They go straight to the accurate path, which rounds once. Scaling
a rounded fast result by `2^k` there would round twice.

## 5. Rounding test

`Y = (y_hi, y_lo)` is a double-word number, so `y_hi = RN(y_hi + y_lo)`. `y_hi` is
the correctly rounded `e^x / 2^k` whenever the interval
`y_hi + y_lo ± ε₁·|Y|` contains no rounding breakpoint. Those are the midpoints
between `y_hi` and its neighbours.

**Decision 4: the test, with the crate's exact `ulp`:**
```
g = ulp(y_hi), halved when y_hi is a power of two and y_lo < 0
return y_hi · 2^k   if   |y_lo| + ε₁'·|y_hi|  <  g / 2
otherwise take the accurate path
```
Here `ε₁' = ε₁·(1 + 2^−50)` absorbs the rounding of `|y_hi|·ε₁'` and of the
sum. The comparison is then conservative.
- **To prove:** that the test never returns a wrongly rounded value. This is a
  two-line argument from the double-word property; Gappa will check the margin.

**Scaling:** `y_hi · 2^k` is exact for `k ≥ −1021`. For `k = 1024`, where `Y < 1`
near overflow, it's applied as `(y_hi · 2^(k−1)) · 2`.

## 6. Accurate path

**Decision 5 (made): 128-bit significand arithmetic,** not triple-word.
- **Why not triple-word:** Fabiano, Muller and Picot's triple-word algorithms
  assume a fused multiply-add, which `core` doesn't offer. Their bounds don't
  hold verbatim without one.
- **The type:** a private type `Q128 = (m: u128, e: i32)`, with value `m·2^e` and
  `m` normalized (top bit set), and truncating operations:
  - multiplication keeps the high 128 bits of the 256-bit product;
  - addition aligns, then truncates;
  - each operation's relative error is below `2^−126`.

  It is deterministic on every target and uses only integer instructions.

**General case** (`|x| ≥ 2^−30`):
1. `r = r1 − p2 − e2 − p3 − e3 − RN(n·L4)`, each binary64 term converted exactly
   to `Q128` and summed. The terms decrease in magnitude, so the absolute error
   is below `2^−130`.
2. `e^r` by its Taylor series to degree 12, in Horner form:
   `1 + r(1 + r/2(1 + r/3(… (1 + r/12))))`, with `1/k` as `Q128` constants
   (*generated*). Truncation: `|r|^13/13! < 2^−143`.
3. `Y = T_j·e^r`, with `T_j` as a `Q128` constant (*generated*, error below
   `2^−127`).
4. The result is `Y·2^k` rounded to binary64 directly from `(m, e + k)` in
   integer arithmetic, including subnormals: one rounding.

Total error below `2^−118` (*certified*), against `2^−113` needed (§2).

**Small arguments** (`2^−54 ≤ |x| < 2^−30`), which need `2^−158`:
1. `(h, l) = two_sum(1, x)`, exactly `1 + x`.
2. `d = e^x − 1 − x = x²/2 + x³/6 + x⁴/24 + x⁵/120` in `Q128`.
   - `|d| ≤ 2^−61`, so the relative error `2^−123` is below `2^−184` absolute.
   - Truncating after `x⁵`: `|x|^6/720 < 2^−189`.
3. `w = l + d` in `Q128`: `|w| ≤ ulp(h)/2 + 2^−61`, with absolute error below
   `2^−176`.
4. `RN(h + w)`: `h` if `|w|` is below half the gap on `w`'s side of `h`;
   otherwise `h`'s neighbour on that side.
   - [LM] guarantees `e^x` is at least `2^−158` from the breakpoint, and the
     error is below `2^−176`. So the comparison decides correctly, and no tie
     can occur.

## 7. Certificates and generators

In this draft so far: `generators/exp_constants.py` and `generators/exp_poly.sollya` (with its output `generators/exp_poly.out`), which write `crates/morphiq-numerics/src/exp/tables.rs`. That file isn't compiled until the kernel declares `mod tables`. The Gappa certificates follow.


| Artifact | Tool | Establishes |
|---|---|---|
| `generators/exp_constants.py` | mpmath, pinned | `INV_L`, `L1`–`L4`, `T_j` (double-word and `Q128`), `1/k` in `Q128`: each with its error |
| `generators/exp_poly.sollya` | Sollya 8.0, pinned image | `c3`–`c6` (`fpminimax`) and the approximation error (`supnorm`) |
| `formal/exp/fast.gappa` | Gappa 1.4.1, pinned image | the polynomial's evaluation error and the reduction error; with the double-word bounds, `ε₁` |
| `formal/exp/accurate.gappa` | Gappa | the accurate path's total error |
| `formal/exp/test.gappa` | Gappa | the rounding test's margin (§5) |

Each certificate is bound by hash to the source it describes
([double-word.md](double-word.md#machine-checked-proofs) describes the binding).

## 8. Checked by (when the kernel lands)

- Bit-exact agreement with `crates/reference/fixtures/exp.json`, 4,030 cases:
  - the published worst cases;
  - every threshold and its neighbour;
  - special values;
  - random arguments.
- The determinism digest on every target.
- The fast path's pass rate, measured and reported.
- Exhaustive checks of chosen sub-intervals against the oracle (scheduled).
