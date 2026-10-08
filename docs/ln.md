# `ln` and `ln_1p`: correctly rounded logarithms

`morphiq_numerics::elementary::{ln, ln_1p}` (`crates/morphiq-numerics/src/ln/`)
follow this derivation step for step, with [exp]'s `Q128` type. Every bound
below is certified, and every constant generated, by the artifacts in §8. Each
numbered **decision** is a design choice open to review.

`ln(x)` returns `ln x` rounded to nearest, ties to even, for every binary64 `x`.
`ln_1p(x)` returns `ln(1 + x)`, without rounding `1 + x`. It is correctly rounded
whenever its fast path decides the rounding, and otherwise within a proved bound
(§7). Here `u = 2^−53` and `RN` is round-to-nearest-even.

## Sources

- **[DLM]** F. de Dinechin, C. Lauter, J.-M. Muller, "Fast and correctly rounded
  logarithms in double-precision", *RAIRO – Theoretical Informatics and
  Applications* 41, 85–102, 2007, doi:10.1051/ita:2007003: the exact reduction
  shared by both paths (§3.1) and the fast path's double-word evaluation of
  `ln(1 + z)` (§3.3).
- **[LM]** V. Lefèvre, J.-M. Muller, "Worst cases for correct rounding of the
  elementary functions in double precision", revised 2003: the accuracy that
  decides every case (Property 2, Table 5).
- **[Ziv]** A. Ziv, "Fast evaluation of elementary mathematical functions with
  correctly rounded last bit", *ACM TOMS* 17(3), 1991: the fast path returns only
  when its result provably rounds correctly.
- **[DW]** This crate's double-word arithmetic ([double-word.md](double-word.md)):
  its operations have machine-checked error bounds in IEEE 754 arithmetic.
- **[exp]** [exp.md](exp.md): the rounding test (§5) and the `Q128` type (§6),
  shared with `exp`.

Issue #30 cites Tang's table-driven logarithm (*ACM TOMS* 16(4), 1990). This
derivation follows [DLM]'s variant instead: its reduction is exact, so the fast
and accurate paths share it and its tables.

## 1. Specification

**`ln`:**

| Input | Result | Why |
|---|---|---|
| NaN, `x < 0`, `−∞` | NaN | outside the domain |
| `±0` | `−∞` | IEEE 754-2019 §9.2 |
| `+∞` | `+∞` | |
| `1` | `+0` | exact |
| otherwise | `RN(ln x)` | §3–§6 |

**`ln_1p`:**

| Input | Result | Why |
|---|---|---|
| NaN, `x < −1`, `−∞` | NaN | outside the domain |
| `−1` | `−∞` | IEEE 754-2019 §9.2 |
| `+∞` | `+∞` | |
| `\|x\| < 2^−54`, `±0` included | `x` | correctly rounded (§7); keeps the sign of zero |
| otherwise | §7 | |

`generators/ln_reference.py` (on `main`) derives every reference value with a
rigorous interval oracle. Its fixture `crates/reference/fixtures/ln.json` is the
test reference.

## 2. Accuracy needed

[LM] Property 2: if `y*` is within mantissa distance `2^−118` of `ln x`, for any
binary64 `x`, then rounding `y*` rounds `ln x` correctly. There's no exception
range: unlike `exp`, the whole domain needs only this bound. A relative error
`ε` is a mantissa distance below `2ε` ([LM] footnote 10), so a relative error
below `2^−119` suffices. [DLM] §3.1 states the same requirement.

`ln x` is never subnormal: for `x ≠ 1`, `|ln x| > 2^−54`. So no result needs
gradual underflow, and none overflows (`|ln x| < 745`).

**`ln_1p`:** [LM] gives no worst cases for `ln(1 + x)`, so §7 states the bound
proved instead of claiming correct rounding everywhere.

## 3. Argument reduction (after [DLM] §3.1)

**Decision 1: [DLM]'s exact reduction, with 128 reciprocals of 10 significant
bits.**
1. **Subnormal `x`:** multiply by `2^54`, exactly, and subtract 54 from the
   exponent below. So `x = 2^e·m` with `m ∈ [1, 2)`, and `−1,074 ≤ e ≤ 1,023`.
2. **The index:** `i` is the top 7 bits of `m`'s fraction, so
   `m ∈ [1 + i/128, 1 + (i+1)/128)`.
   - `i < 53`: `y = m`, `E = e`.
   - `i ≥ 53`: `y = m/2`, `E = e + 1`.

   So `y ∈ [0.70703125, 1.4140625)`, an interval around 1 bounded near
   `[√2/2, √2]`, as in [DLM]. Also `−1,074 ≤ E ≤ 1,024`.
3. **The reciprocal:** `R[i]` approximates `1/y` at the centre of `i`'s
   interval, rounded to 10 significant bits. `R[0] = R[127] = 1` exactly, so
   arguments near 1 reduce with no table term (*generated*: `R_BITS`). Over
   every interval, `|y·R[i] − 1| ≤ 2^−7` (*generated* and checked).
4. **Then** `ln x = E·ln 2 + (−ln R[i]) + ln(1 + z)`, with `z = y·R[i] − 1`.

**`z` is exact, as a double-word** ([DLM]'s portable version):
1. `(p, q) = two_prod(y, R[i])`. `y·R[i]` has at most 63 significant bits, and
   `two_prod` is exact on its domain [DW].
2. `p − 1` is exact: by Sterbenz's lemma, since `p ∈ [1/2, 2]`.
3. `(z_hi, z_lo) = two_sum(p − 1, q)`, so `z_hi + z_lo = z` exactly, with
   `|z_lo| ≤ 2^−53·|z_hi|`.

`y` is a multiple of `2^−53` and `R[i]` of `2^−10`, so `z` is a multiple of
`2^−63`. So `z` is `0` or `|z| ≥ 2^−63`, and `|z_hi| ≥ 2^−64`. The certificates
assume that range (§4).

**Machine-checked:** `formal/ln/LnReduction.v` transcribes `Reduced::of`,
`Reduced::z` and `Reduced::z_exact` on binary64 and the proved `Q128`
transcription, and proves them.
- **`reduce_ok`:** for every finite `x > 0`, subnormals included, `x = 2^E·y`
  exactly, with `y` in table interval `i`, on `2^−53`'s grid, and
  `−1,074 ≤ E ≤ 1,024`. The proof reads the fields from `x`'s encoding as the
  code does.
- **`z_ok`:** `(z_hi, z_lo)` is `y·R[i] − 1` exactly, a double-word with
  `|z_lo| ≤ 2^−53·|z_hi|`, `|z| ≤ 2^−7`, and either zero or
  `|z_hi| ≥ 2^−63`.
- **`z_exact_ok`:** `z_exact` is the same value in `Q128`, normalized or zero.

`formal/ln/LnTables.v`, which `generators/ln_constants.py` writes with the
tables, proves each `R[i]` from its encoding: on `2^−10`'s grid, and within
`2^−7` of `1/y` at both ends of its interval. The formal job compares the
reduction with the Rust code bit for bit on the internal cross-check corpus.

**The three cases** for the error analysis. Each certificate is relative to
`ln x`, so it needs each term's size over `ln x`:
- **A:** `E = 0` and `R[i] = 1`. Then `ln x = ln(1 + z)`, with no other term.
- **B:** `E = 0` and `R[i] ≠ 1`. Then `|ln x| ≥ 0.003913` (`i = 126`).
- **C:** `E ≠ 0`. Then `|ln x| ≥ 0.34646`.

`generators/ln_constants.py` encloses the ratios in interval arithmetic
(`mpmath.iv`, 128 bits, outward rounding):
- over every table interval, closed and widened by `2^−52` on each side, which
  covers `ln_1p`'s `y'` (§7);
- over every exponent of the case, `−1,074 ≤ E ≤ 1,024`.

Each expression uses `ln y` once, so its enclosure is tight. No monotonicity
argument is needed.

| Case | `\|E·ln 2 / ln x\|` | `\|−ln R[i] / ln x\|` | `\|ln(1 + z) / ln x\|` |
|---|---|---|---|
| B | 0 | ≤ 1.51475 | ≤ 0.51475 |
| C | ≤ 2.00062 | ≤ 0.99205 | ≤ 0.01136 |

Every certificate's hypotheses carry these bounds widened by at least 1%.

## 4. Fast path (after [DLM] §3.3)

**Decision 2: [DLM]'s portable evaluation, on the crate's proved double-word
operations.**
1. **The cubic tail.** `t ≈ z_hi³·W(z_hi)`, with
   `W(z) = c3 + z·(c4 + … + z·c9)`:
   - `w` is `W(z_hi)` by Horner's scheme in binary64;
   - `z3 = RN(z_hi·RN(z_hi²))`;
   - `t = RN(z3·w)`.

   `c3`–`c9` are binary64 coefficients from Sollya's `fpminimax` for
   `ln(1 + z) − z + z²/2`, relative, on `|z| ≤ 0.0078126` (*generated*). Their
   relative approximation error is below `0x1.0881…p−54` (Sollya's `supnorm`).
   The evaluation error of `t` is below `2^−50` relative (*certified*:
   `formal/ln/tail.g`, proves `2^−51.09`).
2. **`−z²/2`.** `(s_hi, s_lo) = two_prod(z_hi, z_hi)`, exact. Halving it is
   exact, which gives `B = (−s_hi/2, −s_lo/2)`.
3. **The cross term.** `c = RN(z_hi·z_lo)`, then `v = RN(t − c)`. That is
   `z³W − z_hi·z_lo`, with `z_lo²/2` dropped.
4. `P = DoubleWord(z_hi, z_lo).add(B).add_f64(v)`, which is `ln(1 + z)`.
   - Its relative error is below `3·2^−66 ≈ 2^−64.4` (*certified*:
     `formal/ln/p.g`, proves `2^−64.92`).
   - That covers the tail, the approximation error, `W(z) − W(z_hi)`, the dropped
     `z_lo²/2` and both double-word additions.
5. `S = NEG_LN_R[i].add(P)`. `NEG_LN_R[i]` is `−ln R[i]` as a double-word, and its
   relative error is below `2^−107.1` (*generated*: `NEG_LN_R_BITS`).
6. **Decision 3: `E·ln 2` from a 42-bit split** (after [DLM] §3.3, which uses 40
   bits).
   - `LN2_HI` is `ln 2` rounded to 42 bits, and `LN2_LO = RN(ln 2 − LN2_HI)`.
     Together they're within `2^−101.5` of `ln 2` (*generated*).
   - `E·LN2_HI` is exact for `|E| < 2^11`.
   - `(l_hi, l_lo) = two_sum(E·LN2_HI, RN(E·LN2_LO))`.
   - Its relative error against `E·ln 2` is below `2^−96.47` (*generated*).
7. `Y = DoubleWord(l_hi, l_lo).add(S)`.

The kernel adds every term, including a zero one (`E = 0`, or `R[i] = 1`);
the fast-path certificates also cover skipping it.

**The fast-path bound:** relative to `ln x`, `Y`'s error is below `2^−64`
(*certified*, by case):
- `formal/ln/fast_a.g` proves `2^−64.42`;
- `formal/ln/fast_b.g` proves `2^−65.36`;
- `formal/ln/fast_c.g` proves `2^−70.86`.

Each certificate composes four things:
- `P`'s bound;
- the tables' errors;
- `E·ln 2`'s error;
- the `add` bound `3u²/(1 − 4u)`, machine-checked [DW].

[DLM] §3.3 reports about `2^−60` for its portable fast path. The difference is
the degree-9 polynomial against [DLM]'s degree 7, with the double-word
additions certified here.

## 5. Rounding test

[exp] §5, unchanged, with **`ε₁ = 2^−63`**: `EPS = 2^−63·(1 + 2^−50)`, shared by
`ln` and `ln_1p`. `ln`'s fast path proves `2^−64`, and `ln_1p`'s `2^−63` (§7).
- The proof needs `ln x` not to be a breakpoint. For rational `x ≠ 1`, `ln x` is
  transcendental (Lindemann: `e^a` is transcendental for algebraic `a ≠ 0`). And
  `x = 1` never reaches the test (§1).
- Every result is normal (§2), so no scaling follows, and the test's `ulp` is
  the result's.

When the test passes, the returned `y_hi` is `RN` of the exact value. This holds
for `ln_1p` too: the test needs only the fast path's bound, not worst cases.

## 6. Accurate path

**Decision 4: [exp]'s `Q128` type, under its contract** (multiplication truncated,
relative error in `[−2^−127, 0]`; addition within `2^−126·max(|a|, |b|)`; exact
conversion from and rounding to binary64).

1. `z = y·R[i] − 1` exactly. It's computed in integer arithmetic from `y`'s and
   `R[i]`'s significands and converted to `Q128` exactly: `z` is a multiple of
   `2^−63`, with `|z| ≤ 2^−7`.
2. `ln(1 + z) = z·(1 − z/2 + z²/3 − …)`. Its series to degree 18, in Horner form:
   ```
   G_18 = 1/18;   G_k = 1/k − z·G_(k+1),  k = 17, …, 1;   Lz = z·G_1
   ```
   - `1/k` are `Q128` constants (*generated*: `RECIPROCALS`).
   - **The degree** is the least `d` whose truncation, `|z|^d / (d + 1)` (the
     first omitted term of an alternating, decreasing series), is at most
     `2^−125`. That is negligible next to `Q128`'s rounding (*generated*:
     `DEGREE = 18`).
   - Each Horner level's absolute error is bounded from the previous one
     (*certified*: `formal/ln/accurate_level_01.g` to `_17.g`). With the
     truncation, `|G_1 − ln(1 + z)/z| ≤ 818·2^−135`.
3. `Y = (E·LN2_Q128 + NEG_LN_R_Q128[i]) + Lz`.
   - `E` converts exactly.
   - `LN2_Q128` and `NEG_LN_R_Q128[i]` have relative errors below `2^−127`
     (*generated*).
   - **Unlike the fast path,** a zero term is skipped: with `E = 0` there's no
     `E·ln 2` term, and with `R[i] = 1` no table term. The certificates for cases
     A and B assume no addition there.
4. The result is `Y` rounded to binary64 once, in integer arithmetic.

**Total:** `Y`'s relative error against `ln x` is below `2^−123` (*certified*):
- `formal/ln/accurate_sum_a.g` proves `2^−125.32`;
- `formal/ln/accurate_sum_b.g` proves `2^−123.86`;
- `formal/ln/accurate_sum_c.g` proves `2^−123.51`.

That is a mantissa distance below `2^−122`, against `2^−118` needed (§2). So
rounding `Y` once rounds `ln x` correctly.

## 7. `ln_1p`

**Decision 5: three branches, none rounding `1 + x`.**

**`|x| < 2^−54`: return `x`.** This is correctly rounded.
- For `0 < |x| < 2^−54`, `|ln(1 + x) − x| ≤ x²/(2(1 − |x|))`, which is below
  `2^−55·(1 + 2^−53)·|x|`.
- `ln(1 + x)` lies on the side of `x` toward `−∞`. For `x > 0`, that is toward
  zero, where `x`'s half-gap is at least `2^−54·|x|`, even at a power of two. For
  `x < 0`, it is away from zero, where the half-gap is `ulp(x)/2 > 2^−54·|x|`.
- For subnormal `x`, the distance is below `2^−2000`, far inside half an `ulp`.

So `RN(ln(1 + x)) = x`, and `±0` keeps its sign.

**`2^−54 ≤ |x| < 2^−7`: `z = x`, exactly.** This is case A with
`(z_hi, z_lo) = (x, 0)`, so `|z_hi| ≥ 2^−54`. Both paths and both certificates
apply unchanged: §4's steps 1–4 and §6 at `z = x`, with no `E` or table term.
The fast path is within `2^−64`, and the accurate path within `2^−123`.

**`|x| ≥ 2^−7`: `1 + x = h + l`, exactly.**
- **The split:**
  - for `x < 2^53`, `(h, l) = two_sum(1, x)` (`|x| ≤ 2^1020`, so it's exact [DW]);
  - for `x ≥ 2^53`, `(h, l) = (x, 1)`.

  Either way, `|l| ≤ 2^−53·(1 + 2u)·|h|`. For `x ∈ (−1, −1/2]`, `l = 0` (Sterbenz).
- **No case A here.** `h ≥ 1 + 2^−7` or `h ≤ 1 − 2^−7`, so `h` reduces with
  `i ∉ {0, 127}` or `E ≠ 0`. And `|ln(1 + x)| ≥ ln(1 + 2^−7) > 0.00778`.
- **Fast path:** `ln(1 + x) = ln h + ln(1 + l/h)`.
  - `Y_h` is `ln`'s fast path at `h` (§4), within `2^−64` of `ln h`.
  - Then `Y = Y_h.add_f64(RN(l/h))`.
  - Using `l/h` for `ln(1 + l/h)` costs at most `(l/h)²/(2(1 − |l/h|))`.
  - The bound is `2^−63` relative to `ln(1 + x)` (*certified*:
    `formal/ln/fast_ln_1p.g`, proves `2^−64.0`).
- **Accurate path:** `z' = (y·R[i] − 1) + R[i]·l·2^−E`. With `y`, `E` and `i`
  from `h`, `ln(1 + x) = E·ln 2 − ln R[i] + ln(1 + z')`.
  - The first term is exact, as in §6, and the second is an exact `Q128`
    product. Their `Q128` sum is within `2^−126·2^−7`.
  - That moves `ln(1 + z')` by less than `2^−133/(1 − 2^−7)`. Relative to
    `|ln(1 + x)|`, that is below `524·2^−135`, carried by `accurate_sum_b.g` and
    `_c.g` (zero for `ln`).
  - `|z'| ≤ 2^−7 + 2^−52 < 0.0078126`, inside every certificate's range.
  - `y' = (1 + x)·2^−E` lies within `2^−52` of `h`'s interval, so the case
    ratios of §3, enclosed over the widened intervals, cover `ln_1p` directly.
  - Then §6 steps 2–4 run on `z'`, with total relative error below `2^−123`.

**The bound.**
- When the rounding test passes, the result is `RN(ln(1 + x))` (§5).
- Otherwise the accurate result `Y` is within `2^−123` relative error, so
  `|ln_1p(x) − ln(1 + x)| ≤ ½·ulp + 2^−123·|ln(1 + x)| < (½ + 2^−70)·ulp`.
- It is correctly rounded unless `ln(1 + x)` lies within mantissa distance
  `2^−122` of a breakpoint. No published search excludes that, so it isn't
  claimed.

## 8. Certificates and generators

| Artifact | Tool | Establishes |
|---|---|---|
| `generators/ln_constants.py` | mpmath 1.4.1 | writes `crates/morphiq-numerics/src/ln/tables.rs`: `R[i]`, `−ln R[i]` (double-word and `Q128`), `LN2_HI`/`LN2_LO`, `ln 2` and `1/k` in `Q128`, `c3`–`c9`, each checked against its bound; derives `E·ln 2`'s error, the case ratios (§3) and the series degree (§6) |
| `generators/ln_poly.sollya` | Sollya 8.0 | `c3`–`c9` (`fpminimax`, relative) and the approximation bound (`supnorm`), in `generators/ln_poly.out` |
| `generators/ln_certificates.py` | Python, mpmath | writes every certificate below from those values, with each hypothesis widened by at least 1%; no number in a certificate is typed by hand |
| `formal/ln/tail.g` | Gappa 1.4.1 | the cubic tail, within `2^−50` relative |
| `formal/ln/p.g` | Gappa | `P` against `ln(1 + z)`, within `3·2^−66` relative |
| `formal/ln/fast_a.g`, `_b.g`, `_c.g` | Gappa | `ln`'s fast path, within `2^−64` relative, by case |
| `formal/ln/fast_ln_1p.g` | Gappa | `ln_1p`'s fast path, within `2^−63` |
| `formal/ln/accurate_level_*.g` | Gappa | the series' Horner levels |
| `formal/ln/accurate_sum_a.g`, `_b.g`, `_c.g` | Gappa | the accurate result, within `2^−123` relative, by case |

Every certificate's Coq proof is also built, with each rewriting hint proved, by the formal job ([exp.md](exp.md), gates).

**Gates:**
- **Certificates:** `scripts/check_certificates.sh` checks `formal/ln` as it
  does `formal/exp`, in the `certificates (sollya, gappa)` job:
  - the binding manifest matches;
  - the Sollya script reproduces its output exactly;
  - every certificate proves its goal.
- **Replay:** `scripts/check_generators.sh` replays both generators.

**The binding** (`formal/ln/binding.sha256`) covers this document, the
constants, the Sollya script and output, every certificate, and the kernels'
source (`ln/mod.rs`, `q128.rs`).

## 9. Checked by

- **Bit-exact agreement** with `crates/reference/fixtures/ln.json`
  (`crates/reference/tests/ln.rs`): 4,019 `ln` cases, including [LM] Table 5's
  worst cases, and 3,960 `ln_1p` cases. An `ln_1p` mismatch would be an input
  inside §7's window. It's reported, not waived.
- **Every unrounded result within its certified bound,** against values to 192
  bits (the fixture's `precise` section), in exact arithmetic
  (`src/ln/tests.rs`):
  - `ln`'s fast path within `2^−64` and accurate path within `2^−123`, on 1,200
    arguments;
  - `ln_1p`'s within `2^−63` and `2^−123` on 1,400 arguments across its
    branches, 200 of them around `2^53`, where `1 + x` splits as `(x, 1)`;
  - `P` against `ln(1 + z)` within `3·2^−66` for 600 double-word `z` with a
    nonzero low word, which random arguments rarely produce.
- **The fast paths against the accurate paths:** equal whenever the fast path
  returns, on 2^20 `ln` and about 550,000 `ln_1p` arguments. Measured, they send
  `2^−9.4` of arguments to the accurate path (1,502 of 1,048,576 for `ln`, 761 of
  550,857 for `ln_1p`), against the analytic bound `2^−9`; the tests fail above
  four times that.
- **The rounding test at its boundary,** for both signs and at powers of two.
- **The determinism digest's `ln` and `ln_1p` sections** on every target
  ([determinism.md](determinism.md)).
- Exhaustive checks of chosen sub-intervals against the oracle (scheduled).
