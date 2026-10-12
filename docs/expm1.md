# `expm1`: `e^x − 1` without cancellation

`morphiq_numerics::elementary::expm1` (`crates/morphiq-numerics/src/expm1/`)
follows this derivation. Near zero it evaluates its own polynomial and series,
because `e^x − 1` cancels there. Elsewhere it first uses `exp`'s 512-entry stages, with compensated subtraction
before scaling. The 128-entry double-word and accurate paths remain the
fallback. Every bound is certified (§7).

`expm1(x)` is `e^x − 1`:
- correctly rounded whenever its rounding test decides;
- otherwise within `(1/2 + 2^−65)` ulp;
- `expm1(x) = x` for `|x| < 2^−54`.

## Sources

- **[exp]** [exp.md](exp.md) §8: the reduction `x = k·ln 2 + j/128·ln 2 + r`,
  the fast value and the `Q128` accurate path of `exp`'s fallback.
- **[ln]** [ln.md](ln.md) §5: the rounding test, here with its own `ε₁`.
- **[LM]** Lefèvre and Muller (2003) give no worst cases for `expm1`, so its
  bound is stated, as `ln_1p`'s is.

## 1. Specification

| Input | Result | Why |
|---|---|---|
| NaN | NaN | |
| `x ≥ 709.782712893384` (`0x40862E42FEFA39F0`) | `+∞` | the least `x` whose result rounds to `+∞` (*generated*) |
| `x ≤ −37.42994775023705` (`0xC042B708872320E2`) | `−1` | the greatest `x` whose result rounds to `−1` (*generated*) |
| `\|x\| < 2^−54`, `±0` included | `x` | correctly rounded, below |
| `2^−54 ≤ \|x\| < 2^−5` | §3, §4 | small arguments |
| otherwise | §5 | [exp]'s path |

`generators/expm1_reference.py` derives the thresholds by bisection with the
interval oracle. Its fixture `crates/reference/fixtures/expm1.json` is the test
reference.

**`|x| < 2^−54` returns `x`, correctly rounded.**
- `e^x − 1 − x = x²/2·(1 + x/3 + …)`, which is positive and below
  `2^−55·(1 + 2^−53)·|x|`.
- Half of `x`'s gap on either side is at least `2^−54·|x|`. That holds even at a
  power of two, where the gap toward zero is halved.

So `RN(e^x − 1) = x`. The generator checks this: the result first differs from
`x` at `|x| = √2·2^−53`.

## 2. Accuracy

There are no published worst cases. So for each path, §6 combines the rounding
test, which is exact when it passes, with a proved bound when it doesn't.

## 3. Small arguments, fast path (`2^−54 ≤ |x| < 2^−5`)

**Decision 1: a polynomial below `2^−5`; [exp]'s path above.** At the
threshold, [exp]'s fast error, amplified by the cancellation
`e^x / |e^x − 1| ≤ 32.51`, still fits the fast budget (§5).

1. **The tail** `t ≈ x³·W(x)`, with `W = c3 + x·(c4 + … + x·c9)`:
   - `c3`–`c9` are binary64 coefficients, fitted by Sollya's `fpminimax` to the
     tail `(e^x − 1 − x − x²/2)/x³`, relative, on `|x| ≤ 0.0312501` (*generated*).
   - The tail has a removable singularity at 0, which Sollya's `supnorm` can't
     enclose. So `W` is fitted to and bounded against `T`, the tail's series to
     31 terms, and the bound adds `T`'s remainder (below `2^−280`).
   - The total relative error is below `0x1.0012p−54`.
   - The evaluation is as in [ln] §4 step 1: `w` by Horner's scheme, then
     `x3 = RN(x·RN(x²))` and `t = RN(x3·w)`. Its relative error is below
     `2^−50` (*certified*: `formal/expm1/tail.g`, proves `2^−51.09`).
2. `x²/2` exactly: `(s_hi, s_lo) = two_prod(x, x)`, halved.
3. `P = DoubleWord(x).add(x²/2).add_f64(t)`. Its relative error against
   `e^x − 1` is below `13·2^−66 ≈ 2^−62.3` (*certified*: `formal/expm1/p.g`,
   proves `2^−62.46`).
   - The tail's error, weighted by `x²/6 ≤ 2^−12.6`, dominates. That is why this
     function's `ε₁` is `2^−62` (§6).

`Expm1SmallApprox.v` independently proves the approximation bound for the
stored binary64 coefficients. `Expm1SmallSquare.v`, `Expm1SmallAdd.v` and
`Expm1SmallPoly.v` establish exact halving, double-word normalization and
binary64 evaluation. `Expm1SmallFast.v` composes those facts with the
certificates and proves every accepted small-path result correctly rounded.

## 4. Small arguments, accurate path

`(e^x − 1)/x = 1 + x/2·(1 + x/3·(1 + …))` in `Q128`:
- `H_(d+2) = 1` and `H_m = 1 + (x·(1/m))·H_(m+1)`, for `m = d + 1` down to `2`;
- then `x·H_2`.

**The degree** `d = 15` is the least whose truncation, at most
`(26/25)·A^(d+1)/(d+2)!` over `(e^x − 1)/x ≥ 1 − A/2`, is at most `2^−125`
(*generated*: `generators/expm1_constants.py`, with `1/m` as `Q128` constants).
Taylor’s theorem supplies the factor `exp(t·x)`, `0 < t < 1`;
`exp(A) < 26/25` bounds it for either sign. The first omitted term alone
does not bound the positive-input tail.

Each level's error is bounded from the previous one (*certified*:
`formal/expm1/accurate_level_02.g` to `_16.g`). The result is within `2^−123`
of `e^x − 1` (*certified*: `formal/expm1/accurate_small.g`).

`Expm1Series.v` proves the Taylor remainder from the definition of `exp`.
`Expm1SmallAccurate.v` connects all 15 levels to the executable Q128
operations and generated reciprocal encodings, proves the relative bound,
and proves the final binary64 conversion rounds that approximation once.

## 5. Other arguments

### 5.1. Exponential stages

For `−37 < x < 704` and `|x| ≥ 2^−5`, use [exp.md](exp.md) §3's reduction
and §5–§6's stage values `(h,l)` for `z = exp(x)/2^k`. The reduction proves
`−54 ≤ k ≤ 1016`. Each stage subtracts before scaling:

```
(s, e) = two_sum(h, −2^−k)
lo = RN(e + l)
eps = RN(base + RN(RN(|e| + |l|) · 2^−51))
```

`base` is `2^−59` for A and `2^−68` for B. The exponential evaluation error
is at most `base/2`. The binary64 proof accounts for every rounding in `lo`
and `eps`, and proves

`|z − 2^−k − (s + lo)| + 2^−53(|lo| + eps) ≤ eps`.

The interval test accepts only when `RN(s + RN(lo − eps))` and
`RN(s + RN(lo + eps))` agree. Its proof also covers the larger low words
that can arise for negative arguments. The accepted word is multiplied by
`2^k` exactly: the screened domain proves `|z − 2^−k| ≥ 2^−8`, so neither
rounding nor scaling encounters subnormal results, and overflow is excluded.

`formal/exp/Expm1Stages.v::expm1_stages_ok` proves the complete screened
computation returns `RN(exp(x) − 1)` whenever it accepts. Its dependencies
`Expm1Subtract.v` and `Expm1Scale.v` establish subtraction, error-budget
arithmetic and scaling. A declined test proceeds to stage B, then to §5.2.
This adds no whole-domain correct-rounding claim to the accurate fallback.

### 5.2. Fallback

**Fast:** [exp]'s reduction and fast path give `Y ≈ 2^(j/128)·e^R`, within
`2^−69` (`formal/exp/fast.g`), and `e^x − 1 = 2^k·(2^(j/128)·e^R − 2^−k)`.

**Decision 2: subtract `2^−k` before scaling.**
- `M = Y.add_f64(−2^−k)` keeps the subtraction operands at most `2^54`,
  inside the double-word bounds' domain, even where `e^x` nears overflow.
- `2^−k` is exact: `−54 ≤ k ≤ 1024`, so `2^−k` is at worst a subnormal power of
  two.
- Both words of `Y` lie on the `2^−1020` grid. After subtracting `2^−k`,
  both words lie on the `2^min(−1020,−k)` grid. Scaling by `2^k` is exact:
  the resulting grid is no finer than `2^−1074`, including subnormal low
  words. A finite margin below overflow also covers the final `2Sum`.

The relative error against `e^x − 1` is `kq·eY·(1 + ea) + ea`, with
`kq = e^x/(e^x − 1)`:
- `|kq|` is largest at `|x| = 2^−5`, below `32.51`, enclosed in interval
  arithmetic. It decreases on both sides as `|x|` grows.
- The total is below `2^−62` (*certified*: `formal/expm1/fast_general.g`,
  proves `2^−63.96`).

**Accurate:** [exp]'s accurate `e^x`, within `2^−123.9`, less 1 in `Q128`. The
addition errs by at most `2^−126·max(|V|, 1)`, where `V` is the Q128
approximation to `e^x`. Including `V`'s error gives
`max(|V|, 1)/|e^x − 1| ≤ 542/16`. The result is within `2^−118` of `e^x − 1`
(*certified*: `formal/expm1/accurate_general.g`, proves `2^−118.55`).

**Machine-checked:** `formal/exp/Expm1GeneralReduction.v` computes the
128-entry fallback index and scale from the input, and proves the reduction's
hypotheses for finite `−37.43 ≤ x < X_OVERFLOW`, `|x| ≥ 1/32` (a superset of
arguments admitted by the public screens). `Expm1GeneralSubtract.v`,
`Expm1GeneralScale.v`, `Expm1GeneralSum.v` and `Expm1GeneralFast.v` compose
that reduction with the fast value, cancellation bound, exact scaling,
renormalization and rounding decision. `em_general_fast_ok` proves an
accepted result is `RN(e^x − 1)`, including the largest finite inputs.

`Expm1GeneralAccurate.v` composes the same reduction with the executable Q128
arithmetic and proves the `2^−118` relative bound before conversion.
`em_general_accurate_round` proves the final conversion is finite and rounds
that approximation once. Neither theorem assumes a published worst-case
separation for `expm1`; the accurate branch retains the bounded contract in §6.
The small-argument proofs in §3–4 establish the corresponding bounds.

## 6. Rounding test and bound

**Decision 3: `ε₁ = 2^−62`.** That's [ln] §5's test, with
`EPS = 2^−62·(1 + 2^−50)`. The small and general fallback fast paths are certified within it. An accepted
test places the error interval strictly inside the rounding cell; no
midpoint-distance hypothesis is needed for this branch.

For these fallback paths, at that `ε₁` the test sends about one argument in 2^8.5 to the accurate path
(measured: `2^−8.5` small, `2^−8.4` otherwise; the analytic rate is at most
`2^−8`).

**The bound:**
- When the test passes, the result is `RN(e^x − 1)`.
- Otherwise the accurate result is within `2^−118` relatively, so the error is
  at most `(1/2 + 2^−65)` ulp.
- It is correctly rounded unless `e^x − 1` lies within mantissa distance
  `2^−117` of a breakpoint. No published search excludes that.

`formal/exp/Expm1.v` transcribes the public entry, including every comparison,
accepted stage, fallback decision and final conversion. Its finite-input
theorem proves overflow returns positive infinity; otherwise the result is
`RN(z)` for an approximation `z` within `2^−118` relatively of `exp(x)−1`.
The accepted fast-path theorems establish `z = exp(x)−1`. The entry theorem
adds no worst-case separation assumption. `Expm1Thresholds.v` proves the
screens for overflow, rounding to `−1`, and returning `x`, including
subnormal inputs. Separate entry theorems cover NaNs, infinities and signed
zeros.

## 7. Certificates, generators and tests

| Artifact | Establishes |
|---|---|
| `formal/exp/Expm1Subtract.v`, `Expm1Scale.v`, `Expm1Stages.v` | screened exponential stages, including cancellation and exact scaling |
| `formal/exp/Expm1Small*.v`, `Expm1Series.v` | small fast decision, exact square/halving, Q128 series and Taylor remainder |
| `formal/exp/Expm1.v`, `Expm1Thresholds.v` | public entry and special-value screens |
| `formal/exp/Expm1General*.v` | general fallback reduction, fast decision and accurate Q128 bound with single rounding |
| `generators/expm1_poly.sollya` (Sollya 8.0) | `c3`–`c9` and their bound, with the remainder, in `generators/expm1_poly.out` |
| `generators/expm1_constants.py` | `src/expm1/tables.rs` and `Expm1Tables.v`: coefficients, Q128 reciprocals, degree and checked encodings |
| `generators/expm1_certificates.py` | writes every certificate below; the ratio `kq` is enclosed with `mpmath.iv` |
| `formal/expm1/tail.g`, `p.g` | the small fast path: `2^−50`, then `2^−62.3` |
| `formal/expm1/accurate_level_*.g`, `accurate_small.g` | the small accurate path: `2^−123` |
| `formal/expm1/fast_general.g`, `accurate_general.g` | the other paths: `2^−62` and `2^−118` |
| `generators/expm1_reference.py` | the fixture: thresholds, special values, random arguments at every scale, and 1,200 values to 192 bits |

Every certificate's Coq proof is also built, with each rewriting hint proved, by the formal job ([exp.md](exp.md), gates).

The binding `formal/expm1/binding.sha256` covers this document, the Sollya
script and output, the constants, every certificate and the source. The global
`formal/binding.sha256` additionally binds the executable Coq transcriptions,
kernel audit and Rust sources.

**Checked by:**
- `crates/reference/tests/expm1.rs`: all 4,025 fixture cases, bit for bit. A
  mismatch would be an argument inside §6's window; it's reported, not waived.
- `src/expm1/tests.rs`:
  - every unrounded result within its bound, on both sides of `2^−5`;
  - each fast path against its accurate path on 2^19 arguments, with the pass
    rates above;
  - the stage subtraction budget, including the interval-test margin, against
    the independent 192-bit values;
  - both exponential stages against the accurate path on four fixed-seed
    samples of 2^18 arguments: negative, positive, and the cancellation range
    on either side of zero. Stage B declines 0, 9, 30 and 39 arguments,
    respectively (the ranges are stated in `src/expm1/tests.rs`);
  - the rounding test's constant.
- The extracted binary64 stage transcription against the Rust stage result,
  including the screen edges and arbitrary encodings, in the internal cross-check.
- The extracted general fallback against Rust: input-derived indices and scales,
  both fast words, decision, Q128 value and rounded accurate result. The corpus
  covers every table index, both decisions, fixture inputs, cancellation edges
  and `k = −54` and `1024`, plus finite inputs outside the proved domain.
- The extracted small paths against Rust: both fast words, decision, Q128
  value and rounded accurate result, across all small-path binades, both
  decisions, the fixtures and the screen edges. The complete extracted entry
  also matches Rust for fixture inputs, boundary neighbours, NaN payloads,
  signed zeros, subnormals and arbitrary encodings.
- The determinism digest's `expm1` section and SIMD lane-equivalence tests on
  every supported backend. The proof changes leave runtime arithmetic and
  result bits unchanged.

**A defect this work found in the oracle,** fixed in
`generators/oracle/__init__.py`:
- At 128 bits, mpmath's interval `exp` returned a zero-width enclosure exactly
  on a binary64 midpoint, for an `x` whose `e^x − 1` lies `2^−142` beyond it.
  Both ends rounded alike, to the wrong neighbour.
- The oracle now requires agreement at two consecutive precisions.
- Every committed fixture regenerates unchanged under the fix. The `exp`, `ln`,
  `exp2` and `log2`/`log10` references were all correct.

## Batched evaluation

`elementary::expm1_slice` returns the scalar function's bits for every
element. With `simd`, the small-argument polynomial and both exponential
stages, including compensated subtraction, run in lanes. Screened and undecided arguments use the
scalar fallback. The operation sequence, FMA domain, backend equivalence
tests and same-host measurements are documented in [lanes.md](lanes.md).
The scalar proof coverage and numerical contract above are unchanged.
