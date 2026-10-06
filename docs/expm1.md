# `expm1`: `e^x − 1` without cancellation

`morphiq_numerics::elementary::expm1` (`crates/morphiq-numerics/src/expm1/`)
follows this derivation. Near zero it evaluates its own polynomial and series,
because `e^x − 1` cancels there. Elsewhere it uses [exp.md](exp.md)'s reduction
and paths, and subtracts before scaling. Every bound is certified (§7).

`expm1(x)` is `e^x − 1`:
- correctly rounded whenever its rounding test decides;
- otherwise within `(1/2 + 2^−65)` ulp;
- `expm1(x) = x` for `|x| < 2^−54`.

## Sources

- **[exp]** [exp.md](exp.md): the reduction `x = k·ln 2 + j/128·ln 2 + r`, its
  fast path and its `Q128` accurate path.
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

## 4. Small arguments, accurate path

`(e^x − 1)/x = 1 + x/2·(1 + x/3·(1 + …))` in `Q128`:
- `H_(d+2) = 1` and `H_m = 1 + (x·(1/m))·H_(m+1)`, for `m = d + 1` down to `2`;
- then `x·H_2`.

**The degree** `d = 15` is the least whose truncation, at most
`A^(d+1)/(d+2)!` over `(e^x − 1)/x ≥ 1 − A/2`, is at most `2^−125`
(*generated*: `generators/expm1_constants.py`, with `1/m` as `Q128` constants).

Each level's error is bounded from the previous one (*certified*:
`formal/expm1/accurate_level_02.g` to `_16.g`). The result is within `2^−123`
of `e^x − 1` (*certified*: `formal/expm1/accurate_small.g`, proves `2^−125.6`).

## 5. Other arguments

**Fast:** [exp]'s reduction and fast path give `Y ≈ 2^(j/128)·e^R`, within
`2^−69` (`formal/exp/fast.g`), and `e^x − 1 = 2^k·(2^(j/128)·e^R − 2^−k)`.

**Decision 2: subtract `2^−k` before scaling.**
- `M = Y.add_f64(−2^−k)` keeps every word of size about 1, inside the
  double-word bounds' domain, even where `e^x` nears overflow.
- `2^−k` is exact: `−54 ≤ k ≤ 1024`, so `2^−k` is at worst a subnormal power of
  two.
- Scaling `M`'s words by `2^k` is exact for `k ≥ −54`, since neither word
  underflows.

The relative error against `e^x − 1` is `kq·eY·(1 + ea) + ea`, with
`kq = e^x/(e^x − 1)`:
- `|kq|` is largest at `|x| = 2^−5`, below `32.51`, enclosed in interval
  arithmetic. It decreases on both sides as `|x|` grows.
- The total is below `2^−62` (*certified*: `formal/expm1/fast_general.g`,
  proves `2^−63.96`).

**Accurate:** [exp]'s accurate `e^x`, within `2^−123.9`, less 1 in `Q128`. The
addition errs by at most `2^−126·max(e^x, 1)`, and
`max(e^x, 1)/|e^x − 1| ≤ |kq| + 1`. The result is within `2^−118` of `e^x − 1`
(*certified*: `formal/expm1/accurate_general.g`, proves `2^−118.55`).

## 6. Rounding test and bound

**Decision 3: `ε₁ = 2^−62`.** That's [ln] §5's test, with
`EPS = 2^−62·(1 + 2^−50)`. Both fast paths are certified within it. The test's
proof needs `e^x − 1` not to be a breakpoint, and it is transcendental for every
nonzero rational `x` (Lindemann).

At that `ε₁` the test sends about one argument in 2^8.5 to the accurate path
(measured: `2^−8.5` small, `2^−8.4` otherwise; the analytic rate is at most
`2^−8`).

**The bound:**
- When the test passes, the result is `RN(e^x − 1)`.
- Otherwise the accurate result is within `2^−118` relatively, so the error is
  at most `(1/2 + 2^−65)` ulp.
- It is correctly rounded unless `e^x − 1` lies within mantissa distance
  `2^−117` of a breakpoint. No published search excludes that.

## 7. Certificates, generators and tests

| Artifact | Establishes |
|---|---|
| `generators/expm1_poly.sollya` (Sollya 8.0) | `c3`–`c9` and their bound, with the remainder, in `generators/expm1_poly.out` |
| `generators/expm1_constants.py` | `src/expm1/tables.rs`: `c3`–`c9`, `1/m` in `Q128`, the series degree |
| `generators/expm1_certificates.py` | writes every certificate below; the ratio `kq` is enclosed with `mpmath.iv` |
| `formal/expm1/tail.g`, `p.g` | the small fast path: `2^−50`, then `2^−62.3` |
| `formal/expm1/accurate_level_*.g`, `accurate_small.g` | the small accurate path: `2^−123` |
| `formal/expm1/fast_general.g`, `accurate_general.g` | the other paths: `2^−62` and `2^−118` |
| `generators/expm1_reference.py` | the fixture: thresholds, special values, random arguments at every scale, and 1,200 values to 192 bits |

Every certificate's Coq proof is also built, with each rewriting hint proved, by the formal job ([exp.md](exp.md), gates).

The binding `formal/expm1/binding.sha256` covers this document, the Sollya
script and output, the constants, every certificate and the source.

**Checked by:**
- `crates/reference/tests/expm1.rs`: all 4,025 fixture cases, bit for bit. A
  mismatch would be an argument inside §6's window; it's reported, not waived.
- `src/expm1/tests.rs`:
  - every unrounded result within its bound, on both sides of `2^−5`;
  - each fast path against its accurate path on 2^19 arguments, with the pass
    rates above;
  - the rounding test's constant.
- The determinism digest's `expm1` section on every target.

**A defect this work found in the oracle,** fixed in
`generators/oracle/__init__.py`:
- At 128 bits, mpmath's interval `exp` returned a zero-width enclosure exactly
  on a binary64 midpoint, for an `x` whose `e^x − 1` lies `2^−142` beyond it.
  Both ends rounded alike, to the wrong neighbour.
- The oracle now requires agreement at two consecutive precisions.
- Every committed fixture regenerates unchanged under the fix. The `exp`, `ln`,
  `exp2` and `log2`/`log10` references were all correct.
