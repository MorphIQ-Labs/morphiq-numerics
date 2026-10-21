# `asinh`

`asinh(x) = sign(x)·ln(|x| + √(x² + 1))`, correctly rounded over binary64:
a certified fast path in double-word arithmetic, the shared rounding test, and
a `Q256` accurate path. The code is `crates/morphiq-numerics/src/asinh/`; the
constants are generated and every bound is a Gappa certificate in
`formal/asinh`.

## Status

| Item | State |
|---|---|
| Specification, special values and the `asinh x = x` threshold (§1) | done; threshold by oracle bisection |
| Fast path: series, `ln(x + √(x² + 1))`, large form (§3) | **certified** (Gappa): relative error below `2^-63` |
| Rounding test at `ε₁ = 2^-63` (§5) | sound given the fast bound, as [ln] §5 |
| Accurate path: two Newton steps for `sinh y = x` in `Q256` (§4) | **certified** (Gappa): relative error below `2^-216`, given the facts §4 lists |
| Correct rounding on `(0x1.7137449123ef6p−26, ∞)` (§5) | follows from the two bounds and [CM]'s list; the Rust is **not** machine-checked end to end |
| Coq re-proof of every certificate, each rewriting hint proved, axioms audited (§6) | done by the formal lane (`scripts/write_gappa_proofs.sh`, `check_formal.sh` step 5) |
| Coq transcription of the Rust and its comparison with it | not done |
| ARM NEON, SSE2, AVX2+FMA, AVX-512F lanes; `asinh_slice` | **done** (`asinh/lanes.rs`, [lanes.md](lanes.md)): bit-identical to `asinh` on every cascade over the fixture, thresholds, region edges and random encodings; run on NEON and on x86-64 SSE2 under Rosetta; AVX-512F is CI's SDE job |
| Mutation witnesses | not done |
| Same-host performance against the best alternatives | measured on NEON only: 1.01–1.66× over the scalar loop ([measurements](../crates/reference/measurements/asin-asinh-atan2-m1pro/README.md)); native x86 not measured |

## Sources

- **[CM]** CORE-MATH, `src/binary64/asinh/asinh.wc` at commit
  `0ce0cbc15935e24c656280e5a46c34e89f301b7a` (SHA-256
  `c5835d0d56244e3ce1455358225934c9c5360c2abb7de512680bc9d64ea29e30`, MIT): the
  inputs with at least 43 identical bits after the round bit on
  `0x1.7137449123ef6p-26 ≤ x < 2^1024`, found with BaCSeL. Used as test inputs
  and to size the accurate path (§2), never as code.
- **[M]** J.-M. Muller, *Elementary Functions*, 3rd ed., 2016.
- **[DW]** [double-word.md](double-word.md): the double-word operations' proved bounds.
- **[ln]** [ln.md](ln.md) §4 and §5: the double-word logarithm and the rounding test.
- **[sin_cos]** [sin_cos.md](sin_cos.md) §8: `Q256::recip`'s certified bound.

## 1. Specification

| Input | `asinh` |
|---|---|
| NaN | the NaN |
| `±0` | `±0` |
| `±∞` | `±∞` |
| `\|x\| ≤ 0x1.7137449123ef6p−26` | `x`, exactly (*generated*, below) |
| otherwise | §3–§5, odd in `x` |

**The `asinh x = x` threshold.** `asinh x = x − x³/6 + 3x⁵/40 − …` lies below `x`
by about `x³/6`, so `x` is the nearest binary64 while `x³/6` is below half the
gap toward zero. The oracle (`generators/asinh_reference.py`) bisects the least
argument whose `asinh` is not `x`: `0x1.7137449123ef7p−26`. It is the same
threshold as `sin` and `asin` share, and it is where [CM]'s list begins.

## 2. Accuracy needed

[CM]'s list is complete for the domain it covers, so no input outside it is
closer than `2^-43` ulp to a midpoint, and the hardest listed one, ranked here
at 400 bits over the whole list, is 62.03 bits from one
(`0x1.fd15daa6ce332p+731`). The accurate path's `2^-216` is far inside that.
`asinh x` is transcendental for `x ≠ 0`, so it is never a midpoint.

## 3. Fast path

For `a = |x| > 0x1.7137449123ef6p−26`, the result `Y` is a double-word.

- **`a < 2^-7`: the series.** `asinh a = a − a³·Q(a²)`, `Q` of degree 3 in `a²`
  (`generators/asinh_poly.sollya`: relative error `0x1.000002p-54`). The kernel
  evaluates `P = −Q` with the coefficients' signs, which is the same operations
  negated. `Y = a + RN(RN(a·a²)·P(a²))` by `DoubleWord::add_f64`. Certified:
  `series_tail.g` (the tail, `2^-51`) and `series_compose.g` (`2^-66.4`).
- **`2^-7 ≤ a < 2^28`: `ln(a + √(a² + 1))`.** `a²` is exact by `two_prod`;
  `u = 1 + a²` is a double-word; `s = √u` is `root = RN(√u_hi)` plus the Newton
  correction `RN(r/(2·root))`, `r = ((u_hi − root²_hi) − root²_lo) + u_lo`
  (`root.g`: `2^-100`); `v = a + s` is a double-word. Then
  `Y = ln(v_hi) + RN(v_lo/v_hi)`, with `ln(v_hi)` the double-word of `ln`'s fast
  path ([ln] §4, within `2^-64`). Certified: `log.g` (below `2^-63`).
- **`a ≥ 2^28`: `ln a + ln 2 + 1/(4a²)`.** `asinh a = ln 2a + t/4 − 3t²/32 + …`,
  `t = 1/a² ≤ 2^-56`, so the omitted terms are below `2^-114`. `ln a` is `ln`'s fast
  path, `ln 2` a double-word (`2^-109`), `1/(4a²)` is `RN(RN(¼/a)/a)`, which
  underflows harmlessly for the largest `a`. Certified: `large.g`.

Every operation is binary64, in the written order, on every target.

## 4. Accurate path

`y₀ = Y`. Two Newton steps for `sinh y = x`, `y ← y + (x − sinh y)/cosh y`, in
`Q256`.

- **The exponential.** `e^y = m·2^k`, `k = RN(y/ln 2)` in binary64,
  `r = y − k·ln 2` in `Q256` (`|r| ≤ 0.3467`), `m` the 45-term series
  `1 + r(1 + r/2(1 + r/3(…)))` with `Q256` constants (`EXP_STEPS`). Certified:
  `exp_level_01.g` … `exp_level_45.g` (each Horner level) and `exp.g`
  (the reduction's error, `2^-243.8`).
- **`sinh` and `cosh`** are `(e^y ∓ e^−y)/2` from `m` and `1/m`; the reciprocal
  scales its argument into `[1, 2)` first so `Q256::recip`'s binary64 start is
  finite for every `y` (`Q256::recip`: [sin_cos] §8, `2^-252.6`).
- **The steps.** The exact step lands at `y* + q`, `q = c₂(εy*)²/2`,
  `c₂ = sinh ξ/cosh y₀ ∈ [0, 1.001]`; the computed step adds the exponential's
  error (absolute), the reciprocal's and product's (relative to the
  correction) and the last sum's. `newton_1.g` and `newton_2.g` carry the two
  steps from `ε = 2^-63`; the result is within `2^-216.8` relatively.
- **Stated, not certified:** `c₂ ≤ 1.001` (the mean value theorem for `sinh`),
  `|ξ − y₀| ≤ 2^-52`, and the `Q256` operations' error model (truncated
  products within `2^-255`, sums within `2^-254` of the larger operand), as for
  `sin`/`cos`.

## 5. Rounding test and claims

`decide_with(Y, EPS)`, `EPS = 2^-63(1 + 2^-50)`, as [ln] §5: `Y_hi` is returned when
it is provably `RN` of every real within `2^-63` of `Y`. Otherwise the
accurate value is rounded once by `Q256::to_f64`.

- The fast bound is `2^-63` (`log.g`, `large.g`; the series `2^-66.4`).
- When the test passes, the result is `RN(asinh x)`.
- Otherwise the accurate value is within `2^-216` relatively, and the hardest
  input of the domain is `2^-62` ulp from a midpoint ([CM], §2), so the result
  is `RN(asinh x)`.

So `asinh` is correctly rounded on `(0x1.7137449123ef6p−26, ∞)` given [CM]'s list
is complete and the stated facts of §4 hold, and exactly `x` below.

## 6. Certificates, generators and tests

| Artifact | Establishes |
|---|---|
| `generators/asinh_poly.sollya` (Sollya 8.0) | the series polynomial and its bound, in `generators/asinh_poly.out` |
| `generators/asinh_constants.py` | `src/asinh/tables.rs`: the polynomial, `ln 2` as a double-word, `Q256` `ln 2` and the series' steps |
| `generators/asinh_certificates.py` | writes every certificate in `formal/asinh` (53) |
| `formal/asinh/*` (Gappa 1.4.1, at 400 bits) | §3's series, root, logarithm and large form; §4's exponential levels, reduction and two Newton steps |
| `generators/asinh_reference.py` | the fixture: the 40 hardest arguments of [CM], the threshold and its neighbours, special values, the regions' edges, random arguments |

The binding `formal/asinh/binding.sha256` covers this document, the Sollya script
and output, the generated tables, every certificate and the source `asinh/mod.rs`.

Tests:
- `crates/reference/tests/asinh.rs`: the fixture's cases, bit for bit.
- `src/asinh/tests.rs`: special values, oddness, the regions' boundaries,
  100,000 random arguments on which every fast-path decision equals the
  accurate path's result, and the accurate path against the fast value.
- The formal lane's Coq proof of each certificate (`check_formal.sh` step 5).
- A negative control was run by hand: tightening `root.g`'s claim makes Gappa
  exit non-zero. It is not a gate.
