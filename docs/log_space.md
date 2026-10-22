# `log_sum_exp` and `log_diff_exp`: sums and differences in log space

`morphiq_numerics::log_space::{log_sum_exp, log_sum_exp_pairs,
log_sum_exp_and_normalize, log_diff_exp}`
(`crates/morphiq-numerics/src/log_space/`) follow this derivation step for
step. They compute logarithms of sums and differences of exponentials without
leaving log space. Zero mass is
`−∞`, and positive mass too small to represent as a binary64 probability stays
finite.

The checked arbitrary-length [`normalize_log_weights`](log_normalize.md) API
reuses this reduction, with typed failures and a derived bound on normalized
log probabilities. It has a separate contract from the unchanged pair API.

This document is the contract and derivation the implementation follows. Each
numbered **decision** is a design choice open to review.

The bounds below compose the proved contracts of the operations used, as
[reduce.md](reduce.md)'s bounds do. `generators/log_space_bounds.py`
evaluates every composed expression, higher-order terms included, in exact
rational arithmetic, and checks that each claimed constant dominates it. That
certifies the composition's arithmetic, not that the code follows the
derivation. The reference fixtures check the code (§9). No Gappa certificate
covers the composed operation sequences. Here `u = 2^−53`, `RN` is
round-to-nearest-even, and `γ_k = k·u/(1 − k·u)`.

## Sources

- **[BHH]** P. Blanchard, D. J. Higham, N. J. Higham, "Accurately computing the
  log-sum-exp and softmax functions". Published in *IMA Journal of Numerical
  Analysis* 41(4), 2311–2330, 2021, doi:10.1093/imanum/draa038.
  - **Version read:** the authors' preprint, MIMS EPrint 2019.16, latest
    deposit (eprint 2765, 17 May 2020),
    <https://eprints.maths.manchester.ac.uk/2765/3/paper_nomarks.pdf>.
  - **SHA-256:** `8c079ad2fd71e1ec7c2cae149ac48dd2c079eda7900095deaad59f244f99ab0a`.
  - **Used:** Algorithm 4.1 (PDF p. 10), the shift and the `log1p`
    evaluation (§3).
- **[M]** M. Mächler, "Accurately computing log(1 − exp(−|a|)), assessed by
  the Rmpfr package", 2012.
  - **Version read:** `log1mexp-note.pdf` as shipped in CRAN Rmpfr 1.1-3,
    <https://cran.r-project.org/web/packages/Rmpfr/vignettes/log1mexp-note.pdf>.
  - **SHA-256:** `d13a037ef80613aa993a7128c4924083990b2e4aa3cdca4f6155c9c89ec9dfb9`.
  - **Used:** PDF p. 5, the cutoff `a₀ = log 2`. `log(1 − e^d)` is computed as
    `log(−expm1(d))` for `d > −log 2` and as `log1p(−e^d)` otherwise (§5).
    Only the mathematics is used. The package's R and C source is GPL and is
    not consulted.
- **[ORO]** T. Ogita, S. M. Rump, S. Oishi, "Accurate sum and dot product",
  *SIAM J. Sci. Comput.* 26(6), 1955–1988, 2005, doi:10.1137/030601818.
  - **Version read:** the author-hosted copy marked as published.
  - **SHA-256:** `56e897ffce0a843ea531769d50b8466241ae4f01094b0ddf83d8fff74255cfcc`.
  - **Used:** Sum2, Algorithm 4.4, run in streaming form, with its bound in
    Proposition 4.5 (§3).
- **[exp]**, **[expm1]**, **[ln]**: `morphiq-numerics`' own contracts at the
  pinned revision. `exp` and `ln` are correctly rounded, subnormal results
  included. `expm1` is within `(1/2 + 2^−65)` ulp and `ln_1p` within
  `(1/2 + 2^−70)` ulp.
- **[DW]**: `morphiq-numerics`' error-free transforms. `two_sum` is exact when
  both operands are at most `2^1020` in magnitude.

Each version read is identified above by its URL and SHA-256.

## 1. Specification

### `log_sum_exp(x: &[f64]) -> f64`

This computes `y = ln Σᵢ e^(xᵢ)`.

| Input | Result | Why |
|---|---|---|
| any element NaN | the first NaN | undefined; keeps the payload, as `ln` does |
| no NaN, any `+∞` | `+∞` | the sum is infinite |
| empty, or every element `−∞` | `−∞` | zero mass: `ln 0` |
| exactly one finite element `x_j`, all others `−∞` | `x_j`, exactly, `−0` included | `ln e^(x_j)` |
| otherwise | within the bound of §4 | §3 |

`−∞` elements are zero mass and contribute nothing. A finite element is never
treated as zero mass, however small `e^(xᵢ)` would be in binary64.
`log_sum_exp(&[-800.0])` is `−800`, not `−∞`.

The result never overflows. It is at most `max(x) + ln n`, and for
`max(x) ≤ f64::MAX` that rounds to at most `f64::MAX`, because
`ln n ≪ ulp(f64::MAX)/2`.

### `log_sum_exp_pairs<const N: usize>(x: &[[f64; 2]; N]) -> [f64; N]`

Element `i` of the result is `log_sum_exp(&x[i])`, bit for bit, on every
target and with or without the `simd` feature. It adds no claim of its own:
each element inherits `log_sum_exp`'s table above and its bound. It exists so
that the independent pairs of a two-state recursion's step can share SIMD
lanes (decision 7). Its working storage is a few `[f64; N]` arrays on the
stack, so `N` is meant to be small.

### `log_sum_exp_and_normalize<const N: usize>(x: &[[f64; 2]; N]) -> [(f64, Option<[f64; 2]>); N]`

For each pair `x`, this returns `log_sum_exp(&x)`, bit for bit, together
with `x` divided by its own sum, relative to its larger entry:

```text
hi = 1 if x[1] > x[0], else 0;   lo = 1 − hi
d = RN(x[lo] − x[hi]);   p[hi] = −RN(ln_1p(RN(exp(d))));   p[lo] = RN(d + p[hi])
```

The pair is `None` when `x[hi] = −∞`, which means no entry has mass.
- **Finite entries.** Then `d ≤ 0`, `ln_1p(e^d) ≥ 0` and `p[lo] ≤ p[hi] ≤ 0`,
  so neither entry is positive.
- **`x[lo] = −∞`** gives `p[hi] = −0` and `p[lo] = −∞`.
- **A NaN entry** gives NaN entries, with an unspecified payload.

This record makes no error claim for the pair beyond those operations, each
of which is correctly rounded except `ln_1p` ([ln.md](ln.md)). A two-state
recursion needs both values at every step: the conditional likelihood and the
filtered probabilities. Computing them together shares one exponential, and
lets their two logarithms share lanes (decision 8).

### `log_diff_exp(a: f64, b: f64) -> f64`

This computes `y = ln(e^a − e^b)`, defined for `a ≥ b`.

| Input | Result | Why |
|---|---|---|
| `a` or `b` NaN | that NaN (`a`'s first) | undefined |
| `b > a` | NaN | `e^a − e^b < 0`: outside the domain, as `ln` of a negative |
| `a = b = +∞` | NaN | `∞ − ∞` |
| `a = b`, finite or `−∞` | `−∞` | zero mass, exactly |
| `b = −∞ < a` | `a`, exactly | `ln(e^a − 0)` |
| `a = +∞ > b` | `+∞` | |
| otherwise | within the bound of §6 | §5 |

**Decision 1: out-of-domain arguments give NaN, not a typed error.** This
matches the crate's IEEE 754 convention (`ln` of a negative number is NaN). It
also keeps the signature a plain `f64` function that callers in log-space
recursions can compose. The contract states the NaN; it is never silent.
Callers that must not see NaN check `b ≤ a` first. An engine using it treats
that as an invariant of its recursion.

## 2. Accuracy target

**Decision 2: a proved error bound, not correct rounding.** Correct rounding
needs worst-case results, or an accurate path proved sufficient against them.
No published worst cases exist for these multi-argument functions. What a
log-likelihood accumulation needs is a stated bound. The results are still
identical on every target, because every step is a fixed sequence of correctly
rounded or exact operations. Correct rounding could be added later as an
accurate path, a Ziv rounding test over `Q128`, without changing this contract
except to tighten it.

Both functions return `ŷ = RN(m + L̂)`. Here `m` is an argument, carried
exactly, and `L̂` approximates a logarithm `L` of modest size. The bounds take
the form

```text
|ŷ − y| ≤ u·|y| + β·u·|L| + η
```

- `u·|y|` is the final rounding;
- `β·u·|L|` is the accumulated error of the logarithm term, with `β` a small
  constant;
- `η` is an absolute underflow term, at most a few multiples of `2^−1074`.

When `m` and `L` cancel, so that `y ≈ 0`, the bound is absolute rather than
relative. The inputs determine `y` only to that absolute accuracy, and an
absolute bound is what summing log-likelihoods needs.

## 3. `log_sum_exp`: algorithm (after [BHH])

1. Scan for NaN, `+∞` and finite elements (§1). Let `m = max(x)` over the
   finite elements, and let `j` be the first index attaining it.
2. For every other finite element `i ≠ j`, in index order, form
   `dᵢ = xᵢ − m ≤ 0` exactly as a pair `(dhᵢ, dlᵢ)` with `dhᵢ + dlᵢ = xᵢ − m`
   (decision 3).
3. Each term is `eᵢ = e^(dᵢ) = e^(dhᵢ)·e^(dlᵢ)`. Compute `ehᵢ = exp(dhᵢ)` and
   `pᵢ = RN(ehᵢ·dlᵢ)`, and pass both `ehᵢ` and `pᵢ` as summands.
4. Sum every summand with Sum2 [ORO] in streaming form: a running `two_sum`
   and a compensation accumulator, in a fixed order. The result is
   `t̂ ≈ t = Σ_{i≠j} eᵢ`.
5. If `t̂ = 0`, return `m` exactly. Otherwise `L̂ = ln_1p(t̂)` and the result is
   `ŷ = RN(m + L̂)`.

Step 5 evaluates `ln(1 + t)` without forming `1 + t`, which is [BHH]'s point:
`t ∈ [0, n − 1]` and `L = ln(1 + t) ∈ [0, ln n]`.

**Decision 3: an exact reduction.** `xᵢ − m` rounded to binary64 has relative
error `u`. Exponentiated, that becomes relative error `|dᵢ|·u` in the term,
which is up to about `745u`. The pair `(dh, dl)` keeps the reduction exact,
and `pᵢ` carries `dl` to first order, since `e^(dl) = 1 + dl + r` with
`|r| ≤ dl²` for `|dl| < 1`.

The pair is `two_sum(xᵢ, −m)` for every term. `two_sum` is proved exact for
operands up to `2^1020`. When either operand exceeds that, one of two cases
holds, and the pair is still exact wherever it is used:
- **`xᵢ ≥ m − 746`.** Then both operands exceed `2^1019`, have the same sign,
  and lie within a factor 2 of each other. By Sterbenz's lemma `s = xᵢ − m`
  is exact. `two_sum`'s remaining operations then compute `s + m = xᵢ` and
  `s − xᵢ = −m`, both exact, and it returns `(xᵢ − m, 0)` without overflow.
- **`xᵢ < m − 746`.** Then `dh = RN(xᵢ − m) ≤ −746`, or `−∞` if the
  subtraction overflows. `exp(dh)` is `+0`, and the term is skipped before
  `dl`, which may then be NaN, is used. The dropped mass is below `2^−1075`
  and lies inside `η`. Any term with `exp(dh) = 0` is skipped the same way.

**Decision 4: streaming Sum2, not `reduce::sum2`.** `reduce::sum2` takes a
slice, and this function is `no_std` with no allocation. The streaming form
performs the operations of [ORO] Algorithm 4.4 in the same order, so
Proposition 4.5's bound applies unchanged. The summands are bounded by
`n ≤ 2^1019`, which keeps every `two_sum` in its domain.

**Decision 5: summation order is index order, skipping `j`.** The result is
deterministic for a given slice. A permutation of the slice changes it by at
most the bound, not necessarily by zero.

**Decision 7: lane evaluation returns the same bits.** With the `simd`
feature, the exponentials of step 3, and `log_sum_exp_pairs`' `ln_1p`s of
step 5, are evaluated by `exp_slice` and `ln_1p_slice`, which return `exp`'s
and `ln_1p`'s bits on every backend ([lanes.md](lanes.md) §1). Nothing else
changes:
- **`log_sum_exp`** reduces the other finite terms in index order, as step 2
  does, into chunks of 32 pairs `(dhᵢ, dlᵢ)`. It evaluates each chunk's
  `exp(dhᵢ)` together, and then passes every term to Sum2 in index order,
  skipping each `ehᵢ = 0` before its `dlᵢ` is used, as decision 3 does. Every
  summand, and the order in which it is added, is step 4's, so `t̂` and the
  result are the same bits. A slice of at most two elements has at most one
  other term, which gains nothing from lanes, so it uses scalar arithmetic;
  a pair takes the specialization in decision 9.
- **`log_sum_exp_pairs`** performs steps 1 and 2 per pair, then evaluates
  every pair's `exp(dh)` together, forms each pair's `t̂` by step 4, and
  evaluates every `ln_1p(t̂)` together. A pair without a second finite term
  carries `dh = −∞`, whose exponential is `+0`, so its `t̂` is 0 and step 5
  returns `m`, as `log_sum_exp` does. A pair decided by step 1 (a NaN, `+∞`
  or no finite element) keeps step 1's result, and its lane values are
  discarded.

**Decision 8: one exponential for a log-sum and its normalized pair.** For
a pair, `log_sum_exp`'s reduction is `(dh, dl) = two_sum(x[lo], −x[hi])`
whenever step 1 finds a finite maximum. In that case its `j` is `hi`: both
pick the second entry only when it is strictly larger. `two_sum`'s leading
word is `RN(x[lo] + (−x[hi]))`, which IEEE 754 defines as `RN(x[lo] − x[hi])`.
That is the normalization's `d`, bit for bit. So `exp(dh)` is `exp(d)` and
is evaluated once.
- **Zero mass.** When `x[lo] = −∞`, `d = −∞`, so `exp(d) = +0` and the term
  is skipped (decision 3). That is the same `t̂ = 0` that step 2's skip of a
  `−∞` element gives.
- **The two logarithms,** `ln_1p(t̂)` and `ln_1p(e^d)`, are independent. The
  function passes every pair's two arguments to one `ln_1p_slice` call, and
  every pair's `d` to one `exp_slice` call.
- **Without `simd`** those calls loop the scalar functions. The shared
  exponential still saves one `exp` per pair.
- **Where step 1 decides the log-sum** (a NaN, `+∞`, or no finite entry), the
  log-sum is step 1's result. The pair still follows the formula above.

Without the `simd` feature `log_sum_exp` loops `exp` term by term and
`log_sum_exp_pairs` calls `log_sum_exp` on each pair.

**Decision 9: specialize scalar pairs without changing the arithmetic.** For
exactly two elements, `pair_sum` classifies the first and then the second
NaN before checking either infinity. It selects the second maximum only
when strictly larger, exactly as step 1 does. If the other entry is `−∞`,
the result is the maximum (including two `−∞` entries or a lone `−0`).
Otherwise there is precisely one retained term: `two_sum(v, −m)`, `exp(dh)`,
one call to the unchanged `Sum2Stream::add`, its unchanged `total`, and
step 5. In particular the `exp(dh) = 0` guard still precedes use of `dl`,
and the compensated sum is not replaced by an ordinary addition. This
removes general-slice scanning and index bookkeeping; it changes no
operation in the numerical reduction, output bit, bound, or public API.
The lane pair APIs already reduce one other entry directly, so their
arithmetic remains unchanged. Without SIMD, `log_sum_exp_pairs` inherits
this scalar specialization through its existing call to `log_sum_exp`.

## 4. `log_sum_exp`: error bound

Let `k = n_finite − 1` be the number of terms summed, giving `2k` summands.

**Terms.** `exp` is correctly rounded, so `ehᵢ = e^(dhᵢ)(1 + δ₁)` with
`|δ₁| ≤ u`. If the result is subnormal, the error is absolute and at most
`2^−1075`. `|dlᵢ| ≤ u·|dhᵢ| ≤ 746u < 2^−43`. Then `pᵢ` adds a rounding of at
most `u·|ehᵢ·dlᵢ| ≤ 2^−43·u·ehᵢ`, and the truncated `r` is below `2^−86·ehᵢ`.
Each term is therefore exact to a relative `u(1 + 2^−30)`, plus at most
`2·2^−1075` absolute from the two possibly subnormal operations.

**Sum.** By [ORO] Proposition 4.5, with all summands but the tiny `pᵢ`
non-negative, `S ≤ s·(1 + 2^−42)`, so
`|t̂ − Σ(ehᵢ + pᵢ)| ≤ u·Σ(ehᵢ + pᵢ) + γ²_{2k−1}·S`. Combining with the terms:

```text
|t̂ − t| ≤ δ_t·t + k·2^−1074,   δ_t = 2u + γ²_{2k−1}(1 + 2^−42) + O(u²).
```

For `n ≤ 2^20 + 1`, `γ²_{2k−1} ≤ 2^−64`, so `δ_t ≤ 2u(1 + 2^−10)`.

**Logarithm.** The derivative of `ln(1 + t)` is `1/(1 + t) ≤ 1`, and
`t/(1 + t) ≤ ln(1 + t) = L` for `t ≥ 0`. Hence the propagated error is at most
`δ_t(1 + 2δ_t)·L + k·2^−1074`. `ln_1p` adds `(1/2 + 2^−70)·ulp(L̂)`, which is
at most `(1 + 2^−69)·u·L̂`. `ln_1p(x) = x` exactly for `|x| < 2^−54`, so a
subnormal `t̂` adds nothing.

**Result.** `ŷ = RN(m + L̂)`. The addition is exact if its result is
subnormal, and otherwise has error at most `u·|m + L̂|`, where
`|m + L̂| ≤ |y| + |L̂ − L|`. Altogether:

```text
|ŷ − y| ≤ u·|y| + β·u·L + η,   β = 3 + 2^−8,   η = (2k + 1)·2^−1074,
```

valid for `n ≤ 2^20 + 1`, with `L = ln(1 + t) ≤ ln n`.
- The general formula keeps `γ²_{2k−1}`.
- `η` collects, per term, the two possibly subnormal operations (`2^−1074`)
  and the dropped mass (`2^−1075`), carried through the sum, plus `ln_1p`'s
  subnormal half-ulp.
- The exact-rational check gives `β ≤ 3.00049` at `n = 2^20 + 1` (`3.00000000006`
  at `n = 2`) and `η ≤ (1.5k + 0.5)·2^−1074 (1 + 2^−51)`.

## 5. `log_diff_exp`: algorithm (after [M])

Past the special cases of §1, `−∞ < b < a < +∞`. Form `d = b − a < 0` as
`(dh, dl) = two_sum(b, −a)`. By decision 3's argument, applied to `(b, a)`,
it is exact wherever it is used. The result is
`ŷ = RN(a + L̂)`, where `L̂ ≈ L = ln(1 − e^d) < 0`. Let `T = RN(−ln 2)`.

**Region A, `dh > T`: near-cancellation.** Here `1 − e^d ≤ 1/2·(1 + O(u))`,
so `|L| ≥ ln 2·(1 − O(u))`.

- `q̂ = −expm1(dh)`, with `q̂ ∈ (0, 1/2)`, and `L̂ = RN(ln(q̂))`.

**Decision 7: region A drops `dl`.** Write `z = 1 − e^(dh+dl) = q − g`, with
`q = 1 − e^(dh)` and `g = (1 − q)(e^(dl) − 1)`. Dropping `dl` errs by
`|ln(1 − g/q)|`, and

```text
|g/q| ≤ u(1 + u)·(1 − q)·ln(1/(1 − q))/q ≤ u(1 + u)·ln(1/q),
```

using `|dl| ≤ u·|dh|` and `|dh| = ln(1/(1 − q))`. The second inequality is
`(1 − q)·ln(1/(1 − q)) ≤ q·ln(1/q)` on `(0, 1/2]`. Their difference,
`r(q) = (1 − q)·ln(1 − q) − q·ln q`, is concave
(`r'' = 1/(1 − q) − 1/q < 0`) with `r(0) = r(1/2) = 0`, so `r ≥ 0`. Dropping
`dl` therefore costs at most about `u·|L|`. A correction term would cost a
rounding of the same size in the extra addition, so it gains nothing, and the
bound is the same with or without it.

**Region B, `dh ≤ T`: no cancellation.**

- `eh = exp(dh)` and `ŵ = RN(eh + RN(eh·dl))`, which approximates
  `w = e^d ∈ (0, 1/2·(1 + O(u))]`.
- `L̂ = ln_1p(−ŵ)`, with argument in `[−1/2·(1 + O(u)), 0)`.

If `exp(dh) = 0` (`d < −745`), the result is `a`, and `dl`, which may be NaN
after an overflow, is not used. The dropped mass is below `2^−1075`.

**Decision 6: the region boundary is `T = RN(−ln 2)`, as in [M].** The bound
below holds on both sides, so the boundary's own rounding needs no further
analysis. Any `T` in about `[−0.8, −0.6]` would do, with slightly different
constants.

## 6. `log_diff_exp`: error bound

**Region A.**
- `q̂` has relative error at most `(1 + 2^−64)·u` from `expm1`. In `L` that is
  an absolute error of the same size.
- Dropping `dl` adds `|ln(1 − g/q)| ≤ κ·ln(1/q)`, where
  `κ = u(1 + u)/(1 − 746u(1 + u))` (decision 7).
- `RN(ln q̂)` adds `u·ln(1/q̂)`.
- Since `|L| ≥ (1 − κ)·ln(1/q)` and `ln(1/q) > ln 2`, the relative error in
  `L` is at most `(1 + 1/ln 2 + 1)·u + O(u²) ≈ 3.443u`.

**Region B.**
- `ŵ = w(1 + δ_w)`, with `|δ_w| ≤ 2u(1 + 2^−40)`: one rounding from `exp`,
  one from the sum, and `O(2^−43·u)` from `dl`.
- The conditioning of `ln(1 − w)` for `w ∈ (0, 1/2]` is
  `w/((1 − w)·|ln(1 − w)|)`. That increases from 1 as `w → 0` to `1/ln 2` at
  `w = 1/2`, plus `O(u)` past it, giving at most `(2/ln 2)·u·|L| + O(u²)`.
- `ln_1p` adds `(1 + 2^−69)·u·|L̂|`.
- The total relative error is at most `(1 + 2/ln 2)·u + O(u²) ≈ 3.886u`.

**Result.** With the final `RN(a + L̂)`, as in §4:

```text
|ŷ − y| ≤ u·|y| + β·u·|L| + η,   β = 3.89,   η = 5·2^−1074,
```

The exact-rational check gives relative errors in `L̂` of `3.4427u`
(region A) and `3.8854u` (region B), and
so `β ≤ 3.88540` and `η ≤ 4.5·2^−1074 (1 + 2^−51)`. Region B's conditioning
bound uses that `w/((1 − w)·|ln(1 − w)|)` is `(e^x − 1)/x` in
`x = −ln(1 − w)`, which increases in `x`.

## 7. Zero mass and underflow

These implement the requirements recorded on #44:

- **`−∞` is exact zero mass** in both functions. It is never an error.
- **All-zero sums** give `−∞` exactly: an empty slice, or every element `−∞`.
- **`log_diff_exp(a, a) = −∞`** exactly, for finite `a` and for `a = −∞`.
- **Invalid subtraction** (`b > a`), and `a = b = +∞`, give NaN, as stated in
  §1.
- **Underflow is not zero mass.** A finite input is never converted to `−∞`.
  Mass smaller than the binary64 range relative to the largest term is dropped
  only as an absolute error inside `η`. The finite log-space result keeps the
  dominant term exactly, for example `log_sum_exp(&[-800.0]) = −800`.
- **Near the underflow threshold**, `exp`'s subnormal results carry absolute,
  not relative, error. The `η` terms account for it.

## 8. Cost

- **`log_sum_exp`:** for lengths other than two, one pass to classify and find `m`. A second pass costs,
  per element, one `two_sum`, one `exp`, one multiplication and a `two_sum`
  step of Sum2. One `ln_1p` follows. That is `O(n)` time with no allocation.
  For `n = 2` it classifies the two entries directly, then performs one
  `exp`, one `ln_1p` and the same compensated operations (decision 9).
- **`log_sum_exp_pairs`:** per pair, `log_sum_exp`'s work for `n = 2`. With
  the `simd` feature the `N` exponentials and the `N` logarithms each run in
  lanes. No allocation; its arrays are on the stack. `log_sum_exp`'s
  chunks are too, three arrays of 32.
- **`log_sum_exp_and_normalize`:** per pair, one `two_sum`, one `exp`, two
  `ln_1p` and a few exact operations, against two `exp` and two `ln_1p` for
  `log_sum_exp` and a separate normalization. No allocation.
- **`log_diff_exp`:** one `two_sum`, then one `expm1` and one `ln`
  (region A), or one `exp` and one `ln_1p` (region B). Constant time.

The accurate-path rates of the underlying `exp`, `expm1`, `ln` and `ln_1p`
dominate the cost.

**Local measurement** (`cargo test --release -p morphiq-numerics measure_cost
-- --ignored --nocapture`, with `--features simd,std` for the second column;
not a gate). The conditions:
- Apple M1 Pro, NEON, release build, Rust 1.97.1;
- median of three runs, alternating between builds;
- one-minute load average 2.8 to 2.9 when each run started, with no other
  build or benchmark running.

| Function | Inputs | Without `simd` | With `simd` |
| --- | --- | --- | --- |
| `log_sum_exp` | `n = 2`, operands in `[−20, 20]` | 64 ns per call | 63 ns per call |
| `log_sum_exp` | `n = 1000`, elements in `[−50, 20]` | 26 ns per element | 13 ns per element |
| `log_sum_exp_pairs` | `N = 2`, the same pairs as `n = 2` | 63 ns per pair | 44 ns per pair |
| `log_sum_exp_and_normalize` | `N = 1`, the same pairs | 92 ns per pair | 70 ns per pair |
| `log_sum_exp` and a separate normalization | the same pairs | 115 ns per pair | 116 ns per pair |
| `log_diff_exp` | `a` in `[−20, 20]`, `b = a − [0, 30]` | 57 ns | 58 ns |

Without `simd`, the shared exponential alone makes `log_sum_exp_and_normalize`
1.25× faster than the separate pair. With `simd`, pairing its two `ln_1p`s
makes it 1.66× faster.

On AVX2 and AVX-512F, a batch of two pairs is shorter than one lane chunk.
The backend cascade ([lanes.md](lanes.md) §1) runs it on SSE2's two lanes.
On one i9-10920X with `simd`, `log_sum_exp_pairs` takes 34.7 ns per pair at
`N = 2` against 37.1 ns for `log_sum_exp` at `n = 2`, and the fused
`log_sum_exp_and_normalize` 48.9 ns against 64.8 ns for the separate pair
([measurements](../crates/reference/measurements/lanes-x86-i9-10920x/README.md#compositions)). The run without `simd` was not
timed there.

**Scalar pair specialization, native x86-64.** `bench-log-space` reuses the
fixed-seed input and timing approach of `bench-batched`, retaining every
sample as CSV. Build the same harness at both revisions and alternate fresh
processes. `dependent` feeds the previous output's low bit into the next
input selection; the reported latency includes indexing and black-box
overhead. `independent` loops independent scalar calls. Neither batches
calls into SIMD lanes. Reproduce with:

```sh
cargo build --release --locked -p morphiq-numerics-reference --features simd,std --bin bench-log-space
target/release/bench-log-space --calls 100000 --rounds 1
# Repeat without --features simd,std for the scalar-only build.
```

Measured on a shared Intel i9-10920X (12 cores / 24 threads), Linux x86-64,
Rust 1.97.1 release, default target features, with seven alternating AB/BA
pairs of fresh processes per feature configuration. Each case has 4,096
untimed warmup calls and 100,000 timed calls. No concurrent build or
benchmark was started by this experiment; one-minute host load ranged
from 5.80 to 6.22. Baseline is `1818ab9` plus the identical harness;
candidate adds decision 9. These are local measurements, not CI gates.

| Dependent calls, ns/call (median) | Baseline, `simd,std` | Pair specialization, `simd,std` | Baseline, no features | Pair specialization, no features |
| --- | ---: | ---: | ---: | ---: |
| Near-equal terms | 56.79 | 52.94 | 55.95 | 52.66 |
| Separated terms | 52.29 | 50.27 | 50.97 | 48.40 |
| Cancellation near zero | 56.63 | 49.98 | 55.83 | 50.29 |
| Nonzero subtraction tail | 56.78 | 52.88 | 55.66 | 53.04 |
| Exponential fallback, subnormal mass | 306.82 | 300.16 | 309.38 | 301.79 |
| Underflow to zero mass | 11.71 | 7.02 | 9.26 | 6.99 |
| Eight-term control | 134.97 | 134.30 | 134.33 | 137.56 |

The ordinary pair distributions improve by about 4–12% with `simd,std`;
the fallback-heavy case improves much less. The scalar-only eight-term
control is 2.4% slower in this sample, while its independent loop is 0.4%
slower. This does not establish a gain for arbitrary slice lengths or
other hosts. [All samples](evidence/log-space-two-term-x86.csv), including
independent loops, and [run metadata](evidence/log-space-two-term-x86.json)
retain the ranges, process CPU times, load, compiler and executable hashes.
Process CPU covers input construction, warmup and formatting as well as
timed loops; it is distinct from the per-loop wall measurements above.

## 9. Evidence

1. **Reference fixtures.** `generators/log_space_reference.py` writes
   `crates/reference/fixtures/log_space.json`. It holds 50 exact cases, the
   special values of §1 with NaN payloads where §1 specifies them, and 1,102
   bounded cases.
   - **Allowed interval.** For each bounded case, a rigorous mpmath interval
     enclosure of `y` gives the bound `B` of §4 or §6 in exact rationals,
     using the constants `generators/log_space_bounds.py` checks.
     `[y − B, y + B]` is rounded inward to binary64 endpoints `lo ≤ hi`.
   - **The check.** An implementation passes when `lo ≤ ŷ ≤ hi`. That is an
     exact comparison and sound: every accepted `ŷ` is within the bound. It
     accepts every binary64 within the bound, except where `y ± B` lies within
     the enclosure width of a binary64 number, where that number is excluded.
   - **Coverage.**
     - `−∞` mixed with finite elements;
     - `t̂ = 0`, and terms whose `e^(dᵢ)` is subnormal or underflows to zero;
     - cancellation, where `m ≈ −L` and `y ≈ 0`;
     - operands beyond `2^1020`;
     - both `log_diff_exp` regions, and the boundary at `T` and its
       neighbours;
     - `a` and `b` one ulp apart;
     - 1,000 equal elements, and 1,000 elements near `0.1`, where
       uncompensated summation drifts by about `60u`;
     - two cancellation families with `y ≈ 0`, 30 cases each:
       `e^m + e^b = 1` and `e^a − e^b = 1`. These make the two_sum tail
       `dl` visible;
     - a subtraction that overflows to `−∞`;
     - 1,000 SplitMix64 cases across scales from 1 to `10^300`.
   - **Tightness.** Where `L ≪ ulp(y)`, the bound admits only `RN(y)`: that is
     516 of the 1,102 cases.
   - **Validation.** An independent recomputation at 4,000 bits, with plain
     mpmath and not the interval code, confirmed every interval sound and
     every `RN(y)` correct.
2. **Tests.** `crates/morphiq-numerics/src/log_space/tests.rs` checks every
   exact case bit for bit, and every bounded case by `lo ≤ ŷ ≤ hi`. It
   reports how far the results that are not correctly rounded are from
   `RN(y)`:

   | Function | Bounded cases | Correctly rounded | 1 ulp | 2–3 ulp | 4–15 ulp | ≥ 16 ulp |
   | --- | --- | --- | --- | --- | --- | --- |
   | `log_sum_exp` | 651 | 580 | 28 | 11 | 1 | 31 |
   | `log_diff_exp` | 451 | 370 | 43 | 4 | 3 | 31 |

   Every result is within the bound. Distances of more than one ulp occur
   only under cancellation between `m` and `L`, where the bound is absolute
   and spans many ulps of a small `y`. The `≥ 16` column counts the
   cancellation families and the near-zero cases.
3. **Bound arithmetic.** `generators/log_space_bounds.py --check` verifies the
   composed bounds of §4 and §6 in exact rational arithmetic. It runs with
   the generators (`scripts/check_generators.sh`).
4. **Determinism.** All four functions are in the determinism digest
   ([determinism.md](determinism.md)), which every CI target computes with
   and without the `simd` feature. Its `log_sum_exp` section includes slices
   of 9 to 100 elements, so terms fill and cross the chunks of decision 7.
5. **Lane evaluation** (decision 7; `log_space/tests.rs`, run on AVX-512F
   under Intel's emulator as well as on the test hosts, [lanes.md](lanes.md)
   §6):
   - `log_sum_exp` equals §3's steps with a scalar `exp` per term, bit for
     bit, on every fixture input and on slices of every length from 0 to 100
     at four gap scales, with zero mass, ties, underflowing terms, NaN and
     `+∞` placed around the chunk boundaries, and a slice of 10,000;
   - `log_sum_exp_pairs` equals `log_sum_exp` on each pair, bit for bit, in
     batches of 1, 2, 3, 8 and 17: every pairing of twelve special values,
     the fixture's pairs, and 40,000 random pairs.

   - `log_sum_exp_and_normalize` equals `log_sum_exp` and the stated
     normalization, written out with one scalar `exp` and `ln_1p` each, on
     the same pairs and batch sizes. Entries are compared bit for bit,
     except that a NaN entry need only be NaN.

   Sum2's result rarely depends on the order of its summands: reversing each
   chunk changed no result on 240,000 random slices. So these tests cannot
   detect an order change; decision 7's same order is a property of the code,
   which adds each chunk's terms in index order.
6. **Mutation.** cargo-mutants 27.1.0 over `log_space/mod.rs`, run once with
   the `simd` feature and once without, generates 112 mutants. Each run
   compiles only its own `terms` and `log_sum_exp_pairs` path. 109 are
   caught by the run that compiles them. The other three are equivalent:
   each changes only a choice this contract leaves free, so no test anchored
   outside the implementation can tell them apart.
   - `dh > T` against `dh ≥ T` is the region boundary (decision 6), where
     both regions meet the bound.
   - Inverting the lane `terms`' test for slices of at most two elements
     only exchanges which of two evaluations runs, and both return the same
     bits (decision 7).
   - `x[1] > x[0]` against `≥` in `log_sum_exp_and_normalize` changes `hi`
     only for equal entries. There `d = 0` either way, and both entries are
     `−ln_1p(1)`.

## 10. Out of scope here

- **Signed sums of exponentially scaled terms**, `Σ sᵢ·e^(ℓᵢ)` carried as a
  sign and a log-magnitude. They are #104, outside release 0.1.
- **Correct rounding** (decision 2).
