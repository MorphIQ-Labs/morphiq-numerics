# `log_sum_exp` and `log_diff_exp`: sums and differences in log space

`morphiq_numerics::log_space::{log_sum_exp, log_diff_exp}`
(`crates/morphiq-numerics/src/log_space/`) follow this derivation step for
step. They compute logarithms of sums and differences of exponentials without
leaving log space. Zero mass is
`−∞`, and positive mass too small to represent as a binary64 probability stays
finite.

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

- **`log_sum_exp`:** one pass to classify and find `m`. A second pass costs,
  per element, one `two_sum`, one `exp`, one multiplication and a `two_sum`
  step of Sum2. One `ln_1p` follows. That is `O(n)` time with no allocation.
  For `n = 2` it is one `exp`, one `ln_1p` and a handful of exact
  operations.
- **`log_diff_exp`:** one `two_sum`, then one `expm1` and one `ln`
  (region A), or one `exp` and one `ln_1p` (region B). Constant time.

The accurate-path rates of the underlying `exp`, `expm1`, `ln` and `ln_1p`
dominate the cost.

**Local measurement** (Apple M1 Pro, release build, Rust 1.97.1;
`cargo test --release -p morphiq-numerics measure_cost -- --ignored
--nocapture`; one run, not a gate):

| Function | Inputs | Time per call |
| --- | --- | --- |
| `log_sum_exp` | `n = 2`, operands in `[−20, 20]` | 64 ns |
| `log_diff_exp` | `a` in `[−20, 20]`, `b = a − [0, 30]` | 56 ns |

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
4. **Determinism.** Both functions are in the determinism digest
   ([determinism.md](determinism.md)).
5. **Mutation.** cargo-mutants 27.1.0 over `log_space/mod.rs` catches 43 of
   45 mutants. The other two are equivalent: each changes only a choice this
   contract leaves free, so no test anchored outside the implementation can
   tell them apart.
   - `v > m` against `v ≥ m` picks the first or the last index of a tied
     maximum (decision 5). The other tied element contributes `e^0 = 1`
     either way.
   - `dh > T` against `dh ≥ T` is the region boundary (decision 6), where
     both regions meet the bound.

## 10. Out of scope here

- **Signed sums of exponentially scaled terms**, `Σ sᵢ·e^(ℓᵢ)` carried as a
  sign and a log-magnitude. They are #104, outside release 0.1.
- **Correct rounding** (decision 2).
