# Absolute error contracts for log-space consumers

These bounds express the strong APIs' existing proved guarantees in
**natural-log units**. They include each primitive's final rounding, apply
to exact binary64 inputs, and hold elementwise for the matching `_slice`
APIs. Let `u = 2^−53`, `η = 2^−1075`, and a hat denote the returned value.
All budget expressions below use exact real arithmetic; evaluate them with
outward rounding when implementing a budget. In particular, `η` is not a
representable binary64 constant.

| API and domain | Exact real target `L` | Absolute error in log units |
|---|---|---|
| `ln(x)`, finite `x > 0` | `ln x` | `abs(L̂ − L) ≤ u·abs(L)` |
| `ln_1p(x)`, finite `x > −1` | `ln(1 + x)`, with exact `1 + x` | `abs(L̂ − L) ≤ (u + 2^−122)·abs(L) + η` |
| `log_norm_cdf(x)`, finite `x`, no result overflow | `ln(Φ(x))` | `abs(L̂ − L) ≤ (u + 2^−111)·abs(L) + η` |
| `expm1(x)`, finite nonzero `x`, no result overflow | `ln(abs(exp(x) − 1))` | `abs(ln(abs(expm1(x))) − L) ≤ ρ/(1 − ρ) < 2^−52`, where `ρ = u + 2^−117` |

`expm1` returns a linear value. Its row bounds the **exact log-magnitude
of that returned value**; a subsequent call to `ln` adds its own error.
The other three rows bound the returned logarithm directly. These are
derived bounds, not sampled maxima or new whole-domain correct-rounding
claims. The `fast` namespace has separate contracts in [fast.md](fast.md).

## Derivation and special cases

**`ln`:** [ln.md §1–§2](ln.md#1-specification) establishes correct rounding
and normal nonzero results, giving `u·abs(L)`. Since `abs(L) < 745`, the
largest result binade has spacing `2^−43`; a uniform bound over positive
finite binary64 inputs is `2^−44` log units. `ln(1)` is exact zero.

**`ln_1p`:** [ln.md §7](ln.md) establishes pre-rounding relative error
`ε = 2^−123` on the accurate path. Final rounding gives
`[u + (1 + u)ε]·abs(L) + η`, bounded by the table's expression.
Correctly rounded stages and the tiny-input return satisfy the same bound.
The additive term covers gradual underflow; signed-zero inputs are exact.

**Log-CDF:** the [normal-family contract](normal.md#numerical-contract)
proves `L̂ = L·(1+d)+a` with `abs(d) ≤ u + 2^−111` and `abs(a) ≤ η`.
The table follows by the triangle inequality. For `abs(x) ≤ 1/2`, use the
tighter coefficient `u + 2^−228`. Accepted correctly rounded stages also
satisfy these bounds. Positive-tail underflow to `−0` is included.
In the far negative tail, `abs(L)` grows approximately as `x²/2`, so the
absolute budget grows with it. There is no uniform small absolute
tolerance across the entire finite output domain.

**`expm1`:** [expm1.md §6](expm1.md#6-rounding-test-and-bound) gives
`q̂ = RN(z)`, with `q = exp(x) − 1` and `abs(z/q − 1) ≤ 2^−118`.
Outside the tiny-input branch these results are normal, so the relative
error is at most `u + (1 + u)·2^−118 ≤ ρ`. For `0 < abs(x) < 2^−54`,
including subnormal inputs, the exact return `q̂ = x` and §1's Taylor
remainder give relative error below `u`. Hence `q̂/q = 1 + δ` with
`abs(δ) ≤ ρ < 1`: the result is nonzero and has the correct sign. Then
`abs(ln(1 + δ)) ≤ −ln(1 − ρ) ≤ ρ/(1 − ρ) < 2^−52`.

The finite-error assertions exclude NaNs, infinities, invalid domains,
`ln(±0)`, `ln_1p(−1)`, and log-CDF or `expm1` overflow. Their special-value
semantics remain those of the linked contracts. At `expm1(±0)`, the exact
signed-zero return has log-magnitude `−∞`, so there is no finite log-error
assertion.

## Using the bounds in pricing

For any row of the form `abs(L̂ − L) ≤ α·abs(L) + η`, a consumer can use
the returned value instead of the unknown exact logarithm:

```text
abs(L̂ − L) ≤ (α·abs(L̂) + η)/(1 − α).
```

Alternatively, bound `abs(L) ≤ M` over the consumer's input domain and
use `B = α·M + η`. For `ln`, take `η = 0`.

For finite `x < 0`, `ln(−expm1(x))` targets `ln(1 − exp(x))`. With
`q̂ = expm1(x)`, its total absolute log error is at most
`ρ/(1 − ρ) + u·abs(ln(−q̂))`, where the logarithm in this bound is exact.
Argument formation, such as rounding `x = b − a`, is additional;
[log_diff_exp](log_space.md#6-log_diff_exp-error-bound) budgets it and the
subsequent addition.

If a positive quantity has exact log-value `L` and computed log-value
`L̂` with absolute error at most `B`, then
`abs(exp(L̂)/exp(L) − 1) ≤ expm1(B)` in exact real arithmetic. This is the
relative price error passed through from log space. Conversion to a
binary64 price adds its own rounding and range limits. For sums of log
terms, add their absolute bounds and the arithmetic-rounding budget.
Input uncertainty and cancellation in differences of prices need separate
conditioning bounds; primitive contracts alone do not qualify a pricer.
