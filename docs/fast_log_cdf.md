# Bounded normal log-CDF

`fast::normal::log_norm_cdf(x)` approximates `ln(Φ(x))`, the natural logarithm
of the standard-normal distribution function, for the exact binary64 input.
`log_norm_cdf_slice(x, out)` returns the same bits elementwise through the
existing NEON/SSE2/AVX2/AVX-512 cascade when SIMD is enabled. A length mismatch
panics before writing outputs. The strong `normal::log_norm_cdf` and every other
existing API are unchanged.

## Numerical decision and consumer purpose

Writing `L = ln(Φ(x))` and `Y` for the returned value, on the accelerated domain

```
-22.5 <= x <= -2^-33   or   2^-33 <= x <= 8
```

the contract is the mixed bound in natural-log units

```
abs(Y - L) <= 2^-51 * abs(L) + 2^-48,
```

including the final rounding. `Y` is finite, negative and normal there.
Outside the domain the strong owner supplies its result and special-value
semantics: tiny magnitudes (`-ln 2` correctly rounded at zero), the far
negative tail below `-22.5`, positive saturation to `-0`, overflow to `-∞`,
infinities and NaN payloads. Correct rounding and faithful rounding are not
the fast contract; the fast and strong results may differ.

The consumer is log-space option pricing, which adds `ln Φ(±d)` to log legs
and exponentiates the sum: the quantity it propagates is the absolute error of
`L`, and `expm1` of that error is the relative price error
([log_error.md](log_error.md)). The dominant term in the negative tail is the
binary64 rounding of `a²/2` itself, which any binary64 evaluation of this
composition carries, so a bound proportional to `abs(L)` is the natural form;
the constant term covers the table, logarithm and argument-formation errors
near the centre. Risk's own log-CDF, the accuracy guide for this row, is held
to 4 ULP against MPFR on its reference grid. The published bound is a proved
allowance, not an observed maximum; the observed maximum on the independent
oracle witnesses is reported separately in the owning issue.

| Region / output | Bound | Special values / determinism | Cost and comparator | Justification |
| --- | --- | --- | --- | --- |
| `-22.5 <= x <= -2^-33` | `2^-51·abs(L) + 2^-48` absolute, log units; `L <= -1/2` | finite negative normal; scalar and slice bit-identical | one table erfcx, one bounded `ln`, three operations; Risk `log_norm_cdf` (Cody erfcx + platform `ln`) and SciPy `log_ndtr` as cost references | `FastLogCdf.fast_logcdf_negative_ok` |
| `2^-33 <= x <= 8` | the same bound; `L < 0` | finite negative normal; bit-identical | the bounded CDF lower tail (exp, erfcx), one bounded `ln`, one division, three operations | `FastLogCdf.fast_logcdf_positive_ok` |
| `abs(x) < 2^-33`, `x < -22.5`, `x > 8`, non-finite | strong owner's contract | strong owner's bits, including `-0`, `-∞` and NaN payloads | strong dispatch | `fast_logcdf_fallback`, `fast_logcdf_nonfinite` |

## Derivation

Let `a = abs(x)`, `y = a/√2`, `q = a²/2`, `u = 2^-53`, and `F = erfcx`. The
exact targets are `ln Φ(-a) = -q + ln F(y) - ln 2` and
`ln Φ(a) = ln(1 - Φ(-a))`.

**Negative inputs.** The scalar sequence reuses the bounded CDF's argument
formation and the erfcx table kernel, then the bounded logarithm:

```
t = RN(RN(-a/2) * a)                 # exact halving; |t + q| <= u*q
z = RN(a * INV_SQRT2_HIGH)           # |z - y| <= 3u*y, 2^-34 <= z < 16
f = table_erfcx(z)                   # |f - F(z)| <= 2^-51 F(z)
g = fast_ln(f)                       # |g - ln f| <= u*|ln f| + 2^-65
Y = RN(RN(t + g) - LN2_HIGH)
```

`FastLogCdf.fast_logcdf_argument_ok` and `fast_logcdf_exponent_ok` extend the
CDF's argument and exponent proofs to `a <= 22.5`, where `z < 16` keeps the
table in its certified domain and `t >= -254`. The argument error moves
`ln F` by at most `16u` (`fast_logcdf_erfcx_log_sensitivity`): on `(0, 1]`
the derivative bound `|F'| <= 2/√π` against `F >= 7/(16√π)`, on `[1, 16]` the
tail bound `|F'(c)| c² <= 1/√π` against `F(y) >= 1/(2√π y)`. The table's
relative error contributes at most `5u` to `ln f`, and `|ln f| <= 4.9`
(`fast_logcdf_table_range`). The two additions round relative to quantities
dominated by `abs(L) >= q + ln 2`; the sum `t + g` may be tiny, so its
rounding is bounded by `u|t + g| + 2^-1075`. The constant's error is below
`2^-54`. Collecting terms, `fast_logcdf_negative_ok` proves
`abs(Y - L) <= 2^-51 abs(L) + 2^-48` and `Y <= -1/2`.

**Positive inputs.** The lower tail is the bounded CDF's composition
`q̂ = RN((0.5·exp_cubic(t))·table_erfcx(z))`, now with a relative bound.
`exp_cubic` is the public fast `exp`'s `2^-51` kernel, entered under the CDF's
argument proof; `exp_coarse`'s `2^-38` quadratic is not used in this composition:
`fast_logcdf_lower_relative` composes the exponential's two perturbations
(`2^-51` from the kernel and `exp(u q) - 1 <= 33u` from the rounded exponent),
the table's two (`2^-51` and the argument sensitivity, proportional to `y` on
`(0, 1]`) and the final rounding into `20u` relative for `a <= 1` and `56u` for
`a >= 1`; `q̂ >= 2^-52`. The complement's logarithm then moves by at most
`21u` (`fast_logcdf_complement_log`), since `q/(1 - q)` is at most one below
`a = 1` and below `0.19` above it.

```
w = RN(1 - q̂)                        # |w - (1 - q̂)| <= 2^-54; 1/4 <= w <= 1 - 2^-52
d = RN(1 - w)                        # relative u; d = q̂ + δ + δ', 4/5 <= q̂/d <= 4/3
g = fast_ln(w)
Y = RN(g * RN(q̂ / d))
```

This is Kahan's corrected logarithm: `ln(1 - q̂) = ln(w) * q̂/(q̂ + δ)` up to
`ln(1 - q̂)·δ/(q̂ + δ) + ln(1 - δ/(1 - q̂))·q̂/(q̂ + δ)`, together below
`2.5u` because `|ln(1 - q̂)| <= 1.41 q̂` for `q̂ <= 0.51`. The division and
the product round relative to `abs(L) <= 0.75`. The real-valued lemmas
`fast_logcdf_ratio_range`, `fast_logcdf_product_range` and
`fast_logcdf_positive_real` carry this arithmetic; `fast_logcdf_positive_ok`
supplies the IEEE facts for each rounding and proves the same mixed bound and
`Y < 0`.

**Dispatch.** `fast_logcdf_screen64` is the scalar screen: magnitude at least
`2^-33`, and at most `22.5` for negative or `8` for other inputs; a NaN fails
every comparison. `fast_logcdf_entry_ok` composes the branches with the
screen; `fast_logcdf_fallback` and `fast_logcdf_nonfinite` return the strong
entry's bits elsewhere. The slice kernel evaluates one table lookup, one
exponential (entered only at positive magnitudes at most 8) and one logarithm
per packet, selecting the branch per lane; lanes the screen rejects take the
strong scalar result.

## Checked by

- `formal/fast/FastLogCdf.v`, bound to the sources in `formal/binding.sha256`
  and audited in `formal/audit/KernelAudit.v`; the extracted entry is
  cross-checked against the Rust entry on the internal corpus
  (`internal_crosscheck.rs`, `fast_log_cdf` lines).
- `generators/fast_log_cdf_reference.py` writes
  `crates/reference/fixtures/fast_log_cdf.json`: independent 600- and
  1000-bit mpmath observations of `ln(erfc(-x/√2)/2)` on the strong fixture's
  arguments in the domain, every dispatch and binade boundary with its
  neighbours, uniform sweeps of both branches and dense bands near the screens.
  `crates/reference/tests/fast_log_cdf.rs` decides the budget in exact integer
  arithmetic including the oracle's enclosure, for scalar and slice.
- The fast tests compare scalar and slice bits on mixed packets and remainders,
  check strong-owner bits outside the domain, and sample the budget against the
  strong `log_norm_cdf` over both branches.
- The determinism digest appends a `fast::log_norm_cdf` section; the lane
  code-generation gate covers `fast::lanes::LogCdf`.

## Cost acceptance

Native evidence follows [the benchmark methodology](../scripts/bench_fast/README.md)
and the acceptance rule of #194: paired one-sided 95% upper time ratio at most
one in every required cell, raw samples retained, no slowdown allowance.
Comparators and workloads are declared on #192: Risk's `log_norm_cdf` (Cody
rational erfcx with the platform logarithm, scalar) and SciPy `log_ndtr`;
ordinary `|x| <= 3`, wide `[-8, 8]` and negative-tail `[-22, -8]` populations,
scalar throughput and dependent latency, slice lengths 1 to 4096 with
remainders, mixed and fallback-heavy banks, native x86 and ARM. Unmeasured
cells leave the corresponding claims unestablished.
