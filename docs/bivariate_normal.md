# The bivariate normal distribution function

`bivariate_normal::bivariate_norm_cdf(x, y, rho)` is `P(X <= x, Y <= y)` for a
standard normal pair with correlation `rho`. `BivariateNormal::new(rho)`
builds the part of the work that depends on `rho` alone, and its `cdf` and
`cdf_bounded` evaluate repeatedly at that correlation. This is the first slice
of issue #38. It states what it proves and what it only measures, and it lists
what remains; nothing below claims more than the checks named here establish.

## 1. Status

| Item | State |
| --- | --- |
| Public scalar API, domains, special values, refusals (section 2) | done |
| Genz (2004) algorithm, both regimes, ported from FerroRisk (section 3) | done |
| Per-correlation evaluator, no allocation, bit-identical to the one-shot function | done |
| Absolute bound `2.5e-16` and relative bound above `1e-3` | **measured, not proved** (section 6) |
| Independent MPFR/mpmath reference, two precisions, second route (section 7) | done |
| Generator for the quadrature rules, replayed by `check_generators.sh` | done |
| Correctly rounded `asin` (#41) | not done: an internal bounded `asin` stands in (section 5) |
| Relative accuracy of small probabilities (FerroRisk's tail construction) | not ported: refused instead (section 8) |
| ARM NEON, SSE2, AVX2+FMA and AVX-512F lanes returning the scalar bits | not done |
| Gappa/Coq proof of the error budget | not done |
| Same-host scalar and batch performance against the FerroRisk baseline | measured (section 9); lanes not measured |

## 2. Specification

* **Domain.** `x`, `y` in the extended reals; `rho` in `[-1, 1]`.
* **Value.** The exact probability, within the absolute bound `ABSOLUTE_ERROR_BOUND = 2.5e-16`
  of section 6. This is not a correctly rounded function: the library's
  correct-rounding standard (`AGENTS.md`) is claimed only for results that
  carry it, and this one publishes a bound instead, as the issue requires.
* **Special values.** A NaN argument or a NaN or out-of-range (`|rho| > 1`)
  correlation gives NaN, with a NaN error from the bounded forms. `x = -inf` or
  `y = -inf` gives exactly `+0`; `y = +inf` gives `Phi(x)` and both `+inf`
  give 1. Beyond `|x| = 39` the standard normal CDF is exactly 0 or 1 in
  binary64 (`Phi(-39)` is about `1.4e-333`), so a threshold at or below `-39`
  gives `+0` and one at or above `39` gives `Phi` of the other; this also
  keeps the quadratures from forming `inf * 0`.
* **Exact degenerate correlations.** `rho = 1`: `Phi(min(x, y))`. `rho = -1`:
  `max(0, Phi(lo) - Phi(-hi))`, which is `max(0, Phi(lo) + Phi(hi) - 1)` written
  so a small result keeps its digits. `|rho| < 2^-52`: `Phi(x) Phi(y)`. A
  correlation one unit in the last place inside `+-1` is *not* snapped to the
  endpoint: the pair still smooths over `sqrt(1 - rho^2) = 1.5e-8`, and
  snapping would miss results near `x = y` by about `1e-9`.
* **Signed zero.** The result is a probability and is never `-0`: the clamp to
  `[0, 1]` returns `+0`.
* **Symmetry** in `(x, y)` is structural: the arguments are ordered before any
  arithmetic, so swapped arguments run identical operations and return
  identical bits.
* **Construction.** `BivariateNormal::new(rho)` is fallible: it returns
  `Err(InvalidCorrelation)` for NaN or `|rho| > 1`, so a table can never be
  built for a correlation it cannot serve. It holds three arrays of 20 `f64`
  and a few scalars (about 530 bytes), copies freely, never allocates, and
  builds in `n` `sincos` evaluations plus one `asin` for the `n`-node rule of
  the low-correlation regime and in no work otherwise. The one-shot functions
  are the evaluator behind a freshly built table, so the two are the same
  arithmetic by construction.

## 3. Algorithm

Plackett's identity,

    d/d rho P(X <= x, Y <= y; rho) = phi2(x, y; rho),

with the substitution `rho = sin t` gives Genz's angular form

    P = Phi(x) Phi(y)
        + 1/(2 pi) int_0^{asin rho} exp(-(x^2 + y^2 - 2 x y sin t) / (2 cos^2 t)) dt.

The integrand is smooth and bounded by 1 on `[0, asin rho]`: its only
singularities are the essential ones at `t = +-pi/2`, which the angular
substitution moves out of reach of the interval for `|rho| < 1`, where the
`rho` form has a branch point at `rho = 1` close enough to slow a fixed rule.
The sum is `asin(rho)/(4 pi)` times the weighted sum of the integrand over the
rule's nodes, which come in `+-` pairs about the interval's centre and are
summed in node order.

Two regimes (Genz 2004, ported from FerroRisk at commit `72db248c`):

* **Low correlation, `|rho| < 0.925`.** The Gauss-Legendre sum above. The
  rule has 4 to 20 nodes depending on `|rho|` (section 4).
* **High correlation, `0.925 <= |rho| < 1`.** Genz's `BVND` series: the
  integral is rewritten in `s = sqrt(1 - rho^2)`, whose small size narrows the
  integrand, with a Taylor-corrected subtraction and a 20-node rule. It is
  transcribed in Genz's own variable names so it can be checked line by line;
  FerroRisk's earlier transcription was wrong in five places at once
  (NU-0003) and read plausibly throughout, so this port reads the published
  algorithm and was verified against the reference at the classifier's
  adjacent doubles (section 7).

The split at `0.925` is Genz's. FerroRisk measured the reflection residual of
the low branch at `1.11e-16` through `|rho| = 0.95` and `1.2e-13` at `0.97`,
and the high branch at `1.11e-16` from `0.90` upward, so the split is
conservative with a margin of about `0.025` on the side that matters.

## 4. Domain splits and quadrature orders

The nodes and weights are generated (`generators/bivariate_normal_nodes.py`):
the roots of the Legendre polynomial `P_n` to 120 digits by Newton's method,
rounded once to nearest-even binary64, with the root residual and the weight
sum checked at generation time. The generator is replayed by
`scripts/check_generators.sh`.

The rule order is the smallest keeping the *truncation* error of the quadrature
at or below `2e-17`, one fifth of the published absolute bound. Truncation was
measured in exact arithmetic (mpmath, 40 digits) as the difference between the
`n`-node sum and the integral, over 24 thresholds per correlation including
the equal-threshold, opposite-threshold and `|x|, |y| <= 8` corners where the
integrand is least smooth. Worst absolute truncation error of the sum divided
by `2 pi`:

| `|rho|` | 4 nodes | 6 | 8 | 10 | 12 | 14 | 16 | 20 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 0.05 | 2.3e-19 | | | | | | | |
| 0.09 | 4.4e-17 | 4.5e-24 | | | | | | |
| 0.30 | 4.9e-12 | 1.3e-16 | 3.7e-21 | | | | | |
| 0.50 | 1.1e-09 | 4.5e-13 | 1.3e-16 | 4.2e-20 | | | | |
| 0.65 | 2.2e-08 | 2.9e-11 | 6.5e-14 | 1.5e-16 | 2.6e-19 | | | |
| 0.75 | 9.5e-08 | 8.3e-10 | 3.3e-12 | 1.3e-14 | 6.3e-17 | 3.1e-19 | | |
| 0.80 | 3.7e-07 | 2.4e-09 | 1.2e-11 | 1.7e-13 | 1.6e-15 | 1.2e-17 | | |
| 0.85 | 9.6e-07 | 1.1e-08 | 1.6e-10 | 2.8e-12 | 3.7e-14 | 4.9e-16 | 6.8e-18 | |
| 0.925 | 1.3e-05 | 4.1e-07 | 1.6e-09 | 1.5e-10 | 3.9e-12 | 8.9e-14 | 4.0e-15 | 4.8e-18 |

The error falls geometrically in `n` and grows steeply in `|rho|` (the
singularity nearest the interval is the essential one at `t = pi/2`, and the
interval end `asin rho` approaches it). The limits chosen are

| `|rho|` up to | 0.06 | 0.22 | 0.40 | 0.55 | 0.70 | 0.80 | 0.85 | below 0.925 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| nodes | 4 | 6 | 8 | 10 | 12 | 14 | 16 | 20 |

Each limit sits where the neighbouring row of the table is `2e-17` or less,
with margin for the unmeasured interior; the test
`results_are_continuous_across_every_rule_limit` walks every limit at adjacent
doubles, and the reference fixture has rows on both sides of each.

**This is a measurement over a finite set of thresholds, not a supremum.** A
proved bound is a Bernstein-ellipse estimate of the Gauss-Legendre remainder
for the integrand's analytic extension; it has to maximise
`|exp(-Q(t))|` over the ellipse, which grows with `|x|, |y|`, and does not
close here without a restriction on the thresholds (the saturating range
beyond 39 is excluded, but the integrand is not small on the ellipse until the
thresholds are). That analysis is not done.

## 5. `asin` of the correlation

The low regime needs `asin(rho)` for `0 < |rho| < 0.925`, an angle up to 1.18.
The library has no `asin` yet (#41) and forbids the platform one. `asin_low(m)`
therefore computes it from the correctly rounded `sincos`: a series start
(`m` itself up to 0.5, and `pi/2 - 2 asin(sqrt((1 - m)/2))` above, where the
argument is below 0.5), then two Newton steps `t <- t - (sin t - m)/cos t`.
The start is within `1e-7`, so one step is within `1e-14` and the second
reaches the rounding floor: the error of the result is that of `sin` at
the converged angle divided by `cos t`, at most `5.5e-17 / 0.38 = 1.5e-16` at
`|rho| = 0.925`. Its effect on the result is that error times the integrand at
the interval end over `2 pi`, at most `1.5e-16 * 1 / 6.28 = 2.4e-17`. The test
`asin_low_inverts_sin_to_the_stated_bound` checks the sine residual.

When #41 lands a correctly rounded `asin`, `asin_low` is replaced and the
budget term below shrinks to `1.1e-16 / 2 pi = 1.8e-17`; no other change is
needed.

## 6. Error budget

The result is `Phi(x) Phi(y) + (asr / 4 pi) S`, where `S = sum_i w_i
exp((sn_i x y - hs) / cos_i^2)`, `hs = (x^2 + y^2)/2`, `asr` is the computed
`asin(rho)` and `sn_i, cos_i` the computed sine and cosine of node `i`'s angle.
The terms, with their status:

| Term | Bound | Status |
| --- | --- | --- |
| Quadrature truncation | `<= 2e-17` (section 4) | measured on 24 thresholds per correlation |
| Rule rounding: nodes and weights rounded once | each relative `<= 2^-53`; effect `<= 2^-53 * (asr/4 pi) * sum w_i * 1 <= 2.2e-17 * 0.19 = 4e-18` | derived; the integrand is at most 1 |
| `asin` | `<= 2.4e-17` (section 5) | derived from the rounding of `sin`; sine residual tested |
| Node angle `t_i = asr (1 +- x_i)/2` and its `sincos` | angle error `<= 1.2e-16` moves the integrand by `|f'| * 1.2e-16`, `|f'| <= 3` where `f` is not negligible | derived by inspection of `f'`, **not proved**; folded into the measurement |
| Exponent `(sn x y - hs)/cos^2`: a few rounding errors on a quantity of size `|arg|` | `exp` relative error `<= 3 eps |arg|`, and `max_{arg <= 0} e^{arg} |arg| = 1/e`: `<= 3 eps/e * 0.19 = 2.5e-17` | derived |
| `exp` (correctly rounded) and the weighted sum | `<= 0.5 ulp` each, summed with `n <= 20` additions: `<= 20 * 1.1e-16 * 0.19 / 2 = 2e-16` worst case if all rounding errors aligned; observed `<= 3e-17` | derived worst case far above the observed; **not tight** |
| `Phi(x)`, `Phi(y)` | each within the library's proved normal-CDF bound (`docs/normal.md`) | referenced |
| Product, sum and the clamp to `[0, 1]` | `<= 1.5 ulp(value)` | derived |

Two statements hold: the *published* bound `2.5e-16` is the FerroRisk
contract, kept so a consumer's bound does not change; and it is **measured**
against the reference over a finite set (section 7): worst error `2.22e-16`
on the fixture and `1.97e-16` over 20 000 random low-regime cases and `1.11e-16`
over 3 000 random high-regime cases, all in the region where the value is near
1 and one unit in the last place is `1.1e-16`. The margin is thin (11 per cent
on the fixture). A **proof** of `2.5e-16` needs the terms above bounded with
interval or Gappa arithmetic and the truncation term discharged by the
Bernstein estimate; that is the proof obligation this slice leaves open.

At or above `RELATIVE_FLOOR = 1e-3`, the bounded forms report
`min(1e-13 * value, 2.5e-16)`; measured worst relative error there is
`3.2e-15`. Below the floor only the absolute bound is reported, so a caller
that divides by a small probability carries `2.5e-16` as the error and cannot
mistake the result for a relative one.

## 7. Evidence

* **Reference fixture** `crates/reference/fixtures/bivariate_normal.json`,
  generated by `generators/bivariate_normal_reference.py` (mpmath 1.4.1,
  replayed by `check_generators.sh`). The value is Plackett's integral in the
  angle, `P(-1) + 1/(2 pi) int_{-pi/2}^{asin rho} f(t) dt`, by tanh-sinh at 280
  and 360 bits; where `x + y > 0` the survival identity moves the integral to
  the side where `P(-1) = 0`, so the integrand is positive and a small result
  has no cancellation and is accurate in relative terms. Each case must
  agree between the two precisions to `1e-36` relative (or `1e-46` absolute);
  a subset is also evaluated by Owen's T-function decomposition, which shares
  no integrand with it, and must agree with the first route to `1e-30`. The
  Genz rule is never called. Inputs are exact binary64.
* **Cases.** The grid is every correlation (each rule limit and split at
  adjacent doubles, `+-(1 - 2^-k)` for several `k`, the extremes) against 21
  threshold pairs; 8 required hard cases from FerroRisk's issue #380; 200 random
  cases; and 1 158 rows imported from FerroRisk's reference corpus
  (section 10), each re-evaluated by this oracle rather than copied, and
  recorded with any disagreement.
* **Properties** (`bivariate_normal/tests.rs`, ported from FerroRisk's
  `bivariate_normal_property.rs` and fuzz target): reflection
  `Phi2(a, b, rho) + Phi2(a, -b, -rho) = Phi(a)` within the two bounds,
  including at the unit-correlation edge; monotonicity within the bounds;
  bit-identical symmetry; the evaluator equal to the one-shot function; the
  exact degenerate correlations; NaN and out-of-range handling; saturated
  thresholds; underflowed tails keeping a positive bound; 60 000 arbitrary
  binary64 patterns for the fuzz invariants.
* **Stress outside the fixture:** 20 000 random low-regime cases against a
  64-node exact-arithmetic evaluation of the same integral (40 digits), and
  3 000 random high-regime cases against the oracle; the worst errors are in
  section 6.

## 8. The deep-tail negative-correlation corner (ferro-risk #380)

For `x, y` both well below zero and `rho < 0` the true value is far below the
rounding floor of the sum `Phi(x) Phi(y) + (asr/4 pi) S`, whose two terms
cancel to about one part in `1e16`:

| `x` | `y` | `rho` | true value |
| --- | --- | --- | --- |
| -3 | -3 | -0.78615 | 6.663e-22 |
| -6 | -6 | -0.9 | 4.554e-161 |
| -20 | 1 | -0.5 | 2.842e-114 |

The reflection `Phi2(x, y, rho) = Phi(x) - Phi2(x, -y, -rho)` moves the problem
to positive correlation where each term is well conditioned and cancels
*worse* (`2.03e18` against `1e16`), so no rearrangement of the quadrature
recovers the digits. FerroRisk's `bivariate_norm_cdf_bounded` recovered a
relative bound below `1e-3` for `|rho| < 0.925` by integrating the conditional
density `int phi(t) Phi((y - rho t)/s) dt`, whose log-integrand is concave
with `-1/s^2 <= g'' <= -1`, with tangent-line tails, four 16/32-point panels
and a rounding bound from `log_norm_cdf`; its discretization estimate was
its one non-certified part, and it did not cover `|rho| >= 0.925`.

This slice does **not** resolve the corner; it **refuses** it. In the corner the
value is returned to the absolute bound, and the bounded form reports
`2.5e-16`, which is larger than the value: the caller sees the result is
not usable relative to itself. The three cases above, and five more
(`-8,-8,-0.5`, `-12,-12,-0.95`, `-5,-7,-0.99`, and the two positive-correlation
mirrors), are required cases in the fixture (`kind = "hard"`), and the test
`hard_cases_are_bounded_absolutely_and_refuse_relative_use` asserts both the
absolute bound and that the reported error is not smaller than the value. The
relative construction is the first item of the remaining work (section 11),
and it needs a proved remainder bound on the discretization to meet this
library's standard.

## 9. Performance

(Section filled from the same-host measurement in the pull request.)

## 10. Provenance and port inventory

The implementation, the rule structure, the semantics of the bounded form and
the contract constants are ported from FerroRisk, commit `72db248c`
(`origin/main`, v0.41.4, MorphIQ Labs, same ownership and licensing as this
repository; see `docs/PROVENANCE.md`). Genz (2004) is the published algorithm.
The code is a fresh transcription of Genz's published algorithm in this library's idiom (the pull request records the consultation as `docs/PROVENANCE.md` asks; FerroRisk's own origin for its transcription is in-house, and the owner should confirm it before the FerroRisk copy is deleted): correctly rounded
`exp`, `sincos`, `sqrt` and `norm_cdf` replace the platform libm and
FerroRisk's, the nodes are generated rather than pasted, and `asin` is not
taken from libm. Item by item (the list FerroRisk's deletion cites):

| FerroRisk item | Disposition |
| --- | --- |
| `numerics/bivariate_normal.rs`: Genz low and high regimes, regime classifier, saturation limits, degenerate limits, probability clamp | **ported** (this module) |
| `BoundedProbability`, `bivariate_norm_cdf_bounded` semantics and constants (`2.5e-16`, `1e-3`, `1e-13`) | **ported**; the sub-floor relative construction is **deferred** (section 8) |
| `BvnQuadrature` per-correlation reuse | **ported** as `BivariateNormal` (fallible construction, `Copy`, no allocation, bit-identical to the one-shot function) |
| SIMD (`pulp`) fused Genz sum and its x86 padding | **deferred**: the lanes must return the scalar bits (issue acceptance), which a re-association does not |
| `tests/bivariate_normal_property.rs` | **ported** as deterministic unit tests (proptest is not a dependency) |
| `fuzz/fuzz_targets/bvn_bounded_invariants.rs` | **ported as a test** over 60 000 arbitrary bit patterns; the library has no fuzz target |
| `tests/bivariate_normal_reference.rs`, `testing/bivariate_normal_support.rs` | **ported as test-only**: the reference test reads the fixture and applies the absolute, relative and reported-bound checks |
| `testing/data/bivariate_normal_reference.json` (3 762 rows) | **ported as test-only**: 1 158 rows (BS2002 families dropped, the body and tail families thinned to every tenth row) re-evaluated by this oracle; the other 2 604 rows are in git history at `72db248c` and were **not ported** because the thinned set covers every family and regime edge |
| `testing/calibration/generate_bivariate_normal_reference.py` | **not ported**: replaced by `generators/bivariate_normal_reference.py` (a different route; the earlier script is the cross-check source) |
| `testing/mutations/bivariate_normal.toml` (21 faults) | **not ported**: this library has no mutation harness; the faults map to tests here: the split (`B1`) and every rule limit are held by `results_are_continuous_across_every_rule_limit` and by fixture rows on both sides; the second high-correlation term's sign (`B3`) and the high-regime accumulation by the high-correlation fixture rows; the unit-edge snap (`B24`) by `reflection_holds_at_the_unit_correlation_edge`; NaN handling by `nan_and_out_of_range_inputs_*` |
| SPEC section 7.3 and ferro-risk #380 cancellation analysis | **ported** as section 8; the corner is a required fixture case |
| `formal/lean-math/FerroRisk/AmericanBivariate.lean` (5 laws: Gaussian marginal, two complement identities, comonotone and countermonotone closed forms) | **not ported**: this repository's proofs are Coq/Gappa, not Lean. Their statements are the proof targets of the remaining work; their runtime counterparts are tested: reflection (the two complements) and the degenerate closed forms |
| `benches/numerics.rs` bivariate entries (`bivariate_norm_cdf`, `_high_correlation`, `_hoisted_golden_rho`) | **ported** as the measurement matrix of section 9 (one-shot at several correlations, repeated-`rho`, table construction) |

## 11. Remaining work, in order

1. The relative construction below the floor (section 8), with a proved
   remainder bound, or an explicit refusal API; resolves the #380 corner.
2. A correctly rounded `asin` (#41, asin only); then drop `asin_low`.
3. The Bernstein-ellipse proof of the truncation term and interval/Gappa
   bounds for the rest, then the Coq pipeline of #87.
4. SIMD lanes (NEON, SSE2, AVX2+FMA, AVX-512F) returning the scalar bits, and
   their measurement on ARM and native x86.
5. Re-measure against the performance bar on a quiet host; this slice's
   numbers are one noisy shared host (section 9).
