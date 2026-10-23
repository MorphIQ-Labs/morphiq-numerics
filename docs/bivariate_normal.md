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
| Genz (2004) low-correlation quadrature and the high-correlation panel scheme (section 3) | done |
| Per-correlation evaluator, no allocation, bit-identical to the one-shot function | done |
| Absolute bound per correlation: `1.9e-16` to `3.72e-16` for `|rho| < 0.925`, `2.708e-16` (`rho > 0`) and `3.333e-16` (`rho < 0`) for `0.925 <= |rho| < 1` | **proved** (section 6) |
| Independent MPFR/mpmath reference, two precisions, second route (section 7) | done |
| Generator for the quadrature rules, replayed by `check_generators.sh` | done |
| Correctly rounded `asin` (#41) | done: the table's angle is `elementary::asin(rho)` (section 5) |
| Relative accuracy of small probabilities (FerroRisk's tail construction) | not ported: refused instead (section 8) |
| ARM NEON, SSE2, AVX2+FMA and AVX-512F lanes returning the scalar bits, with slice and paired entry points (section 12) | done for the low-correlation quadrature: bit equality, digest and mutation witnesses (section 12); AVX2 and AVX-512F not yet run here (CI) |
| Coq proof of the error budget | **proved** for both branches (`formal/bivariate/`), from the named hypotheses of section 6; the Coq transcription is by reading, not extracted (section 11) |
| Same-host scalar and batch performance against the FerroRisk baseline | measured (section 9); lanes **unmeasured** |

## 2. Specification

* **Domain.** `x`, `y` in the extended reals; `rho` in `[-1, 1]`.
* **Value.** The exact probability, within `absolute_error_bound(rho)` (at most
  `ABSOLUTE_ERROR_BOUND = 3.721e-16`, section 6). This is not a correctly rounded
  function: the library's correct-rounding standard (`AGENTS.md`) is claimed only
  for results that carry it, and this one publishes a bound instead, as the issue
  requires. No relative bound is published.
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
  built for a correlation it cannot serve. It holds three arrays of 24 `f64`
  and a few scalars (about 600 bytes), copies freely, never allocates, and
  builds in `n` `sin` evaluations plus one `asin` for the `n`-node rule of
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
summed in node order as a double-word (`two_sum` of each term, the
low parts added in order), which rounds once rather than once per node.

Two regimes (Genz 2004 for the split and the low branch; FerroRisk at commit
`72db248c` for the structure):

* **Low correlation, `|rho| < 0.925`.** The Gauss-Legendre sum above. The
  rule has 4 to 24 nodes depending on `|rho|` (section 4).
* **High correlation, `0.925 <= |rho| < 1`.** Plackett's integral in
  `s = sqrt(1 - rho^2)`, whose small size narrows the integrand: graded
  Gauss-Legendre panels (16 nodes above `s = 0.095`, 15 below) integrate the
  integrand directly, with a double-word sum of the node terms, and below
  `s = 0.003` Genz's closed-form moments replace the last panel. This is not
  Genz's `BVND` series: FerroRisk's transcription of that series (20 nodes
  and a Taylor-corrected subtraction) was `2.58e-16` from the exact value at
  `(-0.21101192279835226, -0.0014549743776884816, 0.925)` against a published
  `2.5e-16`, because the series' integrand is flat at zero with an essential
  singularity there, so no quadrature rule has a proved remainder for it.
  The kernel and its proof are in `docs/bivariate_normal_high.md`.

The split at `0.925` is Genz's. FerroRisk measured the reflection residual of
the low branch at `1.11e-16` through `|rho| = 0.95` and `1.2e-13` at `0.97`;
the high branch is proved up to `|rho| < 1`, so the split's margin is the
low branch's, about `0.025`, on the side that matters.

## 4. Domain splits and quadrature orders

The nodes and weights are generated (`generators/bivariate_normal_nodes.py`):
the roots of the Legendre polynomial `P_n` to 120 digits by Newton's method,
rounded once to nearest-even binary64, with the root residual and the weight
sum checked at generation time. The generator is replayed by
`scripts/check_generators.sh`.

The rule order is the smallest whose *proved* truncation bound is at or below
`2e-17`, one fifth of the published absolute bound. The proof is a
Bernstein-ellipse estimate of the Gauss-Legendre remainder, with one
certificate per rule that covers every `|rho|` up to its limit, either sign and
every pair of thresholds (`docs/bivariate_normal_truncation.md`: the derivation,
the classical theorems it assumes, and what is machine-checked in
`formal/bivariate/`). The limits are

| `|rho|` up to | 0.055 | 0.20 | 0.38 | 0.54 | 0.66 | 0.75 | 0.81 | 0.89 | below 0.925 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| nodes | 4 | 6 | 8 | 10 | 12 | 14 | 16 | 20 | 24 |

Each limit is the largest round value for which the certificate closes with a
small margin; the bound divided by `2 pi` is between `1.2e-17` and `1.6e-17` at
every limit. A larger limit needs the next rule. The test
`results_are_continuous_across_every_rule_limit` walks every limit at adjacent
doubles, and the reference fixture has rows on both sides of each.

The estimate is not tight: the truncation measured in exact arithmetic (mpmath,
40 digits, 24 thresholds per correlation) is three to four times smaller than
the proved bound at the limits, so the rules are somewhat longer than the
measurement alone would need. The proof's assumptions, the exact Gauss-Legendre
nodes and weights among them, are listed in the truncation document.

## 5. `asin` of the correlation

The low regime needs `asin(rho)` for `0 < |rho| < 0.925`, an angle up to 1.18.
It is `elementary::asin(rho)`, which is correctly rounded (`docs/asin.md`): the
computed angle is within half an ulp of `asin(rho)`, at most `1.1e-16` at the
top of the range, and the function is odd, so a negative correlation's angle is
exactly the negation of the positive one's. Its effect on the result is that
error times the integrand at the interval end over `2 pi`, at most
`1.1e-16 * 1 / 6.28 = 1.8e-17`. The test
`angular_range_is_the_correctly_rounded_asin` checks the table's angle is
`asin(rho)` bit for bit and odd in `rho`.

## 6. Error budget

The low-correlation result is `Phi(x) Phi(y) + sum_i kw_i exp(-(d p_i + m q_i))`
with `kw_i = w_i asr / (4 pi)` the folded weights and `d p_i + m q_i` the node
exponent as a sum of two non-negative terms (section 3). `docs/bivariate_normal_budget.md`
derives the bound of this operation sequence and `formal/bivariate/` checks it.
The terms:

| Term | Bound | Status |
| --- | --- | --- |
| Quadrature truncation | `<= 2e-17` (section 4) | **proved**: Bernstein ellipse, certificates in `formal/bivariate/`, with the classical theorems the truncation document lists |
| `asin`, the node angles and their `sin` | folded into the per-node constants of the budget | **proved** (`BvnLow.v`, `BvnNode.v`), from the functions' documented contracts |
| Node exponent, `exp`, weight product | per-node constant `<= 6.2e-16` relative on the term, times the correction `<= 0.19` | **proved** (`BvnArg.v`, `BvnQuadG.v`, `BvnLowRule.v`) |
| Double-word sum, one rounding | `O(n^2 u^2)` relative, however many nodes | **proved** (`BvnSum.v`) |
| `Phi(x)`, `Phi(y)` and their product | `2 (2^-54 + 2^-112)` from the operands, kept as a double-word, then one rounding of the result | **proved** from `norm_cdf`'s documented contract (`BvnTail.v`, `BvnFinal.v`) |

**Proved bounds, low-correlation branch.** The bound of the rule `|rho|`
selects, for every threshold pair with `|x|, |y| <= 64`:

| rule (nodes), `|rho|` up to | 4, 0.055 | 6, 0.20 | 8, 0.38 | 10, 0.54 | 12, 0.66 | 14, 0.75 | 16, 0.81 | 20, 0.89 | 24, 0.925 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| bound, `1e-16` | 1.90 | 2.07 | 2.31 | 2.57 | 2.76 | 2.95 | 3.09 | 3.48 | 3.72 |

`absolute_error_bound(rho)` returns that bound (rounded up in the fourth digit),
`BoundedProbability::error` carries it, and `ABSOLUTE_ERROR_BOUND = 3.721e-16` is
the largest. FerroRisk's published `2.5e-16` is therefore proved only up to
`|rho| <= 0.38`; it was a measured figure, and for the high-correlation branch it
was false (section 3: `bivariate_norm_cdf(-0.21101192279835226, -0.0014549743776884816, 0.925)`
was `2.58e-16` from the exact value). The closed-form regimes (independent,
countermonotone: `1.7e-16`; comonotone and the saturated limits: `5.7e-17`) are
derived from the same `norm_cdf` contract by a few lines, not machine-checked.
The high-correlation branch is proved at `2.708e-16` for `rho > 0` and
`3.333e-16` for `rho < 0` (`formal/bivariate/BvnHighEnd.v`: `high_pos_end`,
`high_neg_end_diff`, `high_neg_end_zero`; rounded up in the fourth digit in
`absolute_error_bound`), with no sampled hypothesis. The `rho < 0` value
carries a looser last step (a second `norm_cdf` rounding counted in full) that
a finer argument would reduce by about `2.8e-17`. Its hypotheses are the same
kind as the low branch's: the library contracts (`exp`, `sqrt`, `norm_cdf`,
`two_sum`), classical analysis (Plackett's identity, the Gauss-Legendre
remainder, the skip bounds for `hk >= 100` and `b >= 20 s`) cited and not
machine-checked, and the stored tables' fidelity; the Coq transcription of
the operation sequence matches `mod.rs` by reading. `docs/bivariate_normal_high.md`
lists each.

**Measured.** Over the fixture's 3,495 cases (section 7) the worst absolute error
is `1.11e-16`, within the bound of each case's own correlation; the proved figures
are worst-case alignments of every rounding.

**No relative bound.** Nothing here bounds the error relative to the value, and the
bounded forms report only the absolute bound. A caller that divides by a small
probability carries `error` as the error of the quotient's numerator and must refuse
the quotient where `error` is not far below the value (section 8).

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

The function does **not** resolve the corner; it **refuses** it, by contract. In the
corner the value is returned to the absolute bound, and the bounded form reports the
correlation's bound (at least `1.9e-16`), which is larger than the value: the
caller sees the result is not usable relative to itself, and must refuse a quotient
by it. Where the bound supports relative use is where the value is far above it: a
relative error of `error / value` is supported only for that ratio, never more. The three cases above, and five more
(`-8,-8,-0.5`, `-12,-12,-0.95`, `-5,-7,-0.99`, and the two positive-correlation
mirrors), are required cases in the fixture (`kind = "hard"`), and the test
`hard_cases_are_bounded_absolutely_and_refuse_relative_use` asserts both the
absolute bound and that the reported error is not smaller than the value. A function
that returns such values to relative accuracy would be a separate one with its own
proved remainder bound on the discretization, which FerroRisk's construction
lacked; this one does not claim it.

## 9. Performance

(Section filled from the same-host measurement in the pull request.)

## 10. Provenance and port inventory

The implementation, the rule structure, the semantics of the bounded form and
the contract constants are ported from FerroRisk, commit `72db248c`
(`origin/main`, v0.41.4, MorphIQ Labs, same ownership and licensing as this
repository; see `docs/PROVENANCE.md`). Genz (2004) is the published algorithm.
The low branch is a fresh transcription of Genz's published algorithm in this library's idiom, and the high branch is this library's own panel scheme (the pull request records the consultation as `docs/PROVENANCE.md` asks; FerroRisk's own origin for its transcription is in-house, and the owner should confirm it before the FerroRisk copy is deleted): correctly rounded
`exp`, `sincos`, `sqrt` and `norm_cdf` replace the platform libm and
FerroRisk's, the nodes are generated rather than pasted, and `asin` is not
taken from libm. Item by item (the list FerroRisk's deletion cites):

| FerroRisk item | Disposition |
| --- | --- |
| `numerics/bivariate_normal.rs`: Genz low regime, regime classifier, (the high regime is replaced, section 3), saturation limits, degenerate limits, probability clamp | **ported** (this module) |
| `BoundedProbability`, `bivariate_norm_cdf_bounded` semantics | **ported** with a correlation-dependent proved bound; the `2.5e-16`, `1e-3` and `1e-13` constants are **not** carried over (section 6); the sub-floor relative construction is **refused**, not deferred (section 8) |
| `BvnQuadrature` per-correlation reuse | **ported** as `BivariateNormal` (fallible construction, `Copy`, no allocation, bit-identical to the one-shot function) |
| SIMD (`pulp`) fused Genz sum and its x86 padding | **replaced** by the lanes of section 12, which keep the scalar summation order and so return the scalar bits |
| `tests/bivariate_normal_property.rs` | **ported** as deterministic unit tests (proptest is not a dependency) |
| `fuzz/fuzz_targets/bvn_bounded_invariants.rs` | **ported as a test** over 60 000 arbitrary bit patterns; the library has no fuzz target |
| `tests/bivariate_normal_reference.rs`, `testing/bivariate_normal_support.rs` | **ported as test-only**: the reference test reads the fixture and applies the absolute, relative and reported-bound checks |
| `testing/data/bivariate_normal_reference.json` (3 762 rows) | **ported as test-only**: 1 158 rows (BS2002 families dropped, the body and tail families thinned to every tenth row) re-evaluated by this oracle; the other 2 604 rows are in git history at `72db248c` and were **not ported** because the thinned set covers every family and regime edge |
| `testing/calibration/generate_bivariate_normal_reference.py` | **not ported**: replaced by `generators/bivariate_normal_reference.py` (a different route; the earlier script is the cross-check source) |
| `testing/mutations/bivariate_normal.toml` (21 faults) | **not ported**: this library has no mutation harness; the faults map to tests here: the split (`B1`) and every rule limit are held by `results_are_continuous_across_every_rule_limit` and by fixture rows on both sides; the high regime's node terms, `two_sum` accumulation, closed form and reflection branch by the high-correlation fixture rows (including rows at the counterexample) and the proof's operation sequence; the unit-edge snap (`B24`) by `reflection_holds_at_the_unit_correlation_edge`; NaN handling by `nan_and_out_of_range_inputs_*` |
| SPEC section 7.3 and ferro-risk #380 cancellation analysis | **ported** as section 8; the corner is a required fixture case |
| `formal/lean-math/FerroRisk/AmericanBivariate.lean` (5 laws: Gaussian marginal, two complement identities, comonotone and countermonotone closed forms) | **not ported**: this repository's proofs are Coq/Gappa, not Lean. Their statements are the proof targets of the remaining work; their runtime counterparts are tested: reflection (the two complements) and the degenerate closed forms |
| `benches/numerics.rs` bivariate entries (`bivariate_norm_cdf`, `_high_correlation`, `_hoisted_golden_rho`) | **ported** as the measurement matrix of section 9 (one-shot at several correlations, repeated-`rho`, table construction) |

## 11. Remaining work, in order

1. The Coq transcription of the kernel, extracted and compared bit for bit with the
   Rust, and mutation witnesses for the scalar kernel (issue #87's pipeline).
2. Measure the lanes on ARM and native x86 (#216) and re-measure against the
   performance bar on a quiet host (section 9); this slice's numbers are one noisy
   shared host.

## 12. Batch evaluation and lanes

Entry points (all return the scalar bits on every target, with or without the
`simd` feature; a length mismatch panics with `<name>: slices of different
lengths`, as the other slice functions do):

| Function | Computes |
| --- | --- |
| `BivariateNormal::cdf_slice(x, y, out)` | `out[i] = self.cdf(x[i], y[i])` at the evaluator's one correlation |
| `BivariateNormal::cdf_bounded_slice(x, y, out)` | the bounded form into `[BoundedProbability]`; values are `cdf_slice`'s, bounds are the scalar function of the value, computed in blocks of 64 so nothing allocates |
| `bivariate_norm_cdf_slice(x, y, rho, out)` | `out[i] = bivariate_norm_cdf(x[i], y[i], rho[i])`; an invalid `rho[i]` gives NaN in lane `i` only |
| `bivariate_norm_cdf_bounded_slice(x, y, rho, out)` | the bounded paired form |

With `simd` the pairs go through the library's backend cascade (AVX-512F, AVX2,
SSE2 on x86-64; NEON on aarch64; a last single pair is scalar). A chunk's lane
`i` reads its own table, so a paired batch may mix regimes and rule lengths:
the evaluator is built per lane by the scalar `BivariateNormal::new` (reused
while consecutive correlations are bit-equal), which costs the same `asin` and
`sincos` as the scalar path.

**Vectorised.** After the scalar ordering `x <= y`, a lane is served by the
vector code when neither argument is NaN, `x > -39`, `y < 39`, and its
correlation selects the low-correlation quadrature (`EPSILON <= |rho| < 0.925`):
`d = (x-y)^2`, `m = (x+y)^2`, the node loop in node order with
`kw[j] * exp(-(d p[j] + m q[j]))` accumulated as the scalar double-word
(`two_sum` per term, the low parts added in order), `two_prod(Phi(x), Phi(y))`
with its error term dropped below `PRODUCT_EXACT_FLOOR`, `two_sum(hi, high)`,
the final `sum + (err + (low + lo))` and the clamp. A lane whose rule has fewer
nodes than the chunk's longest (rules of 4 to 24 nodes) is masked on the extra
nodes (its sums are untouched and its `exp` argument is `0`), so no lane
accumulates a node the scalar code does not. The lane `two_prod` returns
`eft::two_prod`'s bits (docs/lanes.md section 2). `exp` and
`norm_cdf` are the library's lane kernels (`Exp`, `Normal<1>`), each equal to
its scalar function bit for bit, so no new transcendental is introduced and
no platform libm is called. Every operation is an individual lane add,
multiply or divide; nothing is fused or reassociated.

**Scalar per lane.** The high-correlation branch (`|rho| >= 0.925`) is **not**
vectorised: its lanes call `BivariateNormal::cdf`. So are the closed-form
regimes (independent, comonotone, countermonotone), a NaN argument, a
saturated argument (`x <= -39` or `y >= 39`), and a lane whose vector result is
NaN. A lane that is masked out of the quadrature carries a harmless argument
(`0`) and its result is discarded.

**Checked by** (`bivariate_normal/lanes/tests.rs`, with `src/lanes/tests.rs`'
backends and `MORPHIQ_LANE_CASES`): bit equality of every lane on every
backend the CPU has, including the one-lane scalar backend, over the
reference fixture's `(h, k, rho)` triples, every correlation (each rule limit
and the Genz split at adjacent doubles, `0`, `+-1` and their neighbours,
`2^-52` and its neighbour, NaN, infinities, `|rho| > 1`) against every
threshold (zeros of both signs, infinities, NaN, the saturation edges at
adjacent doubles, extremes) and random triples with mixed correlations; one
table across every threshold pair; the served-lane mask of each regime class
in every lane position; every length from 0 to 17 at eight offsets through the
driver; repeated invalid correlations; the length checks; and the determinism
digest's `bivariate_normal` and `bivariate_normal_slice` sections, scalar and
`simd`.

**Mutation.** cargo-mutants over `bivariate_normal/lanes.rs`, built with
`simd`: cargo-mutants 27.1.0 (`-j1`, per-job target directories, aarch64 NEON host) generated 98 mutants:
69 are caught, 7 do not compile and 22 survive. None of the survivors changes a result:
  - `&&` against `||` and `<` against `<=` at the node-activity test in `low` (2): a lane that
    reads a node past its rule's end reads the table's zero padding (`kw = 0`), whose term is an
    exact `+0` that `two_sum` and the low-part sum pass through unchanged, and an inactive lane is discarded.
  - `>>` against `<<` where `chunk` decides which lanes the scalar function recomputes (1): the scalar
    function returns the lane's own bits, so recomputing more lanes costs time only.
  - `lane > 0` against `lane < 0` in the table reuse (1): reuse only avoids rebuilding an identical table.
  - `>>` against `<<` in the propagation of an invalid correlation to a repeated neighbour (1): equivalent
    on a two-lane backend, where only lane 1 repeats lane 0; on four- and eight-lane backends
    `repeated_correlations_keep_their_validity_in_every_lane` (40 repeats) is expected to kill it, which this host cannot confirm.
  - The cascade's width test and counter on NEON (2): they select which backend runs which elements,
    which `lanes.md` section 6 records as speed only.
  - The x86-64 cascade lines (15) are not compiled on this host, so cargo-mutants reports them as
    survivors without running them. The mutation run must be repeated on x86-64 (AVX2, AVX-512F under SDE)
    to classify them; the `done +=` and subtraction mutants there should be killed by
    `the_cascade_returns_the_scalar_bits`, and the width tests are speed only.

**Not measured.** The lanes' speed, and whether a regime-mixed batch or the
per-lane table construction pays for itself, are not measured here;
performance is scheduled separately.
