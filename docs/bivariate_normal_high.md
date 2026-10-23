# The high-correlation branch of the bivariate normal: decomposition, truncation, rounding

`high_correlation(dh, dk, rho)` in `crates/morphiq-numerics/src/bivariate_normal/mod.rs`
serves `0.925 <= |rho| < 1`. This note writes out the exact mathematics the
branch evaluates, bounds each error it commits, and says what is proved, what
is derived, and what is only measured. It supplements `docs/bivariate_normal.md`
(sections 3 and 6) and `docs/bivariate_normal_truncation.md` (the low branch).

## 0. Result

| Quantity | Value | Status |
| --- | --- | --- |
| Truncation of the remainder quadrature | `<= 3.3e-18` of the result | proved from the cited theorems of section 6, with the real-arithmetic certificate machine-checked (`BvnHighPanels.v`) |
| Rounding of the accumulation of node terms | `<= 3e-17` of the integral, `5e-18` of the result | machine-checked (`BvnHighBudget.remainder_sum_error`), given the terms' absolute sum `<= 5e-3` (`remainder_magnitude_bound`: `4.3e-3` from claim K) |
| Rounding of `A1`, `A2`, the setup and the node brackets | `<= 5e-16` of the integral, `8e-17` of the result | **derived and sampled, not proved** (section 4.2) |
| Division by `TAU` and the constants | `<= 1.0e-17` of the result | machine-checked (`division_step`, `tau_error`, `sqrt_tau_error`) |
| Assembly, `rho > 0` | `2 * 2^-54 = 1.11e-16` | machine-checked (`pos_assembly`), `norm_cdf` nearest-rounded |
| Assembly, `rho < 0` | `21/8 * 2^-54 = 1.46e-16` | machine-checked (`neg_assembly_final`), `norm_cdf` nearest-rounded |
| **Bound of the branch, `rho > 0`** | **`2.1e-16`** | `BvnHighBudget.high_pos_bound`, conditional on the sampled hypothesis |
| **Bound of the branch, `rho < 0`** | **`2.4e-16`** | `BvnHighBudget.high_neg_bound`, conditional on the same hypothesis |

The branch therefore meets `ABSOLUTE_ERROR_BOUND = 2.5e-16` under three explicit
conditions: the sampled rounding hypothesis `|J~ - J| <= 5e-16 + 21e-18`
(`BvnHighBudget.dJ_bound`, section 4.2), the cited theorems of section 6, and
`norm_cdf` returning the nearest binary64 of `Phi` (section 4.1). Under the
documented `norm_cdf` contract alone (relative `2^-53`), the same structure gives
`2.8e-16` for `rho < 0`; no accounting of this structure reaches `2.5e-16`
without the nearest-rounding statement. The margin of the proved total for
`rho < 0` is 4 per cent.

The previous kernel, a single 20-node Gauss-Legendre rule with the node terms
added one by one to the accumulator, exceeded the bound: `bivariate_norm_cdf(-0.21101192279835226,
-0.0014549743776884816, 0.925)` was `2.5794e-16` from the exact value (section 2).

## 1. The exact decomposition

### 1.1 The target

For `rho > 0` the branch evaluates the upper-tail probability
`P(X >= dh, Y >= dk; rho)` (the caller passes `dh = -x`, `dk = -y`). Put

    r = |rho|,    a = sqrt(1 - r^2),    rs(x) = sqrt(1 - x^2),
    h = dh,       k = dk (rho > 0) or -dk (rho < 0),
    hk = h k,     bs = (h - k)^2,       b = |h - k|.

On the admissible domain `|dh|, |dk| < 39` (the saturation limits of
`degenerate_limit` leave nothing else), so `|hk| <= 1521`; always
`bs >= -4 hk` (`bs = (h + k)^2 - 4 hk`); and `a` runs from `1.49e-8` (one ulp
inside 1) to `0.37997` (`r = 0.925`).

### 1.2 Plackett's identity in the angle, and the substitution `x = cos(theta)`

Plackett's identity written in the angle `theta`, `sin theta = rho'`, gives for
`rho > 0`

    P(r) = P(1) - 1/(2 pi) int_{asin r}^{pi/2} exp(-(h^2 + k^2 - 2 h k sin theta) / (2 cos^2 theta)) d theta,
    P(1) = Phi(-max(h, k)).

With `x = cos theta` (so `sin theta = rs(x)`, `d theta = -dx / rs(x)`, and
`theta = asin r` is `x = a`) the exponent splits, because `x^2 = 1 - rs^2`
(`BvnHighAlgebra.plackett_exponent`):

    (h^2 + k^2 - 2 h k rs) / (2 (1 - rs^2)) = bs / (2 x^2) + hk / (1 + rs).

Hence

    P(h, k; rho) = Phi(-max(h, k)) - J / (2 pi),
    J = int_0^a F(x) dx,    F(x) = exp(-bs/(2 x^2) - hk/(1 + rs)) / rs.

The first part of the exponent, `bs / (2 x^2)`, is the factor that narrows the
integrand: for `bs > 0` it is `C^infinity` and flat at `x = 0`, with an essential
singularity there, which section 2 shows is what a single polynomial rule
cannot resolve.

For `rho < 0` the reflection `P(h, k; -r) = Phi(-h) - P(h, -k; r)` gives

    P(h, k; -r) = max(0, Phi(-h) - Phi(k)) + J' / (2 pi),

`J'` being `J` for the pair `(h, -k)` (the code's `k = -dk`), because
`Phi(-max(h, -k)) = min(Phi(-h), Phi(k))` (`BvnHighAlgebra.reflection_phi_terms`).

### 1.3 Taylor-corrected subtraction

`F = E G` with

    E(x) = exp(-bs/(2 x^2) - hk/2),    G(x) = exp(-hk x^2 / (2 (1 + rs)^2)) / rs
                                             (`BvnHighAlgebra.smooth_exponent`).

`G`, as a function of `u = x^2`, has the expansion `1 + c u + c d u^2 + O(u^3)`
with

    c = (4 - hk) / 8,    d = (12 - hk) / 16,

for every `hk`: the coefficient of `u^j` is a polynomial in `hk` of degree `j`,
and `{c, c d}` agree with the exact rational series of `G` at four values of `hk`
(`0, 1, -1, 5/3`), which fixes both quadratics. Put `T = 1 + c u (1 + d u)` and
`V = G - T = O(u^3)`. Then, for any `c` and `d`,

    J = int_0^a E T dx + int_0^a E V dx        (`BvnHighAlgebra.subtraction_identity`)

and `c, d` decide only how small `V` is.

### 1.4 The analytic part

With the base moment `int_0^a exp(-bs/(2 x^2)) dx = a ea - b sqrt(2 pi) Phi(-b/a)`
(`ea = exp(-bs/(2 a^2))`) and the integration-by-parts recurrences
`3 E2 = a^3 ea - bs E0`, `5 E4 = a^5 ea - bs E2` for the moments of order 2 and 4,
the first integral is `A1 - A2` (`BvnHighAlgebra.moment_closed_form`):

    A1 = a exp(asr) (1 - c (bs - a^2) (1 - d bs/5) / 3 + c d a^4 / 5),     asr = -(bs/a^2 + hk)/2,
    A2 = exp(-hk/2) sqrt(2 pi) Phi(-b/a) b (1 - c bs (1 - d bs/5) / 3).

These are the two closed-form terms of the code, in its own names (`ass = a^2`).

### 1.5 The remainder integral on graded panels

`R = int_0^a E V dx` is evaluated on the panels `[s/2, s]`, `s = a, a/2, a/4, ...`
while `s > 0.003`, by a Gauss-Legendre rule of odd order on each: 15 nodes for
`s > 0.19`, then 13 (`s > 0.095`), 11 (`> 0.0475`), 9 (`> 0.02375`), 7
(`> 0.011875`), 5 (`> 0.0059375`), 3. The node of abscissa `t` is `x = (s/4)(3 + t)`
(`t` in `[-1, 1]`, centre node `t = 0`), its weight factor `(s/4) w`. What
remains below the last panel, at most `0.003`, is dropped. At `a = 0.38` the
rule has 7 panels and 63 nodes; for `a <= 0.003` there is no quadrature.

### 1.6 What the code evaluates

In order, for `rho > 0` (the other sign differs in `k`, `hk` and the last lines):

    hk = dh*dk;  ass = (1 - |rho|)(1 + |rho|);  a = sqrt(ass);  bs = (dh - k)^2;
    c = (4 - hk)/8;  d = (12 - hk)/16;  asr = -(bs/ass + hk)/2;
    bvn  = a * exp(asr) * (1 - c (bs - ass)(1 - d bs/5)/3 + c d ass^2/5)         [asr > -100]
    bvn -= exp(-hk/2) * SQRT_TAU * norm_cdf(-sqrt(bs)/a) * sqrt(bs) * (1 - c bs (1 - d bs/5)/3)   [-hk < 100]
    remainder = sum over panels, nodes of  wf * exp(asr_i) * (exp(-hk x^2/(2 (1+rs)^2))/rs - (1 + c x^2 (1 + d x^2)))   [asr_i > -100]
    bvn += remainder;  bvn = -bvn / TAU
    rho > 0:  result = bvn + norm_cdf(-max(dh, dk))
    rho < 0:  g = -bvn;  (p1, p2) = (norm_cdf(-dh), norm_cdf(dk));
              result = p1 > p2 ? hi + (lo + g) with (hi, lo) = two_sum(p1, -p2) : g
    clamp to [0, 1]

### 1.7 The approximations made

| # | Approximation | Size |
| --- | --- | --- |
| A1 | the panel rules for `R` (truncation) and the dropped part below the last panel | `<= 2.1e-17` of the integral, `3.3e-18` of the result (section 3) |
| A2 | shipped nodes and weights are the binary64 roundings of the exact ones, and the node arguments and weight factors round | included in the node-bracket term of section 4.2 |
| A3 | `A1` dropped when `asr <= -100`; `A2` dropped when `hk <= -100`; a node dropped when its `asr_i <= -100` | each `< 1e-38` (derived, not mechanised): the dropped term is at most `e^-100 = 3.7e-44` times a polynomial in `(bs/a^2, hk)` below `1e4` where a cutoff applies; for `hk <= -100`, `bs >= -4 hk` forces `asr <= -150` |
| A4 | the constants: `TAU` is `2 pi (1 - 3.90e-17)`, `SQRT_TAU` is `sqrt(2 pi) (1 + 7.31e-17)` | machine-checked (`tau_error`, `sqrt_tau_error`); effect `<= 2.7e-18` and `<= 4.6e-18` of the result |
| A5 | every rounded operation | section 4 |
| A6 | the final clamp to `[0, 1]` | never increases the error (`BvnHighAssembly.clamp_lipschitz`) |

## 2. Why a single rule is not provable, and what it cost

`docs/bivariate_normal_truncation.md` bounds a Gauss-Legendre remainder by the
Bernstein ellipse of the interval, which must lie in a region where the
integrand is analytic. The ellipse of `[0, a]` for any parameter `> 1` contains
`x = 0` in its interior, and `E(z) = exp(-bs/(2 z^2) - hk/2)` has an essential
singularity there that is unbounded along the imaginary axis
(`|E(i y)| = exp(bs/(2 y^2) - hk/2)`). For `bs > 0` no ellipse exists, so the
low branch's method does not apply to one rule on `[0, a]`. A derivative
(Peano-kernel) bound with Cauchy estimates on discs of radius `kappa x` fails
too: the discs must stay in the sector `|arg z| < pi/4`, and `40! kappa^-40`
swamps the kernel away from the first node.

Measured in exact arithmetic (the rule's own exact nodes against adaptive
quadrature of `E V` over `[0, a]`), the truncation of the result for a single
20-node rule, maximised over `bs` at `hk = 0` (where it peaks; at `a = 0.38`,
`hk > 0` and `hk < 0` are smaller):

| `a` | `|rho|` | peak truncation of the result |
| --- | --- | --- |
| 0.38 | 0.925 | **1.93e-16** (`bs/a^2 = 0.3`) |
| 0.34 | 0.9404 | 8.9e-17 |
| 0.30 | 0.9539 | 3.7e-17 |
| 0.26 | 0.9656 | 1.4e-17 |
| 0.22 | 0.9755 | 4.2e-18 |
| 0.18 | 0.9837 | 1.0e-18 |
| 0.14 | 0.9902 | 1.8e-19 |
| 0.10 | 0.9950 | 1.7e-20 |

At `a = 0.38`, `hk = 0` a single rule of `N` nodes truncates by `1.9e-16`
(`N = 20`), `1.8e-17` (24), `1.5e-18` (28), `4.5e-19` (32), `1.4e-20` (40),
`3.5e-22` (48): it falls steadily, but no `N` has a proof.

The counterexample on which the 20-node rule exceeded the published bound:

    x   = -0.21101192279835226   (0xbfcb02704dbe1479)
    y   = -0.0014549743776884816 (0xbf57d69ad7989ddc)
    rho =  0.925                 (0x3fed99999999999a, a double above 0.925)
    20-node kernel  0.38767043158686953    (0x3fd8cf97a452ad04), error -2.5794e-16
    panel kernel    0.38767043158686976, error -3.6e-17
    exact           0.387670431586869792906995560869

The exact value is the Plackett angle integral at 60 digits and,
independently, the conditional integral `int phi(t) Phi((y - rho t) /
sqrt(1 - rho^2)) dt` over `(-inf, x]`; they agree to all 30 printed digits. Here
`hk = 3.07e-4`, `bs = 0.0439 = 0.304 a^2`: the peak of the table. The test
`high_correlation_peak_rows_meet_the_published_bound` holds this row and 24
others at the peak, for six correlations of both signs.

## 3. The panels: truncation

### 3.1 Structure

Each panel `[s/2, s]` is short enough that its Bernstein ellipse stays in the
sector `|Im z| <= (21/25) Re z` (about 40 degrees) of the right half plane,
where `|exp(-bs/(2 z^2))| <= 1` because
`Re z^-2 = (x^2 - y^2)/(x^2 + y^2)^2 > 0`. The ellipse of the unit panel
`[1/2, 1]` with parameter `7/2` is `u = 3/4 + (53/112) cos th`,
`v = (45/112) sin th`; every panel's ellipse is its homothetic image, so one
check serves all (`BvnHighPanels.panel_sector`).

### 3.2 The bound

**Claim K.** Write `E V = Et(z) Vt(z^2)` with `Et(z) = exp(-bs/(2 z^2))` and
`Vt(u) = exp(-hk/(1 + sqrt(1 - u)))/sqrt(1 - u) - exp(-hk/2) T(u)` (the factor
`exp(-hk/2)` of `E` moved into `V`). For `z` in the sector with `|z|^2 <= 22/100`
(the panel ellipses of `a <= 19/50` satisfy `|z| <= (19/50)(123/100)`), every real
`bs >= 0` and `hk` with `bs >= -4 hk`,

    |Et(z) Vt(z^2)| <= kappa |z|^6,    kappa = 72/10.

*Proof.* `Vt(u)` is analytic on `|u| < 1` (`rs != 0`, `1 + rs != 0`) and `O(u^3)`,
so `Vt(u)/u^3` is analytic and the Schwarz lemma gives `|Vt(u)| <= (|u|/R)^3 M_R`,
`M_R = max_{|u'| = R} |Vt(u')|`, for `|u| <= R = 9/10`. On `|u'| = R`:
`Re sqrt(1 - u') > 0`, so `Re(1/(1 + rs)) in (0, 1)` and
`|exp(-hk/(1 + rs))| <= exp(max(-hk, 0))`; `|sqrt(1 - u')| >= sqrt(1/10)`, so the
first term of `Vt` is at most `exp(max(-hk,0)) / sqrt(1/10) <= 3.17 exp(max(-hk,0))`
(`BvnHighPanels.inv_sqrt_tenth`); the second is at most
`exp(-hk/2)(1 + |c| R (1 + |d| R))`, with `|c| <= (4 + |hk|)/8`,
`|d| <= (12 + |hk|)/16`, which is at most `1.8 exp(max(-hk, 0))`
(`BvnHighPanels.fpoly_bound`, for `|hk| <= 1521`). So `M_R <= 4.97 exp(max(-hk, 0))`
and `|Vt(z^2)| <= (4.97 / 0.729) exp(max(-hk,0)) |z|^6 <= 7.2 exp(max(-hk,0)) |z|^6`
(`BvnHighPanels.kappa_arith`). For `hk >= 0`, `|Et| <= 1` in the sector. For
`hk < 0`, `bs >= 4 |hk|` and `Re z^-2 >= 1/2` (`BvnHighPanels.sector_decay`, from
the slope `21/25` and `|z|^2 <= 22/100`) give `|Et| exp(|hk|) <= 1`
(`BvnHighPanels.decay_cancel`). `QED`.

On the real axis the same bound gives `|E V| <= kappa x^6`, so the dropped part
satisfies `int_0^{s} |E V| <= kappa s^7 / 7` for `s <= 0.003`: `2.3e-18`.

**Truncation of a panel of scale `s`.** The filled ellipse lies in `Re z > 0`,
`|z| < 1`, so `E V` is analytic on it; by the maximum modulus principle
`|E V| <= M = kappa (s Z)^6` there (`Z = 123/100` bounds `|zeta|` on the
unit-panel ellipse, `BvnHighPanels.panel_modulus`); and the Gauss-Legendre
remainder bound (theorem T1 of `bivariate_normal_truncation.md`, applied to the
panel of half-length `s/4` with `N` nodes) is

    |panel error| <= (s/4) * 64 M / (15 (1 - rho_E^-2) rho_E^(2 N)),    rho_E = 7/2.

### 3.3 The design

The proved design lists, for `a = 19/50`, the scales `s_i = a / 2^i` and node
counts `N = 15, 13, 11, 9, 7, 5, 3`. The kernel assigns nodes by the scale
class of a panel (`s > 0.19`, `> 0.095`, ...), each class holding at most one
panel because scales halve; the bound grows with `s` for fixed `N`, so every
panel's bound is at most that of its class's top scale and the design's total
covers every `a <= 0.38`. The truncation of the integral, panels plus the part
dropped below `0.003`, is `<= 2 pi * 1e-17` (`BvnHighPanels.design_total_bound`)
and evaluates to `2.08e-17`, below `21e-18` (`BvnHighBudget.design_total_small`):
`3.3e-18` of the result. Measured in exact arithmetic over the peak region the
same rule truncates by `2.2e-22` of the integral: the proof is five orders
conservative (`kappa = 7.2` against a measured supremum of `|E V| / |z|^6` of
`0.40` on the ellipses; the sector limits `rho_E`). A tighter `kappa` or a
larger admissible `rho_E` would shave nodes; the design is the cheapest this
proof supports, not the cheapest that is accurate.

Cost: 63 `exp` pairs at `a = 0.38` against 20 for the previous rule, falling
with `a` (a panel exists only while `s > 0.003`: 6 panels at `a = 0.1`, none
below `0.003`).

### 3.4 Variants considered

* A single rule with more nodes: measured in section 2, not provable by any
  argument found.
* More analytic terms (a third moment `E6`, a fifth `E8`): smaller amplitude `V`,
  but the forward moment recurrence multiplies `bs / (m + 3)` per step, and `V`
  is still flat at zero; no truncation proof follows.
* The low branch's rules extended past `0.925`: limited by `|Re sin t| <= 1` to
  `0.936` at 24 nodes (`bivariate_normal_truncation.md` section 6); the node count
  grows like `a^-1/2` toward 1.
* Owen's `T` decomposition (analytic integrand, Bernstein-provable) needs the
  Patefield-Tandy reduction near `|rho| = 1` and sums several terms of size up
  to one: more roundings than `J / (2 pi) <= 0.066`. Not pursued.

## 4. The rounding budget

### 4.1 Model

`u = 2^-53`. `+, -, *, /` are correctly rounded (`|fl(x) - x| <= half-ulp(x)`,
and `<= 2^-54` on `[0, 1]`). `sqrt` and `exp` are correctly rounded
(`docs/sqrt.md`, `docs/exp.md`). `norm_cdf` has the **documented** contract
`Phi(x)(1 + d)`, `|d| <= 2^-53 + 2^-111` (`NormalPublicEntry.normal_public_contract`,
the proved statement); its fast path is correctly rounded, so the **strong model**
`p = RN(Phi)` is what the code computes whenever the fast path accepts, but it is
not a stated theorem. The machine-checked assembly bounds assume the strong model;
`pos_assembly_weak` is the documented-contract form for `rho > 0`.

### 4.2 The accumulated integral

`J~` is formed as `fl(fl(A1~ - A2~) + remainder~)`. The first-order running error
of the graph (reverse-mode accumulation of `|d result / d v| * half-ulp(v)` over
every intermediate `v`, with the exact value of each) is evaluated by a program
that walks the code's operations; the values below are its maxima over 40 000
samples that include `|rho|` down to one ulp below 1, thresholds from `0.01` to
`38`, and `bs` near zero, then a 3 000-step hill climb from the worst sample.
They are **derived and sampled, not proved**: the sup over the three-parameter
domain is a number a dense search brackets, not a theorem.

| Term of the result's error | Value |
| --- | --- |
| `A1` (`sqrt`, `exp`, the polynomial, three products) | `2.6e-17` |
| `A2` (`exp`, `Phi`, the polynomial, four products) | `2.0e-17` |
| the node sum: per-node cancellation of `G - T`, the node and weight roundings, and the accumulation | `2.9e-17` |
| setup (`ass`, `a`, `bs`, `hk`, `c`, `d`, `asr`) | `1.2e-17` |
| the four jointly maximised | **`7.55e-17`** |

In the integral's units (times `2 pi`) the joint maximum is `4.74e-16`;
`BvnHighBudget.dJ_bound = 5e-16 + 21e-18` rounds it up by five per cent and adds
the proved truncation. **That hypothesis is the one unproved input of the
branch's bound.** The accumulation inside the node-sum row is separately proved
(below) and is a small part of it: the per-node cancellation dominates.

Machine-checked parts (`BvnHighBudget.v`):

* the plain sum of the 63 node terms in a local, one rounding each, rounds by at
  most `63 * 2^-61 = 2.7e-17 <= 3e-17` of the integral (`fsum_error`,
  `remainder_sum_error`), when the partial sums stay below `2^-7`; their absolute
  sum is at most `4.3e-3` (`remainder_magnitude_bound`, from claim K on the real
  axis), below the `5e-3` the lemma uses;
* `TAU` and `SQRT_TAU` as the rationals their bits denote, within `4e-17` and
  `7.4e-17` relative of `2 pi` and `sqrt(2 pi)` (`tau_error`, `sqrt_tau_error`);
* division by `TAU` and its rounding: for `|Jt - J| <= dJ`, `0 <= J <= 21/50`,
  `|rnd(-Jt/TAU) + J/(2 pi)| <= 0.1593 dJ + 1e-17` (`division_step`); `J <= 21/50`
  is `F <= 1/rs <= 1/0.925` times `a <= 0.38` (cited, not mechanised).

### 4.3 The assembly (machine-checked)

`formal/bivariate/BvnHighAssembly.v`, over Flocq's binary64 (`FLT_exp (-1074) 53`,
nearest-even), with the accumulated error as a hypothesis `D` on `g` (the
computed `J~ / TAU` or its negation) and `norm_cdf` correctly rounded
(`p = rnd Phi`). `c54 = 2^-54`.

| Theorem | Assembly | Error bound |
| --- | --- | --- |
| `pos_assembly` | `rho > 0`, `clamp(rnd(g + rnd Pm))` | `D + 2 c54 = D + 1.11e-16` |
| `pos_assembly_weak` | the same, `norm_cdf` within `2 c54` | `D + 3 c54 = D + 1.67e-16` |
| `neg_assembly` | `rho < 0` with a rounded difference (the previous kernel) | `D + (7/2) c54 = D + 1.94e-16` |
| `neg_assembly_dw` | the difference kept as the double-word `s + e` (`TwoSum`), `s + rnd(e + g)` | `D + 3 c54 = D + 1.67e-16` |
| `neg_assembly_dw_half` | the same when `Phi2 < 1/2` | `D + (21/8) c54 = D + 1.46e-16` |
| `neg_assembly_final` | the branch: `p2 < p1`, double-word, else `g`; hypothesis `1/2 <= P2 -> P1 <= P2` | `D + (21/8) c54 = D + 1.46e-16` |

The hypothesis of `neg_assembly_final` is the ordering `dh >= dk` the caller
establishes: if `Phi(dk) >= 1/2` then `dk >= 0`, so `dh >= 0` and
`Phi(-dh) <= 1/2 <= Phi(dk)`. The case analysis: the first `norm_cdf` costs
`c54`, the second `c54/2` (it is below one half whenever the difference is
nonzero), the difference costs nothing (kept exact), the small `e + g` costs
`2^-57`, and the final sum `c54`. When `p1 <= p2` the difference is at most
`2 c54` and `g` alone has error `D + 2 c54`. The `TwoSum` error `e` is exact
(`double-word.md`); the theorem needs only `s + e = p1 - p2` and `|e| <= c54`.

Under the documented (weak) `norm_cdf` contract the same case analysis (not
mechanised) gives `D + 5.1 c54 = D + 2.8e-16` for the previous form of the
`rho < 0` assembly; the two `norm_cdf` terms then cost `2 c54` each.

## 5. Totals

All entries are absolute error of the result.

| | Truncation | Rounding of `J` | Division and constants | Assembly | Total |
| --- | --- | --- | --- | --- | --- |
| `rho > 0` | `3.3e-18` (proved) | `7.9e-17` (sampled) | `1.0e-17` (proved) | `1.11e-16` (proved) | `2.1e-16` |
| `rho < 0` | `3.3e-18` (proved) | `7.9e-17` (sampled) | `1.0e-17` (proved) | `1.46e-16` (proved) | `2.4e-16` |

(`7.9e-17 = 0.1593 * 5e-16`; the total is `0.1593 * 521e-18 + 1e-17 + assembly`,
`BvnHighBudget.high_pos_bound` and `high_neg_bound`, stated as `2.1e-16` and
`2.4e-16`.) These are sums of worst cases that need not coincide. The jointly
maximised first-order running bound of the whole graph (every term and the
assembly together, at the point where they coincide) is `1.99e-16`, sampled.

Observed against the exact value (section 7): the worst error of the branch over
several thousand points near the old peak and over `|rho|` from `0.925` to one
ulp below 1 is `1.1e-16`.

## 6. What is proved, and what is not

**Machine-checked** (`formal/bivariate/`, Coq 8.15.2, Flocq 3.4.3, CoqInterval
4.11.5; no `Admitted`, no new axiom; `Print Assumptions` is in
`formal/audit/KernelAudit.v`):

* `BvnHighAlgebra.v`: `plackett_exponent`, `smooth_exponent`,
  `subtraction_identity`, `moment_closed_form` (the closed form of section 1.4,
  given the moment recurrences as hypotheses), `reflection_phi_terms`.
* `BvnHighAssembly.v`: the rounding lemmas for binary64, the clamp, and the
  six assembly theorems of section 4.3.
* `BvnHighPanels.v`: `panel_design` (the sector and modulus of the panel ellipse,
  the decay lemma, the constants of claim K, and the truncation budget of the
  63-node design). The negative control: with the first panel at 12 nodes the
  budget lemma fails in `interval`.
* `BvnHighBudget.v`: the constants, the accumulation, the division, the design's
  truncation, and `high_pos_bound` and `high_neg_bound`, which compose them with
  the assembly, as functions of the single hypothesis `|Jt - J| <= dJ_bound`.

**Cited, not formalised:** the Gauss-Legendre remainder bound for analytic
integrands (T1 of `bivariate_normal_truncation.md`); the maximum modulus
principle and the Schwarz lemma; analyticity of `E V` on the panel ellipse (the
branch of `sqrt(1 - z^2)` and `Re sqrt > 0`); Plackett's identity and the change
of variable of section 1.2; the base moment `int_0^a exp(-bs/(2x^2)) dx =
a ea - b sqrt(2 pi) Phi(-b/a)` and the integration-by-parts recurrences; the
exact rational check that `c, d` are the Taylor coefficients (four values of
`hk`); `J <= 21/50`; that the node terms' deviation from the exact ones leaves
their absolute sum below `5e-3`.

**Derived, not proved:** the rounding of `A1`, `A2`, the setup and the node
brackets (section 4.2: a sampled maximum of a first-order running bound, plus
second-order terms below `1e-30`); the cutoffs of A3; the weak-model assembly
constant; the cost estimate of section 3.3.

**Measured, not proved:** the truncation of a single rule (section 2); the
exact-arithmetic truncation of the panel design (`2.2e-22` of the integral); the
observed errors.

**Assumed:** the strong `norm_cdf` model for the assembly theorems; `exp` and
`sqrt` correctly rounded; no overflow or underflow other than the cutoffs of A3,
where a result below `2^-1022` has an absolute error below `2^-1074`, which the
result's bounded sensitivity to any one intermediate (not mechanised) keeps below
`1e-300`.

**What closing the sampled term needs.** A proof of the `5e-16` hypothesis is a
bound on the first-order running error of about 600 operations over a
three-parameter domain spanning `|rho|` from `0.925` to one ulp below 1,
thresholds to `39`, and `bs/a^2` from 0 to `10^4`. A crude term-by-term bound
(each rounded operation weighted by the supremum of the magnitude it multiplies)
was not pursued: its excess over the sampled joint maximum, which comes from the
per-node bracket `G - T` and from `A1`, `A2` peaking at different points, would
exceed the budget.

## 7. Evidence and reproduction

* The previous kernel's counterexample, the peak table and the node-count table
  of section 2 are exact-arithmetic computations (`mpmath`, 25 to 60 digits).
* The kernel of this note against the exact Plackett integral (30 to 40 digits)
  at `|rho|` in `{0.925, 0.9250000000000002, 0.93, 0.94, 0.954, 0.9755, 0.995,
  0.9999, 1 - 2^-30}`, both signs, thresholds from the peak region to `+-3`: the
  worst error of 7 500 points is `1.1e-16`, and `3.6e-17` at the counterexample.
* `high_correlation_peak_rows_meet_the_published_bound` in `tests.rs` asserts the
  `2.5e-16` bound on 25 rows with reference values to 45 digits; the reference
  fixture of `crates/reference` covers the branch's adjacent doubles.
