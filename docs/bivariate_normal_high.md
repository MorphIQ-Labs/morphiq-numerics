# The high-correlation branch of the bivariate normal: decomposition, truncation, rounding

`high_correlation(dh, dk, rho)` in `crates/morphiq-numerics/src/bivariate_normal/mod.rs`
serves `0.925 <= |rho| < 1`. This note writes out the exact mathematics the
branch evaluates, bounds each error it commits, and says what is proved, what is
only measured, and what fails. It supplements `docs/bivariate_normal.md`
(sections 3 and 6) and `docs/bivariate_normal_truncation.md` (the low branch).

## 0. Verdict

| Question | Answer |
| --- | --- |
| Does the shipped branch meet `ABSOLUTE_ERROR_BOUND = 2.5e-16`? | **No.** `bivariate_norm_cdf(-0.21101192279835226, -0.0014549743776884816, 0.925)` is `2.5794e-16` from the exact probability (section 2.3), against two independent references. |
| Why? | The 20-node Gauss-Legendre rule of the remainder integral truncates by up to `1.93e-16` (result units) at `|rho| = 0.925` (section 2.2); the same rule cannot be bounded by a Bernstein ellipse (section 2.1); the rounding terms add up, in the sum of their worst cases, to `2.8e-16` (`rho > 0`) and `3.6e-16` (`rho < 0`) (sections 4 and 5). |
| Is a bound proved for the shipped kernel? | **No**, and none is provable for its truncation by the method of `bivariate_normal_truncation.md`. What is proved is the structure of the final lines (section 5), the decomposition identities (section 1) and the certificate of a replacement quadrature (section 3). |
| Is there a provable replacement? | Yes: graded panels, 63 nodes at the worst correlation. Its truncation is bounded by `3.3e-18` (section 3). The accumulated worst cases then sum to `2.6e-16` (proved assembly plus derived terms) and the jointly maximised first-order running bound is `1.99e-16`, plus `1e-17` for the constants and the truncation (derived, sampled, not proved). A published bound of `2.5e-16` is **not** defensible by the additive argument; `3.0e-16` is. Section 5 has the table. |

Everything below states its status. Nothing is claimed beyond it.

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
singularity there, which section 2 shows is what a polynomial rule cannot
resolve.

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

### 1.5 The remainder integral and what the code evaluates

`R = int_0^a E V dx` is evaluated by a 20-node Gauss-Legendre rule on `[0, a]`,

    R ~ (a/2) sum_{i=1}^{20} w_i E(x_i) V(x_i),    x_i = (a/2)(1 + t_i),

in the code as ten `+-` node pairs, each term
`a/2 * w * exp(asr_i) * (exp(-hk x^2 / (2 (1 + rs)^2)) / rs - (1 + c x^2 (1 + d x^2)))`.
Then `bvn = -(A1 - A2 + R) / TAU` and the result is `bvn + Phi(-max(dh, dk))`
(`rho > 0`) or `-bvn + max(Phi(-dh) - Phi(dk), 0)` (`rho < 0`), clamped to `[0, 1]`.

### 1.6 The approximations made

| # | Approximation | Size |
| --- | --- | --- |
| A1 | the 20-node rule for `R` (truncation) | section 2: up to `1.93e-16` in the result; **the defect** |
| A2 | shipped nodes and weights are the binary64 roundings of the exact ones | `<= 2 * 2^-53 * int |E V| < 1e-19` (`int |E V| <= 6e-5`, measured) |
| A3 | `A1` dropped when `asr <= -100`; `A2` dropped when `hk <= -100`; a node dropped when its `asr_i <= -100` | each `< 1e-38` (derived, not mechanised): the dropped term is at most `e^-100 = 3.7e-44` times a polynomial in `(bs/a^2, hk)` that is below `1e4` where a cutoff applies; for `hk <= -100`, `bs >= -4 hk` forces `asr <= -150` |
| A4 | the constants: `TAU` is `2 pi (1 - 3.90e-17)`, `SQRT_TAU` is `sqrt(2 pi) (1 + 7.31e-17)` | effect `<= 2.5e-18` and `<= 4.6e-18` of the result |
| A5 | every rounded operation | section 4 |
| A6 | the final clamp to `[0, 1]` | never increases the error (`BvnHighAssembly.clamp_lipschitz`) |

## 2. Truncation of the shipped rule

### 2.1 No Bernstein ellipse

`docs/bivariate_normal_truncation.md` bounds a Gauss-Legendre remainder by the
Bernstein ellipse of the interval, which must lie in a region where the
integrand is analytic. The ellipse of `[0, a]` for any parameter `> 1` contains
`x = 0` in its interior, and `E(z) = exp(-bs/(2 z^2) - hk/2)` has an essential
singularity there that is unbounded along the imaginary axis
(`|E(i y)| = exp(bs/(2 y^2) - hk/2)`). For `bs > 0` no ellipse exists, so the
low branch's method does not apply. A derivative (Peano-kernel) bound with
Cauchy estimates on discs of radius `kappa x` fails too: the discs must stay in the
sector `|arg z| < pi/4`, `kappa < 0.71`, and `40! kappa^-40` swamps the kernel
away from the first node. The convergence of Gauss quadrature on a flat
function is sub-geometric, and the sup over the parameters `(bs, hk, a)` of the
remainder has no closed form.

### 2.2 Measured

Exact arithmetic, 25 to 50 digits (the rule's own exact nodes; `R` against
adaptive quadrature of `E V` over `[0, a]`). The truncation of the result,
`(rule - R) / (2 pi)`, maximised over `bs` at `hk = 0` (where it peaks;
at `a = 0.38`, `hk > 0` and `hk < 0` are smaller):

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

At `a = 0.38`, `hk = 0`, the truncation for a single rule of `N` nodes is
`1.9e-16` (`N = 20`, shipped), `1.8e-17` (24), `1.5e-18` (28), `4.5e-19` (32),
`1.4e-20` (40), `3.5e-22` (48): it falls steadily, but no `N` has a proof here.
The bound `2.5e-16` leaves `0.57e-16` for everything but truncation, and the
rounding terms of section 4 are of that size.

### 2.3 The counterexample

    bivariate_norm_cdf(x, y, rho) with
      x   = -0.21101192279835226   (0xbfcb02704dbe1479)
      y   = -0.0014549743776884816 (0xbf57d69ad7989ddc)
      rho =  0.925                 (0x3fed99999999999a, a double above 0.925)
    returns 0.38767043158686953    (0x3fd8cf97a452ad04)
    exact   0.387670431586869792906995560869
    error   -2.5794e-16            (4.6 ulp; the bound is 2.5e-16)

The exact value is the Plackett angle integral at 60 digits and, independently,
the conditional integral `int phi(t) Phi((y - rho t) / sqrt(1 - rho^2)) dt` over
`(-inf, x]`; they agree to all 30 printed digits. `rho = 0.925` is a double
whose `Regime::of` is `High`; `(dh, dk) = (0.211..., 0.00145...)`, so
`hk = 3.07e-4`, `bs = 0.0439 = 0.304 a^2`: the peak of section 2.2. A fixture row for it
belongs in `crates/reference/fixtures/bivariate_normal.json`; the 3 000 random
high-regime cases of `docs/bivariate_normal.md` section 6 (worst `1.11e-16`) do
not sample the peak. An exact-arithmetic scan of 500 points around it finds
`2.40e-16`, `2.36e-16`, `2.35e-16`, and a scan of 1 500 points `2.58e-16`.

## 3. A replacement whose truncation is provable: graded panels

This section describes a quadrature that is **not** in the tree. It is the
smallest change found that makes the truncation provable.

### 3.1 The structure

Cover `[0, a]` by the panels `[s_i / 2, s_i]`, `s_i = a / 2^i`, `i = 0 .. P - 1`,
each with its own Gauss-Legendre rule of `N_i` nodes (the unit-panel nodes
scaled by `s_i`; the tables are shared), and drop `[0, s_P]`. Each panel is
short enough that its Bernstein ellipse stays in the sector `|Im z| <= (21/25) Re z`
(about `40` degrees) of the right half plane, where `|exp(-bs/(2 z^2))| <= 1`
because `Re z^-2 = (x^2 - y^2)/(x^2 + y^2)^2 > 0`. The ellipse of the unit panel
`[1/2, 1]` with parameter `7/2` is `u = 3/4 + (53/112) cos th`,
`v = (45/112) sin th`; every panel's ellipse is its homothetic image, so one
check serves all.

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
satisfies `int_0^{s_P} |E V| <= kappa s_P^7 / 7`.

**Truncation of panel `i`.** The filled ellipse lies in `Re z > 0`, `|z| < 1`, so
`E V` is analytic on it; by the maximum modulus principle `|E V| <= M_i =
kappa (s_i Z)^6` there (`Z = 123/100` bounds `|zeta|` on the unit-panel ellipse,
`BvnHighPanels.panel_modulus`); and the Gauss-Legendre remainder bound (theorem
T1 of `bivariate_normal_truncation.md`, applied to the panel of half-length
`s_i / 4` with `N_i` nodes) is

    |panel error| <= (s_i/4) * 64 M_i / (15 (1 - rho_E^-2) rho_E^(2 N_i)),    rho_E = 7/2.

### 3.3 The design and its numbers

| panel `i` | 0 | 1 | 2 | 3 | 4 | 5 | 6 |
| --- | --- | --- | --- | --- | --- | --- | --- |
| nodes `N_i` | 15 | 13 | 11 | 9 | 7 | 5 | 3 |

63 nodes at `a = 0.38`; the bound on the truncation of `J`, panels plus the
dropped `[0, a/128]`, is `<= 2 pi * 1e-17` (`BvnHighPanels.design_total_bound`),
that is `<= 1e-17` of the result. Evaluated, the bound is `2.08e-17` for `J`
(`3.3e-18` of the result). The same rule measured in exact arithmetic over the
peak region of section 2.2 truncates by `2.2e-22` of `J`: the proof is five
orders conservative (`kappa = 7.2` against a measured supremum of `|E V| / |z|^6`
of `0.40` on the ellipses; the sector, rather than the singularity, limits
`rho_E`). A tighter `kappa` or a larger admissible `rho_E` would shave nodes; the
design is the cheapest this proof supports, not the cheapest that is accurate.
The number of panels falls with `a`: panel `i` needs `N_i` falling by about one
node per halving of its scale (a factor of `2^7` in amplitude), and
`a < a_0 / 2^P`, `a_0 / 2^P = 0.38 / 128 = 0.003`, needs no quadrature at all:
the dropped part alone is below `2e-18 (a / 0.003)^7`.

Cost: 63 `exp` pairs against 20 at the worst correlation, about three times the
branch's present work there, fewer for larger `|rho|`. The branch is also
`O(1)` in the number of strikes; the node loop is the only change.

### 3.4 Other variants considered

* A single rule with more nodes: measured in section 2.2, **not provable** by any
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
not a stated theorem, and every bound below is given for both.

### 4.2 The accumulated integral

`J~` is formed as `A1~ - A2~ + sum`. The first-order running error of the graph
(reverse-mode accumulation of `|d result / d v| * half-ulp(v)` over every
intermediate `v`, with the exact value of each) is evaluated by a program that
walks the code's operations; the values below are its maxima over 40 000 samples
that include `|rho|` down to one ulp below 1, thresholds from `0.01` to `38`, and
`bs` near zero, then a 3 000-step hill climb from the worst sample. They are
**derived and sampled, not proved**: the sup over the three-parameter domain is
a number a dense search brackets, not a theorem.

| Term of the result's error | Shipped (recursive accumulation) | Replacement (separate accumulator) |
| --- | --- | --- |
| `A1` (`sqrt`, `exp`, the polynomial, three products) | `2.6e-17` | `2.6e-17` |
| `A2` (`exp`, `Phi`, the polynomial, four products) | `2.0e-17` | `2.0e-17` |
| the node sum: per-node cancellation of `G - T` and the accumulation | `1.13e-16` | `2.9e-17` |
| setup (`ass`, `a`, `bs`, `hk`, `c`, `d`, `asr`) | `1.2e-17` | `1.2e-17` |
| the sum of the four, maximised jointly | `1.56e-16` | `7.6e-17` |

The shipped code adds every node's term to `bvn`, which is of size up to `0.41`
(`J <= 0.41`, from `F <= 1/rs` and `a <= 0.38`): each of the 20 additions rounds
by up to half-ulp(`0.4`) `= 2.8e-17`, a worst case of `5.6e-16` in `J`, `9e-17`
in the result, even though the terms themselves sum to `< 6e-5` (measured). The replacement
sums the 20 (or 63) terms first, in an accumulator of size `< 6e-5`, and adds it
once. This is one change to the loop and removes `8e-17`.

### 4.3 The constants and the division

Beyond the table: `bvn = -J~ / TAU` rounds once (`<= 2^-57` of the result, `|g| <
0.066`), `TAU` carries `2.5e-18`, `SQRT_TAU` `4.6e-18`; the clamp changes nothing.

### 4.4 The assembly (machine-checked)

`formal/bivariate/BvnHighAssembly.v`, over Flocq's binary64 (`FLT_exp (-1074) 53`,
nearest-even), with the accumulated error as a hypothesis `D` on `g` (the
computed `J~ / TAU` or its negation) and `norm_cdf` correctly rounded
(`p = rnd Phi`). `c54 = 2^-54`.

| Theorem | Assembly | Error bound |
| --- | --- | --- |
| `pos_assembly` | `rho > 0`, `clamp(rnd(g + rnd Pm))` | `D + 2 c54 = D + 1.11e-16` |
| `pos_assembly_weak` | the same, `norm_cdf` within `2 c54` | `D + 3 c54 = D + 1.67e-16` |
| `neg_assembly` | `rho < 0` as shipped: two `norm_cdf`, a rounded difference, the sum | `D + (7/2) c54 = D + 1.94e-16` |
| `neg_assembly_dw` | `rho < 0` with the difference kept as the double-word `s + e` (`TwoSum`), `s + rnd(e + g)` | `D + 3 c54 = D + 1.67e-16` |

The case analysis behind `neg_assembly`: the two `norm_cdf` errors are each
`<= c54` (`<= c54/2` when the value is below `1/2`); the subtraction is exact
(Sterbenz) when `p2 >= p1/2`, and otherwise `p2 < 1/2`, so the three roundings
are `c54 + c54/2 + c54` and the final sum adds `c54`: `7/2 c54`. When the
difference is exact the errors are `c54 + c54 + c54`. The hypotheses are the
actual structure of the branch: `p_i = rnd Phi_i`, `0 <= Phi_i <= 1`,
`0 <= G + max(0, Phi_1 - Phi_2) <= 1`, `|g - G| <= D`, and for the double-word
form `g` is a float with `|g| <= 1/10` (`J / (2 pi) <= 0.066`). The `TwoSum` error
`e` is exact (`double-word.md`); the theorem needs only `s + e = p1 - p2`.

Under the documented (weak) `norm_cdf` contract the same case analysis
(not mechanised) gives `D + 5.1 c54 = D + 2.8e-16` for `neg_assembly` and for
`neg_assembly_dw`: the two `norm_cdf` terms each cost `2 c54`. So **no** accounting
of this structure reaches `2.5e-16` without the strong model.

A further reduction, derived but not mechanised: when both `norm_cdf` values are
at least `1/2` the difference `Phi(-h) - Phi(k)` equals `Phi(-k) - Phi(h)`, whose
operands are at most `1/2` and carry `c54 / 2` each, so only the mixed case
(`Phi(-h) >= 1/2 > Phi(k)`) remains, at `(5/2) c54 = 1.39e-16`.

## 5. Totals

All entries are absolute error of the result.

| | Truncation | Rounding of `J` and constants | Assembly | Sum of worst cases |
| --- | --- | --- | --- | --- |
| Shipped, `rho > 0` | `1.9e-16` (measured) | `1.56e-16 + 1.5e-17` | `1.11e-16` | `4.7e-16` |
| Shipped, `rho < 0` | `1.9e-16` (measured) | `1.56e-16 + 1.5e-17` | `1.94e-16` | `5.5e-16` |
| Panels + separate sum, `rho > 0` | `3.3e-18` (proved) | `7.6e-17 + 1.5e-17` | `1.11e-16` | `2.1e-16` |
| Panels + separate sum + double-word difference, `rho < 0` | `3.3e-18` (proved) | `7.6e-17 + 1.5e-17` | `1.67e-16` | `2.6e-16` |
| the same with the complementary difference | `3.3e-18` | `7.6e-17 + 1.5e-17` | `1.39e-16` | `2.3e-16` |

The first two rows are not bounds: the truncation is a measured maximum, the rest
are worst cases that need not coincide. The observed worst error of the shipped
branch is `2.58e-16`. The jointly maximised first-order running bound of the
whole graph (`J` terms, constants and assembly together, at the point where they
actually coincide) is `1.99e-16` for panels plus separate sum plus double-word
difference, `1.97e-16` without the double-word, `2.76e-16` shipped, and with the
weak `norm_cdf` model `2.44e-16`, `2.73e-16` and `2.96e-16`. These joint figures
are sampled, so the sum of worst cases (which is proved only in its truncation
and assembly parts) is the defensible upper bound:

* **`2.5e-16` cannot be defended for the whole function** by the additive
  argument, even with every proposed change, unless the complementary difference
  is also adopted and `norm_cdf` is stated to be nearest-rounded (`2.3e-16`, a
  margin of 8 per cent that rests on the sampled `J` term).
* **`3.0e-16` can**: the additive worst case of the replacement is `2.6e-16`.
* The published bound is the maximum over the two branches; this one is the
  binding branch, and the rounding of the final assembly, not the quadrature, is
  what binds it once the truncation is proved.

## 6. What is proved, and what is not

**Machine-checked** (`formal/bivariate/`, Coq 8.15.2, Flocq 3.4.3, CoqInterval
4.11.5; no `Admitted`, no new axiom; `Print Assumptions` is in
`formal/audit/KernelAudit.v`):

* `BvnHighAlgebra.v`: `plackett_exponent`, `smooth_exponent`,
  `subtraction_identity`, `moment_closed_form` (the closed form of section 1.4,
  given the moment recurrences as hypotheses), `reflection_phi_terms`.
* `BvnHighAssembly.v`: the rounding lemmas for binary64 (`rnd_err_unit`,
  `rnd_err_half`, `rnd_err_eighth`), the clamp (`clamp_lipschitz`, `round_clamp`),
  and `pos_assembly`, `pos_assembly_weak`, `neg_assembly`, `neg_assembly_dw`.
* `BvnHighPanels.v`: `panel_design` (the sector and modulus of the panel ellipse,
  the decay lemma, the constants of claim K, and the truncation budget of the
  63-node design). The negative control: with the first panel at 12 nodes the
  budget lemma fails in `interval`.

**Cited, not formalised:** the Gauss-Legendre remainder bound for analytic
integrands (T1 of `bivariate_normal_truncation.md`); the maximum modulus
principle and the Schwarz lemma; analyticity of `E V` on the panel ellipse (the
branch of `sqrt(1 - z^2)` and `Re sqrt > 0`); Plackett's identity and the change
of variable of section 1.2; the base moment `int_0^a exp(-bs/(2x^2)) dx =
a ea - b sqrt(2 pi) Phi(-b/a)` and the integration-by-parts recurrences; the
exact rational check that `c, d` are the Taylor coefficients (four values of `hk`).

**Derived, not proved:** the rounding of `J` (table of section 4.2: a sampled
maximum of a first-order running bound, plus second-order terms below `1e-30`);
the cutoffs of A3; the weak-model assembly constant; the complementary-difference
reduction; the cost estimate of section 3.3.

**Measured, not proved:** the truncation of the shipped rule and of any single
rule (section 2.2); the exact-arithmetic truncation of the panel design
(`2.2e-22` of `J`); the worst observed error (`2.58e-16`).

**Assumed:** the strong `norm_cdf` model for the `D + 2 c54` and `D + 3 c54`
statements (the weak model is the documented contract); `exp` and `sqrt` correctly
rounded; no overflow or underflow other than the cutoffs of A3, where a result
below `2^-1022` has an absolute error below `2^-1074`, which the result's bounded sensitivity to any one intermediate (not mechanised) keeps below `1e-300`.

## 7. Defects found and the change they call for

1. **Truncation** (section 2): the published bound is false. Root cause: a
   polynomial rule on an integrand that is flat at an endpoint with an essential
   singularity there; the safeguards missed it because the 3 000 random
   high-regime cases of `bivariate_normal.md` section 6 do not sample the peak
   (`|rho| = 0.925`, `hk ~ 0`, `bs / a^2 ~ 0.3`), where the truncation is
   `1.9e-16`. Prevents recurrence: a fixture row at the peak and the panel
   certificate.
2. **Accumulation**: `bvn += term` inside the node loop rounds each of 20
   additions by up to half-ulp of an `O(0.4)` accumulator (worst case `9e-17`
   of the result, sampled `8e-17`). Fix: sum the node terms in a local first and
   add once; the terms are `< 6e-5`.
3. **Assembly for `rho < 0`**: two `norm_cdf` roundings, a rounded difference and
   a rounded sum cost up to `3.5 * 2^-54 = 1.94e-16`; with the documented
   `norm_cdf` contract, `2.8e-16`. Fix: keep the difference as a double-word
   (`TwoSum`, `eft.rs`) and add `g` to it once (`neg_assembly_dw`), and, where
   both `norm_cdf` values are at least a half, use the complementary pair.
4. **Documentation**: `bivariate_normal.md` section 6 reports the `2.5e-16` bound
   as measured and section 1 lists the high branch's proof as not done; section
   3 says the branch "was verified against the reference at the classifier's
   adjacent doubles"; none of it records the peak. This note replaces those
   statements once the kernel changes.
5. **Not a kernel defect, noted**: `formal/bivariate/.BvnEllipse.aux` and
   `formal/bivariate/.nra.cache` are tracked build artefacts.

A search for siblings in `mod.rs` found the same recursive accumulation nowhere
else (the low branch already uses a double-word), and no other quadrature over a
flat endpoint. The transcription itself is correct: every line of
`high_correlation` was matched to section 1 (the exponents, `c`, `d`, the two
closed-form terms with their signs, the node scaling, the reflection) and
agrees with the reference to the truncation and rounding above at the 2 300 points
tried.

## 8. Reproduction

The counterexample of section 2.3 is a single call. The exact value: with
`mpmath` at 60 digits, `P = Phi(x) Phi(y) + (1/(2 pi)) int_0^{asin rho}
exp(-(x^2 + y^2 - 2 x y sin t) / (2 cos^2 t)) dt`, and independently
`int_{-inf}^x phi(t) Phi((y - rho t) / sqrt(1 - rho^2)) dt`. The truncation
table of section 2.2 is `(a/2) sum w E V(x_i)` against `int_0^a E V` with
`E V` as in section 1.3, `hk = 0`, `bs = 0.3 a^2`, at 28 digits.
