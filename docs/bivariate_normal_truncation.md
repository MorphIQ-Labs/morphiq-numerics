# Quadrature truncation of the bivariate normal's low-correlation rule

This note proves a bound on the truncation term of `docs/bivariate_normal.md`
section 6 for the Gauss-Legendre rule of the low-correlation regime. It covers
that one term. Rounding of the nodes, weights, `asin`, `sincos`, `exp`, the
sum and the high-correlation `BVND` branch are not covered here. It also
proves the rule table that its premises support, which is **not** the table in
the source (section 6).

## 1. Statement

Let `I(a) = int_0^a f(t) dt`, `f(t) = exp(-Q(t))`,
`Q(t) = (x^2 + y^2 - 2 x y sin t) / (2 cos^2 t)`, and let `S_N(a)` be the
`N`-node Gauss-Legendre sum on `[0, a]` (exact nodes and weights). For a rule
with correlation limit `L` and the parameters of section 5,

    |S_N(a) - I(a)| <= 2 pi * 2e-17 = 1.2566e-16   for every real x, y and every 0 < a <= asin L,

and the same for `a < 0` by `t -> -t`. Dividing by `2 pi` is the quantity in
`docs/bivariate_normal.md`. No threshold restriction is needed: the proof does
not use `|x|, |y| <= 39`, so the saturating range is covered too.

## 2. Derivation

Write `r = x^2 + y^2` and `k = 2xy / r` (`|k| <= 1`; for `r = 0` the
integrand is 1 and the rule is exact). With `s = sin t`, `cos^2 t = 1 - s^2`,

    Q = r g(s),   g(s) = (1 - k s) / (2 (1 - s^2)),

and `g` is affine in `k`. For `s = X + iY`, with `D = 1 - s^2 = (1 - X^2 + Y^2) - 2iXY`,

    Re g = [(1 - kX)(1 - X^2) + Y^2 (1 + kX)] / (2 |D|^2).

If `|X| <= 1` and `|k| <= 1` the bracket is nonnegative (each factor is), so
`Re Q >= 0` and `|f(t)| = exp(-Re Q) <= 1`. For `t = u + iv`,
`X = Re sin t = sin u cosh v`.

Map `[0, a]` to `[-1, 1]` by `t = (a/2)(1 + tau)`. The Bernstein ellipse of
parameter `rho` for `[-1, 1]` is the image of `|w| = rho` under
`tau = (w + 1/w)/2`; in `t` it is the curve
`u = a/2 + a (rho + 1/rho) cos(th) / 4`, `v = a (rho - 1/rho) sin(th) / 4`,
`th in [0, pi]` (the lower half is its mirror, with the same `X`). It is
`a * E`, a homothety of one fixed ellipse about `t = 0`, which lies inside it.
Hence for `0 < a' <= A` the ellipse for `[0, a']` lies in the filled ellipse
for `[0, A]`.

**Premises checked for one `(A, rho)`:**

1. (extent) `A (rho + 1)^2 / (4 rho) < 1.5707` and `A (rho - 1)^2 / (4 rho) < 1.5707`:
   the filled ellipse lies in `|u| < pi/2`, so `cos u > 0`, `|cos t|^2 = cos^2 u + sinh^2 v > 0`,
   and `f` is analytic on a neighbourhood of it.
2. (modulus) `-1 <= sin u cosh v <= 1` on the boundary. By the maximum modulus
   principle `|f| <= 1` on the filled ellipse, for every `|k| <= 1`.
3. (budget) `(A/2) * 64 / (15 (1 - rho^-2) rho^(2N)) <= 1.2566e-16`.

**Cited theorems (not formalised; the formal files do not assume them):**

* **T1.** Trefethen, *Is Gauss quadrature better than Clenshaw-Curtis?*, SIAM
  Review 50 (2008), Theorem 4.5, eq. (4.14): for `f` analytic with `|f| <= M`
  in the region bounded by the ellipse with foci `+-1` and semi-axes summing to
  `rho > 1`, the `(n+1)`-point Gauss rule satisfies
  `|I - I_n| <= 64 M / (15 (1 - rho^-2) rho^(2n+2))`. With `N = n + 1`
  points the exponent is `2N`. (Attributed there to Rabinowitz; sharpened proof
  in that paper's section 5.) Scaling to `[0, a']` multiplies the error by `a'/2`.
* **T2.** Maximum modulus principle.
* **T3.** Gauss-Legendre nodes and weights are the exact ones (the rounding of
  the stored nodes is a separate term).
* **T4.** `Re sin(u + iv) = sin u cosh v`, `Im sin(u + iv) = cos u sinh v`.

Combining: with `M = 1` and the error scaling `a'/2 <= A/2`,
`|S_N(a') - I(a')| <= (A/2) 64 / (15 (1 - rho^-2) rho^(2N))`, premise 3.

## 3. Why a larger `M` is not needed

`Re g >= 0` on the whole ellipse removes the growth of `|exp(-Q)|` that the
earlier note feared (section 4 of `bivariate_normal.md`): the singularities
at `t = +-pi/2` are never inside the ellipse and the exponent has a
nonnegative real part on it, for every `x, y`. The price is the largest
admissible `rho`: it is set by `|Re sin t| <= 1` (about 2.2 at `N = 24`), not by
the distance to `pi/2`. I also evaluated, numerically and without relying on it,
ellipses that allow `Re g < 0` with `M = exp(r delta)` and `r`-dependent `rho`,
and the trivial large-`r` bound `2a exp(-r / (2(1 + |rho|)))`; at the
nodes-and-limits sizes of the table they gave no larger provable limit than the
single `M = 1` ellipse (differences below 0.002 in `|rho|`), so the proof keeps
the simpler one.

## 4. Machine-checked (`formal/bivariate/`)

Coq 8.15.2, CoqInterval 4.11.5 (image `ff-coq:local`), no `Admitted`, no
added axioms (the assumptions are Coq's real-number axioms and the primitive
integer/float specifications CoqInterval's `interval` tactic reaches; this
tree's audit lists the same families).

* `BvnEllipse.v`: the algebra of section 2 (`num_re_g_factor`,
  `re_g_nonneg`: `|k| <= 1, |X| <= 1 => 0 <= num_re_g k X Y`;
  `den_re_g_pos`), the ellipse parametrisation, `ellipse_ok` (`-1 <= Re sin t <= 1`
  for all `th in [0, pi]`), `ellipse_inside`, `trunc_bound`.
* `BvnRules.v`: for each `N` in the table below, `sin A >= L + 2e-4`
  (so `A >= asin L` plus margin), `inside_N`, `ellipse_N` (interval arithmetic
  with bisection on `th`) and `bound_N` (premise 3).
* `BvnTruncation.v`: `certified N L A rho` and the nine theorems
  `certified_N`.

**Not machine-checked:** T1 to T4; the identification of Coq's real
expressions with the complex integrand (`g(s)` and `Re sin`); that the filled
ellipse is `a * E`; that `L` is the double the code compares with (the margin
`2e-4` in `sin A` covers the decimal-to-double gap by many orders). These are the
paper steps of section 2. The negative control (`ellipse_ok` at `A = 1.0979`,
`rho = 2.9`) fails in `interval`, so the tactic is not vacuous.

## 5. Proved rule table

Per rule: the correlation limit `L`, the angle bound `A`, the ellipse
parameter, the largest `|Re sin t|` on the ellipse (numerical, below 1 is the
premise), and the proved truncation bound `(A/2) 64/(15 (1-rho^-2) rho^(2N)) / (2 pi)`,
to be compared with `2e-17`.

| `N` | `|rho|` up to `L` | `A` | `rho_E` | max `|Re sin t|` | proved bound / `2 pi` |
| --- | --- | --- | --- | --- | --- |
| 4 | 0.055 | 0.0556 | 76.8 | 0.937 | 1.6e-17 |
| 6 | 0.200 | 0.2019 | 20.2 | 0.948 | 1.5e-17 |
| 8 | 0.380 | 0.3903 | 9.9 | 0.968 | 1.6e-17 |
| 10 | 0.540 | 0.5710 | 6.38 | 0.983 | 1.6e-17 |
| 12 | 0.660 | 0.7214 | 4.73 | 0.986 | 1.6e-17 |
| 14 | 0.750 | 0.8486 | 3.82 | 0.993 | 1.6e-17 |
| 16 | 0.810 | 0.9447 | 3.25 | 0.991 | 1.5e-17 |
| 20 | 0.890 | 1.0979 | 2.59 | 0.996 | 1.3e-17 |
| 24 | 0.925 | 1.1816 | 2.22 | 0.989 | 1.2e-17 |

(the sixth column is Coq-proved in the form `<= 2 pi * 2e-17`; the printed
values are from the same formula in double precision.)

## 6. Relation to the shipped table

The source's limits are 0.06, 0.22, 0.40, 0.55, 0.70, 0.80, 0.85 and below
0.925 for 4, 6, 8, 10, 12, 14, 16 and 20 nodes. The Bernstein estimate proves
the truncation budget only up to (numerical maxima over the same estimate, before margin)

| nodes | 4 | 6 | 8 | 10 | 12 | 14 | 16 | 20 | 24 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| largest `|rho|` | 0.0598 | 0.2131 | 0.3940 | 0.5507 | 0.6706 | 0.7589 | 0.8196 | 0.8965 | 0.9362 |

so the shipped limits of 0.06 (4), 0.22, 0.40, 0.55 (at the edge), 0.70,
0.80, 0.85 and 0.925 (20 nodes) are **not** covered by this proof; the
measured errors of section 4 of `bivariate_normal.md` are smaller than this
bound by a factor of about 3 near the top limits, which a sharper argument
might close, but none is proved here. The table of section 5 is covered,
using one additional rule (24 nodes) for `0.89 < |rho| < 0.925`.
