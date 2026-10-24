# Absolute error of the low-correlation branch

This note derives and states the proved absolute error bound of
`BivariateNormal::low` (`|rho| < 0.925`) as the kernel computes it, and records
what the proof assumes. It does not cover the high-correlation `BVND` branch or
the closed-form regimes. The machine-checked statement is
`formal/bivariate/BvnTop.v` (`low_branch`), specialised per rule in
`BvnBudget.v` (`low_N`).

## 1. The computation that is bounded

For ordered finite `x <= y`, `|x|, |y| <= 64`, and a rule `N` selected by
`|rho|` (`docs/bivariate_normal_truncation.md` section 5). Table build, per
correlation (`fl` is binary64 round to nearest even, every operation below is
one rounding):

    asr  = asin(rho)                               (contract, section 4)
    K    = fl(asr / (2 TAU))                       TAU = fl(2 pi)
    for each node i (the positive abscissa x_i with sign +1, then -1):
      th_i = fl(fl(asr * fl(sgn x_i + 1)) / 2)
      s_i  = sin(th_i)                             (contract)
      p_i  = fl(0.25 / fl(1 - s_i)),  q_i = fl(0.25 / fl(1 + s_i))
      kw_i = fl(w_i * K)                           w_i the stored weight

Evaluation, per `(x, y)`:

    d = fl(fl(x - y)^2),  m = fl(fl(x + y)^2)
    term_i = fl(kw_i * exp(-fl(fl(d p_i) + fl(m q_i))))
    (H, L) = two_sum accumulation of the term_i, L = fl(L + e) in node order
    (hi, lo) = two_prod(Phi(x), Phi(y))            lo = 0 below 1e-270
    (s, e)   = two_sum(hi, H)
    R = clamp(fl(s + fl(e + fl(L + lo))), 0, 1)

The exponent `d p + m q` is `(x^2 + y^2 - 2 x y sin t)/(2 cos^2 t)` written as
a sum of two non-negative terms (`d = r - 2p`, `m = r + 2p`,
`r/2 - p s = (d (1 + s) + m (1 - s))/4`), so it has no cancellation and needs no
cosine. The result is rounded **once**, at the last addition.

The exact target is `P = Phi(x) Phi(y) + (1/2 pi) int_0^{asin rho} f`,
`f(t) = exp(-(x^2 + y^2 - 2 x y sin t) / (2 cos^2 t))`.

## 2. Derivation

* **Exponent.** The computed argument is within `7.1 u Q(s)` of
  `Q(s) = d/(4(1 - s)) + m/(4(1 + s))` at the rounded sine `s` (plus a
  subnormal-scale `300 z`): `d'`, `m'` carry three roundings each, `p`, `q` two,
  the products one and the sum one, all of non-negative quantities
  (`BvnArg.v`). The sine's rounding and the node angle's enter through
  `|Q(s') - Q(s)| <= |s' - s| / (1 - |s'|) Q(s)`, uniform in `kappa`
  (`BvnQ.v`, `Q_diff`); the angle error is `u |asr| (tau + 0.76)`
  (`BvnLow.v`, `angle_err`); the sine's is its documented half-ulp.
* **Term.** `|term_i - W_i f_i| <= |W_i| f_i ((1+ew)(1+rx) e^{theta_i Q_i + 300 z} - 1) + 3 z`
  (`BvnNode.v`, `node_err`): `W_i = Kex w_i`, `Kex = asr/(4 pi)`;
  `kw_i` is within `ew = (1+u)^2 (1+eta) - 1` of it (stored weight, `K`'s
  rounding and distance of `TAU` from `2 pi` with `eta = 1.7e-16`, and the
  product), and `rx = 2u + 2^-99` is the `exp` and product roundings.
* **Supremum over the exponent.** For `nu = 1 - theta`,
  `e^{-Q} ((1 + b) e^{theta Q} - 1) <= (theta/nu) exp(nu b/theta - 1)` when
  `nu b <= theta`, else `b` (`BvnQuadG.v`), for every `Q >= 0`, hence every
  `x`, `y`; `b = 6.2e-16 >= (1 + 2000 u^2)(1 + ew)(1 + rx) e^{300 z} - 1`.
* **Sum.** The double-word accumulation of at most 24 same-sign terms is within
  `2000 u^2` relative and `30 z` of their exact total, and `|L| <= 24 (3 u |T| + 2 z)`
  (`BvnSum.v`; non-positive terms by oddness of rounding).
* **Last stage.** The product's two words are exact for `Phi(x) Phi(y) >= 1e-270`
  (`two_prod`, `formal/two-prod`); `fl(s + r)` carries `2^-54` and the three small
  additions `< 2^-90` together (`BvnFinal.v`); the clamp cannot increase the error
  when the exact value is in `[0, 1]`. The integral at `asr` against at
  `asin rho` differs by at most `|asin rho - asr| <= 2^(k-54) + 2^-62 2^k`
  (`BvnIntegral.v`, Coquelicot `RInt`); truncation is `trunc_bound` of the rule.

Total, with `eP = 2^-54 + 2^-112` the distribution function's error:

    B = 2^-54 + 2^-900 + 2^-90 + 2 eP + (A/(4 pi)) sum_i Whi_i G_i + 200 z
        + Tr/(2 pi) + (2^(k-54) + 2^-62 2^k)/(2 pi).

## 3. Result

| rule `N`, `|rho| <=` | proved bound `B` |
| --- | --- |
| 6, 0.20 | 2.07e-16 |
| 8, 0.38 | 2.31e-16 |
| 12, 0.66 | 2.76e-16 |
| 14, 0.75 | 2.95e-16 |
| 20, 0.89 | 3.48e-16 |
| 24, below 0.925 | 3.72e-16 |

The published `2.5e-16` is proved for `|rho| < 0.29` with the rules used (6 and 8 nodes; the 8-node theorem itself covers `|rho| <= 0.38`); the
smallest bound proved for the whole branch is `3.72e-16`. The three changes
against the previous kernel (`5.29e-16` at the top rule) bought, in the order
the derivation meets them:

* the cancellation-free exponent: the exponent's relative error falls from
  the numerator's rounding times `1/(1 - sigma)` (a factor 13 at the top node)
  to `7.1 u`, and the cosine and `zt` terms disappear; `-0.5e-16` at the top rule;
* the weight folded into `kw_i` and the unrounded double-word handoff: the sum's
  `fl(H + L)` rounding and the multiplication by `K` (two roundings) are gone,
  at the cost of one rounding in `kw_i`; the per-term constant `b` falls from
  `7.3e-16` to `6.2e-16`; `-0.45e-16`;
* the product and last addition error-free: the product's rounding is gone and
  the addition is the only rounding of the result (`2^-54` instead of
  `2 * 2^-54`); the two distribution functions' own errors stay; `-0.55e-16`.

## 4. What is assumed

Named hypotheses of the theorems (none is an `Axiom`):

* `exp_contract`: `exp` returns a rounding of a value within `2^-100`
  relatively of `e^v` (`docs/exp.md` proves correct rounding, which implies it);
  `sin_contract`: `sin` returns a binary64 within `(1 + 2^-100) 2^(k-54)` of
  `sin theta` whenever `|sin theta| <= 2^k` (`docs/sin_cos.md`: correct rounding
  where [LM] reaches, within `(1/2 + 2^-144)` ulp elsewhere, on `|theta| <= 2.5`);
* the distribution function: `|Phi' - Phi| <= 2^-54 + 2^-112`, in `[0, 1]`
  (`docs/normal.md`: the returned value is `RN(Z)` with `|Z - Phi| <= 2^-112 Phi`;
  no whole-domain correct rounding is claimed there and none is used);
* `asin`: a rounding of a value within `2^-62` relatively of `asin rho`
  (`docs/asin.md`: fast path below `2^-63`, accurate path `2^-124`; correct
  rounding needs `CoreMath` and is not used);
* **Plackett**: the exact value is a probability (`0 <= P <= 1`);
* **T1**: `|int_0^asr f - (asr/2) sum W_i f(asr tau_i)| <= Tr`, the Gauss-Legendre
  remainder of `docs/bivariate_normal_truncation.md` section 2;
* the stored abscissas and weights are the binary64 roundings of the exact
  rule's, which lies in the enclosures of `BvnData.v` (generated, 120-digit
  roots with outward margin `10^-30`); `kw_i` is `fl(w_i * K)`.

Inputs are binary64 numbers with `|x|, |y| <= 64` (the kernel is reached with
`|x|, |y| < 39`). No operation is assumed free of underflow: every rounding
carries its subnormal term `z = 2^-1075`, and the `two_prod` error word is taken
as zero below `1e-270`, where the product's own rounding is below `2^-900`. The
kernel is transcribed in `formal/bivariate/BvnKernel.v`, extracted and compared bit for
bit with the Rust (`docs/bivariate_normal.md` section 6.5), and `BvnRefineLow.v` proves
its pieces equal the Coq functions this budget is about: `node_angle_ok` (`angle`), `low_node_ok`
(`node_term`, with `argnc`'s `p` and `q` as the table stores them), `low_sum_ok` (`acc`),
`low_finish_ok` (`finish`, `PRODUCT_EXACT_FLOOR` included) and `kernel_low_ok` (`Rhat` of `BvnTop.v`),
under the magnitude bounds the proofs give and the library relations of item 1; the per-node
ranges (`node_ranges`) and the match of the stored table to the proof's `NodeS` records
(`nodes_match`) are hypotheses of `kernel_low_ok`; the match rests, as before, on the generator
and the enclosures of `BvnData.v`.

The global axioms of `BvnBudget.low_N` are Coq's classical-real axioms
(`classic`, `sig_forall_dec`, `sig_not_dec`, `functional_extensionality_dep`,
from the real-number library and Coquelicot) and the primitive integer and float
specifications CoqInterval's `interval` tactic reaches; all are in
`formal/axioms*.expected`, and `KernelAudit.v` prints them for every rule.
`generators/bivariate_normal_budget.py` writes `BvnData.v` (the enclosures) and
`BvnBudget.v` (the per-rule lemmas); `--check` replays it.

## 5. Not proved here

* The double-word `Phi` or any change to remove the distribution functions'
  `2 eP`; the proved floor is about `3.3e-16` at the top rule with the present
  `Phi`.
* A tighter weight (a double-word `w_i K` rounded once) would lower `b` to about
  `4.5e-16`, about `-0.2e-16` at the top rule; not implemented.
* `|rho|` at or above `0.925`, `rho = +-1` and `|rho| < 2^-52`.
