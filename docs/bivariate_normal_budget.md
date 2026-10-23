# Absolute error of the low-correlation branch

This note derives and states the proved absolute error bound of
`BivariateNormal::low` (`|rho| < 0.925`) as the kernel computes it today, and
records what the proof assumes. It does not cover the high-correlation `BVND`
branch, the closed-form regimes or the double-word accumulation's variants.
The machine-checked statement is `formal/bivariate/BvnTop.v` (`low_branch`),
specialised per rule in `BvnBudget.v` (`low_N`).

## 1. The computation that is bounded

For ordered finite `x <= y`, `|x|, |y|` zero or at least `2^-400`, and a rule
`N` selected by `|rho|` (`docs/bivariate_normal_truncation.md` section 5):

    asr   = asin(rho)                         correctly rounded
    p_i   = fl(sgn_i * xh_i + 1)              xh_i, w_i: the stored abscissa and weight
    th_i  = fl(fl(asr * p_i) / 2)
    s_i, c_i = sincos(th_i)                   correctly rounded
    den_i = fl(c_i * c_i)
    hs    = fl(fl(fl(x*x) + fl(y*y)) / 2),    xy = fl(x*y)
    a_i   = fl(fl(fl(s_i * xy) - hs) / den_i)
    t_i   = fl(w_i * fl(exp(a_i)))            exp correctly rounded
    (H, L) = two_sum accumulation of the t_i, L = fl(L + e) in order
    K     = fl(asr / (2 * TAU))
    C     = fl(fl(H + L) * K)
    P0    = fl(Phi(x) * Phi(y))               Phi correctly rounded
    R     = clamp(fl(C + P0), 0, 1)

The exact target is `P = Phi(x) Phi(y) + (1/2 pi) int_0^{asin rho} f`,
`f(t) = exp(-(x^2 + y^2 - 2 x y sin t) / (2 cos^2 t))`.

## 2. Derivation

* **Exponent.** With `S = sin theta`, `Q(S) = (r/2 - p S)/(1 - S^2)`,
  `r = x^2 + y^2`, `p = x y`, `|p| <= r/2`. The computed `a_i` is within
  `ar * Q(S)` of `-Q(S)` (`BvnArg.v`), where the relative error is the sum of the
  quotient's `zt` (rounded cosine), the rounding of `hs`, `xy` and the
  subtraction relative to `r/2 (1 - kappa S)` (the cancellation: `1/(1 - sigma)`
  is 13 at the top node) and the final division. Rounding `sin theta` and the
  node angle `theta` are bounded separately: `Q(S') - Q(s)` is
  `(r/2)(S' - s)(S' + s - kappa (1 + s S'))/((1 - S'^2)(1 - s^2))`, whose
  ratio to `Q(s)` is at most `|S' - s| / (1 - |S'|)` for every `kappa`
  (`BvnNode.v`, `Q_diff`). The angle error is `u |asr| (tau + 0.76)`
  (`BvnLow.v`, `angle_err`).
* **Term.** `|t_i - W_i f_i| <= W_i f_i ((1+u)^3 e^{theta_i Q_i + z} - 1) + 3 z`
  (`node_err`), `u = 2^-53`, `z = 2^-1075`.
* **Supremum over the exponent.** For `nu = 1 - theta`,
  `e^{-Q} ((1 + b) e^{theta Q} - 1) <= (theta/nu) exp(nu b/theta - 1)` when
  `nu b <= theta` and `b` otherwise (`BvnQuadG.v`), for every `Q >= 0`, hence for
  every `x`, `y`.
* **Sum.** The double-word accumulation of at most 24 non-negative terms is
  within `2000 u^2` relative and `30 z` of their exact total (`BvnSum.v`).
* **Chain.** `fl(fl(H + L) K)` against `Kex V`, `Kex = asr/(4 pi)`,
  with multiplier `1 + psi = (1 + eta)(1 + 2000 u^2)(1 + u)^2`,
  `eta = 1.7e-16` (the rounding of `asr/(2 TAU)` and `TAU`'s distance from
  `2 pi`, `BvnTail.v`), and per-term constant `b = 7.3e-16 >= (1+psi)(1+u)^3 e^z - 1`
  (`BvnChain.v`, `BvnLowRule.v`).
* **Remaining terms.** `Phi(x)`, `Phi(y)`: `2^-54` each; product: `2 * 2^-54`
  from the operands plus `2^-54` rounding; final add: `2^-54`; the clamp cannot
  increase the error when the exact value is in `[0, 1]` (`BvnTail.v`).
  The correction's integral at `asr` against at `asin rho`: the integrand is in
  `(0, 1]` so the difference is at most `|asin rho - asr| <= 2^(k-54)`
  (`BvnIntegral.v`, Coquelicot `RInt`). The Gauss-Legendre truncation is
  `trunc_bound` of the rule (`BvnRules.v`).

Total: `B = 4 * 2^-54 + (A/(4 pi)) sum_i Whi_i G_i + 1000 z + Tr/(2 pi) + 2^(k-54)/(2 pi)`.

## 3. Result

| rule `N`, `|rho| <=` | proved bound `B` |
| --- | --- |
| 4, 0.055 | 2.47e-16 |
| 6, 0.20 | 2.67e-16 |
| 8, 0.38 | 2.95e-16 |
| 10, 0.54 | 3.28e-16 |
| 12, 0.66 | 3.56e-16 |
| 14, 0.75 | 3.85e-16 |
| 16, 0.81 | 4.11e-16 |
| 20, 0.89 | 4.78e-16 |
| 24, below 0.925 | 5.29e-16 |

The published `2.5e-16` is **not** proved for the current kernel: it holds for
the first rule only, and the overall proved bound is `5.3e-16`. The observed
worst error of `2.22e-16` sits inside the bound; the proved figure is a
worst-case alignment of every rounding.

## 4. What is assumed

Named hypotheses of the theorems (none is an `Axiom`):

* the library functions `Phi`, `asin`, `sin`, `cos`, `exp` return
  `rndF` of the exact value (their documents prove it; `sincos` is correctly
  rounded on `|x| <= 2.5`, which covers the angles);
* **Plackett**: the exact value is a probability (`0 <= P <= 1`);
* **T1**: `|int_0^asr f - (asr/2) sum W_i f(asr tau_i)| <= Tr`, the Gauss-Legendre
  remainder of `docs/bivariate_normal_truncation.md` section 2;
* the stored abscissas and weights are the binary64 roundings of the exact rule's,
  and the exact rule lies in the enclosures of `BvnData.v` (generated, 120-digit
  roots with outward margin `10^-30`);
* no underflow in the exponent argument: `x`, `y` are zero or at least `2^-400`
  in magnitude (a smaller nonzero input is outside the statement); overflow does
  not occur for `|x|, |y| < 39`.

The Rust is not extracted: the Coq transcription (`angle`, `argf`, `termf`,
`acc`, `Chat`, `Rhat`) mirrors the sequence of section 1 by reading, not by a
bit-for-bit comparison.

The global axioms of `BvnBudget.low_N` are Coq's classical-real axioms
(`classic`, `sig_forall_dec`, `sig_not_dec`, `functional_extensionality_dep`,
from the real-number library and Coquelicot) and the primitive integer and float
specifications CoqInterval's `interval` reaches; all are in
`formal/axioms*.expected`, and `KernelAudit.v` prints them for every rule.
`generators/bivariate_normal_budget.py` writes `BvnData.v` (the enclosures) and
`BvnBudget.v` (the per-rule lemmas); `--check` replays it.

## 5. Variants (derived with the same closed forms, not yet transcribed)

Top rule (`N = 24`); the first column keeps the same bound structure.

| change | bound |
| --- | --- |
| current kernel (proved) | 5.2e-16 |
| `fma(Phi(x), Phi(y), C)` or `two_prod` + `two_sum` for the last add | 4.6e-16 (removes `2^-54`) |
| exponent as `-(d p_i + m q_i)`, `d = (x-y)^2`, `m = (x+y)^2`, `p_i = 1/(4(1-s_i))`, `q_i = 1/(4(1+s_i))` tabulated (no cancellation) | 4.6e-16 |
| both | 4.1e-16 |
| both and `asr/(4 pi)` folded into the stored weights with one rounding | 3.9e-16 |

The floor is `3 * 2^-54 + 2^-54/2`-ish from the two distribution functions and
the last rounding plus about `1.0e-16` of correction error; `2.5e-16` is
not reachable without double-word `Phi`.
