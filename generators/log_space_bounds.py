#!/usr/bin/env python3
"""Exact-rational check of the error bounds in docs/log_space.md (§4, §6).

The derivation composes per-operation error bounds into one bound per function:
|ŷ − y| ≤ u·|y| + β·u·|L| + η. This script evaluates every composed expression,
higher-order terms included, in exact rational arithmetic (fractions.Fraction),
and checks that the constants the document claims dominate them.

It certifies the arithmetic of the composition, not that the implementation
follows the derivation; the reference fixtures check that. Irrational constants
enter only through rational enclosures stated below.

Standard library only. `--check` exits non-zero if a claim fails; without it,
the computed constants are printed.
"""
import sys
from fractions import Fraction as F

U = F(1, 2**53)
TINY = F(1, 2**1074)  # the smallest positive subnormal
HALF_TINY = F(1, 2**1075)

# ln 2 = 0.693147180559945309417232121458176568075500134360255254120680...
# Enclosed by its 40-digit truncation and that plus one unit in the last place.
LN2_LO = F(6931471805599453094172321214581765680755, 10**40)
LN2_HI = LN2_LO + F(1, 10**40)

# T = RN(−ln 2), the log_diff_exp region boundary (decision 6), exactly.
T = F(-0.6931471805599453)
assert T == F(-6243314768165359, 2**53), "RN(−ln 2) changed"

# exp(x) = +0 for x below about −745.13, so a nonzero exp(dh) has |dh| < 746,
# and the two_sum tail satisfies |dl| ≤ u·|dh| < 746u (decision 3).
D = 746 * U

# morphiq-numerics contracts at the pinned revision: expm1 within
# (1/2 + 2^−65) ulp and ln_1p within (1/2 + 2^−70) ulp; ulp(v) ≤ 2u|v| for
# normal v, so their relative errors are at most these.
EXPM1_REL = (1 + F(1, 2**64)) * U
LN1P_REL = (1 + F(1, 2**69)) * U

# The constants docs/log_space.md claims.
CLAIM_LSE_BETA = 3 + F(1, 2**8)
CLAIM_LSE_N_MAX = 2**20 + 1
CLAIM_DIFF_BETA = F(389, 100)


def claim_lse_eta(k):
    """The η the document claims for k summed terms, in units of 2^−1074."""
    return (2 * k + 1) * TINY


CLAIM_DIFF_ETA = 5 * TINY


def gamma(n):
    return n * U / (1 - n * U)


def lse(k):
    """β and η of log_sum_exp with k terms summed (n = k + 1 finite inputs)."""
    # §4 Terms: eh = e^dh(1+δ1), p = eh·dl(1+δ2), e^dl = 1 + dl + r with
    # |r| ≤ dl²; e^dl ≥ 1 − D.
    eps_term = (U + 2 * U * D + U * U * D + D * D) / (1 - D)
    # Σ|summands| against t.
    rho = (1 + U) * (1 + D * (1 + U)) / (1 - D)
    g2 = gamma(2 * k - 1) ** 2 if k > 0 else F(0)
    # [ORO] Proposition 4.5, with the term errors.
    delta_t = eps_term + U * (1 + eps_term) + g2 * rho
    # Two possibly subnormal operations per term, carried through the sum,
    # plus each dropped mass (exp underflow to +0, or decision 3) below 2^−1075.
    eta_t = k * TINY * (1 + U + g2) + k * HALF_TINY
    # ln(1 + t): |ΔL| ≤ δ_t/(1 − δ_t)·L + η_t/(1 − η_t), since t/(1+t) ≤ L.
    a = delta_t / (1 - delta_t)
    b = eta_t / (1 - eta_t)
    # ln_1p's rounding, a subnormal result's absolute half-ulp, then the final
    # RN(m + L̂): |ŷ − y| ≤ u|y| + (1 + u)|L̂ − L|.
    beta = (1 + U) * (LN1P_REL + (1 + LN1P_REL) * a) / U
    eta = (1 + U) * ((1 + LN1P_REL) * b + HALF_TINY)
    return beta, eta


def diff_region_a():
    """Relative error of L̂ = RN(ln q̂) in log_diff_exp's region A.

    L = ln z with z = 1 − e^(dh + dl) = q − g, q = 1 − e^dh < 1/2 and
    g = (1 − q)(e^dl − 1); dl is dropped. With |dl| ≤ u·|dh|, |dh| = −ln(1 − q)
    and |e^dl − 1| ≤ |dl|(1 + |dl|):
        |g/q| ≤ u(1 + u)·(1 − q)(−ln(1 − q))/q ≤ u(1 + u)·|ln q|,
    using (1 − q)·ln(1/(1 − q)) ≤ q·ln(1/q) on (0, 1/2]: their difference
    r(q) = (1 − q)ln(1 − q) − q·ln q is concave (r'' = 1/(1 − q) − 1/q < 0)
    with r(0) = r(1/2) = 0, so r ≥ 0. |ln q| ≤ 745.2 as q ≥ 2^−1074.
    """
    dq = EXPM1_REL  # q̂ = q(1 + δq); also covers expm1(x) = x for |x| < 2^−54
    e1 = dq / (1 - dq)  # |ln q̂ − ln q|
    # |ln(1 − g/q)| ≤ |g/q|/(1 − |g/q|) ≤ κ·|ln q|.
    kappa = U * (1 + U) / (1 - 746 * U * (1 + U))
    # |L| = |ln q + ln(1 − g/q)| ≥ (1 − κ)|ln q|, and |ln q| > ln 2.
    # |L̂ − L| ≤ e1 + κ|ln q| + u(|ln q| + e1).
    rel = (kappa + U) / (1 - kappa)
    absolute = e1 * (1 + U)
    return rel + absolute / (LN2_LO * (1 - kappa))


def diff_region_b():
    """Relative error of L̂ in log_diff_exp's region B, and w's upper bound."""
    # ŵ = RN(eh + RN(eh·dl)), eh = e^dh(1 + δ1).
    eps_w = ((1 + D) * ((1 + U) ** 2 - 1) + D * U * (1 + U) ** 2 + D * D) / (1 - D)
    # w ≤ e^T·e^|dl| with |dl| < u at dh ≈ T; e^T = e^(−ln 2 + (T + ln 2))/…
    # T + ln 2 ≤ LN2_HI + T, and e^x ≤ 1 + 2x for 0 ≤ x ≤ 1.
    w_max = F(1, 2) * (1 + 2 * (LN2_HI + T)) * (1 + 2 * U)
    assert w_max > F(1, 2)
    # Conditioning w/((1 − w(1 + ε))·|ln(1 − w)|) increases in w (it is
    # (e^x − 1)/x in x = −ln(1 − w), with a decreasing extra factor), and
    # |ln(1 − w_max)| ≥ ln 2 as w_max ≥ 1/2.
    h = w_max / ((1 - w_max * (1 + eps_w)) * LN2_LO)
    rel = h * eps_w + LN1P_REL * (1 + h * eps_w)
    return rel, w_max, eps_w


def diff():
    a_rel = diff_region_a()
    b_rel, w_max, eps_w = diff_region_b()
    worst = max(a_rel, b_rel)
    beta = (1 + U) * worst / U
    # Subnormal ŵ: three operations' half-ulps, propagated by 1/(1 − w);
    # ln_1p's subnormal half-ulp; a dropped mass below 2^−1075 (decision 3).
    prop = 1 / (1 - w_max * (1 + eps_w))
    eta = (1 + U) * (prop * 3 * HALF_TINY + HALF_TINY + prop * HALF_TINY)
    return beta, eta, {"region A": a_rel / U, "region B": b_rel / U}


def main():
    check = "--check" in sys.argv[1:]
    failures = []

    worst_beta = F(0)
    for k in (1, 2, 3, 16, 2**10, CLAIM_LSE_N_MAX - 1):
        beta, eta = lse(k)
        worst_beta = max(worst_beta, beta)
        if not check:
            print(f"log_sum_exp k={k}: beta = {float(beta):.17g}, "
                  f"eta = {float(eta / TINY):.17g}·2^-1074")
        if beta > CLAIM_LSE_BETA:
            failures.append(f"log_sum_exp k={k}: beta {float(beta)} > claim")
        if eta > claim_lse_eta(k):
            failures.append(f"log_sum_exp k={k}: eta {float(eta / TINY)} > claim")

    beta, eta, parts = diff()
    if not check:
        for name, value in parts.items():
            print(f"log_diff_exp {name}: relative error of L-hat = {float(value):.17g}u")
        print(f"log_diff_exp: beta = {float(beta):.17g}, "
              f"eta = {float(eta / TINY):.17g}·2^-1074")
    if beta > CLAIM_DIFF_BETA:
        failures.append(f"log_diff_exp: beta {float(beta)} > claim")
    if eta > CLAIM_DIFF_ETA:
        failures.append(f"log_diff_exp: eta {float(eta / TINY)} > claim")

    if failures:
        print("\n".join(failures), file=sys.stderr)
        sys.exit(1)
    if check:
        print("log_space bounds: every claimed constant dominates its composed bound")


if __name__ == "__main__":
    main()
