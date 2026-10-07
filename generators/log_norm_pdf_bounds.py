#!/usr/bin/env python3
"""Exact-rational check of log_norm_pdf's regime-M bounds (docs/log_norm_pdf.md §3).

With S = a²/2 + C and Z the double-word sum of the exact square and C_HI + C_LO:
- ε, the relative error of Z against S, composes DoubleWord::add's bound
  3u² + 13u³ with the constant's truncation 2^−109 (log_norm_pdf_constants.py);
- the rounding test is run at ε₁ = 2^−80, so ε ≤ ε₁ must hold;
- when the test fails, −Z_hi is within (1/2 + K)·ulp of the result, and K must
  not exceed the claimed 2^−50.

Standard library only. `--check` exits non-zero if a claim fails; without it,
the computed values are printed.
"""
import math
import sys
from fractions import Fraction as F

U = F(1, 2**53)
DW_ADD = 3 * U**2 + 13 * U**3        # DoubleWord::add, relative
TRUNCATION = F(1, 2**109)            # |C − C_HI − C_LO| < 2^−109·C ≤ 2^−109·S
EPS_1 = F(1, 2**80)                  # the rounding test's ε₁
CLAIM_EPS = F(1, 2**103)
CLAIM_FALLBACK = F(1, 2**50)


def main():
    # |Z − S| ≤ DW_ADD·(S + TRUNCATION·S) + TRUNCATION·S.
    eps = DW_ADD * (1 + TRUNCATION) + TRUNCATION
    # S ≤ |Z|/(1 − ε) ≤ |Z_hi|(1 + u)/(1 − ε), taken with a further (1 + ε)
    # of margin, and ulp(v) > u·|v|: ε·S ≤ ε(1 + u)(1 + ε)/((1 − ε)u)·ulp(Z_hi).
    fallback = eps * (1 + U) * (1 + eps) / ((1 - eps) * U)
    checks = [
        ('epsilon < 2^-103', eps < CLAIM_EPS),
        ('epsilon <= epsilon_1 = 2^-80', eps <= EPS_1),
        ('fallback K <= 2^-50', fallback <= CLAIM_FALLBACK),
    ]
    if '--check' not in sys.argv[1:]:
        print(f'epsilon = 2^{math.log2(eps):.4f}')
        print(f'fallback K = 2^{math.log2(fallback):.4f}')
    failed = [name for name, ok in checks if not ok]
    if failed:
        sys.exit('log_norm_pdf bounds failed: ' + ', '.join(failed))
    if '--check' in sys.argv[1:]:
        print('log_norm_pdf bounds: every claimed constant dominates its composed bound')


if __name__ == '__main__':
    main()
