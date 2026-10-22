#!/usr/bin/env python3
"""Exact binary64-input systems; dense pivoted rational elimination oracle.

Only Python integer/Fraction arithmetic and exact binary64 encoding are used.
The 401-row case uses a manufactured integer solution checked by exact A*x.
No consumer data or Thomas recurrence is used. Replay with --check.
"""
from fractions import Fraction as F
import json
import math
from pathlib import Path
import struct
import sys

OUTPUT = Path(__file__).resolve().parents[1] / 'crates/reference/fixtures/tridiagonal.json'


def bits(x):
    return struct.pack('>d', x).hex()


def dense_solve(lower, diagonal, upper, rhs):
    n = len(diagonal)
    a = [[F(0) for _ in range(n + 1)] for _ in range(n)]
    for i in range(n):
        a[i][i] = F(diagonal[i])
        a[i][n] = F(rhs[i])
        if i:
            a[i][i-1] = F(lower[i-1])
        if i + 1 < n:
            a[i][i+1] = F(upper[i])
    # General dense Gauss-Jordan with row pivoting, deliberately distinct from
    # a tridiagonal forward-elimination/back-substitution implementation.
    for k in range(n):
        p = max(range(k, n), key=lambda i: abs(a[i][k]))
        a[k], a[p] = a[p], a[k]
        divisor = a[k][k]
        assert divisor
        a[k] = [v / divisor for v in a[k]]
        for i in range(n):
            if i != k:
                coefficient = a[i][k]
                a[i] = [v - coefficient * w for v, w in zip(a[i], a[k])]
    return [row[n] for row in a]


def product(lower, diagonal, upper, x):
    result = []
    for i, d in enumerate(diagonal):
        y = F(d) * x[i]
        if i:
            y += F(lower[i-1]) * x[i-1]
        if i + 1 < len(diagonal):
            y += F(upper[i]) * x[i+1]
        result.append(y)
    return result


def case(name, lower, diagonal, upper, rhs, solution=None):
    if solution is None:
        solution = dense_solve(lower, diagonal, upper, rhs)
    assert product(lower, diagonal, upper, solution) == list(map(F, rhs))
    return dict(name=name, lower=list(map(bits, lower)), diagonal=list(map(bits, diagonal)),
                upper=list(map(bits, upper)), rhs=list(map(bits, rhs)),
                solution=[[str(x.numerator), str(x.denominator)] for x in solution])


def generate():
    cases = [case('empty', [], [], [], [])]
    for d, r in [(1., -0.), (-2., 3.), (2.**-1074, 2.**-1074), (2.**-1022, 2.**-1074),
                 (2.**900, 2.**-900), (2.**-900, 2.**-901)]:
        cases.append(case(f'singleton-{len(cases)}', [], [d], [], [r]))
    # Exactly nonsingular but increasingly ill-conditioned near the boundary.
    for k in [4, 20, 48, 52]:
        d = 1. + 2.**-k
        cases.append(case(f'near-dominance-{k}', [1.], [d, d], [1.], [1., -1.]))
    # Signed diagonals/neighbours and unrelated RHSs; dyadic coefficients.
    for n in [2, 3, 7, 17]:
        lower = [((i * 7 + 3) % 17 - 8) / 8 for i in range(n-1)]
        upper = [((i * 11 + 5) % 19 - 9) / 8 for i in range(n-1)]
        diagonal = [((-1.)**i) * (3. + (i % 5) / 8) for i in range(n)]
        for shift in [-1060, -1022, -900, 0, 900]:
            scale = lambda xs: [math.ldexp(x, shift) for x in xs]
            for r in range(3):
                rhs = [((i * 13 + r * 7) % 23 - 11) / 8 for i in range(n)]
                cases.append(case(f'mixed-{n}-{shift}-{r}', scale(lower), scale(diagonal), scale(upper), scale(rhs)))
    # Strongly unequal row scales and cancellation in the RHS.
    cases.append(case('row-scaled', [2.**-500, -2.**500],
                      [4., 2.**-498, 2.**502], [-1., 2.**-500], [3., 2.**-500, -2.**501]))
    n = 401
    lower, upper = [-1.] * (n-1), [1.] * (n-1)
    diagonal = [4.] * n
    x = [F(i % 13 - 6) for i in range(n)]
    rhs = list(map(float, product(lower, diagonal, upper, x)))
    cases.append(case('manufactured-401', lower, diagonal, upper, rhs, x))
    return dict(generator='generators/tridiagonal_reference.py',
                oracle='Python exact integers/Fraction; dense pivoted Gauss-Jordan; exact manufactured long system',
                cases=cases)


if __name__ == '__main__':
    content = json.dumps(generate(), indent=2) + '\n'
    if '--check' in sys.argv:
        assert OUTPUT.read_text() == content, f'{OUTPUT} differs; regenerate'
    else:
        OUTPUT.write_text(content)
