#!/usr/bin/env python3
"""Public synthetic sign-domain systems with an independent dense exact oracle."""
from fractions import Fraction as F
import json
import math
from pathlib import Path
import sys
from tridiagonal_reference import case, product

OUTPUT = Path(__file__).resolve().parents[1] / 'crates/reference/fixtures/tridiagonal_sign.json'


def generate():
    cases = [case('empty', [], [], [], [])]
    for d, rhs in [(1., -0.), (2.**-1074, 2.**-1074), (2.**-1022, 2.**-1074),
                   (2.**900, 2.**-900)]:
        cases.append(case(f'single-{len(cases)}', [], [d], [], [rhs]))
    cases.append(case('outside-dominance', [-3., -3.], [2., 2., 2.], [3., 3.], [-4., 2., 12.]))
    for n in [2, 3, 7, 17]:
        lower = [(-1.)**i * (i % 7 + 1) for i in range(n-1)]
        upper = [-(-1.)**i * (i % 5 + 2) for i in range(n-1)]
        diagonal = [1. + (i % 3)/4 for i in range(n)]
        for shift in [-1050, -1022, -900, 0, 900]:
            scale = lambda xs: [math.ldexp(x, shift) for x in xs]
            rhs = [(i % 11 - 5)/4 for i in range(n)]
            cases.append(case(f'alternating-{n}-{shift}', scale(lower), scale(diagonal), scale(upper), scale(rhs)))
    for lower, upper in [([-0., 2.], [3., -0.]), ([0., -2.], [-3., 0.]),
                         ([2.**-1074, -2.**-1074], [-2.**-1074, 2.**-1074])]:
        cases.append(case(f'zero-or-tiny-link-{len(cases)}', lower, [1., 2., 1.], upper, [1., -2., 3.]))
    for n in [2, 3, 17, 401]:
        # Exact pivots 2 and normalized upper 1/2. Deliberately not dominant.
        lower, diagonal, upper = [-2.]*(n-1), [2.]+[1.]*(n-1), [1.]*(n-1)
        x = [F(i % 13 - 6) for i in range(n)]
        rhs = list(map(float, product(lower, diagonal, upper, x)))
        cases.append(case(f'exact-manufactured-{n}', lower, diagonal, upper, rhs, x))
    return dict(generator='generators/tridiagonal_sign_reference.py',
                oracle='Python exact integers/Fraction; dense pivoted Gauss-Jordan; exact manufactured systems', cases=cases)


if __name__ == '__main__':
    content = json.dumps(generate(), indent=2) + '\n'
    if '--check' in sys.argv:
        assert OUTPUT.read_text() == content, f'{OUTPUT} differs; regenerate'
    else:
        OUTPUT.write_text(content)
