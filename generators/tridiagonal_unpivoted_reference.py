#!/usr/bin/env python3
"""Independent public synthetic systems; exact dense pivoted rational oracle."""
from fractions import Fraction as F
import json
import math
from pathlib import Path
import sys
from tridiagonal_reference import case, product

OUTPUT = Path(__file__).resolve().parents[1] / 'crates/reference/fixtures/tridiagonal_unpivoted.json'


def generate():
    cases = [case('empty', [], [], [], [])]
    for d in [-2., -2.**-1074, 2.**-1074, 2.**900]:
        cases.append(case(f'single-{len(cases)}', [], [d], [], [d]))
    # Mixed adjacent products, neither global sufficient domain.
    for shift in [-1000, 0, 900]:
        scale = lambda xs: [math.ldexp(x, shift) for x in xs]
        cases.append(case(f'mixed-{shift}', scale([4., -2.]), scale([2., 1., -3.]),
                          scale([1., 3.]), scale([3., -5., 7.])))
    cases.append(case('zero-second-diagonal', [1.], [1., 0.], [1.], [1., 2.]))
    # Manufactured integer solutions: pivots alternate +/-2, normalized upper
    # is exactly 1/2. Neither strong domain admits the alternating diagonal.
    for n in [2, 3, 17, 401]:
        lower = [2. if i % 3 else -2. for i in range(n-1)]
        pivot = [2. * (-1.)**i for i in range(n)]
        diagonal = [pivot[0]] + [pivot[i] + lower[i-1]/2 for i in range(1, n)]
        upper = [p/2 for p in pivot[:-1]]
        x = [F(i % 13 - 6) for i in range(n)]
        rhs = list(map(float, product(lower, diagonal, upper, x)))
        cases.append(case(f'exact-manufactured-{n}', lower, diagonal, upper, rhs, x))
    # A nonsingular matrix that requires a row interchange is an exact refusal
    # witness: the oracle succeeds while the unpivoted API must refuse.
    refused = [case('zero-leading-nonsingular', [1.], [0., 1.], [1.], [2., 3.])]
    return dict(generator='generators/tridiagonal_unpivoted_reference.py',
                oracle='Python exact integers/Fraction; dense pivoted Gauss-Jordan; exact manufactured systems',
                cases=cases, refused=refused)


if __name__ == '__main__':
    content = json.dumps(generate(), indent=2) + '\n'
    if '--check' in sys.argv:
        assert OUTPUT.read_text() == content, f'{OUTPUT} differs; regenerate'
    else:
        OUTPUT.write_text(content)
