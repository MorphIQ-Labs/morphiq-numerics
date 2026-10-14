#!/usr/bin/env python3
"""FiniteInterval fixtures: exact rational arithmetic and mpmath interval oracle.

Arithmetic endpoints are derived from exact Fraction images, rounded once by
CPython's exact rational-to-binary64 conversion, then widened as the contract
specifies. Separately assert containment of the exact mathematical corner
images (including direct quotients, not just the staged reciprocal result).
Elementary endpoints use the shared mpmath 1.4.1 interval oracle, requiring
nearest-bit agreement at two consecutive precisions starting at 128 bits.
No library implementation is called. Replay with --check.
"""
import json
import math
from fractions import Fraction as F
from pathlib import Path
import sys

from mpmath import iv
from oracle import correctly_rounded, from_bits, splitmix64, to_bits

OUTPUT = Path(__file__).resolve().parents[1] / 'crates/reference/fixtures/interval.json'
INF = math.inf
MAX = from_bits(0x7fefffffffffffff)
ETA = from_bits(1)


def bits(x):
    return f'{to_bits(x):016x}'


def nearest(q):
    try:
        return float(q)
    except OverflowError:
        return -INF if q < 0 else INF


def widen(l, u):
    l, u = math.nextafter(l, -INF), math.nextafter(u, INF)
    if not (math.isfinite(l) and math.isfinite(u)):
        return 'range'
    return l, u


def arithmetic(op, a, b):
    l, u, c, d = map(F, (*a, *b))
    if op == 'add':
        values = [l+c, u+d]
    elif op == 'sub':
        values = [l-d, u-c]
    elif op == 'mul':
        values = [x*y for x in (l, u) for y in (c, d)]
    elif op == 'div':
        if c <= 0 <= d:
            return 'domain'
        reciprocal = widen(nearest(1/d), nearest(1/c))
        if isinstance(reciprocal, str):
            return reciprocal
        result = arithmetic('mul', a, reciprocal)
        values = [x/y for x in (l, u) for y in (c, d)]
        if not isinstance(result, str):
            assert F(result[0]) <= min(values) <= max(values) <= F(result[1])
        return result
    result = widen(nearest(min(values)), nearest(max(values)))
    if not isinstance(result, str):
        assert F(result[0]) <= min(values) <= max(values) <= F(result[1])
    return result


def unary(op, a):
    l, u = a
    if op == 'square':
        values = [F(l)**2, F(u)**2]
        if l <= 0 <= u:
            values.append(F(0))
        result = widen(nearest(min(values)), nearest(max(values)))
    else:
        if (op == 'ln' and l <= 0) or (op == 'sqrt' and l < 0):
            return 'domain'
        f = {'ln': iv.ln, 'sqrt': iv.sqrt, 'exp': iv.exp}[op]
        # Extremely large exp arguments are trivially outside representable
        # range; avoid unbounded oracle exponents on random binary64 inputs.
        if op == 'exp' and u > 1000:
            return 'range'
        def rounded(x):
            if op == 'exp' and x < -1000:
                return 0.0  # exp(-1000) < half the least subnormal
            return correctly_rounded(f, x)
        result = widen(rounded(l), rounded(u))
    if op != 'ln' and not isinstance(result, str):
        result = max(0.0, result[0]), result[1]
    return result


def case(op, a, b=(0., 0.)):
    result = arithmetic(op, a, b) if op in ('add', 'sub', 'mul', 'div') else unary(op, a)
    out = {'op': op, 'al': bits(a[0]), 'au': bits(a[1]), 'bl': bits(b[0]), 'bu': bits(b[1])}
    if isinstance(result, str):
        out['status'] = result
    else:
        out.update(status='ok', lo=bits(result[0]), hi=bits(result[1]))
    return out


def generate():
    endpoints = [
        (0., 0.), (-0., -0.), (-1., 1.), (-3., -2.), (2., 3.),
        (ETA, ETA), (-ETA, ETA), (0., ETA), (1., math.nextafter(1., INF)),
        (math.nextafter(1., 0.), 1.), (0.5, 0.5), (-0.5, -0.5),
        (MAX, MAX), (-MAX, -MAX), (-MAX, MAX),
        (from_bits(0x0010000000000000), from_bits(0x0010000000000001)),
        (1e-300, 2e-300), (-2e-300, -1e-300), (1e300, 2e300),
        (-1000., -999.), (709., 710.), (-746., -745.),
    ]
    cases = [case(op, a, b) for a in endpoints for b in endpoints
             for op in ('add', 'sub', 'mul', 'div')]
    rng = splitmix64(0x158f1a17)
    def finite():
        while True:
            x = from_bits(next(rng))
            if math.isfinite(x):
                return x
    random_intervals = [tuple(sorted((finite(), finite()))) for _ in range(256)]
    for i, a in enumerate(random_intervals):
        b = random_intervals[(i+1) % len(random_intervals)]
        cases.extend(case(op, a, b) for op in ('add', 'sub', 'mul', 'div'))
    cases.extend(case(op, a) for a in endpoints + random_intervals
                 for op in ('square', 'ln', 'exp', 'sqrt'))
    return {'generator': 'generators/interval_reference.py',
            'oracle': 'exact Fraction; mpmath 1.4.1 intervals, 128 bits doubled, two-precision agreement',
            'cases': cases}


def main():
    result = generate()
    text = json.dumps(result, indent=1) + '\n'
    if '--check' in sys.argv[1:]:
        if OUTPUT.read_text() != text:
            sys.exit(f'{OUTPUT} differs from a fresh generation')
    else:
        OUTPUT.write_text(text)
    print(f'interval: {len(result["cases"])} cases')


if __name__ == '__main__':
    main()
