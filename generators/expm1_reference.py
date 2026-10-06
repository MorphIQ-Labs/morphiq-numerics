#!/usr/bin/env python3
"""Correctly rounded expm1(x) = e^x - 1 for binary64 x: the reference values
expm1 is tested against.

Each value is rounded to nearest, ties to even, into binary64, by the interval
oracle in generators/oracle; e^x - 1 is evaluated in interval arithmetic, so it
never cancels a rounded e^x.

Writes crates/reference/fixtures/expm1.json; with --check, fails if the
committed fixture differs from a fresh generation. Needs mpmath
(generators/requirements.txt).

The cases:
- No published worst cases: Lefevre and Muller (2003) don't cover expm1.
- The thresholds, derived by bisection on binary64 encodings: the largest x
  with a finite result, the largest x whose result rounds to -1, and the edges
  where the result is x itself. Each is recorded with its neighbour.
- Special values: NaN, -1 at -inf, +inf, and +-0 kept with their sign.
- 4,000 inputs from a SplitMix64 stream (Steele, Lea and Flood, OOPSLA 2014):
  across the whole domain, near zero at every scale, and in [-1, 1].

The "precise" section records, for 1,200 SplitMix64 inputs, e^x - 1 to 192 bits
(oracle.precise): the reference for the unrounded fast and accurate results.
"""
import json
import math
import pathlib
import sys

import mpmath
from mpmath import iv

from oracle import bisect, correctly_rounded, from_bits, precise, splitmix64, to_bits

OUTPUT = pathlib.Path(__file__).resolve().parents[1] / 'crates/reference/fixtures/expm1.json'


def expm1_iv(v):
    return iv.exp(v) - 1


def expm1_rn(x):
    """e^x - 1 correctly rounded to binary64."""
    if math.isnan(x):
        return x
    if x == math.inf:
        return math.inf
    if x == -math.inf:
        return -1.0
    if x == 0.0:
        return x  # keeps the sign of zero
    return correctly_rounded(expm1_iv, x)


def thresholds():
    pos = lambda b: from_bits(b)          # noqa: E731
    neg = lambda b: -from_bits(b)         # noqa: E731
    overflow = bisect(to_bits(709.0), to_bits(710.0), lambda b: expm1_rn(pos(b)) == math.inf)
    minus_one = bisect(to_bits(30.0), to_bits(40.0), lambda b: expm1_rn(neg(b)) == -1.0)
    # The edges of the range where expm1(x) = x: the least positive and the
    # greatest negative x whose result differs from x.
    pos_x = bisect(1, to_bits(2.0 ** -40), lambda b: expm1_rn(pos(b)) != pos(b))
    neg_x = bisect(1, to_bits(2.0 ** -40), lambda b: expm1_rn(neg(b)) != neg(b))
    found = {
        'largest x with a finite result': pos(overflow - 1),
        'least x overflowing': pos(overflow),
        'largest x above -1': neg(minus_one - 1),
        'least x rounding to -1': neg(minus_one),
        'largest positive x returning x': pos(pos_x - 1),
        'least positive x not returning x': pos(pos_x),
        'least negative x returning x': neg(neg_x - 1),
        'largest negative x not returning x': neg(neg_x),
    }
    # Below 2^-54 in magnitude the result is x (docs/expm1.md, section 1).
    if found['least positive x not returning x'] < 2.0 ** -54 or \
            -found['largest negative x not returning x'] < 2.0 ** -54:
        sys.exit('expm1(x) = x fails below 2^-54')
    return found


def special_cases():
    return [('special', x) for x in (
        0.0, -0.0, math.inf, -math.inf, math.nan,
        from_bits(0x7FEFFFFFFFFFFFFF), -from_bits(0x7FEFFFFFFFFFFFFF),
        from_bits(1), -from_bits(1), 2.0 ** -1022, -(2.0 ** -1022), 1.0, -1.0,
        0.03125, -0.03125, from_bits(to_bits(0.03125) - 1), -from_bits(to_bits(0.03125) - 1),
    )]


def random_cases():
    words = splitmix64(0x65786D3172656631)
    unit = lambda: (next(words) >> 11) * 2.0 ** -53  # noqa: E731
    cases = []
    for _ in range(2000):
        cases.append(('random, whole domain', -40.0 + unit() * 750.0))
    for _ in range(1000):
        e = -60 + next(words) % 60
        x = (1.0 + unit()) * 2.0 ** e
        cases.append(('random, near zero', -x if next(words) & 1 else x))
    for _ in range(1000):
        cases.append(('random, [-1, 1]', -1.0 + unit() * 2.0))
    return cases


def precise_cases():
    words = splitmix64(0x65786D3170726531)
    unit = lambda: (next(words) >> 11) * 2.0 ** -53  # noqa: E731
    xs = [-37.0 + unit() * 746.0 for _ in range(500)]           # the exp-based range
    for _ in range(100):                                        # just outside 2^-5
        x = 0.03125 * (1.0 + unit())
        xs.append(-x if next(words) & 1 else x)
    for _ in range(600):                                        # 2^-54 <= |x| < 2^-5
        x = (1.0 + unit()) * 2.0 ** (-54 + next(words) % 49)
        xs.append(-x if next(words) & 1 else x)
    out = []
    for x in xs:
        negative, m, e = precise(expm1_iv, x)
        out.append({'x': f'{to_bits(x):016x}', 'negative': negative, 'm': f'{m:048x}', 'e': e})
    return out


def document():
    found = thresholds()
    cases = special_cases()
    cases += [(f'threshold: {name}', x) for name, x in found.items()]
    cases += random_cases()
    return {
        'generator': 'generators/expm1_reference.py',
        'oracle': f'mpmath {mpmath.__version__} interval arithmetic, from 128 bits, '
                  'doubled until both ends of the enclosure round alike',
        'rounding': 'to nearest, ties to even; overflow to +inf',
        'sources': [
            'IEEE 754-2019, section 9.2 (special values)',
            'Steele, Lea and Flood, OOPSLA 2014, Figure 16 (the random inputs)',
        ],
        'thresholds': {name: f'{to_bits(x):016x}' for name, x in found.items()},
        'precise': precise_cases(),
        'cases': [
            {'kind': kind, 'x': f'{to_bits(x):016x}', 'expm1': f'{to_bits(expm1_rn(x)):016x}'}
            for kind, x in cases
        ],
    }


def main():
    data = json.dumps(document(), indent=1) + '\n'
    if '--check' in sys.argv[1:]:
        if OUTPUT.read_text() != data:
            sys.exit(f'{OUTPUT} differs from a fresh generation')
        return
    OUTPUT.write_text(data)


if __name__ == '__main__':
    main()
