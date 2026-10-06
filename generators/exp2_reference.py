#!/usr/bin/env python3
"""Correctly rounded exp2(x) = 2^x for binary64 x: the reference values exp2 is
tested against.

Each value is rounded to nearest, ties to even, into binary64, by the interval
oracle in generators/oracle (subnormal results rounded once, overflow to +inf).

Writes crates/reference/fixtures/exp2.json; with --check, fails if the committed
fixture differs from a fresh generation. Needs mpmath (generators/requirements.txt).

The cases:
- V. Lefevre, J.-M. Muller, "Worst cases for correct rounding of the elementary
  functions in double precision", revised version dated August 14, 2003
  (https://perso.ens-lyon.fr/jean-michel.muller/TMDworstcases.pdf, SHA-256
  718e25ca37ab8d826586fb15dd127c578fcae9ec60c4d5caee82120698d99c4f), Table 6:
  the hardest input to round in each interval of the full range, each checked
  against the bits the table states for 2^x.
- The thresholds, derived by bisection on binary64 encodings: the largest x
  whose result is finite, the smallest whose result is nonzero, the smallest
  whose result is normal, and the arguments either side of 0 whose result is
  exactly 1. Each is recorded with its neighbour.
- Special values, and integers across the whole range, where 2^x is exact.
- 4,000 inputs from a SplitMix64 stream (Steele, Lea and Flood, OOPSLA 2014):
  across the whole domain, near zero, and in [-2, 2].

The "precise" section records, for 1,200 SplitMix64 inputs, 2^x to 192 bits
(oracle.precise): the reference for the unrounded fast and accurate results.
"""
import json
import math
import pathlib
import sys

import mpmath
from mpmath import iv

from oracle import (bisect, check_worst_case, correctly_rounded, from_bits,
                    precise, splitmix64, to_bits)

OUTPUT = pathlib.Path(__file__).resolve().parents[1] / 'crates/reference/fixtures/exp2.json'


def exp2_rn(x):
    """2^x correctly rounded to binary64."""
    if math.isnan(x):
        return x
    if x == math.inf:
        return math.inf
    if x == -math.inf:
        return 0.0
    if x == 0.0:
        return 1.0
    return correctly_rounded(lambda v: iv.mpf(2) ** v, x)


# Lefevre & Muller, Table 6: (sign, input digits, input exponent, the digits of
# 2^x as printed, then the bits after the first 53 significant ones).
TABLE_6 = [
    (-1, '1.0010100001100011101010111010111010101111011110110010', -15,
     '0.11111111111111100110010100011111010001100000111101111', '0' + '0' * 57 + '1110'),
    (-1, '1.0100000101101111011011000110010001000101101011001111', -20,
     '0.11111111111111111111001000010011001010111010011001110', '1' + '1' * 57 + '0000'),
    (-1, '1.0000010101010110000000011100100010101011001111110001', -32,
     '0.11111111111111111111111111111111010010101101101100001', '1' + '1' * 57 + '0000'),
    (-1, '1.0001100001011011100011011011011011010101100000011101', -33,
     '0.11111111111111111111111111111111100111101101010111100', '0' + '0' * 57 + '1100'),
    (1, '1.1011111110111011110111100100010011101101111111000101', -25,
     '1.0000000000000000000000001001101100101100001110000101', '0' + '0' * 59 + '1011'),
    (1, '1.1110010001011001011001010010011010111111100101001101', -10,
     '1.0000000001010011111111000010111011000010101101010011', '0' + '1' * 59 + '0100'),
]


def table_6_cases():
    return [('worst case', check_worst_case(lambda v: mpmath.mpf(2) ** v, *entry, 'Table 6'))
            for entry in TABLE_6]


def thresholds():
    pos = lambda b: from_bits(b)          # noqa: E731
    neg = lambda b: -from_bits(b)         # noqa: E731
    overflow = bisect(to_bits(1023.0), to_bits(1025.0), lambda b: exp2_rn(pos(b)) == math.inf)
    zero = bisect(to_bits(1074.0), to_bits(1076.0), lambda b: exp2_rn(neg(b)) == 0.0)
    subnormal = bisect(to_bits(1021.0), to_bits(1023.0), lambda b: exp2_rn(neg(b)) < 2.0 ** -1022)
    above_one = bisect(1, to_bits(2.0 ** -50), lambda b: exp2_rn(pos(b)) != 1.0)
    below_one = bisect(1, to_bits(2.0 ** -50), lambda b: exp2_rn(neg(b)) != 1.0)
    return {
        'largest x with a finite result': pos(overflow - 1),
        'least x overflowing': pos(overflow),
        'least x with a nonzero result': neg(zero - 1),
        'largest x rounding to 0': neg(zero),
        'least x with a normal result': neg(subnormal - 1),
        'largest x with a subnormal result': neg(subnormal),
        'largest positive x rounding to 1': pos(above_one - 1),
        'least positive x above 1': pos(above_one),
        'least negative x rounding to 1': neg(below_one - 1),
        'largest negative x below 1': neg(below_one),
    }


def special_cases():
    cases = [('special', x) for x in (
        0.0, -0.0, math.inf, -math.inf, math.nan,
        from_bits(0x7FEFFFFFFFFFFFFF), -from_bits(0x7FEFFFFFFFFFFFFF),
        from_bits(1), -from_bits(1), 2.0 ** -1022, -(2.0 ** -1022), 0.5, -0.5,
    )]
    # Integers: exact wherever representable, including subnormal results.
    cases += [('integer', float(k)) for k in (-1076, -1075, -1074, -1073, -1050, -1023,
                                             -1022, -1021, -2, -1, 1, 2, 3, 52, 53,
                                             1000, 1022, 1023, 1024, 1025)]
    return cases


def random_cases():
    words = splitmix64(0x6578703272656631)
    unit = lambda: (next(words) >> 11) * 2.0 ** -53  # noqa: E731
    cases = []
    for _ in range(2000):
        cases.append(('random, whole domain', -1076.0 + unit() * 2101.0))
    for _ in range(1000):
        e = -60 + next(words) % 60
        x = (1.0 + unit()) * 2.0 ** e
        cases.append(('random, near zero', -x if next(words) & 1 else x))
    for _ in range(1000):
        cases.append(('random, [-2, 2]', -2.0 + unit() * 4.0))
    return cases


def precise_cases():
    words = splitmix64(0x6578703270726531)
    unit = lambda: (next(words) >> 11) * 2.0 ** -53  # noqa: E731
    xs = [-1021.9 + unit() * 2044.8 for _ in range(600)]         # normal results
    xs += [-1074.9 + unit() * 53.0 for _ in range(300)]          # subnormal results
    for _ in range(300):                                         # small arguments
        x = (1.0 + unit()) * 2.0 ** (-60 + next(words) % 59)
        xs.append(-x if next(words) & 1 else x)
    out = []
    for x in xs:
        _, m, e = precise(lambda v: iv.mpf(2) ** v, x)
        out.append({'x': f'{to_bits(x):016x}', 'm': f'{m:048x}', 'e': e})
    return out


def document():
    found = thresholds()
    cases = special_cases() + table_6_cases()
    cases += [(f'threshold: {name}', x) for name, x in found.items()]
    cases += random_cases()
    return {
        'generator': 'generators/exp2_reference.py',
        'oracle': f'mpmath {mpmath.__version__} interval arithmetic, from 128 bits, '
                  'doubled until both ends of the enclosure round alike',
        'rounding': 'to nearest, ties to even; subnormals rounded once; overflow to +inf',
        'sources': [
            'Lefevre and Muller, Worst cases for correct rounding of the elementary '
            'functions in double precision, revised 2003, Table 6',
            'Steele, Lea and Flood, OOPSLA 2014, Figure 16 (the random inputs)',
        ],
        'thresholds': {name: f'{to_bits(x):016x}' for name, x in found.items()},
        'precise': precise_cases(),
        'cases': [
            {'kind': kind, 'x': f'{to_bits(x):016x}', 'exp2': f'{to_bits(exp2_rn(x)):016x}'}
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
