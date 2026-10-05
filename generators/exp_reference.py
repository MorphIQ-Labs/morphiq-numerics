#!/usr/bin/env python3
"""Correctly rounded exp(x) for binary64 x: the reference values exp is tested
against.

Each value is exp(x) rounded to nearest, ties to even, into binary64, with
subnormal results rounded once and overflow giving +inf. It is computed with
mpmath's interval arithmetic: the precision is doubled from 128 bits until both
ends of the enclosure of exp(x) round to the same binary64 number, which is
then the correctly rounded result. Rounding is done in integer arithmetic. So
no value depends on a tolerance or on the precision being "enough".

Writes crates/reference/fixtures/exp.json; with --check, fails if the committed
fixture differs from a fresh generation. Needs mpmath (generators/requirements.txt).

The cases:
- V. Lefevre, J.-M. Muller, "Worst cases for correct rounding of the elementary
  functions in double precision", revised version dated August 14, 2003
  (https://perso.ens-lyon.fr/jean-michel.muller/TMDworstcases.pdf, SHA-256
  718e25ca37ab8d826586fb15dd127c578fcae9ec60c4d5caee82120698d99c4f), Table 4: the hardest
  input to round in each interval of the full range. Each is checked against
  the bit pattern the table states for its exponential, so a mistyped input
  fails here.
- The thresholds, derived by bisection on binary64 encodings, not copied: the
  largest x whose result is finite, the smallest whose result is nonzero, the
  smallest whose result is normal, and the arguments either side of 0 whose
  result is exactly 1. Those last two are checked against the same paper's
  Table 2. Each threshold is recorded with its neighbour.
- Special values: +-0, +-inf, a NaN, the extreme finite and subnormal inputs.
- 4,000 inputs from a SplitMix64 stream (Steele, Lea and Flood, OOPSLA 2014):
  across the whole domain, near zero, and in [-50, 50].
"""
import json
import math
import pathlib
import sys

import mpmath
from mpmath import iv

from oracle import (bisect, check_worst_case, correctly_rounded, from_bits,
                    splitmix64, to_bits)

OUTPUT = pathlib.Path(__file__).resolve().parents[1] / 'crates/reference/fixtures/exp.json'


def exp_rn(x):
    """exp(x) correctly rounded to binary64."""
    if math.isnan(x):
        return x
    if x == math.inf:
        return math.inf
    if x == -math.inf or x == 0.0:
        return 0.0 if x == -math.inf else 1.0
    return correctly_rounded(iv.exp, x)


# Lefevre & Muller, Table 4: (sign, input digits, input exponent, the digits of
# exp(x) as printed: 53 significant bits, then the bits after them).
TABLE_4 = [
    (-1, '1.1110110100110001100011101111101101100010011111101010', -27,
     '1.1111111111111111111111111000010010110011100111000100', '1' + '1' * 59 + '0001'),
    (-1, '1.0100000000000000000000000000000000000000000000110010', -46,
     '1.1111111111111111111111111111111111111111111101100000', '0' + '0' * 84 + '1010'),
    (-1, '1.0000000000000000000000000000000000000000000000000001', -51,
     '1.1111111111111111111111111111111111111111111111111100', '0' + '0' * 100 + '1010'),
    (1, '1.1111111111111111111111111111111111111111111111111111', -53,
     '1.0000000000000000000000000000000000000000000000000000', '1' + '1' * 104 + '0101'),
    (1, '1.1111111111111111111111111111111111111111111110000000', -46,
     '1.0000000000000000000000000000000000000000000001111111', '1' + '1' * 83 + '0101'),
    (1, '1.0001111111111111111111111111111111111111111110101111', -45,
     '1.0000000000000000000000000000000000000000000010001111', '1' + '1' * 83 + '0000'),
    (1, '110.00001111010100101111001101111010111011001111110100', 0,
     '110101100.01010000101101000000100111001000101011101110', '0' + '0' * 57 + '1000'),
]


def table_4_cases():
    return [('worst case', check_worst_case(mpmath.exp, *entry, 'Table 4')) for entry in TABLE_4]


def thresholds():
    pos = lambda b: from_bits(b)          # noqa: E731
    neg = lambda b: -from_bits(b)         # noqa: E731
    overflow = bisect(to_bits(709.0), to_bits(710.0), lambda b: exp_rn(pos(b)) == math.inf)
    zero = bisect(to_bits(744.0), to_bits(746.0), lambda b: exp_rn(neg(b)) == 0.0)
    subnormal = bisect(to_bits(708.0), to_bits(709.0), lambda b: exp_rn(neg(b)) < 2.0 ** -1022)
    above_one = bisect(1, to_bits(2.0 ** -50), lambda b: exp_rn(pos(b)) != 1.0)
    below_one = bisect(1, to_bits(2.0 ** -50), lambda b: exp_rn(neg(b)) != 1.0)
    found = {
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
    # Lefevre & Muller, Table 2: exp(e) rounds to 1 for 0 <= e < 2^-53 and for
    # 0 <= -e <= 2^-54.
    if found['least positive x above 1'] != 2.0 ** -53:
        sys.exit(f"exp(e) = 1 ends at {found['least positive x above 1']!r}, not 2^-53")
    if found['least negative x rounding to 1'] != -(2.0 ** -54):
        sys.exit(f"exp(-e) = 1 ends at {found['least negative x rounding to 1']!r}, not -2^-54")
    return found


def random_cases():
    words = splitmix64(0x6578705F72656631)
    unit = lambda: (next(words) >> 11) * 2.0 ** -53  # noqa: E731
    cases = []
    for _ in range(2000):
        cases.append(('random, whole domain', -745.5 + unit() * 1455.5))
    for _ in range(1000):
        e = -60 + next(words) % 60
        x = (1.0 + unit()) * 2.0 ** e
        cases.append(('random, near zero', -x if next(words) & 1 else x))
    for _ in range(1000):
        cases.append(('random, [-50, 50]', -50.0 + unit() * 100.0))
    return cases


def special_cases():
    return [('special', x) for x in (
        0.0, -0.0, math.inf, -math.inf, math.nan,
        from_bits(0x7FEFFFFFFFFFFFFF), -from_bits(0x7FEFFFFFFFFFFFFF),
        from_bits(1), -from_bits(1), 2.0 ** -1022, -(2.0 ** -1022), 1.0, -1.0,
    )]


def document():
    found = thresholds()
    cases = special_cases() + table_4_cases()
    cases += [(f'threshold: {name}', x) for name, x in found.items()]
    cases += random_cases()
    return {
        'generator': 'generators/exp_reference.py',
        'oracle': f'mpmath {mpmath.__version__} interval arithmetic, from 128 bits, '
                  'doubled until both ends of the enclosure round alike',
        'rounding': 'to nearest, ties to even; subnormals rounded once; overflow to +inf',
        'sources': [
            'Lefevre and Muller, Worst cases for correct rounding of the elementary '
            'functions in double precision, revised 2003, Tables 2 and 4',
            'Steele, Lea and Flood, OOPSLA 2014, Figure 16 (the random inputs)',
        ],
        'thresholds': {name: f'{to_bits(x):016x}' for name, x in found.items()},
        'cases': [
            {'kind': kind, 'x': f'{to_bits(x):016x}', 'exp': f'{to_bits(exp_rn(x)):016x}'}
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
