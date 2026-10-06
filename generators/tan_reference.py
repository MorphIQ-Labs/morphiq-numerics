#!/usr/bin/env python3
"""Correctly rounded tan(x) for binary64 x: the reference values tan is
tested against.

Each value is rounded to nearest, ties to even, into binary64, by the interval
oracle in generators/oracle.

Writes crates/reference/fixtures/tan.json; with --check, fails if the committed
fixture differs from a fresh generation. Needs mpmath
(generators/requirements.txt).

The cases:
- V. Lefevre, J.-M. Muller, "Worst cases for correct rounding of the elementary
  functions in double precision", revised version dated August 14, 2003
  (https://perso.ens-lyon.fr/jean-michel.muller/TMDworstcases.pdf, SHA-256
  718e25ca37ab8d826586fb15dd127c578fcae9ec60c4d5caee82120698d99c4f): Table 12
  (tan on [2^-25, arctan 2]), each checked against the bits the table states.
- The threshold up to which tan(x) = x, by bisection (Table 2 gives
  1.817 2^-27), recorded with its neighbour. Above it the equality returns,
  for 2^-26 <= x < 1.1447 2^-26, which those arguments' cases exercise.
- Special values, the binary64 numbers nearest multiples of pi/2, where tan is
  large or near zero, and the closest approach to one (generators/trig_reduction.py).
- 4,000 inputs from a SplitMix64 stream (Steele, Lea and Flood, OOPSLA 2014):
  every binade, [-pi, pi], and near zero at every scale.

The "precise" section records, for 1,200 SplitMix64 inputs, tan to 256 bits
(oracle.precise).
"""
import json
import math
import pathlib
import sys

import mpmath
from mpmath import iv

from oracle import (bisect, check_worst_case, correctly_rounded, from_bits,
                    precise, splitmix64, to_bits)

OUTPUT = pathlib.Path(__file__).resolve().parents[1] / 'crates/reference/fixtures/tan.json'


def tan_rn(x):
    if math.isnan(x) or math.isinf(x):
        return math.nan
    if x == 0.0:
        return x
    return correctly_rounded(iv.tan, x)


TABLE_12 = [
    (1, '1.1101111111111111111111111111111111111111111100011111', -22,
     '1.1110000000000000000000000000000000000000000101010001', '0' + '1' * 78 + '0100'),
    (1, '1.0110011111111111111111111111111111111010000100010100', -18,
     '1.0110100000000000000000000000000000001000111001100001', '1' + '1' * 57 + '0100'),
    (1, '1.0101000001001000011010110010111110000111000000010100', -5,
     '1.0101000001111000110011101011111111111001110001110010', '1' + '0' * 57 + '1001'),
    (1, '0.10100011010101100001101110010001001000011010100110110', 0,
     '0.10111101110100100100111110111001110011000001010011110', '1' + '1' * 54 + '0011'),
]


def thresholds():
    """tan(x) = x while x^3/3 stays under half an ulp of x: for x = m 2^-27 that
    is m^3 < 6, and for x = m 2^-26 it is m^3 < 1.5. So the set where tan(x) = x
    has a hole, and the edge that bounds it from below lies in [2^-27, 2^-26):
    bisected there. Below 2^-27 every x qualifies (m^3 < 24); the generator
    checks the binade's ends."""
    lo, hi = to_bits(2.0 ** -27), to_bits(2.0 ** -26)
    assert tan_rn(from_bits(lo)) == from_bits(lo) and tan_rn(from_bits(hi - 1)) != from_bits(hi - 1)
    b = bisect(lo, hi - 1, lambda b: tan_rn(from_bits(b)) != from_bits(b))
    return {'largest x with tan(y) = y for every |y| <= x': from_bits(b - 1),
            'least x with tan(x) != x': from_bits(b)}


def special_cases():
    cases = [('special', x) for x in (
        0.0, -0.0, math.inf, -math.inf, math.nan,
        from_bits(0x7FEFFFFFFFFFFFFF), -from_bits(0x7FEFFFFFFFFFFFFF),
        from_bits(1), -from_bits(1), 2.0 ** -1022, 1.0, -1.0,
        6381956970095103 * 2.0 ** 797,
    )]
    with mpmath.workprec(200):
        for k in (1, 2, 3, 4, 5, 7, 100, 1001, 10 ** 6 + 1):
            x = float(k * mpmath.pi / 2)
            for y in (x, from_bits(to_bits(x) - 1), from_bits(to_bits(x) + 1)):
                cases.append(('near k pi/2', y))
    return cases


def random_cases():
    words = splitmix64(0x74616E5F72656631)
    unit = lambda: (next(words) >> 11) * 2.0 ** -53  # noqa: E731
    cases = []
    for _ in range(2000):
        x = from_bits(next(words) % 0x7FF0000000000000 or 1)
        cases.append(('random, every binade', -x if next(words) & 1 else x))
    for _ in range(1000):
        cases.append(('random, [-pi, pi]', (unit() * 2.0 - 1.0) * 3.141592653589793))
    for _ in range(1000):
        x = (1.0 + unit()) * 2.0 ** (-60 + next(words) % 60)
        cases.append(('random, near zero', -x if next(words) & 1 else x))
    return cases


def precise_cases():
    words = splitmix64(0x74616E5F70726531)
    unit = lambda: (next(words) >> 11) * 2.0 ** -53  # noqa: E731
    xs = [(unit() * 2.0 - 1.0) * 3.2 for _ in range(500)]
    for _ in range(400):
        b = to_bits(2.0 ** -26) + next(words) % (to_bits(2.0 ** 1023) - to_bits(2.0 ** -26))
        xs.append(-from_bits(b) if next(words) & 1 else from_bits(b))
    for _ in range(300):
        xs.append((1.0 + unit()) * 2.0 ** (-26 + next(words) % 22))
    out = []
    for x in xs:
        negative, m, e = precise(iv.tan, x, bits=256)
        out.append({'x': f'{to_bits(x):016x}', 'negative': negative, 'm': f'{m:064x}', 'e': e})
    return out


def document():
    found = thresholds()
    cases = special_cases()
    cases += [('worst case', check_worst_case(mpmath.tan, *e, 'Table 12')) for e in TABLE_12]
    cases += [(f'threshold: {name}', x) for name, x in found.items()]
    cases += random_cases()
    return {
        'generator': 'generators/tan_reference.py',
        'oracle': f'mpmath {mpmath.__version__} interval arithmetic, from 128 bits, '
                  'doubled until both ends of the enclosure round alike at two precisions',
        'rounding': 'to nearest, ties to even',
        'sources': [
            'Lefevre and Muller, Worst cases for correct rounding of the elementary '
            'functions in double precision, revised 2003, Tables 2 and 12',
            'Steele, Lea and Flood, OOPSLA 2014, Figure 16 (the random inputs)',
        ],
        'thresholds': {name: f'{to_bits(x):016x}' for name, x in found.items()},
        'precise': precise_cases(),
        'cases': [
            {'kind': kind, 'x': f'{to_bits(x):016x}', 'tan': f'{to_bits(tan_rn(x)):016x}'}
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
