#!/usr/bin/env python3
"""Correctly rounded ln(x) and ln_1p(x) = ln(1 + x) for binary64 x: the
reference values ln and ln_1p are tested against.

Each value is rounded to nearest, ties to even, into binary64, by the interval
oracle in generators/oracle (mpmath interval arithmetic, precision doubled until
both ends of the enclosure round alike). ln_1p's enclosure is of ln(1 + x) with
1 + x formed in interval arithmetic, so it is never rounded first.

Writes crates/reference/fixtures/ln.json; with --check, fails if the committed
fixture differs from a fresh generation. Needs mpmath (generators/requirements.txt).

The cases:
- ln: V. Lefevre, J.-M. Muller, "Worst cases for correct rounding of the
  elementary functions in double precision", revised version dated August 14,
  2003 (https://perso.ens-lyon.fr/jean-michel.muller/TMDworstcases.pdf, SHA-256
  718e25ca37ab8d826586fb15dd127c578fcae9ec60c4d5caee82120698d99c4f), Table 5:
  the hardest input to round in each interval of the full range. Each is
  checked against the bit pattern the table states, so a mistyped input fails.
  The paper gives no worst cases for ln(1 + x); ln_1p has none here.
- Special values, as IEEE 754-2019 section 9.2 specifies them: NaN for
  negative arguments, ln(+-0) = -inf, ln(1) = +0, ln_1p(-1) = -inf, and
  ln_1p(+-0) = +-0.
- Inputs from a SplitMix64 stream (Steele, Lea and Flood, OOPSLA 2014): ln over
  every positive binade including the subnormals, near 1, and in [0.5, 2];
  ln_1p near 0 at every scale, across (-1, 1), near -1, and large.
"""
import json
import math
import pathlib
import sys

import mpmath
from mpmath import iv

from oracle import check_worst_case, correctly_rounded, from_bits, splitmix64, to_bits

OUTPUT = pathlib.Path(__file__).resolve().parents[1] / 'crates/reference/fixtures/ln.json'


def ln_rn(x):
    """ln(x) correctly rounded to binary64."""
    if math.isnan(x) or x < 0:
        return math.nan
    if x == 0:
        return -math.inf
    if x == math.inf:
        return math.inf
    if x == 1:
        return 0.0
    return correctly_rounded(iv.log, x)


def ln_1p_rn(x):
    """ln(1 + x) correctly rounded to binary64, without rounding 1 + x."""
    if math.isnan(x) or x < -1:
        return math.nan
    if x == -1:
        return -math.inf
    if x == math.inf:
        return math.inf
    if x == 0:
        return x  # keeps the sign of zero
    return correctly_rounded(lambda v: iv.log(1 + v), x)


# Lefevre & Muller, Table 5: (sign, input digits, input exponent, the digits of
# ln(x) as printed: 53 significant bits, then the bits after them).
TABLE_5 = [
    (1, '1.1110101001110001110110000101110011101110000000100000', -509,
     '-101100000.00101001011010100110011010110100001011111111', '1' + '1' * 60 + '0000'),
    (1, '1.1001010001110110111000110000010011001101011111000111', -384,
     '-100001001.10110110000011001010111101000111101100110101', '1' + '0' * 60 + '1010'),
    (1, '1.0010011011101001110001001101001100100111100101100000', -232,
     '-10100000.101010110010110000100101111001101000010000100', '0' + '0' * 60 + '1001'),
    (1, '1.0110000100111001010101011101110010000000001011111000', -35,
     '-10111.111100000010111110011011101011110110000000110101', '0' + '1' * 60 + '0011'),
    (1, '1.0110001010101000100001100001001101100010100110110110', 678,
     '111010110.01000111100111101011101001111100100101110001', '0' + '0' * 64 + '1110'),
]


def ln_cases():
    cases = [('special', x) for x in (
        math.nan, -1.0, -math.inf, -0.0, 0.0, 1.0, math.inf,
        from_bits(1), 2.0 ** -1022, from_bits(0x7FEFFFFFFFFFFFFF), 2.0, 0.5,
        from_bits(to_bits(1.0) + 1), from_bits(to_bits(1.0) - 1),
    )]
    cases += [('worst case', check_worst_case(mpmath.log, *entry, 'Table 5')) for entry in TABLE_5]
    words = splitmix64(0x6C6E5F7265663031)
    for _ in range(2000):
        # Every positive finite encoding, subnormals included.
        b = next(words) % 0x7FF0000000000000
        cases.append(('random, every binade', from_bits(b or 1)))
    for _ in range(1000):
        k = 1 + next(words) % 60
        u = 1.0 + (next(words) >> 11) * 2.0 ** -53
        cases.append(('random, near 1', 1.0 + u * 2.0 ** -k if next(words) & 1 else 1.0 - u * 2.0 ** -(k + 1)))
    for _ in range(1000):
        cases.append(('random, [0.5, 2]', 0.5 + (next(words) >> 11) * 2.0 ** -53 * 1.5))
    return cases


def ln_1p_cases():
    cases = [('special', x) for x in (
        math.nan, -2.0, -math.inf, -1.0, -0.0, 0.0, math.inf,
        from_bits(1), -from_bits(1), 2.0 ** -1022, -(2.0 ** -1022),
        from_bits(0x7FEFFFFFFFFFFFFF), from_bits(to_bits(-1.0) - 1), 1.0, -0.5,
    )]
    words = splitmix64(0x6C6E31705F726566)
    unit = lambda: (next(words) >> 11) * 2.0 ** -53  # noqa: E731
    for _ in range(2000):
        # Magnitudes from the least subnormal up to 1/2, either sign.
        e = -1074 + next(words) % 1073
        if e >= -1022:
            x = (1.0 + unit()) * 2.0 ** e
        else:
            x = from_bits(1 + next(words) % ((1 << 52) - 1))
        cases.append(('random, near 0', -x if next(words) & 1 else x))
    for _ in range(1000):
        cases.append(('random, (-1, 1)', -1.0 + unit() * 2.0))
    for _ in range(500):
        k = 1 + next(words) % 60
        cases.append(('random, near -1', -1.0 + (1.0 + unit()) * 2.0 ** -(k + 1)))
    for _ in range(500):
        cases.append(('random, large', (1.0 + unit()) * 2.0 ** (next(words) % 1024)))
    return [(kind, x) for kind, x in cases if not (x <= -1.0 and kind.startswith('random'))]


def document():
    return {
        'generator': 'generators/ln_reference.py',
        'oracle': f'mpmath {mpmath.__version__} interval arithmetic, from 128 bits, '
                  'doubled until both ends of the enclosure round alike',
        'rounding': 'to nearest, ties to even; subnormals rounded once',
        'sources': [
            'Lefevre and Muller, Worst cases for correct rounding of the elementary '
            'functions in double precision, revised 2003, Table 5',
            'IEEE 754-2019, section 9.2 (special values)',
            'Steele, Lea and Flood, OOPSLA 2014, Figure 16 (the random inputs)',
        ],
        'ln': [
            {'kind': kind, 'x': f'{to_bits(x):016x}', 'ln': f'{to_bits(ln_rn(x)):016x}'}
            for kind, x in ln_cases()
        ],
        'ln_1p': [
            {'kind': kind, 'x': f'{to_bits(x):016x}', 'ln_1p': f'{to_bits(ln_1p_rn(x)):016x}'}
            for kind, x in ln_1p_cases()
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
