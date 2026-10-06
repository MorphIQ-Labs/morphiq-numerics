#!/usr/bin/env python3
"""Correctly rounded sin(x) and cos(x) for binary64 x: the reference values
sin, cos and sincos are tested against.

Each value is rounded to nearest, ties to even, into binary64, by the interval
oracle in generators/oracle.

Writes crates/reference/fixtures/sin_cos.json; with --check, fails if the
committed fixture differs from a fresh generation. Needs mpmath
(generators/requirements.txt).

The cases:
- V. Lefevre, J.-M. Muller, "Worst cases for correct rounding of the elementary
  functions in double precision", revised version dated August 14, 2003
  (https://perso.ens-lyon.fr/jean-michel.muller/TMDworstcases.pdf, SHA-256
  718e25ca37ab8d826586fb15dd127c578fcae9ec60c4d5caee82120698d99c4f): Table 8
  (sin on [2^-24, 2 + 4675/8192]) and Table 10 (cos on [2^-25, 12867/8192]),
  each checked against the bits the table states.
- The thresholds, derived by bisection on binary64 encodings:
  - sin(x) = x up to the least x where it isn't (Table 2 gives 1.4422 2^-26);
  - cos(x) for |x| < 2^-25 is a step function of |x| with values 1 - k 2^-53,
    k = 0..4; each step's last argument and the next are recorded
    (docs/sin_cos.md, section 1).
- Special values, and multiples of pi/2 and pi nearest representable inputs.
- 4,000 inputs from a SplitMix64 stream (Steele, Lea and Flood, OOPSLA 2014):
  every binade, [-2 pi, 2 pi], and near zero at every scale.

The "precise" section records, for 1,200 SplitMix64 inputs, sin and cos to 256
bits (oracle.precise): the reference for the unrounded fast and accurate
results, whose bounds reach 2^-143. The "reduction" section records, for 607
arguments x >= pi/4, k mod 4 and r = x - k pi/2 (|r| <= pi/4) to 256 bits,
computed at 2,400 bits, where r keeps over 2,000 bits even at the closest
approach.
"""
import json
import math
import pathlib
import sys

import mpmath
from mpmath import iv

from oracle import (bisect, check_worst_case, correctly_rounded, from_bits,
                    precise, splitmix64, to_bits)

OUTPUT = pathlib.Path(__file__).resolve().parents[1] / 'crates/reference/fixtures/sin_cos.json'


def rn(f, special):
    def g(x):
        if math.isnan(x) or math.isinf(x):
            return math.nan
        if x == 0.0:
            return special(x)
        return correctly_rounded(f, x)
    return g


sin_rn = rn(iv.sin, lambda x: x)       # sin(+-0) = +-0
cos_rn = rn(iv.cos, lambda x: 1.0)

# Lefevre & Muller: (sign, input digits, input exponent, the digits of f(x) as
# printed, then the bits after the first 53 significant ones).
TABLE_8 = [
    (1, '1.1110000000000000000000000000000000000000000111000010', -20,
     '1.1101111111111111111111111111111111111111000000101110', '0' + '0' * 72 + '1110'),
    (1, '1.0101100110001011101011101001111001100011001011110110', -7,
     '1.0101100110001010000010101110101001001000100110010110', '0' + '1' * 59 + '0000'),
    (1, '1.1111111001110110011101110011100111010000111101101101', -2,
     '1.1110100110010101000001110011000011000100011010010101', '1' + '1' * 65 + '0000'),
    (1, '1.1001001000011111101101010100010001000010110100011000', 0,
     '0.11111111111111111111111111111111111111111111111111111', '1' + '1' * 54 + '0110'),
    (1, '1.0110011101010110011101000101011101110000101001010001', 1,
     '1.0100111111110011010100001110010000010010100000100001', '0' + '0' * 54 + '1010'),
]
TABLE_10 = [
    (1, '1.1000000000000000000000000000000000000000000000001001', -23,
     '0.11111111111111111111111111111111111111111111101110000', '0' + '0' * 88 + '1101'),
    (1, '1.1000000000000000000000000000000000000000000000100100', -22,
     '0.11111111111111111111111111111111111111111110111000000', '0' + '0' * 82 + '1101'),
    (1, '1.0010000000000000000000000000000000000000111100110000', -18,
     '0.11111111111111111111111111111111111101011110000000000', '0' + '0' * 60 + '1001'),
    (1, '1.0000011010110101000001010101010100001110011010110010', -9,
     '0.11111111111111111101111001001101000111111101111111110', '0' + '0' * 58 + '1100'),
    (1, '1.1001011111001100110100111101001011000100001110001111', -6,
     '0.11111111111010111011001101011101010000111000010101000', '1' + '1' * 55 + '0111'),
    (1, '1.0110101110001010011000100111001111010111110000100001', 0,
     '1.0011001101111111110001011011000001110010110001010010', '1' + '0' * 54 + '1011'),
]


def thresholds():
    found = {}
    # sin(x) = x below the least x where they differ.
    b = bisect(1, to_bits(2.0 ** -20), lambda b: sin_rn(from_bits(b)) != from_bits(b))
    found['largest x with sin(x) = x'] = from_bits(b - 1)
    found['least x with sin(x) != x'] = from_bits(b)
    # cos on [0, 2^-25): the last argument of each step 1 - k 2^-53, k = 0..3;
    # the step to 1 - 4 2^-53 continues past 2^-25.
    for k in range(4):
        value = 1.0 - k * 2.0 ** -53
        b = bisect(1, to_bits(2.0 ** -25), lambda b: cos_rn(from_bits(b)) < value)
        found[f'largest x with cos(x) = 1 - {k} 2^-53'] = from_bits(b - 1)
        found[f'least x with cos(x) < 1 - {k} 2^-53'] = from_bits(b)
    return found


def special_cases():
    pi = mpmath.pi
    cases = [('special', x) for x in (
        0.0, -0.0, math.inf, -math.inf, math.nan,
        from_bits(0x7FEFFFFFFFFFFFFF), -from_bits(0x7FEFFFFFFFFFFFFF),
        from_bits(1), -from_bits(1), 2.0 ** -1022, 1.0, -1.0,
    )]
    # The binary64 numbers nearest k pi/2, where sin or cos is near zero.
    with mpmath.workprec(200):
        for k in (1, 2, 3, 4, 5, 6, 7, 8, 100, 1000, 10 ** 6):
            v = k * pi / 2
            x = float(v)
            for y in (x, from_bits(to_bits(x) - 1), from_bits(to_bits(x) + 1)):
                cases.append(('near k pi/2', y))
    return cases


def random_cases():
    words = splitmix64(0x73696E636F737266)
    unit = lambda: (next(words) >> 11) * 2.0 ** -53  # noqa: E731
    cases = []
    for _ in range(2000):
        b = next(words) % 0x7FF0000000000000
        x = from_bits(b or 1)
        cases.append(('random, every binade', -x if next(words) & 1 else x))
    for _ in range(1000):
        cases.append(('random, [-2 pi, 2 pi]', (unit() * 2.0 - 1.0) * 6.283185307179586))
    for _ in range(1000):
        x = (1.0 + unit()) * 2.0 ** (-60 + next(words) % 60)
        cases.append(('random, near zero', -x if next(words) & 1 else x))
    return cases


def precise_cases():
    words = splitmix64(0x73696E636F737031)
    unit = lambda: (next(words) >> 11) * 2.0 ** -53  # noqa: E731
    xs = [(unit() * 2.0 - 1.0) * 3.2 for _ in range(500)]
    for _ in range(400):
        b = to_bits(2.0 ** -24) + next(words) % (to_bits(2.0 ** 1023) - to_bits(2.0 ** -24))
        xs.append(-from_bits(b) if next(words) & 1 else from_bits(b))
    for _ in range(300):
        xs.append((1.0 + unit()) * 2.0 ** (-24 + next(words) % 20))
    out = []
    for x in xs:
        entry = {'x': f'{to_bits(x):016x}'}
        for name, f in (('sin', iv.sin), ('cos', iv.cos)):
            negative, m, e = precise(f, x, bits=256)
            entry.update({f'{name}_negative': negative, f'{name}_m': f'{m:064x}', f'{name}_e': e})
        out.append(entry)
    return out


def reduction_cases():
    """x = k pi/2 + r with |r| <= pi/4: k mod 4 and r to 256 bits, for x across
    the range, including the argument closest to a multiple of pi/2
    (generators/trig_reduction.py)."""
    words = splitmix64(0x7265647563653031)
    xs = [6381956970095103 * 2.0 ** 797, 0.7853981633974483, 0.7853981633974484,
          1.5707963267948966, 3.141592653589793, 1e22, from_bits(0x7FEFFFFFFFFFFFFF)]
    for _ in range(600):
        b = to_bits(0.79) + next(words) % (0x7FEFFFFFFFFFFFFF - to_bits(0.79))
        xs.append(from_bits(b))
    out = []
    with mpmath.workprec(2400):
        half_pi = mpmath.pi / 2
        for x in xs:
            y = mpmath.mpf(x) / half_pi
            k = int(mpmath.nint(y))
            r = (y - k) * half_pi
            negative = r < 0
            m, e = mpmath.frexp(abs(r))
            mant = int(mpmath.nint(m * mpmath.mpf(2) ** 256))
            exp = int(e) - 256
            if mant >> 256:
                mant, exp = mant >> 1, exp + 1
            out.append({'x': f'{to_bits(x):016x}', 'k': k % 4, 'negative': bool(negative),
                        'm': f'{mant:064x}', 'e': exp})
    return out


def document():
    found = thresholds()
    cases = special_cases()
    cases += [('worst case, sin', check_worst_case(mpmath.sin, *e, 'Table 8')) for e in TABLE_8]
    cases += [('worst case, cos', check_worst_case(mpmath.cos, *e, 'Table 10')) for e in TABLE_10]
    cases += [(f'threshold: {name}', x) for name, x in found.items()]
    cases += random_cases()
    return {
        'generator': 'generators/sin_cos_reference.py',
        'oracle': f'mpmath {mpmath.__version__} interval arithmetic, from 128 bits, '
                  'doubled until both ends of the enclosure round alike at two precisions',
        'rounding': 'to nearest, ties to even',
        'sources': [
            'Lefevre and Muller, Worst cases for correct rounding of the elementary '
            'functions in double precision, revised 2003, Tables 2, 8 and 10',
            'Steele, Lea and Flood, OOPSLA 2014, Figure 16 (the random inputs)',
        ],
        'thresholds': {name: f'{to_bits(x):016x}' for name, x in found.items()},
        'precise': precise_cases(),
        'reduction': reduction_cases(),
        'cases': [
            {'kind': kind, 'x': f'{to_bits(x):016x}',
             'sin': f'{to_bits(sin_rn(x)):016x}', 'cos': f'{to_bits(cos_rn(x)):016x}'}
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
