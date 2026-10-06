#!/usr/bin/env python3
"""Correctly rounded log2(x) and log10(x) for binary64 x: the reference values
log2 and log10 are tested against.

Each value is rounded to nearest, ties to even, into binary64, by the interval
oracle in generators/oracle.

Writes crates/reference/fixtures/log2_log10.json; with --check, fails if the
committed fixture differs from a fresh generation. Needs mpmath
(generators/requirements.txt).

The cases:
- log2: V. Lefevre, J.-M. Muller, "Worst cases for correct rounding of the
  elementary functions in double precision", revised version dated August 14,
  2003 (https://perso.ens-lyon.fr/jean-michel.muller/TMDworstcases.pdf, SHA-256
  718e25ca37ab8d826586fb15dd127c578fcae9ec60c4d5caee82120698d99c4f), Table 7,
  checked against the bits the table states, and the same mantissa at other
  exponents, which section 5.2 shows are worst cases too.
- log10: no published worst cases; random inputs, and the exact powers of ten.
- Special values: NaN for negative arguments, -inf at +-0, +0 at 1, exact
  results at powers of two (log2) and of ten (log10).
- Inputs from a SplitMix64 stream (Steele, Lea and Flood, OOPSLA 2014): every
  positive binade including the subnormals, near 1, and in [0.5, 2].

The "precise" section records, for 1,200 SplitMix64 inputs to each function,
the value to 192 bits (oracle.precise).
"""
import json
import math
import pathlib
import sys

import mpmath
from mpmath import iv

from oracle import (check_worst_case, correctly_rounded, from_binary, from_bits,
                    precise, splitmix64, to_bits)

OUTPUT = pathlib.Path(__file__).resolve().parents[1] / 'crates/reference/fixtures/log2_log10.json'


def log_rn(base):
    def f(x):
        if math.isnan(x) or x < 0:
            return math.nan
        if x == 0:
            return -math.inf
        if x == math.inf:
            return math.inf
        if x == 1:
            return 0.0
        return correctly_rounded(lambda v: iv.log(v) / iv.log(base), x)
    return f


log2_rn, log10_rn = log_rn(2), log_rn(10)

# Lefevre & Muller, Table 7: (sign, input digits, input exponent, the digits of
# log2(x) as printed, then the bits after the first 53 significant ones).
TABLE_7_MANTISSA = '1.0110000101010101010111110111010110001000010110110100'
TABLE_7 = [
    (1, TABLE_7_MANTISSA, -513,
     '-1000000000.1000100011111101001011111100001011001000110', '0' + '0' * 55 + '1100'),
    (1, TABLE_7_MANTISSA, 512,
     '1000000000.0111011100000010110100000011110100110111001', '1' + '1' * 55 + '0011'),
]


def specials(powers):
    return [('special', x) for x in (
        math.nan, -1.0, -math.inf, -0.0, 0.0, 1.0, math.inf, from_bits(1), 2.0 ** -1022,
        from_bits(0x7FEFFFFFFFFFFFFF), from_bits(to_bits(1.0) + 1), from_bits(to_bits(1.0) - 1),
    )] + [('exact power', p) for p in powers]


def random_cases(seed):
    words = splitmix64(seed)
    unit = lambda: (next(words) >> 11) * 2.0 ** -53  # noqa: E731
    cases = []
    for _ in range(2000):
        cases.append(('random, every binade', from_bits(1 + next(words) % (0x7FF0000000000000 - 1))))
    for _ in range(1000):
        k = 1 + next(words) % 52
        u = 1.0 + unit()
        cases.append(('random, near 1', 1.0 + u * 2.0 ** -k if next(words) & 1 else 1.0 - u * 2.0 ** -(k + 1)))
    for _ in range(1000):
        cases.append(('random, [0.5, 2]', 0.5 + unit() * 1.5))
    return [(kind, x) for kind, x in cases if x != 1.0]


def log2_cases():
    cases = specials([2.0 ** k for k in (-1074, -1073, -1023, -1022, -1, 1, 2, 52, 1023)])
    for entry in TABLE_7:
        cases.append(('worst case', check_worst_case(lambda v: mpmath.log(v, 2), *entry, 'Table 7')))
    # Section 5.2: the same mantissa at exponents 513..1023 and -1024..-514.
    for e in (513, 700, 1023, -514, -700, -900):
        cases.append(('worst case, same mantissa', from_binary(1, TABLE_7_MANTISSA, e)))
    return cases + random_cases(0x6C6F67325F726566)


def log10_cases():
    # 10^k is exact in binary64 for 0 <= k <= 22.
    return specials([10.0 ** k for k in range(1, 23)]) + random_cases(0x6C6F6731305F7266)


def precise_cases(base, seed):
    words = splitmix64(seed)
    unit = lambda: (next(words) >> 11) * 2.0 ** -53  # noqa: E731
    xs = [from_bits(1 + next(words) % (0x7FF0000000000000 - 1)) for _ in range(500)]
    for _ in range(400):
        k = 1 + next(words) % 52
        u = 1.0 + unit()
        xs.append(1.0 + u * 2.0 ** -k if next(words) & 1 else 1.0 - u * 2.0 ** -(k + 1))
    xs += [0.5 + unit() * 1.5 for _ in range(300)]
    out = []
    for x in xs:
        if x == 1.0:
            continue
        negative, m, e = precise(lambda v: iv.log(v) / iv.log(base), x)
        out.append({'x': f'{to_bits(x):016x}', 'negative': negative, 'm': f'{m:048x}', 'e': e})
    return out


def document():
    return {
        'generator': 'generators/log2_log10_reference.py',
        'oracle': f'mpmath {mpmath.__version__} interval arithmetic, from 128 bits, '
                  'doubled until both ends of the enclosure round alike',
        'rounding': 'to nearest, ties to even',
        'sources': [
            'Lefevre and Muller, Worst cases for correct rounding of the elementary '
            'functions in double precision, revised 2003, Table 7 and section 5.2 (log2)',
            'IEEE 754-2019, section 9.2 (special values)',
            'Steele, Lea and Flood, OOPSLA 2014, Figure 16 (the random inputs)',
        ],
        'precise': {
            'log2': precise_cases(2, 0x6C6F67325F707231),
            'log10': precise_cases(10, 0x6C6F6731305F7031),
        },
        'log2': [{'kind': k, 'x': f'{to_bits(x):016x}', 'log2': f'{to_bits(log2_rn(x)):016x}'}
                 for k, x in log2_cases()],
        'log10': [{'kind': k, 'x': f'{to_bits(x):016x}', 'log10': f'{to_bits(log10_rn(x)):016x}'}
                  for k, x in log10_cases()],
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
