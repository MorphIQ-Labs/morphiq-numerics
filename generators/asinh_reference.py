#!/usr/bin/env python3
"""Correctly rounded asinh(x) for binary64 x: the reference values asinh is
tested against.

Each value is rounded to nearest, ties to even, into binary64, by the interval
oracle in generators/oracle (mpmath interval arithmetic, precision doubled until
both ends of the enclosure round alike).

Writes crates/reference/fixtures/asinh.json; with --check, fails if the committed
fixture differs from a fresh generation. Needs mpmath (generators/requirements.txt).

The cases:
- Worst cases: the 40 inputs of CORE-MATH's binary64 asinh worst-case list
  (src/binary64/asinh/asinh.wc at commit 0ce0cbc15935e24c656280e5a46c34e89f301b7a,
  SHA-256 c5835d0d56244e3ce1455358225934c9c5360c2abb7de512680bc9d64ea29e30;
  MIT, https://core-math.gitlabpages.inria.fr/worst.html) whose asinh lies closest
  to a rounding boundary. The list holds every input with at least 43 identical
  bits after the round bit on 0x1.7137449123ef6p-26 <= x < 2^1024, found with
  BaCSeL. They were ranked here by the distance of asinh(x) to the nearest
  midpoint, in ulps, at 400 bits. The generator recomputes that distance for
  each one and refuses an input closer than HARDEST_MIN_BITS, so a mistyped
  input fails.
- The least argument whose asinh is not x, found by bisection with the oracle,
  and its neighbours: asinh(x) = x - x^3/6 + ..., so asinh(x) rounds to x for
  every |x| up to that threshold (docs/asinh.md section 1).
- Special values, as IEEE 754-2019 section 9.2 specifies them.
- The structure's boundaries: 2^-7 (the series ends) and 2^28 (the logarithmic
  form begins), the largest finite value, and the subnormals.
- Inputs from a SplitMix64 stream (Steele, Lea and Flood, OOPSLA 2014): every
  binade of [2^-1074, 2^1023], [2^-7, 2^28], and arguments around 1.
"""
import json
import math
import pathlib
import sys

import mpmath
from mpmath import iv

from oracle import bisect, correctly_rounded, from_bits, splitmix64, to_bits

OUTPUT = pathlib.Path(__file__).resolve().parents[1] / 'crates/reference/fixtures/asinh.json'

# The 40 hardest inputs of asinh.wc, hardest first.
HARDEST = [
    '0x1.fd15daa6ce332p+731', '0x1.be87838f1a47cp+773', '0x1.b7f71a488641ap+339',
    '0x1.6b3d29c0f9e6ep+542', '0x1.d6a413a59c7eap+501', '0x1.ad9cb1932cb03p+479',
    '0x1.1f19ae6db054ep+192', '0x1.5996e62e5753fp+185', '0x1.bbdf7dd7ac127p+330',
    '0x1.f2382637c71c2p+459', '0x1.edce031790119p+914', '0x1.d3da559aa99f5p+62',
    '0x1.6ab13075e3f2dp+456', '0x1.31143c7c0b1e6p+961', '0x1.5c2e78e590c40p+822',
    '0x1.dd6cee1a13ad7p+263', '0x1.123add2cfe736p+358', '0x1.6fda0b1009a70p+487',
    '0x1.b4870d2098262p+476', '0x1.d4a93d69f93ebp+462', '0x1.58bba4db12da9p+150',
    '0x1.c561b55246db6p+717', '0x1.fd2634ca3c97cp+1', '0x1.382c35530591fp+520',
    '0x1.1d676463a3fcep+584', '0x1.618a1864daf76p+643', '0x1.b67b4f02f33d6p+648',
    '0x1.fcdb4d6db2715p+1012', '0x1.04517520386e5p+136', '0x1.8171a16d5fda7p+227',
    '0x1.5b46700fda328p+677', '0x1.12e24c5146e47p+171', '0x1.777a4f7107178p+527',
    '0x1.b5b78085c0f06p+541', '0x1.e65df55368954p+861', '0x1.50d57691544d7p+243',
    '0x1.19aa3b9c3a117p+423', '0x1.0c2b0c8ad63d5p+632', '0x1.b9bd2112d4ffbp+22',
    '0x1.44a2f58075274p+349',
]
# Every listed input is at least this many bits (in ulps of asinh(x)) from a
# midpoint, as measured at 400 bits by midpoint_bits.
HARDEST_MIN_BITS = 57.0


def asinh_interval(v):
    """An enclosure of asinh(v) for an interval v: for v >= 0,
    log1p(v + v^2 / (1 + sqrt(1 + v^2))), every term positive, so nothing
    cancels; asinh is odd."""
    if v.a < 0:
        return -asinh_interval(-v)
    return iv.log1p(v + v * v / (1 + iv.sqrt(1 + v * v)))


def asinh_rn(x):
    """asinh(x) correctly rounded to binary64."""
    if math.isnan(x) or math.isinf(x) or x == 0:
        return x  # NaN, +-infinity and the signed zeros are their own images
    return correctly_rounded(asinh_interval, x)


def midpoint_bits(x):
    """-log2 of the distance from asinh(x) to the nearest rounding midpoint, in
    units of the ulp of asinh(x)."""
    with mpmath.workprec(400):
        y = mpmath.asinh(mpmath.mpf(x))
        e = int(mpmath.floor(mpmath.log(abs(y), 2)))
        scaled = abs(y) / mpmath.mpf(2) ** (max(e, -1022) - 52)
        distance = abs(scaled - mpmath.floor(scaled) - mpmath.mpf(1) / 2)
        return float(-mpmath.log(distance, 2))


def worst_cases():
    cases = []
    for text in HARDEST:
        x = float.fromhex(text)
        bits = midpoint_bits(x)
        if bits < HARDEST_MIN_BITS:
            sys.exit(f'asinh({text}) is only {bits:.2f} bits from a midpoint')
        cases.append(('worst case', x))
    return cases


def threshold_cases():
    """The first x for which asinh(x) does not round to x, and its neighbours."""
    lo, hi = to_bits(2.0 ** -27), to_bits(2.0 ** -25)
    first = bisect(lo, hi, lambda b: asinh_rn(from_bits(b)) != from_bits(b))
    cases = []
    for b in range(first - 4, first + 4):
        cases += [('threshold', from_bits(b)), ('threshold', -from_bits(b))]
    return first, cases


def special_cases():
    return [('special', x) for x in (
        math.nan, math.inf, -math.inf, 0.0, -0.0, 1.0, -1.0, 0.5, -0.5, 2.0, -2.0,
        from_bits(1), -from_bits(1), from_bits(0x000FFFFFFFFFFFFF), 2.0 ** -1022,
        from_bits(0x7FEFFFFFFFFFFFFF), -from_bits(0x7FEFFFFFFFFFFFFF),
        from_bits(0x7FF8000000000001),
    )]


def structure_cases():
    cases = []
    for text in ('0x1p-7', '0x1p28'):
        x = float.fromhex(text)
        for step in range(-4, 5):
            cases.append(('boundary, ' + text, from_bits(to_bits(x) + step)))
    for n in range(-26, 30):
        cases.append(('powers of two', 2.0 ** n))
    for text in ('0x1.fffffffffffffp-8', '0x1.fffffffffffffp+27', '0x1p+511',
                 '0x1p+512', '0x1.fffffffffffffp+1023'):
        cases.append(('corner', float.fromhex(text)))
    return cases


def random_cases():
    words = splitmix64(0x6173696E685F7265)
    unit = lambda: (next(words) >> 11) * 2.0 ** -53  # noqa: E731
    cases = []
    for _ in range(2500):
        # Every positive finite encoding, subnormals included.
        b = 1 + next(words) % (to_bits(math.inf) - 1)
        x = from_bits(b)
        cases.append(('random, every binade', -x if next(words) & 1 else x))
    for _ in range(1500):
        e = -7.0 + 35.0 * unit()
        cases.append(('random, [2^-7, 2^28]', 2.0 ** e))
    for _ in range(800):
        cases.append(('random, around 1', 0.25 + 3.75 * unit()))
    for _ in range(800):
        x = from_bits(to_bits(1.0) + next(words) % (to_bits(2.0 ** 40) - to_bits(1.0)))
        cases.append(('random, [1, 2^40]', -x if next(words) & 1 else x))
    return cases


def document():
    first, thresholds = threshold_cases()
    cases = (special_cases() + worst_cases() + thresholds + structure_cases()
             + random_cases())
    return {
        'generator': 'generators/asinh_reference.py',
        'oracle': f'mpmath {mpmath.__version__} interval arithmetic, from 128 bits, '
                  'doubled until both ends of the enclosure round alike',
        'rounding': 'to nearest, ties to even; subnormals rounded once',
        'sources': [
            'CORE-MATH, src/binary64/asinh/asinh.wc at commit '
            '0ce0cbc15935e24c656280e5a46c34e89f301b7a, SHA-256 '
            'c5835d0d56244e3ce1455358225934c9c5360c2abb7de512680bc9d64ea29e30 '
            '(worst cases computed with BaCSeL)',
            'IEEE 754-2019, section 9.2 (special values)',
            'Steele, Lea and Flood, OOPSLA 2014, Figure 16 (the random inputs)',
        ],
        'threshold': f'{first:016x}',
        'asinh': [
            {'kind': kind, 'x': f'{to_bits(x):016x}', 'asinh': f'{to_bits(asinh_rn(x)):016x}'}
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
