#!/usr/bin/env python3
"""Correctly rounded asin(x) for binary64 x: the reference values asin is
tested against.

Each value is rounded to nearest, ties to even, into binary64, by the interval
oracle in generators/oracle (mpmath interval arithmetic, precision doubled until
both ends of the enclosure round alike).

Writes crates/reference/fixtures/asin.json; with --check, fails if the committed
fixture differs from a fresh generation. Needs mpmath (generators/requirements.txt).

The cases:
- Worst cases: the 40 inputs of CORE-MATH's binary64 asin worst-case list
  (src/binary64/asin/asin.wc at commit 0ce0cbc15935e24c656280e5a46c34e89f301b7a,
  SHA-256 c7869311e52f598490c4d67f57f1fd6b25737da7672cd3b266704426a9970830;
  MIT, https://core-math.gitlabpages.inria.fr/worst.html) whose asin lies closest
  to a rounding boundary. The list holds every input with at least 43 identical
  bits after the round bit on 2^-26 <= x <= 1, found with BaCSeL. They were
  ranked here by the distance of asin(x) to the nearest midpoint, in ulps, at
  400 bits. The generator recomputes that distance for each one and refuses an
  input closer than HARDEST_MIN_BITS, so a mistyped input fails.
- The least argument whose asin is not x, found by bisection with the oracle,
  and its neighbours: asin(x) = x + x^3/6 + ..., so asin(x) rounds to x for
  every |x| up to that threshold (docs/asin.md section 2).
- Special values, as IEEE 754-2019 section 9.2 specifies them.
- The structure's boundaries: the multiples of 1/64, the crossover sqrt(1/2)
  and the arguments next to 1, where asin(x) = pi/2 - delta.
- Inputs from a SplitMix64 stream (Steele, Lea and Flood, OOPSLA 2014): every
  binade of [2^-1074, 1], [1/2, 1], near 1 and across (-1, 1).
"""
import json
import math
import pathlib
import sys

import mpmath
from mpmath import iv

from oracle import bisect, correctly_rounded, from_bits, splitmix64, to_bits

OUTPUT = pathlib.Path(__file__).resolve().parents[1] / 'crates/reference/fixtures/asin.json'

# The 40 hardest inputs of asin.wc, hardest first.
HARDEST = [
    '0x1.c373ff4aad79bp-14', '0x1.a4816b2066707p-5', '0x1.7137449123ef6p-26',
    '0x1.522bffce02485p-19', '0x1.51c4b960778f5p-23', '0x1.5363d5cd68131p-13',
    '0x1.f317ce4e1019dp-7', '0x1.2231aea708e6ep-14', '0x1.ab4d373bb9c21p-19',
    '0x1.860db11c8df3bp-16', '0x1.3217783d70d1dp-14', '0x1.ddf6e4e4450aep-14',
    '0x1.a0b1709cc13cbp-24', '0x1.9a15c667f5cb6p-17', '0x1.9d34dd7faad08p-5',
    '0x1.9697cb602c582p-3', '0x1.af2a09dd5382fp-11', '0x1.3520ce764eea1p-21',
    '0x1.4f747439b3489p-25', '0x1.ff0f3022b2e9dp-16', '0x1.74da6951cbf1bp-19',
    '0x1.f04242b4136e5p-11', '0x1.ac6fe500ab565p-24', '0x1.ba7275b7bfb15p-13',
    '0x1.e06d213552689p-23', '0x1.d5b05a89d3e77p-1', '0x1.8aec56b25bdf1p-7',
    '0x1.57c61ad53bc2cp-7', '0x1.1a37d0cacaa17p-19', '0x1.1ed06d50f7e88p-1',
    '0x1.71b8724f3322ap-9', '0x1.6533f127faaa4p-7', '0x1.50b3edb7a082ap-13',
    '0x1.7477d528ac2b5p-10', '0x1.63ae6fe9336dfp-2', '0x1.d7c6f0e805b3cp-4',
    '0x1.5d6cbb2ec90cap-22', '0x1.5f07120fe568ap-23', '0x1.d5fa99d152081p-24',
    '0x1.a687c9297897fp-10',
]
# Every listed input is at least this many bits (in ulps of asin(x)) from a
# midpoint, as measured at 400 bits by midpoint_bits.
HARDEST_MIN_BITS = 52.0

SEGMENTS = 64  # multiples of 1/SEGMENTS are structure boundaries.


def asin_interval(v):
    """An enclosure of asin(v) for an interval v within [-1, 1]: mpmath's
    interval context has no asin, and atan2(v, sqrt(1 - v^2)) is asin(v) there.
    For a binary64 v, 1 - v^2 is formed from an exact square."""
    return iv.atan2(v, iv.sqrt(1 - v * v))


def asin_rn(x):
    """asin(x) correctly rounded to binary64."""
    if math.isnan(x) or abs(x) > 1:
        return math.nan
    if x == 0:
        return x  # keeps the sign of zero
    return correctly_rounded(asin_interval, x)


def midpoint_bits(x):
    """-log2 of the distance from asin(x) to the nearest rounding midpoint, in
    units of the ulp of asin(x)."""
    with mpmath.workprec(400):
        y = mpmath.asin(mpmath.mpf(x))
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
            sys.exit(f'asin({text}) is only {bits:.2f} bits from a midpoint')
        cases.append(('worst case', x))
    return cases


def threshold_cases():
    """The first x for which asin(x) does not round to x, and its neighbours."""
    lo, hi = to_bits(2.0 ** -27), to_bits(2.0 ** -25)
    first = bisect(lo, hi, lambda b: asin_rn(from_bits(b)) != from_bits(b))
    cases = []
    for b in range(first - 4, first + 4):
        cases += [('threshold', from_bits(b)), ('threshold', -from_bits(b))]
    return first, cases


def special_cases():
    one_up = from_bits(to_bits(1.0) + 1)
    one_down = from_bits(to_bits(1.0) - 1)
    return [('special', x) for x in (
        math.nan, math.inf, -math.inf, 0.0, -0.0, 1.0, -1.0, one_up, -one_up,
        2.0, -2.0, one_down, -one_down, 0.5, -0.5, from_bits(1), -from_bits(1),
        from_bits(0x000FFFFFFFFFFFFF), 2.0 ** -1022, from_bits(0x7FEFFFFFFFFFFFFF),
        from_bits(0x7FF8000000000001),
    )]


def structure_cases():
    cases = []
    for k in range(1, SEGMENTS + 1):
        a = k / SEGMENTS
        for step in (-2, -1, 0, 1, 2):
            x = from_bits(to_bits(a) + step)
            if x <= 1.0:
                cases.append(('boundary, multiples of 1/64', x))
    root = math.sqrt(0.5)
    for step in range(-6, 7):
        cases.append(('crossover sqrt(1/2)', from_bits(to_bits(root) + step)))
    for k in range(1, 9):
        cases.append(('next to 1', 1.0 - k * 2.0 ** -53))
    for n in range(2, 53):
        cases.append(('next to 1', 1.0 - 2.0 ** -n))
    for text in ('0x1.fffffffffffffp-7', '0x1p-6', '0x1.ffffffffffffep-1023'):
        cases.append(('corner', float.fromhex(text)))
    return cases


def random_cases():
    words = splitmix64(0x6173696E5F726566)
    unit = lambda: (next(words) >> 11) * 2.0 ** -53  # noqa: E731
    cases = []
    for _ in range(2000):
        # Every positive finite encoding up to 1, subnormals included.
        b = 1 + next(words) % (to_bits(1.0) - 1)
        x = from_bits(b)
        cases.append(('random, every binade', -x if next(words) & 1 else x))
    for _ in range(1500):
        cases.append(('random, [1/2, 1]', 0.5 + unit() * 0.5))
    for _ in range(1000):
        k = 1 + next(words) % 52
        cases.append(('random, near 1', 1.0 - (1.0 + unit()) * 2.0 ** -(k + 1)))
    for _ in range(1000):
        x = unit() * 2.0 - 1.0
        cases.append(('random, (-1, 1)', x))
    return cases


def document():
    first, thresholds = threshold_cases()
    cases = (special_cases() + worst_cases() + thresholds + structure_cases()
             + random_cases())
    return {
        'generator': 'generators/asin_reference.py',
        'oracle': f'mpmath {mpmath.__version__} interval arithmetic, from 128 bits, '
                  'doubled until both ends of the enclosure round alike',
        'rounding': 'to nearest, ties to even; subnormals rounded once',
        'sources': [
            'CORE-MATH, src/binary64/asin/asin.wc at commit '
            '0ce0cbc15935e24c656280e5a46c34e89f301b7a, SHA-256 '
            'c7869311e52f598490c4d67f57f1fd6b25737da7672cd3b266704426a9970830 '
            '(worst cases computed with BaCSeL)',
            'IEEE 754-2019, section 9.2 (special values)',
            'Steele, Lea and Flood, OOPSLA 2014, Figure 16 (the random inputs)',
        ],
        'threshold': f'{first:016x}',
        'asin': [
            {'kind': kind, 'x': f'{to_bits(x):016x}', 'asin': f'{to_bits(asin_rn(x)):016x}'}
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
