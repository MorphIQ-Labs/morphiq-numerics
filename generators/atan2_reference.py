#!/usr/bin/env python3
"""Correctly rounded atan2(y, x) for binary64 y and x: the reference values atan2
is tested against.

Each value is rounded to nearest, ties to even, into binary64, by the interval
oracle in generators/oracle (mpmath interval arithmetic, precision doubled until
both ends of the enclosure round alike); the special values are IEEE 754-2019
section 9.2's.

Writes crates/reference/fixtures/atan2.json; with --check, fails if the committed
fixture differs from a fresh generation. Needs mpmath (generators/requirements.txt).

The cases:
- Worst cases: the 40 pairs of CORE-MATH's binary64 atan2 worst-case list
  (src/binary64/atan2/atan2.wc at commit 0ce0cbc15935e24c656280e5a46c34e89f301b7a,
  SHA-256 9e4fb81a3c4a789ea739203d2db3ef9689c48208d94196726fa7a22886e573db;
  MIT, https://core-math.gitlabpages.inria.fr/worst.html) whose atan2 lies closest
  to a rounding boundary, ranked here by the distance of the value to the nearest
  midpoint, in ulps, at 500 bits. The list is a restricted set, not an
  exhaustive search. The generator recomputes the distance for each pair and
  refuses one closer than HARDEST_MIN_BITS, so a mistyped pair fails.
- Special values: every pair of {NaN, +-inf, +-0, +-1, +-2^-1074, +-2^-1022, +-max}.
- The two subnormal results whose ratio is exactly a midpoint (atan2 lies just
  below it and rounds down), and their neighbours.
- The structure's boundaries: ratios at k/64 and k/64 +- 1/128, both quadrant
  forms, equal magnitudes, the ratio 2^-900 and either side.
- Inputs from a SplitMix64 stream (Steele, Lea and Flood, OOPSLA 2014): random
  encodings, ratios in [0, 1] with either argument larger, and every binade
  of the ratio.
"""
import json
import math
import pathlib
import sys

import mpmath
from mpmath import iv

from oracle import correctly_rounded, from_bits, splitmix64, to_bits

OUTPUT = pathlib.Path(__file__).resolve().parents[1] / 'crates/reference/fixtures/atan2.json'

# The 40 hardest pairs (y, x) of atan2.wc, hardest first.
HARDEST = [
    ('0x1.07a11ffd843abp+53', '0x1.f9982dddc9cccp+52'), ('0x1.fdfe11f61919cp+74', '0x1.53feb7b3de47bp+52'),
    ('0x1.2981ce8381491p+52', '0x1.4efd17defb8d1p+52'), ('0x1.2d3d9a4b9aefap+70', '0x1.4534432011dc4p+51'),
    ('0x1.8c48c7e9f59bbp+69', '0x1.4c7775f720a8dp+53'), ('0x1.ea018dddc111dp+71', '0x1.88f9e3de5d6d3p+53'),
    ('0x1.5047c4426721bp+76', '0x1.9ada1a85962dfp+52'), ('0x1.bdcba7c10415cp+74', '0x1.e58dc28ff472fp+52'),
    ('0x1.af7e4cc85653dp+76', '0x1.c4c43bce2aaddp+52'), ('0x1.4db20cd28f530p+89', '0x1.8e3198375aaf2p+51'),
    ('0x1.4e015ccaa709ap+52', '0x1.cafc4eba977aep+51'), ('0x1.c645cf90f1da1p+83', '0x1.2fad1fea7a20ap+53'),
    ('0x1.67bb337d216b9p+53', '0x1.f8d20e4ccf641p+52'), ('0x1.0125b1aa363f3p+53', '0x1.793c81fd18e3ep+52'),
    ('0x1.c6fb9d76e4879p+52', '0x1.568092de15e5fp+53'), ('0x1.eff44ffd58ef0p+83', '0x1.5c87c26616817p+52'),
    ('0x1.1cab9c60bb450p+62', '0x1.8a15d739ee3f1p+52'), ('0x1.dfdc3b7e8d260p+52', '0x1.39c512a930c49p+52'),
    ('0x1.dd08accb68fa2p+52', '0x1.9e58d74a159ddp+52'), ('0x1.bf95cd7449337p+52', '0x1.68b85fd1960e4p+53'),
    ('0x1.4d0cbd0fc026dp+83', '0x1.bf556f65c206bp+52'), ('0x1.ff3025e90bdf4p+55', '0x1.ede6c97e6b6bbp+52'),
    ('0x1.5d386ce72e2b2p+57', '0x1.61b7ea6316bb3p+52'), ('0x1.081ee70e83ab7p+52', '0x1.ae391ac23e68fp+52'),
    ('0x1.1ed63d9eaf352p+52', '0x1.a78d666afbc35p+52'), ('0x1.4bc7c0ea37ab2p+81', '0x1.89c54ab70daeap+51'),
    ('0x1.b0136f66a0919p+70', '0x1.1a622e69b98e4p+53'), ('0x1.96509cf22d1fep+61', '0x1.1723a8e862b98p+52'),
    ('0x1.dda6246006ef6p+66', '0x1.dda6fa0689316p+51'), ('0x1.d0b8be2bed534p+51', '0x1.94458d52d490cp+51'),
    ('0x1.4c3e0af3b201dp+52', '0x1.c62f4752b3b02p+52'), ('0x1.79b3686229452p+79', '0x1.47362dee55845p+52'),
    ('0x1.91b3450be8479p+80', '0x1.1627e8decc23fp+53'), ('0x1.aff2d5523eb2fp+78', '0x1.1c1e5c18b0728p+53'),
    ('0x1.20b41d3401e41p+70', '0x1.87a8b786075c6p+52'), ('0x1.0a54b78afd46cp+77', '0x1.b0dbaae9ff820p+50'),
    ('0x1.13604a0d35b52p+82', '0x1.8f984ef696cdcp+51'), ('0x1.c2b118f5c6805p+82', '0x1.643755b190f9dp+53'),
    ('0x1.a92c2c9490577p+57', '0x1.41095ae4a8760p+53'), ('0x1.fc2661c3b85f2p+51', '0x1.8b49541b85592p+52'),
]
# Every listed pair is at least this many bits (in ulps of atan2) from a midpoint.
HARDEST_MIN_BITS = 85.0


def atan2_rn(y, x):
    """atan2(y, x) correctly rounded to binary64, IEEE 754-2019 section 9.2."""
    if math.isnan(y) or math.isnan(x):
        return math.nan
    negative_x = math.copysign(1.0, x) < 0
    if y == 0:
        return math.copysign(math.pi if negative_x else 0.0, y) if negative_x else y
    if x == 0:
        return math.copysign(math.pi / 2, y)
    if math.isinf(y):
        if math.isinf(x):
            return math.copysign(float.fromhex('0x1.2d97c7f3321d2p+1') if negative_x else math.pi / 4, y)
        return math.copysign(math.pi / 2, y)
    if math.isinf(x):
        return math.copysign(math.pi if negative_x else 0.0, y)
    value = correctly_rounded(lambda xv: iv.atan2(iv.mpf(y), xv), x)
    return value


def midpoint_bits(y, x):
    with mpmath.workprec(500):
        v = mpmath.atan2(mpmath.mpf(y), mpmath.mpf(x))
        e = int(mpmath.floor(mpmath.log(abs(v), 2)))
        scaled = abs(v) / mpmath.mpf(2) ** (max(e, -1022) - 52)
        distance = abs(scaled - mpmath.floor(scaled) - mpmath.mpf(1) / 2)
        return float(-mpmath.log(distance, 2))


def worst_cases():
    cases = []
    for ty, tx in HARDEST:
        y, x = float.fromhex(ty), float.fromhex(tx)
        bits = midpoint_bits(y, x)
        if bits < HARDEST_MIN_BITS:
            sys.exit(f'atan2({ty}, {tx}) is only {bits:.2f} bits from a midpoint')
        cases.append(('worst case', y, x))
    return cases


def special_cases():
    values = [math.nan, math.inf, -math.inf, 0.0, -0.0, 1.0, -1.0, from_bits(1), -from_bits(1),
              2.0 ** -1022, -2.0 ** -1022, from_bits(0x7FEFFFFFFFFFFFFF), -from_bits(0x7FEFFFFFFFFFFFFF),
              from_bits(0x7FF8000000000001)]
    return [('special', y, x) for y in values for x in values]


def tie_cases():
    """y/x exactly a midpoint of two subnormals: y = (2j + 1) 2^-1074, x = 2."""
    cases = []
    for j in (0, 1, 2, 3, 5, 100, 2 ** 51, 2 ** 52 - 1):
        y = from_bits(2 * j + 1)
        for sx in (1.0, -1.0):
            cases += [('subnormal midpoint', y, 2.0 * sx), ('subnormal midpoint', -y, 2.0 * sx)]
    # Neighbours: the ratio just above and below the midpoint.
    for j in (1, 2, 7):
        y = from_bits(2 * j + 1)
        for dx in (-1, 1):
            cases.append(('subnormal midpoint, neighbour', y, from_bits(to_bits(2.0) + dx)))
    return cases


def structure_cases():
    cases = []
    for k in range(0, 65):
        for edge in (k / 64, k / 64 - 1 / 128, k / 64 + 1 / 128):
            if 0 < edge <= 1.0:
                for step in (-1, 0, 1):
                    t = from_bits(to_bits(edge) + step)
                    if 0 < t <= 1.0:
                        for sy, sx in ((1, 1), (1, -1), (-1, 1), (-1, -1)):
                            cases.append(('ratio boundary', sy * t, sx * 1.0))
                            cases.append(('ratio boundary, swapped', sy * 1.0, sx * t))
    for sy, sx in ((1, 1), (1, -1), (-1, 1), (-1, -1)):
        cases.append(('equal magnitudes', sy * 3.0, sx * 3.0))
        cases.append(('equal magnitudes', sy * 2.0 ** -1074, sx * 2.0 ** -1074))
    for step in range(-3, 4):
        t = from_bits(to_bits(2.0 ** -900) + step)
        cases += [('ratio 2^-900', t, 1.0), ('ratio 2^-900', 1.0, t), ('ratio 2^-900', -t, -1.0), ('ratio 2^-900', 1.0, -t)]
    return cases


def random_cases():
    words = splitmix64(0x6174616E325F7265)
    unit = lambda: (next(words) >> 11) * 2.0 ** -53  # noqa: E731
    cases = []
    for _ in range(2500):
        y = from_bits(next(words))
        x = from_bits(next(words))
        if math.isfinite(y) and math.isfinite(x):
            cases.append(('random encodings', y, x))
    for _ in range(1500):
        t = unit()
        s = 2.0 ** (next(words) % 40 - 20) * (1 + unit())
        sy = -1.0 if next(words) & 1 else 1.0
        sx = -1.0 if next(words) & 1 else 1.0
        if next(words) & 1:
            cases.append(('random ratios', sy * t * s, sx * s))
        else:
            cases.append(('random ratios, swapped', sy * s, sx * t * s))
    for _ in range(1500):
        e = -(next(words) % 1100)
        t = 2.0 ** e * (1 + unit())
        if t * 2 ** 40 < 1e300:
            cases.append(('random binades of the ratio', t, 1.0 + unit()))
    return cases


def document():
    cases = special_cases() + worst_cases() + tie_cases() + structure_cases() + random_cases()
    return {
        'generator': 'generators/atan2_reference.py',
        'oracle': f'mpmath {mpmath.__version__} interval arithmetic, from 128 bits, '
                  'doubled until both ends of the enclosure round alike',
        'rounding': 'to nearest, ties to even; subnormals rounded once',
        'sources': [
            'CORE-MATH, src/binary64/atan2/atan2.wc at commit '
            '0ce0cbc15935e24c656280e5a46c34e89f301b7a, SHA-256 '
            '9e4fb81a3c4a789ea739203d2db3ef9689c48208d94196726fa7a22886e573db '
            '(worst cases)',
            'IEEE 754-2019, section 9.2 (special values)',
            'Steele, Lea and Flood, OOPSLA 2014, Figure 16 (the random inputs)',
        ],
        'atan2': [
            {'kind': kind, 'y': f'{to_bits(y):016x}', 'x': f'{to_bits(x):016x}',
             'atan2': f'{to_bits(atan2_rn(y, x)):016x}'}
            for kind, y, x in cases
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
