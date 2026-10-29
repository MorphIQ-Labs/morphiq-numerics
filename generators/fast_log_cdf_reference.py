#!/usr/bin/env python3
"""Independent log-CDF high/low observations at 600 and 1000 bits.

Inputs cover the bounded log-CDF's accelerated domain, `-22.5 <= x <= -2^-33`
and `2^-33 <= x <= 8`: the strong normal fixture's arguments there, both
neighbors of every dispatch boundary, every binade boundary inside the domain,
uniform sweeps of each branch, and a dense band near the positive side's
complement cancellation. These are observations, not a global proof.
"""
import json
import math
import struct
import sys
from pathlib import Path

import mpmath as mp
from fast_reference import number, rounded, word

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / 'crates/reference/fixtures/fast_log_cdf.json'
MIN_MAGNITUDE = 2.0**-33
NEG_LIMIT = 22.5
POS_LIMIT = 8.0


def accelerated(x):
    return (-NEG_LIMIT <= x <= -MIN_MAGNITUDE) or (MIN_MAGNITUDE <= x <= POS_LIMIT)


def bits(x):
    return struct.unpack('>Q', struct.pack('>d', x))[0]


def neighbors(x):
    b = bits(x)
    return [struct.unpack('>d', struct.pack('>Q', w))[0] for w in (b - 1, b, b + 1)]


def inputs():
    values = set()
    fixture = json.loads((OUTPUT.parent / 'normal.json').read_text())
    for row in fixture['cases']:
        values.add(number(row['x']))
    for boundary in [-NEG_LIMIT, -8.0, -1.0, -0.5, -MIN_MAGNITUDE, MIN_MAGNITUDE,
                     0.5, 1.0, POS_LIMIT]:
        values.update(neighbors(boundary))
    for exponent in range(-33, 5):
        for sign in (-1.0, 1.0):
            values.update(neighbors(sign * 2.0**exponent))
    # Uniform sweeps of both branches, shifted off the dyadic grid.
    for i in range(6001):
        values.add(-NEG_LIMIT + (NEG_LIMIT - MIN_MAGNITUDE) * (i + 0.37) / 6001.5)
    for i in range(4001):
        values.add(MIN_MAGNITUDE + (POS_LIMIT - MIN_MAGNITUDE) * (i + 0.61) / 4001.5)
    # Positive arguments near the dispatch screens and where the lower tail
    # approaches 1/2, exercising the rounded complement.
    for i in range(1, 2001):
        values.add(MIN_MAGNITUDE * (1 + i / 1000.0))
        values.add(POS_LIMIT * (1 - i / 400000.0))
    return sorted(x for x in values if accelerated(x) and math.isfinite(x))


def log_cdf(x, precision):
    with mp.workprec(precision):
        a = mp.mpf(x)
        return mp.log(mp.erfc(-a / mp.sqrt(2)) / 2)


def generate():
    cases = []
    for x in inputs():
        first = log_cdf(x, 600)
        second = log_cdf(x, 1000)
        with mp.workprec(1000):
            high = rounded(second)
            low = rounded(second - mp.mpf(high))
            center = mp.mpf(high) + mp.mpf(low)
            uncertainty = abs(mp.mpf(high)) * mp.mpf(2)**-104 + mp.mpf(2)**-1074
            assert abs(first - center) <= uncertainty
            assert abs(second - center) <= uncertainty
        cases.append(dict(x=word(x), high=word(high), low=word(low)))
    return json.dumps(dict(provenance=dict(
        generator='generators/fast_log_cdf_reference.py',
        oracle='mpmath, pinned by generators/requirements.txt',
        definition='ln(erfc(-x/sqrt(2))/2)',
        precision_bits=[600, 1000],
        uncertainty='abs(high)*2^-104 + 2^-1074; both observations enclosed'),
        cases=cases), indent=2) + '\n'


if __name__ == '__main__':
    text = generate()
    if '--check' in sys.argv:
        if OUTPUT.read_text() != text:
            raise SystemExit('fast log-CDF oracle fixture differs')
    else:
        OUTPUT.write_text(text)
