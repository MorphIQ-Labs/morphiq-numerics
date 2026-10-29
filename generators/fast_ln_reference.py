#!/usr/bin/env python3
"""Independent ln high/low observations at 600 and 1000 bits.

Reuse the strong ln inputs (including published worst cases), and cover every
reciprocal cell boundary at several exponents, the entire exponent range, and
the immediate neighbors of one. These are observations, not a global proof.
"""
import json
import math
import sys
from pathlib import Path

import mpmath as mp
from fast_reference import number, rounded, word

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / 'crates/reference/fixtures/fast_ln.json'


def inputs():
    fixture = json.loads((OUTPUT.parent / 'ln.json').read_text())
    words = {row['x'] for row in fixture['ln']}
    # The generated reciprocal table's offset and nine-bit index partition.
    offset = 0x3fe6a00000000000
    for exponent in [-1021, -500, -1, 0, 1, 500, 1023]:
        for cell in range(513):
            center = offset + (cell << 43) + (exponent << 52)
            for bits in [center-1, center, center+1]:
                if 0 < bits < 0x7ff0000000000000:
                    words.add(f'{bits:016x}')
    for exponent in range(1, 2047):
        for bits in [(exponent << 52)-1, exponent << 52, (exponent << 52)+1]:
            words.add(f'{bits:016x}')
    for delta in range(-32, 33):
        words.add(f'{0x3ff0000000000000+delta:016x}')
    return sorted(w for w in words if 0 < number(w) < math.inf)


def generate():
    cases = []
    for bits in inputs():
        x = number(bits)
        with mp.workprec(600):
            first = mp.log(mp.mpf(x))
        with mp.workprec(1000):
            second = mp.log(mp.mpf(x))
            high = rounded(second)
            low = rounded(second - mp.mpf(high))
            center = mp.mpf(high) + mp.mpf(low)
            uncertainty = abs(mp.mpf(high))*mp.mpf(2)**-104 + mp.mpf(2)**-1074
            assert abs(first-center) <= uncertainty
            assert abs(second-center) <= uncertainty
        cases.append(dict(x=bits, high=word(high), low=word(low)))
    return json.dumps(dict(provenance=dict(
        generator='generators/fast_ln_reference.py',
        oracle='mpmath, pinned by generators/requirements.txt',
        precision_bits=[600, 1000],
        uncertainty='abs(high)*2^-104 + 2^-1074; both observations enclosed'),
        cases=cases), indent=2) + '\n'


if __name__ == '__main__':
    text = generate()
    if '--check' in sys.argv:
        if OUTPUT.read_text() != text:
            raise SystemExit('fast ln oracle fixture differs')
    else:
        OUTPUT.write_text(text)
