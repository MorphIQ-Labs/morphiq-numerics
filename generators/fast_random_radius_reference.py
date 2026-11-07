#!/usr/bin/env python3
"""Independent interval-oracle radii on reciprocal-cell and uniform boundaries.

Covers every reciprocal boundary/midpoint at exponent -1, representative
cells at every uniform exponent, adjacent odd-grid points, the near-one
branch boundary, extrema, and the retained diagnostic worst-case witnesses.
No library result participates in the expected values.
"""
from fractions import Fraction
from pathlib import Path
import json
import struct
import sys

import mpmath
from mpmath import iv
from oracle import correctly_rounded, to_bits

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / 'crates/reference/fixtures/fast_pair_radius.json'
OFF = 0x3FE6A00000000000


def words():
    result = {0, (1 << 64) - 1, 0x0000001FF0000000,
              0xFA7FFFFFFFFFE000, 0xFF800F45A880A000}

    def around(u, width=1):
        # u = (2*k+1)*2^-53, word = k<<12. Fraction preserves endpoints.
        k = (u * (1 << 53) - 1) // 2
        for adjacent in range(k-width, k+width+1):
            if 0 <= adjacent < 1 << 52:
                result.add(adjacent << 12)

    for exponent in range(-53, 1):
        indices = range(1025) if exponent == -1 else range(0, 1025, 64)
        for index in indices:
            y = struct.unpack('>d', struct.pack('>Q', OFF + (index << 42)))[0]
            around(Fraction.from_float(y) * Fraction(2) ** exponent)
    around(Fraction(511, 512), 32)
    return sorted(result)


def document():
    rows = []
    for word in words():
        u = (2*(word >> 12)+1) * 2.0**-53
        log = correctly_rounded(iv.log, u)
        radius = correctly_rounded(iv.sqrt, -2.0*log)
        rows.append({'word': f'{word:016x}', 'radius': f'{to_bits(radius):016x}'})
    return {'generator': 'generators/fast_random_radius_reference.py',
            'oracle': f'mpmath {mpmath.__version__} interval arithmetic, from 128 bits, '
                      'doubled until both enclosure ends round alike at two precisions',
            'reference': 'RN(sqrt(-2*RN(ln((2*(word>>12)+1)*2^-53))))',
            'rows': rows}


def main():
    text = json.dumps(document(), indent=1) + '\n'
    if '--check' in sys.argv:
        if OUTPUT.read_text() != text:
            sys.exit(f'{OUTPUT} differs from a fresh generation')
    else:
        OUTPUT.write_text(text)


if __name__ == '__main__':
    main()
