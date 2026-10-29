#!/usr/bin/env python3
"""Independent high/low oracle intervals for the explicit fast contracts.

The binary64-rounded fixtures cannot resolve every allowed fast result: adding
half an ULP of reference uncertainty can reject a result within the public
bound. Reuse their input bits, evaluate the mathematical definitions at 600 and
1000 bits, and retain two binary64 words plus a conservative uncertainty of
abs(high)*2^-104 + 2^-1074. Both precision observations must lie inside this
interval. With u=2^-53, rounding high and its residual costs at most
u*u/(1-u)*abs(high) plus half a minimum subnormal; 2^-104=4*u*u
retains two guard bits for the independent oracle observation. These are
independent oracle witnesses, not whole-domain proofs.
"""
from pathlib import Path
import json
import math
import struct
import sys

import mpmath as mp

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / 'crates/reference/fixtures/fast.json'


def number(word):
    return struct.unpack('>d', bytes.fromhex(word))[0]


def word(value):
    return struct.pack('>d', value).hex()


def rounded(value):
    """Round a high-precision dyadic once on the binary64 grid, including lows."""
    negative, mantissa, exponent, _ = value._mpf_
    mantissa, exponent = int(mantissa), int(exponent)
    if not mantissa:
        return 0.0
    quantum = max(mantissa.bit_length() - 1 + exponent - 52, -1074)
    shift = quantum - exponent
    if shift > 0:
        kept, remainder = divmod(mantissa, 1 << shift)
        half = 1 << (shift - 1)
        if remainder > half or (remainder == half and kept & 1):
            kept += 1
    else:
        kept = mantissa << -shift
    result = math.ldexp(float(kept), quantum)
    return -result if negative else result


def reference(primitive, x, precision):
    with mp.workprec(precision):
        a = mp.mpf(x)
        if primitive == 'exp':
            return mp.exp(a)
        if primitive == 'erfcx':
            return mp.exp(a*a)*mp.erfc(a)
        return mp.erfc(-a/mp.sqrt(2))/2


def generate():
    cases = []
    for primitive, filename in [('exp', 'exp.json'), ('erfcx', 'erfcx.json'), ('cdf', 'normal.json')]:
        fixture = json.loads((OUTPUT.parent/filename).read_text())
        for row in fixture['cases']:
            x = number(row['x'])
            active = (abs(x) < 704 if primitive == 'exp' else
                      -.5 <= x < 16 and abs(x) >= 2**-33 if primitive == 'erfcx' else
                      2**-33 <= abs(x) <= 8)
            if not active:
                continue
            first = reference(primitive, x, 600)
            second = reference(primitive, x, 1000)
            with mp.workprec(1000):
                high = rounded(second)
                low = rounded(second-mp.mpf(high))
                center = mp.mpf(high)+mp.mpf(low)
                uncertainty = abs(mp.mpf(high))*mp.mpf(2)**-104 + mp.mpf(2)**-1074
                assert abs(first-center) <= uncertainty, (primitive, row['x'], 600)
                assert abs(second-center) <= uncertainty, (primitive, row['x'], 1000)
            cases.append(dict(primitive=primitive, x=row['x'], high=word(high), low=word(low)))
    return json.dumps(dict(provenance=dict(generator='generators/fast_reference.py',
        oracle='mpmath, pinned by generators/requirements.txt', precision_bits=[600, 1000],
        input_generators=['exp_reference.py', 'erfcx_reference.py', 'normal_reference.py'],
        uncertainty='abs(high)*2^-104 + 2^-1074; both precision observations enclosed'), cases=cases), indent=2)+'\n'


if __name__ == '__main__':
    text = generate()
    if '--check' in sys.argv:
        if not OUTPUT.exists() or OUTPUT.read_text() != text:
            raise SystemExit(f'generated file differs: {OUTPUT.relative_to(ROOT)}')
    else:
        OUTPUT.write_text(text)
