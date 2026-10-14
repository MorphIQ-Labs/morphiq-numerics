#!/usr/bin/env python3
"""Independent erfcx witnesses, mpmath 1.4.1 at 600 and 1000 bits.

Direct exp(x*x)*erfc(x) below 64; above it, the alternating asymptotic
series, stopped before its first omitted term is below 2^(-prec-16).
Every emitted binary64 rounding must agree at both precisions. These are
oracle witnesses, not an exhaustive correct-rounding claim.
"""
import json
import math
import pathlib
import random
import struct
import sys
import mpmath as mp

ROOT = pathlib.Path(__file__).resolve().parents[1]
OUT = ROOT / 'crates/reference/fixtures/erfcx.json'

def bits(x):
    return struct.pack('>d', x).hex()

def number(b):
    return struct.unpack('>d', bytes.fromhex(b))[0]

def value(x, prec):
    with mp.workprec(prec):
        z = mp.mpf(x)
        if x < 64:
            return mp.exp(z*z) * mp.erfc(z)
        t = 1 / (2*z*z)
        term = mp.mpf(1)
        total = term
        for k in range(1, 10000):
            term *= -(2*k - 1)*t
            if abs(term) < mp.mpf(2)**(-prec-16):
                return total/(z*mp.sqrt(mp.pi))
            total += term
        raise AssertionError('asymptotic series did not converge to target')

def round_binary64(v):
    # Round the high-precision dyadic once, on the actual binary64 grid.
    # float(mpf) may double-round at the normal/subnormal boundary.
    m, e = v.man_exp
    m, e = int(m), int(e)
    quantum = max(m.bit_length() - 1 + e - 52, -1074)
    shift = quantum - e
    if shift > 0:
        kept, rem = divmod(m, 1 << shift)
        half = 1 << (shift - 1)
        if rem > half or (rem == half and kept & 1): kept += 1
    else: kept = m << -shift
    try: return math.ldexp(float(kept), quantum)
    except OverflowError: return math.inf

def expected(x):
    if math.isnan(x):
        return bits(x)
    if x == math.inf: return bits(0.0)
    if x < -27: return bits(math.inf)
    a, b = round_binary64(value(x, 600)), round_binary64(value(x, 1000))
    assert bits(a) == bits(b), x
    return bits(a)

def main():
    points = [0.3, 32., 1024., -2., -20., 1e308, 0., -0., math.inf, -math.inf, number('7ff8000000001234'),
              number('fff8000000005678'), number('7ff0000000004321'),
              math.ulp(0.), -math.ulp(0.), float.fromhex('0x1.fffffffffffffp1023')]
    edges = [number(w) for w in ['c03aa0f4d2e063cf','3c8c5bf891b4ef6b',
             'bc9c5bf891b4ef69','7fc20dd750429b6e']]
    edges += [-.5, 1., 16., 512., 1e270, 2.**46]
    edges += [(k+.5)/32 for k in range(-16, 32)]
    edges += [2.**e*(1+i/32) for e in range(4) for i in range(33)]
    for x in edges:
        points.append(x)
        lo, hi = x, x
        for _ in range(3):
            lo, hi = math.nextafter(lo, -math.inf), math.nextafter(hi, math.inf)
            points.extend([lo, hi])
    rng = random.Random(0x34_e2fc)
    for _ in range(256):
        points += [rng.uniform(-26.628, -.5), rng.uniform(-.5, 16),
                   rng.uniform(16, 512), math.ldexp(rng.uniform(1,2),rng.randrange(9,1023)),
                   math.ldexp(rng.uniform(-1,1),rng.randrange(-70,-45))]
    data = {'provenance': {'generator': 'generators/erfcx_reference.py',
            'mpmath': mp.__version__, 'precisions': [600, 1000]},
            'cases': [{'x': bits(x), 'y': expected(x)} for x in points]}
    text = json.dumps(data, indent=2)+'\n'
    if '--check' in sys.argv:
        assert OUT.read_text() == text, 'erfcx fixture differs'
    else: OUT.write_text(text)
    print(f'erfcx: {len(points)} independently rounded witnesses')

if __name__ == '__main__': main()
