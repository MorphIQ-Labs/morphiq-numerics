#!/usr/bin/env python3
"""Independent oracle for `DoubleWord::exp_split` (docs/double-word.md#exponential).

For a double-word input `x = hi + lo` it records `m = round(x / ln 2)` and
`exp(x) * 2^-m` at 600 bits as three binary64 words (high, mid, low; their sum
is within 2^-150 relative of the value), so the test compares
`value * 2^(n - m)` with it in exact integer arithmetic without overflowing
binary64. Inputs: uniform and log-spaced arguments over the domain
`|hi| < 1455`, both signs; every 1024-way reduction seam neighbourhood on a
sample of multiples of ln(2)/1024; the domain limits; the tiny-argument switch
at 2^-60; and random trailing words below half an ulp of the leading word.

mpmath 1.4.1 (generators/requirements.txt), seeded, deterministic.
Usage: double_word_exp_reference.py [--check]
"""
from pathlib import Path
import json
import random
import struct
import sys

import mpmath as mp

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'crates/reference/fixtures/double_word_exp.json'
PREC = 600


def bits(x):
    return struct.unpack('<Q', struct.pack('<d', x))[0]


def ulp(x):
    if x == 0.0:
        return 5e-324
    m, e = mp.frexp(mp.mpf(abs(x)))
    return float(mp.ldexp(1, int(e) - 53))


def trailing(rng, hi):
    if rng.random() < 0.15:
        return 0.0
    lo = (rng.random() - 0.5) * ulp(hi) * 0.999
    return lo if hi + lo == hi else 0.0


def words(v):
    out = []
    for _ in range(3):
        w = float(v)
        out.append(w)
        v -= mp.mpf(w)
    return out


def cases():
    rng = random.Random(266)
    xs = []
    for _ in range(6000):
        xs.append(rng.uniform(-1454.999, 1454.999))
    for _ in range(4000):
        mag = 10 ** rng.uniform(-18, 3.16)
        xs.append(mag if rng.random() < 0.5 else -mag)
    with mp.workprec(PREC):
        step = mp.log(2) / 1024
        for _ in range(2000):
            n = rng.randint(-2_150_000, 2_150_000)
            seam = float((n + mp.mpf('0.5')) * step)
            centre = float(n * step)
            for base in (seam, centre):
                if abs(base) < 1454.999:
                    xs.extend([base, mp_next(base, 1), mp_next(base, -1)])
    for edge in (1454.999, -1454.999, 1454.0, -1454.0, 2.0 ** -60, -(2.0 ** -60),
                 2.0 ** -59, -(2.0 ** -59), 2.0 ** -61, 1e-300, -1e-300, 0.0):
        xs.extend([edge, mp_next(edge, 1), mp_next(edge, -1)])
    rows = []
    with mp.workprec(PREC):
        ln2 = mp.log(2)
        for hi in xs:
            if not abs(hi) < 1455.0:
                continue
            lo = trailing(rng, hi)
            x = mp.mpf(hi) + mp.mpf(lo)
            m = int(mp.nint(x / ln2))
            ref = mp.exp(x) * mp.ldexp(1, -m)
            high, mid, low = words(ref)
            rows.append({'hi': f'{bits(hi):016x}', 'lo': f'{bits(lo):016x}', 'm': m,
                         'high': f'{bits(high):016x}', 'mid': f'{bits(mid):016x}',
                         'low': f'{bits(low):016x}'})
    return rows


def mp_next(x, direction):
    import math
    return math.nextafter(x, math.inf if direction > 0 else -math.inf)


def main():
    text = json.dumps({'generator': 'generators/double_word_exp_reference.py',
                       'mpmath': mp.__version__, 'precision_bits': PREC,
                       'cases': cases()}, separators=(',', ':')) + '\n'
    if '--check' in sys.argv:
        if not OUT.exists() or OUT.read_text() != text:
            raise SystemExit(f'generated file differs: {OUT.relative_to(ROOT)}')
    else:
        OUT.write_text(text)


if __name__ == '__main__':
    main()
