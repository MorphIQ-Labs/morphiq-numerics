#!/usr/bin/env python3
"""The constants of atan2 (docs/atan2.md), with their errors.

Writes crates/morphiq-numerics/src/atan2/tables.rs; with --check, fails if the
committed file differs from a fresh generation. Needs mpmath
(generators/requirements.txt). `derive()` returns the values the certificates
use.

- SEGMENTS[k - 1], k = 1..=64 (section 4): for `a = k/64`,
    [atan(a).hi, atan(a).lo, c1.hi, c1.lo, g0, ..., g8]
  with `c1 = 1/(1 + a^2)` and `G_k`'s coefficients from
  generators/atan2_poly.out, so that
    atan(a + t) = atan(a) + c1 t + t^2 (g0 + g1 t + ... + g8 t^8)
  on |t| <= 0.0078126. The double-words are `hi = RN(v)`, `lo = RN(v - hi)`.
- POLY0 (section 4): `atan z = z + z^3 (p0 + p1 z^2 + p2 z^4 + p3 z^6)` for
  z <= 0.0078126, from the same file.
- HALF_PI: pi/2 as a double-word.

The polynomials' errors are the Sollya supnorm plus the Taylor remainder bound
of atan2_poly.sollya. As a check, not a proof, the generator also evaluates
each segment's polynomial at 400 points in mpmath and refuses a deviation
larger than that bound.
"""
import math
import pathlib
import re
import struct
import sys

import mpmath

ROOT = pathlib.Path(__file__).resolve().parents[1]
OUTPUT = ROOT / 'crates/morphiq-numerics/src/atan2/tables.rs'
POLY = ROOT / 'generators/atan2_poly.out'
PREC = 600
T = mpmath.mpf('0.0078126')  # |t| <= 1/128, widened for z's double-word error
SEGMENTS = 64                # k = round(64 t) <= 64 for t <= 1
DEGREE = 8


def to_bits(x):
    return struct.unpack('<Q', struct.pack('<d', x))[0]


def rn53(v):
    v = mpmath.mpf(v)
    if v == 0:
        return 0.0
    sign = -1 if v < 0 else 1
    man, exp = abs(v).man_exp
    man = int(man)
    shift = man.bit_length() - 53
    if shift > 0:
        m, rem, half = man >> shift, man & ((1 << shift) - 1), 1 << (shift - 1)
        if rem > half or (rem == half and m & 1):
            m += 1
        exp += shift
    else:
        m = man
    return sign * math.ldexp(m, int(exp))


def read_poly():
    return {n: v for n, v in (line.split() for line in POLY.read_text().split('\n') if line.strip())}


def double_word(v):
    hi = rn53(v)
    lo = rn53(v - hi)
    return hi, lo, abs(v - hi - lo) / abs(v)


def derive():
    mpmath.mp.prec = PREC
    values = read_poly()
    rows, worst_dw, worst_poly = [], mpmath.mpf(0), mpmath.mpf(0)
    for k in range(1, SEGMENTS + 1):
        a = mpmath.mpf(k) / 64
        y = double_word(mpmath.atan(a))
        c1 = double_word(1 / (1 + a * a))
        worst_dw = max(worst_dw, y[2], c1[2])
        g = [float.fromhex(values[f'g{k:02d}{j}']) for j in range(DEGREE + 1)]
        bound = mpmath.mpf(float.fromhex(values[f'u{k:02d}0'])) + mpmath.mpf(float.fromhex(values[f'r{k:02d}0']))
        # Not a proof: the polynomial against atan at 400 points.
        deviation = mpmath.mpf(0)
        for i in range(401):
            t = -T + 2 * T * i / 400
            p = mpmath.mpf(0)
            for c in reversed(g):
                p = p * t + mpmath.mpf(c)
            approx = mpmath.mpf(y[0]) + mpmath.mpf(y[1]) + (mpmath.mpf(c1[0]) + mpmath.mpf(c1[1])) * t + t * t * p
            deviation = max(deviation, abs(approx - mpmath.atan(a + t)))
        assert deviation <= bound * T * T * (1 + mpmath.mpf(2) ** -20) + mpmath.mpf(2) ** -105, (
            f'segment {k}: deviation {mpmath.nstr(deviation, 5)} exceeds {mpmath.nstr(bound * T * T, 5)}')
        worst_poly = max(worst_poly, bound * T * T / mpmath.atan(a - T))
        rows.append((y[0], y[1], c1[0], c1[1], *g))
    assert worst_dw < mpmath.mpf(2) ** -106
    poly0 = [float.fromhex(values[f'p0{0}{j}']) for j in range(4)]
    half_pi = double_word(mpmath.pi / 2)
    return dict(values=values, rows=rows, poly0=poly0, worst_dw=worst_dw,
                worst_poly=worst_poly, half_pi=half_pi)


def generate():
    d = derive()
    v = d['values']
    f = lambda x: f'f64::from_bits(0x{to_bits(x):016x})'  # noqa: E731
    lines = [
        '//! Constants of `atan2`, written by `generators/atan2_constants.py`; do not',
        '//! edit. `docs/atan2.md` gives the derivation.',
        '',
        '/// `atan z ≈ z + z³·(p0 + p1 z² + p2 z⁴ + p3 z⁶)` for `0 <= z <= 0.0078126`',
        f'/// (`generators/atan2_poly.sollya`): relative error of the series at most {v["v000"]}.',
        'pub(super) const POLY0: [f64; 4] = [',
        *[f'    {f(c)},' for c in d['poly0']],
        '];',
        '/// `[atan(a).hi, atan(a).lo, c1.hi, c1.lo, g0, ..., g8]` for `a = k/64`,',
        '/// `k = 1..=64` at index `k - 1`, `c1 = 1/(1 + a²)`:',
        '/// `atan(a + t) = atan(a) + c1·t + t²·(g0 + g1·t + … + g8·t⁸)` on `|t| <= 0.0078126`.',
        f'/// The double-words have relative error below 2^{float(mpmath.log(d["worst_dw"], 2)):.1f}; the',
        '/// polynomials are bounded by `generators/atan2_poly.out`.',
        f'pub(super) const SEGMENTS: [[f64; {4 + DEGREE + 1}]; {SEGMENTS}] = [',
        *[line for row in d['rows'] for line in ('    [', *[f'        {f(x)},' for x in row], '    ],')],
        '];',
        '/// `π/2` as a double-word `(hi, lo)`.',
        'pub(super) const HALF_PI: (f64, f64) = (',
        f'    {f(d["half_pi"][0])},',
        f'    {f(d["half_pi"][1])},',
        ');',
    ]
    return '\n'.join(lines) + '\n'


def main():
    outputs = {OUTPUT: generate()}
    if '--check' in sys.argv[1:]:
        for path, data in outputs.items():
            if path.read_text() != data:
                sys.exit(f'{path} differs from a fresh generation')
        return
    for path, data in outputs.items():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(data)


if __name__ == '__main__':
    main()
