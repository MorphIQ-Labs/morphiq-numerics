#!/usr/bin/env python3
"""The constants of sin and cos (docs/sin_cos.md), with their errors.

Writes crates/morphiq-numerics/src/trig/tables.rs; with --check, fails if the
committed file differs from a fresh generation. Needs mpmath
(generators/requirements.txt). `derive()` returns the values
generators/trig_certificates.py uses.

- POLY_S, POLY_C: the fast path's polynomials, from generators/trig_poly.out.
- TABLE[i] = (sin(i/64), cos(i/64)) as double-words, i = 0..50 (section 4).
- The accurate path's series (section 5), in s = r^2:
    sin r / r = 1 - s/(2.3) (1 - s/(4.5) (1 - ...)),
    cos r     = 1 - s/(1.2) (1 - s/(3.4) (1 - ...)),
  with the factors 1/((2n)(2n+1)) and 1/((2n-1)(2n)) as 256-bit significands,
  to the least degree whose first omitted term, over |r| <= pi/4 and relative
  to sin r / r >= 0.9 or cos r >= 0.7, is at most 2^-210.
- The ratios of each table interval (section 4), enclosed with mpmath.iv:
  the largest of S/sin(a+t), S|cos t - 1|/sin(a+t), C|sin t|/sin(a+t), and of
  C/cos(a+t), C|cos t - 1|/cos(a+t), S|sin t|/cos(a+t), over a = i/64 and the
  t the reduction can give.
"""
import math
import pathlib
import struct
import sys

import mpmath

ROOT = pathlib.Path(__file__).resolve().parents[1]
OUTPUT = ROOT / 'crates/morphiq-numerics/src/trig/tables.rs'
POLY = ROOT / 'generators/trig_poly.out'
PREC = 600
T = mpmath.mpf('0.0078126')  # |t| <= 1/128, widened for r's double-word error
N_TABLE = 51                 # i = round(64 r) <= round(64 pi/4) = 50


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


def q256(v):
    e = int(mpmath.floor(mpmath.log(v, 2))) - 255
    m = int(mpmath.nint(v / mpmath.mpf(2) ** e))
    if m >> 256:
        m, e = int(mpmath.nint(v / mpmath.mpf(2) ** (e + 1))), e + 1
    assert m >> 255 == 1
    return m, e, abs(mpmath.mpf(m) * mpmath.mpf(2) ** e - v) / v


def degree(first_omitted):
    return next(n for n in range(1, 64) if first_omitted(n) <= mpmath.mpf(2) ** -210)


def read_poly():
    values = dict(line.split() for line in POLY.read_text().split('\n') if line.strip())
    return values


def ratios():
    """The largest ratios over the table intervals, enclosed with mpmath.iv."""
    iv = mpmath.iv
    iv.prec = 128
    quarter_pi = mpmath.pi / 4
    best = dict(ks=0, ka=0, kb=0, kc=0, kca=0, ksb=0)
    up = lambda x: max(abs(mpmath.mp.make_mpf(x._mpi_[0])), abs(mpmath.mp.make_mpf(x._mpi_[1])))  # noqa: E731
    for i in range(N_TABLE):
        a = mpmath.mpf(i) / 64
        lo, hi = (mpmath.mpf(0) if i == 0 else -T), min(T, quarter_pi - a + mpmath.mpf(2) ** -50)
        if hi < lo:
            continue
        t = iv.mpf([lo, hi])
        x = iv.mpf(a) + t
        sin_x, cos_x = iv.sin(x), iv.cos(x)
        s, c = iv.sin(iv.mpf(a)), iv.cos(iv.mpf(a))
        cm, sn = abs(iv.cos(t) - 1), abs(iv.sin(t))
        if i > 0:
            best['ks'] = max(best['ks'], up(s / sin_x))
            best['ka'] = max(best['ka'], up(s * cm / sin_x))
            best['kb'] = max(best['kb'], up(c * sn / sin_x))
        else:
            # a = 0: sin(a + t) = sin t, S = 0 and C = 1, so C sin t over it is 1.
            best['kb'] = max(best['kb'], mpmath.mpf(1))
        best['kc'] = max(best['kc'], up(c / cos_x))
        best['kca'] = max(best['kca'], up(c * cm / cos_x))
        best['ksb'] = max(best['ksb'], up(s * sn / cos_x))
    return best


def derive():
    mpmath.mp.prec = PREC
    values = read_poly()
    table, worst = [], 0
    for i in range(N_TABLE):
        a = mpmath.mpf(i) / 64
        row = []
        for v in (mpmath.sin(a), mpmath.cos(a)):
            hi = rn53(v)
            lo = rn53(v - hi)
            if v != 0:
                worst = max(worst, abs(v - hi - lo) / abs(v))
            row.append((hi, lo))
        table.append(row)
    assert worst < mpmath.mpf(2) ** -106
    q = mpmath.pi / 4
    n_sin = degree(lambda n: q ** (2 * n + 2) / mpmath.factorial(2 * n + 3) / mpmath.mpf('0.9'))
    n_cos = degree(lambda n: q ** (2 * n + 2) / mpmath.factorial(2 * n + 2) / mpmath.mpf('0.7'))
    sin_steps = [q256(mpmath.mpf(1) / ((2 * n) * (2 * n + 1))) for n in range(1, n_sin + 1)]
    cos_steps = [q256(mpmath.mpf(1) / ((2 * n - 1) * (2 * n))) for n in range(1, n_cos + 1)]
    worst_q = max(e for _, _, e in sin_steps + cos_steps)
    assert worst_q < mpmath.mpf(2) ** -255
    return dict(values=values, table=table, worst=worst, n_sin=n_sin, n_cos=n_cos,
                sin_steps=sin_steps, cos_steps=cos_steps, worst_q=worst_q, ratios=ratios())


def step(m, e):
    """One (limbs, exponent) entry, laid out as rustfmt lays it out."""
    return ['    (', '        [',
            *[f'            0x{(m >> (64 * i)) & ((1 << 64) - 1):016x},' for i in range(4)],
            '        ],', f'        {e},', '    ),']


def generate():
    d = derive()
    v = d['values']
    f = lambda x: f'f64::from_bits(0x{to_bits(x):016x})'  # noqa: E731
    lines = [
        '//! Constants of `sin` and `cos`, written by `generators/trig_constants.py`; do',
        '//! not edit. `docs/sin_cos.md` gives the derivation.',
        '',
        '/// `(sin t − t)/t³ ≈ Ps(t²)` (`generators/trig_poly.sollya`): relative error at most',
        f'/// {v["sin_error_bound"]} on `|t| <= 0.0078126`.',
        'pub(super) const POLY_S: [f64; 3] = [',
        *[f'    {f(float.fromhex(v[f"s{k}"]))},' for k in range(3)],
        '];',
        '/// `(cos t − 1 + t²/2)/t⁴ ≈ Pc(t²)`: relative error at most',
        f'/// {v["cos_error_bound"]} on `|t| <= 0.0078126`.',
        'pub(super) const POLY_C: [f64; 3] = [',
        *[f'    {f(float.fromhex(v[f"c{k}"]))},' for k in range(3)],
        '];',
        '/// `(sin(i/64), cos(i/64))`, each a double-word `(hi, lo)` as binary64 encodings;',
        f'/// relative error below 2^{float(mpmath.log(d["worst"], 2)):.1f}.',
        f'pub(super) const TABLE: [[(u64, u64); 2]; {N_TABLE}] = [',
        *[line for s, c in d['table'] for line in (
            '    [',
            f'        (0x{to_bits(s[0]):016x}, 0x{to_bits(s[1]):016x}),',
            f'        (0x{to_bits(c[0]):016x}, 0x{to_bits(c[1]):016x}),',
            '    ],')],
        '];',
        f'/// `1/((2n)(2n+1))`, `n = 1..={d["n_sin"]}`, as `(m, e)`: four limbs least significant',
        f'/// first, value `m 2^e`; relative error below 2^{float(mpmath.log(d["worst_q"], 2)):.1f}.',
        f'pub(super) const SIN_STEPS: [([u64; 4], i32); {d["n_sin"]}] = [',
        *[line for m, e, _ in d['sin_steps'] for line in step(m, e)],
        '];',
        f'/// `1/((2n−1)(2n))`, `n = 1..={d["n_cos"]}`, likewise.',
        f'pub(super) const COS_STEPS: [([u64; 4], i32); {d["n_cos"]}] = [',
        *[line for m, e, _ in d['cos_steps'] for line in step(m, e)],
        '];',
    ]
    return '\n'.join(lines) + '\n'


def main():
    data = generate()
    if '--check' in sys.argv[1:]:
        if OUTPUT.read_text() != data:
            sys.exit(f'{OUTPUT} differs from a fresh generation')
        return
    OUTPUT.write_text(data)


if __name__ == '__main__':
    main()
