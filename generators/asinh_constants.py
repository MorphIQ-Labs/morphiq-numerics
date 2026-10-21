#!/usr/bin/env python3
"""The constants of asinh (docs/asinh.md), with their errors.

Writes crates/morphiq-numerics/src/asinh/tables.rs; with --check, fails if the
committed file differs from a fresh generation. Needs mpmath
(generators/requirements.txt). `derive()` returns the values the certificates
use.

- POLY0 (section 3): `asinh z = z + z^3 P(z^2)` for 0 <= z <= 0.0078126, P of
  degree 3 in z^2 from generators/asinh_poly.out.
- LN2: ln 2 as a double-word `hi = RN(v)`, `lo = RN(v - hi)` (section 3, the
  large-argument form).
- EXP_STEPS: `1/n`, n = 1..=N, in Q256, the steps of the accurate path's
  series `exp r = 1 + r (1 + r/2 (1 + r/3 (...)))` (section 4), for
  |r| <= R_MAX; N is the least with the first omitted term below 2^-262.
- LN2_Q256 and INV_LN2: the reduction `y = k ln 2 + r` (section 4).
"""
import math
import pathlib
import struct
import sys

import mpmath

ROOT = pathlib.Path(__file__).resolve().parents[1]
OUTPUT = ROOT / 'crates/morphiq-numerics/src/asinh/tables.rs'
POLY = ROOT / 'generators/asinh_poly.out'
PREC = 700
# |r| <= ln2/2 plus the slack of rounding k = RN(y / ln 2) in binary64.
R_MAX = mpmath.mpf(3467) / 10000


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
    """v > 0 as (m, e, relative error): 2^255 <= m < 2^256, value m 2^e."""
    e = int(mpmath.floor(mpmath.log(v, 2))) - 255
    m = int(mpmath.nint(v / mpmath.mpf(2) ** e))
    if m >> 256:
        m, e = int(mpmath.nint(v / mpmath.mpf(2) ** (e + 1))), e + 1
    assert m >> 255 == 1
    return m, e, abs(mpmath.mpf(m) * mpmath.mpf(2) ** e - v) / v


def read_poly():
    return {n: v for n, v in (line.split() for line in POLY.read_text().split('\n') if line.strip())}


def exp_degree():
    """The least N with R_MAX^(N+1) / (N+1)! below 2^-262."""
    return next(n for n in range(1, 200)
                if R_MAX ** (n + 1) / mpmath.factorial(n + 1) <= mpmath.mpf(2) ** -262)


def derive():
    mpmath.mp.prec = PREC
    values = read_poly()
    poly0 = [float.fromhex(values[f'p00{j}']) for j in range(4)]
    ln2 = mpmath.log(2)
    hi = rn53(ln2)
    lo = rn53(ln2 - hi)
    ln2_error = abs(ln2 - mpmath.mpf(hi) - mpmath.mpf(lo)) / ln2
    assert ln2_error < mpmath.mpf(2) ** -106
    n = exp_degree()
    steps = [q256(mpmath.mpf(1) / k) for k in range(1, n + 1)]
    ln2_q = q256(ln2)
    return dict(values=values, poly0=poly0, ln2=(hi, lo), ln2_error=ln2_error, n=n,
                steps=steps, ln2_q=ln2_q, inv_ln2=rn53(1 / ln2))


def step(m, e):
    """One (limbs, exponent) entry, laid out as rustfmt lays it out."""
    return ['    (', '        [',
            *[f'            0x{(m >> (64 * i)) & ((1 << 64) - 1):016x},' for i in range(4)],
            '        ],', f'        {e},', '    ),']


def generate():
    d = derive()
    v = d['values']
    f = lambda x: f'f64::from_bits(0x{to_bits(x):016x})'  # noqa: E731
    worst_step = max(err for _, _, err in d['steps'])
    m, e, err = d['ln2_q']
    lines = [
        '//! Constants of `asinh`, written by `generators/asinh_constants.py`; do not',
        '//! edit. `docs/asinh.md` gives the derivation.',
        '',
        '/// `asinh z ≈ z + z³·(p0 + p1 z² + p2 z⁴ + p3 z⁶)` for `0 <= z <= 0.0078126`',
        f'/// (`generators/asinh_poly.sollya`): relative error of the series at most {v["v000"]}.',
        'pub(super) const POLY0: [f64; 4] = [',
        *[f'    {f(c)},' for c in d['poly0']],
        '];',
        '/// `ln 2` as a double-word `(hi, lo)`, relative error below '
        f'2^{float(mpmath.log(d["ln2_error"], 2)):.1f}.',
        'pub(super) const LN2: (f64, f64) = (',
        f'    {f(d["ln2"][0])},',
        f'    {f(d["ln2"][1])},',
        ');',
        '/// `1/RN(ln 2)`, from which the accurate path rounds `k = y/ln 2`.',
        f'pub(super) const INV_LN2: f64 = {f(d["inv_ln2"])};',
        f'/// `ln 2` in `Q256`, as `(m, e)`: four limbs least significant first, value `m 2^e`;',
        f'/// relative error below 2^{float(mpmath.log(err, 2)):.1f}.',
        'pub(super) const LN2_Q256: ([u64; 4], i32) = (',
        '    [',
        *[f'        0x{(m >> (64 * i)) & ((1 << 64) - 1):016x},' for i in range(4)],
        '    ],',
        f'    {e},',
        ');',
        f'/// `1/n`, `n = 1..={d["n"]}`, as `(m, e)`: four limbs least significant first, value',
        f'/// `m 2^e`; relative error below 2^{float(mpmath.log(worst_step, 2)):.1f}.',
        f'pub(super) const EXP_STEPS: [([u64; 4], i32); {d["n"]}] = [',
        *[line for m, e, _ in d['steps'] for line in step(m, e)],
        '];',
    ]
    return '\n'.join(lines) + '\n'


def main():
    data = generate()
    if '--check' in sys.argv[1:]:
        if OUTPUT.read_text() != data:
            sys.exit(f'{OUTPUT} differs from a fresh generation')
        return
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(data)


if __name__ == '__main__':
    main()
