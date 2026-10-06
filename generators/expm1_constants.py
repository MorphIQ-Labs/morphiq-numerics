#!/usr/bin/env python3
"""The constants of expm1 (docs/expm1.md), with their errors.

Writes crates/morphiq-numerics/src/expm1/tables.rs; with --check, fails if the
committed file differs from a fresh generation. Needs mpmath
(generators/requirements.txt). `derive()` returns the values
generators/expm1_certificates.py uses.

- c3..c9: the small-argument polynomial, read from generators/expm1_poly.out,
  which generators/expm1_poly.sollya writes.
- DEGREE: the small-argument series degree (section 4): the least d whose
  truncation, the first omitted term A^(d+1)/(d+2)! over (e^x - 1)/x >= 1 - A/2,
  is at most 2^-125, negligible next to Q128's own rounding.
- RECIPROCALS[m - 2] = 1/m, m = 2..DEGREE + 1, as 128-bit significands.
"""
from fractions import Fraction
import math
import pathlib
import sys

import mpmath

ROOT = pathlib.Path(__file__).resolve().parents[1]
OUTPUT = ROOT / 'crates/morphiq-numerics/src/expm1/tables.rs'
POLY = ROOT / 'generators/expm1_poly.out'
A = Fraction(312501, 10_000_000)  # |x| <= 0.0312501: 2^-5 with margin
DEGREE = next(d for d in range(1, 64)
              if A ** (d + 1) / math.factorial(d + 2) / (1 - A / 2) <= Fraction(1, 2**125))


def read_poly():
    values = dict(line.split() for line in POLY.read_text().split('\n') if line.strip())
    return [float.fromhex(values[f'c{k}']) for k in range(3, 10)], values


def q128(v):
    with mpmath.workprec(600):
        e = int(mpmath.floor(mpmath.log(v, 2))) - 127
        m = int(mpmath.nint(v / mpmath.mpf(2) ** e))
        if m >> 128:
            m, e = int(mpmath.nint(v / mpmath.mpf(2) ** (e + 1))), e + 1
        assert m >> 127 == 1
        err = abs(mpmath.mpf(m) * mpmath.mpf(2) ** e - v) / v
    return m, e, err


def derive():
    mpmath.mp.prec = 600  # every value from its definition, before any rounding
    poly, values = read_poly()
    reciprocals, worst = [], 0
    for m in range(2, DEGREE + 2):
        mm, e, err = q128(mpmath.mpf(1) / m)
        worst = max(worst, err)
        reciprocals.append((mm, e))
    assert worst < mpmath.mpf(2) ** -127
    return dict(poly=poly, poly_bound=values['relative_error_bound'], reciprocals=reciprocals,
                worst_rec=worst, degree=DEGREE)


def generate():
    d = derive()
    to_bits = lambda x: int.from_bytes(__import__('struct').pack('>d', x), 'big')  # noqa: E731
    lines = [
        '//! Constants of `expm1`, written by `generators/expm1_constants.py`; do not',
        '//! edit. `docs/expm1.md` gives the derivation.',
        '',
        '/// The small-argument polynomial\'s tail (`generators/expm1_poly.sollya`): `c3..c9`',
        f'/// with relative error at most {d["poly_bound"]} on `2^-55 <= |x| <= 0.0312501`.',
        'pub(super) const POLY: [f64; 7] = [',
        *[f'    f64::from_bits(0x{to_bits(c):016x}),' for c in d['poly']],
        '];',
        f'/// `1/m`, `m = 2..={DEGREE + 1}`, as `(m, e)` with value `m * 2^e`; relative error below',
        f'/// 2^{float(mpmath.log(d["worst_rec"], 2)):.1f}.',
        f'pub(super) const RECIPROCALS: [(u128, i32); {DEGREE}] = [',
        *[f'    (0x{m:032x}, {e}),' for m, e in d['reciprocals']],
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
