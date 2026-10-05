#!/usr/bin/env python3
"""The constants of exp (docs/exp.md), with their errors.

Writes crates/morphiq-numerics/src/exp/tables.rs; with --check, fails if the
committed file differs from a fresh generation. Needs mpmath
(generators/requirements.txt). Every value is computed from its definition with
mpmath at 600 bits and rounded once, in integer arithmetic, to the stated
format; each error is checked against the bound docs/exp.md relies on.

- INV_L = RN(128 / ln 2), and the shifter 1.5 * 2^52 (section 3, steps 1 and 2).
- L1..L4: L = ln 2 / 128 split so that n * L1 is exact for |n| < 2^18 (L1 has
  35 significant bits) and |L - (L1 + L2 + L3 + L4)| < 2^-200 (section 3, step 4).
- T[j] = 2^(j/128), j = 0..127: as a double-word (hi, lo) for the fast path,
  and as a 128-bit significand, top bit set, value m * 2^-127, for the
  accurate path (sections 4 and 6).
- RECIPROCALS[k] = 1/k, k = 1..12, as 128-bit significands with exponents, for
  the accurate path's Taylor series (section 6).
- c3..c6: the fast path's polynomial, read from generators/exp_poly.out, which
  generators/exp_poly.sollya writes (fpminimax, with the supnorm error bound).
"""
import math
import pathlib
import struct
import sys

import mpmath

ROOT = pathlib.Path(__file__).resolve().parents[1]
OUTPUT = ROOT / 'crates/morphiq-numerics/src/exp/tables.rs'
POLY = ROOT / 'generators/exp_poly.out'
PREC = 600


def to_bits(x):
    return struct.unpack('<Q', struct.pack('<d', x))[0]


def rn_bits(v, bits):
    """v (an mpf) rounded to nearest-even with `bits` significant bits, exactly,
    as a Python float when bits <= 53. v is nonzero and in binary64's normal range."""
    v = mpmath.mpf(v)
    sign = -1 if v < 0 else 1
    man, exp = abs(v).man_exp
    man = int(man)
    shift = man.bit_length() - bits
    if shift > 0:
        m, rem, half = man >> shift, man & ((1 << shift) - 1), 1 << (shift - 1)
        if rem > half or (rem == half and m & 1):
            m += 1
        exp += shift
    else:
        m = man
    return sign * math.ldexp(m, int(exp))


def q128(v):
    """A positive mpf as a 128-bit significand with its top bit set and an
    exponent: v ~ m * 2^e, rounded to nearest. Returns (m, e, |error| / v)."""
    with mpmath.workprec(PREC):
        e = int(mpmath.floor(mpmath.log(v, 2))) - 127
        m = int(mpmath.nint(v / mpmath.mpf(2) ** e))
        if m >> 128:
            m, e = int(mpmath.nint(v / mpmath.mpf(2) ** (e + 1))), e + 1
        assert m >> 127 == 1, 'normalized'
        err = abs(mpmath.mpf(m) * mpmath.mpf(2) ** e - v) / v
    return m, e, err


def read_poly():
    """c3..c6 and the supnorm bound, as generators/exp_poly.sollya printed them.
    Each coefficient must be exactly a binary64: parsed as a float and as an
    arbitrary-precision number, the two must agree."""
    values = dict(line.split() for line in POLY.read_text().split('\n') if line.strip())
    coefficients = []
    for k in (3, 4, 5, 6):
        c = float.fromhex(values[f'c{k}'])
        with mpmath.workprec(PREC):
            assert mpmath.mpf(c) == mpmath.mpf(mpmath.mpmathify(float.fromhex(values[f'c{k}'])))
        coefficients.append(c)
    return coefficients, values['error_bound']


def generate():
    mpmath.mp.prec = PREC
    ln2 = mpmath.log(2)
    L = ln2 / 128
    inv_l = rn_bits(128 / ln2, 53)

    l1 = rn_bits(L, 35)
    l2 = rn_bits(L - l1, 53)
    l3 = rn_bits(L - l1 - l2, 53)
    l4 = rn_bits(L - l1 - l2 - l3, 53)
    residual = abs(L - (mpmath.mpf(l1) + l2 + l3 + l4))
    assert residual < mpmath.mpf(2) ** -200, f'residual 2^{float(mpmath.log(residual, 2))}'
    # n * L1 exact for |n| < 2^18: L1 has at most 35 significant bits.
    m1, _ = mpmath.mpf(l1).man_exp
    assert abs(int(m1)).bit_length() <= 35

    table_dw, table_q, worst_dw, worst_q = [], [], 0, 0
    for j in range(128):
        t = mpmath.mpf(2) ** (mpmath.mpf(j) / 128)
        hi = rn_bits(t, 53)
        lo = rn_bits(t - hi, 53) if t != hi else 0.0
        assert hi + lo == hi, 'double-word: hi = RN(hi + lo)'
        worst_dw = max(worst_dw, abs(t - hi - lo) / t)
        m, e, err = q128(t)
        assert e == -127
        worst_q = max(worst_q, err)
        table_dw.append((hi, lo))
        table_q.append(m)
    assert worst_dw < mpmath.mpf(2) ** -106, 'double-word table error'
    assert worst_q < mpmath.mpf(2) ** -127, 'Q128 table error'

    reciprocals, worst_r = [], 0
    for k in range(1, 13):
        m, e, err = q128(mpmath.mpf(1) / k)
        worst_r = max(worst_r, err)
        reciprocals.append((m, e))
    assert worst_r < mpmath.mpf(2) ** -127

    poly, poly_bound = read_poly()

    log2 = lambda v: float(mpmath.log(v, 2))  # noqa: E731
    f = lambda x: f'f64::from_bits(0x{to_bits(x):016x})'  # noqa: E731
    lines = [
        '//! Constants of `exp`, written by `generators/exp_constants.py`; do not edit.',
        '//! Each comment states the definition and the error the generator checked;',
        '//! `docs/exp.md` gives the derivation.',
        '',
        f'/// `RN(128 / ln 2)` ({inv_l!r}).',
        f'pub(super) const INV_L: f64 = {f(inv_l)};',
        '/// `1.5 * 2^52`: adding and subtracting it rounds to the nearest integer.',
        f'pub(super) const SHIFTER: f64 = {f(1.5 * 2.0 ** 52)};',
        f'/// `L = ln 2 / 128 = L1 + L2 + L3 + L4` to within 2^{log2(residual):.1f};',
        '/// `L1` has 35 significant bits, so `n * L1` is exact for `|n| < 2^18`.',
        f'pub(super) const L1: f64 = {f(l1)};',
        f'pub(super) const L2: f64 = {f(l2)};',
        f'pub(super) const L3: f64 = {f(l3)};',
        f'pub(super) const L4: f64 = {f(l4)};',
        '/// The fast path\'s polynomial coefficients (`generators/exp_poly.sollya`):',
        f'/// `|e^r - 1 - r - r^2 (1/2 + r (c3 + ...))| <= {poly_bound}` on `|r| <= 0.0027077`.',
        'pub(super) const POLY: [f64; 4] = [',
        *[f'    {f(c)},' for c in poly],
        '];',
        f'/// `2^(j/128)` as a double-word `(hi, lo)`, as binary64 encodings; relative',
        f'/// error below 2^{log2(worst_dw):.1f}.',
        'pub(super) const T_BITS: [(u64, u64); 128] = [',
        *[f'    (0x{to_bits(hi):016x}, 0x{to_bits(lo):016x}),' for hi, lo in table_dw],
        '];',
        f'/// `2^(j/128)` as `m * 2^-127`; relative error below 2^{log2(worst_q):.1f}.',
        'pub(super) const T_Q128: [u128; 128] = [',
        *[f'    0x{m:032x},' for m in table_q],
        '];',
        f'/// `1/k`, `k = 1..=12`, as `(m, e)` with value `m * 2^e`; relative error below 2^{log2(worst_r):.1f}.',
        'pub(super) const RECIPROCALS: [(u128, i32); 12] = [',
        *[f'    (0x{m:032x}, {e}),' for m, e in reciprocals],
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
