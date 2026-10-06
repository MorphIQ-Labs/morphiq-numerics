#!/usr/bin/env python3
"""The constants of exp2, log2 and log10 (docs/exp2.md, docs/log2.md), with
their errors.

Writes crates/morphiq-numerics/src/exp2/tables.rs and
crates/morphiq-numerics/src/log2/tables.rs; with --check, fails if either
committed file differs from a fresh generation. Needs mpmath
(generators/requirements.txt). Every value is computed with mpmath at 600 bits
and rounded once, in integer arithmetic; each error is checked against the
bound the documents and certificates rely on. `derive()` returns the errors
for generators/radix_certificates.py.

- LN2_HI = RN(ln 2), LN2_LO = RN(ln 2 - LN2_HI): exp2's r ln 2 (docs/exp2.md).
- LN2 as a 128-bit significand: exp2's accurate path.
- 1/ln 2 and 1/ln 10, each as a double-word (hi, lo) and as a 128-bit
  significand: log2's and log10's scaling (docs/log2.md).
"""
import math
import pathlib
import struct
import sys

import mpmath

ROOT = pathlib.Path(__file__).resolve().parents[1]
EXP2 = ROOT / 'crates/morphiq-numerics/src/exp2/tables.rs'
LOG2 = ROOT / 'crates/morphiq-numerics/src/log2/tables.rs'
PREC = 600


def to_bits(x):
    return struct.unpack('<Q', struct.pack('<d', x))[0]


def rn53(v):
    """v (nonzero, normal range) rounded to nearest-even binary64, exactly."""
    v = mpmath.mpf(v)
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


def q128(v):
    """A positive mpf as (m, e), v ~ m 2^e with m's top bit set; and the
    relative error."""
    e = int(mpmath.floor(mpmath.log(v, 2))) - 127
    m = int(mpmath.nint(v / mpmath.mpf(2) ** e))
    if m >> 128:
        m, e = int(mpmath.nint(v / mpmath.mpf(2) ** (e + 1))), e + 1
    assert m >> 127 == 1
    return m, e, abs(mpmath.mpf(m) * mpmath.mpf(2) ** e - v) / v


def double_word(v):
    hi = rn53(v)
    lo = rn53(v - hi)
    assert hi + lo == hi
    return hi, lo, abs(v - hi - lo) / v


def derive():
    mpmath.mp.prec = PREC
    ln2 = mpmath.log(2)
    d = {}
    d['ln2_hi'], d['ln2_lo'], d['ln2_err'] = double_word(ln2)
    assert d['ln2_err'] < mpmath.mpf(2) ** -106
    d['ln2_m'], d['ln2_e'], d['ln2_qerr'] = q128(ln2)
    for name, v in (('inv_ln2', 1 / ln2), ('inv_ln10', 1 / mpmath.log(10))):
        hi, lo, err = double_word(v)
        assert err < mpmath.mpf(2) ** -106
        m, e, qerr = q128(v)
        assert qerr < mpmath.mpf(2) ** -127
        d[name] = dict(hi=hi, lo=lo, err=err, m=m, e=e, qerr=qerr)
    assert d['ln2_qerr'] < mpmath.mpf(2) ** -127
    return d


def log2(v):
    return float(mpmath.log(v, 2))


def f(x):
    return f'f64::from_bits(0x{to_bits(x):016x})'


def generate():
    d = derive()
    exp2 = '\n'.join([
        '//! Constants of `exp2`, written by `generators/radix_constants.py`; do not',
        '//! edit. `docs/exp2.md` gives the derivation.',
        '',
        f'/// `RN(ln 2)` and `RN(ln 2 - LN2_HI)`: together within 2^{log2(d["ln2_err"]):.1f} relative of `ln 2`.',
        f'pub(super) const LN2_HI: f64 = {f(d["ln2_hi"])};',
        f'pub(super) const LN2_LO: f64 = {f(d["ln2_lo"])};',
        f'/// `ln 2` as `m * 2^{d["ln2_e"]}`; relative error below 2^{log2(d["ln2_qerr"]):.1f}.',
        f'pub(super) const LN2_Q128: (u128, i32) = (0x{d["ln2_m"]:032x}, {d["ln2_e"]});',
    ]) + '\n'
    lines = [
        '//! Constants of `log2` and `log10`, written by `generators/radix_constants.py`;',
        '//! do not edit. `docs/log2.md` gives the derivation.',
    ]
    for name, label in (('inv_ln2', '1 / ln 2'), ('inv_ln10', '1 / ln 10')):
        c = d[name]
        upper = name.upper()
        lines += [
            '',
            f'/// `{label}` as a double-word `{upper}_HI + {upper}_LO`; relative error below',
            f'/// 2^{log2(c["err"]):.1f}.',
            f'pub(super) const {upper}_HI: f64 = {f(c["hi"])};',
            f'pub(super) const {upper}_LO: f64 = {f(c["lo"])};',
            f'/// `{label}` as `m * 2^{c["e"]}`; relative error below 2^{log2(c["qerr"]):.1f}.',
            f'pub(super) const {upper}_Q128: (u128, i32) = (0x{c["m"]:032x}, {c["e"]});',
        ]
    return {EXP2: exp2, LOG2: '\n'.join(lines) + '\n'}


def main():
    files = generate()
    for path, text in files.items():
        if '--check' in sys.argv[1:]:
            if path.read_text() != text:
                sys.exit(f'{path} differs from a fresh generation')
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)


if __name__ == '__main__':
    main()
