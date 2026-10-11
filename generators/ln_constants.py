#!/usr/bin/env python3
"""The constants of ln and ln_1p (docs/ln.md), with their errors.

Writes crates/morphiq-numerics/src/ln/tables.rs and formal/ln/LnTables.v; with
--check, fails if a committed file differs from a fresh generation. Needs mpmath
(generators/requirements.txt). Every value is computed from its definition with
mpmath at 600 bits and rounded once, in integer arithmetic; each error is
checked against the bound docs/ln.md relies on.

- R[i], i = 0..127: the reduction's reciprocals (section 3). y's significand m
  in [1 + i/128, 1 + (i+1)/128) gives y = m for i < 53 and y = m/2 for
  i >= 53, so y in [0.70703125, 1.4140625). R[i] approximates 1/y at the
  interval's centre, rounded to 10 significant bits; R[0] = R[127] = 1
  exactly, so arguments near 1 reduce with no table term. |y R[i] - 1| <= 2^-7.
- NEG_LN_R[i] = -ln R[i]: as a double-word (hi, lo) for the fast path, and as a
  signed 128-bit significand with exponent for the accurate path.
- LN2_HI, LN2_LO: ln 2 split so that E * LN2_HI is exact for |E| < 2^11
  (LN2_HI has 42 significant bits; |E| <= 1074 in section 3); and ln 2 as a
  128-bit significand. LAMBDA bounds the relative error of E ln 2 as
  E * LN2_HI + RN(E * LN2_LO) (section 4).
- The ratios of section 3: for each case of the reduction, the largest
  |E ln 2|, |-ln R[i]| and |ln(1 + z)| over |ln x|, and the least |ln x|.
  Each is enclosed in interval arithmetic (mpmath.iv, 128 bits, outward
  rounding) over every table interval, closed and widened by 2^-52 on each
  side for ln_1p's y' (section 7), and every exponent E of the case, so no
  monotonicity argument is needed. Each expression uses ln y once, so its
  enclosure is tight.
- DEGREE: the accurate path's series degree (section 6), the least d whose
  truncation |z|^d / (d + 1) is at most 2^-125, negligible next to Q128's own
  rounding (2^-127 per operation).
- RECIPROCALS[k] = 1/k, k = 1..DEGREE, as 128-bit significands with exponents.
- c3..c9: the fast path's polynomial, read from generators/ln_poly.out, which
  generators/ln_poly.sollya writes.
"""
from fractions import Fraction
import math
import pathlib
import struct
import sys

import mpmath

from exp_constants import decode

ROOT = pathlib.Path(__file__).resolve().parents[1]
OUTPUT = ROOT / 'crates/morphiq-numerics/src/ln/tables.rs'
COQ_OUTPUT = ROOT / 'formal/ln/LnTables.v'
POLY = ROOT / 'generators/ln_poly.out'
PREC = 600
Z_MAX = mpmath.mpf(2) ** -7
Z_BOUND = Fraction(78126, 10_000_000)  # |z| <= 0.0078126, Z_MAX with margin for ln_1p
DEGREE = next(d for d in range(1, 64) if Z_BOUND ** d / (d + 1) <= Fraction(1, 2**125))


def to_bits(x):
    return struct.unpack('<Q', struct.pack('<d', x))[0]


def rn_bits(v, bits):
    """v (nonzero, in binary64's normal range) rounded to nearest-even with
    `bits` significant bits, exactly, as a Python float."""
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
    """A nonzero mpf as (sign, m, e): |v| ~ m * 2^e with m's top bit set,
    rounded to nearest. Returns (sign, m, e, relative error)."""
    with mpmath.workprec(PREC):
        sign = 1 if v < 0 else 0
        a = abs(v)
        e = int(mpmath.floor(mpmath.log(a, 2))) - 127
        m = int(mpmath.nint(a / mpmath.mpf(2) ** e))
        if m >> 128:
            m, e = int(mpmath.nint(a / mpmath.mpf(2) ** (e + 1))), e + 1
        assert m >> 127 == 1, 'normalized'
        err = abs(mpmath.mpf(m) * mpmath.mpf(2) ** e - a) / a
    return sign, m, e, err


def read_poly():
    values = dict(line.split() for line in POLY.read_text().split('\n') if line.strip())
    return [float.fromhex(values[f'c{k}']) for k in range(3, 10)], values['relative_error_bound']


def ratios(r):
    """The case ratios (section 3), enclosed rigorously: returns the upper
    bounds of each |ratio| and the lower bound of |ln x|, by case."""
    iv = mpmath.iv
    iv.prec = 128
    upper = lambda x: max(abs(mpmath.mp.make_mpf(x._mpi_[0])), abs(mpmath.mp.make_mpf(x._mpi_[1])))  # noqa: E731

    def lower(x):
        a, b = mpmath.mp.make_mpf(x._mpi_[0]), mpmath.mp.make_mpf(x._mpi_[1])
        assert a > 0 or b < 0, 'ln x is bounded away from zero'
        return min(abs(a), abs(b))

    ln2 = iv.log(2)
    widen = mpmath.mpf(2) ** -52
    case_b = dict(k2=0, k3=0, lnx=mpmath.inf)
    case_c = dict(k1=0, k2=0, k3=0, lnx=mpmath.inf)
    for i in range(128):
        lo = 1 + mpmath.mpf(i) / 128
        hi = 1 + mpmath.mpf(i + 1) / 128
        if i >= 53:
            lo, hi = lo / 2, hi / 2
        ly = iv.log(iv.mpf([lo - widen, hi + widen]))
        n = -iv.log(r[i])
        if r[i] != 1:
            # Case B: E = 0. ln x = ln y; -ln R[i] / ln y, and ln(1 + z) / ln y = 1 - that.
            case_b['k2'] = max(case_b['k2'], upper(n / ly))
            case_b['k3'] = max(case_b['k3'], upper(1 - n / ly))
            case_b['lnx'] = min(case_b['lnx'], lower(ly))
        for e in range(-1074, 1025):
            if e == 0:
                continue
            # Case C: ln x = E ln 2 + ln y, and ln(1 + z) = ln y + ln R[i].
            el = e * ln2
            d = el + ly
            case_c['k1'] = max(case_c['k1'], upper(el / (el + ly)))
            case_c['k2'] = max(case_c['k2'], upper(n / d))
            case_c['k3'] = max(case_c['k3'], upper(1 - (el + n) / (el + ly)))
            case_c['lnx'] = min(case_c['lnx'], lower(d))
    return case_b, case_c


def derive():
    """Every constant and every bound the tables and certificates rely on."""
    mpmath.mp.prec = PREC
    ln2 = mpmath.log(2)

    r, neg_ln_dw, neg_ln_q = [], [], []
    worst_z, worst_dw, worst_q = 0, 0, 0
    for i in range(128):
        lo = 1 + mpmath.mpf(i) / 128
        hi = 1 + mpmath.mpf(i + 1) / 128
        if i >= 53:
            lo, hi = lo / 2, hi / 2
        ri = 1.0 if i in (0, 127) else rn_bits(2 / (lo + hi), 10)
        worst_z = max(worst_z, abs(lo * ri - 1), abs(hi * ri - 1))
        r.append(ri)
        if ri == 1.0:
            neg_ln_dw.append((0.0, 0.0))
            neg_ln_q.append((0, 0, 0))
            continue
        v = -mpmath.log(ri)
        h = rn_bits(v, 53)
        l = rn_bits(v - h, 53)
        assert h + l == h
        worst_dw = max(worst_dw, abs(v - h - l) / abs(v))
        s, m, e, err = q128(v)
        worst_q = max(worst_q, err)
        neg_ln_dw.append((h, l))
        neg_ln_q.append((s, m, e))
    assert worst_z <= Z_MAX, 'the reduced argument stays within 2^-7'
    assert worst_dw < mpmath.mpf(2) ** -106
    assert worst_q < mpmath.mpf(2) ** -127

    ln2_hi = rn_bits(ln2, 42)
    ln2_lo = rn_bits(ln2 - ln2_hi, 53)
    m_hi, _ = mpmath.mpf(ln2_hi).man_exp
    assert abs(int(m_hi)).bit_length() <= 42, 'E * LN2_HI exact for |E| < 2^11'
    ln2_err = abs(ln2 - ln2_hi - ln2_lo) / ln2
    assert ln2_err < mpmath.mpf(2) ** -94
    _, ln2_m, ln2_e, ln2_qerr = q128(ln2)
    assert ln2_qerr < mpmath.mpf(2) ** -127

    reciprocals, worst_rec = [], 0
    for k in range(1, DEGREE + 1):
        _, m, e, err = q128(mpmath.mpf(1) / k)
        worst_rec = max(worst_rec, err)
        reciprocals.append((m, e))
    assert worst_rec < mpmath.mpf(2) ** -127

    # E ln 2 = E * LN2_HI + E * LN2_LO + E (ln 2 - LN2_HI - LN2_LO); rounding
    # E * LN2_LO adds at most u |E * LN2_LO|. Relative to E ln 2:
    lam = ln2_err + mpmath.mpf(2) ** -53 * abs(mpmath.mpf(ln2_lo)) / ln2
    assert lam < mpmath.mpf(2) ** -95

    case_b, case_c = ratios(r)

    poly, poly_bound = read_poly()
    return dict(
        r=r, neg_ln_dw=neg_ln_dw, neg_ln_q=neg_ln_q, worst_z=worst_z, worst_dw=worst_dw,
        worst_q=worst_q, ln2_hi=ln2_hi, ln2_lo=ln2_lo, ln2_err=ln2_err, ln2_m=ln2_m,
        ln2_e=ln2_e, ln2_qerr=ln2_qerr, lam=lam, reciprocals=reciprocals,
        worst_rec=worst_rec, poly=poly, poly_bound=poly_bound, case_b=case_b, case_c=case_c,
    )


def generate():
    d = derive()
    r, neg_ln_dw, neg_ln_q = d['r'], d['neg_ln_dw'], d['neg_ln_q']
    worst_z, worst_dw, worst_q = d['worst_z'], d['worst_dw'], d['worst_q']
    ln2_hi, ln2_lo, ln2_err = d['ln2_hi'], d['ln2_lo'], d['ln2_err']
    ln2_m, ln2_e, ln2_qerr = d['ln2_m'], d['ln2_e'], d['ln2_qerr']
    reciprocals, worst_rec = d['reciprocals'], d['worst_rec']
    poly, poly_bound = d['poly'], d['poly_bound']

    log2 = lambda v: float(mpmath.log(v, 2))  # noqa: E731
    f = lambda x: f'f64::from_bits(0x{to_bits(x):016x})'  # noqa: E731
    lines = [
        '//! Constants of `ln` and `ln_1p`, written by `generators/ln_constants.py`; do not',
        '//! edit. Each comment states the definition and the error the generator',
        '//! checked; `docs/ln.md` gives the derivation.',
        '',
        f'/// `RN(ln 2)` to 42 bits, so `E * LN2_HI` is exact for `|E| < 2^11`; with `LN2_LO`,',
        f'/// within 2^{log2(ln2_err):.1f} relative of `ln 2`.',
        f'pub(super) const LN2_HI: f64 = {f(ln2_hi)};',
        f'pub(super) const LN2_LO: f64 = {f(ln2_lo)};',
        f'/// `ln 2` as `m * 2^{ln2_e}`; relative error below 2^{log2(ln2_qerr):.1f}.',
        f'pub(super) const LN2_Q128: u128 = 0x{ln2_m:032x};',
        f'/// The reduction\'s reciprocals, as binary64 encodings: `|y R[i] - 1| <= 2^{log2(worst_z):.1f}`.',
        'pub(super) const R_BITS: [u64; 128] = [',
        *[f'    0x{to_bits(v):016x},' for v in r],
        '];',
        f'/// `-ln R[i]` as a double-word `(hi, lo)`, as encodings; relative error below',
        f'/// 2^{log2(worst_dw):.1f}. Zero where `R[i] = 1`.',
        'pub(super) const NEG_LN_R_BITS: [(u64, u64); 128] = [',
        *[f'    (0x{to_bits(h):016x}, 0x{to_bits(l):016x}),' for h, l in neg_ln_dw],
        '];',
        f'/// `-ln R[i]` as `(negative, m, e)` with value `(-1)^negative * m * 2^e`;',
        f'/// relative error below 2^{log2(worst_q):.1f}. `m = 0` where `R[i] = 1`.',
        'pub(super) const NEG_LN_R_Q128: [(bool, u128, i32); 128] = [',
        *[f'    ({"true" if s else "false"}, 0x{m:032x}, {e}),' for s, m, e in neg_ln_q],
        '];',
        f'/// `1/k`, `k = 1..={DEGREE}`, as `(m, e)` with value `m * 2^e`; relative error below',
        f'/// 2^{log2(worst_rec):.1f}.',
        f'pub(super) const RECIPROCALS: [(u128, i32); {DEGREE}] = [',
        *[f'    (0x{m:032x}, {e}),' for m, e in reciprocals],
        '];',
        '/// The fast path\'s cubic tail (`generators/ln_poly.sollya`): `c3..c9` with',
        f'/// relative error at most {poly_bound} to `ln(1 + z) - z + z^2/2` on `|z| <= 0.0078126`.',
        'pub(super) const POLY: [f64; 7] = [',
        *[f'    {f(c)},' for c in poly],
        '];',
    ]
    return {OUTPUT: '\n'.join(lines) + '\n', COQ_OUTPUT: coq_tables(r)}


def coq_tables(r):
    """formal/ln/LnTables.v: the reduction's reciprocals and what the proofs
    take about them, each entry proved from its encoding."""
    lines = [
        '(** Constants of [ln]\'s reduction, written by generators/ln_constants.py; do',
        '    not edit. Each is given by its binary64 encoding, as in',
        '    crates/morphiq-numerics/src/ln/tables.rs, with what the proofs take about',
        '    it (docs/ln.md, section 3). *)',
        '',
        'From Coq Require Import Reals ZArith List Lia Lra.',
        'From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.',
        'From Binary64 Require Import IEEE64 Grid Encodings.',
        'Import ListNotations.',
        '',
        'Open Scope R_scope.',
        '',
        '(** Table interval [i]: the significand [m] in [[1 + i/128, 1 + (i+1)/128)],',
        '    and [y = m] for [i < 53], [y = m/2] otherwise. *)',
        'Definition ln_lo (i : nat) : R := if (i <? 53)%nat then 1 + INR i / 128 else (1 + INR i / 128) / 2.',
        'Definition ln_hi (i : nat) : R := if (i <? 53)%nat then 1 + INR (S i) / 128 else (1 + INR (S i) / 128) / 2.',
        '',
        '(** [R[i]], the reduction\'s reciprocals, by their encodings. *)',
        'Definition ln_r_bits : list Z := [',
        *[f'  {to_bits(v)}%Z{";" if i < 127 else ""}' for i, v in enumerate(r)],
        '].',
        'Definition ln_r (i : nat) : f64 := b64_of_bits (nth i ln_r_bits 0%Z).',
        '',
        '(** Each [R[i]] is a binary64 number on [2^-10]\'s grid between [1/2] and [2],',
        '    and [|y·R[i] - 1| <= 2^-7] over its interval: [y·R[i]] is increasing in',
        '    [y], so the endpoints decide it. *)',
        'Definition ln_r_ok (i : nat) : Prop :=',
        '  finite (ln_r i) /\\ on_grid (-10) (B (ln_r i)) /\\ / 2 <= B (ln_r i) <= 2 /\\',
        '  1 - / 128 <= ln_lo i * B (ln_r i) /\\ ln_hi i * B (ln_r i) <= 1 + / 128.',
        '',
    ]
    for i, v in enumerate(r):
        bits = to_bits(v)
        s, m, k = decode(bits)
        assert s == 0
        n = Fraction(m, 2 ** k) * 1024
        assert n.denominator == 1, 'on 2^-10\'s grid'
        lines += [
            f'Lemma ln_r_ok_{i} : ln_r_ok {i}.',
            'Proof.',
            f'  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r {i}) with (b64_of_bits {bits}).',
            f'  split; [exact (bits_finite {bits} _ _ _ eq_refl) | ].',
            f'  rewrite (bits_val {bits} false {m} {k} eq_refl). cbn [SpecFloat.cond_Zopp].',
            f'  replace (2 ^ {k}) with {2 ** k} by ring.',
            f'  replace (INR {i}) with {i} by (rewrite INR_IZR_INZ; reflexivity).',
            f'  replace (INR (S {i})) with {i + 1} by (rewrite INR_IZR_INZ; reflexivity).',
            '  cbv [Nat.ltb Nat.leb].',
            f'  split; [exists {n.numerator}%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].',
            '  repeat split; lra.',
            'Qed.',
        ]
    lines += [
        '',
        'Theorem ln_r_table_ok i : (i < 128)%nat -> ln_r_ok i.',
        'Proof.',
        '  intros H.',
        *[f'  destruct i as [|i]; [exact ln_r_ok_{i} | ].' for i in range(128)],
        '  lia.',
        'Qed.',
        '',
        '(** [R[0] = R[127] = 1]: arguments near 1 reduce with no table term. *)',
        'Lemma ln_r_ends : B (ln_r 0) = 1 /\\ B (ln_r 127) = 1.',
        'Proof.',
        '  split.',
    ]
    for i in (0, 127):
        bits = to_bits(r[i])
        _, m, k = decode(bits)
        assert r[i] == 1.0
        lines += [
            f'  - change (ln_r {i}) with (b64_of_bits {bits}).',
            f'    rewrite (bits_val {bits} false {m} {k} eq_refl). cbn [SpecFloat.cond_Zopp].',
            f'    replace (2 ^ {k}) with {2 ** k} by ring. lra.',
        ]
    lines += ['Qed.']
    return '\n'.join(lines) + '\n'


def main():
    check = '--check' in sys.argv[1:]
    for path, text in generate().items():
        if check:
            if path.read_text() != text:
                sys.exit(f'{path} differs from a fresh generation')
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)


if __name__ == '__main__':
    main()
