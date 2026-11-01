#!/usr/bin/env python3
"""Generate the bounded normal CDF's body polynomial and tail rational.

The body approximates erf(y)/y as a polynomial of degree 8 in s = y^2 on
0 <= y <= BODY; the tail approximates erfcx(y) as N(y)/D(y), N of degree 8 and
D of degree 9 with D(0) = 1 (degrees matching erfcx's 1/y decay), on BODY <= y <= ANCHOR. Both are relative-error
minimax fits by the Remez exchange at 200 bits (mpmath), rounded to binary64.
ANCHOR = 91/16 is the erfcx Taylor centre 126 (ErfcxAccurateCenterModel), the
first at or above RN(8 * INV_SQRT2_HIGH): Coq anchors the tail's error bound
there. The rounded words' observed relative errors are reported; the proved
bounds come from formal/fast (FastCdf*.v), not from this fit.

Writes crates/morphiq-numerics/src/fast/cdf_tables.rs, formal/fast/FastCdfConstants.v,
formal/fast/FastCdfResidual.v (the tail residual's piecewise enclosures) and the
Gappa certificates formal/normal/fast_cdf_body.g and fast_cdf_tail.g. mpmath 1.4.1 (generators/requirements.txt).
Usage: fast_cdf_constants.py [--check]
"""
from fractions import Fraction
from pathlib import Path
import struct
import sys

import mpmath as mp

ROOT = Path(__file__).resolve().parents[1]
RUST = ROOT / 'crates/morphiq-numerics/src/fast/cdf_tables.rs'
COQ = ROOT / 'formal/fast/FastCdfConstants.v'
mp.mp.prec = 200
BODY = mp.mpf('0.46875')
ANCHOR = mp.mpf(91) / 16
BODY_DEGREE = 8
TAIL_NUM, TAIL_DEN = 8, 9


def erfcx(y):
    return mp.exp(y * y) * mp.erfc(y)


def erf_ratio(s):
    if s == 0:
        return 2 / mp.sqrt(mp.pi)
    y = mp.sqrt(s)
    return mp.erf(y) / y


def remez(f, n, m, lo, hi, grid=4000, rounds=60):
    """Relative minimax p/q (q[0] = 1) of degrees n, m for f on [lo, hi]."""
    count = n + m + 2
    xs = [(lo + hi) / 2 + (hi - lo) / 2 * mp.cos(mp.pi * (count - 1 - i) / (count - 1))
          for i in range(count)]
    q = [mp.mpf(1)] + [mp.mpf(0)] * m
    for _ in range(rounds):
        level = mp.mpf(0)
        for _ in range(40):
            a = mp.matrix(count, count)
            b = mp.matrix(count, 1)
            for i, x in enumerate(xs):
                fx = f(x)
                qold = mp.polyval(q[::-1], x)
                for j in range(n + 1):
                    a[i, j] = x ** j
                for k in range(1, m + 1):
                    a[i, n + k] = -fx * x ** k
                a[i, n + m + 1] = -(-1) ** i * fx * qold
                b[i] = fx
            s = mp.lu_solve(a, b)
            p = [s[j] for j in range(n + 1)]
            q_new = [mp.mpf(1)] + [s[n + k] for k in range(1, m + 1)]
            new_level = s[n + m + 1]
            q = q_new
            if abs(new_level - level) <= abs(new_level) * mp.mpf(2) ** -120:
                break
            level = new_level
        points = [lo + (hi - lo) * mp.mpf(i) / grid for i in range(grid + 1)]
        error = [mp.polyval(p[::-1], x) / mp.polyval(q[::-1], x) / f(x) - 1 for x in points]
        turns = [0] + [i for i in range(1, grid)
                       if (error[i] - error[i - 1]) * (error[i + 1] - error[i]) <= 0] + [grid]
        chosen = []
        for i in turns:
            if chosen and mp.sign(error[i]) == mp.sign(error[chosen[-1]]):
                if abs(error[i]) > abs(error[chosen[-1]]):
                    chosen[-1] = i
            else:
                chosen.append(i)
        while len(chosen) > count:
            chosen.pop(0 if abs(error[chosen[0]]) < abs(error[chosen[-1]]) else -1)
        worst = max(abs(e) for e in error)
        if len(chosen) < count:
            break
        xs = [points[i] for i in chosen]
        if worst - abs(level) <= worst * mp.mpf(2) ** -20:
            break
    return p, q


def word(x):
    return struct.unpack('>Q', struct.pack('>d', float(x)))[0]


def observed(f, p, q, lo, hi, grid=20000):
    pf = [mp.mpf(float(c)) for c in p]
    qf = [mp.mpf(float(c)) for c in q]
    return max(abs(mp.polyval(pf[::-1], x) / mp.polyval(qf[::-1], x) / f(x) - 1)
               for x in [lo + (hi - lo) * mp.mpf(i) / grid for i in range(grid + 1)])


def fraction(x):
    return Fraction(float(x))


RESIDUAL_BOUND = Fraction(1, 2 ** 53)
YMAX = 8 * struct.unpack('>d', struct.pack('>Q', 0x3fe6a09e667f3bcd))[0]


def coq_constant(name, value):
    """A binary64 coefficient: its encoding, rational value, Float2 form and finiteness."""
    bits = word(value)
    if value == 0:
        raise ValueError(name)
    negative = value < 0
    mantissa = (bits & ((1 << 52) - 1)) | (1 << 52)
    shift = 1075 - ((bits >> 52) & 2047)
    while mantissa % 2 == 0:
        mantissa //= 2
        shift -= 1
    signed = -mantissa if negative else mantissa
    numerator = f'(- {mantissa})' if negative else str(mantissa)
    value_form = f'{numerator} / 2 ^ {shift}' if shift > 0 else f'{signed * 2 ** (-shift)}'
    sign = 'true' if negative else 'false'
    full = (bits & ((1 << 52) - 1)) | (1 << 52)
    full_shift = 1075 - ((bits >> 52) & 2047)
    full_num = f'(- {full})' if negative else str(full)
    return (f'Definition {name} : f64 := b64_of_bits {bits}.\n'
            f'Lemma {name}_val : B {name} = {full_num} / 2 ^ {full_shift}.\n'
            f'Proof. exact (bits_val {bits} {sign} {full} {full_shift} eq_refl). Qed.\n'
            f'Lemma {name}_finite : finite {name}.\n'
            f'Proof. exact (bits_finite {bits} _ _ _ eq_refl). Qed.\n'
            f'Lemma {name}_g : B {name} = float2R (Float2 ({signed}) ({-shift})).\n'
            f'Proof. apply word_value_ok; vm_compute; reflexivity. Qed.\n')


def real_poly(names, var):
    terms = []
    for k, name in enumerate(names):
        terms.append(f'B {name}' + (f' * {var}' + f' ^ {k}' if k > 1 else f' * {var}' if k == 1 else ''))
    return ' + '.join(terms)


def real_dpoly(names, var):
    terms = []
    for k, name in enumerate(names):
        if k == 0:
            continue
        terms.append(f'{k} * B {name}' + (f' * {var} ^ {k - 1}' if k > 2 else f' * {var}' if k == 2 else ''))
    return ' + '.join(terms)


def residual_pieces(num, den):
    """Partition [BODY, ANCHOR] so that each piece's |Q| <= K and D >= d give K/d^2 <= 2^-53."""
    numf = [mp.mpf(float(c)) for c in num]
    denf = [mp.mpf(float(c)) for c in den]
    P = lambda c, t: mp.polyval(c[::-1], t)
    dP = lambda c, t: mp.polyval([k * c[k] for k in range(1, len(c))][::-1], t)
    k = 2 / mp.sqrt(mp.pi)
    Q = lambda t: dP(numf, t) * P(denf, t) - P(numf, t) * dP(denf, t) - 2 * t * P(numf, t) * P(denf, t) + k * P(denf, t) ** 2
    def bound(x):
        # x > 0 to three significant bits, rounded up
        e = int(mp.floor(mp.log(x, 2))) - 2
        m = int(mp.ceil(x / mp.mpf(2) ** e))
        return Fraction(m) * Fraction(2) ** e
    pieces = []
    stack = [(Fraction(15, 32), Fraction(91, 16))]
    while stack:
        a, b = stack.pop()
        ts = [mp.mpf(a.numerator) / a.denominator + (mp.mpf(b.numerator) / b.denominator - mp.mpf(a.numerator) / a.denominator) * i / 200 for i in range(201)]
        qmax = max(abs(Q(t)) for t in ts)
        K = bound(qmax * mp.mpf('1.25'))
        dmin = P(denf, mp.mpf(a.numerator) / a.denominator)
        d = Fraction(int(mp.floor(dmin * (1 - mp.mpf('1e-6')) * 2 ** 20)), 2 ** 20)
        if K <= RESIDUAL_BOUND * d * d:
            pieces.append((a, b, K, d))
        else:
            mid = (a + b) / 2
            stack += [(mid, b), (a, mid)]
    return sorted(pieces)


def q(x):
    return f'({x.numerator}/{x.denominator})'


def certificate_body(body):
    lines = ['# Generated by generators/fast_cdf_constants.py; bounded normal CDF body.',
             '@rnd = float<ieee_64, ne>;']
    lines += [f'c{i} = {float(c).hex()};' for i, c in enumerate(body)]
    lines += ['y = rnd(yy);', 's = rnd(y*y);', 's2 = rnd(s*s);', 's4 = rnd(s2*s2);',
              'S = y*y;', 'S2 = S*S;', 'S4 = S2*S2;']
    for i in range(0, 8, 2):
        lines += [f'a{i // 2} = rnd(c{i} + rnd(s*c{i + 1}));', f'A{i // 2} = c{i} + S*c{i + 1};']
    lines += ['b0 = rnd(a0 + rnd(s2*a1));', 'B0 = A0 + S2*A1;',
              'b1 = rnd(a2 + rnd(s2*a3));', 'B1 = A2 + S2*A3;',
              'p = rnd(rnd(b0 + rnd(s4*b1)) + rnd(rnd(s4*s4)*c8));', 'P = (B0 + S4*B1) + S4*S4*c8;',
              'v = rnd(0x1p-1 + rnd(0x1p-1*rnd(y*p)));', 'V = 0x1p-1 + 0x1p-1*(y*P);',
              '{ yy in [-0x1.ep-2, 0x1.ep-2] -> v - V in [-0x1p-52, 0x1p-52] /\\ v in [0x1.dp-3, 0x1.9p-1] }']
    return '\n'.join(lines) + '\n'


def certificate_tail(num, den):
    lines = ['# Generated by generators/fast_cdf_constants.py; bounded normal CDF tail rational.',
             '@rnd = float<ieee_64, ne>;']
    lines += [f'n{i} = {float(c).hex()};' for i, c in enumerate(num)]
    lines += [f'd{i} = {float(c).hex()};' for i, c in enumerate(den)]
    lines += ['y = rnd(yy);', 'y2 = rnd(y*y);', 'y4 = rnd(y2*y2);', 'y8 = rnd(y4*y4);',
              'Y2 = y*y;', 'Y4 = Y2*Y2;', 'Y8 = Y4*Y4;']
    for p, cs in (('n', num), ('d', den)):
        for i in range(0, len(cs) - 1, 2):
            lines += [f'{p}a{i // 2} = rnd({p}{i} + rnd(y*{p}{i + 1}));', f'{p}A{i // 2} = {p}{i} + y*{p}{i + 1};']
    lines += ['nb0 = rnd(na0 + rnd(y2*na1));', 'NB0 = nA0 + Y2*nA1;',
              'nb1 = rnd(na2 + rnd(y2*na3));', 'NB1 = nA2 + Y2*nA3;',
              'nc = rnd(nb0 + rnd(y4*nb1));', 'NC = NB0 + Y4*NB1;',
              'nh = rnd(nc + rnd(y8*n8));', 'NE = NC + Y8*n8;',
              'db0 = rnd(da0 + rnd(y2*da1));', 'DB0 = dA0 + Y2*dA1;',
              'db1 = rnd(da2 + rnd(y2*da3));', 'DB1 = dA2 + Y2*dA3;',
              'dc = rnd(db0 + rnd(y4*db1));', 'DC = DB0 + Y4*DB1;',
              'dh = rnd(dc + rnd(y8*da4));', 'DE = DC + Y8*dA4;',
              'r = rnd(nh/dh);', 'R = NE/DE;',
              '{ yy in [0x1.ep-2, %s] -> r -/ R in [-0x1.6p-49, 0x1.6p-49] }' % YMAX.hex()]
    return '\n'.join(lines) + '\n'


def outputs():
    body, _ = remez(erf_ratio, BODY_DEGREE, 0, mp.mpf(0), BODY * BODY)
    tail_n, tail_d = remez(erfcx, TAIL_NUM, TAIL_DEN, BODY, ANCHOR)
    body = [mp.mpf(float(c)) for c in body]
    tail_n = [mp.mpf(float(c)) for c in tail_n]
    tail_d = [mp.mpf(float(c)) for c in tail_d]
    body_error = observed(erf_ratio, body, [1], mp.mpf(0), BODY * BODY)
    tail_error = observed(erfcx, tail_n, tail_d, BODY, ANCHOR)
    groups = [('BODY', body), ('TAIL_N', tail_n), ('TAIL_D', tail_d)]
    rust = ['//! Generated by generators/fast_cdf_constants.py; do not edit.',
            "//! The bounded normal CDF's body polynomial (erf(y)/y in s = y^2) and",
            '//! tail rational (erfcx(y) = N(y)/D(y)), in ascending powers.',
            f'//! Observed relative errors of the rounded words: body 2^{float(mp.log(body_error, 2)):.2f},',
            f'//! tail 2^{float(mp.log(tail_error, 2)):.2f}; formal/fast/FastCdf*.v proves the bounds.',
            '']
    for name, coefficients in groups:
        rust.append(f'pub(super) const {name}: [f64; {len(coefficients)}] = [')
        rust += [f'    f64::from_bits(0x{word(c):016x}),' for c in coefficients]
        rust.append('];')
    rust.append('')
    names = {'BODY': [f'cdf_body_{k}' for k in range(len(body))],
             'TAIL_N': [f'cdf_num_{k}' for k in range(len(tail_n))],
             'TAIL_D': [f'cdf_den_{k}' for k in range(len(tail_d))]}
    coq = ['(** Generated by generators/fast_cdf_constants.py; do not edit.',
           "    The bounded normal CDF's coefficients, in ascending powers. *)",
           'From Coq Require Import Reals ZArith Lia Lra.',
           'From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.',
           'From Binary64 Require Import IEEE64 Encodings.',
           'From Gappa Require Import Gappa_library.',
           'Require Import ErfcxTableCertificateModel.',
           'Open Scope R_scope.', '']
    for name, coefficients in groups:
        for coq_name, c in zip(names[name], coefficients):
            coq.append(coq_constant(coq_name, float(c)))
    coq += [f'Definition cdf_tail_num t := {real_poly(names["TAIL_N"], "t")}.',
            f'Definition cdf_tail_den t := {real_poly(names["TAIL_D"], "t")}.',
            f'Definition cdf_tail_dnum t := {real_dpoly(names["TAIL_N"], "t")}.',
            f'Definition cdf_tail_dden t := {real_dpoly(names["TAIL_D"], "t")}.',
            f'Definition cdf_body_poly s := {real_poly(names["BODY"], "s")}.',
            '(** All tail coefficients, as rationals, for interval enclosures. *)',
            'Ltac cdf_values := rewrite ?' + ', ?'.join(f'{n}_val' for n in names['TAIL_N'] + names['TAIL_D'] + names['BODY']) + '.',
            '']
    pieces = residual_pieces(tail_n, tail_d)
    tail = ['(** Generated by generators/fast_cdf_constants.py; do not edit.',
            '    The tail residual Q = N\'D - ND\' - 2tND + (2/sqrt pi) D^2, bounded piecewise:',
            f'    on each of {len(pieces)} pieces |Q| <= K and D >= d with K <= 2^-53 d^2. *)',
            'From Coq Require Import Reals Lra.',
            'From Interval Require Import Tactic.',
            'From Binary64 Require Import IEEE64.',
            'Require Import ErfcxConstants FastCdfConstants.',
            'Open Scope R_scope.',
            'Definition cdf_tail_residual t := cdf_tail_dnum t * cdf_tail_den t - cdf_tail_num t * cdf_tail_dden t',
            '  - 2 * t * cdf_tail_num t * cdf_tail_den t + 2 * inv_sqrt_pi * cdf_tail_den t ^ 2.', '']
    for index, (a, b, K, d) in enumerate(pieces):
        tail += [f'Lemma cdf_residual_piece_{index:02d} t : {q(a)} <= t <= {q(b)} ->',
                 f'  Rabs (cdf_tail_residual t) <= {q(K)} /\\ {q(d)} <= cdf_tail_den t.',
                 'Proof.',
                 '  intros T. unfold cdf_tail_residual, cdf_tail_num, cdf_tail_den, cdf_tail_dnum, cdf_tail_dden, inv_sqrt_pi.',
                 '  cdf_values. split; interval with (i_bisect t, i_taylor t, i_degree 22, i_prec 160, i_depth 6).',
                 'Qed.']
    tail += ['Theorem cdf_residual_bound t : 15/32 <= t <= 91/16 ->',
             '  Rabs (cdf_tail_residual t) <= / 2 ^ 53 * cdf_tail_den t ^ 2 /\\ 1 <= cdf_tail_den t.',
             'Proof.', '  intros T.']
    for index, (a, b, K, d) in enumerate(pieces):
        closing = '' if index == len(pieces) - 1 else f'  destruct (Rle_dec t {q(b)}) as [P{index} | P{index}].\n  {{'
        if index < len(pieces) - 1:
            tail.append(closing)
        tail.append(f'    destruct (cdf_residual_piece_{index:02d} t ltac:(lra)) as [Kq Dd].')
        tail.append(f'    assert (D2 : {q(d)} ^ 2 <= cdf_tail_den t ^ 2) by (apply pow_incr; lra).')
        tail.append('    split; [ | lra]. eapply Rle_trans; [exact Kq | ].')
        tail.append(f'    apply Rle_trans with (/ 2 ^ 53 * {q(d)} ^ 2); [lra | apply Rmult_le_compat_l; [lra | exact D2]].')
        if index < len(pieces) - 1:
            tail.append('  }')
    tail += ['Qed.', '']
    return {RUST: '\n'.join(rust),
            COQ: '\n'.join(coq),
            ROOT / 'formal/fast/FastCdfResidual.v': '\n'.join(tail),
            ROOT / 'formal/normal/fast_cdf_body.g': certificate_body(body),
            ROOT / 'formal/normal/fast_cdf_tail.g': certificate_tail(tail_n, tail_d)}


def main():
    generated = outputs()
    if '--check' in sys.argv:
        for path, text in generated.items():
            if not path.exists() or path.read_text() != text:
                raise SystemExit(f'generated file differs: {path.relative_to(ROOT)}')
        return
    for path, text in generated.items():
        path.write_text(text)


if __name__ == '__main__':
    main()
