#!/usr/bin/env python3
"""The constants of expm1 (docs/expm1.md), with their errors.

Writes crates/morphiq-numerics/src/expm1/tables.rs and formal/exp/Expm1Tables.v;
with --check, fails if a committed file differs from a fresh generation. Needs mpmath
(generators/requirements.txt). `derive()` returns the values
generators/expm1_certificates.py uses.

- c3..c9: the small-argument polynomial, read from generators/expm1_poly.out,
  which generators/expm1_poly.sollya writes.
- DEGREE: the small-argument series degree (section 4): the least d whose
  truncation, exp(A) A^(d+1)/(d+2)! over (e^x - 1)/x >= 1 - A/2,
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
TAIL_FACTOR = Fraction(26, 25)  # exp(A) < 1.04; proved in Expm1Series.v
DEGREE = next(d for d in range(1, 64)
              if TAIL_FACTOR * A ** (d + 1) / math.factorial(d + 2) / (1 - A / 2) <= Fraction(1, 2**125))


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


def coq_tables():
    """The same encodings and reciprocals, with kernel-checked bounds."""
    from exp_constants import coq_value
    d = derive()
    lines = [
        '(** Written by generators/expm1_constants.py; do not edit. *)',
        'From Coq Require Import Reals ZArith List Lia.',
        'From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.',
        'From Binary64 Require Import IEEE64 Grid Encodings.',
        'From Interval Require Import Tactic.',
        'Import ListNotations.',
        'Open Scope R_scope.',
    ]
    from expm1_reference import thresholds
    edges = thresholds()
    for name, value in [
        ('em_overflow', edges['least x overflowing']),
        ('em_minus_one_screen', edges['largest x rounding to -1']),
        ('em_minus_one', -1.0), ('em_tiny', 2.0**-54), ('em_small', 2.0**-5),
    ]:
        lines += coq_value(name, value)
    for i, c in enumerate(d['poly'], 3):
        lines += coq_value(f'em_c{i}', c)
        value = Fraction(c)
        k = value.denominator.bit_length() - 1
        lines += [f'Definition em_a{i} : R := IZR {value.numerator} * bpow radix2 (-{k}).',
                  f'Lemma em_c{i}_real : B em_c{i} = em_a{i}.',
                  f'Proof. rewrite em_c{i}_val. unfold em_a{i}. apply Rle_antisym; interval with (i_prec 120). Qed.']
    def horner(coefficients):
        acc = coefficients[-1]
        for coefficient in reversed(coefficients[:-1]):
            acc = f'({coefficient} + x * {acc})'
        return acc
    lines += [f'Definition em_w (x : R) : R := {horner([f"B em_c{i}" for i in range(3, 10)])}.']
    errors = [Fraction(1, math.factorial(i)) - (Fraction(d['poly'][i-3]) if i <= 9 else 0)
              for i in range(3, DEGREE + 2)]
    lines += [f'Definition em_poly_difference (x : R) : R := {horner([f"({v.numerator}/{v.denominator})" for v in errors])}.']
    lines += [
        'Definition em_recip_bits : list (Z * nat) := [',
        *[f'  ({m}%Z, {-e}%nat){";" if i < DEGREE - 1 else ""}'
          for i, (m, e) in enumerate(d['reciprocals'])],
        '].',
        'Definition em_recip k := nth (k - 2) em_recip_bits (0%Z, 0%nat).',
        'Definition em_recip_ok k : Prop :=',
        ' (2^127 <= fst (em_recip k) < 2^128)%Z /\\',
        ' Rabs (IZR (fst (em_recip k)) / 2^snd (em_recip k) * INR k - 1) <= /2^127.',
    ]
    for i, (m, e) in enumerate(d['reciprocals'], 2):
        lines += [
            f'Lemma em_recip_ok_{i} : em_recip_ok {i}.',
            'Proof.',
            f' unfold em_recip_ok; change (em_recip {i}) with ({m}%Z, {-e}%nat); cbn [fst snd].',
            ' split; [lia | ]. rewrite INR_IZR_INZ.',
            f' change (Z.of_nat {i}) with {i}%Z. interval with (i_prec 140).',
            'Qed.',
        ]
    lines += [
        f'Theorem em_recip_table_ok k : (2 <= k <= {DEGREE + 1})%nat -> em_recip_ok k.',
        'Proof.',
        ' intros H. destruct k as [|[|k]]; try lia.',
        *[f' destruct k as [|k]; [exact em_recip_ok_{i} | ].' for i in range(2, DEGREE + 2)],
        ' lia.',
        'Qed.',
    ]
    return '\n'.join(lines) + '\n'


def main():
    for path, data in [(OUTPUT, generate()), (ROOT / 'formal/exp/Expm1Tables.v', coq_tables())]:
        if '--check' in sys.argv[1:]:
            if path.read_text() != data:
                sys.exit(f'{path} differs from a fresh generation')
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(data)


if __name__ == '__main__':
    main()
