#!/usr/bin/env python3
"""Writes formal/asin/AsinApprox.v: for each of asin's 45 table segments, the
Coq theorem that the segment's polynomial, at the table's own words, is within
the budget of compose_<kk>.g of `asin (k/64 + t)` on |t| <= 0.0078126
(docs/asin.md, section 4).

The theorem is proved by `sin` monotonicity, not by trusting Sollya: with S the
polynomial and E its budget, `sin (S - E) <= k/64 + t <= sin (S + E)` for every
t, which Coq's `interval` (bisection and Taylor models in t) establishes, and
`asin_within` turns that into `|asin (k/64 + t) - S| <= E`.

The budget is the compose certificate's: Sollya's supnorm plus the Taylor
remainder for the polynomial, and the tables' double-word relative error for
asin(a) and c1 (generators/asin_certificates.py).

With --check, fails if the committed file differs from a fresh generation.
Needs mpmath (generators/requirements.txt).
"""
from fractions import Fraction
import math
import pathlib
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import asin_certificates as certs  # noqa: E402
import asin_constants  # noqa: E402

OUT = certs.DIR / 'AsinApprox.v'


def budget(k, row, values):
    """The segment's absolute budget E: polynomial + asin(a) + c1 t, each as in
    compose_<kk>.g, rounded up to a 24-bit mantissa."""
    a = certs.mpmath.mpf(k) / 64
    asin_a = certs.frac(certs.mpmath.asin(a))
    c1 = certs.frac(1 / certs.mpmath.sqrt(1 - a * a))
    e_poly = certs.T * certs.T * (certs.hex_fraction(values[f'u{k:02d}0']) + certs.hex_fraction(values[f'r{k:02d}0']))
    e = e_poly + certs.DW_ACC * asin_a + certs.DW_ACC * c1 * certs.T
    shift = 24 - math.floor(math.log2(e)) - 1
    n = math.ceil(e * 2 ** shift)
    return Fraction(n, 2 ** shift), n, shift


def word(x):
    """`IZR M * bpow radix2 E` for a binary64 table value."""
    bits, sign, m, k, M, d, E = certs.word_data(x)
    return f'IZR ({M}) * bpow radix2 ({E})'


def lemma(k, row, values):
    e, n, shift = budget(k, row, values)
    names = ['r0', 'r1', 'rH', 'rL'] + [f'q{j}' for j in range(9)]
    hyps = ' -> '.join(f'{nm} = {word(w)}' for nm, w in zip(names, row))
    poly = '[' + '; '.join(f'q{j}' for j in range(9)) + ']'
    ev = f'(IZR {n} * bpow radix2 (-{shift}))'
    kk = f'{k:02d}'
    return f"""Lemma approx_{kk} ({' '.join(names)} t : R) :
  {hyps} -> Rabs t <= 0.0078126 ->
  Rabs (asin (IZR {k} / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl {poly} t))) <= {ev}.
Proof.
  intros {' '.join(f'H{j}' for j in range(13))} Ht.
  subst {' '.join(names)}. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply asin_within; [ interval | | | | ].
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.
"""


HEADER = """(** The table segments of asin approximate [asin]: for [k = 1..45], with the
    segment's words, [|asin (k/64 + t) - (c0 + c1 + (cH + cL) t + t^2 G(t))|] is
    within the budget of [compose_<kk>.g] for every [|t| <= 0.0078126]. Written by
    generators/asin_approx.py; do not edit.

    Each is proved by [sin] monotonicity ([asin_within]), the bounds on [sin] at
    the polynomial's two ends by [interval]; Sollya's report is not an input. *)
From Coq Require Import Reals ZArith Lra Psatz List.
From Flocq Require Import Core.
From Interval Require Import Tactic.
Require Import Ln1pLemmas AsinSegment AsinSeriesSmall AsinWithin.
Import ListNotations.
Open Scope R_scope.

(** The series branch: [asin z] is [z + z^3 P(z^2)], [P]'s coefficients the table
    POLY0's, to [3/16 2^-54 z^3] on [[2^-28, 0.0078126]] (the relative accuracy of
    Sollya's fit and the series' truncation, which [series_compose.g] budgets as
    [2^-54 (1 + 2^-23)] of [asin z - z >= z^3/6]). *)
Lemma approx_series z : / 2 ^ 28 <= z <= 0.0078126 ->
  Rabs (asin z - (z + z * z * z * (q0r + z * z * (q1r + z * z * (q2r + z * z * q3r)))))
    <= 3 / 16 / 2 ^ 54 * (z * z * z).
Proof.
  intros Hz. unfold q0r, q1r, q2r, q3r. bpow_num.
  apply asin_within; [ interval | | | | ].
  all: interval with (i_bisect z, i_taylor z, i_prec 240, i_degree 14, i_depth 60).
Qed.
"""


def generate():
    d = asin_constants.derive()
    out = [HEADER]
    for k in range(1, asin_constants.SEGMENTS + 1):
        out.append(lemma(k, d['rows'][k - 1], d['values']))
    return '\n'.join(out)


def main():
    text = generate()
    if '--check' in sys.argv[1:]:
        if OUT.read_text() != text:
            sys.exit(f'{OUT} differs from a fresh generation')
        return
    OUT.write_text(text)
    print(f'{OUT.name}: {asin_constants.SEGMENTS} segment theorems')


if __name__ == '__main__':
    main()
