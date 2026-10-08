#!/usr/bin/env python3
"""The constants of exp (docs/exp.md), with their errors.

Writes crates/morphiq-numerics/src/exp/tables.rs and formal/exp/ExpTables.v;
with --check, fails if a committed file differs from a fresh generation. Needs
mpmath (generators/requirements.txt). Every value is computed from its
definition with mpmath at 600 bits and rounded once, in integer arithmetic, to
the stated format; each error is checked against the bound docs/exp.md and the
certificates rely on. ExpTables.v states the fast path's constants by their
encodings and proves each of those bounds with CoqInterval, so the proofs don't
rest on this script's arithmetic.

- INV_L = RN(128 / ln 2), and the shifter 1.5 * 2^52 (section 3, steps 1 and 2).
- L1..L4: L = ln 2 / 128 split so that n * L1 is exact for |n| < 2^18 (L1 has
  35 significant bits) and |L - (L1 + L2 + L3 + L4)| < 2^-206 (section 3, step 4).
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
COQ_OUTPUT = ROOT / 'formal/exp/ExpTables.v'
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


def decode(bits):
    """What Flocq's binary_float_of_bits_aux 52 11 returns for a finite
    encoding: None for a zero, else (sign, significand, k) with value
    ±significand * 2^-k. Every constant here has a negative exponent."""
    sign, biased, frac = bits >> 63, (bits >> 52) & 0x7ff, bits & ((1 << 52) - 1)
    assert biased != 0x7ff, 'finite'
    if biased == 0 and frac == 0:
        return None
    m, e = (frac, -1074) if biased == 0 else (frac | 1 << 52, biased - 1075)
    assert e < 0
    return sign, m, -e


def coq_value(name, x):
    """A binary64 constant by its encoding, and the lemma giving its value."""
    bits = to_bits(x)
    d = decode(bits)
    lines = [f'Definition {name} : f64 := b64_of_bits {bits}.']
    if d is None:
        lines += [f'Lemma {name}_val : B {name} = 0.',
                  f'Proof. exact (bits_zero {bits} false eq_refl). Qed.',
                  f'Lemma {name}_finite : finite {name}.',
                  f'Proof. exact (bits_finite_zero {bits} false eq_refl). Qed.']
    else:
        s, m, k = d
        value = f'(- {m})' if s else f'{m}'
        lines += [f'Lemma {name}_val : B {name} = {value} / 2 ^ {k}.',
                  f'Proof. exact (bits_val {bits} {"true" if s else "false"} {m} {k} eq_refl). Qed.',
                  f'Lemma {name}_finite : finite {name}.',
                  f'Proof. exact (bits_finite {bits} _ _ _ eq_refl). Qed.']
    return lines


def hex_rational(s):
    """A hex float literal of any length (Sollya prints the bound with more
    digits than binary64 has) as (numerator, k): value numerator * 2^-k."""
    mantissa, exponent = s[2:].split('p')
    whole, _, frac = mantissa.partition('.')
    num, k = int(whole + frac, 16), 4 * len(frac) - int(exponent)
    while num % 2 == 0 and k > 0:
        num, k = num // 2, k - 1
    assert k > 0
    return num, k


def coq_tables(l_split, poly, poly_bound, table_dw, table_q, reciprocals):
    """formal/exp/ExpTables.v: the fast path's constants and their bounds."""
    num, k = hex_rational(poly_bound)
    c = ['exp_c3', 'exp_c4', 'exp_c5', 'exp_c6']
    lines = [
        '(** Constants of [exp]\'s fast path, written by generators/exp_constants.py;',
        '    do not edit. Each is given by its binary64 encoding, as in',
        '    crates/morphiq-numerics/src/exp/tables.rs, with its value. Each bound the',
        '    certificates take about them is proved here by CoqInterval, from the',
        '    definitions of [ln] and [exp]. *)',
        '',
        'From Coq Require Import Reals ZArith List Lia.',
        'From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.',
        'From Binary64 Require Import IEEE64 Grid Encodings.',
        'From Interval Require Import Tactic.',
        'Import ListNotations.',
        '',
        'Open Scope R_scope.',
        '',
        '(** [L = ln 2 / 128 = L1 + L2 + L3 + L4 + dL] with [|dL| <= 2^-206]',
        '    (docs/exp.md, section 3; [dL] in formal/exp/reduction.g). *)',
    ]
    for i, x in enumerate(l_split, 1):
        lines += coq_value(f'exp_l{i}', x)
    lines += [
        'Theorem exp_l_split : Rabs (B exp_l1 + B exp_l2 + B exp_l3 + B exp_l4 - ln 2 / 128) <= / 2 ^ 206.',
        'Proof.',
        '  rewrite exp_l1_val, exp_l2_val, exp_l3_val, exp_l4_val.',
        '  interval with (i_prec 260).',
        'Qed.',
        '',
        '(** The polynomial\'s coefficients, and its approximation error on',
        '    [|r| <= 0.0027077] (generators/exp_poly.sollya\'s supnorm bound; [a] in',
        '    formal/exp/fast.g). *)',
    ]
    for name, x in zip(c, poly):
        lines += coq_value(name, x)
    lines += [
        f'Definition exp_poly_bound : R := {num} / 2 ^ {k}.',
        'Theorem exp_poly_approx r : Rabs r <= 0.0027077 ->',
        '  Rabs (exp r - 1 - r - r * r * (1 / 2 + r * (B exp_c3 + r * (B exp_c4 + r * (B exp_c5 + r * B exp_c6)))))',
        '  <= exp_poly_bound.',
        'Proof.',
        '  intros H. rewrite exp_c3_val, exp_c4_val, exp_c5_val, exp_c6_val. unfold exp_poly_bound.',
        '  interval with (i_taylor r, i_degree 12, i_bisect r, i_prec 120, i_depth 12).',
        'Qed.',
        '',
        '(** [T_j = 2^(j/128)] as a double-word [(hi, lo)], within [2^-107]',
        '    relatively ([d4] in formal/exp/fast.g); both words are multiples of',
        '    [2^-120], so a nonzero one is at least that in magnitude. *)',
        'Definition exp_t_bits : list (Z * Z) := [',
    ]
    pairs = [(to_bits(hi), to_bits(lo)) for hi, lo in table_dw]
    lines += [f'  ({h}%Z, {l}%Z){";" if j < 127 else ""}' for j, (h, l) in enumerate(pairs)]
    lines += [
        '].',
        'Definition exp_t_hi (j : nat) : f64 := b64_of_bits (fst (nth j exp_t_bits (0%Z, 0%Z))).',
        'Definition exp_t_lo (j : nat) : f64 := b64_of_bits (snd (nth j exp_t_bits (0%Z, 0%Z))).',
        '',
        'Definition exp_t_ok (j : nat) : Prop :=',
        '  finite (exp_t_hi j) /\\ finite (exp_t_lo j) /\\',
        '  on_grid (-120) (B (exp_t_hi j)) /\\ on_grid (-120) (B (exp_t_lo j)) /\\',
        '  Rabs (B (exp_t_hi j)) <= 2 /\\ Rabs (B (exp_t_lo j)) <= 1 /\\',
        '  Rabs ((B (exp_t_hi j) + B (exp_t_lo j) - exp (INR j * ln 2 / 128)) / exp (INR j * ln 2 / 128))',
        '    <= / 2 ^ 107.',
        '',
    ]
    for j, (h, l) in enumerate(pairs):
        dh, dl = decode(h), decode(l)
        assert dh is not None and dh[0] == 0 and dh[2] <= 120
        rw = [f'(bits_val {h} false {dh[1]} {dh[2]} eq_refl)']
        fin = [f'bits_finite {h} _ _ _ eq_refl']
        grid = ['apply (val_grid _ _ 120); lia']
        if dl is None:
            rw.append(f'(bits_zero {l} false eq_refl)')
            fin.append(f'bits_finite_zero {l} false eq_refl')
            grid.append('apply grid_0')
        else:
            assert dl[2] <= 120
            rw.append(f'(bits_val {l} {"true" if dl[0] else "false"} {dl[1]} {dl[2]} eq_refl)')
            fin.append(f'bits_finite {l} _ _ _ eq_refl')
            grid.append('apply (val_grid _ _ 120); lia')
        lines += [
            f'Lemma exp_t_ok_{j} : exp_t_ok {j}.',
            'Proof.',
            f'  unfold exp_t_ok, exp_t_hi, exp_t_lo; cbn [nth fst snd exp_t_bits].',
            f'  split; [exact ({fin[0]}) | split; [exact ({fin[1]}) | ]].',
            f'  rewrite {rw[0]}, {rw[1]}; cbn [cond_Zopp].',
            f'  split; [{grid[0]} | split; [{grid[1]} | ]].',
            '  split; [interval with (i_prec 64) | split; [interval with (i_prec 64) | ]].',
            f'  rewrite INR_IZR_INZ; change (Z.of_nat {j}) with {j}%Z.',
            '  interval with (i_prec 160).',
            'Qed.',
        ]
    lines += [
        '',
        'Theorem exp_table_ok j : (j < 128)%nat -> exp_t_ok j.',
        'Proof.',
        '  intros H.',
        *[f'  destruct j as [|j]; [exact exp_t_ok_{j} | ].' for j in range(128)],
        '  lia.',
        'Qed.',
        '',
        '(** The accurate path\'s [T_j = 2^(j/128)] as a 128-bit significand [m], value',
        '    [m·2^-127], top bit set, within [2^-127] relatively ([eT] in',
        '    formal/exp/accurate_y.g). *)',
        'Definition exp_tq_bits : list Z := [',
        *[f'  {m}%Z{";" if j < 127 else ""}' for j, m in enumerate(table_q)],
        '].',
        'Definition exp_tq (j : nat) : Z := nth j exp_tq_bits 0%Z.',
        '',
        'Definition exp_tq_ok (j : nat) : Prop :=',
        '  (2 ^ 127 <= exp_tq j < 2 ^ 128)%Z /\\',
        '  Rabs ((IZR (exp_tq j) / 2 ^ 127 - exp (INR j * ln 2 / 128)) / exp (INR j * ln 2 / 128)) <= / 2 ^ 127.',
        '',
    ]
    for j, m in enumerate(table_q):
        assert 2**127 <= m < 2**128
        lines += [
            f'Lemma exp_tq_ok_{j} : exp_tq_ok {j}.',
            'Proof.',
            '  unfold exp_tq_ok, exp_tq; cbn [nth exp_tq_bits].',
            '  split; [lia | ].',
            f'  rewrite INR_IZR_INZ; change (Z.of_nat {j}) with {j}%Z.',
            '  interval with (i_prec 200).',
            'Qed.',
        ]
    lines += [
        '',
        'Theorem exp_tq_table_ok j : (j < 128)%nat -> exp_tq_ok j.',
        'Proof.',
        '  intros H.',
        *[f'  destruct j as [|j]; [exact exp_tq_ok_{j} | ].' for j in range(128)],
        '  lia.',
        'Qed.',
        '',
        '(** [1/k], [k = 1..12], as a 128-bit significand [m] and exponent [-s]: value',
        '    [m·2^-s], top bit set, within [2^-127] relatively ([k] in',
        '    formal/exp/accurate_level_*.g). *)',
        'Definition exp_recip_bits : list (Z * nat) := [',
        *[f'  ({m}%Z, {-e}%nat){";" if i < 11 else ""}' for i, (m, e) in enumerate(reciprocals)],
        '].',
        'Definition exp_recip (k : nat) : Z * nat := nth (k - 1) exp_recip_bits (0%Z, 0%nat).',
        '',
        'Definition exp_recip_ok (k : nat) : Prop :=',
        '  (2 ^ 127 <= fst (exp_recip k) < 2 ^ 128)%Z /\\',
        '  Rabs (IZR (fst (exp_recip k)) / 2 ^ snd (exp_recip k) * INR k - 1) <= / 2 ^ 127.',
        '',
    ]
    for i, (m, e) in enumerate(reciprocals, 1):
        assert 2**127 <= m < 2**128 and e < 0
        lines += [
            f'Lemma exp_recip_ok_{i} : exp_recip_ok {i}.',
            'Proof.',
            '  unfold exp_recip_ok, exp_recip; cbn [nth exp_recip_bits fst snd Nat.sub].',
            '  split; [lia | ].',
            f'  rewrite INR_IZR_INZ; change (Z.of_nat {i}) with {i}%Z.',
            '  interval with (i_prec 200).',
            'Qed.',
        ]
    lines += [
        '',
        'Theorem exp_recip_table_ok k : (1 <= k <= 12)%nat -> exp_recip_ok k.',
        'Proof.',
        '  intros H.',
        '  destruct k as [|k]; [lia | ].',
        *[f'  destruct k as [|k]; [exact exp_recip_ok_{i} | ].' for i in range(1, 13)],
        '  lia.',
        'Qed.',
    ]
    return '\n'.join(lines) + '\n'


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
    # formal/exp/reduction.g and ExpReduction.v take |dL| <= 2^-206.
    assert residual < mpmath.mpf(2) ** -206, f'residual 2^{float(mpmath.log(residual, 2))}'
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
    # formal/exp/fast.g takes |d4| <= 2^-107.
    assert worst_dw < mpmath.mpf(2) ** -107, 'double-word table error'
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
    return {
        OUTPUT: '\n'.join(lines) + '\n',
        COQ_OUTPUT: coq_tables((l1, l2, l3, l4), poly, poly_bound, table_dw, table_q, reciprocals),
    }


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
