#!/usr/bin/env python3
"""Writes the Coq facts about atan2's table that the proofs in formal/atan2 take
as input: Atan2Approx.v (each of the 64 segments' polynomials approximates
`atan (k/64 + t)` within the compose certificate's budget, by `interval`) and
Atan2Segments.v (each segment's evaluation certificate over its table words and
the facts `SegOkRow` states).

With --check, fails if a committed file differs from a fresh generation. Needs
mpmath (generators/requirements.txt).
"""
from fractions import Fraction
import math
import pathlib
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import asin_certificates as ac  # noqa: E402
import atan2_certificates as a2c  # noqa: E402
import atan2_constants  # noqa: E402

mpmath = ac.mpmath
DIR = a2c.DIR
T, U, DW_ACC = ac.T, ac.U, ac.DW_ACC
FAST = a2c.FAST
# The per-segment relative budget of the fast value against atan(a + s).
REL = Fraction(1, 2**63)
SEGMENTS = atan2_constants.SEGMENTS


def approx_budget(k, values):
    """Segment k's absolute approximation budget (docs/atan2.md, section 4):
    Sollya's supnorm plus the Taylor remainder for the polynomial, and the
    tables' double-word error for atan(a) and c1, as compose_<kk>.g takes them,
    rounded up to a 24-bit mantissa. Returns (E, n, shift), E = n 2^-shift."""
    a = mpmath.mpf(k) / 64
    atan_a = ac.frac(mpmath.atan(a))
    c1 = ac.frac(1 / (1 + a * a))
    e_poly = T * T * (ac.hex_fraction(values[f'u{k:02d}0']) + ac.hex_fraction(values[f'r{k:02d}0']))
    e = e_poly + DW_ACC * atan_a + DW_ACC * c1 * T
    shift = 24 - math.floor(math.log2(e)) - 1
    n = math.ceil(e * 2 ** shift)
    return Fraction(n, 2 ** shift), n, shift


def amin(k):
    """A rational lower bound of atan(k/64 - T), to 20 bits, with its (n, shift)."""
    mpmath.mp.prec = 300
    v = mpmath.atan(mpmath.mpf(k) / 64 - mpmath.mpf(78126) / 10**7)
    shift = 20 - math.floor(math.log2(float(v))) - 1
    n = math.floor(v * 2 ** shift) - 1
    return n, shift


def word_data(x):
    """ac.word_data, with the one zero word (k = 64's c1.lo) as M = 0, E = 0."""
    if atan2_constants.to_bits(x) == 0:
        return 0, False, None, None, 0, 0, 0
    return ac.word_data(x)


def word(x):
    if atan2_constants.to_bits(x) == 0:
        return '0'
    bits, sign, m, k, M, d, E = word_data(x)
    return f'IZR ({M}) * bpow radix2 ({E})'


def lemma(k, row, values):
    e, n, shift = approx_budget(k, values)
    names = ['r0', 'r1', 'rH', 'rL'] + [f'q{j}' for j in range(9)]
    hyps = ' -> '.join(f'{nm} = {word(w)}' for nm, w in zip(names, row))
    poly = '[' + '; '.join(f'q{j}' for j in range(9)) + ']'
    ev = f'(IZR {n} * bpow radix2 (-{shift}))'
    kk = f'{k:02d}'
    return f"""Lemma approx_{kk} ({' '.join(names)} t : R) :
  {hyps} -> Rabs t <= 0.0078126 ->
  Rabs (atan (IZR {k} / 64 + t) - (r0 + r1 + ((rH + rL) * t + t * t * pl {poly} t))) <= {ev}.
Proof.
  intros {' '.join(f'H{j}' for j in range(13))} Ht.
  subst {' '.join(names)}. bpow_num. cbn [pl]. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rabs_le. split.
  all: interval with (i_bisect t, i_taylor t, i_prec 140, i_degree 20, i_depth 40).
Qed.

Lemma amin_{kk}_num : IZR {amin(k)[0]} * bpow radix2 (-{amin(k)[1]}) <= atan (IZR {k} / 64 - 0.0078126).
Proof. bpow_num. interval with (i_prec 100). Qed.

Lemma amin_{kk} t : Rabs t <= 0.0078126 -> IZR {amin(k)[0]} * bpow radix2 (-{amin(k)[1]}) <= atan (IZR {k} / 64 + t).
Proof.
  intros Ht. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  apply Rle_trans with (1 := amin_{kk}_num). apply atan_le. lra.
Qed.
"""


HEADER = """(** The table segments of atan2 approximate [atan]: for [k = 1..64], with the
    segment's words, [|atan (k/64 + t) - (c0 + c1 + (cH + cL) t + t^2 G(t))|] is
    within the budget of [compose_<kk>.g] for every [|t| <= 0.0078126], and
    [atan (k/64 + t)] stays above [amin_<kk>]. Written by generators/atan2_proofs.py;
    do not edit. Each is proved by [interval] (bisection and Taylor models in
    [t]); Sollya's report is not an input. *)
From Coq Require Import Reals ZArith Lra Psatz List.
From Flocq Require Import Core.
From Interval Require Import Tactic.
Require Import Ln1pLemmas AsinSegment AsinSeriesSmall.
Import ListNotations.
Open Scope R_scope.

Lemma atan_le x y : x <= y -> atan x <= atan y.
Proof.
  intros H. destruct (Rle_lt_or_eq_dec x y H) as [L | E]; [apply Rlt_le, atan_increasing, L | rewrite E; apply Rle_refl].
Qed.
"""


def generate_approx():
    d = atan2_constants.derive()
    out = [HEADER]
    for k in range(1, SEGMENTS + 1):
        out.append(lemma(k, d['rows'][k - 1], d['values']))
    return '\n'.join(out)


def evals():
    """(bound, dg bound) literals of each segment's evaluation certificate, read
    back from the committed formal/atan2/eval_<kk>.g so the Coq facts use exactly
    the certificate that was proved."""
    import re
    out = {}
    for k in range(1, SEGMENTS + 1):
        text = (DIR / f'eval_{k:02d}.g').read_text()
        bound = re.search(r'tail - Vx in \[-(\d+b-\d+),', text).group(1)
        dgb = re.search(r'dg in \[-(\d+b-\d+),', text).group(1)
        out[k] = (bound, dgb)
    return out


def generate_segments():
    d = atan2_constants.derive()
    rows, values = d['rows'], d['values']
    ev = evals()
    # The bound the certificate's own generator would write, as a check that the
    # committed certificates are the current ones.
    for k in range(1, SEGMENTS + 1):
        fresh = a2c.eval_bound(rows[k - 1])
        assert ev[k][0] == fresh, f'eval_{k:02d}.g is stale: {ev[k][0]} vs {fresh}'
    out = [
        "(** Segment-by-segment facts of atan2's tables, written by",
        '    generators/atan2_proofs.py; do not edit. For each segment k, the',
        '    certificate formal/atan2/eval_<kk>.g applied over the table words of',
        '    src/atan2/tables.rs, the numeric facts [SegOkRowA] states, and the',
        "    segment's fast value against [atan]. *)",
        'From Coq Require Import Reals ZArith Lia Lra Psatz List.',
        'From Flocq Require Import Core.',
        'From Gappa Require Import Gappa_library.',
        'From Binary64 Require Import Binary64Add IEEE64 Grid.',
        'From Interval Require Import Tactic.',
        'Require Import Ln1pLemmas StageGappa AsinTables AsinKernel AsinSegment AsinWithin Atan2Tables Atan2Kernel Atan2Segment Atan2Approx.',
        *[f'Require atan2_eval_{k:02d}.' for k in range(1, SEGMENTS + 1)],
        'Import ListNotations.',
        'Open Scope R_scope.',
        '',
        "(** The double-word addition's rounding is far below every budget here. *)",
        'Lemma ea_dw_small : 0 <= 3 * bpow radix2 (- prec) ^ 2 / (1 - 4 * bpow radix2 (- prec)) <= / 1000000000000000000000000000000.',
        'Proof.',
        '  replace (- prec)%Z with (-53)%Z by reflexivity. bpow_num.',
        '  split; [interval with (i_prec 120) | interval with (i_prec 160)].',
        'Qed.',
        '',
        'Lemma zero_word : finite (aw 0) /\\ B (aw 0) = 0.',
        'Proof. split; vm_compute; reflexivity. Qed.',
        '',
    ]
    dispatch = []
    for k in range(1, SEGMENTS + 1):
        row = rows[k - 1]
        bound, dgb = ev[k]
        words = [word_data(x) for x in row]
        real = ['0' if atan2_constants.to_bits(x) == 0 else f'(IZR ({w[4]}) * bpow radix2 ({w[6]}))' for w, x in zip(words, row)]
        bound_r = f'(IZR {bound.split("b-")[0]} * bpow radix2 (-{bound.split("b-")[1]}))'
        dgb_r = f'(IZR {dgb.split("b-")[0]} * bpow radix2 (-{dgb.split("b-")[1]}))'
        bn, be = ac.split_lit(bound)
        kk2 = f'{k:02d}'
        bits_of = [atan2_constants.to_bits(x) for x in row]

        def destruct_word(j):
            bits, sign, m, kk, M, dd, E = words[j]
            if bits_of[j] == 0:
                return f'  destruct zero_word as [F{j} V{j}].'
            return (f'  destruct (word_ok_intro (0x{bits:016x})%Z {"true" if sign else "false"} {m}%positive {kk}%nat'
                    f' ({M})%Z {dd}%Z ({E})%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F{j} V{j}].')

        out += [
            f'Lemma evalcert_{kk2} : EvalCert {" ".join(real[2:])} {bound_r} {dgb_r}.',
            'Proof.',
            '  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.',
            f'  - apply (rabs_bnd _ {bn} ({-bn}) ({be})); [reflexivity | bpow_num; lra | ].',
            f'    gappa_goal (atan2_eval_{kk2}.l1 th_ tl_ dg).',
            '  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].',
            f'    gappa_goal (atan2_eval_{kk2}.l1 th_ tl_ dg).',
            'Qed.',
            '',
            f'Lemma segok_{kk2} : SegOkRowA [{"; ".join(f"(0x{bits_of[j]:016x})%Z" for j in range(13))}] {bound_r}.',
            'Proof.',
            '  unfold SegOkRowA. cbn [nth].',
        ]
        for j in range(13):
            out.append(destruct_word(j))
        out += [
            f'  refine (segok_from_values_a {" ".join(["_"] * 28)}',
            f'    {" ".join(f"F{j}" for j in range(13))} {" ".join(f"V{j}" for j in range(13))}',
            f'    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_{kk2} _ _).',
            '  all: seg_numeric.',
            'Qed.',
            '',
        ]
        e_budget, e_n, e_shift = approx_budget(k, values)
        am_n, am_s = amin(k)
        b_frac = Fraction(int(bound.split('b-')[0]), 2 ** int(bound.split('b-')[1]))
        e_a = 3 * U * U / (1 - 4 * U)
        a_min = Fraction(am_n, 2 ** am_s)
        assert ((e_budget + b_frac) * (1 + e_a) + e_a * a_min) <= REL * a_min, (
            f'segment {k}: relative fast bound {float((((e_budget + b_frac) * (1 + e_a) + e_a * a_min) / a_min) * 2 ** 62)} 2^-62')
        row_list = '[' + '; '.join(f'(0x{b:016x})%Z' for b in bits_of) + ']'
        tt = f'((B zh - IZR {k} / 64) + B zl)'
        rel = 'bpow radix2 (-63)'
        out += [
            f'Lemma row_{kk2} : nth (Z.to_nat ({k}%Z - 1)) atan2_segments [] = {row_list}.',
            'Proof. reflexivity. Qed.',
            '',
            f'Lemma fast_{kk2} zh zl : finite zh -> finite zl -> / 128 <= B zh -> B zh <= 1 ->',
            f'  Znearest ne (B zh * 64) = {k}%Z -> Rabs (B zl) <= bpow radix2 (-53) -> on_grid (-211) (B zl) ->',
            '  exists h l, atan2_series zh zl = (h, l) /\\ finite h /\\ finite l /\\ B h = rndF (B h + B l) /\\',
            f'    Rabs (B h + B l - atan (IZR {k} / 64 + {tt})) <= {rel} * atan (IZR {k} / 64 + {tt}).',
            'Proof.',
            '  intros Fz Fl L U Hn Hl Hg.',
            f'  pose proof (series_segment_a zh zl {k}%Z {bound_r} ltac:(lia) Fz Fl L U Hn Hl Hg segok_{kk2}) as SS.',
            f'  cbv zeta in SS. rewrite row_{kk2} in SS. cbn [nth] in SS.',
            '  destruct SS as ' + ac.intro_pattern(['h', 'l', 'Hs', 'Fh', "Fl'", 'Nrm', 'Ht', 'e1', 'ea', 'E1', 'Eea', 'Eq']) + '.',
            "  exists h, l. split; [exact Hs | split; [exact Fh | split; [exact Fl' | split; [exact Nrm | ]]]].",
        ]
        for j in range(13):
            out.append(destruct_word(j))
        out += [
            '  unfold seg_poly in Eq.',
            f'  pose proof (approx_{kk2} _ _ _ _ _ _ _ _ _ _ _ _ _ {tt} {" ".join(f"V{j}" for j in range(13))} Ht) as AP.',
            f'  pose proof (amin_{kk2} {tt} Ht) as HAm.',
            '  destruct ea_dw_small as [Ea0 Ea1].',
            '  rewrite Eq.',
            f'  refine (fast_compose _ _ e1 ea (IZR {e_n} * bpow radix2 (-{e_shift})) {bound_r} _ (IZR {am_n} * bpow radix2 (-{am_s})) _ AP E1 Eea HAm _ Ea0 _).',
            '  - apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0].',
            '  - bpow_num. replace (- prec)%Z with (-53)%Z by reflexivity. bpow_num. clear - Fz. interval with (i_prec 200).',
            'Qed.',
            '',
        ]
        dispatch.append(k)
    cases = ' \\/ '.join(f'k = {k}%Z' for k in range(1, SEGMENTS + 1))
    out += [
        '(** The table branch: [k = round (64 zh)] in [1..64], the tail [zl] a double-word low part',
        '    on the [2^-211] grid. *)',
        f'Theorem fast_table (k : Z) zh zl : (1 <= k <= {SEGMENTS})%Z -> finite zh -> finite zl -> / 128 <= B zh -> B zh <= 1 ->',
        '  Znearest ne (B zh * 64) = k -> Rabs (B zl) <= bpow radix2 (-53) -> on_grid (-211) (B zl) ->',
        '  exists h l, atan2_series zh zl = (h, l) /\\ finite h /\\ finite l /\\ B h = rndF (B h + B l) /\\',
        '    Rabs (B h + B l - atan (IZR k / 64 + ((B zh - IZR k / 64) + B zl)))',
        '      <= bpow radix2 (-63) * atan (IZR k / 64 + ((B zh - IZR k / 64) + B zl)).',
        'Proof.',
        '  intros Hk Fz Fl L U Hn Hl Hg.',
        f'  assert (Hc : {cases}) by lia.',
        '  repeat (destruct Hc as [E | Hc]; [rewrite E in Hn; rewrite E; first ' + '[' + ' | '.join(
            f'exact (fast_{kk:02d} zh zl Fz Fl L U Hn Hl Hg)' for kk in dispatch) + '] | ]).',
        f'  rewrite Hc in Hn. rewrite Hc. exact (fast_{SEGMENTS} zh zl Fz Fl L U Hn Hl Hg).',
        'Qed.',
    ]
    return '\n'.join(out) + '\n'


def main():
    files = {'Atan2Approx.v': generate_approx(), 'Atan2Segments.v': generate_segments()}
    if '--check' in sys.argv[1:]:
        for name, text in files.items():
            if (DIR / name).read_text() != text:
                sys.exit(f'{DIR / name} differs from a fresh generation')
        return
    for name, text in files.items():
        (DIR / name).write_text(text)
        print(f'{name}: written')


if __name__ == '__main__':
    main()
