(** exp/mod.rs's fast value [fast_at] (docs/exp.md, section 4), transcribed on
    binary64 and proved: for the reduced argument [(r_hi, r_lo)] of
    [ExpReduction.reduce] and every table index [j], the double-word [Y] is
    within [2^-69] relatively of [T_j·e^R], where [T_j = 2^(j/128)] and [R] is
    the exact reduced argument ([fast_ok]). The bound is formal/exp/fast.g's
    theorem, whose Coq proof Gappa writes as module [exp_fast]; this file proves
    each of its hypotheses about the transcription: the double-word operations'
    bounds (formal/binary64), formal/exp/mvt.g's theorem, and the constants'
    bounds, which ExpTables.v proves from the definitions of [exp] and [ln]. *)

From Coq Require Import ZArith Reals Lia Lra Psatz.
From Flocq Require Import Core Relative IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Mul IEEE64Eft Encodings.
From Gappa Require Gappa_definitions Gappa_round_def.
Require ExpTables exp_fast exp_mvt.
Import ExpTables.

Open Scope R_scope.

(** The constants [0.5] and [1.0], and [0.0] as the low word of [1.0]. *)
Definition c_half : f64 := b64_of_bits 4602678819172646912.  (* 0x3fe0000000000000 *)
Definition c_one : f64 := b64_of_bits 4607182418800017408.   (* 0x3ff0000000000000 *)
Definition c_zero : f64 := b64_of_bits 0.

Lemma c_half_val : B c_half = 4503599627370496 / 2 ^ 53.
Proof. exact (bits_val 4602678819172646912 false 4503599627370496 53 eq_refl). Qed.
Lemma c_one_val : B c_one = 4503599627370496 / 2 ^ 52.
Proof. exact (bits_val 4607182418800017408 false 4503599627370496 52 eq_refl). Qed.
Lemma c_zero_val : B c_zero = 0.
Proof. exact (bits_zero 0 false eq_refl). Qed.

(** [fast_at(r, j)]: the polynomial in Horner order at [r_hi], then
    [P = r.add_f64(q)], [E = 1.add(P)], [T_j = sum(hi, lo)] and [Y = T_j.mul(E)]. *)
Definition fast_at (rh rl : f64) (j : nat) : f64 * f64 :=
  let t5 := fadd exp_c5 (fmul rh exp_c6) in
  let t4 := fadd exp_c4 (fmul rh t5) in
  let t3 := fadd exp_c3 (fmul rh t4) in
  let h := fadd c_half (fmul rh t3) in
  let q := fmul (fmul rh rh) h in
  let '(ph, pl) := add_f64_64 rh rl q in
  let '(eh, el) := add64 c_one c_zero ph pl in
  let '(th, tl) := two_sum64 (exp_t_hi j) (exp_t_lo j) in
  mul64 th tl eh el.

(** The rounding [fast.g] models: binary64, nearest-even. *)
Notation rn := (round radix2 (FLT_exp (-1074) 53) Gappa_round_def.rndNE).

(** formal/exp/fast.g's theorem, over reals: the double-word steps are
    [(1 + d_i)] factors and [T_j]'s table error is [(1 + d4)]. *)
Theorem fast_bound (Tj rhi rlo dr m a d4 d1 d2 d3 : R) :
  rn rhi = rhi -> Rabs rhi <= 0.00270769 -> Rabs rlo <= / 2 ^ 62 -> Rabs dr <= / 2 ^ 113 ->
  Rabs m <= 25 / 2 ^ 75 -> Rabs a <= exp_poly_bound ->
  Rabs d1 <= / 2 ^ 105 -> Rabs d2 <= 25 / 2 ^ 109 -> Rabs d3 <= 21 / 2 ^ 108 -> Rabs d4 <= / 2 ^ 107 ->
  1 <= Tj <= 2 ->
  let c3 := 375299968947529 * / 2 ^ 51 in let c4 := 6004799503160511 * / 2 ^ 57 in
  let c5 := 4803840849707593 * / 2 ^ 59 in let c6 := 3202560482380763 * / 2 ^ 61 in
  let t5 := rn (c5 + rn (rhi * c6)) in let t4 := rn (c4 + rn (rhi * t5)) in
  let t3 := rn (c3 + rn (rhi * t4)) in let h := rn (/ 2 + rn (rhi * t3)) in
  let q := rn (rn (rhi * rhi) * h) in
  let Q := rhi * rhi * (/ 2 + rhi * (c3 + rhi * (c4 + rhi * (c5 + rhi * c6)))) in
  let expR := 1 + (rhi + rlo - dr) + Q + m + a in
  let Y := Tj * (1 + d4) * ((1 + (rhi + rlo + q) * (1 + d1)) * (1 + d2)) * (1 + d3) in
  Rabs ((Y - Tj * expR) / (Tj * expR)) <= / 2 ^ 69.
Proof.
  intros Hr Hrhi Hrlo Hdr Hm Ha Hd1 Hd2 Hd3 Hd4 HT. cbv zeta.
  apply Rnot_lt_le. intros Hlt.
  apply (exp_fast.l1 Tj rhi rlo dr m a d4 d1 d2 d3).
  unfold exp_fast.s1, exp_fast.s2, exp_fast.s3, exp_fast.s4, exp_fast.s5, exp_fast.s6, exp_fast.s7,
    exp_fast.s8, exp_fast.s9, exp_fast.s10, exp_fast.s11, Gappa_definitions.BND.
  rewrite !Hr.
  unfold exp_poly_bound in Ha.
  apply Rabs_le_inv in Hrhi. apply Rabs_le_inv in Hrlo. apply Rabs_le_inv in Hdr. apply Rabs_le_inv in Hm.
  apply Rabs_le_inv in Ha. apply Rabs_le_inv in Hd1. apply Rabs_le_inv in Hd2. apply Rabs_le_inv in Hd3.
  apply Rabs_le_inv in Hd4.
  cbv [Gappa_definitions.lower Gappa_definitions.upper Gappa_definitions.float2R Gappa_definitions.float10R
       Gappa_definitions.Fnum Gappa_definitions.Fexp Gappa_definitions.Fnum10 Gappa_definitions.Fexp10
       exp_fast.i1 exp_fast.i2 exp_fast.i3 exp_fast.i4 exp_fast.i5 exp_fast.i6 exp_fast.i7 exp_fast.i8
       exp_fast.i9 exp_fast.i10 exp_fast.i11 exp_fast.f1 exp_fast.f2 exp_fast.f3 exp_fast.f4 exp_fast.f5
       exp_fast.f6 exp_fast.f7 exp_fast.f8 exp_fast.f9 exp_fast.f10 exp_fast.f11 exp_fast.f12 exp_fast.f13
       exp_fast.f14 exp_fast.f15 exp_fast.f16 exp_fast.f17 exp_fast.f18 exp_fast.f19 exp_fast.f20
       exp_fast.f21 exp_fast.f22 F2R Defs.Fnum Defs.Fexp].
  repeat split; try (simpl; lra).
  (* Gappa's spellings of 1, 1/2 and the coefficients, as the statement's. *)
  intros Hb.
  assert (K : forall k : nat, bpow radix2 (- Z.of_nat k) = / 2 ^ k)
    by (intros k; rewrite bpow_opp, bpow_powerRZ, <- pow_powerRZ; reflexivity).
  replace (Gappa_pred_bnd.Float1 1) with 1 in Hb by (cbv [Gappa_pred_bnd.Float1]; simpl; ring).
  replace (5 * bpow Gappa_definitions.radix10 (-1)) with (/ 2) in Hb by (simpl; field).
  replace (bpow radix2 (-51)) with (/ 2 ^ 51) in Hb by (symmetry; exact (K 51%nat)).
  replace (bpow radix2 (-57)) with (/ 2 ^ 57) in Hb by (symmetry; exact (K 57%nat)).
  replace (bpow radix2 (-59)) with (/ 2 ^ 59) in Hb by (symmetry; exact (K 59%nat)).
  replace (bpow radix2 (-61)) with (/ 2 ^ 61) in Hb by (symmetry; exact (K 61%nat)).
  replace (bpow radix2 (-69)) with (/ 2 ^ 69) in Hb by (symmetry; exact (K 69%nat)).
  apply (Rlt_irrefl (/ 2 ^ 69)). apply Rlt_le_trans with (1 := Hlt).
  apply Rabs_le. lra.
Qed.

(** The polynomial [Q(v) = v²·(1/2 + v·(c3 + v·(c4 + v·(c5 + v·c6))))], exactly. *)
Definition Qpoly (v : R) : R :=
  v * v * (/ 2 + v * (375299968947529 * / 2 ^ 51 + v * (6004799503160511 * / 2 ^ 57
    + v * (4803840849707593 * / 2 ^ 59 + v * (3202560482380763 * / 2 ^ 61))))).

(** formal/exp/mvt.g's theorem: evaluating [Q] at [r_hi] instead of the exact
    [R = r_hi + delta] costs at most [0x1.9p-71]. *)
Theorem mvt_bound rhi delta : Rabs rhi <= 0.00270769 -> Rabs delta <= 4503599627370497 * / 2 ^ 114 ->
  Rabs (Qpoly (rhi + delta) - Qpoly rhi) <= 25 * / 2 ^ 75.
Proof.
  intros Hr Hd. unfold Qpoly.
  apply Rnot_lt_le. intros Hlt.
  apply (exp_mvt.l1 rhi delta).
  unfold exp_mvt.s1, exp_mvt.s2, exp_mvt.s3, Gappa_definitions.BND.
  apply Rabs_le_inv in Hr. apply Rabs_le_inv in Hd.
  cbv [Gappa_definitions.lower Gappa_definitions.upper Gappa_definitions.float2R Gappa_definitions.float10R
       Gappa_definitions.Fnum Gappa_definitions.Fexp Gappa_definitions.Fnum10 Gappa_definitions.Fexp10
       exp_mvt.i1 exp_mvt.i2 exp_mvt.i3 exp_mvt.f1 exp_mvt.f2 exp_mvt.f3 exp_mvt.f4 exp_mvt.f5 exp_mvt.f6
       F2R Defs.Fnum Defs.Fexp].
  split; [split; simpl; lra | ].
  intros Hb.
  assert (K : forall k : nat, bpow radix2 (- Z.of_nat k) = / 2 ^ k)
    by (intros k; rewrite bpow_opp, bpow_powerRZ, <- pow_powerRZ; reflexivity).
  replace (5 * bpow Gappa_definitions.radix10 (-1)) with (/ 2) in Hb by (simpl; field).
  replace (bpow radix2 (-51)) with (/ 2 ^ 51) in Hb by (symmetry; exact (K 51%nat)).
  replace (bpow radix2 (-57)) with (/ 2 ^ 57) in Hb by (symmetry; exact (K 57%nat)).
  replace (bpow radix2 (-59)) with (/ 2 ^ 59) in Hb by (symmetry; exact (K 59%nat)).
  replace (bpow radix2 (-61)) with (/ 2 ^ 61) in Hb by (symmetry; exact (K 61%nat)).
  replace (bpow radix2 (-75)) with (/ 2 ^ 75) in Hb by (symmetry; exact (K 75%nat)).
  apply (Rlt_irrefl (25 * / 2 ^ 75)). apply Rlt_le_trans with (1 := Hlt).
  apply Rabs_le. lra.
Qed.
