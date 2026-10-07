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
From Binary64 Require Import Binary64Add Binary64Mul IEEE64 IEEE64Add IEEE64Mul IEEE64Eft Grid Encodings.
From Gappa Require Gappa_definitions Gappa_round_def.
From Interval Require Import Tactic.
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
Lemma c_half_finite : finite c_half.
Proof. exact (bits_finite 4602678819172646912 _ _ _ eq_refl). Qed.
Lemma c_one_finite : finite c_one.
Proof. exact (bits_finite 4607182418800017408 _ _ _ eq_refl). Qed.
Lemma c_zero_finite : finite c_zero.
Proof. exact (bits_finite_zero 0 false eq_refl). Qed.

(** [q = r_hi²·(1/2 + r_hi·(c3 + r_hi·(c4 + r_hi·(c5 + r_hi·c6))))], in Horner
    order, as [fast_at] evaluates it. *)
Definition poly_q (rh : f64) : f64 :=
  let t5 := fadd exp_c5 (fmul rh exp_c6) in
  let t4 := fadd exp_c4 (fmul rh t5) in
  let t3 := fadd exp_c3 (fmul rh t4) in
  let h := fadd c_half (fmul rh t3) in
  fmul (fmul rh rh) h.

(** [fast_at(r, j)]: the polynomial at [r_hi], then [P = r.add_f64(q)],
    [E = 1.add(P)], [T_j = sum(hi, lo)] and [Y = T_j.mul(E)]. *)
Definition fast_at (rh rl : f64) (j : nat) : f64 * f64 :=
  let q := poly_q rh in
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

(** An operation whose exact result is at most [2^e] in magnitude is finite,
    is that result rounded, and is itself at most [2^e]. *)
Lemma fadd_p e x y : finite x -> finite y -> (-1074 <= e <= 1023)%Z ->
  Rabs (B x + B y) <= bpow radix2 e ->
  finite (fadd x y) /\ B (fadd x y) = rndF (B x + B y) /\ Rabs (B (fadd x y)) <= bpow radix2 e.
Proof.
  intros Fx Fy He H.
  assert (Hb : bnd 1 e (B x + B y)) by (unfold bnd; lra).
  assert (Ho : (1 < 2 ^ (1024 - e))%Z) by (apply Z.pow_gt_1; lia).
  destruct (fadd_ok 1 e x y Fx Fy ltac:(lia) ltac:(lia) Ho ltac:(lia) Hb) as [F E].
  split; [exact F | split; [exact E | ]].
  rewrite E. pose proof (bnd_round 1 e _ ltac:(lia) ltac:(lia) Hb) as R. unfold bnd in R. lra.
Qed.

Lemma fmul_p e x y : finite x -> finite y -> (-1074 <= e <= 1023)%Z ->
  Rabs (B x * B y) <= bpow radix2 e ->
  finite (fmul x y) /\ B (fmul x y) = rndF (B x * B y) /\ Rabs (B (fmul x y)) <= bpow radix2 e.
Proof.
  intros Fx Fy He H.
  assert (Hb : bnd 1 e (B x * B y)) by (unfold bnd; lra).
  assert (Ho : (1 < 2 ^ (1024 - e))%Z) by (apply Z.pow_gt_1; lia).
  destruct (fmul_ok 1 e x y Fx Fy ltac:(lia) ltac:(lia) Ho ltac:(lia) Hb) as [F E].
  split; [exact F | split; [exact E | ]].
  rewrite E. pose proof (bnd_round 1 e _ ltac:(lia) ltac:(lia) Hb) as R. unfold bnd in R. lra.
Qed.

Lemma Rabs_mult_le a b A C : Rabs a <= A -> Rabs b <= C -> Rabs (a * b) <= A * C.
Proof. intros Ha Hb. rewrite Rabs_mult. apply Rmult_le_compat; try apply Rabs_pos; assumption. Qed.

(** Rounding errs by at most [u = 2^-53] relatively above [2^-1022], and never
    exceeds [2^-1022] in magnitude below it. *)
Lemma rel_FLT v : bpow radix2 (-1022) <= Rabs v -> Rabs (rndF v - v) <= / 9007199254740992 * Rabs v.
Proof.
  intros H.
  pose proof (relative_error_N_FLT radix2 emin prec ltac:(unfold prec; lia) ne v H) as R.
  change (bpow radix2 (- prec + 1)) with (/ 4503599627370496) in R. lra.
Qed.

Lemma rnd_mag v : Rabs (rndF v) <= (1 + / 9007199254740992) * Rabs v + bpow radix2 (-1022).
Proof.
  pose proof (bpow_gt_0 radix2 (-1022)) as P.
  destruct (Rle_lt_dec (bpow radix2 (-1022)) (Rabs v)) as [H | H].
  - pose proof (rel_FLT v H) as R. pose proof (Rabs_triang_inv (rndF v) v). lra.
  - assert (F : fmtF (bpow radix2 (-1022)))
      by (apply generic_format_bpow; unfold FLT_exp, emin, prec; lia).
    pose proof (abs_round_le_generic radix2 (FLT_exp emin prec) (Znearest ne) v _ F (Rlt_le _ _ H)).
    pose proof (Rabs_pos v). lra.
Qed.

(** A double-word's low word, when its sum is below [2^-8]: at most half an
    ulp of [2^-9]'s binade. *)
Lemma err_small v : Rabs v < bpow radix2 (-8) -> Rabs (rndF v - v) <= bpow radix2 (-62).
Proof.
  intros H. destruct (Req_dec v 0) as [-> | Hv].
  - rewrite round_0 by apply valid_rnd_N. rewrite Rminus_0_r, Rabs_R0. apply bpow_ge_0.
  - apply Rle_trans with (/ 2 * ulp radix2 (FLT_exp emin prec) v).
    + apply error_le_half_ulp. exact _.
    + rewrite ulp_neq_0 by exact Hv. unfold cexp.
      pose proof (mag_le_bpow radix2 v (-8) Hv H) as M.
      replace (bpow radix2 (-62)) with (bpow radix2 (-1) * bpow radix2 (-61))
        by (rewrite <- bpow_plus; reflexivity).
      change (bpow radix2 (-1)) with (/ 2).
      apply Rmult_le_compat_l; [lra | apply bpow_le]. unfold FLT_exp, emin, prec. lia.
Qed.

(** [poly_q] computes [fast.g]'s [q], at most [2^-17]. *)
Lemma poly_ok rh : finite rh -> Rabs (B rh) <= 0.00270769 ->
  let r := B rh in
  let c3 := 375299968947529 * / 2 ^ 51 in let c4 := 6004799503160511 * / 2 ^ 57 in
  let c5 := 4803840849707593 * / 2 ^ 59 in let c6 := 3202560482380763 * / 2 ^ 61 in
  finite (poly_q rh) /\
  B (poly_q rh) = rn (rn (r * r) * rn (/ 2 + rn (r * rn (c3 + rn (r * rn (c4 + rn (r * rn (c5 + rn (r * c6))))))))) /\
  Rabs (B (poly_q rh)) <= bpow radix2 (-17) /\
  Rabs (B (poly_q rh)) <= 1.001 * (r * r) + bpow radix2 (-1020).
Proof.
  intros Fr Hr. cbv zeta.
  pose proof exp_c3_finite as F3. pose proof exp_c4_finite as F4.
  pose proof exp_c5_finite as F5. pose proof exp_c6_finite as F6. pose proof c_half_finite as Fh.
  (* The coefficients, as fast.g spells them, and their magnitudes. *)
  assert (V3 : B exp_c3 = 375299968947529 * / 2 ^ 51) by (rewrite exp_c3_val; unfold Rdiv; field).
  assert (V4 : B exp_c4 = 6004799503160511 * / 2 ^ 57) by (rewrite exp_c4_val; unfold Rdiv; field).
  assert (V5 : B exp_c5 = 4803840849707593 * / 2 ^ 59) by (rewrite exp_c5_val; unfold Rdiv; field).
  assert (V6 : B exp_c6 = 3202560482380763 * / 2 ^ 61) by (rewrite exp_c6_val; unfold Rdiv; field).
  assert (Vh : B c_half = / 2) by (rewrite c_half_val; unfold Rdiv; field).
  assert (C3 : 0 <= B exp_c3 <= 0.16667) by (rewrite exp_c3_val; split; interval).
  assert (C4 : 0 <= B exp_c4 <= 0.041667) by (rewrite exp_c4_val; split; interval).
  assert (C5 : 0 <= B exp_c5 <= 0.0083334) by (rewrite exp_c5_val; split; interval).
  assert (C6 : 0 <= B exp_c6 <= 0.0013889) by (rewrite exp_c6_val; split; interval).
  assert (H0 : 0 <= Rabs (B rh)) by apply Rabs_pos.
  unfold poly_q.
  destruct (fmul_p (-17) rh exp_c6 Fr F6 ltac:(lia)) as [Fa [Ea Ba]].
  { change (bpow radix2 (-17)) with (/ 131072). apply Rle_trans with (0.00270769 * 0.0013889).
    - apply Rabs_mult_le; [exact Hr | rewrite Rabs_pos_eq; lra].
    - lra. }
  change (bpow radix2 (-17)) with (/ 131072) in Ba.
  destruct (fadd_p (-6) exp_c5 (fmul rh exp_c6) F5 Fa ltac:(lia)) as [Fb [Eb Bb]].
  { change (bpow radix2 (-6)) with (/ 64). apply Rle_trans with (1 := Rabs_triang _ _).
    rewrite (Rabs_pos_eq (B exp_c5)) by lra. lra. }
  change (bpow radix2 (-6)) with (/ 64) in Bb.
  destruct (fmul_p (-14) rh _ Fr Fb ltac:(lia)) as [Fc [Ec Bc]].
  { change (bpow radix2 (-14)) with (/ 16384).
    apply Rle_trans with (0.00270769 * / 64); [apply Rabs_mult_le; assumption | lra]. }
  change (bpow radix2 (-14)) with (/ 16384) in Bc.
  destruct (fadd_p (-4) exp_c4 _ F4 Fc ltac:(lia)) as [Fd [Ed Bd]].
  { change (bpow radix2 (-4)) with (/ 16). apply Rle_trans with (1 := Rabs_triang _ _).
    rewrite (Rabs_pos_eq (B exp_c4)) by lra. lra. }
  change (bpow radix2 (-4)) with (/ 16) in Bd.
  destruct (fmul_p (-12) rh _ Fr Fd ltac:(lia)) as [Fe [Ee Be]].
  { change (bpow radix2 (-12)) with (/ 4096).
    apply Rle_trans with (0.00270769 * / 16); [apply Rabs_mult_le; assumption | lra]. }
  change (bpow radix2 (-12)) with (/ 4096) in Be.
  destruct (fadd_p (-2) exp_c3 _ F3 Fe ltac:(lia)) as [Ff [Ef Bf]].
  { change (bpow radix2 (-2)) with (/ 4). apply Rle_trans with (1 := Rabs_triang _ _).
    rewrite (Rabs_pos_eq (B exp_c3)) by lra. lra. }
  change (bpow radix2 (-2)) with (/ 4) in Bf.
  destruct (fmul_p (-10) rh _ Fr Ff ltac:(lia)) as [Fg [Eg Bg]].
  { change (bpow radix2 (-10)) with (/ 1024).
    apply Rle_trans with (0.00270769 * / 4); [apply Rabs_mult_le; assumption | lra]. }
  change (bpow radix2 (-10)) with (/ 1024) in Bg.
  destruct (fadd_p 0 c_half _ Fh Fg ltac:(lia)) as [Fi [Ei Bi]].
  { change (bpow radix2 0) with 1. rewrite Vh. apply Rle_trans with (1 := Rabs_triang _ _).
    rewrite (Rabs_pos_eq (/ 2)) by lra. lra. }
  change (bpow radix2 0) with 1 in Bi.
  destruct (fmul_p (-17) rh rh Fr Fr ltac:(lia)) as [Fj [Ej Bj]].
  { change (bpow radix2 (-17)) with (/ 131072).
    apply Rle_trans with (0.00270769 * 0.00270769); [apply Rabs_mult_le; assumption | lra]. }
  change (bpow radix2 (-17)) with (/ 131072) in Bj.
  destruct (fmul_p (-17) _ _ Fj Fi ltac:(lia)) as [Fk [Ek Bk]].
  { change (bpow radix2 (-17)) with (/ 131072).
    apply Rle_trans with (/ 131072 * 1); [apply Rabs_mult_le; assumption | lra]. }
  split; [exact Fk | split; [ | split; [exact Bk | ]]].
  - rewrite Ek, Ej, Ei, Eg, Ef, Ee, Ed, Ec, Eb, Ea, V3, V4, V5, V6, Vh. reflexivity.
  - (* |q| <= (1 + u)^2 r^2 plus what underflow can add. *)
    pose proof (rnd_mag (B (fmul rh rh) * B (fadd c_half (fmul rh (fadd exp_c3 (fmul rh (fadd exp_c4
                  (fmul rh (fadd exp_c5 (fmul rh exp_c6)))))))))) as M2.
    pose proof (rnd_mag (B rh * B rh)) as M1. rewrite <- Ej in M1. rewrite <- Ek in M2.
    assert (Hh : Rabs (B (fmul rh rh) * B (fadd c_half (fmul rh (fadd exp_c3 (fmul rh (fadd exp_c4
                  (fmul rh (fadd exp_c5 (fmul rh exp_c6))))))))) <= Rabs (B (fmul rh rh)) * 1)
      by (apply Rabs_mult_le; [lra | exact Bi]).
    rewrite (Rabs_pos_eq (B rh * B rh)) in M1 by apply Rle_0_sqr.
    replace (bpow radix2 (-1020)) with (4 * bpow radix2 (-1022))
      by (change 4 with (bpow radix2 2); rewrite <- bpow_plus; reflexivity).
    pose proof (bpow_gt_0 radix2 (-1022)). pose proof (Rle_0_sqr (B rh)). unfold Rsqr in *. lra.
Qed.

Lemma bpow_m (k : nat) : bpow radix2 (- Z.of_nat k) = / 2 ^ k.
Proof. rewrite bpow_opp, bpow_powerRZ, <- pow_powerRZ. reflexivity. Qed.

(** The double-word bounds, as fast.g states them. *)
Lemma u2_105 : 2 * bpow radix2 (- prec) ^ 2 = / 2 ^ 105.
Proof.
  rewrite <- bpow_m. change (- Z.of_nat 105)%Z with (1 + (-53 + -53))%Z.
  rewrite !bpow_plus. change (- prec)%Z with (-53)%Z. change (bpow radix2 1) with 2. ring.
Qed.

Lemma gr q x : on_grid q x -> on_grid q (rn x).
Proof.
  intros H.
  exact (@grid_round (FLT_exp (-1074) 53) (@FLT_exp_valid (-1074) 53 prec_gt_0)
           Gappa_round_def.rndNE (valid_rnd_N _) q x H).
Qed.

(** [q] is a multiple of [2^-967] when [r_hi] is one of [2^-151]: the grid
    refines by [r_hi]'s at each product. *)
Lemma poly_grid rh : finite rh -> Rabs (B rh) <= 0.00270769 -> on_grid (-151) (B rh) ->
  on_grid (-967) (B (poly_q rh)).
Proof.
  intros Fr Hr G. pose proof (poly_ok rh Fr Hr) as PO. cbv zeta in PO.
  destruct PO as [_ [E _]]. rewrite E.
  pose proof (val_grid 375299968947529 51 51 ltac:(lia)) as G3.
  pose proof (val_grid 6004799503160511 57 57 ltac:(lia)) as G4.
  pose proof (val_grid 4803840849707593 59 59 ltac:(lia)) as G5.
  pose proof (val_grid 3202560482380763 61 61 ltac:(lia)) as G6.
  assert (Gh : on_grid (-1) (/ 2)) by (exists 1%Z; change (IZR 1 * bpow radix2 (-1)) with (1 * / 2); ring).
  pose proof (gr _ _ (grid_mult _ _ _ _ G G6)) as Ga.
  pose proof (gr (-212) _ (grid_plus _ _ _ (grid_le (- Z.of_nat 59) (-212) _ ltac:(lia) G5) Ga)) as Gt5.
  pose proof (gr _ _ (grid_mult _ _ _ _ G Gt5)) as Gb.
  pose proof (gr (-363) _ (grid_plus _ _ _ (grid_le (- Z.of_nat 57) (-363) _ ltac:(lia) G4) Gb)) as Gt4.
  pose proof (gr _ _ (grid_mult _ _ _ _ G Gt4)) as Gc.
  pose proof (gr (-514) _ (grid_plus _ _ _ (grid_le (- Z.of_nat 51) (-514) _ ltac:(lia) G3) Gc)) as Gt3.
  pose proof (gr _ _ (grid_mult _ _ _ _ G Gt3)) as Gd.
  pose proof (gr (-665) _ (grid_plus _ _ _ (grid_le (-1) (-665) _ ltac:(lia) Gh) Gd)) as Gt.
  pose proof (gr _ _ (grid_mult _ _ _ _ G G)) as Gr2.
  exact (gr _ _ (grid_mult _ _ _ _ Gr2 Gt)).
Qed.

Lemma add_f64_zero : add_f64 0 0 0 = (0, 0).
Proof.
  assert (Z : rndF 0 = 0) by (apply round_0; exact _).
  unfold add_f64, two_sum, fast_two_sum. cbv zeta.
  repeat (rewrite ?Rplus_0_r, ?Rplus_0_l, ?Rminus_0_r, ?Rminus_0_l, ?Ropp_0, ?Z).
  reflexivity.
Qed.

Lemma small_big x e : Rabs x <= 1 -> (0 <= e)%Z -> Rabs x <= bpow radix2 e.
Proof.
  intros H He. apply Rle_trans with 1; [exact H | ].
  change 1 with (bpow radix2 0). apply bpow_le. exact He.
Qed.

Lemma bnd10 x : Rabs x <= 1 -> bnd 1 0 x.
Proof. intros H. unfold bnd. change (IZR 1 * bpow radix2 0) with (1 * 1). lra. Qed.

(** [P = r.add_f64(q)]: a double-word number on [2^-967]'s grid, equal to
    [(r_hi + r_lo + q)·(1 + d1)] with [|d1| <= 2^-105] ([d1] in fast.g). *)
Lemma p_step rh rl :
  finite rh -> finite rl -> B rh = rndF (B rh + B rl) ->
  Rabs (B rh) <= 0.00270769 -> Rabs (B rl) <= bpow radix2 (-62) ->
  on_grid (-151) (B rh) -> on_grid (-151) (B rl) ->
  let '(ph, pl) := add_f64_64 rh rl (poly_q rh) in
  finite ph /\ finite pl /\ B ph = rndF (B ph + B pl) /\
  on_grid (-967) (B ph) /\ on_grid (-967) (B pl) /\
  exists d1, Rabs d1 <= / 2 ^ 105 /\ B ph + B pl = (B rh + B rl + B (poly_q rh)) * (1 + d1).
Proof.
  intros Fh Fl Dh Hrh Hrl Gh Gl.
  pose proof (poly_ok rh Fh Hrh) as PO. cbv zeta in PO. destruct PO as [Fq [Bq [Mq Rq]]].
  pose proof (poly_grid rh Fh Hrh Gh) as Gq.
  set (q := poly_q rh) in *.
  change (bpow radix2 (-17)) with (/ 131072) in Mq.
  change (bpow radix2 (-62)) with (/ 4611686018427387904) in Hrl.
  assert (Uh : Rabs (B rh) <= 1) by lra. assert (Ul : Rabs (B rl) <= 1) by lra.
  assert (Uq : Rabs (B q) <= 1) by lra.
  pose proof (add_f64_ieee rh rl q Fh Fl Fq Dh (small_big _ 1018 Uh ltac:(lia))
                (small_big _ 1018 Ul ltac:(lia)) (small_big _ 1018 Uq ltac:(lia))) as AI.
  destruct (add_f64_64_ok 1 0 rh rl q Fh Fl Fq (bnd10 _ Uh) (bnd10 _ Ul) (bnd10 _ Uq)
              ltac:(lia) ltac:(reflexivity) ltac:(reflexivity) ltac:(lia)) as [_ [_ EQ]].
  pose proof (add_f64_dw (B rh) (B rl) (B q) (B_fmt rh) (B_fmt rl) (B_fmt q) Dh) as DW.
  pose proof (grid_add_f64 (-967) (B rh) (B rl) (B q) (grid_le (-151) (-967) _ ltac:(lia) Gh)
                (grid_le (-151) (-967) _ ltac:(lia) Gl) Gq) as GP.
  destruct (add_f64_64 rh rl q) as [ph pl]. cbn [fst snd] in EQ.
  rewrite <- EQ in DW, GP. cbn [fst snd] in DW, GP. destruct GP as [Gph Gpl].
  destruct AI as [Fph [Fpl Rel]].
  split; [exact Fph | split; [exact Fpl | split; [exact DW | split; [exact Gph | split; [exact Gpl | ]]]]].
  destruct (Req_dec (B rh) 0) as [Z0 | NZ].
  - (* r_hi = 0: then r_lo = q = 0, and so is P. *)
    assert (Z : forall rnd, Valid_rnd rnd -> round radix2 (FLT_exp (-1074) 53) rnd 0 = 0)
      by (intros rnd V; apply round_0; exact V).
    assert (L0 : B rl = 0).
    { rewrite Z0, Rplus_0_l, round_generic in Dh; [lra | exact _ | apply B_fmt]. }
    assert (Q0 : B q = 0).
    { rewrite Bq, Z0, Rmult_0_r, (Z Gappa_round_def.rndNE (valid_rnd_N _)), Rmult_0_l.
      exact (Z Gappa_round_def.rndNE (valid_rnd_N _)). }
    rewrite Z0, L0, Q0, add_f64_zero in EQ. injection EQ as E1 E2.
    exists 0. split; [rewrite Rabs_R0; apply Rlt_le, Rinv_0_lt_compat, pow_lt; lra | ].
    rewrite E1, E2, Z0, L0, Q0. ring.
  - (* r_hi <> 0: S = r_hi + r_lo + q is r_hi's sign and magnitude, so not zero. *)
    pose proof (grid_nonzero _ _ Gh NZ) as Big.
    assert (Vbig : bpow radix2 (-1022) <= Rabs (B rh + B rl)).
    { apply Rnot_lt_le. intros H.
      assert (F : fmtF (bpow radix2 (-1022)))
        by (apply generic_format_bpow; unfold FLT_exp, emin, prec; lia).
      pose proof (abs_round_le_generic radix2 (FLT_exp emin prec) (Znearest ne) _ _ F (Rlt_le _ _ H)) as A.
      rewrite <- Dh in A. assert (bpow radix2 (-1022) < bpow radix2 (-151)) by (apply bpow_lt; lia). lra. }
    pose proof (rel_FLT _ Vbig) as RL. rewrite <- Dh in RL.
    replace (B rh - (B rh + B rl)) with (- B rl) in RL by ring. rewrite Rabs_Ropp in RL.
    pose proof (Rabs_triang (B rh) (B rl)) as T.
    assert (Lrel : Rabs (B rl) <= / 4503599627370496 * Rabs (B rh)).
    { assert (Rabs (B rl) * (1 - / 9007199254740992) <= / 9007199254740992 * Rabs (B rh)) by lra.
      pose proof (Rabs_pos (B rh)). lra. }
    assert (Sq : B rh * B rh <= 0.00270769 * Rabs (B rh)).
    { rewrite <- (Rabs_pos_eq (B rh * B rh)) by apply Rle_0_sqr. rewrite Rabs_mult.
      apply Rmult_le_compat_r; [apply Rabs_pos | exact Hrh]. }
    assert (Tiny : bpow radix2 (-1020) <= / 1024 * bpow radix2 (-151)).
    { replace (/ 1024 * bpow radix2 (-151)) with (bpow radix2 (-161))
        by (change (/ 1024) with (bpow radix2 (-10)); rewrite <- bpow_plus; reflexivity).
      apply bpow_le. lia. }
    assert (SNZ : B rh + B rl + B q <> 0).
    { intros S0. assert (Rabs (B rh) <= Rabs (B rl) + Rabs (B q)).
      { replace (B rh) with (- (B rl + B q)) by lra. rewrite Rabs_Ropp. apply Rabs_triang. }
      pose proof (bpow_gt_0 radix2 (-151)). pose proof (Rabs_pos (B rl)). lra. }
    exists ((B ph + B pl - (B rh + B rl + B q)) / (B rh + B rl + B q)). split.
    + rewrite <- u2_105. exact Rel.
    + field. exact SNZ.
Qed.

Lemma one_dw : B c_one = rndF (B c_one + B c_zero).
Proof.
  rewrite c_zero_val, Rplus_0_r. symmetry. apply round_generic; [exact _ | apply B_fmt].
Qed.

Lemma c_one_1 : B c_one = 1.
Proof. rewrite c_one_val. change (2 ^ 52) with (2 * 2 ^ 51). simpl. lra. Qed.

(** [E = 1.add(P)]: a double-word number near 1 on [2^-967]'s grid, equal to
    [(1 + P)·(1 + d2)] with [|d2| <= 25·2^-109] ([d2] in fast.g). *)
Lemma e_step ph pl :
  finite ph -> finite pl -> B ph = rndF (B ph + B pl) -> Rabs (B ph + B pl) <= / 256 ->
  on_grid (-967) (B ph) -> on_grid (-967) (B pl) ->
  let '(eh, el) := add64 c_one c_zero ph pl in
  finite eh /\ finite el /\ B eh = rndF (B eh + B el) /\ on_grid (-967) (B el) /\
  / 2 <= B eh <= 2 /\
  exists d2, Rabs d2 <= 25 / 2 ^ 109 /\ B eh + B el = (1 + (B ph + B pl)) * (1 + d2).
Proof.
  intros Fph Fpl Dp Hp Gph Gpl.
  pose proof c_one_1 as O1. pose proof c_zero_val as O0.
  assert (Uph : Rabs (B ph) <= / 128).
  { rewrite Dp. pose proof (rnd_mag (B ph + B pl)) as M.
    assert (bpow radix2 (-1022) <= / 1024) by (change (/ 1024) with (bpow radix2 (-10)); apply bpow_le; lia).
    lra. }
  assert (Upl : Rabs (B pl) <= 1).
  { replace (B pl) with ((B ph + B pl) - B ph) by ring.
    apply Rle_trans with (1 := Rabs_triang _ _). rewrite Rabs_Ropp. lra. }
  assert (U1 : Rabs (B c_one) <= 1) by (rewrite O1, Rabs_R1; lra).
  assert (U0 : Rabs (B c_zero) <= 1) by (rewrite O0, Rabs_R0; lra).
  assert (Uph1 : Rabs (B ph) <= 1) by lra.
  assert (NZ : B c_one + B c_zero + (B ph + B pl) <> 0).
  { rewrite O1, O0. intros H. pose proof Hp as Hp'. apply Rabs_le_inv in Hp'. lra. }
  pose proof (add_ieee c_one c_zero ph pl c_one_finite c_zero_finite one_dw Fph Fpl Dp
                (small_big _ 1016 U1 ltac:(lia)) (small_big _ 1016 U0 ltac:(lia))
                (small_big _ 1016 Uph1 ltac:(lia)) (small_big _ 1016 Upl ltac:(lia)) NZ) as AI.
  destruct (add64_ok 1 0 c_one c_zero ph pl c_one_finite c_zero_finite Fph Fpl
              (bnd10 _ U1) (bnd10 _ U0) (bnd10 _ Uph1) (bnd10 _ Upl)
              ltac:(lia) ltac:(reflexivity) ltac:(reflexivity) ltac:(lia)) as [_ [_ EQ]].
  assert (Hx : 1 <= B c_one <= 2 - 2 * bpow radix2 (- prec)).
  { rewrite O1. change (bpow radix2 (- prec)) with (/ 9007199254740992). lra. }
  assert (Hy : Rabs (B ph) <= Rabs (B c_one)) by (rewrite O1, Rabs_R1; lra).
  assert (Hs : B c_one + B ph <> 0)
    by (rewrite O1; intros H; pose proof Uph as U'; apply Rabs_le_inv in U'; lra).
  pose proof (add_dw _ _ _ _ (B_fmt c_one) (B_fmt c_zero) one_dw (B_fmt ph) (B_fmt pl) Dp NZ Hy Hs Hx) as DW.
  assert (G1 : on_grid (-967) (B c_one)).
  { rewrite O1. apply grid_le with 0%Z; [lia | ]. exists 1%Z. change (bpow radix2 0) with 1. ring. }
  assert (G0 : on_grid (-967) (B c_zero)) by (rewrite O0; apply grid_0).
  pose proof (grid_add (-967) _ _ _ _ G1 G0 Gph Gpl) as GE.
  destruct (add64 c_one c_zero ph pl) as [eh el]. cbn [fst snd] in EQ.
  rewrite <- EQ in DW, GE. cbn [fst snd] in DW, GE. destruct GE as [_ Gel].
  destruct AI as [Feh [Fel Rel]].
  rewrite O1, O0, Rplus_0_r in Rel.
  assert (R2 : Rabs ((B eh + B el - (1 + (B ph + B pl))) / (1 + (B ph + B pl))) <= 25 / 2 ^ 109).
  { apply Rle_trans with (1 := Rel). unfold prec. change (bpow radix2 (-53)) with (/ 9007199254740992).
    interval. }
  assert (P1 : 1 - / 256 <= 1 + (B ph + B pl) <= 1 + / 256) by (apply Rabs_le_inv in Hp; lra).
  set (d2 := (B eh + B el - (1 + (B ph + B pl))) / (1 + (B ph + B pl))) in R2.
  assert (Ee : B eh + B el = (1 + (B ph + B pl)) * (1 + d2)) by (unfold d2; field; lra).
  assert (D2 : Rabs d2 <= / 1000) by (apply Rle_trans with (1 := R2); interval).
  (* E is within 2^-8 of 1, and E_hi = RN(E) is near it. *)
  assert (Ev : 0.99 <= B eh + B el <= 1.01).
  { rewrite Ee. apply Rabs_le_inv in D2. split; nra. }
  assert (Big : bpow radix2 (-1022) <= Rabs (B eh + B el))
    by (rewrite Rabs_pos_eq by lra; apply Rle_trans with (/ 1024);
        [change (/ 1024) with (bpow radix2 (-10)); apply bpow_le; lia | lra]).
  pose proof (rel_FLT _ Big) as RE. rewrite <- DW in RE.
  rewrite (Rabs_pos_eq (B eh + B el)) in RE by lra. apply Rabs_le_inv in RE.
  split; [exact Feh | split; [exact Fel | split; [exact DW | split; [exact Gel | split; [lra | ]]]]].
  exists d2. split; [exact R2 | exact Ee].
Qed.
