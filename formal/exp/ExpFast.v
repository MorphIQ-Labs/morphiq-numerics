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

(** [poly_q] computes [fast.g]'s [q], at most [2^-17]. *)
Lemma poly_ok rh : finite rh -> Rabs (B rh) <= 0.00270769 ->
  let r := B rh in
  let c3 := 375299968947529 * / 2 ^ 51 in let c4 := 6004799503160511 * / 2 ^ 57 in
  let c5 := 4803840849707593 * / 2 ^ 59 in let c6 := 3202560482380763 * / 2 ^ 61 in
  finite (poly_q rh) /\
  B (poly_q rh) = rn (rn (r * r) * rn (/ 2 + rn (r * rn (c3 + rn (r * rn (c4 + rn (r * rn (c5 + rn (r * c6))))))))) /\
  Rabs (B (poly_q rh)) <= bpow radix2 (-17).
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
  split; [exact Fk | split; [ | exact Bk]].
  rewrite Ek, Ej, Ei, Eg, Ef, Ee, Ed, Ec, Eb, Ea, V3, V4, V5, V6, Vh. reflexivity.
Qed.
