(** The reciprocal of the accurate path: [Q256::recip] on an argument scaled into [[1, 2)],
    and the scaling undone ([atan2_recip]). [AsinRecip.q_recip_ok]'s proof for an argument up to [2]. *)
From Coq Require Import Reals ZArith Lia Lra Psatz List.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 RoundingCore.
From Interval Require Import Tactic.
From Q Require Import Q256 Q256Real QSpec.
From Q Require LimbScan Limbs.
Require Import Ln1pLemmas AsinTables AsinKernel AsinSqrtStep AsinNormal AsinQSeries AsinRecip ErfcxAccurateInputs Atan2Kernel.
Open Scope R_scope.

(** The binary64 start of the reciprocal. *)
Lemma recip_start_a c : Q256Real.valid c -> bpow radix2 (-28) <= qval c <= 2 ->
  Q256Real.valid (qf (fdiv asin_one (Q256.to_f64 c))) /\ 0 < qval (qf (fdiv asin_one (Q256.to_f64 c))) /\ Rabs (qval c * qval (qf (fdiv asin_one (Q256.to_f64 c))) - 1) <= bpow radix2 (-51).
Proof.
  intros Vc [Hlo Hhi]. set (cv := qval c) in *.
  assert (Hc28 : 0 < bpow radix2 (-28)) by apply bpow_gt_0.
  assert (Hr : Rabs (rndF cv) < bpow radix2 1024).
  { assert (Hge : bpow radix2 (-28) <= rndF cv) by (apply rndF_ge_bpow; [lia | exact Hlo]).
    assert (Hle : rndF cv <= 2) by (apply rndF_le_two; lra).
    rewrite Rabs_pos_eq by lra.
    apply Rle_lt_trans with 2; [exact Hle | ]. change 2 with (bpow radix2 1). apply bpow_lt; lia. }
  destruct (q_to_float_round c Vc Hr) as [Fx Bx]. change (qval c) with cv in Bx.
  set (x := Q256.to_f64 c) in *.
  assert (Hx28 : bpow radix2 (-28) <= B x) by (rewrite Bx; apply rndF_ge_bpow; [lia | exact Hlo]).
  assert (Hx2 : B x <= 2) by (rewrite Bx; apply rndF_le_two; lra).
  assert (Hcn : bpow radix2 (-1022) <= Rabs cv).
  { rewrite Rabs_pos_eq by lra. apply Rle_trans with (bpow radix2 (-28)); [apply bpow_le; lia | exact Hlo]. }
  pose proof (rnd_rel_f cv Hcn) as R0. rewrite <- Bx in R0. rewrite (Rabs_pos_eq cv) in R0 by lra.
  assert (P53 : bpow radix2 (-53) = / 9007199254740992) by exact bp53. rewrite P53 in R0.
  apply Rabs_le_inv in R0 as [R0a R0b].
  destruct one_val as [V1 Fone].
  assert (Hx0 : B x <> 0) by lra.
  assert (Hb : bnd 1 28 (B asin_one / B x)).
  { unfold bnd. rewrite V1. change (IZR 1) with 1. rewrite Rmult_1_l.
    assert (Hb28 : bpow radix2 28 * bpow radix2 (-28) = 1) by (rewrite <- bpow_plus; reflexivity).
    rewrite Rabs_pos_eq by (apply Rlt_le; apply Rdiv_lt_0_compat; lra).
    apply (Rmult_le_reg_r (B x)); [lra | ]. unfold Rdiv. rewrite Rmult_assoc, Rinv_l by exact Hx0. nra. }
  destruct (fdiv_bnd 1 28 asin_one x Fone Hx0 ltac:(lia) ltac:(lia) (pow_room 1 (1024 - 28) ltac:(lia) ltac:(lia)) ltac:(lia) Hb) as [Ff [Ef _]].
  set (f := fdiv asin_one x) in *.
  rewrite V1 in Ef.
  assert (Hq : bpow radix2 (-1022) <= Rabs (1 / B x)).
  { rewrite Rabs_pos_eq by (apply Rlt_le; apply Rdiv_lt_0_compat; lra).
    apply Rle_trans with (/ 2); [ | apply Rle_trans with (1 / B x); [ | lra]].
    - apply Rle_trans with (bpow radix2 (-1)); [apply bpow_le; lia | bpow_num; lra].
    - unfold Rdiv. rewrite Rmult_1_l. apply Rinv_le_contravar; lra. }
  pose proof (rnd_rel_f _ Hq) as R1. rewrite <- Ef in R1. rewrite P53 in R1.
  rewrite (Rabs_pos_eq (1 / B x)) in R1 by (apply Rlt_le; apply Rdiv_lt_0_compat; lra).
  destruct (q_float_ok f Ff) as [Vy Qy].
  change (qf f) with (q_float f). refine (conj Vy (conj _ _)).
  - rewrite Qy. apply Rabs_le_inv in R1 as [R1a R1b].
    assert (Hw : 0 < 1 / B x). { apply Rdiv_lt_0_compat; [lra | lra]. }
    set (w := 1 / B x) in *. lra.
  - rewrite Qy. set (w := 1 / B x) in *.
    assert (Hwx : w * B x = 1) by (unfold w; field; exact Hx0).
    assert (Hw : 0 < w) by (unfold w; apply Rdiv_lt_0_compat; lra).
    apply Rabs_le_inv in R1 as [R1a R1b].
    assert (Hcw : cv * w <= 1.0001).
    { apply (Rmult_le_reg_r (B x)); [lra | ]. nra. }
    replace (cv * B f - 1) with (cv * (B f - w) + (cv - B x) * w) by (nra).
    assert (bpow radix2 (-51) = / 2251799813685248) by (bpow_num; reflexivity).
    assert (Hs1 : Rabs (cv * (B f - w)) <= / 9007199254740992 * (cv * w)).
    { rewrite Rabs_mult, (Rabs_pos_eq cv) by lra.
      assert (cv * Rabs (B f - w) <= cv * (/ 9007199254740992 * w)) by (apply Rmult_le_compat_l; [lra | apply Rabs_le; split; lra]).
      nra. }
    assert (Hs2 : Rabs ((cv - B x) * w) <= / 9007199254740992 * (cv * w)).
    { rewrite Rabs_mult, (Rabs_pos_eq w) by lra.
      assert (Rabs (cv - B x) <= / 9007199254740992 * cv) by (apply Rabs_le; split; lra).
      nra. }
    apply Rle_trans with (Rabs (cv * (B f - w)) + Rabs ((cv - B x) * w)); [apply Rabs_triang | ].
    nra.
Qed.


Theorem q_recip_ok_a c : Q256Real.valid c -> bpow radix2 (-28) <= qval c <= 2 ->
  Q256Real.valid (q_recip c) /\ 0 < qval (q_recip c) /\ Rabs (qval c * qval (q_recip c) - 1) <= bpow radix2 (-252).
Proof.
  intros Vc Hc. destruct Hc as [Hlo Hhi].
  assert (Hcp : 0 < qval c) by (pose proof (bpow_gt_0 radix2 (-28)); lra).
  destruct (recip_start_a c Vc (conj Hlo Hhi)) as [V0 [P0 E0]].
  rewrite q_recip_steps.
  set (y0 := qf (fdiv asin_one (Q256.to_f64 c))) in *.
  destruct (recip_step_ok c y0 (bpow radix2 (-51)) Vc V0 Hcp P0 E0 (small_bpow (-51) ltac:(lia))) as [V1 [P1 E1]].
  assert (E1' : Rabs (qval c * qval (recip_step c y0) - 1) <= bpow radix2 (-101))
    by (apply Rle_trans with (1 := E1); apply chain1; split; [apply bpow_ge_0 | apply Rle_refl]).
  destruct (recip_step_ok c (recip_step c y0) (bpow radix2 (-101)) Vc V1 Hcp P1 E1' (small_bpow (-101) ltac:(lia))) as [V2 [P2 E2]].
  assert (E2' : Rabs (qval c * qval (recip_step c (recip_step c y0)) - 1) <= bpow radix2 (-201))
    by (apply Rle_trans with (1 := E2); apply chain2; split; [apply bpow_ge_0 | apply Rle_refl]).
  destruct (recip_step_ok c (recip_step c (recip_step c y0)) (bpow radix2 (-201)) Vc V2 Hcp P2 E2' (small_bpow (-201) ltac:(lia))) as [V3 [P3 E3]].
  refine (conj V3 (conj P3 _)).
  apply Rle_trans with (1 := E3); apply chain3; split; [apply bpow_ge_0 | apply Rle_refl].
Qed.

(** A positive value lies in [[2^top, 2^(top + 1))]. *)
Lemma top_bounds c : Q256Real.valid c -> 0 < qval c ->
  bpow radix2 (Q256Real.top c) <= qval c < bpow radix2 (Q256Real.top c + 1).
Proof.
  intros V Hp. destruct V as [O N]. unfold Q256Real.top. rewrite LimbScan.is_zero_ok by apply O.
  destruct (Z.eqb_spec (Limbs.v (Q256.m c)) 0) as [Z | Z].
  - exfalso. rewrite (Q256Real.qval_zero c Z) in Hp. lra.
  - destruct N as [N | N]; [contradiction | ].
    pose proof (Q256.mag_bounds c N) as [Low High]. rewrite (Q256Real.mag_abs c O) in Low, High.
    rewrite (Rabs_pos_eq (qval c)) in Low, High by lra.
    replace (Q256.e c + 255 + 1)%Z with (Q256.e c + 256)%Z by ring. split; assumption.
Qed.

Theorem atan2_recip_ok c : Q256Real.valid c -> 0 < qval c ->
  Q256Real.valid (atan2_recip c) /\ 0 < qval (atan2_recip c) /\ Rabs (qval c * qval (atan2_recip c) - 1) <= bpow radix2 (-252).
Proof.
  intros V Hp. unfold atan2_recip. set (tp := Q256Real.top c).
  destruct (Q256Real.mul_pow2_any c (- tp) V) as [V1 Q1]. set (c1 := Q256Real.mul_pow2 c (- tp)) in *.
  destruct (top_bounds c V Hp) as [T1 T2]. fold tp in T1, T2.
  assert (Hc1 : 1 <= qval c1 < 2).
  { rewrite Q1. assert (Hc : bpow radix2 tp * bpow radix2 (- tp) = 1) by (rewrite <- bpow_plus; replace (tp + - tp)%Z with 0%Z by ring; reflexivity). pose proof (bpow_gt_0 radix2 (- tp)) as Pt.
    assert (bpow radix2 (tp + 1) * bpow radix2 (- tp) = 2) by (rewrite <- bpow_plus; replace (tp + 1 + - tp)%Z with 1%Z by ring; reflexivity).
    split; nra. }
  destruct (q_recip_ok_a c1 V1 ltac:(split; [apply Rle_trans with 1; [apply Rle_trans with (bpow radix2 0); [apply bpow_le; lia | right; reflexivity] | lra] | lra])) as [V2 [P2 E2]].
  destruct (Q256Real.mul_pow2_any (q_recip c1) (- tp) V2) as [V3 Q3].
  refine (conj V3 (conj _ _)).
  - rewrite Q3. apply Rmult_lt_0_compat; [exact P2 | apply bpow_gt_0].
  - rewrite Q3. replace (qval c * (qval (q_recip c1) * bpow radix2 (- tp))) with (qval c1 * qval (q_recip c1)) by (rewrite Q1; ring). exact E2.
Qed.
