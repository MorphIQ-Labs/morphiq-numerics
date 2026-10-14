(** The central Q256 CDF composition and its final binary64 error. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Binary64 Require Import IEEE64.
From Q Require Import Q256 Q256Real.
Require Import StageGappa NormalCentered NormalAccurateCenter NormalAccurateRounding
  ErfcxAccurateSquare.
Open Scope R_scope.

Definition normal_cdf x := /2+normal_center x.
Definition normal_q_central_cdf x := add q_half (normal_q_center x).

Lemma normal_center_range x : Rabs x<=/2 -> Rabs(normal_center x)<=/4.
Proof.
  intros X. pose proof(normal_shape_range _ X) as Shape.
  apply Rabs_le_inv in X;unfold normal_center,normal_density_constant.
  apply Rabs_le;split;interval with(i_prec 80).
Qed.

Lemma normal_central_cdf_range x : Rabs x<=/2 -> /4<=normal_cdf x<=3/4.
Proof.
  intros X. pose proof(normal_center_range _ X) as Center.
  apply Rabs_le_inv in Center;unfold normal_cdf;split;lra.
Qed.

Theorem normal_q_central_cdf_error x : finite x -> Rabs(B x)<=/2 ->
  valid(normal_q_central_cdf x) /\ exists e,Rabs e<=bpow radix2 (-246) /\
  qval(normal_q_central_cdf x)=normal_cdf(B x)*(1+e).
Proof.
  intros F X.
  destruct(normal_q_center_error x F X) as [Q [e [E Value]]].
  pose proof(normal_center_range _ X) as Center.
  assert (Cbound : Rabs(qval(normal_q_center x))<=/2).
  { rewrite Value,Rabs_mult. apply Rabs_le_inv in E.
    pose proof(Rabs_pos(normal_center(B x))).
    rewrite (Rabs_pos_eq(1+e)) by (bpow_num_all;lra).
    bpow_num_all;nra. }
  destruct q_half_ok as [H Half].
  destruct(add_any _ _ H Q) as [Result Addition].
  rewrite Half,(Rabs_pos_eq(/2)),Rmax_left in Addition by lra.
  assert (CenterError : Rabs(qval(normal_q_center x)-normal_center(B x))<=bpow radix2 (-249)).
  { rewrite Value. replace(normal_center(B x)*(1+e)-normal_center(B x))with(normal_center(B x)*e)by ring.
    rewrite Rabs_mult.
    eapply Rle_trans with((/4)*bpow radix2 (-247)).
    - apply Rmult_le_compat;[apply Rabs_pos|apply Rabs_pos|exact Center|exact E].
    - bpow_num;lra. }
  assert (Error : Rabs(qval(normal_q_central_cdf x)-normal_cdf(B x))<=bpow radix2 (-248)).
  { unfold normal_q_central_cdf,normal_cdf.
    replace(qval(add q_half (normal_q_center x))-(/2+normal_center(B x)))with
      ((qval(add q_half (normal_q_center x))-(/2+qval(normal_q_center x)))+
      (qval(normal_q_center x)-normal_center(B x)))by ring.
    eapply Rle_trans;[apply Rabs_triang|].
    assert(Budget : bpow radix2 (-254)*(/2)+bpow radix2 (-249)<=bpow radix2 (-248))by(bpow_num;lra).
    lra. }
  pose proof(normal_central_cdf_range _ X) as Range.
  split;[exact Result|]. exists((qval(normal_q_central_cdf x)-normal_cdf(B x))/normal_cdf(B x)). split.
  - unfold Rdiv;rewrite Rabs_mult,Rabs_Rinv,(Rabs_pos_eq(normal_cdf(B x)))by lra.
    apply(Rmult_le_reg_r(normal_cdf(B x)));[lra|].
    rewrite Rmult_assoc,Rinv_l,Rmult_1_r by lra.
    eapply Rle_trans;[exact Error|].
    replace(bpow radix2 (-248))with(bpow radix2 (-246)/4)by(bpow_num;field).
    pose proof(bpow_gt_0 radix2 (-246));nra.
  - field;lra.
Qed.

Theorem normal_q_central_cdf_rounded x : finite x -> Rabs(B x)<=/2 ->
  finite(Q256.to_f64(normal_q_central_cdf x)) /\ exists d a,
  Rabs d<=bpow radix2 (-53)+bpow radix2 (-245) /\
  Rabs a<=bpow radix2 (-1075) /\
  B(Q256.to_f64(normal_q_central_cdf x))=normal_cdf(B x)*(1+d)+a.
Proof.
  intros F X. destruct(normal_q_central_cdf_error x F X) as [Q Error].
  pose proof(normal_central_cdf_range _ X) as Range.
  assert (Fbound : 0<=normal_cdf(B x)<=1) by(split;lra).
  assert (Ebound : 0<=bpow radix2 (-246)<=/4)by(split;[apply bpow_ge_0|interval with(i_prec 80)]).
  replace(bpow radix2 (-245))with(2*bpow radix2 (-246))by(bpow_num;field).
  exact(normal_q_positive_rounded _ _ _ Q Fbound Ebound Error).
Qed.
