(** Accurate positive-input log-CDF: propagate the tail's relative error
    through ln(1-q), including the logarithm loop and final underflow. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Binary64 Require Import IEEE64.
From Q Require Import Q256 Q256Real.
Require Import StageGappa NormalTailAnalytic NormalTailRange NormalAccurateTailFull
  NormalAccurateOuter NormalComplementAnalytic NormalComplementSeries
  NormalComplementLoop NormalLogSensitivity NormalAccurateRounding.
Open Scope R_scope.

Definition normal_q_log_cdf_positive x := normal_q_log_complement(normal_q_tail x).

Theorem normal_q_log_cdf_positive_error x : finite x -> /2<=B x<=38.6 ->
  valid(normal_q_log_cdf_positive x) /\ exists e,Rabs e<=bpow radix2 (-112) /\
  qval(normal_q_log_cdf_positive x)=ln(1-normal_tail(B x))*(1+e).
Proof.
  intros F X;destruct(normal_q_tail_error x F X)as[T [et [ET Tvalue]]].
  pose proof(normal_tail_outer_range(B x)(proj1 X))as Target.
  pose proof(normal_q_outer_tail_range x F X)as TailRange.
  destruct(normal_q_log_complement_error _ T TailRange)as[Result [el [EL Lvalue]]].
  pose proof(normal_complement_target_range (normal_tail(B x))ltac:(split;lra))as Lrange.
  pose proof(normal_complement_target_range _ TailRange)as Qrange.
  assert (Epsilon : 0<=bpow radix2 (-115)<=/4)by(split;[apply bpow_ge_0|interval with(i_prec 80)]).
  pose proof(normal_log_complement_perturbation (normal_tail(B x))et (bpow radix2 (-115))
    Target Epsilon ET)as Perturbation;rewrite <-Tvalue in Perturbation.
  assert (LogMagnitude : Rabs(ln(1-qval(normal_q_tail x)))<=3*(-ln(1-normal_tail(B x)))).
  { rewrite Rabs_left1 by lra;apply Rabs_le_inv in ET;rewrite Tvalue in Qrange|-*;nra. }
  assert (Evaluation : Rabs(qval(normal_q_log_cdf_positive x)-ln(1-qval(normal_q_tail x)))<=
    3*(-ln(1-normal_tail(B x)))*bpow radix2 (-232)).
  { unfold normal_q_log_cdf_positive;rewrite Lvalue.
    replace(ln(1-qval(normal_q_tail x))*(1+el)-ln(1-qval(normal_q_tail x)))with
      (ln(1-qval(normal_q_tail x))*el)by ring.
    rewrite Rabs_mult;apply Rmult_le_compat;[apply Rabs_pos|apply Rabs_pos|exact LogMagnitude|exact EL]. }
  assert (Absolute : Rabs(qval(normal_q_log_cdf_positive x)-ln(1-normal_tail(B x)))<=
    (-ln(1-normal_tail(B x)))*bpow radix2 (-112)).
  { replace(qval(normal_q_log_cdf_positive x)-ln(1-normal_tail(B x)))with
      ((qval(normal_q_log_cdf_positive x)-ln(1-qval(normal_q_tail x)))+
        (ln(1-qval(normal_q_tail x))-ln(1-normal_tail(B x))))by ring.
    eapply Rle_trans;[apply Rabs_triang|].
    assert (Budget : 3*bpow radix2 (-232)+4*bpow radix2 (-115)<=bpow radix2 (-112))by(interval with(i_prec 300));nra. }
  split;[exact Result|]. exists((qval(normal_q_log_cdf_positive x)-ln(1-normal_tail(B x)))/ln(1-normal_tail(B x)));split.
  - unfold Rdiv;rewrite Rabs_mult,Rabs_Rinv,(Rabs_left1(ln(1-normal_tail(B x))))by lra.
    apply(Rmult_le_reg_r(-ln(1-normal_tail(B x))));[lra|].
    rewrite Rmult_assoc,Rinv_l,Rmult_1_r by lra;nra.
  - field;lra.
Qed.

Theorem normal_q_log_cdf_positive_rounded x : finite x -> /2<=B x<=38.6 ->
  finite(Q256.to_f64(normal_q_log_cdf_positive x)) /\ exists d a,
  Rabs d<=bpow radix2 (-53)+bpow radix2 (-111) /\ Rabs a<=bpow radix2 (-1075) /\
  B(Q256.to_f64(normal_q_log_cdf_positive x))=ln(1-normal_tail(B x))*(1+d)+a.
Proof.
  intros F X;destruct(normal_q_log_cdf_positive_error x F X)as[Result Error].
  pose proof(normal_tail_outer_range(B x)(proj1 X))as Tail.
  pose proof(normal_complement_target_range(normal_tail(B x))ltac:(split;lra))as Range.
  replace(bpow radix2 (-111))with(2*bpow radix2 (-112))by(bpow_num;field).
  apply normal_q_bounded_rounded;try assumption;[rewrite Rabs_left1;lra|split;[apply bpow_ge_0|interval with(i_prec 80)]].
Qed.
