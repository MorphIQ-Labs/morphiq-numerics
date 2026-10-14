(** Error propagation through the two logarithmic compositions. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
Require Import StageGappa Ln1pApprox NormalComplementAnalytic.
Open Scope R_scope.

Lemma normal_ln1p_small e : Rabs e<=/2 -> Rabs(ln(1+e))<=2*Rabs e.
Proof.
  intros E;pose proof(ln1p_series 1 e E)as Error.
  replace(lser 1 e)with e in Error by(cbn;field).
  assert (Remainder : Rabs e^(1+1)/(1-Rabs e)<=Rabs e).
  { pose proof(Rabs_pos e);apply(Rmult_le_reg_r(1-Rabs e));[lra|].
    unfold Rdiv;rewrite Rmult_assoc,Rinv_l,Rmult_1_r by lra;change(Rabs e*(Rabs e*1)<=Rabs e*(1-Rabs e));nra. }
  replace(ln(1+e))with((ln(1+e)-e)+e)by ring.
  eapply Rle_trans;[apply Rabs_triang|];lra.
Qed.

Theorem normal_log_relative_perturbation f e epsilon : 0<f -> 0<=epsilon<=/2 -> Rabs e<=epsilon ->
  Rabs(ln(f*(1+e))-ln f)<=2*epsilon.
Proof.
  intros F Epsilon E;assert (Positive : 0<1+e)by(apply Rabs_le_inv in E;lra).
  rewrite ln_mult by assumption;replace(ln f+ln(1+e)-ln f)with(ln(1+e))by ring.
  eapply Rle_trans;[apply normal_ln1p_small;lra|lra].
Qed.

Theorem normal_log_complement_perturbation q e epsilon : 0<q<=3/8 ->
  0<=epsilon<=/4 -> Rabs e<=epsilon ->
  Rabs(ln(1-q*(1+e))-ln(1-q))<=(-ln(1-q))*(4*epsilon).
Proof.
  intros Q Epsilon E;pose proof(normal_complement_target_range q ltac:(split;lra))as Target.
  set(d:= -q*e/(1-q)).
  assert (D : Rabs d<=2*q*epsilon).
  { unfold d,Rdiv;rewrite Rabs_mult,Rabs_mult,Rabs_Rinv,
      (Rabs_pos_eq(1-q)),(Rabs_left1(-q))by lra.
    assert (Reciprocal : 0</(1-q)<=2)by(split;interval with(i_prec 80)).
    replace(- -q*Rabs e* /(1-q))with(q*(Rabs e* /(1-q)))by ring.
    replace(2*q*epsilon)with(q*(epsilon*2))by ring.
    apply Rmult_le_compat_l;[lra|apply Rmult_le_compat;[apply Rabs_pos|lra|exact E|lra]]. }
  assert (Small : Rabs d<=/2)by nra.
  assert (Identity : 1-q*(1+e)=(1-q)*(1+d))by(unfold d;field;lra).
  rewrite Identity,ln_mult by(apply Rabs_le_inv in Small;lra).
  replace(ln(1-q)+ln(1+d)-ln(1-q))with(ln(1+d))by ring.
  pose proof(normal_ln1p_small d Small);nra.
Qed.
