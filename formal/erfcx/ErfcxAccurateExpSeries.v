(** Approximation and Q256 evaluation of the reflected exponential series. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Q Require Import Q256 Q256Real.
Require Import StageGappa Expm1Series ErfcxFactorial ErfcxAccurateHorner.
Open Scope R_scope.

Lemma exp_horner_polynomial r : exp_horner r 24=esum 24 r.
Proof.
  unfold esum. cbn [sum_f_R0 exp_horner]. binary_factorials.
  repeat rewrite INR_IZR_INZ. small_numerals. field.
Qed.

Lemma exp_horner_truncation r : Rabs r<=/256 ->
  Rabs (exp_horner r 24-exp r)<=bpow radix2 (-282).
Proof.
  intros R. rewrite exp_horner_polynomial,Rabs_minus_sym.
  eapply Rle_trans; [apply exp_taylor_bound; lra | ].
  binary_factorials. pose proof (Rabs_pos r) as Pos.
  bpow_num. interval with (i_prec 400).
Qed.

Theorem q_exp_horner_exp r : valid r -> Rabs (qval r)<=/256 ->
  valid (q_exp_horner r 24) /\
  Rabs (qval (q_exp_horner r 24)-exp (qval r))<=bpow radix2 (-251).
Proof.
  intros R Range. destruct (q_exp_horner_error r 24 R Range ltac:(lia)) as [Q Error].
  pose proof (exp_horner_truncation _ Range) as Truncation. split; [exact Q | ].
  replace (qval (q_exp_horner r 24)-exp (qval r)) with
    ((qval (q_exp_horner r 24)-exp_horner (qval r) 24)+
      (exp_horner (qval r) 24-exp (qval r))) by ring.
  eapply Rle_trans; [apply Rabs_triang | ].
  assert (B : bpow radix2 (-252)+bpow radix2 (-282)<=bpow radix2 (-251)) by (bpow_num; lra).
  lra.
Qed.
