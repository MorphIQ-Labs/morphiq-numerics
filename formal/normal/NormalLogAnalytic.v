(** Log-CDF identities and the analytic remainders of its two accurate
    logarithm series. Integer-significand evaluation errors are separate. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
Require Import StageGappa Ln1pApprox ErfcxGaussianTarget NormalErfcxSensitivity
  NormalTailAnalytic.
Open Scope R_scope.

Theorem normal_log_tail_identity x : 0<x ->
  ln(normal_tail x)= -x*x/2+ln(gaussian_erfcx(x/sqrt 2)/2).
Proof.
  intros X. unfold normal_tail.
  replace(exp(-x*x/2)*gaussian_erfcx(x/sqrt 2)/2)with
    (exp(-x*x/2)*(gaussian_erfcx(x/sqrt 2)/2))by field.
  rewrite ln_mult,ln_exp;[reflexivity|apply exp_pos|].
  apply Rdiv_lt_0_compat;[|lra]. apply normal_erfcx_positive,Rdiv_lt_0_compat;
    [exact X|interval with(i_prec 80)].
Qed.

Fixpoint normal_atanh_series n t :=
  match n with
  | O => 0
  | S k => normal_atanh_series k t+t^(2*k+1)/INR(2*k+1)
  end.

Lemma normal_atanh_polynomial_identity n t :
  lser (2*n) t-lser (2*n) (-t)=2*normal_atanh_series n t.
Proof.
  induction n as [|n IH];[cbn;ring|].
  replace(2*S n)%nat with(S(S(2*n)))by lia.
  cbn[lser normal_atanh_series].
  rewrite pow_1_even,pow_1_odd.
  assert (Even : (-t)^(2*n)=t^(2*n)).
  { replace(-t)with((-1)*t)by ring;rewrite Rpow_mult_distr,pow_1_even;ring. }
  replace(2*n+1)%nat with(S(2*n))by lia.
  cbn[pow];rewrite Even.
  replace(normal_atanh_series n t)with((lser (2*n) t-lser (2*n) (-t))/2)by lra.
  ring_simplify;field;repeat split;apply not_0_INR;lia.
Qed.

Definition normal_atanh_argument y := (y-1)/(y+1).

Theorem normal_atanh_identity y : 1<=y<=2 ->
  0<=normal_atanh_argument y<=/3 /\
  ln y=ln(1+normal_atanh_argument y)-ln(1-normal_atanh_argument y).
Proof.
  intros Y. assert (Range : 0<=normal_atanh_argument y<=/3).
  { unfold normal_atanh_argument;split.
    - unfold Rdiv;apply Rmult_le_pos;[lra|left;apply Rinv_0_lt_compat;lra].
    - apply(Rmult_le_reg_r(y+1));[lra|].
      replace((y-1)/(y+1)*(y+1))with(y-1)by(field;lra);lra. }
  split;[exact Range|].
  assert (Product : y*(1-normal_atanh_argument y)=1+normal_atanh_argument y).
  { unfold normal_atanh_argument;field;lra. }
  pose proof(ln_mult y (1-normal_atanh_argument y) ltac:(lra) ltac:(lra)) as Log.
  rewrite Product in Log;lra.
Qed.

Theorem normal_atanh_series_error n y : 1<=y<=2 ->
  Rabs(ln y-2*normal_atanh_series n (normal_atanh_argument y))<=
    2*(normal_atanh_argument y)^(2*n+1)/(1-normal_atanh_argument y).
Proof.
  intros Y. destruct(normal_atanh_identity y Y) as [Range Identity].
  set(t:=normal_atanh_argument y)in *.
  pose proof(ln1p_series (2*n) t ltac:(rewrite Rabs_pos_eq;lra)) as A.
  pose proof(ln1p_series (2*n) (-t) ltac:(rewrite Rabs_Ropp,Rabs_pos_eq;lra)) as B.
  rewrite Rabs_Ropp,(Rabs_pos_eq t)in B by lra.
  rewrite (Rabs_pos_eq t)in A by lra.
  rewrite Identity,<-normal_atanh_polynomial_identity.
  replace(1-t)with(1+ -t)by ring.
  replace(ln(1+t)-ln(1+ -t)-(lser (2*n) t-lser (2*n) (-t)))with
    ((ln(1+t)-lser (2*n) t)-(ln(1+ -t)-lser (2*n) (-t)))by ring.
  replace((ln(1+t)-lser (2*n) t)-(ln(1+ -t)-lser (2*n) (-t)))with
    ((ln(1+t)-lser (2*n) t)+ -(ln(1+ -t)-lser (2*n) (-t)))by ring.
  eapply Rle_trans;[apply Rabs_triang|]. rewrite Rabs_Ropp.
  replace(1+ -t)with(1-t)in A,B|-*by ring.
  eapply Rle_trans;[apply Rplus_le_compat;[exact A|exact B]|].
  right;unfold Rdiv,Rminus;ring.
Qed.

Theorem normal_atanh_series100_error y : 1<=y<=2 ->
  Rabs(ln y-2*normal_atanh_series 100 (normal_atanh_argument y))<=bpow radix2 (-316).
Proof.
  intros Y. pose proof(normal_atanh_series_error 100 y Y) as Error.
  destruct(normal_atanh_identity y Y) as [Range _].
  eapply Rle_trans;[exact Error|]. interval with(i_prec 400).
Qed.

Theorem normal_log_complement_series299_error q : 0<=q<=/2 ->
  Rabs(ln(1-q)-lser 299 (-q))<=bpow radix2 (-299).
Proof.
  intros Q. pose proof(ln1p_series 299 (-q) ltac:(rewrite Rabs_Ropp,Rabs_pos_eq;lra)) as Error.
  rewrite Rabs_Ropp,(Rabs_pos_eq q) in Error by lra.
  replace(1-q)with(1+ -q)by ring.
  eapply Rle_trans;[exact Error|]. interval with(i_prec 400).
Qed.
