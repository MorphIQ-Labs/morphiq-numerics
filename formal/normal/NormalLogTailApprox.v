(** Logarithmic Mills correction beyond 37. The asymptotic remainder comes
    from the existing improper-integral theorem, not a sampled fit. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
Require Import StageGappa ErfcxFactorial ErfcxAsymptotic ErfcxTailIntegral NormalLogSensitivity.
Open Scope R_scope.

Definition normal_log_tail_polynomial u :=
  u*(1+u*(-5/2+u*(37/3+u*(-353/4+u*(4081/5+
  u*(-55205/6+u*(854197/7+u*(-14876033/8)))))))).

Definition normal_mills_polynomial u :=
  1+u*(-1+u*(3+u*(-15+u*(105+u*(-945+u*(10395+
  u*(-135135+u*2027025))))))).

Lemma normal_log_mills_polynomial_error u : 0<=u<=/1369 ->
  Rabs(ln(normal_mills_polynomial u)+normal_log_tail_polynomial u)<=bpow radix2 (-65).
Proof.
  intros U;unfold normal_mills_polynomial,normal_log_tail_polynomial.
  apply Rabs_le;split;
    interval with(i_bisect u,i_taylor u,i_degree 10,i_prec 120,i_depth 12).
Qed.

Lemma normal_mills_asymptotic_identity u :
  asym_polynomial 8 (2*u)=normal_mills_polynomial u.
Proof.
  unfold asym_polynomial,asym_coefficient,normal_mills_polynomial.
  cbn [sum_f_R0];binary_factorials;repeat rewrite INR_IZR_INZ;
    cbn [Nat.mul Nat.add Z.of_nat];field.
Qed.

Lemma normal_mills_remainder u : 0<=u<=/1369 ->
  Rabs(tail_integral(2*u)-normal_mills_polynomial u)<=bpow radix2 (-65).
Proof.
  intros U;pose proof(tail_integral_asymptotic 8 (2*u) ltac:(lra))as E.
  rewrite normal_mills_asymptotic_identity in E.
  replace((-1)^S 8)with(-1)in E by(simpl pow;ring).
  assert(Next : asym_next_coefficient 8 (2*u)*INR(fact(2*S 8))<=bpow radix2 (-65)).
  { unfold asym_next_coefficient;binary_factorials;interval with(i_prec 120). }
  apply Rabs_le;split;lra.
Qed.

Lemma normal_mills_polynomial_range u : 0<=u<=/1369 ->
  99/100<=normal_mills_polynomial u<=101/100.
Proof.
  intros U;unfold normal_mills_polynomial;split;
    interval with(i_bisect u,i_taylor u,i_degree 8,i_prec 100,i_depth 12).
Qed.

Theorem normal_log_mills_approximation u : 0<=u<=/1369 ->
  Rabs(ln(tail_integral(2*u))+normal_log_tail_polynomial u)<=bpow radix2 (-62).
Proof.
  intros U;pose proof(normal_mills_remainder u U)as Remainder.
  pose proof(normal_mills_polynomial_range u U)as Range.
  pose proof(normal_log_mills_polynomial_error u U)as Polynomial.
  set(p:=normal_mills_polynomial u)in *.
  set(e:=(tail_integral(2*u)-p)/p).
  assert(E : Rabs e<=bpow radix2 (-64)).
  { unfold e,Rdiv;rewrite Rabs_mult,Rabs_Rinv,(Rabs_pos_eq p)by lra.
    eapply Rle_trans;[apply Rmult_le_compat_r;[left;apply Rinv_0_lt_compat;lra|exact Remainder]|].
    interval with(i_prec 100). }
  pose proof(normal_log_relative_perturbation p e (bpow radix2 (-64))
    ltac:(lra) ltac:(split;interval with(i_prec 100)) E)as Log.
  replace(p*(1+e))with(tail_integral(2*u))in Log by(unfold e;field;lra).
  replace(ln(tail_integral(2*u))+normal_log_tail_polynomial u)with
    ((ln(tail_integral(2*u))-ln p)+(ln p+normal_log_tail_polynomial u))by ring.
  eapply Rle_trans;[apply Rabs_triang|].
  eapply Rle_trans;[apply Rplus_le_compat;[exact Log|exact Polynomial]|].
  bpow_num;lra.
Qed.
