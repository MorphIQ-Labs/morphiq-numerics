(** The positive far log-CDF uses -q for q=Phi(-x). Its omitted logarithmic
    term is included in the same rounding guard as the probability error. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
Require Import StageGappa Ln1pApprox.
Open Scope R_scope.

Lemma normal_finite_log_remainder q : 0<q<=/2 ->
  Rabs(-ln(1-q)-q)<=2*q*q.
Proof.
  intros Q;pose proof(ln1p_series 1 (-q)ltac:(rewrite Rabs_left1;lra))as Series.
  replace(lser 1 (-q))with(-q)in Series by(cbn;field).
  replace(1+ -q)with(1-q)in Series by ring.
  replace(-ln(1-q)-q)with(-(ln(1-q)- -q))by ring;rewrite Rabs_Ropp.
  apply Rle_trans with(Rabs(-q)^(1+1)/(1-Rabs(-q)));[exact Series|].
  rewrite Rabs_left1 by lra;replace(- -q)with q by ring.
  apply(Rmult_le_reg_r(1-q));[lra|].
  unfold Rdiv;rewrite Rmult_assoc,Rinv_l,Rmult_1_r by lra;cbn;nra.
Qed.

Lemma normal_finite_tail_budget h l z : 0<h -> 0<z ->
  Rabs l<=bpow radix2(-51)*h ->
  Rabs(z-(h+l))<=5*bpow radix2(-68)*z ->
  z<=2*h /\ Rabs(z-(h+l))<=21*bpow radix2(-70)*h.
Proof.
  intros H Z L Error;pose proof Error as Signed;apply Rabs_le_inv in L,Signed.
  bpow_num_all;split;nra.
Qed.

Theorem normal_finite_log_budget q h l k : 0<q<=bpow radix2(-980) -> 0<h ->
  Rabs l<=bpow radix2(-51)*h ->
  Rabs(q/bpow radix2 k-(h+l))<=5*bpow radix2(-68)*(q/bpow radix2 k) ->
  Rabs((-ln(1-q))/bpow radix2 k-(h+l))<=11*bpow radix2(-69)*h.
Proof.
  intros Q H L Error;assert(Power : 0<bpow radix2 k)by apply bpow_gt_0.
  assert(Z : 0<q/bpow radix2 k)by(apply Rdiv_lt_0_compat;lra).
  destruct(normal_finite_tail_budget h l _ H Z L Error)as[Range Budget].
  pose proof(normal_finite_log_remainder q ltac:(bpow_num_all;split;lra))as Remainder.
  replace((-ln(1-q))/bpow radix2 k-(h+l))with
    ((-ln(1-q)-q)/bpow radix2 k+(q/bpow radix2 k-(h+l)))by(field;lra).
  eapply Rle_trans;[apply Rabs_triang|].
  assert(Scaled : Rabs((-ln(1-q)-q)/bpow radix2 k)<=2*q*(q/bpow radix2 k)).
  { unfold Rdiv;rewrite Rabs_mult,Rabs_Rinv,(Rabs_pos_eq(bpow radix2 k))by lra.
    replace(2*q*(q* /bpow radix2 k))with((2*q*q)* /bpow radix2 k)by ring.
    apply Rmult_le_compat_r;[apply Rlt_le,Rinv_0_lt_compat;exact Power|exact Remainder]. }
  assert(Tiny : 2*q*(q/bpow radix2 k)<=bpow radix2(-70)*h).
  { assert(2*q*(q/bpow radix2 k)<=4*q*h)by nra.
    bpow_num_all;nra. }
  assert(C : 11*bpow radix2(-69)=22*bpow radix2(-70))by(bpow_num;field).
  rewrite C;lra.
Qed.
