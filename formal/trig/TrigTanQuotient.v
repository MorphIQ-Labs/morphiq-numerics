(** Accurate tangent's quotient error, before quadrant and denominator selection. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Q Require Import Q256 Q256Real.
From Binary64 Require Import IEEE64.
From Interval Require Import Tactic.
Require Import AsinKernel TrigReciprocal StageGappa.
Open Scope R_scope.

Lemma trig_relative_factor y v eps : 0<=eps -> Rabs(y-v)<=eps*Rabs v ->
  exists d, Rabs d<=eps /\ y=v*(1+d).
Proof.
  intros P Error. destruct (Req_dec v 0) as [Zero|Nonzero].
  - subst v. rewrite Rminus_0_r,Rabs_R0,Rmult_0_r in Error.
    assert (Y:y=0) by (apply Rabs_le_inv in Error; lra).
    exists 0. rewrite Rabs_R0,Y. split; [exact P|ring].
  - exists ((y-v)/v). split.
    + unfold Rdiv. rewrite Rabs_mult,Rabs_Rinv by exact Nonzero.
      apply (Rmult_le_reg_r (Rabs v)); [apply Rabs_pos_lt; exact Nonzero|].
      rewrite Rmult_assoc,Rinv_l,Rmult_1_r by (apply Rabs_no_R0; exact Nonzero).
      exact Error.
    + field; exact Nonzero.
Qed.

Lemma trig_quotient_error a b r m :
  Rabs a<=bpow radix2 (-198) -> Rabs b<=bpow radix2 (-198) ->
  Rabs r<=bpow radix2 (-252) -> Rabs m<=bpow radix2 (-255) ->
  Rabs((1+a)*(1+r)*(1+m)/(1+b)-1)<=bpow radix2 (-196).
Proof.
  intros A B R M. apply Rabs_le_inv in A,B,R,M.
  bpow_num_all. apply Rabs_le; split; interval with (i_prec 400).
Qed.

Theorem trig_q_quotient_error n d nv dv : valid n -> valid d -> dv<>0 ->
  bpow radix2 (-1022)<=Rabs(qval d) -> finite(Q256.to_f64 d) ->
  Rabs(qval n-nv)<=bpow radix2 (-198)*Rabs nv ->
  Rabs(qval d-dv)<=bpow radix2 (-198)*Rabs dv ->
  valid(Q256.mul n (AsinKernel.q_recip d)) /\
  Rabs(qval(Q256.mul n (AsinKernel.q_recip d))-nv/dv)<=bpow radix2 (-196)*Rabs(nv/dv).
Proof.
  intros N D Dnonzero Lower Finite En Ed.
  destruct (q_reciprocal_full_contract d D Lower Finite) as [R Er].
  destruct (trig_relative_factor (qval n) nv _ (bpow_ge_0 _ _) En) as [a [A Na]].
  destruct (trig_relative_factor (qval d) dv _ (bpow_ge_0 _ _) Ed) as [b [B Db]].
  destruct (trig_relative_factor (qval(AsinKernel.q_recip d)) (/qval d) _
    (bpow_ge_0 _ _) Er) as [r [Re Rr]].
  destruct (mul_relative n (AsinKernel.q_recip d) N R) as [V [m [M Result]]].
  split; [exact V|].
  assert (Bsmall:0<1+b).
  { apply Rabs_le_inv in B.
    assert (Small:bpow radix2 (-198)<1) by (change 1 with (bpow radix2 0); apply bpow_lt; lia).
    lra. }
  rewrite Result,Na,Rr,Db.
  replace (nv*(1+a)*(/(dv*(1+b))*(1+r))*(1+m)-nv/dv) with
    ((nv/dv)*((1+a)*(1+r)*(1+m)/(1+b)-1)) by (field; split; lra).
  rewrite Rabs_mult. apply Rle_trans with (Rabs(nv/dv)*bpow radix2 (-196)).
  - apply Rmult_le_compat_l; [apply Rabs_pos|apply trig_quotient_error; assumption].
  - right; ring.
Qed.
