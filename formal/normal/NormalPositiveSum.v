(** Relative Q256 addition for nonnegative series. Cancellation is absent,
    so the generic alignment bound is relative to the sum itself. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Q Require Import Q256 Q256Real.
Require Import StageGappa.
Open Scope R_scope.

Theorem normal_q_positive_add_relative a b : valid a -> valid b ->
  0<=qval a -> 0<=qval b ->
  valid(add a b) /\ exists e,Rabs e<=bpow radix2 (-254) /\
    qval(add a b)=(qval a+qval b)*(1+e).
Proof.
  intros A B NonnegativeA NonnegativeB;destruct(add_any a b A B)as[Result Error].
  rewrite(Rabs_pos_eq(qval a)),(Rabs_pos_eq(qval b))in Error by lra.
  assert (Bound : Rmax(qval a)(qval b)<=qval a+qval b)by(apply Rmax_lub;lra).
  assert (Relative : Rabs(qval(add a b)-(qval a+qval b))<=bpow radix2 (-254)*(qval a+qval b)).
  { eapply Rle_trans;[exact Error|apply Rmult_le_compat_l;[apply bpow_ge_0|exact Bound]]. }
  split;[exact Result|]. destruct(Req_dec(qval a+qval b)0)as[Zero|Nonzero].
  - exists 0;split;[rewrite Rabs_R0;apply bpow_ge_0|].
    rewrite Zero,Rmult_0_r,Rminus_0_r in Relative;apply Rabs_le_inv in Relative.
    rewrite Zero;ring_simplify;lra.
  - exists((qval(add a b)-(qval a+qval b))/(qval a+qval b));split.
    + unfold Rdiv;rewrite Rabs_mult,Rabs_Rinv,(Rabs_pos_eq(qval a+qval b))by lra.
      apply(Rmult_le_reg_r(qval a+qval b));[lra|].
      rewrite Rmult_assoc,Rinv_l,Rmult_1_r by lra;exact Relative.
    + field;exact Nonzero.
Qed.

Lemma normal_positive_relative_value target epsilon value : 0<target ->
  0<=epsilon<1 -> (exists e,Rabs e<=epsilon /\ value=target*(1+e)) -> 0<value.
Proof.
  intros Positive Epsilon [e [E Value]];apply Rabs_le_inv in E;rewrite Value;nra.
Qed.

Lemma normal_weighted_relative_error a b ea eb epsilon :
  0<=a -> 0<=b -> 0<a+b -> Rabs ea<=epsilon -> Rabs eb<=epsilon ->
  Rabs((a*ea+b*eb)/(a+b))<=epsilon.
Proof.
  intros A B Sum EA EB;apply Rabs_le_inv in EA,EB.
  assert (Bounds : -epsilon*(a+b)<=a*ea+b*eb<=epsilon*(a+b)).
  { split;nra. }
  apply Rabs_le;split.
  - apply(Rmult_le_reg_r(a+b));[exact Sum|].
    unfold Rdiv;rewrite Rmult_assoc,Rinv_l,Rmult_1_r by lra;nra.
  - apply(Rmult_le_reg_r(a+b));[exact Sum|].
    unfold Rdiv;rewrite Rmult_assoc,Rinv_l,Rmult_1_r by lra;nra.
Qed.
