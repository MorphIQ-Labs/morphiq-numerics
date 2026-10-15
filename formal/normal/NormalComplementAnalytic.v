(** Positive-series form of -ln(1-q), with bounds relative to q so that
    very small upper-tail probabilities retain a useful error guarantee. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
Require Import StageGappa Ln1pApprox.
Open Scope R_scope.

Fixpoint normal_complement_series n q :=
  match n with O=>0 | S k=>normal_complement_series k q+q^(S k)/INR(S k) end.

Lemma normal_complement_series_identity n q : normal_complement_series n q= -lser n (-q).
Proof.
  induction n as[|n IH];[cbn;ring|]. cbn[normal_complement_series lser];rewrite IH.
  assert (Power : (-q)^(S n)= -((-1)^n)*q^(S n)).
  { replace(-q)with((-1)*q)by ring;rewrite Rpow_mult_distr;cbn[pow];ring. }
  rewrite Power.
  assert (Sign : (-1)^n*(-1)^n=1).
  { rewrite <-pow_add;replace(n+n)%nat with(2*n)%nat by lia;apply pow_1_even. }
  replace((-1)^n/INR(S n)*(-((-1)^n)*q^(S n)))with
    (-(((-1)^n*(-1)^n)*(q^(S n)/INR(S n))))by(unfold Rdiv;ring).
  rewrite Sign;ring.
Qed.

Theorem normal_complement_remainder n q : 0<=q<=/2 ->
  Rabs(-ln(1-q)-normal_complement_series n q)<=q^(n+1)/(1-q).
Proof.
  intros Q;pose proof(ln1p_series n (-q)ltac:(rewrite Rabs_Ropp,Rabs_pos_eq;lra))as Error.
  rewrite Rabs_Ropp,(Rabs_pos_eq q)in Error by lra.
  rewrite normal_complement_series_identity.
  replace(1-q)with(1+ -q)by ring.
  replace(-ln(1+ -q)- -lser n (-q))with(-(ln(1+ -q)-lser n (-q)))by ring.
  rewrite Rabs_Ropp;exact Error.
Qed.

Theorem normal_complement_target_range q : 0<q<=/2 -> q<= -ln(1-q)<=2*q.
Proof.
  intros Q;pose proof(exp_ineq1_le(ln(1-q)))as Lower;rewrite exp_ln in Lower by lra.
  pose proof(normal_complement_remainder 1 q ltac:(split;lra))as Error.
  replace(normal_complement_series 1 q)with q in Error by(cbn;field).
  assert (Remainder : q^(1+1)/(1-q)<=q).
  { apply(Rmult_le_reg_r(1-q));[lra|]. unfold Rdiv;rewrite Rmult_assoc,Rinv_l,Rmult_1_r by lra.
    change(q*(q*1)<=q*(1-q));nra. }
  apply Rabs_le_inv in Error;split;lra.
Qed.

Lemma normal_complement_series_geometric n q : 0<=q<=/2 ->
  0<=normal_complement_series n q<=q*(1-q^n)/(1-q).
Proof.
  intros Q;induction n as[|n IH];[cbn;unfold Rdiv;split;nra|].
  cbn[normal_complement_series].
  assert (Power : 0<=q^(S n))by(apply pow_le;lra).
  assert (Den : 1<=INR(S n))by(change 1 with(INR 1);apply le_INR;lia).
  assert (Term : 0<=q^(S n)/INR(S n)<=q^(S n)).
  { assert (R : 0</INR(S n)<=1).
    { split;[apply Rinv_0_lt_compat;lra|rewrite <-Rinv_1;apply Rinv_le_contravar;lra]. }
    unfold Rdiv;split;nra. }
  assert (Next : q*(1-q^n)/(1-q)+q^(S n)=q*(1-q^(S n))/(1-q)).
  { cbn[pow];field;lra. }
  split;[lra|rewrite <-Next;lra].
Qed.

Theorem normal_complement_series_range n q : (1<=n)%nat -> 0<q<=/2 ->
  q<=normal_complement_series n q<=2*q.
Proof.
  intros N Q;pose proof(normal_complement_series_geometric n q ltac:(split;lra))as Bounds.
  split.
  - clear Bounds;induction n as[|n IH];[lia|]. destruct n as[|n].
    + cbn;unfold Rdiv;field_simplify;lra.
    + change(q<=normal_complement_series(S n)q+q^(S(S n))/INR(S(S n))).
      specialize(IH ltac:(lia)).
      assert (0<=q^(S(S n))/INR(S(S n))).
      { unfold Rdiv;apply Rmult_le_pos;[apply pow_le;lra|left;apply Rinv_0_lt_compat,lt_0_INR;lia]. } lra.
  - eapply Rle_trans;[exact(proj2 Bounds)|].
    apply(Rmult_le_reg_r(1-q));[lra|]. unfold Rdiv;rewrite Rmult_assoc,Rinv_l,Rmult_1_r by lra.
    pose proof(pow_le q n ltac:(lra));nra.
Qed.

Theorem normal_complement_remainder299 q : 0<q<=/2 ->
  Rabs(-ln(1-q)-normal_complement_series 299 q)<=(-ln(1-q))*bpow radix2 (-298).
Proof.
  intros Q;pose proof(normal_complement_remainder 299 q ltac:(split;lra))as Error.
  pose proof(normal_complement_target_range q Q)as Target.
  assert (Small : q^299/(1-q)<=bpow radix2 (-298))by(interval with(i_prec 400)).
  eapply Rle_trans;[exact Error|].
  replace(q^(299+1)/(1-q))with(q*(q^299/(1-q)))by(rewrite pow_add;change(q^1)with(q*1);unfold Rdiv;ring).
  pose proof(bpow_gt_0 radix2 (-298));nra.
Qed.
