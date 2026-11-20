(** Relative-error witnesses and scaling of analytic enclosures, including zero. *)
From Coq Require Import Reals Lra Psatz.
From Flocq Require Import Core.
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

Lemma trig_scaled_enclosure v a k lo hi p eps : 0<=k ->
 a+k*lo<=v<=a+k*hi -> Rabs(lo-p)<=eps*Rabs p -> Rabs(hi-p)<=eps*Rabs p ->
 Rabs(v-(a+k*p))<=eps*Rabs(k*p).
Proof.
 intros K Range Lo Hi. apply Rabs_le_inv in Lo,Hi.
 assert (Low:k*(p-eps*Rabs p)<=k*lo) by (apply Rmult_le_compat_l; [exact K|lra]).
 assert (High:k*hi<=k*(p+eps*Rabs p)) by (apply Rmult_le_compat_l; [exact K|lra]).
 rewrite Rabs_mult,(Rabs_pos_eq _ K). apply Rabs_le; split; nra.
Qed.
