(** The supremum over the exponent of one node's relative error: for
    [theta], [b] nonnegative and [nu = 1 - theta], [exp(-nu Q) (b + theta Q)]
    is at most [(theta/nu) exp(nu b/theta - 1)] when [nu b <= theta] and at
    most [b] otherwise, for every [Q >= 0]. *)
From Coq Require Import Reals Lra Psatz.
Require Import BvnRound.
Open Scope R_scope.

Definition Gsup (b theta nu : R) : R :=
  if Rle_dec (nu * b) theta then theta / nu * exp (nu * b / theta - 1) else b.

Lemma Gsup_bound b theta nu Q : 0 <= Q -> 0 <= b -> 0 < theta -> 0 < nu ->
  exp (- (nu * Q)) * (b + theta * Q) <= Gsup b theta nu.
Proof.
  intros HQ Hb Ht Hn. unfold Gsup.
  set (zz := nu * Q).
  assert (Hz : 0 <= zz) by (unfold zz; apply Rmult_le_pos; lra).
  assert (E : b + theta * Q = theta / nu * (zz + nu * b / theta)).
  { unfold zz. field. split; lra. }
  rewrite E.
  set (beta := nu * b / theta).
  assert (Hbeta : 0 <= beta) by (unfold beta; apply Rmult_le_pos; [nra | apply Rlt_le, Rinv_0_lt_compat; lra]).
  assert (Htn : 0 < theta / nu) by (apply Rmult_lt_0_compat; [lra | apply Rinv_0_lt_compat; lra]).
  destruct (Rle_dec (nu * b) theta) as [Hle | Hgt].
  - assert (Hb1 : beta <= 1).
    { unfold beta. apply Rmult_le_reg_r with theta; [lra |].
      replace (nu * b / theta * theta) with (nu * b) by (field; lra). lra. }
    (* exp(-zz) (zz + beta) <= exp(beta - 1) *)
    assert (Hk : exp (- zz) * (zz + beta) <= exp (beta - 1)).
    { assert (H1 : zz + beta <= exp (zz + beta - 1)).
      { pose proof (exp_ineq1_le (zz + beta - 1)). lra. }
      assert (H2 : exp (- zz) * exp (zz + beta - 1) = exp (beta - 1)).
      { rewrite <- exp_plus. f_equal. ring. }
      assert (H3 : exp (- zz) * (zz + beta) <= exp (- zz) * exp (zz + beta - 1))
        by (apply Rmult_le_compat_l; [left; apply exp_pos | exact H1]).
      lra. }
    replace (exp (- zz) * (theta / nu * (zz + beta))) with (theta / nu * (exp (- zz) * (zz + beta))) by ring.
    apply Rmult_le_compat_l; [lra | exact Hk].
  - assert (Hb1 : 1 < beta).
    { unfold beta. apply Rmult_lt_reg_r with theta; [lra |].
      replace (nu * b / theta * theta) with (nu * b) by (field; lra). lra. }
    assert (Hk : exp (- zz) * (zz + beta) <= beta).
    { assert (He : 1 + zz <= exp zz) by apply exp_ineq1_le.
      assert (H4 : zz + beta <= beta * exp zz) by nra.
      assert (H5 : exp (- zz) * exp zz = 1) by (rewrite <- exp_plus; replace (- zz + zz) with 0 by ring; apply exp_0).
      assert (H6 : exp (- zz) * (zz + beta) <= exp (- zz) * (beta * exp zz))
        by (apply Rmult_le_compat_l; [left; apply exp_pos | exact H4]).
      nra. }
    replace (exp (- zz) * (theta / nu * (zz + beta))) with (theta / nu * (exp (- zz) * (zz + beta))) by ring.
    assert (Hm : theta / nu * (exp (- zz) * (zz + beta)) <= theta / nu * beta)
      by (apply Rmult_le_compat_l; [lra | exact Hk]).
    eapply Rle_trans; [exact Hm |]. right. unfold beta. field. split; lra.
Qed.

(** One node's contribution: [exp(-Q) (B' exp(theta Q) - 1)], [B' = 1 + b], is at
    most [Gsup b theta (1 - theta)] for [theta] in [(0, 1)]. *)
Lemma node_sup b theta Q : 0 <= Q -> 0 <= b -> 0 < theta -> theta < 1 ->
  exp (- Q) * ((1 + b) * exp (theta * Q) - 1) <= Gsup b theta (1 - theta).
Proof.
  intros HQ Hb Ht Ht1.
  eapply Rle_trans; [| apply (Gsup_bound b theta (1 - theta) Q HQ Hb Ht); lra].
  assert (E1 : exp (- Q) * ((1 + b) * exp (theta * Q) - 1) = exp (- ((1 - theta) * Q)) * (1 + b) - exp (- Q)).
  { assert (H : exp (- Q) * exp (theta * Q) = exp (- ((1 - theta) * Q))).
    { rewrite <- exp_plus. f_equal. ring. }
    nra. }
  assert (E2 : exp (- Q) = exp (- ((1 - theta) * Q)) * exp (- (theta * Q))).
  { rewrite <- exp_plus. f_equal. ring. }
  pose proof (exp_ineq1_le (- (theta * Q))) as H3.
  pose proof (exp_pos (- ((1 - theta) * Q))) as H4.
  assert (H5 : exp (- ((1 - theta) * Q)) * (1 - theta * Q) <= exp (- Q)).
  { rewrite E2. apply Rmult_le_compat_l; [lra | lra]. }
  nra.
Qed.
