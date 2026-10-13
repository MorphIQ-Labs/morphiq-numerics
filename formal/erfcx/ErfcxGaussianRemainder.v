(** Uniform center-certificate truncation budgets. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
Require Import StageGappa ErfcxConstants ErfcxFactorial ErfcxGaussianTarget.
Open Scope R_scope.

Lemma gaussian_approx_uniform n x b : Rabs x<=b ->
  Rabs(gaussian_erfcx x-gaussian_approx n x)<=
    2*inv_sqrt_pi*exp(b*b)*b*((b*b)^S n/INR(fact(S n))).
Proof.
  intros Range. eapply Rle_trans; [apply gaussian_approx_error|].
  pose proof (Rabs_pos x) as Abs. pose proof Range as X. apply Rabs_le_inv in X.
  assert (B : 0<=b) by lra.
  assert (Square : 0<=x*x<=b*b) by nra.
  assert (Exp : exp(x*x)<=exp(b*b)).
  { destruct (Rle_lt_or_eq_dec _ _ (proj2 Square)) as [Lt|Eq].
    - apply Rlt_le,exp_increasing; exact Lt.
    - rewrite Eq; apply Rle_refl. }
  assert (Pow : (x*x)^S n<=(b*b)^S n) by (apply pow_incr; exact Square).
  assert (P : 0<INR(fact(S n))) by (apply lt_0_INR,lt_O_fact).
  assert (C : 0<=2*inv_sqrt_pi) by (pose proof inv_sqrt_pi_positive; lra).
  assert (E : 0<=exp(x*x)) by (apply Rlt_le,exp_pos).
  assert (T : 0<=(x*x)^S n/INR(fact(S n)))
    by (unfold Rdiv; apply Rmult_le_pos; [apply pow_le; lra|apply Rlt_le,Rinv_0_lt_compat; exact P]).
  apply Rmult_le_compat.
  - apply Rmult_le_pos; [apply Rmult_le_pos; assumption|exact Abs].
  - exact T.
  - apply Rmult_le_compat; [apply Rmult_le_pos; assumption|exact Abs| |exact Range].
    apply Rmult_le_compat_l; assumption.
  - unfold Rdiv. apply Rmult_le_compat_r; [apply Rlt_le,Rinv_0_lt_compat; exact P|exact Pow].
Qed.

Lemma gaussian_remainder_1 x : Rabs x<=1 ->
  Rabs(gaussian_erfcx x-gaussian_approx 100 x)<=bpow radix2 (-350).
Proof.
  intros X. eapply Rle_trans; [apply (gaussian_approx_uniform 100 x 1 X)|].
  unfold inv_sqrt_pi. binary_factorials. bpow_num. interval with (i_prec 400).
Qed.

Lemma gaussian_remainder_2 x : Rabs x<=2 ->
  Rabs(gaussian_erfcx x-gaussian_approx 140 x)<=bpow radix2 (-350).
Proof.
  intros X. eapply Rle_trans; [apply (gaussian_approx_uniform 140 x 2 X)|].
  unfold inv_sqrt_pi. binary_factorials. bpow_num. interval with (i_prec 400).
Qed.

Lemma gaussian_remainder_4 x : Rabs x<=4 ->
  Rabs(gaussian_erfcx x-gaussian_approx 230 x)<=bpow radix2 (-350).
Proof.
  intros X. eapply Rle_trans; [apply (gaussian_approx_uniform 230 x 4 X)|].
  unfold inv_sqrt_pi. binary_factorials. bpow_num. interval with (i_prec 400).
Qed.

Lemma gaussian_remainder_8 x : Rabs x<=8 ->
  Rabs(gaussian_erfcx x-gaussian_approx 440 x)<=bpow radix2 (-350).
Proof.
  intros X. eapply Rle_trans; [apply (gaussian_approx_uniform 440 x 8 X)|].
  unfold inv_sqrt_pi. binary_factorials. bpow_num. interval with (i_prec 400).
Qed.

Lemma gaussian_remainder_16 x : Rabs x<=16 ->
  Rabs(gaussian_erfcx x-gaussian_approx 1100 x)<=bpow radix2 (-350).
Proof.
  intros X. eapply Rle_trans; [apply (gaussian_approx_uniform 1100 x 16 X)|].
  unfold inv_sqrt_pi. binary_factorials. bpow_num. interval with (i_prec 400).
Qed.
