(** The asymmetric interval around zero whose erfcx rounds to one. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64 Encodings.
Require Import StageGappa ErfcxConstants ErfcxGaussianSeries ErfcxGaussianTarget
  ErfcxGaussianMonotone.
Open Scope R_scope.
Definition erfcx_one_pos : f64 := b64_of_bits 4362963262169739115.
Definition erfcx_one_neg : f64 := b64_of_bits 13590838898651885417.
Lemma erfcx_one_pos_ok : finite erfcx_one_pos /\
  B erfcx_one_pos=7982422502469483*bpow radix2 (-107).
Proof.
  split;[exact(bits_finite 4362963262169739115 false 7982422502469483 (-107) eq_refl)|reflexivity].
Qed.
Lemma erfcx_one_neg_ok : finite erfcx_one_neg /\
  B erfcx_one_neg= -7982422502469481*bpow radix2 (-106).
Proof.
  split;[exact(bits_finite 13590838898651885417 true 7982422502469481 (-106) eq_refl)|].
  unfold erfcx_one_neg;rewrite(bits_val 13590838898651885417 true 7982422502469481 106 eq_refl);bpow_num;simpl;field.
Qed.
Definition gaussian_small_polynomial x := exp(x*x)*(1-2*inv_sqrt_pi*x*(1-x*x/3)).
Lemma gaussian_small_approx x : gaussian_approx 1 x=gaussian_small_polynomial x.
Proof.
  unfold gaussian_approx,gaussian_sum,gaussian_small_polynomial.
  cbn. field.
Qed.
Lemma gaussian_small_error x : Rabs x<=bpow radix2 (-52) ->
  Rabs(gaussian_erfcx x-gaussian_small_polynomial x)<=bpow radix2 (-260).
Proof.
  intros X. pose proof(gaussian_approx_error 1 x) as Error.
  rewrite gaussian_small_approx in Error.
  eapply Rle_trans;[exact Error|]. apply Rabs_le_inv in X.
  unfold inv_sqrt_pi;cbn. bpow_num_all;interval with(i_prec 400).
Qed.
Lemma erfcx_one_endpoint_bounds :
  1-bpow radix2 (-54)<gaussian_erfcx(B erfcx_one_pos) /\
  gaussian_erfcx(B erfcx_one_neg)<1+bpow radix2 (-53).
Proof.
  destruct erfcx_one_pos_ok as [_ Pos]. destruct erfcx_one_neg_ok as [_ Neg].
  assert (P : Rabs(B erfcx_one_pos)<=bpow radix2 (-52))
    by (rewrite Pos;bpow_num;interval with(i_prec 80)).
  assert (N : Rabs(B erfcx_one_neg)<=bpow radix2 (-52))
    by (rewrite Neg;bpow_num;interval with(i_prec 80)).
  pose proof(gaussian_small_error _ P) as PE. pose proof(gaussian_small_error _ N) as NE.
  apply Rabs_le_inv in PE,NE.
  assert (PL : 1-bpow radix2 (-54)+bpow radix2 (-260)<gaussian_small_polynomial(B erfcx_one_pos)).
  { rewrite Pos;unfold gaussian_small_polynomial,inv_sqrt_pi;bpow_num;interval with(i_prec 400). }
  assert (NH : gaussian_small_polynomial(B erfcx_one_neg)+bpow radix2 (-260)<1+bpow radix2 (-53)).
  { rewrite Neg;unfold gaussian_small_polynomial,inv_sqrt_pi;bpow_num;interval with(i_prec 400). }
  split;lra.
Qed.
Theorem erfcx_one_interval x : B erfcx_one_neg<=x<=B erfcx_one_pos ->
  1-bpow radix2 (-54)<gaussian_erfcx x<1+bpow radix2 (-53).
Proof.
  intros X. destruct erfcx_one_endpoint_bounds as [P N].
  destruct erfcx_one_pos_ok as [_ Pos].
  assert (Upper : B erfcx_one_pos<=bpow radix2 (-20)) by (rewrite Pos;bpow_num;interval with(i_prec 80)).
  pose proof(gaussian_small_monotone x (B erfcx_one_pos) (proj2 X) Upper).
  pose proof(gaussian_small_monotone (B erfcx_one_neg) x (proj1 X) ltac:(lra));split;lra.
Qed.
Lemma round_one_interval y : 1-bpow radix2 (-54)<y<1+bpow radix2 (-53) -> rndF y=1.
Proof.
  intros Y.
  assert (Format : generic_format radix2 (FLT_exp emin prec) 1).
  { change 1 with (bpow radix2 0);apply generic_format_bpow;unfold FLT_exp,emin,prec;lia. }
  assert (Pred : pred radix2 (FLT_exp emin prec) 1=1-bpow radix2 (-53))
    by exact(pred_bpow radix2 (FLT_exp emin prec) 0).
  assert (Ulp : ulp radix2 (FLT_exp emin prec) 1=bpow radix2 (-52))
    by exact(ulp_bpow radix2 (FLT_exp emin prec) 0).
  assert (Succ : succ radix2 (FLT_exp emin prec) 1=1+bpow radix2 (-52)).
  { rewrite succ_eq_pos by lra;rewrite Ulp;reflexivity. }
  apply Rle_antisym.
  - apply round_N_le_midp;try exact _;[exact Format|]. rewrite Succ;bpow_num_all;lra.
  - apply round_N_ge_midp;try exact _;[exact Format|]. rewrite Pred;bpow_num_all;lra.
Qed.
Theorem erfcx_one_round x : B erfcx_one_neg<=x<=B erfcx_one_pos -> rndF(gaussian_erfcx x)=1.
Proof. intros X;apply round_one_interval,erfcx_one_interval;exact X. Qed.
