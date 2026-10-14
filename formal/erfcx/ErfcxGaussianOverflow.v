(** The encoded overflow threshold against the finite Gaussian definition. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Interval Require Import Tactic.
From Binary64 Require Import IEEE64 Encodings.
Require Import StageGappa ErfcxGaussianTarget ErfcxGaussianReflection ErfcxGaussianFar
  ErfcxGaussianMonotone ErfcxReflectionSquare.
Open Scope R_scope.
Lemma gaussian_overflow_boundary :
  bpow radix2 1024-bpow radix2 970<=gaussian_erfcx(B reflection_limit).
Proof.
  pose proof reflection_limit_value as Limit.
  pose proof(gaussian_far_bound (-B reflection_limit) ltac:(lra)) as Bound.
  replace (-B reflection_limit * -B reflection_limit) with (B reflection_limit*B reflection_limit) in Bound by ring.
  apply Rabs_le_inv in Bound.
  assert (Identity : gaussian_erfcx(B reflection_limit)=
    2*exp(B reflection_limit*B reflection_limit)-gaussian_erfcx(-B reflection_limit))
    by (rewrite gaussian_erfcx_reflection;ring).
  rewrite Identity. eapply Rle_trans with
    ((2-bpow radix2 (-350))*exp(B reflection_limit*B reflection_limit));[|nra].
  unfold reflection_limit.
  rewrite(bits_val 13851560577301767119 true 7495322764862415 48 eq_refl).
  bpow_num. simpl. interval with(i_prec 400).
Qed.
Theorem gaussian_overflow_magnitude x : x<=B reflection_limit ->
  bpow radix2 1024-bpow radix2 970<=gaussian_erfcx x.
Proof.
  intros X. eapply Rle_trans;[apply gaussian_overflow_boundary|].
  apply gaussian_small_monotone;[exact X|].
  pose proof reflection_limit_value. pose proof(bpow_gt_0 radix2 (-20));lra.
Qed.
