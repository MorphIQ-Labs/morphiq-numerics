(** Monotonicity over the negative branch and the neighborhood of zero. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Coquelicot Require Import Coquelicot.
From Flocq Require Import Core.
From Interval Require Import Tactic.
Require Import StageGappa ErfcxConstants ErfcxGaussianTarget ErfcxGaussianReflection ErfcxTaylorLocal.
Open Scope R_scope.
Lemma gaussian_small_derivative_negative x : x<=bpow radix2 (-20) ->
  2*x*gaussian_erfcx x-2*inv_sqrt_pi<0.
Proof.
  intros X. assert (Cs : /2<=inv_sqrt_pi) by (unfold inv_sqrt_pi;interval with(i_prec 80)).
  destruct(Rle_dec x 0) as [Negative|Positive].
  - pose proof(gaussian_negative_at_least_one x Negative);nra.
  - assert (Bound : Rabs(gaussian_erfcx x)<=512).
    { replace x with (0+x) by ring;apply gaussian_local_bound.
      - rewrite Rabs_R0;lra.
      - apply Rabs_le;bpow_num_all;split;lra.
      - rewrite gaussian_erfcx_at_zero,Rabs_R1;lra. }
    apply Rabs_le_inv in Bound;bpow_num_all;nra.
Qed.
Theorem gaussian_small_monotone a b : a<=b -> b<=bpow radix2 (-20) ->
  gaussian_erfcx b<=gaussian_erfcx a.
Proof.
  intros Order B. destruct(Rle_lt_or_eq_dec _ _ Order) as [Lt|Eq];[|rewrite Eq;lra].
  destruct(MVT_cor2 gaussian_erfcx (fun x=>2*x*gaussian_erfcx x-2*inv_sqrt_pi) a b Lt)
    as [c [Difference Range]].
  - intros c C. apply is_derive_Reals;apply gaussian_erfcx_derivative.
  - pose proof(gaussian_small_derivative_negative c ltac:(lra));nra.
Qed.
