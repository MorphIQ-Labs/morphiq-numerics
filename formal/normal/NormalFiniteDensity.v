(** Density in the finite underflow band, including the final grid test. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Binary64 Require Import Binary64Add IEEE64.
Require Import StageGappa ErfcxProduct NormalGaussianKernel NormalGaussianRange
  NormalDensityMantissa NormalAccurateDensity NormalFiniteRound.
Open Scope R_scope.

Lemma normal_finite_density_exponent x : finite x -> 37<=B x<=39 ->
  let '(_,_,k):=normal_density_mantissa64 x in (-1100<=k<= -980)%Z.
Proof.
  intros F X;pose proof(normal_gaussian_finite_tail_exponent x F X)as K.
  unfold normal_density_mantissa64;destruct(normal_gaussian64 x)as[[a b]k].
  destruct normal_density_constant64 as[c d];destruct(product64 a b c d);exact K.
Qed.

Lemma normal_finite_low_ratio h l : 0<h -> -bpow radix2(-51)<=l/h<=bpow radix2(-51) ->
  Rabs l<=bpow radix2(-51)*h.
Proof.
  intros H L;assert(Identity : l=(l/h)*h)by(field;lra).
  rewrite Identity at 1;rewrite Rabs_mult,(Rabs_pos_eq h)by lra.
  apply Rmult_le_compat_r;[lra|apply Rabs_le;exact L].
Qed.

Definition normal_finite_density64 x :=
  let '(h,l,k):=normal_density_mantissa64 x in normal_finite_scaled_fast64 h l (k+600).

Theorem normal_finite_density_ieee x v : finite x -> 37<=B x<=39 ->
  normal_finite_density64 x=Some v -> finite v /\ B v=rndF(normal_density(B x)).
Proof.
  intros F X;pose proof(normal_density_mantissa_extended_ieee x F
    ltac:(bpow_num_all;split;lra))as Density.
  pose proof(normal_finite_density_exponent x F X)as Exponent.
  unfold normal_finite_density64;destruct(normal_density_mantissa64 x)as[[h l]k].
  destruct Density as[Fh [Fl [K [H [Ratio [Norm Error]]]]]].
  assert(Low : Rabs(B l)<=bpow radix2(-51)*B h)by(apply normal_finite_low_ratio;lra||exact Ratio).
  intros Decision;destruct(normal_finite_scaled_fast_ieee h l (k+600)
    (normal_density(B x)/bpow radix2 k)v Fh Fl
    ltac:(bpow_num_all;split;lra)Low Norm ltac:(lia))as[Fv V].
  - rewrite Rabs_minus_sym;apply Rle_trans with(bpow radix2(-69));[exact Error|bpow_num_all;nra].
  - exact Decision.
  - split;[exact Fv|rewrite V;replace(k+600-600)%Z with k by ring].
    f_equal;field;apply Rgt_not_eq,bpow_gt_0.
Qed.
