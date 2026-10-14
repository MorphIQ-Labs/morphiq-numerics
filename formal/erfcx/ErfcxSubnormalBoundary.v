(** The last normal-output input is separated from the real normal/subnormal
    boundary, even with the scaled tail's omitted correction. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 Encodings.
From Interval Require Import Tactic.
Require Import StageGappa ErfcxConstants.
Open Scope R_scope.
Definition erfcx_subnormal_limit : f64 := b64_of_bits 9205935806714387310.

Lemma erfcx_subnormal_limit_ok : finite erfcx_subnormal_limit /\
  B erfcx_subnormal_limit=5081767996463982*bpow radix2 969 /\
  bpow radix2 1021<=B erfcx_subnormal_limit.
Proof.
  assert (V : B erfcx_subnormal_limit=5081767996463982*bpow radix2 969) by reflexivity.
  split.
  - exact (bits_finite 9205935806714387310 false 5081767996463982 969 eq_refl).
  - split; [exact V | rewrite V; bpow_num; lra].
Qed.

Lemma erfcx_subnormal_predecessor :
  pred radix2 (FLT_exp emin prec) (B erfcx_subnormal_limit)=5081767996463981*bpow radix2 969.
Proof.
  destruct erfcx_subnormal_limit_ok as (F & V & Lower).
  destruct (bits_down erfcx_subnormal_limit F ltac:(apply Rle_trans with (bpow radix2 1021);
    [apply bpow_le; lia | exact Lower])) as [_ P].
  unfold emin, prec. rewrite <- P. reflexivity.
Qed.

Lemma erfcx_normal_boundary_margin :
  /2*(5081767996463981*bpow radix2 (-52))<=inv_sqrt_pi*(1-bpow radix2 (-100)).
Proof. unfold inv_sqrt_pi. bpow_num. interval with (i_prec 128). Qed.

Theorem erfcx_normal_tail_lower x correction : finite x -> 0<B x ->
  B x<B erfcx_subnormal_limit -> 0<=correction<=bpow radix2 (-1794) ->
  bpow radix2 (-1022)<=(inv_sqrt_pi/B x)*(1-correction).
Proof.
  intros Fx X Below Corr.
  pose proof (pred_ge_gt radix2 (FLT_exp emin prec) (B x) (B erfcx_subnormal_limit)
    (B_fmt x) (B_fmt erfcx_subnormal_limit) Below) as Previous.
  rewrite erfcx_subnormal_predecessor in Previous.
  assert (Reduced : B x*bpow radix2 (-1021)<=5081767996463981*bpow radix2 (-52)).
  { apply Rmult_le_compat_r with (r:=bpow radix2 (-1021)) in Previous; [ | apply bpow_ge_0].
    rewrite Rmult_assoc, <- bpow_plus in Previous. exact Previous. }
  assert (Small : correction<=bpow radix2 (-100)).
  { apply Rle_trans with (bpow radix2 (-1794)); [lra | apply bpow_le; lia]. }
  pose proof erfcx_normal_boundary_margin as Margin.
  pose proof inv_sqrt_pi_positive as Positive.
  assert (Bound : /2*(B x*bpow radix2 (-1021))<=inv_sqrt_pi*(1-correction)) by nra.
  assert (Id : /2*(B x*bpow radix2 (-1021))=bpow radix2 (-1022)*B x).
  { change (/2) with (bpow radix2 (-1)). rewrite Rmult_comm, Rmult_assoc, <- bpow_plus.
    change (-1021 + -1)%Z with (-1022)%Z. ring. }
  rewrite Id in Bound. apply Rmult_le_reg_r with (B x); [exact X | ].
  replace (inv_sqrt_pi/B x*(1-correction)*B x) with (inv_sqrt_pi*(1-correction)) by (field; lra).
  exact Bound.
Qed.
