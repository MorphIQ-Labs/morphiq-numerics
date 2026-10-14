(** The omitted scaled-tail correction derived from the defining integral. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 Encodings.
Require Import StageGappa ErfcxConstants ErfcxTailIntegral ErfcxScaledFast.
Open Scope R_scope.

(** Substituting u=2*x*v in (2/sqrt(pi))*integral exp(-v^2-2*x*v) dv
    gives this normalized positive-input representation. *)
Definition positive_erfcx x := (inv_sqrt_pi/x)*tail_integral ((/x)*(/x)).
Definition erfcx_scaled_limit : f64 := b64_of_bits 8646428874712260188.

Lemma erfcx_scaled_limit_ok : finite erfcx_scaled_limit /\
  B erfcx_scaled_limit=8524789415648860*bpow radix2 844 /\
  3*bpow radix2 895<=B erfcx_scaled_limit.
Proof.
  assert (V : B erfcx_scaled_limit=8524789415648860*bpow radix2 844) by reflexivity.
  split.
  - exact (bits_finite 8646428874712260188 false 8524789415648860 844 eq_refl).
  - split; [exact V | rewrite V; bpow_num; lra].
Qed.

Lemma scaled_tail_analytic_correction x : 3*bpow radix2 895<=x ->
  0<=1-tail_integral ((/x)*(/x))<=bpow radix2 (-1794).
Proof.
  intros X.
  assert (Xpos : 0<x) by (pose proof (bpow_gt_0 radix2 895); lra).
  assert (Square : bpow radix2 1793<=x*x).
  { replace (bpow radix2 1793) with (8*(bpow radix2 895*bpow radix2 895)).
    - pose proof (bpow_gt_0 radix2 895). nra.
    - change 8 with (bpow radix2 3). rewrite <- !bpow_plus. reflexivity. }
  assert (Reciprocal : 0<=(/x)*(/x)<=bpow radix2 (-1793)).
  { split; [pose proof (Rinv_0_lt_compat x Xpos); nra | ].
    replace ((/x)*(/x)) with (/(x*x)) by (field; lra).
    replace (bpow radix2 (-1793)) with (/bpow radix2 1793) by (rewrite <- bpow_opp; reflexivity).
    apply Rinv_le_contravar; [apply bpow_gt_0 | exact Square]. }
  destruct (tail_integral_correction ((/x)*(/x)) (proj1 Reciprocal)) as [Low High].
  split; [exact Low | apply Rle_trans with (((/x)*(/x))/2); [exact High | ]].
  replace (bpow radix2 (-1794)) with (bpow radix2 (-1793)/2).
  - lra.
  - unfold Rdiv. change (/2) with (bpow radix2 (-1)). rewrite <- bpow_plus. reflexivity.
Qed.

Theorem tail_scaled_fast_analytic_ieee x v : finite x -> B erfcx_scaled_limit<B x ->
  tail_scaled_fast64 x=Some v -> finite v /\ B v=rndF (positive_erfcx (B x)).
Proof.
  intros Fx X Decision. destruct erfcx_scaled_limit_ok as (Ft & Value & Lower).
  assert (Large : bpow radix2 896<=B x).
  { apply Rle_trans with (3*bpow radix2 895); [ | lra].
    replace (bpow radix2 896) with (2*bpow radix2 895)
      by (change 2 with (bpow radix2 1); rewrite <- bpow_plus; reflexivity).
    pose proof (bpow_gt_0 radix2 895). lra. }
  pose proof (scaled_tail_analytic_correction (B x) ltac:(lra)) as Correction.
  destruct (tail_scaled_fast_ieee x (1-tail_integral ((/B x)*(/B x))) v Fx Large Correction Decision) as [Fv V].
  replace (1-(1-tail_integral ((/B x)*(/B x)))) with (tail_integral ((/B x)*(/B x))) in V by ring.
  split; [exact Fv | exact V].
Qed.
