(** The complete fixed-coefficient ratio fits the existing 10u far-tail budget. *)
From Coq Require Import Reals Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Gappa Require Import Gappa_library.
From Binary64 Require Import IEEE64 RoundingGaps.
Require Import StageGappa ErfcxConstants ErfcxGaussianTarget NormalErfcxSensitivity
  FastCdfConstants FastCdfFarConstants FastCdfFarApprox FastCdfFarArithmetic FastCdf.
Open Scope R_scope.

Lemma cdf_far_ideal_poly a : 0<a -> fast_cdf_far_ratio_ideal a =
  B cdf_far_scale/a*cdf_far_poly (1/(a*a)).
Proof.
  intros A. unfold fast_cdf_far_ratio_ideal,cdf_far_poly,cdf_far_words.
  cbn [cdf_horner]. field; lra.
Qed.

Lemma cdf_far_ideal_scale a : 0<a -> fast_cdf_far_ratio_ideal a =
  (B cdf_far_scale/(sqrt 2*inv_sqrt_pi))*cdf_far_real (a/sqrt 2).
Proof.
  intros A. rewrite cdf_far_ideal_poly by lra. unfold cdf_far_real.
  assert (S : sqrt 2*sqrt 2=2) by (apply sqrt_def; lra).
  assert (Sp : 0<sqrt 2) by (apply sqrt_lt_R0;lra).
  pose proof inv_sqrt_pi_positive as I.
  replace (1/(2*(a/sqrt 2)*(a/sqrt 2))) with (1/(a*a)).
  - field; lra.
  - replace (2*(a/sqrt 2)*(a/sqrt 2)) with (a*a).
    + reflexivity.
    + apply (Rmult_eq_reg_r (sqrt 2*sqrt 2)).
      * field_simplify; nra.
      * nra.
Qed.

Lemma cdf_far_scale_error :
  Rabs(B cdf_far_scale/(sqrt 2*inv_sqrt_pi)-1)<=bpow radix2(-53).
Proof.
  rewrite cdf_far_scale_val. unfold inv_sqrt_pi. bpow_num.
  interval with (i_prec 160).
Qed.

Theorem fast_cdf_far_ratio_ok a : finite a -> 8<=B a<=45/2 ->
  finite(fast_cdf_far_ratio64 a) /\
  Rabs(B(fast_cdf_far_ratio64 a)-gaussian_erfcx (B a/sqrt 2))
    <=10*bpow radix2(-53)*gaussian_erfcx (B a/sqrt 2).
Proof.
  intros Fa A.
  destruct (fast_cdf_far_ratio_ieee a Fa A) as [Fr Vr]. split;[exact Fr|].
  destruct (fast_cdf_far_ratio_certificate (B a) (B_fmt a) A)
    as [[e [Be Ee]] [Rr Ir]].
  assert (Ar : Rabs(fast_cdf_far_ratio_value (B a)-fast_cdf_far_ratio_ideal (B a))
    <=6*bpow radix2(-53)*fast_cdf_far_ratio_ideal (B a)).
  { rewrite Ee. replace (fast_cdf_far_ratio_ideal (B a)*(1+e)-fast_cdf_far_ratio_ideal (B a))
      with (fast_cdf_far_ratio_ideal (B a)*e) by ring.
    rewrite Rabs_mult,Rabs_pos_eq by lra.
    assert (E : Rabs e<=6*bpow radix2(-53)).
    { cbn [lower upper] in Be.
      change (float2R (Float2 (-3) (-52))) with (IZR (-3)*bpow radix2(-52)) in Be.
      change (float2R (Float2 3 (-52))) with (IZR 3*bpow radix2(-52)) in Be.
      apply Rabs_le. revert Be; bpow_num; simpl; lra. }
    nra. }
  set (y:=B a/sqrt 2).
  assert (Sp : 0<sqrt 2) by (apply sqrt_lt_R0;lra).
  assert (S : sqrt 2*sqrt 2=2) by (apply sqrt_def;lra).
  assert (Y : 0<=y<=16).
  { unfold y. split;[apply Rlt_le,Rdiv_lt_0_compat;lra|].
    apply (Rmult_le_reg_r (sqrt 2));[exact Sp|].
    rewrite cdf_sqrt2_cancel. interval. }
  assert (Square : y*y=(B a*B a)/2).
  { unfold y. replace ((B a/sqrt 2)*(B a/sqrt 2))
      with ((B a*B a)/(sqrt 2*sqrt 2)) by (field;lra).
    rewrite S. reflexivity. }
  pose proof (cdf_far_poly_approx y Y ltac:(rewrite Square;nra)) as Approx.
  assert (Ypos : 0<y) by (unfold y;apply Rdiv_lt_0_compat;lra).
  assert (Ep : 0<gaussian_erfcx y) by (apply normal_erfcx_positive;lra).
  assert (Rp : 0<=cdf_far_real y).
  { pose proof (Rabs_le_inv _ _ Approx). bpow_num_all; nra. }
  assert (Sc : Rabs(fast_cdf_far_ratio_ideal (B a)-cdf_far_real y)
    <=bpow radix2(-53)*cdf_far_real y).
  { rewrite cdf_far_ideal_scale by lra. fold y.
    replace (B cdf_far_scale/(sqrt 2*inv_sqrt_pi)*cdf_far_real y-cdf_far_real y)
      with ((B cdf_far_scale/(sqrt 2*inv_sqrt_pi)-1)*cdf_far_real y) by ring.
    rewrite Rabs_mult,(Rabs_pos_eq (cdf_far_real y)) by exact Rp.
    apply Rmult_le_compat_r;[exact Rp|exact cdf_far_scale_error]. }
  pose proof (bpow_gt_0 radix2(-53)) as U.
  pose proof (cdf_rel_chain _ _ _ _ _ Sc Approx ltac:(lra) ltac:(lra) ltac:(lra)) as Ideal.
  apply (cdf_rel_weaken _ _ _ (3*bpow radix2(-53))) in Ideal;[|lra|bpow_num;nra].
  pose proof (cdf_rel_chain _ _ _ _ _ Ar Ideal ltac:(lra) ltac:(lra) ltac:(lra)) as Total.
  rewrite Vr. fold y. eapply cdf_rel_weaken;[lra| |exact Total]. bpow_num;nra.
Qed.
