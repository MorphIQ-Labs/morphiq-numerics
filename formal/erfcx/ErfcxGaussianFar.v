(** A small relative correction suffices for far-negative reflection. This
    avoids assuming an identity between finite and improper integrals. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Coquelicot Require Import Coquelicot.
From Flocq Require Import Core.
From Interval Require Import Tactic.
Require Import StageGappa ErfcxConstants ErfcxTaylorODE ErfcxGaussianTarget
  ErfcxTaylorLocal ErfcxAccurateCenterModel ErfcxAccurateCenterBounds.
Open Scope R_scope.
Lemma gaussian_at_sixteen_bound : Rabs(gaussian_erfcx 16)<=512.
Proof.
  destruct(accurate_center_bounds 176 ltac:(lia)) as [C F].
  assert (Center : accurate_center 176=127/8).
  { unfold accurate_center,center_numerator,center_denominator;vm_compute;field. }
  rewrite Center in C,F.
  replace 16 with (127/8+ /8) by field.
  apply gaussian_local_bound;[exact C|rewrite Rabs_pos_eq;lra|apply Rabs_le;lra].
Qed.
Lemma gaussian_far_integral h : 0<=h<=11 ->
  Rabs(RInt(shifted_gaussian 16 h)0 1)<=exp(-256).
Proof.
  intros H.
  assert (Point : forall t,0<=t<=1 -> Rabs(shifted_gaussian 16 h t)<=exp(-256)).
  { intros t T. unfold shifted_gaussian,gaussian.
    rewrite Rabs_pos_eq by (apply Rlt_le,exp_pos).
    destruct(Req_dec (h*t) 0) as [Z|NZ].
    - rewrite Z. replace (-(16+0)*(16+0)) with (-256) by ring;lra.
    - apply Rlt_le,exp_increasing. assert (0<h*t) by nra. nra. }
  pose proof(@norm_RInt_le_const R_NormedModule (shifted_gaussian 16 h)0 1
    (RInt(shifted_gaussian 16 h)0 1)(exp(-256)) ltac:(lra) Point
    (RInt_correct _ _ _ (shifted_gaussian_integrable 16 h 0 1))) as Bound.
  change (Rabs(RInt(shifted_gaussian 16 h)0 1)<=(1-0)*exp(-256)) in Bound;lra.
Qed.
Theorem gaussian_far_bound x : 16<=x<=27 ->
  Rabs(gaussian_erfcx x)<=exp(x*x)*bpow radix2 (-350).
Proof.
  intros X. pose proof(gaussian_far_integral (x-16) ltac:(lra)) as Integral.
  pose proof gaussian_at_sixteen_bound as Center.
  assert (Cs : Rabs inv_sqrt_pi<=1) by (unfold inv_sqrt_pi;interval with (i_prec 80)).
  pose proof(gaussian_local_variation 16 (x-16)) as Variation.
  replace (16+(x-16)) with x in Variation by ring.
  rewrite local_integral_scale in Variation.
  replace (16+(x-16)) with x in Variation by ring.
  assert (Split : exp(x*x-16*16)=exp(x*x)*exp(-256)).
  { rewrite <- exp_plus;f_equal;ring. }
  rewrite Split in Variation.
  assert (Error : Rabs(exp(-256)*gaussian_erfcx 16-
    2*inv_sqrt_pi*(x-16)*RInt(shifted_gaussian 16 (x-16))0 1)<=bpow radix2 (-350)).
  { eapply Rle_trans;[apply Rabs_triang|].
    rewrite Rabs_Ropp,!Rabs_mult,(Rabs_pos_eq 2),(Rabs_pos_eq(exp(-256))),
      (Rabs_pos_eq(x-16)) by (try lra;apply Rlt_le,exp_pos).
    assert (First : exp(-256)*Rabs(gaussian_erfcx 16)<=exp(-256)*512)
      by (apply Rmult_le_compat_l;[apply Rlt_le,exp_pos|exact Center]).
    assert (Second : 2*Rabs inv_sqrt_pi*(x-16)*Rabs(RInt(shifted_gaussian 16 (x-16))0 1)<=22*exp(-256)).
    { assert (0<=2*Rabs inv_sqrt_pi*(x-16)<=22) by (pose proof(Rabs_pos inv_sqrt_pi);nra).
      pose proof(Rabs_pos(RInt(shifted_gaussian 16 (x-16))0 1));nra. }
    eapply Rle_trans with (534*exp(-256));[lra|]. bpow_num;interval with (i_prec 400). }
  rewrite Variation.
  replace (exp(x*x)*exp(-256)*gaussian_erfcx 16-
    2*inv_sqrt_pi*(x-16)*(exp(x*x)*RInt(shifted_gaussian 16 (x-16))0 1)) with
    (exp(x*x)*(exp(-256)*gaussian_erfcx 16-
    2*inv_sqrt_pi*(x-16)*RInt(shifted_gaussian 16 (x-16))0 1)) by ring.
  rewrite Rabs_mult,(Rabs_pos_eq(exp(x*x))) by (apply Rlt_le,exp_pos).
  apply Rmult_le_compat_l;[apply Rlt_le,exp_pos|exact Error].
Qed.
