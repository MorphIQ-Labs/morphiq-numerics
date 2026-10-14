(** Forward Gaussian-integral bounds used when reflection omits its small
    positive correction. No improper-integral identity is assumed. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Coquelicot Require Import Coquelicot.
From Flocq Require Import Core.
From Interval Require Import Tactic.
Require Import StageGappa ErfcxConstants ErfcxTaylorODE ErfcxGaussianTarget
  ErfcxTaylorLocal ErfcxAccurateCenterModel ErfcxAccurateCenterBounds.
Open Scope R_scope.
Lemma gaussian_forward_integral c h : 0<=c -> 0<=h ->
  Rabs(RInt(shifted_gaussian c h)0 1)<=exp(-c*c).
Proof.
  intros C H.
  assert (Point : forall t,0<=t<=1 -> Rabs(shifted_gaussian c h t)<=exp(-c*c)).
  { intros t T. unfold shifted_gaussian,gaussian.
    rewrite Rabs_pos_eq by (apply Rlt_le,exp_pos).
    assert (HT : 0<=h*t) by (apply Rmult_le_pos;lra).
    assert (Order : -(c+h*t)*(c+h*t)<= -c*c) by nra.
    destruct(Rle_lt_or_eq_dec _ _ Order) as [Lt|Eq].
    - apply Rlt_le,exp_increasing;exact Lt.
    - rewrite Eq;lra. }
  pose proof(@norm_RInt_le_const R_NormedModule (shifted_gaussian c h)0 1
    (RInt(shifted_gaussian c h)0 1)(exp(-c*c)) ltac:(lra) Point
    (RInt_correct _ _ _ (shifted_gaussian_integrable c h 0 1))) as Bound.
  change (Rabs(RInt(shifted_gaussian c h)0 1)<=(1-0)*exp(-c*c)) in Bound;lra.
Qed.
Lemma gaussian_forward_bound c h : 0<=c -> 0<=h ->
  Rabs(gaussian_erfcx(c+h))<=exp((c+h)*(c+h))*exp(-c*c)*
    (Rabs(gaussian_erfcx c)+2*Rabs inv_sqrt_pi*h).
Proof.
  intros C H. pose proof(gaussian_forward_integral c h C H) as Integral.
  rewrite gaussian_local_variation,local_integral_scale.
  assert (Split : exp((c+h)*(c+h)-c*c)=exp((c+h)*(c+h))*exp(-c*c))
    by (rewrite <- exp_plus;f_equal;ring).
  rewrite Split.
  eapply Rle_trans;[apply Rabs_triang|].
  rewrite Rabs_Ropp,!Rabs_mult,(Rabs_pos_eq 2),(Rabs_pos_eq h),
    (Rabs_pos_eq(exp((c+h)*(c+h)))),(Rabs_pos_eq(exp(-c*c)))
    by (try lra;apply Rlt_le,exp_pos).
  assert (Factor : 0<=2*Rabs inv_sqrt_pi*h*exp((c+h)*(c+h)))
    by (apply Rmult_le_pos;[apply Rmult_le_pos;[pose proof(Rabs_pos inv_sqrt_pi);lra|exact H]|apply Rlt_le,exp_pos]).
  pose proof(Rmult_le_compat_l _ _ _ Factor Integral). nra.
Qed.
Lemma gaussian_at_eight_bound : Rabs(gaussian_erfcx 8)<=512.
Proof.
  destruct(accurate_center_bounds 145 ltac:(lia)) as [C F].
  assert (Center : accurate_center 145=65/8).
  { unfold accurate_center,center_numerator,center_denominator;vm_compute;field. }
  rewrite Center in C,F. replace 8 with (65/8- /8) by field.
  apply gaussian_local_bound;[exact C|apply Rabs_le;split;lra|apply Rabs_le;lra].
Qed.
Theorem gaussian_omitted_relative x : 8<=x<=27 ->
  Rabs(gaussian_erfcx x)<=exp(x*x)*bpow radix2 (-80).
Proof.
  intros X. pose proof(gaussian_forward_bound 8 (x-8) ltac:(lra) ltac:(lra)) as Bound.
  replace (8+(x-8)) with x in Bound by ring.
  replace (-(8:R)*8) with (-64) in Bound by ring.
  pose proof gaussian_at_eight_bound as Center.
  assert (Cs : Rabs inv_sqrt_pi<=1) by (unfold inv_sqrt_pi;interval with(i_prec 80)).
  assert (Factor : Rabs(gaussian_erfcx 8)+2*Rabs inv_sqrt_pi*(x-8)<=550)
    by (pose proof(Rabs_pos inv_sqrt_pi);nra).
  eapply Rle_trans;[exact Bound|].
  replace (exp(x*x)*exp(-64)*(Rabs(gaussian_erfcx 8)+2*Rabs inv_sqrt_pi*(x-8))) with
    (exp(x*x)*(exp(-64)*(Rabs(gaussian_erfcx 8)+2*Rabs inv_sqrt_pi*(x-8)))) by ring.
  apply Rmult_le_compat_l;[apply Rlt_le,exp_pos|].
  eapply Rle_trans with (exp(-64)*550).
  - apply Rmult_le_compat_l;[apply Rlt_le,exp_pos|exact Factor].
  - bpow_num;interval with(i_prec 200).
Qed.
