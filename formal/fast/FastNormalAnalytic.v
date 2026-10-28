(** Absolute Gaussian-tail sensitivity for the two rounded input arguments.
    The damping factors are retained: an undamped relative tail estimate is
    insufficient for the public absolute probability contract. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
Require Import StageGappa Exp2Stages ErfcxGaussianTarget NormalErfcxSensitivity
  NormalErfcxLinear NormalErfcxFastScaled NormalTailAnalytic.
Open Scope R_scope.

Theorem fast_normal_perturbation a z t : 0<a<=8 -> 0<z ->
  Rabs(z-a/sqrt 2)<=3*bpow radix2(-53)*(a/sqrt 2) ->
  Rabs(t+a*a/2)<=bpow radix2(-53)*(a*a/2) ->
  Rabs(exp t*gaussian_erfcx z/2-normal_tail a)<=3*bpow radix2(-53).
Proof.
  intros A Z Zerror Terror.
  set(y:=a/sqrt 2).
  set(q:=a*a/2).
  assert(Y : 0<y<=6).
  { unfold y;split.
    - apply Rdiv_lt_0_compat;[exact(proj1 A)|interval with(i_prec 80)].
    - interval with(i_prec 80). }
  assert(Q : 0<=q<=32)by(unfold q;nra).
  assert(QY : q=y*y)by(unfold q,y;symmetry;apply normal_sqrt_two_square).
  fold y in Zerror;fold q in Terror.
  pose proof(normal_erfcx_lipschitz y z (proj1 Y)Z)as FactorError.
  assert(Fz : 0<gaussian_erfcx z<=1).
  { split;[apply normal_erfcx_positive|apply normal_erfcx_unit_upper];exact Z. }
  assert(Dsmall : Rabs(t+q)<=/1024).
  { eapply Rle_trans;[exact Terror|bpow_num_all;nra]. }
  pose proof(exp_local_lipschitz (t+q)0 Dsmall ltac:(rewrite Rabs_R0;lra))as ExpError.
  rewrite exp_0,Rminus_0_r in ExpError.
  assert(Identity : exp t=exp(-q)*exp(t+q)).
  { rewrite <-exp_plus;f_equal;ring. }
  assert(ExpDifference : Rabs(exp t-exp(-q))<=2*bpow radix2(-53)*q*exp(-q)).
  { rewrite Identity;replace(exp(-q)*exp(t+q)-exp(-q))with(exp(-q)*(exp(t+q)-1))by (unfold Rdiv;ring).
    rewrite Rabs_mult,(Rabs_pos_eq(exp(-q)))by(left;apply exp_pos).
    eapply Rle_trans with(exp(-q)*(2*Rabs(t+q))).
    - apply Rmult_le_compat_l;[left;apply exp_pos|exact ExpError].
    - replace(2*bpow radix2(-53)*q*exp(-q))with(exp(-q)*(2*(bpow radix2(-53)*q)))by (unfold Rdiv;ring).
      apply Rmult_le_compat_l;[left;apply exp_pos|lra]. }
  assert(Qdamped : q*exp(-q)<=1).
  { interval with(i_prec 80,i_bisect q). }
  assert(Ydamped : y*exp(-q)<=2/3).
  { rewrite QY;interval with(i_prec 80,i_bisect y). }
  assert(ExponentPart : Rabs((exp t-exp(-q))*gaussian_erfcx z/2)<=bpow radix2(-53)).
  { replace((exp t-exp(-q))*gaussian_erfcx z/2)with
      ((exp t-exp(-q))*(gaussian_erfcx z/2))by (unfold Rdiv;ring).
    rewrite Rabs_mult,(Rabs_pos_eq(gaussian_erfcx z/2))by lra.
    assert(Scale : Rabs(exp t-exp(-q))*(gaussian_erfcx z/2)<=Rabs(exp t-exp(-q))/2).
    { replace(Rabs(exp t-exp(-q))/2)with(Rabs(exp t-exp(-q))*(/2))by (unfold Rdiv;ring).
      apply Rmult_le_compat_l;[apply Rabs_pos|lra]. }
    bpow_num_all;nra. }
  assert(ArgumentPart : Rabs(exp(-q)*(gaussian_erfcx z-gaussian_erfcx y)/2)<=2*bpow radix2(-53)).
  { replace(exp(-q)*(gaussian_erfcx z-gaussian_erfcx y)/2)with
      ((exp(-q)/2)*(gaussian_erfcx z-gaussian_erfcx y))by (unfold Rdiv;ring).
    rewrite Rabs_mult,(Rabs_pos_eq(exp(-q)/2))by(pose proof(exp_pos(-q));lra).
    assert(Scale : (exp(-q)/2)*Rabs(gaussian_erfcx z-gaussian_erfcx y)<=
      (exp(-q)/2)*(2*Rabs(z-y))).
    { apply Rmult_le_compat_l;[pose proof(exp_pos(-q));lra|exact FactorError]. }
    assert(Scale2 : (exp(-q)/2)*(2*Rabs(z-y))<=
      (exp(-q)/2)*(2*(3*bpow radix2(-53)*y))).
    { apply Rmult_le_compat_l;[pose proof(exp_pos(-q));lra|lra]. }
    bpow_num_all;nra. }
  unfold normal_tail;fold y.
  replace(-a*a/2)with(-q)by(unfold q,Rdiv;ring).
  replace(exp t*gaussian_erfcx z/2-exp(-q)*gaussian_erfcx y/2)with
    ((exp t-exp(-q))*gaussian_erfcx z/2+exp(-q)*(gaussian_erfcx z-gaussian_erfcx y)/2)by (unfold Rdiv;ring).
  eapply Rle_trans;[apply Rabs_triang|];lra.
Qed.

Theorem fast_normal_perturbed_range a z t : 0<a<=8 -> 0<z ->
  Rabs(t+a*a/2)<=bpow radix2(-53)*(a*a/2) ->
  0<exp t*gaussian_erfcx z/2<=51/100.
Proof.
  intros A Z Error.
  assert(Q : 0<=a*a/2<=32)by nra.
  pose proof(Rabs_le_inv _ _ Error)as T.
  assert(Tupper : t<=32*bpow radix2(-53))by(bpow_num_all;nra).
  assert(Eupper : exp t<=102/100).
  { eapply Rle_trans with(exp(32*bpow radix2(-53))).
    - apply exp_le;exact Tupper.
    - bpow_num;interval with(i_prec 80). }
  pose proof(normal_erfcx_positive z Z)as Fpos.
  pose proof(normal_erfcx_unit_upper z Z)as Fupper.
  pose proof(exp_pos t)as Epos.
  assert(Product : exp t*gaussian_erfcx z<=(102/100)*1).
  { apply Rmult_le_compat;try lra. }
  split;[apply Rdiv_lt_0_compat;[apply Rmult_lt_0_compat;assumption|lra]|nra].
Qed.
