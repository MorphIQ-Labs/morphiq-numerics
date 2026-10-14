(** Centered normal CDF: integrated Gaussian polynomial and its remainder.
    This is an analytic component, not an IEEE entry-point theorem. *)
From Coq Require Import Reals Lia Lra Psatz.
From Coquelicot Require Import Coquelicot.
From Interval Require Import Tactic.
From Flocq Require Import Core.
Require Import StageGappa ErfcxTaylorODE ErfcxGaussianSeries ErfcxFactorial.
Open Scope R_scope.

Definition normal_density_constant : R := /sqrt(2*PI).
Definition normal_shape x := RInt (gaussian_scaled (x/sqrt 2)) 0 1.
Definition normal_center x := normal_density_constant*x*normal_shape x.
Definition normal_center_polynomial n x :=
  normal_density_constant*x*gaussian_sum n (x/sqrt 2).

Lemma normal_shape_range x : Rabs x<=/2 -> 7/8<=normal_shape x<=1.
Proof.
  intros X. apply Rabs_le_inv in X.
  assert (Point : forall u,0<=u<=1 -> 7/8<=gaussian_scaled (x/sqrt 2) u<=1).
  { intros u U. unfold gaussian_scaled,gaussian.
    split.
    - interval with (i_prec 80).
    - assert (E : -(x/sqrt 2*u)*(x/sqrt 2*u)<=0) by nra.
      destruct (Rle_lt_or_eq_dec _ _ E) as [Lt|Eq].
      + rewrite <- exp_0;apply Rlt_le,exp_increasing;exact Lt.
      + rewrite Eq,exp_0;lra. }
  assert (Lower : RInt (fun _ : R=>7/8) 0 1<=normal_shape x).
  { apply RInt_le;[lra|apply ex_RInt_const|apply gaussian_scaled_integrable|].
    intros u U;exact(proj1(Point u ltac:(lra))). }
  assert (Upper : normal_shape x<=RInt (fun _ : R=>1) 0 1).
  { apply RInt_le;[lra|apply gaussian_scaled_integrable|apply ex_RInt_const|].
    intros u U;exact(proj2(Point u ltac:(lra))). }
  rewrite RInt_const in Lower,Upper.
  change ((1-0)*(7/8)<=normal_shape x) in Lower.
  change (normal_shape x<=(1-0)*1) in Upper. split;lra.
Qed.

Theorem normal_center_polynomial_error n x :
  Rabs(normal_center x-normal_center_polynomial n x)<=
    normal_density_constant*Rabs x*((x*x/2)^S n/INR(fact(S n))).
Proof.
  unfold normal_center,normal_center_polynomial,normal_shape.
  replace (normal_density_constant*x*RInt(gaussian_scaled(x/sqrt 2))0 1-
    normal_density_constant*x*gaussian_sum n (x/sqrt 2)) with
    (normal_density_constant*x*(RInt(gaussian_scaled(x/sqrt 2))0 1-gaussian_sum n (x/sqrt 2))) by ring.
  rewrite !Rabs_mult,(Rabs_pos_eq normal_density_constant).
  2: unfold normal_density_constant;left;interval with(i_prec 80).
  assert (Square : (x/sqrt 2)*(x/sqrt 2)=x*x/2).
  { assert (S : sqrt 2*sqrt 2=2) by (apply sqrt_sqrt;lra).
    assert (P : sqrt 2<>0) by (interval with(i_prec 80)).
    replace (x/sqrt 2*(x/sqrt 2)) with (x*x/(sqrt 2*sqrt 2)) by (field;exact P).
    rewrite S;reflexivity. }
  pose proof(gaussian_integral_remainder n (x/sqrt 2)) as Error.
  rewrite Square in Error.
  apply Rmult_le_compat_l;[|exact Error].
  apply Rmult_le_pos;[unfold normal_density_constant;left;interval with(i_prec 80)|apply Rabs_pos].
Qed.

Theorem normal_center_degree12_error x : Rabs x<=/2 ->
  Rabs(normal_center x-normal_center_polynomial 12 x)<=
    normal_density_constant*Rabs x*/2^71.
Proof.
  intros X. pose proof X as Bounds;apply Rabs_le_inv in Bounds.
  eapply Rle_trans;[apply normal_center_polynomial_error|].
  apply Rmult_le_compat_l.
  - apply Rmult_le_pos;[unfold normal_density_constant;left;interval with(i_prec 80)|apply Rabs_pos].
  - binary_factorials. interval with(i_prec 100).
Qed.
