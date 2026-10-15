(** The erfcx tail is the complement of the centered normal integral. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Coquelicot Require Import Coquelicot.
From Flocq Require Import Core.
From Interval Require Import Tactic.
Require Import ErfcxConstants ErfcxTaylorODE ErfcxGaussianSeries ErfcxGaussianTarget
  ErfcxTailIntegral ErfcxScaledAnalytic NormalCentered NormalErfcxIdentity
  NormalErfcxSensitivity.
Open Scope R_scope.

Definition normal_tail x := exp(-x*x/2)*gaussian_erfcx(x/sqrt 2)/2.

Lemma normal_sqrt_two_square x : (x/sqrt 2)*(x/sqrt 2)=x*x/2.
Proof.
  assert (S : sqrt 2*sqrt 2=2)by(apply sqrt_sqrt;lra).
  replace(x/sqrt 2*(x/sqrt 2))with(x*x/(sqrt 2*sqrt 2))by(field;interval with(i_prec 80)).
  rewrite S;reflexivity.
Qed.

Theorem normal_tail_complement x : normal_tail x=/2-normal_center x.
Proof.
  unfold normal_tail,gaussian_erfcx;rewrite gaussian_integral_scaled,normal_sqrt_two_square.
  assert (Cancel : exp(-x*x/2)*exp(x*x/2)=1).
  { rewrite <-exp_plus;replace(-x*x/2+x*x/2)with 0 by field;apply exp_0. }
  assert (Constant : inv_sqrt_pi/sqrt 2=normal_density_constant).
  { unfold inv_sqrt_pi,normal_density_constant.
    rewrite sqrt_mult by (pose proof PI_RGT_0;lra).
    field;split;interval with(i_prec 80). }
  unfold normal_center,normal_shape.
  replace(exp(-x*x/2)*(exp(x*x/2)*(1-2*inv_sqrt_pi*(x/sqrt 2*RInt(gaussian_scaled(x/sqrt 2))0 1)))/2)
    with((exp(-x*x/2)*exp(x*x/2))*(/2-(inv_sqrt_pi/sqrt 2)*x*RInt(gaussian_scaled(x/sqrt 2))0 1))by(field;interval with(i_prec 80)).
  rewrite Cancel,Constant;ring.
Qed.

Theorem normal_tail_range x : 0<x -> 0<normal_tail x<=/2.
Proof.
  intros X. assert (Z : 0<x/sqrt 2)by(apply Rdiv_lt_0_compat;[exact X|interval with(i_prec 80)]).
  pose proof(normal_erfcx_positive _ Z) as F.
  split.
  - unfold normal_tail;pose proof(exp_pos(-x*x/2));nra.
  - rewrite normal_tail_complement.
    assert (Shape : 0<=normal_shape x).
    { unfold normal_shape;apply RInt_ge_0;[lra|apply gaussian_scaled_integrable|].
      intros u U;unfold gaussian_scaled,gaussian;left;apply exp_pos. }
    assert (C : 0<normal_density_constant)by(unfold normal_density_constant;interval with(i_prec 80)).
    assert (Center : 0<=normal_center x).
    { unfold normal_center;apply Rmult_le_pos;[apply Rmult_le_pos;lra|exact Shape]. }
    lra.
Qed.

Theorem normal_center_odd x : normal_center(-x)= -normal_center x.
Proof.
  assert (Shape : normal_shape(-x)=normal_shape x).
  { unfold normal_shape;apply RInt_ext;intros u U.
    unfold gaussian_scaled,gaussian;f_equal;unfold Rdiv;ring. }
  unfold normal_center;rewrite Shape;ring.
Qed.

Theorem normal_tail_negative_cdf x : normal_tail x=/2+normal_center(-x).
Proof. rewrite normal_center_odd,normal_tail_complement;ring. Qed.
