(** Monotonic tail bounds outside the central interval, used to keep the
    complementary compositions and logarithms away from cancellation. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Interval Require Import Tactic.
Require Import NormalCentered NormalTailAnalytic NormalErfcxSensitivity.
Require Import ErfcxGaussianTarget.
Open Scope R_scope.

Theorem normal_tail_decreasing a b : 0<a<=b -> normal_tail b<=normal_tail a.
Proof.
  intros Range.
  assert (Scale : 0<a/sqrt 2<=b/sqrt 2).
  { assert(0</sqrt 2)by(interval with(i_prec 80));unfold Rdiv;split;nra. }
  pose proof(normal_erfcx_decreasing _ _ Scale)as F.
  pose proof(normal_erfcx_positive (b/sqrt 2)ltac:(lra))as PositiveF.
  assert (Gaussian : exp(-b*b/2)<=exp(-a*a/2)).
  { assert(-b*b/2<= -a*a/2)by nra.
    destruct(Rle_lt_or_eq_dec _ _ H)as[Lt|Eq];[left;apply exp_increasing;exact Lt|rewrite Eq;lra]. }
  assert (Product : exp(-b*b/2)*gaussian_erfcx(b/sqrt 2)<=
    exp(-a*a/2)*gaussian_erfcx(a/sqrt 2)).
  { apply Rmult_le_compat;[left;apply exp_pos|lra|exact Gaussian|exact F]. }
  unfold normal_tail;nra.
Qed.

Theorem normal_tail_outer_range x : /2<=x -> 0<normal_tail x<=3/8.
Proof.
  intros X;pose proof(normal_tail_range x ltac:(lra))as Positive.
  pose proof(normal_tail_decreasing (/2)x ltac:(split;lra))as Upper.
  rewrite(normal_tail_complement(/2))in Upper.
  pose proof(normal_shape_range (/2)ltac:(rewrite Rabs_pos_eq;lra))as Shape.
  assert (Density : 3/8<=normal_density_constant)by(unfold normal_density_constant;interval with(i_prec 80)).
  unfold normal_center in Upper;split;nra.
Qed.

Theorem normal_center_outer_range x : /2<=x -> /8<=normal_center x</2.
Proof.
  intros X;pose proof(normal_tail_outer_range x X);rewrite normal_tail_complement in H;split;lra.
Qed.
