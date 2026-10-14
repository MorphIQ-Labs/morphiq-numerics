(** Positive erfcx is decreasing, and its relative sensitivity to a scaled
    argument stays bounded even where its value is extremely small. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Coquelicot Require Import Coquelicot.
From Flocq Require Import Core.
Require Import ErfcxConstants ErfcxTailIntegral ErfcxScaledAnalytic ErfcxGaussianTarget
  NormalErfcxIdentity.
Open Scope R_scope.

Definition normal_erfcx_derivative x := 2*x*gaussian_erfcx x-2*inv_sqrt_pi.

Lemma normal_erfcx_derivative_bounds x : 0<x ->
  -2*inv_sqrt_pi<=normal_erfcx_derivative x<=0 /\
  Rabs(normal_erfcx_derivative x)*x*x<=inv_sqrt_pi.
Proof.
  intros X. pose proof inv_sqrt_pi_positive as C.
  assert (T : 0<=(/x)*(/x))by nra.
  destruct(tail_integral_limit _ T) as [_ Range].
  pose proof(tail_integral_correction _ T) as Correction.
  assert (Value : normal_erfcx_derivative x=2*inv_sqrt_pi*(tail_integral((/x)*(/x))-1)).
  { unfold normal_erfcx_derivative;rewrite <-positive_erfcx_gaussian by exact X.
    unfold positive_erfcx;field;lra. }
  assert (Bounds : -2*inv_sqrt_pi<=normal_erfcx_derivative x<=0) by(rewrite Value;split;nra).
  split;[exact Bounds|]. rewrite Rabs_left1 by lra. rewrite Value.
  assert (Reciprocal : (/x)*(/x)*x*x=1)by(field;lra).
  assert (Gap : 0<=1-tail_integral((/x)*(/x))<=(/x)*(/x)/2)by lra.
  assert (Product : (1-tail_integral((/x)*(/x)))*x*x<=/2).
  { assert (A : (1-tail_integral((/x)*(/x)))*(x*x)<=((/x)*(/x)/2)*(x*x)).
    { apply Rmult_le_compat_r;[nra|lra]. } nra. }
  nra.
Qed.

Theorem normal_erfcx_decreasing a b : 0<a<=b -> gaussian_erfcx b<=gaussian_erfcx a.
Proof.
  intros Range. destruct(Rle_lt_or_eq_dec _ _ (proj2 Range)) as [Lt|Eq];[|rewrite Eq;lra].
  destruct(MVT_cor2 gaussian_erfcx normal_erfcx_derivative a b Lt) as [c [Difference C]].
  - intros;apply is_derive_Reals,gaussian_erfcx_derivative.
  - pose proof(normal_erfcx_derivative_bounds c ltac:(lra)) as Bounds;nra.
Qed.

Lemma normal_erfcx_large_lower x : 1<=x -> inv_sqrt_pi/(2*x)<=gaussian_erfcx x.
Proof.
  intros X. pose proof inv_sqrt_pi_positive as C.
  assert (Reciprocal : 0</x<=1).
  { split;[apply Rinv_0_lt_compat;lra|rewrite <-Rinv_1;apply Rinv_le_contravar;lra]. }
  pose proof(tail_integral_correction ((/x)*(/x)) ltac:(nra)) as Correction.
  assert (J : /2<=tail_integral((/x)*(/x)))by nra.
  rewrite <-positive_erfcx_gaussian by lra;unfold positive_erfcx.
  replace(inv_sqrt_pi/(2*x))with(inv_sqrt_pi/x*(/2))by(field;lra).
  apply Rmult_le_compat_l;[unfold Rdiv;apply Rmult_le_pos;lra|exact J].
Qed.

Lemma normal_erfcx_small_lower x : 0<x<=2 -> 7*inv_sqrt_pi/16<=gaussian_erfcx x.
Proof.
  intros X. pose proof(normal_erfcx_decreasing x 2 X) as Decreasing.
  pose proof(tail_integral_correction ((/2)*(/2)) ltac:(nra)) as Correction.
  assert (AtTwo : 7*inv_sqrt_pi/16<=gaussian_erfcx 2).
  { rewrite <-positive_erfcx_gaussian by lra;unfold positive_erfcx.
    pose proof inv_sqrt_pi_positive;nra. }
  lra.
Qed.

Lemma normal_erfcx_relative_derivative x c : 0<x -> x/2<=c ->
  Rabs(normal_erfcx_derivative c)*x<=16*gaussian_erfcx x.
Proof.
  intros X C. pose proof(normal_erfcx_derivative_bounds c ltac:(lra)) as [Bounds Tail].
  pose proof inv_sqrt_pi_positive as Positive.
  pose proof(Rabs_pos(normal_erfcx_derivative c)) as Nonnegative.
  destruct(Rle_dec 2 x) as [Large|Small].
  - pose proof(normal_erfcx_large_lower x ltac:(lra)) as Lower.
    assert (L : inv_sqrt_pi<=2*x*gaussian_erfcx x).
    { apply(Rmult_le_compat_r (2*x)) in Lower;[|lra].
      replace(inv_sqrt_pi/(2*x)*(2*x))with inv_sqrt_pi in Lower by(field;lra);nra. }
    assert (Product : Rabs(normal_erfcx_derivative c)*(x*x/4)<=
      Rabs(normal_erfcx_derivative c)*(c*c)).
    { apply Rmult_le_compat_l;[exact Nonnegative|nra]. }
    assert (F : 0<gaussian_erfcx x)by nra.
    nra.
  - pose proof(normal_erfcx_small_lower x ltac:(split;lra)) as Lower.
    rewrite Rabs_left1 by lra;nra.
Qed.

Lemma normal_erfcx_positive x : 0<x -> 0<gaussian_erfcx x.
Proof.
  intros X. destruct(Rle_dec 1 x) as [Large|Small].
  - pose proof(normal_erfcx_large_lower x Large).
    assert (0<inv_sqrt_pi/(2*x)).
    { apply Rdiv_lt_0_compat;[apply inv_sqrt_pi_positive|lra]. } lra.
  - pose proof(normal_erfcx_small_lower x ltac:(split;lra)).
    pose proof inv_sqrt_pi_positive;lra.
Qed.

Lemma normal_erfcx_secant x a b : 0<x -> x/2<=a<=b ->
  Rabs(gaussian_erfcx b-gaussian_erfcx a)*x<=16*gaussian_erfcx x*(b-a).
Proof.
  intros X Range. destruct(Rle_lt_or_eq_dec _ _ (proj2 Range)) as [Lt|Eq].
  2: rewrite Eq,Rminus_diag_eq,Rabs_R0 by reflexivity;lra.
  destruct(MVT_cor2 gaussian_erfcx normal_erfcx_derivative a b Lt) as [c [Difference C]].
  - intros;apply is_derive_Reals,gaussian_erfcx_derivative.
  - pose proof(normal_erfcx_relative_derivative x c X ltac:(lra)) as Bound.
    rewrite Difference,Rabs_mult,(Rabs_pos_eq(b-a))by lra.
    assert (Product : (Rabs(normal_erfcx_derivative c)*x)*(b-a)<=
      (16*gaussian_erfcx x)*(b-a)).
    { apply Rmult_le_compat_r;[lra|exact Bound]. } nra.
Qed.

Theorem normal_erfcx_scaled_argument_error x y : 0<x -> Rabs(y-x)<=x/2 ->
  Rabs(gaussian_erfcx y-gaussian_erfcx x)<=16*gaussian_erfcx x*(Rabs(y-x)/x).
Proof.
  intros X Difference. pose proof(Rabs_le_inv _ _ Difference) as Range.
  apply(Rmult_le_reg_r x);[exact X|].
  replace(16*gaussian_erfcx x*(Rabs(y-x)/x)*x)with(16*gaussian_erfcx x*Rabs(y-x))by(field;lra).
  destruct(Rle_dec x y) as [Order|Order].
  - rewrite (Rabs_pos_eq(y-x)) by lra;apply normal_erfcx_secant;[exact X|split;lra].
  - rewrite Rabs_minus_sym,(Rabs_left (y-x))by lra.
    replace(-(y-x))with(x-y)by ring;apply normal_erfcx_secant;[exact X|split;lra].
Qed.
