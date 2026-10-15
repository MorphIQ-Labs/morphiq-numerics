(** A first-order erfcx correction with a quadratic remainder on the normal
    tail's compact reduction range. All targets use the defining integral. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Coquelicot Require Import Coquelicot.
From Flocq Require Import Core.
From Interval Require Import Tactic.
Require Import StageGappa ErfcxConstants ErfcxTailIntegral ErfcxScaledAnalytic
  ErfcxGaussianTarget NormalErfcxIdentity NormalErfcxSensitivity.
Open Scope R_scope.

Lemma normal_erfcx_compact_range x : /8<=x<=33 -> 0<gaussian_erfcx x<=8.
Proof.
  intros X;split;[apply normal_erfcx_positive;lra|].
  rewrite <-positive_erfcx_gaussian by lra;unfold positive_erfcx.
  pose proof(tail_integral_limit ((/x)*(/x))ltac:(nra))as[_ T].
  assert(C : 0<inv_sqrt_pi<=1)by(unfold inv_sqrt_pi;split;interval with(i_prec 80)).
  assert(Reciprocal : 0<=/x<=8)by(split;interval with(i_prec 80)).
  unfold Rdiv;pose proof(Rmult_le_compat_l (inv_sqrt_pi* /x) _ _ ltac:(nra)(proj2 T));nra.
Qed.

Lemma normal_erfcx_absolute_secant a b : 0<a<=b ->
  Rabs(gaussian_erfcx b-gaussian_erfcx a)<=2*(b-a).
Proof.
  intros Range;destruct(Rle_lt_or_eq_dec _ _ (proj2 Range))as[Lt|Eq].
  2: rewrite Eq,Rminus_diag_eq,Rabs_R0 by reflexivity;lra.
  destruct(MVT_cor2 gaussian_erfcx normal_erfcx_derivative a b Lt)as[c [Difference C]].
  - intros;apply is_derive_Reals,gaussian_erfcx_derivative.
  - pose proof(normal_erfcx_derivative_bounds c ltac:(lra))as[Bounds _].
    assert(Pi : inv_sqrt_pi<=1)by(unfold inv_sqrt_pi;interval with(i_prec 80)).
    rewrite Difference,Rabs_mult,(Rabs_pos_eq(b-a)),(Rabs_left1(normal_erfcx_derivative c))by lra;nra.
Qed.

Lemma normal_erfcx_lipschitz a b : 0<a -> 0<b ->
  Rabs(gaussian_erfcx b-gaussian_erfcx a)<=2*Rabs(b-a).
Proof.
  intros A B;destruct(Rle_dec a b)as[Order|Order].
  - rewrite(Rabs_pos_eq(b-a))by lra;apply normal_erfcx_absolute_secant;split;lra.
  - rewrite Rabs_minus_sym,(Rabs_left1(b-a))by lra.
    replace(- (b-a))with(a-b)by ring;apply normal_erfcx_absolute_secant;split;lra.
Qed.

Lemma normal_erfcx_derivative_lipschitz a b : /8<=a<=33 -> /8<=b<=33 ->
  Rabs(normal_erfcx_derivative b-normal_erfcx_derivative a)<=160*Rabs(b-a).
Proof.
  intros A B;pose proof(normal_erfcx_compact_range b B)as F.
  pose proof(normal_erfcx_lipschitz a b ltac:(lra)ltac:(lra))as Difference.
  unfold normal_erfcx_derivative;replace(2*b*gaussian_erfcx b-2*inv_sqrt_pi-(2*a*gaussian_erfcx a-2*inv_sqrt_pi))with
    (2*(b-a)*gaussian_erfcx b+2*a*(gaussian_erfcx b-gaussian_erfcx a))by ring.
  eapply Rle_trans;[apply Rabs_triang|].
  rewrite !Rabs_mult,(Rabs_pos_eq 2),(Rabs_pos_eq a),(Rabs_pos_eq(gaussian_erfcx b))by lra.
  pose proof(Rabs_pos(b-a));pose proof(Rabs_pos(gaussian_erfcx b-gaussian_erfcx a));nra.
Qed.

Lemma normal_erfcx_linear_interval a b z : /8<=a<=b -> b<=33 -> a<=z<=b ->
  Rabs((gaussian_erfcx b-gaussian_erfcx a)-normal_erfcx_derivative z*(b-a))<=160*(b-a)^2.
Proof.
  intros A B Z;destruct(Rle_lt_or_eq_dec _ _ (proj2 A))as[Lt|Eq].
  2: rewrite Eq;replace((gaussian_erfcx b-gaussian_erfcx b)-normal_erfcx_derivative z*(b-b))with 0 by ring;rewrite Rabs_R0;nra.
  destruct(MVT_cor2 gaussian_erfcx normal_erfcx_derivative a b Lt)as[c [Difference C]].
  - intros;apply is_derive_Reals,gaussian_erfcx_derivative.
  - pose proof(normal_erfcx_derivative_lipschitz z c ltac:(split;lra)ltac:(split;lra))as Bound.
    assert(Distance : Rabs(c-z)<=b-a)by(apply Rabs_le;split;lra).
    rewrite Difference;replace(normal_erfcx_derivative c*(b-a)-normal_erfcx_derivative z*(b-a))with
      ((normal_erfcx_derivative c-normal_erfcx_derivative z)*(b-a))by ring.
    rewrite Rabs_mult,(Rabs_pos_eq(b-a))by lra;nra.
Qed.

Theorem normal_erfcx_linear_remainder z d : /4<=z<=32 -> Rabs d<=bpow radix2 (-49) ->
  Rabs(gaussian_erfcx(z+d)-(gaussian_erfcx z+d*normal_erfcx_derivative z))<=256*d*d.
Proof.
  intros Z D;assert(Small : -/8<=d<=/8)by(apply Rabs_le_inv in D;bpow_num_all;split;lra).
  destruct(Rle_dec 0 d)as[Positive|Negative].
  - pose proof(normal_erfcx_linear_interval z (z+d)z ltac:(split;lra)ltac:(lra)ltac:(split;lra))as Error.
    replace(gaussian_erfcx(z+d)-(gaussian_erfcx z+d*normal_erfcx_derivative z))with
      ((gaussian_erfcx(z+d)-gaussian_erfcx z)-normal_erfcx_derivative z*((z+d)-z))by ring.
    eapply Rle_trans;[exact Error|];nra.
  - pose proof(normal_erfcx_linear_interval (z+d)z z ltac:(split;lra)ltac:(lra)ltac:(split;lra))as Error.
    replace(gaussian_erfcx(z+d)-(gaussian_erfcx z+d*normal_erfcx_derivative z))with
      (-((gaussian_erfcx z-gaussian_erfcx(z+d))-normal_erfcx_derivative z*(z-(z+d))))by ring.
    rewrite Rabs_Ropp;eapply Rle_trans;[exact Error|];nra.
Qed.
