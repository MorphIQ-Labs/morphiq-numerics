(** The log-CDF tail in terms of the normalized Mills integral. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Interval Require Import Tactic.
Require Import ErfcxConstants ErfcxTailIntegral ErfcxScaledAnalytic
  NormalErfcxIdentity NormalTailAnalytic NormalLogAnalytic.
Open Scope R_scope.

Theorem normal_log_mills_identity x : 37<=x ->
  ln(normal_tail x)= -x*x/2-ln x-ln(2*PI)/2+ln(tail_integral(2*((1/x)*(1/x)))).
Proof.
  intros X.
  assert(S2 : 0<sqrt 2)by(interval with(i_prec 80)).
  assert(SP : 0<sqrt PI)by(interval with(i_prec 80)).
  assert(Square : sqrt 2*sqrt 2=2)by(apply sqrt_sqrt;lra).
  assert(Reciprocal : (/(x/sqrt 2))*(/(x/sqrt 2))=2*((1/x)*(1/x))).
  { replace((/(x/sqrt 2))*(/(x/sqrt 2)))with
      ((sqrt 2*sqrt 2)*((1/x)*(1/x)))by(field;lra).
    rewrite Square;reflexivity. }
  assert(Constant : inv_sqrt_pi/(x/sqrt 2)/2=/(x*sqrt(2*PI))).
  { unfold inv_sqrt_pi;rewrite sqrt_mult by(pose proof PI_RGT_0;lra).
    field_simplify_eq;try (repeat split;lra);nra. }
  assert(T : 0<=2*((1/x)*(1/x))<=2/1369).
  { assert(R : 0<=1/x<=1/37)by(split;[left;apply Rdiv_lt_0_compat;lra|
      unfold Rdiv;rewrite !Rmult_1_l;apply Rinv_le_contravar;lra]);nra. }
  pose proof(tail_integral_correction _ (proj1 T))as Correction.
  assert(J : 0<tail_integral(2*((1/x)*(1/x))))by lra.
  assert(S2P : 0<sqrt(2*PI))by(interval with(i_prec 80)).
  assert(LogSqrt : ln(sqrt(2*PI))=ln(2*PI)/2).
  { pose proof(ln_mult (sqrt(2*PI)) (sqrt(2*PI)) S2P S2P)as L.
    rewrite sqrt_sqrt in L by(pose proof PI_RGT_0;nra);lra. }
  rewrite normal_log_tail_identity by lra.
  rewrite <-positive_erfcx_gaussian by(apply Rdiv_lt_0_compat;lra).
  unfold positive_erfcx;rewrite Reciprocal.
  replace(inv_sqrt_pi/(x/sqrt 2)*tail_integral(2*(1/x*(1/x)))/2)with
    ((inv_sqrt_pi/(x/sqrt 2)/2)*tail_integral(2*(1/x*(1/x))))by(unfold Rdiv;ring).
  rewrite Constant,ln_mult by(try exact J;apply Rinv_0_lt_compat;nra).
  rewrite ln_Rinv by nra;rewrite ln_mult by lra;rewrite LogSqrt;ring.
Qed.
