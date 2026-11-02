(** The bounded normal CDF's body: [Phi(x) - 1/2 = erf(x/sqrt 2)/2], and the
    generated polynomial [P(y^2)] approximates [erf(y)/y] for [|y| <= 15/32]. *)
From Coq Require Import Reals Lia Lra Psatz List.
From Coquelicot Require Import Coquelicot.
From Interval Require Import Tactic.
From Flocq Require Import Core.
Require Import StageGappa Expm1Series ErfcxConstants ErfcxExpRemainder ErfcxTaylorODE
  ErfcxGaussianSeries ErfcxGaussianTarget ErfcxFactorial NormalCentered FastCdfConstants.
Import ListNotations.
Open Scope R_scope.

Lemma gaussian_pointwise_weighted n x u :
 Rabs (gaussian_scaled x u-gaussian_polynomial n x u)<=
 (x*x)^S n/INR(fact(S n))*u^(2*S n).
Proof.
 destruct (exp_negative_taylor_remainder n ((x*u)*(x*u)) ltac:(nra))
   as [theta [Theta Error]].
 unfold gaussian_scaled,gaussian,gaussian_polynomial.
 replace (-(x*u)*(x*u)) with (-((x*u)*(x*u))) by ring. rewrite Error.
 unfold Rdiv. rewrite !Rabs_mult,pow_1_abs.
 rewrite (Rabs_right theta) by lra.
 rewrite (Rabs_right (((x*u)*(x*u))^S n)) by (apply Rle_ge,pow_le;nra).
 assert (F : 0<INR(fact(S n))) by (apply lt_0_INR,lt_O_fact).
 rewrite Rabs_right by (left;apply Rinv_0_lt_compat;exact F).
 assert (Power : ((x*u)*(x*u))^S n=(x*x)^S n*u^(2*S n)).
 { replace ((x*u)*(x*u)) with ((x*x)*(u^2)) by (simpl pow;ring).
   rewrite Rpow_mult_distr,pow_mult. reflexivity. }
 replace ((x*x)^S n*/INR(fact(S n))*u^(2*S n)) with
   (((x*u)*(x*u))^S n*/INR(fact(S n))) by (rewrite Power;ring).
 assert (P : 0<=((x*u)*(x*u))^S n) by (apply pow_le;nra).
 apply Rmult_le_compat_r;[left;apply Rinv_0_lt_compat;exact F|nra].
Qed.

Theorem gaussian_integral_weighted_remainder n x :
 Rabs (RInt (gaussian_scaled x) 0 1-gaussian_sum n x)<=
 (x*x)^S n/(INR(fact(S n))*INR(S(2*S n))).
Proof.
 pose proof (@RInt_minus R_CompleteNormedModule (gaussian_scaled x) (gaussian_polynomial n x) 0 1
   (gaussian_scaled_integrable x 0 1) (gaussian_polynomial_integrable n x 0 1)) as Difference.
 change (RInt (fun u => gaussian_scaled x u-gaussian_polynomial n x u) 0 1=
   RInt (gaussian_scaled x) 0 1-RInt (gaussian_polynomial n x) 0 1) in Difference.
 rewrite gaussian_polynomial_integral in Difference. rewrite <-Difference.
 assert (Integral : is_RInt (fun u => (x*x)^S n/INR(fact(S n))*u^(2*S n)) 0 1
   ((x*x)^S n/(INR(fact(S n))*INR(S(2*S n))))).
 { pose proof (@is_RInt_scal R_NormedModule (fun u : R => u^(2*S n)) 0 1
     ((x*x)^S n/INR(fact(S n)))
     (1^S(2*S n)/INR(S(2*S n))-0^S(2*S n)/INR(S(2*S n))) (is_RInt_pow 0 1 (2*S n))) as Scale.
   change (is_RInt (fun u => (x*x)^S n/INR(fact(S n))*u^(2*S n)) 0 1
     (((x*x)^S n/INR(fact(S n)))*(1^S(2*S n)/INR(S(2*S n))-0^S(2*S n)/INR(S(2*S n))))) in Scale.
   rewrite pow1,pow_i in Scale by lia.
   replace (((x*x)^S n/INR(fact(S n)))*(1/INR(S(2*S n))-0/INR(S(2*S n))))
     with ((x*x)^S n/(INR(fact(S n))*INR(S(2*S n)))) in Scale by (field;split;apply not_0_INR;[lia|pose proof (lt_O_fact (S n));lia]).
   exact Scale. }
 apply (@norm_RInt_le R_NormedModule
   (fun u => gaussian_scaled x u-gaussian_polynomial n x u)
   (fun u => (x*x)^S n/INR(fact(S n))*u^(2*S n)) 0 1
   _ _ ltac:(lra) (fun u _ => gaussian_pointwise_weighted n x u)).
 - apply (@RInt_correct R_CompleteNormedModule). apply (@ex_RInt_minus R_NormedModule);
     [apply gaussian_scaled_integrable|apply gaussian_polynomial_integrable].
 - exact Integral.
Qed.

(** [Phi(x) - 1/2 = int_0^(x/sqrt 2) exp(-t^2) dt / sqrt pi]. *)
Theorem cdf_center_integral x : normal_center x=inv_sqrt_pi*RInt gaussian 0 (x/sqrt 2).
Proof.
  rewrite gaussian_integral_scaled. unfold normal_center,normal_shape.
  assert (Constant : normal_density_constant=inv_sqrt_pi/sqrt 2).
  { unfold inv_sqrt_pi,normal_density_constant.
    rewrite sqrt_mult by (pose proof PI_RGT_0;lra).
    field;split;interval with(i_prec 80). }
  rewrite Constant. field. interval with(i_prec 80).
Qed.

(** The generated body polynomial against the degree-12 Taylor sum of
    [int_0^1 exp(-(y u)^2) du]. *)
Lemma cdf_body_taylor y : Rabs y<=15/32 ->
  Rabs(/2*cdf_body_poly(y*y)-inv_sqrt_pi*gaussian_sum 12 y)<=/2^56.
Proof.
  intros Y. apply Rabs_le_inv in Y.
  unfold cdf_body_poly,cdf_body_words,gaussian_sum,inv_sqrt_pi. cbn [cdf_horner sum_f_R0].
  binary_factorials. repeat rewrite INR_IZR_INZ. small_numerals. cdf_values.
  interval with (i_bisect y, i_taylor y, i_degree 26, i_prec 200).
Qed.

Theorem cdf_body_approx y : Rabs y<=15/32 ->
  Rabs(/2*(y*cdf_body_poly(y*y))-inv_sqrt_pi*RInt gaussian 0 y)<=/2^55*Rabs y.
Proof.
  intros Y. pose proof (cdf_body_taylor y Y) as T.
  pose proof (gaussian_integral_weighted_remainder 12 y) as R.
  assert (Small : (y*y)^S 12/(INR(fact(S 12))*INR(S(2*S 12)))<=/2^60).
  { apply Rabs_le_inv in Y. binary_factorials. repeat rewrite INR_IZR_INZ. small_numerals.
    interval with (i_bisect y, i_prec 100). }
  assert (I : 0<inv_sqrt_pi<=1) by (unfold inv_sqrt_pi;split;interval with (i_prec 80)).
  rewrite gaussian_integral_scaled.
  replace (/2*(y*cdf_body_poly(y*y))-inv_sqrt_pi*(y*RInt(gaussian_scaled y)0 1)) with
    (y*((/2*cdf_body_poly(y*y)-inv_sqrt_pi*gaussian_sum 12 y)-
        inv_sqrt_pi*(RInt(gaussian_scaled y)0 1-gaussian_sum 12 y))) by ring.
  rewrite Rabs_mult,Rmult_comm. apply Rmult_le_compat_r;[apply Rabs_pos|].
  eapply Rle_trans;[apply Rabs_triang|]. rewrite Rabs_Ropp,Rabs_mult,(Rabs_pos_eq inv_sqrt_pi) by lra.
  assert (inv_sqrt_pi*Rabs(RInt(gaussian_scaled y)0 1-gaussian_sum 12 y)<=/2^60).
  { eapply Rle_trans;[apply Rmult_le_compat_l;[lra|exact R]|]. nra. }
  lra.
Qed.
