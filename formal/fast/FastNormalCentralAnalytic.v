(** Integrated Taylor remainder for the bounded CDF's |x|<=1 domain. *)
From Coq Require Import Reals Lia Lra Psatz.
From Coquelicot Require Import Coquelicot.
From Interval Require Import Tactic.
From Flocq Require Import Core.
Require Import StageGappa Expm1Series ErfcxExpRemainder ErfcxTaylorODE
 ErfcxGaussianSeries ErfcxFactorial NormalCentered.
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

Theorem fast_normal_center_truncation x : Rabs x<=1 ->
 Rabs (normal_center x-normal_center_polynomial 12 x)<=3/2^53.
Proof.
 intros X. unfold normal_center,normal_center_polynomial,normal_shape.
 replace (normal_density_constant*x*RInt(gaussian_scaled(x/sqrt 2))0 1-
   normal_density_constant*x*gaussian_sum 12 (x/sqrt 2)) with
   (normal_density_constant*x*(RInt(gaussian_scaled(x/sqrt 2))0 1-gaussian_sum 12 (x/sqrt 2))) by ring.
 rewrite !Rabs_mult,(Rabs_pos_eq normal_density_constant).
 2: unfold normal_density_constant;left;interval with(i_prec 80).
 eapply Rle_trans.
 - apply Rmult_le_compat_l;[apply Rmult_le_pos;[unfold normal_density_constant;left;interval with(i_prec 80)|apply Rabs_pos]|apply gaussian_integral_weighted_remainder].
 - apply Rabs_le_inv in X. unfold normal_density_constant. binary_factorials.
   repeat rewrite INR_IZR_INZ;small_numerals.
   interval with(i_prec 100).
Qed.
