(** Gaussian integral polynomial and a uniform, signed-argument remainder.
    Scaling to [0,1] handles negative centers without a separate argument. *)
From Coq Require Import Reals Lia Lra Psatz.
From Coquelicot Require Import Coquelicot.
Require Import Expm1Series ErfcxExpRemainder ErfcxTaylorODE.
Open Scope R_scope.

Definition gaussian_scaled x u := gaussian (x*u).
Definition gaussian_polynomial n x u := exp_negative_polynomial n ((x*u)*(x*u)).
Definition gaussian_sum n x :=
  sum_f_R0 (fun k => (-x*x)^k/(INR(fact k)*INR(S(2*k)))) n.

Lemma gaussian_scaled_integrable x a b : ex_RInt (gaussian_scaled x) a b.
Proof.
  apply (@ex_RInt_continuous R_CompleteNormedModule). intros u U.
  apply (@ex_derive_continuous R_AbsRing R_CompleteNormedModule).
  unfold gaussian_scaled,gaussian. eexists. auto_derive; trivial.
Qed.

Lemma gaussian_polynomial_continuous n x u : continuous (gaussian_polynomial n x) u.
Proof.
  unfold gaussian_polynomial,exp_negative_polynomial,esum.
  induction n as [|n IH].
  - cbn [sum_f_R0 pow]. apply continuous_const.
  - change (continuous (fun u => sum_f_R0 (fun k => (- (x*u*(x*u)))^k/INR(fact k)) n+
      (-(x*u*(x*u)))^S n/INR(fact(S n))) u).
    apply (@continuous_plus R_UniformSpace R_AbsRing R_NormedModule); [exact IH|].
    apply (@ex_derive_continuous R_AbsRing R_CompleteNormedModule).
    eexists. auto_derive; trivial.
Qed.
Lemma gaussian_polynomial_integrable n x a b : ex_RInt (gaussian_polynomial n x) a b.
Proof. apply (@ex_RInt_continuous R_CompleteNormedModule). intros; apply gaussian_polynomial_continuous. Qed.

Lemma gaussian_monomial_integral k x :
  RInt (fun u => (-(x*u*(x*u)))^k/INR(fact k)) 0 1=
    (-x*x)^k/(INR(fact k)*INR(S(2*k))).
Proof.
  assert (P : ex_RInt (fun u : R => u^(2*k)) 0 1).
  { eexists. apply is_RInt_pow. }
  transitivity (RInt (fun u => ((-x*x)^k/INR(fact k))*u^(2*k)) 0 1).
  - apply RInt_ext. intros u U.
    replace (-(x*u*(x*u))) with ((-x*x)*(u^2)) by (simpl pow; ring).
    rewrite Rpow_mult_distr,pow_mult. unfold Rdiv. rewrite !Rmult_assoc. f_equal. apply Rmult_comm.
  - pose proof (@RInt_scal R_CompleteNormedModule (fun u : R => u^(2*k)) 0 1
      ((-x*x)^k/INR(fact k)) P) as Scale.
    change (RInt (fun u => ((-x*x)^k/INR(fact k))*u^(2*k)) 0 1=
      ((-x*x)^k/INR(fact k))*RInt (fun u => u^(2*k)) 0 1) in Scale.
    rewrite Scale,(is_RInt_unique _ _ _ _ (is_RInt_pow 0 1 (2*k))),pow1,pow_i; [|lia].
    assert (F : INR(fact k)<>0) by (apply not_0_INR; pose proof(lt_O_fact k); lia).
    assert (K : INR(S(2*k))<>0) by (apply not_0_INR; lia).
    change (((-x*x)^k/INR(fact k))*(1/INR(S(2*k))-0/INR(S(2*k)))=
      (-x*x)^k/(INR(fact k)*INR(S(2*k)))).
    field; auto.
Qed.

Lemma gaussian_polynomial_integral n x :
  RInt (gaussian_polynomial n x) 0 1=gaussian_sum n x.
Proof.
  induction n as [|n IH].
  - apply gaussian_monomial_integral.
  - change (RInt (fun u => gaussian_polynomial n x u+
      (-(x*u*(x*u)))^S n/INR(fact(S n))) 0 1=
      gaussian_sum n x+(-x*x)^S n/(INR(fact(S n))*INR(S(2*S n)))).
    assert (P : ex_RInt (fun u => (-(x*u*(x*u)))^S n/INR(fact(S n))) 0 1).
    { apply (@ex_RInt_continuous R_CompleteNormedModule). intros u U.
      apply (@ex_derive_continuous R_AbsRing R_CompleteNormedModule). eexists. auto_derive; trivial. }
    pose proof (@RInt_plus R_CompleteNormedModule (gaussian_polynomial n x)
      (fun u => (-(x*u*(x*u)))^S n/INR(fact(S n))) 0 1
      (gaussian_polynomial_integrable n x 0 1) P) as Plus.
    change (RInt (fun u => gaussian_polynomial n x u+
      (-(x*u*(x*u)))^S n/INR(fact(S n))) 0 1=
      RInt (gaussian_polynomial n x) 0 1+
      RInt (fun u => (-(x*u*(x*u)))^S n/INR(fact(S n))) 0 1) in Plus.
    rewrite Plus,IH,gaussian_monomial_integral. reflexivity.
Qed.

Lemma gaussian_pointwise_remainder n x u : 0<=u<=1 ->
  Rabs (gaussian_scaled x u-gaussian_polynomial n x u)<=
    (x*x)^S n/INR(fact(S n)).
Proof.
  intros U. destruct (exp_negative_taylor_remainder n ((x*u)*(x*u)) ltac:(nra))
    as [theta [Theta Error]].
  unfold gaussian_scaled,gaussian,gaussian_polynomial.
  replace (-(x*u)*(x*u)) with (-((x*u)*(x*u))) by ring. rewrite Error.
  unfold Rdiv. rewrite !Rabs_mult,pow_1_abs.
  rewrite (Rabs_right theta) by lra.
  rewrite (Rabs_right (((x*u)*(x*u))^S n)) by (apply Rle_ge,pow_le; nra).
  assert (F : 0<INR(fact(S n))) by (apply lt_0_INR,lt_O_fact).
  rewrite Rabs_right by (left; apply Rinv_0_lt_compat; exact F).
  assert (Pow : ((x*u)*(x*u))^S n<=(x*x)^S n).
  { apply pow_incr. assert (0<=x*x) by nra.
    assert (u*u<=1) by nra. split; nra. }
  assert (P : 0<=((x*u)*(x*u))^S n) by (apply pow_le; nra).
  apply Rmult_le_compat_r; [left; apply Rinv_0_lt_compat; exact F|]. nra.
Qed.

Theorem gaussian_integral_remainder n x :
  Rabs (RInt (gaussian_scaled x) 0 1-gaussian_sum n x)<=
    (x*x)^S n/INR(fact(S n)).
Proof.
  pose proof (@RInt_minus R_CompleteNormedModule (gaussian_scaled x) (gaussian_polynomial n x) 0 1
    (gaussian_scaled_integrable x 0 1) (gaussian_polynomial_integrable n x 0 1)) as Difference.
  change (RInt (fun u => gaussian_scaled x u-gaussian_polynomial n x u) 0 1=
    RInt (gaussian_scaled x) 0 1-RInt (gaussian_polynomial n x) 0 1) in Difference.
  rewrite gaussian_polynomial_integral in Difference. rewrite <- Difference.
  pose proof (@norm_RInt_le_const R_NormedModule
    (fun u => gaussian_scaled x u-gaussian_polynomial n x u) 0 1
    (RInt (fun u => gaussian_scaled x u-gaussian_polynomial n x u) 0 1)
    ((x*x)^S n/INR(fact(S n))) ltac:(lra)
    (fun u U => gaussian_pointwise_remainder n x u U)
    (RInt_correct _ _ _ (@ex_RInt_minus R_NormedModule _ _ _ _
      (gaussian_scaled_integrable x 0 1) (gaussian_polynomial_integrable n x 0 1)))) as Bound.
  change (Rabs (RInt (fun u => gaussian_scaled x u-gaussian_polynomial n x u) 0 1)<=
    (1-0)*((x*x)^S n/INR(fact(S n)))) in Bound. lra.
Qed.

Definition gaussian_term n x := (-x*x)^n/(INR(fact n)*INR(S(2*n))).
Lemma gaussian_term_step n x :
  gaussian_term (S n) x=(-x*x)*gaussian_term n x*
    (INR(S(2*n))/(INR(S n)*INR(S(2*S n)))).
Proof.
  unfold gaussian_term. cbn [pow fact]. rewrite mult_INR.
  assert (F : INR(fact n)<>0) by (apply not_0_INR; pose proof(lt_O_fact n); lia).
  assert (N : INR(S n)<>0) by (apply not_0_INR; lia).
  assert (K : INR(S(2*n))<>0) by (apply not_0_INR; lia).
  assert (L : INR(S(2*S n))<>0) by (apply not_0_INR; lia).
  field; auto.
Qed.

