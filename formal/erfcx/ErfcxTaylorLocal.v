(** Local variation of the defining Gaussian integral. *)
From Coq Require Import Reals Lia Lra Psatz.
From Coquelicot Require Import Coquelicot.
From Flocq Require Import Core.
From Interval Require Import Tactic.
Require Import ErfcxConstants ErfcxTaylorODE ErfcxGaussianTarget.
Open Scope R_scope.
Definition local_integrand c h t := exp((c+h)*(c+h)-(c+h*t)*(c+h*t)).
Definition shifted_gaussian c h t := gaussian(c+h*t).

Lemma shifted_gaussian_integrable c h a b : ex_RInt (shifted_gaussian c h) a b.
Proof.
  apply (@ex_RInt_continuous R_CompleteNormedModule). intros t T.
  apply (@ex_derive_continuous R_AbsRing R_CompleteNormedModule).
  unfold shifted_gaussian,gaussian. eexists. auto_derive; trivial.
Qed.
Lemma local_integrand_integrable c h a b : ex_RInt (local_integrand c h) a b.
Proof.
  apply (@ex_RInt_continuous R_CompleteNormedModule). intros t T.
  apply (@ex_derive_continuous R_AbsRing R_CompleteNormedModule).
  unfold local_integrand. eexists. auto_derive; trivial.
Qed.

Lemma gaussian_segment c h : RInt gaussian c (c+h)=h*RInt (shifted_gaussian c h) 0 1.
Proof.
  pose proof (@RInt_comp_lin R_CompleteNormedModule gaussian h c 0 1
    (gaussian_integrable (h*0+c) (h*1+c))) as Change.
  replace (h*0+c) with c in Change by ring.
  replace (h*1+c) with (c+h) in Change by ring.
  rewrite <- Change. transitivity (RInt (fun t => h*shifted_gaussian c h t) 0 1).
  - apply RInt_ext. intros t T. change (h*gaussian(h*t+c)=h*gaussian(c+h*t)).
    replace (h*t+c) with (c+h*t) by ring; reflexivity.
  - exact (@RInt_scal R_CompleteNormedModule (shifted_gaussian c h) 0 1 h
      (shifted_gaussian_integrable c h 0 1)).
Qed.
Lemma local_integral_scale c h :
  RInt (local_integrand c h) 0 1=exp((c+h)*(c+h))*RInt (shifted_gaussian c h) 0 1.
Proof.
  transitivity (RInt (fun t => exp((c+h)*(c+h))*shifted_gaussian c h t) 0 1).
  - apply RInt_ext. intros t T. unfold local_integrand,shifted_gaussian,gaussian.
    rewrite <- exp_plus. f_equal; ring.
  - exact (@RInt_scal R_CompleteNormedModule (shifted_gaussian c h) 0 1 (exp((c+h)*(c+h)))
      (shifted_gaussian_integrable c h 0 1)).
Qed.

Theorem gaussian_local_variation c h :
  gaussian_erfcx(c+h)=exp((c+h)*(c+h)-c*c)*gaussian_erfcx c-
    2*inv_sqrt_pi*h*RInt(local_integrand c h)0 1.
Proof.
  pose proof (@RInt_Chasles R_CompleteNormedModule gaussian 0 c (c+h)
    (gaussian_integrable 0 c) (gaussian_integrable c (c+h))) as Split.
  change (RInt gaussian 0 c+RInt gaussian c (c+h)=RInt gaussian 0 (c+h)) in Split.
  unfold gaussian_erfcx. rewrite <- Split,gaussian_segment,local_integral_scale.
  assert (Cancel : exp((c+h)*(c+h)-c*c)*exp(c*c)=exp((c+h)*(c+h)))
    by (rewrite <- exp_plus; f_equal; ring).
  replace (exp((c+h)*(c+h)-c*c)*(exp(c*c)*(1-2*inv_sqrt_pi*RInt gaussian 0 c))) with
    ((exp((c+h)*(c+h)-c*c)*exp(c*c))*(1-2*inv_sqrt_pi*RInt gaussian 0 c)) by ring.
  rewrite Cancel. ring.
Qed.

Lemma local_integral_bound c h : Rabs c<=16 -> Rabs h<=/8 ->
  Rabs(RInt(local_integrand c h)0 1)<=64.
Proof.
  intros C H. apply Rabs_le_inv in C,H.
  assert (Integrand : forall t,0<=t<=1 -> Rabs(local_integrand c h t)<=64).
  { intros t T. unfold local_integrand.
    replace ((c+h)*(c+h)-(c+h*t)*(c+h*t)) with (h*(1-t)*(2*c+h*(1+t))) by ring.
    interval with (i_prec 80). }
  pose proof (@norm_RInt_le_const R_NormedModule (local_integrand c h) 0 1
    (RInt(local_integrand c h)0 1) 64 ltac:(lra) Integrand
    (RInt_correct _ _ _ (local_integrand_integrable c h 0 1))) as Bound.
  change (Rabs(RInt(local_integrand c h)0 1)<=(1-0)*64) in Bound. lra.
Qed.

Theorem gaussian_local_bound c h : Rabs c<=16 -> Rabs h<=/8 ->
  Rabs(gaussian_erfcx c)<=3 -> Rabs(gaussian_erfcx(c+h))<=512.
Proof.
  intros C H F. pose proof (local_integral_bound c h C H) as Integral.
  assert (E : Rabs(exp((c+h)*(c+h)-c*c))<=64).
  { apply Rabs_le_inv in C,H.
    replace ((c+h)*(c+h)-c*c) with (h*(2*c+h)) by ring. interval with (i_prec 80). }
  assert (Cs : Rabs inv_sqrt_pi<=1) by (unfold inv_sqrt_pi; interval with (i_prec 80)).
  rewrite gaussian_local_variation. eapply Rle_trans; [apply Rabs_triang|].
  rewrite Rabs_Ropp,!Rabs_mult,(Rabs_pos_eq 2) by lra.
  assert (First : Rabs(exp((c+h)*(c+h)-c*c))*Rabs(gaussian_erfcx c)<=64*3)
    by (apply Rmult_le_compat; [apply Rabs_pos|apply Rabs_pos|exact E|exact F]).
  assert (Second : 2*Rabs inv_sqrt_pi*Rabs h*Rabs(RInt(local_integrand c h)0 1)<=16).
  { pose proof(Rabs_pos inv_sqrt_pi); pose proof(Rabs_pos h); pose proof(Rabs_pos(RInt(local_integrand c h)0 1)).
    assert (A : 2*Rabs inv_sqrt_pi*Rabs h<=/4) by nra.
    nra. }
  lra.
Qed.
