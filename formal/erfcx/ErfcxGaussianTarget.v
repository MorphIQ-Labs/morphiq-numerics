(** The defining Gaussian-integral erfcx and its rational-series enclosure. *)
From Coq Require Import Reals Lia Lra Psatz.
From Coquelicot Require Import Coquelicot.
Require Import ErfcxConstants ErfcxTaylorODE ErfcxGaussianSeries.
Open Scope R_scope.
Definition gaussian_erfcx x := exp(x*x)*(1-2*inv_sqrt_pi*RInt gaussian 0 x).
Definition gaussian_approx n x := exp(x*x)*(1-2*inv_sqrt_pi*x*gaussian_sum n x).

Lemma gaussian_integral_scaled x : RInt gaussian 0 x=x*RInt (gaussian_scaled x) 0 1.
Proof.
  pose proof (@RInt_comp_lin R_CompleteNormedModule gaussian x 0 0 1
    (gaussian_integrable (x*0+0) (x*1+0))) as Change.
  replace (x*0+0) with 0 in Change by ring.
  replace (x*1+0) with x in Change by ring.
  rewrite <- Change. transitivity (RInt (fun u => x*gaussian_scaled x u) 0 1).
  - apply RInt_ext. intros u U. change (x*gaussian(x*u+0)=x*gaussian(x*u)). rewrite Rplus_0_r; reflexivity.
  - exact (@RInt_scal R_CompleteNormedModule (gaussian_scaled x) 0 1 x
      (gaussian_scaled_integrable x 0 1)).
Qed.

Theorem gaussian_approx_error n x :
  Rabs (gaussian_erfcx x-gaussian_approx n x)<=
    2*inv_sqrt_pi*exp(x*x)*Rabs x*((x*x)^S n/INR(fact(S n))).
Proof.
  unfold gaussian_erfcx,gaussian_approx. rewrite gaussian_integral_scaled.
  replace (exp(x*x)*(1-2*inv_sqrt_pi*(x*RInt(gaussian_scaled x)0 1))-
    exp(x*x)*(1-2*inv_sqrt_pi*x*gaussian_sum n x)) with
    (- (2*inv_sqrt_pi*exp(x*x))*x*(RInt(gaussian_scaled x)0 1-gaussian_sum n x)) by ring.
  rewrite !Rabs_mult,Rabs_Ropp.
  assert (C : 0<=2*inv_sqrt_pi*exp(x*x)).
  { pose proof inv_sqrt_pi_positive; pose proof(exp_pos(x*x)); nra. }
  rewrite (Rabs_right (2*inv_sqrt_pi*exp(x*x))) by lra.
  apply Rmult_le_compat_l; [apply Rmult_le_pos; [exact C|apply Rabs_pos]|].
  apply gaussian_integral_remainder.
Qed.

Lemma gaussian_erfcx_at_zero : gaussian_erfcx 0=1.
Proof.
  unfold gaussian_erfcx. rewrite RInt_point.
  change (exp(0*0)*(1-2*inv_sqrt_pi*0)=1).
  replace (0*0) with 0 by ring; rewrite exp_0; ring.
Qed.

Theorem gaussian_erfcx_derivative x :
  is_derive gaussian_erfcx x (2*x*gaussian_erfcx x-2*inv_sqrt_pi).
Proof.
  unfold gaussian_erfcx. auto_derive.
  - split; [apply gaussian_integrable|]. split; [|exact I].
    apply filter_forall. intros z. unfold gaussian.
    apply (continuity_pt_comp (fun u => -u*u) exp z).
    + apply continuity_pt_mult; [apply continuity_pt_opp|]; apply continuity_pt_id.
    + apply derivable_continuous_pt,derivable_pt_exp.
  - unfold gaussian. replace (-x*x) with (-(x*x)) by ring.
    assert (Cancel : exp(x*x)*exp(-(x*x))=1)
      by (rewrite <- exp_plus; replace (x*x+-(x*x)) with 0 by ring; apply exp_0).
    replace (exp(x*x)* -(2*inv_sqrt_pi*(1*exp(-(x*x)))))
      with (-2*inv_sqrt_pi*(exp(x*x)*exp(-(x*x)))) by ring.
    rewrite Cancel. ring.
Qed.
