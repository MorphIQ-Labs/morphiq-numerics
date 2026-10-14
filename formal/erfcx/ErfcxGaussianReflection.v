(** Reflection and a lower bound from the finite defining Gaussian integral. *)
From Coq Require Import Reals Lra Psatz.
From Coquelicot Require Import Coquelicot.
Require Import ErfcxConstants ErfcxTaylorODE ErfcxGaussianSeries ErfcxGaussianTarget.
Open Scope R_scope.
Lemma gaussian_integral_odd x : RInt gaussian 0 (-x)= -RInt gaussian 0 x.
Proof.
  rewrite !gaussian_integral_scaled.
  assert (Even : RInt (gaussian_scaled (-x)) 0 1=RInt (gaussian_scaled x) 0 1).
  { apply RInt_ext. intros u U. unfold gaussian_scaled,gaussian.
    f_equal; ring. }
  rewrite Even. change (-x * RInt (gaussian_scaled x) 0 1 = -(x * RInt (gaussian_scaled x) 0 1)). ring.
Qed.
Theorem gaussian_erfcx_reflection x : gaussian_erfcx (-x)=2*exp(x*x)-gaussian_erfcx x.
Proof.
  unfold gaussian_erfcx. rewrite gaussian_integral_odd.
  replace (-x * -x) with (x*x) by ring. ring.
Qed.
Theorem gaussian_negative_lower x : x<=0 -> exp(x*x)<=gaussian_erfcx x.
Proof.
  intros X.
  assert (Integral : 0<=RInt gaussian 0 (-x)).
  { apply RInt_ge_0; [lra|apply gaussian_integrable|].
    intros t T. unfold gaussian. apply Rlt_le,exp_pos. }
  rewrite gaussian_integral_odd in Integral.
  unfold gaussian_erfcx. pose proof inv_sqrt_pi_positive.
  pose proof (exp_pos(x*x)).
  assert (0<=2*inv_sqrt_pi*exp(x*x)) by nra.
  pose proof (Rmult_le_compat_l _ _ _ (Rlt_le _ _ (exp_pos(x*x))) Integral). nra.
Qed.
Theorem gaussian_negative_at_least_one x : x<=0 -> 1<=gaussian_erfcx x.
Proof.
  intros X. eapply Rle_trans; [|apply gaussian_negative_lower;exact X].
  destruct (Req_dec x 0) as [Z|NZ].
  - subst x; replace (0*0) with 0 by ring; rewrite exp_0; lra.
  - rewrite <- exp_0. apply Rlt_le,exp_increasing; nra.
Qed.
