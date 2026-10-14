(** Identity between the finite Gaussian and positive improper-integral
    representations of erfcx. No Gaussian normalization hypothesis is used. *)
From Coq Require Import Reals Lia Lra Psatz.
From Coquelicot Require Import Coquelicot.
Require Import ErfcxConstants ErfcxTaylorODE ErfcxGaussianTarget
  ErfcxTailIntegral ErfcxScaledAnalytic NormalGaussianIntegral.
Open Scope R_scope.

Definition tail_shifted_gaussian x u := gaussian(x+u/(2*x)).

Lemma tail_shifted_integrable x a b : 0<x -> ex_RInt (tail_shifted_gaussian x) a b.
Proof.
  intros X. apply (@ex_RInt_continuous R_CompleteNormedModule). intros u U.
  apply (@ex_derive_continuous R_AbsRing R_CompleteNormedModule).
  unfold tail_shifted_gaussian,gaussian. eexists;auto_derive;repeat split;nra.
Qed.

Lemma tail_integrand_gaussian x u : 0<x ->
  tail_integrand ((/x)*(/x)) u=exp(x*x)*tail_shifted_gaussian x u.
Proof.
  intros X. unfold tail_integrand,tail_shifted_gaussian,gaussian.
  rewrite <- !exp_plus. f_equal;field;lra.
Qed.

Lemma tail_integral_substitution x b : 0<x ->
  RInt (tail_integrand ((/x)*(/x))) 0 b=
    (2*x*exp(x*x))*RInt gaussian x (x+b/(2*x)).
Proof.
  intros X.
  assert (Scaled : RInt (tail_integrand ((/x)*(/x))) 0 b=
    exp(x*x)*RInt (tail_shifted_gaussian x) 0 b).
  { transitivity (RInt(fun u=>exp(x*x)*tail_shifted_gaussian x u)0 b).
    - apply RInt_ext;intros u U;apply tail_integrand_gaussian;exact X.
    - exact (@RInt_scal R_CompleteNormedModule (tail_shifted_gaussian x) 0 b
        (exp(x*x)) (tail_shifted_integrable x 0 b X)). }
  pose proof(@RInt_comp_lin R_CompleteNormedModule gaussian (/(2*x)) x 0 b
    (gaussian_integrable (/(2*x)*0+x) (/(2*x)*b+x))) as Change.
  replace (/(2*x)*0+x) with x in Change by ring.
  replace (/(2*x)*b+x) with (x+b/(2*x)) in Change by (unfold Rdiv;ring).
  assert (Integral : RInt gaussian x (x+b/(2*x))=
    (/(2*x))*RInt(tail_shifted_gaussian x)0 b).
  { rewrite <- Change.
    transitivity (RInt(fun u=>/(2*x)*tail_shifted_gaussian x u)0 b).
    - apply RInt_ext;intros u U.
      change (/(2*x)*gaussian(/(2*x)*u+x)=/(2*x)*gaussian(x+u/(2*x))). f_equal.
      f_equal;unfold Rdiv;ring.
    - exact (@RInt_scal R_CompleteNormedModule (tail_shifted_gaussian x) 0 b
        (/(2*x)) (tail_shifted_integrable x 0 b X)). }
  rewrite Scaled,Integral.
  change (@eq R (exp(x*x)*RInt(tail_shifted_gaussian x)0 b)
    ((2*x*exp(x*x))*(/(2*x)*RInt(tail_shifted_gaussian x)0 b))).
  field;lra.
Qed.

Lemma gaussian_tail_endpoints_unbounded x : 0<x ->
  is_lim_seq (fun n=>x+INR n/(2*x)) p_infty.
Proof.
  intros X. apply (proj1(is_lim_seq_spec _ p_infty)). intros M.
  pose proof(proj2(is_lim_seq_spec INR p_infty) is_lim_seq_INR) as Naturals.
  destruct(Naturals (2*x*(M-x))) as [N Bound]. exists N;intros n Hn.
  specialize(Bound n Hn).
  assert (Cancel : (INR n/(2*x))*(2*x)=INR n) by (field;lra).
  nra.
Qed.

Theorem normalized_tail_gaussian_identity x : 0<x ->
  tail_integral ((/x)*(/x))=
    (2*x*exp(x*x))*(gaussian_mass-RInt gaussian 0 x).
Proof.
  intros X.
  pose proof(gaussian_tail_endpoints_unbounded x X) as Endpoints.
  assert (Positive : eventually(fun n=>1<=x+INR n/(2*x))).
  { pose proof(proj2(is_lim_seq_spec _ p_infty) Endpoints) as Beyond.
    destruct(Beyond 1) as [N Bound]. exists N;intros n Hn;specialize(Bound n Hn);lra. }
  pose proof(gaussian_integral_limit _ Positive Endpoints) as Primitive.
  pose proof(is_lim_seq_minus' _ (fun _=>RInt gaussian 0 x) _ _ Primitive
    (is_lim_seq_const (RInt gaussian 0 x))) as Difference.
  assert (Segments : is_lim_seq (fun n=>RInt gaussian x (x+INR n/(2*x)))
    (gaussian_mass-RInt gaussian 0 x)).
  { eapply is_lim_seq_ext;[|exact Difference]. intros n.
    pose proof(RInt_Chasles gaussian 0 x (x+INR n/(2*x))
      (gaussian_integrable 0 x) (gaussian_integrable x (x+INR n/(2*x)))) as Split.
    change (RInt gaussian 0 x+RInt gaussian x (x+INR n/(2*x))=
      RInt gaussian 0 (x+INR n/(2*x))) in Split.
    change (RInt gaussian 0 (x+INR n/(2*x))-RInt gaussian 0 x=
      RInt gaussian x (x+INR n/(2*x)));lra. }
  pose proof(is_lim_seq_mult' (fun _=>2*x*exp(x*x)) _ (2*x*exp(x*x)) _
    (is_lim_seq_const (2*x*exp(x*x))) Segments) as Scaled.
  assert (Transformed : is_lim_seq (tail_integral_sequence ((/x)*(/x)))
    ((2*x*exp(x*x))*(gaussian_mass-RInt gaussian 0 x))).
  { eapply is_lim_seq_ext;[|exact Scaled]. intros n.
    unfold tail_integral_sequence. symmetry;apply tail_integral_substitution;exact X. }
  destruct(tail_integral_limit ((/x)*(/x)) ltac:(nra)) as [Original Bounds].
  pose proof(is_lim_seq_unique _ _ Original) as A.
  pose proof(is_lim_seq_unique _ _ Transformed) as B. congruence.
Qed.

Theorem positive_erfcx_gaussian x : 0<x -> positive_erfcx x=gaussian_erfcx x.
Proof.
  intros X. unfold positive_erfcx,gaussian_erfcx.
  rewrite normalized_tail_gaussian_identity by exact X.
  assert (Normalization : 2*inv_sqrt_pi*gaussian_mass=1).
  { unfold inv_sqrt_pi,gaussian_mass.
    assert (P : sqrt PI<>0).
    { pose proof(sqrt_sqrt PI (Rlt_le _ _ PI_RGT_0));intros Zero;rewrite Zero in H;pose proof PI_RGT_0;nra. }
    field;exact P. }
  replace 1 with (2*inv_sqrt_pi*gaussian_mass) by (symmetry;exact Normalization).
  field;lra.
Qed.
