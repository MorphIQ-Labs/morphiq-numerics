(** Gaussian normalization without assuming an improper-integral identity.
    For I(x)=integral_0^x exp(-u^2) du and
    J(x)=integral_0^1 exp(-x^2*(1+t^2))/(1+t^2) dt,
    differentiation gives (I(x)^2+J(x))'=0 and J(0)=pi/4. *)
From Coq Require Import Reals Lia Lra Psatz.
From Coquelicot Require Import Coquelicot.
From Interval Require Import Tactic.
Require Import ErfcxTaylorODE ErfcxGaussianSeries ErfcxGaussianTarget ErfcxMoments.
Open Scope R_scope.

Definition gaussian_box_integrand x t := exp(-x*x*(1+t*t))/(1+t*t).
Definition gaussian_box x := RInt (gaussian_box_integrand x) 0 1.

Lemma gaussian_box_integrable x a b : ex_RInt (gaussian_box_integrand x) a b.
Proof.
  apply (@ex_RInt_continuous R_CompleteNormedModule). intros t T.
  apply (@ex_derive_continuous R_AbsRing R_CompleteNormedModule).
  unfold gaussian_box_integrand. eexists. auto_derive; repeat split; nra.
Qed.

Lemma gaussian_primitive_derivative x :
  is_derive (fun z=>RInt gaussian 0 z) x (gaussian x).
Proof.
  apply (@is_derive_RInt R_CompleteNormedModule gaussian (fun z=>RInt gaussian 0 z) 0 x).
  - apply filter_forall. intros z;apply RInt_correct,gaussian_integrable.
  - apply gaussian_continuous.
Qed.

Lemma gaussian_box_integrand_derivative x t :
  is_derive (fun u=>gaussian_box_integrand u t) x (-2*x*exp(-x*x*(1+t*t))).
Proof.
  unfold gaussian_box_integrand. auto_derive;[repeat split;nra|].
  field; nra.
Qed.

Lemma gaussian_box_integrand_Derive x t :
  Derive (fun u=>gaussian_box_integrand u t) x = -2*x*exp(-x*x*(1+t*t)).
Proof. apply is_derive_unique,gaussian_box_integrand_derivative. Qed.

Lemma gaussian_box_derivative_continuous x t :
  continuity_2d_pt (fun u v=>Derive(fun z=>gaussian_box_integrand z v)u) x t.
Proof.
  eapply continuity_2d_pt_ext.
  - intros u v; symmetry;apply gaussian_box_integrand_Derive.
  - apply continuity_2d_pt_mult.
    + apply continuity_2d_pt_mult;[apply continuity_2d_pt_const|apply continuity_2d_pt_id1].
    + apply continuity_1d_2d_pt_comp;[apply derivable_continuous_pt,derivable_pt_exp|].
      repeat first [apply continuity_2d_pt_mult|apply continuity_2d_pt_plus|
        apply continuity_2d_pt_opp|apply continuity_2d_pt_const|
        apply continuity_2d_pt_id1|apply continuity_2d_pt_id2].
Qed.

Theorem gaussian_box_derivative x :
  is_derive gaussian_box x (-2*gaussian x*RInt gaussian 0 x).
Proof.
  pose proof (is_derive_RInt_param gaussian_box_integrand 0 1 x) as Param.
  assert (D : is_derive gaussian_box x
    (RInt (fun t=>Derive(fun u=>gaussian_box_integrand u t)x) 0 1)).
  { apply Param.
    - apply filter_forall. intros u t T. eexists;apply gaussian_box_integrand_derivative.
    - intros t T;apply gaussian_box_derivative_continuous.
    - apply filter_forall. intros u;apply gaussian_box_integrable. }
  assert (Integral : RInt (fun t=>Derive(fun u=>gaussian_box_integrand u t)x) 0 1=
    (-2*x*gaussian x)*RInt (gaussian_scaled x) 0 1).
  { transitivity (RInt (fun t=>(-2*x*gaussian x)*gaussian_scaled x t) 0 1).
    - apply RInt_ext. intros t T. rewrite gaussian_box_integrand_Derive.
      unfold gaussian_scaled,gaussian.
      assert (E : exp(-x*x*(1+t*t))=exp(-x*x)*exp(-(x*t)*(x*t)))
        by (rewrite <- exp_plus;f_equal;ring).
      rewrite E, !Rmult_assoc;reflexivity.
    - exact (@RInt_scal R_CompleteNormedModule (gaussian_scaled x) 0 1
        (-2*x*gaussian x) (gaussian_scaled_integrable x 0 1)). }
  rewrite Integral in D. rewrite gaussian_integral_scaled.
  replace (-2*gaussian x*(x*RInt(gaussian_scaled x)0 1)) with
    ((-2*x*gaussian x)*RInt(gaussian_scaled x)0 1) by ring. exact D.
Qed.

Lemma gaussian_box_at_zero : gaussian_box 0=PI/4.
Proof.
  assert (Integral : is_RInt (fun t : R=>/(1+t*t)) 0 1 (atan 1-atan 0)).
  { apply (is_RInt_derive atan).
    - intros t T. replace (1+t*t) with (1+t²) by (unfold Rsqr;ring).
      apply is_derive_atan.
    - intros t T. apply (@ex_derive_continuous R_AbsRing R_CompleteNormedModule).
      eexists;auto_derive;repeat split;nra. }
  rewrite atan_1,atan_0,Rminus_0_r in Integral.
  unfold gaussian_box.
  transitivity (RInt (fun t : R=>/(1+t*t)) 0 1).
  - apply RInt_ext. intros t T. unfold gaussian_box_integrand.
    replace (-0*0*(1+t*t)) with 0 by ring. rewrite exp_0.
    change (1*/(1+t*t)=/(1+t*t));ring.
  - apply is_RInt_unique;exact Integral.
Qed.

Definition gaussian_box_invariant x :=
  RInt gaussian 0 x*RInt gaussian 0 x+gaussian_box x.

Lemma gaussian_box_invariant_derivative x : is_derive gaussian_box_invariant x 0.
Proof.
  pose proof(gaussian_primitive_derivative x) as D.
  pose proof(is_derive_mult _ _ x _ _ D D Rmult_comm) as Square.
  pose proof(is_derive_plus _ _ x _ _ Square (gaussian_box_derivative x)) as Sum.
  change (is_derive gaussian_box_invariant x
    ((gaussian x*RInt gaussian 0 x+RInt gaussian 0 x*gaussian x)+
    (-2*gaussian x*RInt gaussian 0 x))) in Sum.
  replace ((gaussian x*RInt gaussian 0 x+RInt gaussian 0 x*gaussian x)+
    (-2*gaussian x*RInt gaussian 0 x)) with 0 in Sum by ring.
  exact Sum.
Qed.

Theorem gaussian_square_identity x : 0<=x ->
  RInt gaussian 0 x*RInt gaussian 0 x+gaussian_box x=PI/4.
Proof.
  intros X.
  assert (Initial : gaussian_box_invariant 0=PI/4).
  { unfold gaussian_box_invariant;rewrite RInt_point,gaussian_box_at_zero.
    change (0*0+PI/4=PI/4);ring. }
  change (gaussian_box_invariant x=PI/4).
  destruct(Rle_lt_or_eq_dec _ _ X) as [Positive|Zero].
  - destruct(MVT_cor2 gaussian_box_invariant (fun _=>0) 0 x Positive)
      as [c [Difference Range]].
    + intros c C;apply is_derive_Reals,gaussian_box_invariant_derivative.
    + lra.
  - rewrite <- Zero;exact Initial.
Qed.

Lemma gaussian_box_bounds x : 0<=gaussian_box x<=gaussian x.
Proof.
  assert (Point : forall t, 0<=gaussian_box_integrand x t<=gaussian x).
  { intros t.
    assert (Den : 0<1+t*t) by nra.
    assert (Inv : 0</(1+t*t)<=1).
    { split;[apply Rinv_0_lt_compat;exact Den|].
      replace 1 with (/1) at 2 by field. apply Rinv_le_contravar;nra. }
    assert (E : exp(-x*x*(1+t*t))<=gaussian x).
    { unfold gaussian. assert (P : -x*x*(1+t*t)<= -x*x) by nra.
      destruct(Rle_lt_or_eq_dec _ _ P) as [Lt|Eq].
      - apply Rlt_le,exp_increasing;exact Lt.
      - rewrite Eq;lra. }
    pose proof(exp_pos(-x*x*(1+t*t))).
    unfold gaussian_box_integrand,Rdiv;split;nra. }
  split.
  - apply RInt_ge_0;[lra|apply gaussian_box_integrable|].
    intros t T;exact(proj1(Point t)).
  - apply Rle_trans with (RInt(fun _ : R=>gaussian x)0 1).
    + apply RInt_le;[lra|apply gaussian_box_integrable|apply ex_RInt_const|].
      intros t T;exact(proj2(Point t)).
    + rewrite RInt_const. change ((1-0)*gaussian x<=gaussian x);lra.
Qed.

Definition gaussian_mass : R := sqrt PI/2.

Lemma gaussian_mass_bounds : /2<gaussian_mass<1.
Proof. unfold gaussian_mass;interval with(i_prec 80). Qed.

Lemma gaussian_mass_square : gaussian_mass*gaussian_mass=PI/4.
Proof.
  unfold gaussian_mass.
  pose proof(sqrt_sqrt PI (Rlt_le _ _ PI_RGT_0)) as S.
  nra.
Qed.

Theorem gaussian_integral_remainder_bound x : 0<=x ->
  0<=gaussian_mass-RInt gaussian 0 x<=2*gaussian x.
Proof.
  intros X.
  assert (I : 0<=RInt gaussian 0 x).
  { apply RInt_ge_0;[exact X|apply gaussian_integrable|].
    intros t T;unfold gaussian;apply Rlt_le,exp_pos. }
  pose proof(gaussian_square_identity x X) as Identity.
  pose proof(gaussian_box_bounds x) as Box.
  pose proof gaussian_mass_bounds as Mass.
  pose proof gaussian_mass_square as Square.
  assert (Order : RInt gaussian 0 x<=gaussian_mass) by nra.
  assert (Factor : (gaussian_mass-RInt gaussian 0 x)*
    (gaussian_mass+RInt gaussian 0 x)=gaussian_box x) by nra.
  split;[lra|]. nra.
Qed.

Lemma gaussian_integral_remainder_reciprocal x : 1<=x ->
  0<=gaussian_mass-RInt gaussian 0 x<=2/x.
Proof.
  intros X.
  pose proof(gaussian_integral_remainder_bound x ltac:(lra)) as Bound.
  pose proof(exponential_moment_bound 0 x ltac:(lra)) as Exp.
  unfold exponential_moment in Exp;cbn [pow fact INR] in Exp;rewrite Rmult_1_l in Exp.
  change (0<=exp(-x)<=1/x) in Exp.
  assert (Gaussian : gaussian x<=exp(-x)).
  { unfold gaussian. destruct(Req_dec x 1) as [One|NotOne].
    - rewrite One;right;f_equal;ring.
    - apply Rlt_le,exp_increasing;nra. }
  unfold Rdiv in *;split;nra.
Qed.

(** The limit holds along every positive unbounded argument sequence, not
    just integer endpoints; the tail substitution uses affine endpoints. *)
Theorem gaussian_integral_limit u :
  eventually(fun n=>1<=u n) -> is_lim_seq u p_infty ->
  is_lim_seq (fun n=>RInt gaussian 0 (u n)) gaussian_mass.
Proof.
  intros Positive Unbounded.
  assert (Gap : is_lim_seq (fun n=>gaussian_mass-RInt gaussian 0 (u n)) 0).
  { apply (is_lim_seq_le_le_loc (fun _=>0) _ (fun n=>2/u n)).
    - destruct Positive as [N Positive]. exists N;intros n Hn.
      apply gaussian_integral_remainder_reciprocal,Positive;exact Hn.
    - apply is_lim_seq_const.
    - apply (is_lim_seq_div _ _ 2 p_infty 0).
      + apply is_lim_seq_const.
      + exact Unbounded.
      + discriminate.
      + unfold is_Rbar_div,is_Rbar_mult;simpl;rewrite Rmult_0_r;reflexivity. }
  pose proof(is_lim_seq_minus' (fun _=>gaussian_mass)
    (fun n=>gaussian_mass-RInt gaussian 0 (u n)) gaussian_mass 0
    (is_lim_seq_const gaussian_mass) Gap) as Limit.
  rewrite Rminus_0_r in Limit.
  eapply is_lim_seq_ext;[|exact Limit]. intros n.
  change (gaussian_mass-(gaussian_mass-RInt gaussian 0 (u n))=RInt gaussian 0 (u n));ring.
Qed.
