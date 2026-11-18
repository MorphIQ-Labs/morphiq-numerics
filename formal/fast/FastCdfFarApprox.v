(** Uniform approximation for the fixed-coefficient far-tail ratio.
    The polynomial solves the scaled Mills-ratio ODE up to a certified residual;
    a Gaussian-integral anchor closes the comparison at y=16. *)
From Coq Require Import Reals Lra Psatz.
From Coquelicot Require Import Coquelicot.
From Flocq Require Import Core.
Require Import StageGappa ErfcxConstants ErfcxGaussianTarget NormalErfcxSensitivity
  FastCdfConstants FastCdfFarConstants FastCdfFarResidual FastCdfFarAnchor FastCdfOde FastCdfApprox.
Open Scope R_scope.

Definition cdf_far_rho y := -2*inv_sqrt_pi*cdf_far_residual (1/(2*y*y)).

Lemma cdf_far_real_derivative y : 0<y ->
  is_derive cdf_far_real y (2*y*cdf_far_real y-2*inv_sqrt_pi+cdf_far_rho y).
Proof.
  intros Y.
  assert (Idx : is_derive (fun u : R => 1/(2*u*u)) y (-1/(y*y*y))).
  { auto_derive; [repeat split; nra|unfold plus,mult,opp,minus,one,zero; simpl; field; lra]. }
  pose proof (is_derive_comp (cdf_horner cdf_far_words)
    (fun u : R => 1/(2*u*u)) y (cdf_dhorner cdf_far_words (1/(2*y*y)))
    (-1/(y*y*y)) (cdf_horner_derivative _ _) Idx) as P.
  assert (D : is_derive (fun u : R => inv_sqrt_pi/u) y (-inv_sqrt_pi/(y*y))).
  { auto_derive; [repeat split; lra|unfold plus,mult,opp,minus,one,zero; simpl; field; lra]. }
  pose proof (@is_derive_mult R_AbsRing
    (fun u : R => inv_sqrt_pi/u)
    (fun u : R => cdf_horner cdf_far_words (1/(2*u*u))) y
    (-inv_sqrt_pi/(y*y))
    ((-1/(y*y*y)) * cdf_dhorner cdf_far_words (1/(2*y*y)))
    D P ltac:(intros; apply Rmult_comm)) as V.
  unfold cdf_far_real,cdf_far_rho,cdf_far_residual,cdf_far_poly,cdf_far_dpoly.
  replace (2*y*(inv_sqrt_pi/y*cdf_horner cdf_far_words (1/(2*y*y)))
    -2*inv_sqrt_pi + -2*inv_sqrt_pi*
      (2*(1/(2*y*y))*(1/(2*y*y))*cdf_dhorner cdf_far_words (1/(2*y*y))
       +(1+1/(2*y*y))*cdf_horner cdf_far_words (1/(2*y*y))-1))
    with ((-inv_sqrt_pi/(y*y))*cdf_horner cdf_far_words (1/(2*y*y))
      +(inv_sqrt_pi/y)*((-1/(y*y*y))*cdf_dhorner cdf_far_words (1/(2*y*y)))).
  - exact V.
  - field; lra.
Qed.

Lemma cdf_far_rho_continuous y : 0<y -> continuous cdf_far_rho y.
Proof.
  intros Y.
  assert (H : ex_derive (cdf_horner cdf_far_words) (1/(2*y*y)))
    by (eexists;apply cdf_horner_derivative).
  assert (D : ex_derive (cdf_dhorner cdf_far_words) (1/(2*y*y)))
    by apply cdf_dhorner_ex.
  apply (@ex_derive_continuous R_AbsRing R_NormedModule).
  unfold cdf_far_rho,cdf_far_residual,cdf_far_poly,cdf_far_dpoly.
  set (h:=cdf_horner cdf_far_words) in *.
  set (d:=cdf_dhorner cdf_far_words) in *.
  clearbody h d.
  auto_derive; repeat split; try assumption; nra.
Qed.

Lemma cdf_far_index_range y : 0<=y<=16 -> 32<=y*y ->
  1/512<=1/(2*y*y)<=1/64.
Proof.
  intros Y Square. unfold Rdiv; rewrite !Rmult_1_l.
  split; apply Rinv_le_contravar; nra.
Qed.

Lemma cdf_far_rho_bound y : 0<=y<=16 -> 32<=y*y ->
  Rabs(cdf_far_rho y)<=2*inv_sqrt_pi*(/2^54).
Proof.
  intros Y Square.
  pose proof (cdf_far_residual_bound _ (cdf_far_index_range y Y Square)) as R.
  unfold cdf_far_rho. rewrite Rabs_mult,Rabs_mult.
  replace (Rabs (-2)) with 2 by (rewrite Rabs_left; lra).
  rewrite (Rabs_pos_eq inv_sqrt_pi) by
    (pose proof inv_sqrt_pi_positive; lra).
  apply Rmult_le_compat_l; [pose proof inv_sqrt_pi_positive; lra|exact R].
Qed.

Theorem cdf_far_poly_approx y : 0<=y<=16 -> 32<=y*y ->
  Rabs(cdf_far_real y-gaussian_erfcx y)<=bpow radix2(-53)*gaussian_erfcx y.
Proof.
  intros Y Square. assert (Ypos : 0<y) by nra.
  pose proof inv_sqrt_pi_positive as I.
  assert (E : 0<=gaussian_erfcx y) by (apply Rlt_le,normal_erfcx_positive;lra).
  assert (C : Rabs(cdf_far_real y-gaussian_erfcx y)<=
    (/2^55+(2*inv_sqrt_pi*(/2^54))*/(2*inv_sqrt_pi))*gaussian_erfcx y).
  { apply (cdf_ode_relative cdf_far_real cdf_far_rho y 16
      (2*inv_sqrt_pi*(/2^54)) (/2^55)).
    - lra.
    - apply Rmult_le_pos; [lra|apply Rlt_le,Rinv_0_lt_compat,pow_lt;lra].
    - apply Rlt_le,Rinv_0_lt_compat,pow_lt;lra.
    - intros t T. apply cdf_far_real_derivative;lra.
    - intros t T. apply cdf_far_rho_continuous;lra.
    - intros t T. apply cdf_far_rho_bound;[lra|nra].
    - apply Rlt_le,normal_erfcx_positive;lra.
    - exact cdf_far_anchor_error. }
  eapply Rle_trans; [exact C|]. apply Rmult_le_compat_r; [exact E|].
  replace ((2*inv_sqrt_pi*(/2^54))*/(2*inv_sqrt_pi)) with (/2^54) by (field;lra).
  bpow_num; lra.
Qed.
