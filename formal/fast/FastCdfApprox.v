(** The bounded normal CDF's tail rational against erfcx: relative error at
    most [2^-56 + 2^-53 sqrt(pi)/2] on [15/32 <= y <= 91/16], from the ODE
    comparison (FastCdfOde), the residual enclosures (FastCdfResidual) and the
    anchor at erfcx Taylor centre 126 (FastCdfAnchor). *)
From Coq Require Import Reals Lra Psatz.
From Coquelicot Require Import Coquelicot.
From Binary64 Require Import IEEE64.
Require Import ErfcxConstants ErfcxGaussianTarget NormalErfcxSensitivity
  FastCdfConstants FastCdfResidual FastCdfAnchor FastCdfOde.
Open Scope R_scope.

Definition cdf_tail_ratio t := cdf_tail_num t / cdf_tail_den t.
Definition cdf_tail_rho t := cdf_tail_residual t / cdf_tail_den t ^ 2.

Lemma cdf_horner_derivative cs t : is_derive (cdf_horner cs) t (cdf_dhorner cs t).
Proof.
  induction cs as [ | c r IH].
  - apply (is_derive_ext (fun _ => 0)); [intros; reflexivity | ]. apply (@is_derive_const R_AbsRing).
  - apply (is_derive_ext (fun u => c + u * cdf_horner r u)); [intros; reflexivity | ].
    evar (d : R). replace (cdf_dhorner (c :: r) t) with d.
    + apply (@is_derive_plus R_AbsRing R_NormedModule (fun _ => c) (fun u => u * cdf_horner r u)).
      * apply (@is_derive_const R_AbsRing).
      * apply (@is_derive_mult R_AbsRing); [apply (@is_derive_id R_AbsRing) | exact IH | intros; apply Rmult_comm].
    + unfold d. simpl. unfold plus, mult, zero, one; simpl. ring.
Qed.

Lemma cdf_dhorner_ex cs t : ex_derive (cdf_dhorner cs) t.
Proof.
  induction cs as [ | c r IH].
  - exists 0. apply (is_derive_ext (fun _ => 0)); [intros; reflexivity | ]. apply (@is_derive_const R_AbsRing).
  - apply (ex_derive_ext (fun u => cdf_horner r u + u * cdf_dhorner r u)); [intros; reflexivity | ].
    assert (H : ex_derive (cdf_horner r) t) by (eexists; apply cdf_horner_derivative).
    auto_derive; repeat split; assumption.
Qed.

Lemma cdf_tail_num_derivative t : is_derive cdf_tail_num t (cdf_tail_dnum t).
Proof. apply cdf_horner_derivative. Qed.

Lemma cdf_tail_den_derivative t : is_derive cdf_tail_den t (cdf_tail_dden t).
Proof. apply cdf_horner_derivative. Qed.

Lemma cdf_tail_ratio_derivative t : 1 <= cdf_tail_den t ->
  is_derive cdf_tail_ratio t (2 * t * cdf_tail_ratio t - 2 * inv_sqrt_pi + cdf_tail_rho t).
Proof.
  intros D.
  pose proof (is_derive_div cdf_tail_num cdf_tail_den t (cdf_tail_dnum t) (cdf_tail_dden t)
    (cdf_tail_num_derivative t) (cdf_tail_den_derivative t) ltac:(lra)) as Dv.
  replace (2 * t * cdf_tail_ratio t - 2 * inv_sqrt_pi + cdf_tail_rho t)
    with ((cdf_tail_dnum t * cdf_tail_den t - cdf_tail_num t * cdf_tail_dden t) / (cdf_tail_den t ^ 2)).
  - unfold cdf_tail_ratio. exact Dv.
  - unfold cdf_tail_rho, cdf_tail_residual, cdf_tail_ratio.
    set (n := cdf_tail_num t) in *. set (d := cdf_tail_den t) in *. set (dn := cdf_tail_dnum t) in *. set (dd := cdf_tail_dden t) in *.
    field. lra.
Qed.

Lemma cdf_tail_rho_continuous t : 1 <= cdf_tail_den t -> continuous cdf_tail_rho t.
Proof.
  intros D.
  assert (N : ex_derive cdf_tail_num t) by (eexists; apply cdf_tail_num_derivative).
  assert (Dd : ex_derive cdf_tail_den t) by (eexists; apply cdf_tail_den_derivative).
  assert (N' : ex_derive cdf_tail_dnum t) by apply cdf_dhorner_ex.
  assert (D' : ex_derive cdf_tail_dden t) by apply cdf_dhorner_ex.
  apply (@ex_derive_continuous R_AbsRing R_NormedModule).
  unfold cdf_tail_rho, cdf_tail_residual.
  auto_derive; repeat split; try assumption; nra.
Qed.

Lemma cdf_tail_rho_bound t : 15/32 <= t <= 91/16 -> Rabs (cdf_tail_rho t) <= / 2 ^ 53.
Proof.
  intros T. destruct (cdf_residual_bound t T) as [Q D].
  unfold cdf_tail_rho. unfold Rdiv. rewrite Rabs_mult, Rabs_Rinv, (Rabs_pos_eq (cdf_tail_den t ^ 2)) by nra.
  apply (Rmult_le_reg_r (cdf_tail_den t ^ 2)); [nra | ].
  rewrite Rmult_assoc, Rinv_l, Rmult_1_r by nra. exact Q.
Qed.

Theorem cdf_tail_approx y : 15/32 <= y <= 91/16 ->
  Rabs (cdf_tail_ratio y - gaussian_erfcx y) <=
    (/ 2 ^ 56 + / 2 ^ 53 * / (2 * inv_sqrt_pi)) * gaussian_erfcx y.
Proof.
  intros Y.
  apply (cdf_ode_relative cdf_tail_ratio cdf_tail_rho y (91/16) (/ 2 ^ 53) (/ 2 ^ 56)).
  - lra.
  - apply Rlt_le, Rinv_0_lt_compat, pow_lt; lra.
  - apply Rlt_le, Rinv_0_lt_compat, pow_lt; lra.
  - intros t T. apply cdf_tail_ratio_derivative. exact (proj2 (cdf_residual_bound t ltac:(lra))).
  - intros t T. apply cdf_tail_rho_continuous. exact (proj2 (cdf_residual_bound t ltac:(lra))).
  - intros t T. apply cdf_tail_rho_bound. lra.
  - apply Rlt_le, normal_erfcx_positive. lra.
  - exact cdf_anchor_error.
Qed.
