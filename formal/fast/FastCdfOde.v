(** The ODE comparison behind the bounded normal CDF's tail rational.

    erfcx solves [f' = 2 t f - 2/sqrt pi]. A function [Rf] with the same
    equation up to a residual [rho] stays close to erfcx: integrating
    [(Rf - erfcx) exp(-t^2)], whose derivative is [rho exp(-t^2)], from a right
    endpoint [Y] where both are known gives the bound at every [y <= Y]. *)
From Coq Require Import Reals Lra Psatz.
From Coquelicot Require Import Coquelicot.
Require Import ErfcxConstants ErfcxTaylorODE ErfcxGaussianTarget.
Open Scope R_scope.

Lemma cdf_gaussian_derivative t : is_derive gaussian t (-2 * t * gaussian t).
Proof. unfold gaussian. auto_derive; [exact I | ring_simplify; replace (- t * t) with (- t ^ 2) by ring; ring]. Qed.

Lemma cdf_gaussian_scale t : gaussian t * exp (t * t) = 1.
Proof.
  unfold gaussian. rewrite <- exp_plus. replace (- t * t + t * t) with 0 by ring. apply exp_0.
Qed.

Lemma cdf_gaussian_positive t : 0 < gaussian t.
Proof. apply exp_pos. Qed.

Section Compare.
Variables (Rf rho : R -> R) (y Y M : R).
Hypothesis Order : y <= Y.
Hypothesis Derivative : forall t, y <= t <= Y ->
  is_derive Rf t (2 * t * Rf t - 2 * inv_sqrt_pi + rho t).
Hypothesis Continuous : forall t, y <= t <= Y -> continuous rho t.
Hypothesis Bound : forall t, y <= t <= Y -> Rabs (rho t) <= M.

Let g t := (Rf t - gaussian_erfcx t) * gaussian t.

Lemma cdf_ode_derivative t : y <= t <= Y -> is_derive g t (rho t * gaussian t).
Proof.
  intros T. unfold g.
  apply (is_derive_ext (fun u => (Rf u - gaussian_erfcx u) * gaussian u)); [reflexivity | ].
  evar (d : R). replace (rho t * gaussian t) with d.
  - apply (@is_derive_mult R_AbsRing).
    + apply (@is_derive_minus R_AbsRing R_NormedModule); [exact (Derivative t T) | apply gaussian_erfcx_derivative].
    + apply cdf_gaussian_derivative.
    + intros n m; apply Rmult_comm.
  - unfold d. simpl. unfold minus, plus, mult, opp; simpl. ring.
Qed.

Lemma cdf_ode_integrand_continuous t : y <= t <= Y -> continuous (fun u => rho u * gaussian u) t.
Proof.
  intros T. apply (@continuous_mult R_UniformSpace R_AbsRing); [exact (Continuous t T) | apply gaussian_continuous].
Qed.

Theorem cdf_ode_compare :
  Rabs (Rf y - gaussian_erfcx y) <=
    Rabs (Rf Y - gaussian_erfcx Y) * exp (y * y - Y * Y) + M * (exp (y * y) * RInt gaussian y Y).
Proof.
  assert (Ftc : is_RInt (fun u => rho u * gaussian u) y Y (minus (g Y) (g y))).
  { apply (@is_RInt_derive R_CompleteNormedModule).
    - intros t T. rewrite Rmin_left, Rmax_right in T by exact Order. exact (cdf_ode_derivative t T).
    - intros t T. rewrite Rmin_left, Rmax_right in T by exact Order. exact (cdf_ode_integrand_continuous t T). }
  assert (Ex : ex_RInt (fun u => rho u * gaussian u) y Y) by (eexists; exact Ftc).
  apply (@is_RInt_unique R_CompleteNormedModule) in Ftc. unfold minus, plus, opp in Ftc; simpl in Ftc.
  assert (Abs : Rabs (RInt (fun u => rho u * gaussian u) y Y) <= M * RInt gaussian y Y).
  { eapply Rle_trans; [apply abs_RInt_le; [exact Order | exact Ex] | ].
    pose proof (@RInt_scal R_CompleteNormedModule gaussian y Y M (gaussian_integrable y Y)) as Sc.
    unfold scal in Sc; simpl in Sc; unfold mult in Sc; simpl in Sc. rewrite <- Sc.
    apply RInt_le; [exact Order | | | ].
    - apply (@ex_RInt_continuous R_CompleteNormedModule). intros t T.
      rewrite Rmin_left, Rmax_right in T by exact Order.
      apply (@continuous_comp R_UniformSpace R_UniformSpace R_UniformSpace
        (fun u => rho u * gaussian u) Rabs); [exact (cdf_ode_integrand_continuous t T) | ].
      apply continuous_Rabs.
    - apply (@ex_RInt_scal R_CompleteNormedModule); apply gaussian_integrable.
    - intros t T. unfold scal; simpl; unfold mult; simpl.
      rewrite Rabs_mult, (Rabs_pos_eq (gaussian t)) by (apply Rlt_le, cdf_gaussian_positive).
      apply Rmult_le_compat_r; [apply Rlt_le, cdf_gaussian_positive | apply Bound; lra]. }
  assert (Gy : g y = g Y - RInt (fun u => rho u * gaussian u) y Y) by lra.
  assert (Back : Rf y - gaussian_erfcx y = g y * exp (y * y)).
  { unfold g. rewrite Rmult_assoc, cdf_gaussian_scale. ring. }
  assert (GY : g Y * exp (y * y) = (Rf Y - gaussian_erfcx Y) * exp (y * y - Y * Y)).
  { unfold g, gaussian. rewrite Rmult_assoc, <- exp_plus. f_equal; f_equal; ring. }
  rewrite Back, Gy.
  replace ((g Y - RInt (fun u => rho u * gaussian u) y Y) * exp (y * y))
    with (g Y * exp (y * y) - RInt (fun u => rho u * gaussian u) y Y * exp (y * y)) by ring.
  rewrite GY.
  eapply Rle_trans; [apply Rabs_triang | ].
  rewrite Rabs_Ropp, !Rabs_mult, (Rabs_pos_eq (exp (y * y - Y * Y))), (Rabs_pos_eq (exp (y * y)))
    by (apply Rlt_le, exp_pos).
  apply Rplus_le_compat_l.
  replace (M * (exp (y * y) * RInt gaussian y Y)) with (M * RInt gaussian y Y * exp (y * y)) by ring.
  apply Rmult_le_compat_r; [apply Rlt_le, exp_pos | exact Abs].
Qed.
End Compare.

(** [exp(y^2) * int_y^Y exp(-t^2) dt = sqrt(pi)/2 * (erfcx y - exp(y^2 - Y^2) erfcx Y)]. *)
Lemma cdf_gaussian_gap y Y :
  exp (y * y) * RInt gaussian y Y =
    / (2 * inv_sqrt_pi) * (gaussian_erfcx y - exp (y * y - Y * Y) * gaussian_erfcx Y).
Proof.
  assert (Split : RInt gaussian y Y = RInt gaussian 0 Y - RInt gaussian 0 y).
  { pose proof (@RInt_Chasles R_CompleteNormedModule gaussian 0 y Y
                  (gaussian_integrable 0 y) (gaussian_integrable y Y)) as C.
    change (RInt gaussian 0 y + RInt gaussian y Y = RInt gaussian 0 Y) in C. lra. }
  assert (I : 0 < inv_sqrt_pi) by apply inv_sqrt_pi_positive.
  unfold gaussian_erfcx. rewrite Split.
  assert (E : exp (y * y - Y * Y) * exp (Y * Y) = exp (y * y))
    by (rewrite <- exp_plus; f_equal; ring).
  replace (exp (y * y - Y * Y) * (exp (Y * Y) * (1 - 2 * inv_sqrt_pi * RInt gaussian 0 Y)))
    with (exp (y * y) * (1 - 2 * inv_sqrt_pi * RInt gaussian 0 Y))
    by (rewrite <- Rmult_assoc, E; reflexivity).
  field. lra.
Qed.

(** The erfcx difference is nonnegative: [exp(y^2 - Y^2) erfcx Y <= erfcx y]. *)
Lemma cdf_erfcx_decay y Y : y <= Y -> exp (y * y - Y * Y) * gaussian_erfcx Y <= gaussian_erfcx y.
Proof.
  intros O. pose proof (cdf_gaussian_gap y Y) as G.
  assert (Nonneg : 0 <= RInt gaussian y Y).
  { apply RInt_ge_0; [exact O | apply gaussian_integrable | intros t _; apply Rlt_le, cdf_gaussian_positive]. }
  assert (I : 0 < inv_sqrt_pi) by apply inv_sqrt_pi_positive.
  assert (0 <= exp (y * y) * RInt gaussian y Y) by (apply Rmult_le_pos; [apply Rlt_le, exp_pos | exact Nonneg]).
  assert (P : 0 < / (2 * inv_sqrt_pi)) by (apply Rinv_0_lt_compat; lra).
  rewrite G in H.
  apply (Rmult_le_reg_l (/ (2 * inv_sqrt_pi))); [exact P | ].
  nra.
Qed.

(** The relative form used by the kernel: an anchor's relative error [e1] at [Y]
    and a residual bound [M] give [e1 + M sqrt(pi)/2] relative at [y]. *)
Theorem cdf_ode_relative (Rf rho : R -> R) y Y M e1 :
  y <= Y -> 0 <= M -> 0 <= e1 ->
  (forall t, y <= t <= Y -> is_derive Rf t (2 * t * Rf t - 2 * inv_sqrt_pi + rho t)) ->
  (forall t, y <= t <= Y -> continuous rho t) ->
  (forall t, y <= t <= Y -> Rabs (rho t) <= M) ->
  0 <= gaussian_erfcx Y ->
  Rabs (Rf Y - gaussian_erfcx Y) <= e1 * gaussian_erfcx Y ->
  Rabs (Rf y - gaussian_erfcx y) <= (e1 + M * / (2 * inv_sqrt_pi)) * gaussian_erfcx y.
Proof.
  intros O M0 E0 D C B EY A.
  pose proof (cdf_ode_compare Rf rho y Y M O D C B) as Cmp.
  rewrite cdf_gaussian_gap in Cmp.
  pose proof (cdf_erfcx_decay y Y O) as Dec.
  assert (I : 0 < inv_sqrt_pi) by apply inv_sqrt_pi_positive.
  assert (P : 0 < / (2 * inv_sqrt_pi)) by (apply Rinv_0_lt_compat; lra).
  assert (X : 0 <= exp (y * y - Y * Y)) by (apply Rlt_le, exp_pos).
  assert (T1 : Rabs (Rf Y - gaussian_erfcx Y) * exp (y * y - Y * Y) <= e1 * gaussian_erfcx y).
  { eapply Rle_trans; [apply Rmult_le_compat_r; [exact X | exact A] | ].
    rewrite Rmult_assoc, (Rmult_comm (gaussian_erfcx Y)). apply Rmult_le_compat_l; [exact E0 | exact Dec]. }
  assert (T2 : M * (/ (2 * inv_sqrt_pi) * (gaussian_erfcx y - exp (y * y - Y * Y) * gaussian_erfcx Y))
               <= M * / (2 * inv_sqrt_pi) * gaussian_erfcx y).
  { rewrite Rmult_assoc. apply Rmult_le_compat_l; [exact M0 | ].
    apply Rmult_le_compat_l; [lra | ].
    assert (0 <= exp (y * y - Y * Y) * gaussian_erfcx Y) by (apply Rmult_le_pos; [exact X | exact EY]).
    lra. }
  lra.
Qed.
