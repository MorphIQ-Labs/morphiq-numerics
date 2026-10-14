(** Taylor's local target, with the positive-tail value as a boundary at 16. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Coquelicot Require Import Coquelicot.
Require Import ErfcxConstants ErfcxScaledAnalytic.
Open Scope R_scope.

Definition gaussian u := exp (-u*u).
Definition boundary_erfcx anchor x :=
  exp (x*x-256)*anchor+2*inv_sqrt_pi*exp (x*x)*RInt gaussian x 16.
Definition table_erfcx := boundary_erfcx (positive_erfcx 16).

Lemma gaussian_continuous u : continuous gaussian u.
Proof.
  apply (@ex_derive_continuous R_AbsRing R_CompleteNormedModule).
  unfold gaussian. eexists. auto_derive; trivial.
Qed.
Lemma gaussian_integrable a b : ex_RInt gaussian a b.
Proof. apply (@ex_RInt_continuous R_CompleteNormedModule). intros; apply gaussian_continuous. Qed.

Lemma gaussian_integral_derivative x :
  is_derive (fun z => RInt gaussian z 16) x (-gaussian x).
Proof.
  apply (@is_derive_RInt' R_CompleteNormedModule gaussian (fun z => RInt gaussian z 16) x 16).
  - apply filter_forall. intros z. apply RInt_correct,gaussian_integrable.
  - apply gaussian_continuous.
Qed.

Theorem boundary_erfcx_derivative anchor x :
  is_derive (boundary_erfcx anchor) x (2*x*boundary_erfcx anchor x-2*inv_sqrt_pi).
Proof.
  unfold boundary_erfcx. auto_derive.
  - split; [apply gaussian_integrable | ]. split; [ | exact I].
    apply filter_forall. intros z. unfold gaussian.
    apply (continuity_pt_comp (fun u => -u*u) exp z).
    + apply continuity_pt_mult; [apply continuity_pt_opp | ]; apply continuity_pt_id.
    + apply derivable_continuous_pt,derivable_pt_exp.
  - unfold gaussian. replace (-x*x) with (-(x*x)) by ring.
    assert (Cancel : exp (x*x)*exp (-(x*x))=1)
      by (rewrite <- exp_plus; replace (x*x+-(x*x)) with 0 by ring; apply exp_0).
    replace (2*inv_sqrt_pi*exp (x*x)*-(1*exp (-(x*x)))) with
      (-2*inv_sqrt_pi*(exp (x*x)*exp (-(x*x)))) by ring.
    rewrite Cancel.
    replace (exp (x*x+-(256))) with (exp (x*x-256)) by (f_equal; ring).
    fold gaussian. ring.
Qed.

Lemma boundary_erfcx_at_16 anchor : boundary_erfcx anchor 16=anchor.
Proof.
  unfold boundary_erfcx. rewrite RInt_point.
  replace (16*16-256) with 0 by ring. rewrite exp_0. change (1*anchor+2*inv_sqrt_pi*exp(16*16)*0=anchor). ring.
Qed.
