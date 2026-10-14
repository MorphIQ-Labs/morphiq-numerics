(** The middle-tail polynomial's analytic contract and accepted IEEE result. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64.
Require Import StageGappa ErfcxTailIntegral ErfcxMiddlePolynomial.
Require Import ErfcxMiddleApprox ErfcxMiddleRemainder ErfcxMiddleFast ErfcxScaledAnalytic.
Open Scope R_scope.

Lemma middle_integral_contract t : /2^18<=t<=/2^8 ->
  998/1000<=tail_integral t<=1 /\
  - /2^74<=correction_exact t-tail_integral t<=/2^74.
Proof.
  intros T.
  assert (T0 : 0<=t<=/2^8) by (assert (0</2^18) by (simpl; lra); lra).
  pose proof (tail_integral_correction t (proj1 T0)) as Range.
  pose proof (middle_asymptotic_remainder t T0) as Remainder.
  pose proof (Rabs_le_inv _ _ (middle_polynomial_approx t T)) as Approx.
  split; [simpl in T0; lra | ].
  assert (Budget : 3/2^76+/2^140<=/2^74) by (simpl; lra).
  lra.
Qed.

Theorem middle_fast_analytic_ieee x v : finite x -> 16<=B x<=512 ->
  middle_fast64 x=Some v -> finite v /\ B v=rndF (positive_erfcx (B x)).
Proof.
  intros Fx X Decision.
  assert (Y : /512<=1/B x<=/16).
  { unfold Rdiv. rewrite Rmult_1_l. split; apply Rinv_le_contravar; lra. }
  assert (T : /2^18<=(1/B x)*(1/B x)<=/2^8) by (simpl; nra).
  destruct (middle_integral_contract _ T) as [Range Approx].
  destruct (middle_fast_ieee x (tail_integral ((1/B x)*(1/B x))) v
    Fx X Range Approx Decision) as [Fv Value].
  split; [exact Fv | ]. unfold positive_erfcx.
  replace (1/B x) with (/B x) in Value by (unfold Rdiv; ring). exact Value.
Qed.
