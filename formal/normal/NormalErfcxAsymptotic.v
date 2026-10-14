(** The shared accurate erfcx tail for an extended, rather than binary64,
    argument. Its existing loop and product bounds are preserved. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Q Require Import Q256 Q256Real.
Require Import ErfcxAccurateInputs ErfcxAccurateSetup ErfcxAccurateSquare
  ErfcxAccurateLoop ErfcxAccurateProduct ErfcxTailIntegral ErfcxScaledAnalytic
  NormalErfcxReciprocal.
Open Scope R_scope.

Definition normal_q_erfcx_tail_series x := q_asym_series (q_half_square(q_recip x)) q_odd.

Theorem normal_q_erfcx_tail_series_error x : valid x -> 16<=qval x<=3*bpow radix2 1022 ->
  valid(normal_q_erfcx_tail_series x) /\
  Rabs(qval(normal_q_erfcx_tail_series x)-tail_integral((/qval x)*(/qval x)))<=bpow radix2 (-226).
Proof.
  intros X Range.
  destruct(normal_q_reciprocal_error x X Range) as [Y Error].
  destruct(q_half_square_error _ (/qval x) Y Error) as [Qt Square].
  assert (Reciprocal : 0</qval x<=/16).
  { split;[apply Rinv_0_lt_compat|apply Rinv_le_contravar];lra. }
  assert (T : 0<=(/qval x)*(/qval x)<=/2^8).
  { split;[nra|]. eapply Rle_trans with((/16)*(/16));[apply Rmult_le_compat;lra|right;field]. }
  unfold normal_q_erfcx_tail_series;apply q_asym_series_integral;try assumption.
  exact q_odd_ok.
Qed.

Definition normal_q_erfcx_asymptotic x := mul (mul (normal_q_erfcx_tail_series x) (q_recip x)) q_cs.

Theorem normal_q_erfcx_asymptotic_error x : valid x -> 16<=qval x<=3*bpow radix2 1022 ->
  valid(normal_q_erfcx_asymptotic x) /\ exists e,Rabs e<=bpow radix2 (-224) /\
  qval(normal_q_erfcx_asymptotic x)=positive_erfcx(qval x)*(1+e).
Proof.
  intros X Range.
  destruct(normal_q_erfcx_tail_series_error x X Range) as [S Serror].
  destruct(normal_q_reciprocal_error x X Range) as [Y [ey [Ey Yvalue]]].
  destruct q_cs_ok as [C Cvalue]. destruct q_cs_error as [ec [Ec Cvalue']].
  assert (Reciprocal : 0</qval x<=/16).
  { split;[apply Rinv_0_lt_compat|apply Rinv_le_contravar];lra. }
  assert (T : 0<=(/qval x)*(/qval x)<=/2^8).
  { split;[nra|]. eapply Rle_trans with((/16)*(/16));[apply Rmult_le_compat;lra|right;field]. }
  pose proof(tail_integral_correction _ (proj1 T)) as Correction.
  assert (J : /2<=tail_integral((/qval x)*(/qval x)))by(cbn[pow]in T;lra).
  destruct(accurate_series_relative _ _ J Serror) as [es [Es Svalue]].
  destruct(mul_relative _ _ S Y) as [P [a [A Pvalue]]].
  destruct(mul_relative _ _ P C) as [Result [b [Berr ResultValue]]].
  split;[exact Result|]. exists((1+es)*(1+ey)*(1+ec)*(1+a)*(1+b)-1). split.
  - apply accurate_product_error;assumption.
  - unfold normal_q_erfcx_asymptotic;rewrite ResultValue,Pvalue,Svalue,Yvalue,Cvalue'.
    unfold positive_erfcx,Rdiv;ring.
Qed.
