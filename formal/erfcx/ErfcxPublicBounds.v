(** Every ordinary public branch, including its accurate fallback. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Binary64 Require Import Binary64Add IEEE64.
From Q Require Q256.
Require Import StageGappa ErfcxGaussianTarget ErfcxScaledAnalytic ErfcxRounding
  ErfcxPublicModel ErfcxTableFast ErfcxTableAnalyticEntry ErfcxMiddleFast ErfcxMiddleAnalytic
  ErfcxTailFast ErfcxCubicAnalytic ErfcxScaledFast ErfcxReflectionFast ErfcxReflectionAnalyticFast
  ErfcxReflectionSquare ErfcxAccurateReflectionEntry ErfcxAccurateReflectionRounded
  ErfcxAccurateTaylorEntry ErfcxAccurateTaylorRounded ErfcxAccurateProduct ErfcxAccurateRounded.
Open Scope R_scope.
Definition erfcx_bounded f dmax amax y := finite y /\ exists d a,
  Rabs d<=dmax /\ Rabs a<=amax /\ B y=f*(1+d)+a.
Lemma erfcx_exact_bounded f dmax amax y : finite y -> B y=rndF f ->
  bpow radix2 (-53)<=dmax -> bpow radix2 (-1075)<=amax -> erfcx_bounded f dmax amax y.
Proof.
  intros Fy Value Dmax Amax. destruct(rounding_decomposition f) as [d [a [D [A Round]]]].
  split;[exact Fy|]. exists d,a. split;[apply Rabs_le;split;lra|].
  split;[apply Rabs_le;split;lra|rewrite Value;exact Round].
Qed.
Theorem erfcx_regular_table x : finite x -> -/2<=B x<16 ->
  erfcx_bounded (gaussian_erfcx(B x)) (bpow radix2 (-53))
    (bpow radix2 (-123)+bpow radix2 (-1075)) (erfcx_regular64 x).
Proof.
  intros Fx X. destruct erfcx_negative_half_ok as [Fn N].
  destruct reflection_sixteen_ok as [F16 V16].
  assert (Neg : erfcx_lt x erfcx_negative_half=false)
    by (apply erfcx_lt_false;[exact Fx|exact Fn|rewrite N;lra]).
  assert (Table : erfcx_lt x reflection_sixteen=true)
    by (apply erfcx_lt_true;[exact Fx|exact F16|rewrite V16;lra]).
  unfold erfcx_regular64;rewrite Neg,Table;unfold erfcx_fallback.
  destruct(table_fast64 x) as [y|] eqn:Fast.
  - destruct(table_fast_analytic_ieee x y Fx X Fast) as [Fy Value].
    apply erfcx_exact_bounded;[exact Fy|exact Value|lra|pose proof(bpow_ge_0 radix2 (-123));lra].
  - apply q_taylor_rounded;assumption.
Qed.
Theorem erfcx_regular_negative x : finite x -> B reflection_limit<B x< -/2 ->
  erfcx_bounded (gaussian_erfcx(B x)) (bpow radix2 (-53)+bpow radix2 (-122))
    (bpow radix2 (-1075)) (erfcx_regular64 x).
Proof.
  intros Fx X. destruct erfcx_negative_half_ok as [Fn N].
  assert (Neg : erfcx_lt x erfcx_negative_half=true)
    by (apply erfcx_lt_true;[exact Fx|exact Fn|rewrite N;lra]).
  unfold erfcx_regular64;rewrite Neg;unfold erfcx_fallback.
  destruct(reflection_fast64 x) as [y|] eqn:Fast.
  - destruct(reflection_fast_analytic_ieee x y Fx X Fast) as [Fy Value].
    apply erfcx_exact_bounded;[exact Fy|exact Value|pose proof(bpow_ge_0 radix2 (-122));lra|lra].
  - apply q_negative_rounded;assumption.
Qed.
Lemma erfcx_scaled_limit_upper : B erfcx_scaled_limit<=bpow radix2 897.
Proof. destruct erfcx_scaled_limit_ok as [_ [Value _]];rewrite Value;bpow_num;lra. Qed.
Theorem erfcx_regular_tail x : finite x -> 16<=B x ->
  erfcx_bounded (positive_erfcx(B x)) (bpow radix2 (-53)+bpow radix2 (-223))
    (bpow radix2 (-1075)) (erfcx_regular64 x).
Proof.
  intros Fx X. destruct erfcx_negative_half_ok as [Fn N].
  destruct reflection_sixteen_ok as [F16 V16].
  destruct erfcx_five_twelve_ok as [F512 V512].
  destruct erfcx_scaled_limit_ok as [Flimit [Limit _]].
  assert (Neg : erfcx_lt x erfcx_negative_half=false)
    by (apply erfcx_lt_false;[exact Fx|exact Fn|rewrite N;lra]).
  assert (Table : erfcx_lt x reflection_sixteen=false)
    by (apply erfcx_lt_false;[exact Fx|exact F16|rewrite V16;lra]).
  assert (Fallback : erfcx_bounded (positive_erfcx(B x))
    (bpow radix2 (-53)+bpow radix2 (-223)) (bpow radix2 (-1075)) (Q256.to_f64(q_asym x)))
    by (apply q_asym_rounded;assumption).
  assert (Exact : forall y,finite y -> B y=rndF(positive_erfcx(B x)) ->
    erfcx_bounded (positive_erfcx(B x)) (bpow radix2 (-53)+bpow radix2 (-223)) (bpow radix2 (-1075)) y).
  { intros y Fy Value;apply erfcx_exact_bounded;[exact Fy|exact Value|pose proof(bpow_ge_0 radix2 (-223));lra|lra]. }
  unfold erfcx_regular64;rewrite Neg,Table.
  destruct(erfcx_lt x erfcx_five_twelve) eqn:Middle.
  - apply erfcx_lt_true in Middle;try assumption. rewrite V512 in Middle.
    unfold erfcx_fallback;destruct(middle_fast64 x) as [y|] eqn:Fast;[|exact Fallback].
    destruct(middle_fast_analytic_ieee x y Fx ltac:(lra) Fast) as [Fy Value];apply Exact;assumption.
  - apply erfcx_lt_false in Middle;try assumption. rewrite V512 in Middle.
    destruct(erfcx_lt erfcx_scaled_limit x) eqn:Scaled.
    + apply erfcx_lt_true in Scaled;try assumption.
      unfold erfcx_fallback;destruct(tail_scaled_fast64 x) as [y|] eqn:Fast;[|exact Fallback].
      destruct(tail_scaled_fast_analytic_ieee x y Fx Scaled Fast) as [Fy Value];apply Exact;assumption.
    + apply erfcx_lt_false in Scaled;try assumption.
      unfold erfcx_fallback;destruct(tail_unscaled_fast64 x) as [y|] eqn:Fast;[|exact Fallback].
      pose proof erfcx_scaled_limit_upper as Upper.
      destruct(tail_unscaled_fast_analytic_ieee x y Fx ltac:(split;lra) Fast) as [Fy Value];apply Exact;assumption.
Qed.
