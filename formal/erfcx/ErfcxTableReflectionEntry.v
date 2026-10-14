(** Discharge the positive table hypotheses in reflected subtraction. *)
From Coq Require Import Reals ZArith Lia Lra.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add.
Require Import StageGappa ErfcxGaussianTarget ErfcxTableReduction ErfcxTableEntry
  ErfcxTableCertificateModel ErfcxTableBound ErfcxTableAnalyticEntry
  ErfcxTableReflectionIndex ErfcxTableReflectionRanges ErfcxTableReflectionBudget
  ErfcxReflectionValue.
Open Scope R_scope.
Theorem reflection_table_polynomial_range x : finite x -> /2<B x<9 ->
  0.034<=table_exact x<=0.616.
Proof.
  intros Fx X. pose proof(table_reduce_ieee x Fx ltac:(lra)) as Reduction.
  pose proof(reflection_table_index x Fx X) as Index.
  pose proof(table_reduce_exponent x Fx ltac:(lra)) as Exponent.
  unfold table_exact. destruct(table_reduce64 x) as [[[i c]h]e].
  destruct Reduction as [I [E [Fc [Fh [Exact Hr]]]]].
  destruct Index as [Index Positive].
  apply reflection_polynomial_certificate;[lia| |].
  - rewrite <- Exponent,<- erfcx_table_radius;exact Hr.
  - intros N;apply Positive;lia.
Qed.
Theorem reflection_table_value_bounds x : finite x -> /2<B x<9 ->
  let '(h,l):=table_eval64 x in
  0<=gaussian_erfcx(B x)<=1 /\ /32<=B h<=0.617 /\
  Rabs(B l)<=bpow radix2 (-53) /\
  Rabs(B h+B l-gaussian_erfcx(B x))<=bpow radix2 (-67).
Proof.
  intros Fx X.
  pose proof(reflection_table_polynomial_range x Fx X) as Polynomial.
  destruct(table_approximation_ieee x Fx ltac:(lra)) as [F Approx].
  pose proof(table_evaluation_error x Fx ltac:(lra)) as Eval.
  pose proof(table_eval_normalized_ieee x Fx ltac:(lra)) as Normal.
  destruct(table_eval64 x) as [h l].
  destruct Eval as [_ [_ Error]]. destruct Normal as [_ [_ [_ [Norm _]]]].
  exact(table_reflection_budget (table_exact x)(gaussian_erfcx(B x))
    (B h+B l)(B h)(B l) Polynomial F Approx Error eq_refl Norm).
Qed.
Theorem gaussian_reflection_table_contract x : finite x ->
  reflection_table_contract x (gaussian_erfcx(-B x)).
Proof.
  intros Fx X.
  assert (Fn : finite(fneg x)) by (unfold fneg,b64_opp;rewrite is_finite_Bopp;exact Fx).
  assert (Bn : B(fneg x)= -B x) by apply B2R_Bopp.
  pose proof(reflection_table_value_bounds (fneg x) Fn ltac:(rewrite Bn;exact X)) as Bounds.
  rewrite Bn in Bounds. destruct(table_eval64(fneg x)) as [h l];tauto.
Qed.
