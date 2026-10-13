(** The Gaussian approximation bound at the actual binary64 table entry. *)
From Coq Require Import Reals ZArith Lia Lra.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64.
Require Import StageGappa ErfcxGaussianTarget ErfcxTableReduction ErfcxTableEntry
  ErfcxTableCertificateModel ErfcxTableBound ErfcxTableFast
  ErfcxAccurateCenterModel ErfcxAccurateTaylorReduction ErfcxTableReflectionIndex ErfcxTableAnalytic.
Open Scope R_scope.
Theorem table_approximation_ieee x : finite x -> -/2<=B x<16 ->
  0<gaussian_erfcx(B x) /\
  Rabs((table_exact x-gaussian_erfcx(B x))/gaussian_erfcx(B x))<=bpow radix2 (-69).
Proof.
  intros Fx X.
  pose proof(table_reduce_ieee x Fx X) as Reduction.
  pose proof(accurate_table_reduce_ieee x Fx X) as Center.
  pose proof(table_reduce_exponent x Fx X) as Exponent.
  unfold table_exact. destruct(table_reduce64 x) as [[[i c]h]e].
  destruct Reduction as [I [E [Fc [Fh [Exact Hr]]]]].
  destruct Center as [_ [_ [_ [Cv [Exact' _]]]]].
  pose proof(table_analytic_certificate (Z.to_nat i)(B h) ltac:(lia)
    ltac:(rewrite <- Exponent,<- erfcx_table_radius;exact Hr)) as Bound.
  replace (accurate_center(Z.to_nat i)+B h) with (B x) in Bound by (rewrite <- Cv;lra).
  exact Bound.
Qed.
Theorem table_fast_analytic_ieee x v : finite x -> -/2<=B x<16 ->
  table_fast64 x=Some v -> finite v /\ B v=rndF(gaussian_erfcx(B x)).
Proof.
  intros Fx X Decision. destruct(table_approximation_ieee x Fx X) as [F Approx].
  exact(table_fast_ieee x (gaussian_erfcx(B x)) v Fx X F Approx Decision).
Qed.
