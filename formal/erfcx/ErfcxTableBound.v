(** The table certificates applied to the actual IEEE entry point. *)
From Coq Require Import Reals ZArith Lia Lra.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64.
Require Import StageGappa ErfcxReciprocal ErfcxTableReduction ErfcxTableEntry ErfcxTableCertificateModel ErfcxTableCertificates.
Open Scope R_scope.

Lemma table_reduce_exponent x : finite x -> -/2<=B x<16 ->
 let '(i,c,h,e) := table_reduce64 x in e=table_exponent (Z.to_nat i).
Proof.
 intros Fx X. destruct one_ok as [Fo Bo].
 unfold table_reduce64. rewrite (Bcompare_correct 53 1024 x one Fx Fo),Bo.
 destruct (Rcompare_spec (B x) 1) as [L|Eq|G].
 - pose proof (table_uniform_ieee x Fx ltac:(lra)) as T.
   destruct (table_uniform64 x) as [[i c] h]. destruct T as [I _].
   unfold table_exponent. destruct (Nat.ltb_spec (Z.to_nat i) 49);[reflexivity|lia].
 - pose proof (table_binade_ieee x Fx ltac:(lra)) as T.
   destruct (table_binade64 x) as [[[i c] h] e]. destruct T as [E [I _]].
   unfold table_exponent. destruct (Nat.ltb_spec (Z.to_nat i) 49);[lia|].
   rewrite Z2Nat.id by lia. apply Z.div_unique with (i-49-32*e)%Z;lia.
 - pose proof (table_binade_ieee x Fx ltac:(lra)) as T.
   destruct (table_binade64 x) as [[[i c] h] e]. destruct T as [E [I _]].
   unfold table_exponent. destruct (Nat.ltb_spec (Z.to_nat i) 49);[lia|].
   rewrite Z2Nat.id by lia. apply Z.div_unique with (i-49-32*e)%Z;lia.
Qed.

Definition table_exact x :=
 let '(i,c,h,e) := table_reduce64 x in table_polynomial_exact (Z.to_nat i) (B h).
Theorem table_evaluation_error x : finite x -> -/2<=B x<16 ->
 let '(yh,yl) := table_eval64 x in
 finite yh /\ finite yl /\
 Rabs ((B yh+B yl-table_exact x)/table_exact x)<=/2^67.
Proof.
 intros Fx X. pose proof (table_reduce_ieee x Fx X) as Reduce.
 pose proof (table_reduce_exponent x Fx X) as Exponent.
 pose proof (table_eval_ieee x Fx X) as Value.
 unfold table_eval64,table_value,table_exact in *.
 destruct (table_reduce64 x) as [[[i c] h] e].
 destruct Reduce as [I [E [Fc [Fh [Exact H]]]]].
 pose proof (table_certificate (Z.to_nat i) (B h) ltac:(lia) (B_fmt h)
   ltac:(rewrite <-Exponent;exact H)) as Bound.
 rewrite <-Exponent in Bound.
 destruct (ErfcxTableEntry.table_polynomial64 (Z.to_nat i) h e) as [yh yl].
 destruct Value as [Fyh [Fyl V]]. split;[exact Fyh|]. split;[exact Fyl|].
 rewrite V. apply Rabs_le;exact Bound.
Qed.
