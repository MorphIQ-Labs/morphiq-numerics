(** The reflected table lookup only uses centers at or above one half. *)
From Coq Require Import Reals ZArith Lia Lra.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import IEEE64.
Require Import StageGappa ErfcxTableReduction ErfcxTableBound ErfcxTableCertificateModel
  ErfcxAccurateCenterModel ErfcxAccurateTaylorReduction.
Open Scope R_scope.
Lemma erfcx_table_radius e : bpow radix2 (e-6)=bpow radix2 e/64.
Proof. replace (e-6)%Z with (e+ -6)%Z by lia;rewrite bpow_plus;bpow_num;field. Qed.
Theorem reflection_table_index x : finite x -> /2<B x<9 ->
  let '(i,c,h,e):=table_reduce64 x in
  (32<=i<177)%Z /\ (i=32%Z -> 0<=B h).
Proof.
  intros Fx X.
  pose proof(table_reduce_ieee x Fx ltac:(lra)) as Reduction.
  pose proof(accurate_table_reduce_ieee x Fx ltac:(lra)) as Center.
  pose proof(table_reduce_exponent x Fx ltac:(lra)) as Exponent.
  destruct(table_reduce64 x) as [[[i c]h]e].
  destruct Reduction as [I [E [Fc [Fh [Exact Hr]]]]].
  destruct Center as [_ [_ [_ [Cv _]]]].
  split.
  - split;[|lia]. destruct(Z_lt_ge_dec i 32) as [Small|Large];[|lia].
    assert (Uniform : B c=IZR(i-16)/32).
    { rewrite Cv,accurate_uniform_center by lia;reflexivity. }
    assert (Exponent0 : e=0%Z).
    { rewrite Exponent. unfold table_exponent.
      destruct(Nat.ltb_spec (Z.to_nat i)49);[reflexivity|lia]. }
    rewrite Exponent0 in Hr. change (Rabs(B h)<=bpow radix2 (-6)) in Hr. bpow_num_all.
    apply Rabs_le_inv in Hr.
    assert (Cbound : IZR(i-16)<=15) by (apply IZR_le;lia).
    exfalso. rewrite Uniform in Exact. lra.
  - intros Index. rewrite Index in Cv.
    change (Z.to_nat 32) with 32%nat in Cv.
    assert (C : accurate_center 32=/2).
    { unfold accurate_center,center_numerator,center_denominator;vm_compute;field. }
    rewrite C in Cv;lra.
Qed.
