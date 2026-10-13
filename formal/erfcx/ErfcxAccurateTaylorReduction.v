(** The accurate table lookup uses the same exact reduction as the fast path. *)
From Coq Require Import Reals ZArith Lia Lra.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import IEEE64.
From Q Require Import QSpec.
Require Import StageGappa ErfcxReciprocal ErfcxTableReduction ErfcxAccurateCenterModel.
Open Scope R_scope.
Lemma accurate_uniform_center i : (0<=i<=48)%Z ->
  accurate_center(Z.to_nat i)=IZR(i-16)/32.
Proof.
  intros I. unfold accurate_center,center_numerator,center_denominator.
  assert (Index : Nat.ltb (Z.to_nat i) 49=true) by (apply Nat.ltb_lt;lia).
  rewrite Index,Z2Nat.id by lia. reflexivity.
Qed.
Lemma accurate_binade_center i e : (0<=e<=3)%Z -> (49+32*e<=i<81+32*e)%Z ->
  accurate_center(Z.to_nat i)=(1+(IZR(i-49-32*e)+/2)/32)*bpow radix2 e.
Proof.
  intros E I. unfold accurate_center,center_numerator,center_denominator.
  assert (Index : Nat.ltb (Z.to_nat i) 49=false) by (apply Nat.ltb_ge;lia).
  rewrite Index,Z2Nat.id by lia.
  assert (Div : ((i-49)/32=e)%Z).
  { symmetry; apply Z.div_unique with (r:=(i-49-32*e)%Z);[left;lia|ring]. }
  rewrite Div,Z.mod_eq by lia. rewrite Div.
  rewrite !mult_IZR,!plus_IZR,!mult_IZR,IZR_pow2 by lia. field.
Qed.

Theorem accurate_table_reduce_ieee x : finite x -> -/2<=B x<16 ->
  let '(i,c,h,e):=table_reduce64 x in
  (0<=i<177)%Z /\ finite c /\ finite h /\ B c=accurate_center(Z.to_nat i) /\
    B c+B h=B x /\ Rabs(B h)<=/8.
Proof.
  intros Fx X. destruct ErfcxReciprocal.one_ok as [Fo Bo].
  unfold table_reduce64. rewrite (Bcompare_correct 53 1024 x ErfcxReciprocal.one Fx Fo),Bo.
  destruct(Rcompare_spec (B x) 1) as [Low|Eq|High].
  - pose proof(table_uniform_ieee x Fx ltac:(lra)) as Reduce.
    destruct(table_uniform64 x) as [[i c]h]. cbv zeta in Reduce.
    destruct Reduce as [I [Fc [Fh [Cv [Exact [Hr Rest]]]]]].
    split;[lia|]. split;[exact Fc|]. split;[exact Fh|]. split.
    + rewrite accurate_uniform_center by exact I. exact Cv.
    + split;[exact Exact|lra].
  - pose proof(table_binade_ieee x Fx ltac:(lra)) as Reduce.
    destruct(table_binade64 x) as [[[i c]h]e]. cbv zeta in Reduce.
    destruct Reduce as [E [I [Fc [Fh [Exact [Cv Hr]]]]]].
    split;[lia|]. split;[exact Fc|]. split;[exact Fh|]. split.
    + rewrite accurate_binade_center with (e:=e) by assumption. exact Cv.
    + split;[exact Exact|]. eapply Rle_trans;[exact Hr|]. change (/8) with (bpow radix2 (-3)). apply bpow_le;lia.
  - pose proof(table_binade_ieee x Fx ltac:(lra)) as Reduce.
    destruct(table_binade64 x) as [[[i c]h]e]. cbv zeta in Reduce.
    destruct Reduce as [E [I [Fc [Fh [Exact [Cv Hr]]]]]].
    split;[lia|]. split;[exact Fc|]. split;[exact Fh|]. split.
    + rewrite accurate_binade_center with (e:=e) by assumption. exact Cv.
    + split;[exact Exact|]. eapply Rle_trans;[exact Hr|]. change (/8) with (bpow radix2 (-3)). apply bpow_le;lia.
Qed.
