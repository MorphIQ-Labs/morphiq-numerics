(** Binary64 entry of the accurate Taylor path, including center shortcuts. *)
From Coq Require Import Reals ZArith Lia Lra.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import IEEE64.
From Q Require Import Q256 Q256Real.
Require Import StageGappa ExpFast ErfcxGaussianTarget ErfcxTaylorLocal ErfcxTableReduction
  ErfcxAccurateInputs ErfcxAccurateCenterModel ErfcxAccurateCenters ErfcxAccurateCenterBounds
  ErfcxAccurateTaylorLoop ErfcxAccurateTaylor ErfcxAccurateTaylorReduction.
Open Scope R_scope.
Definition q_taylor x :=
  let '(i,c,h,e):=table_reduce64 x in
  match Bcompare 53 1024 h ExpFast.c_zero with
  | Some Eq => q_center(Z.to_nat i)
  | _ => q_taylor_series (q_float c) (Z.to_nat i) (q_float h)
  end.
Theorem q_taylor_error x : finite x -> -/2<=B x<16 ->
  valid(q_taylor x) /\ Rabs(qval(q_taylor x)-gaussian_erfcx(B x))<=bpow radix2 (-124).
Proof.
  intros Fx X. pose proof(accurate_table_reduce_ieee x Fx X) as Reduction.
  unfold q_taylor. destruct(table_reduce64 x) as [[[i c]h]e]. cbv zeta in Reduction.
  destruct Reduction as [I [Fc [Fh [Cv [Exact Hr]]]]].
  assert (Index : (Z.to_nat i<177)%nat) by lia.
  destruct(q_float_ok c Fc) as [C Cvalue]. destruct(q_float_ok h Fh) as [H Hvalue].
  destruct(q_taylor_series_error (q_float c) (Z.to_nat i) (q_float h) C H Index
    ltac:(rewrite Cvalue;exact Cv) ltac:(rewrite Hvalue;exact Hr)) as [Series Error].
  rewrite Hvalue in Error. replace (accurate_center(Z.to_nat i)+B h) with (B x) in Error by (rewrite <- Cv;lra).
  rewrite (Bcompare_correct 53 1024 h ExpFast.c_zero Fh ExpFast.c_zero_finite),ExpFast.c_zero_val.
  destruct(Rcompare_spec (B h) 0) as [Neg|Zero|Pos];try (split;assumption).
  destruct(q_center_ok (Z.to_nat i) Index) as [Center CenterError]. split;[exact Center|].
  replace (B x) with (accurate_center(Z.to_nat i)) by (rewrite <- Cv; lra).
  eapply Rle_trans;[exact CenterError|apply bpow_le;lia].
Qed.
Theorem table_target_bound x : finite x -> -/2<=B x<16 -> Rabs(gaussian_erfcx(B x))<=512.
Proof.
  intros Fx X. pose proof(accurate_table_reduce_ieee x Fx X) as Reduction.
  destruct(table_reduce64 x) as [[[i c]h]e]. cbv zeta in Reduction.
  destruct Reduction as [I [Fc [Fh [Cv [Exact Hr]]]]].
  destruct(accurate_center_bounds (Z.to_nat i) ltac:(lia)) as [Cr Fr].
  replace (B x) with (accurate_center(Z.to_nat i)+B h) by (rewrite <- Cv;lra).
  apply gaussian_local_bound;[exact Cr|exact Hr|apply Rabs_le;lra].
Qed.
