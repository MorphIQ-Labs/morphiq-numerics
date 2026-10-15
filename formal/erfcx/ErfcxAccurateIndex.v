(** Decode the integer selected by the accurate reflected exponential.
    The shifter bits recover the same bounded integer as Rust's i32 cast. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Mul.
Require Import StageGappa ErfcxAccurateReduction.
Require ExpReduction ExpStageReduction.
Open Scope R_scope.

Definition accurate_index s :=
  (bits_of_b64 (fadd (fmul s ExpReduction.c_inv_l) ExpReduction.shifter)-
   bits_of_b64 ExpReduction.shifter)%Z.

Theorem accurate_index_ok s : finite s -> -745.1333<=B s<=709.79 ->
  finite (accurate_n s) /\ B (accurate_n s)=IZR (accurate_index s) /\
  (Z.abs (accurate_index s)<=137601)%Z /\
  Rabs (B s-IZR (accurate_index s)*(ln 2/128))<=0.002708.
Proof.
  intros F S. destruct (accurate_n_ieee s F S) as [N [ni [Value [Ni Residual]]]].
  assert (Fi : finite ExpReduction.c_inv_l) by exact (proj1 ExpReduction.c_finite).
  assert (I : 0<=B ExpReduction.c_inv_l<=185).
  { rewrite ExpReduction.c_inv_l_val. unfold F2R; cbn [Fnum Fexp]. bpow_num. split; lra. }
  assert (Bound : bnd 1 18 (B s*B ExpReduction.c_inv_l)).
  { unfold bnd. change (bpow radix2 18) with 262144. apply Rabs_le; nra. }
  destruct (fmul_ok 1 18 s ExpReduction.c_inv_l F Fi ltac:(lia) ltac:(lia)
    ltac:(reflexivity) ltac:(lia) Bound) as [Y Yvalue].
  set (y := fmul s ExpReduction.c_inv_l) in *.
  assert (Yrange : Rabs (B y)<=bpow radix2 18).
  { rewrite Yvalue. pose proof (bnd_round 1 18 (B s*B ExpReduction.c_inv_l) ltac:(lia) ltac:(lia) Bound) as Rounded.
    unfold bnd in Rounded. change (IZR 1) with 1 in Rounded. rewrite Rmult_1_l in Rounded. exact Rounded. }
  assert (Ylarge : Rabs (B y)<=bpow radix2 50) by (eapply Rle_trans; [exact Yrange | apply bpow_le; lia]).
  destruct (ExpReduction.shifter_round y Y Ylarge) as [_ Round].
  assert (Equal : ni=Znearest ne (B y)).
  { apply eq_IZR. rewrite <- Value. exact Round. }
  destruct (ExpStageReduction.shifter_add y Y Ylarge) as [T Tvalue].
  rewrite <- Equal in Tvalue.
  pose proof (ExpStageReduction.shifted_bits _ ni T Tvalue ltac:(lia)) as Bits.
  assert (Index : accurate_index s=ni).
  { unfold accurate_index. fold y. rewrite Bits,ExpStageReduction.shifter_bits. ring. }
  rewrite Index. repeat split; assumption.
Qed.
