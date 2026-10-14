(** Range hypotheses for all stored centers, discharged by exact integers. *)
From Coq Require Import Reals ZArith Lia Lra List Bool.
From Flocq Require Import Core.
From Q Require Import QSpec Q256 Q256Real.
From Q Require Limbs.
Require Import StageGappa ErfcxAccurateData ErfcxAccurateConstants
  ErfcxAccurateCenterModel ErfcxAccurateCenters ErfcxGaussianTarget.
Import ListNotations.
Open Scope R_scope.
Definition center_range_check i :=
  let c:=nth i f_at_c_data ([],0%Z) in
  (-260<=?snd c)%Z && (snd c<=? -255)%Z &&
  (2^255<=?Limbs.v(fst c))%Z && (Limbs.v(fst c)<=?2^256)%Z &&
  (0<?center_denominator i)%Z &&
  (Z.abs(center_numerator i)<=?16*center_denominator i)%Z.
Lemma center_ranges_checked : forallb center_range_check (seq 0 177)=true.
Proof. vm_compute; reflexivity. Qed.

Theorem accurate_center_bounds i : (i<177)%nat ->
  Rabs(accurate_center i)<=16 /\ /64<=gaussian_erfcx(accurate_center i)<=3.
Proof.
  intros I. pose proof center_ranges_checked as Checked.
  apply forallb_forall with (x:=i) in Checked; [|apply in_seq; lia].
  unfold center_range_check in Checked. repeat rewrite andb_true_iff in Checked.
  repeat rewrite Z.leb_le in Checked. rewrite Z.ltb_lt in Checked.
  destruct Checked as [[[[[Elo Ehi] Mlo] Mhi] Den] Center].
  destruct (q_center_ok i I) as [Valid Error].
  destruct (constant_q_ok _ (f_at_c_data_checked i I)) as [_ Value].
  set (m:=Limbs.v(fst(nth i f_at_c_data ([],0%Z)))) in *.
  set (e:=snd(nth i f_at_c_data ([],0%Z))) in *.
  assert (Ml : bpow radix2 255<=IZR m) by (rewrite <- IZR_pow2 by lia; apply IZR_le; exact Mlo).
  assert (Mh : IZR m<=bpow radix2 256) by (rewrite <- IZR_pow2 by lia; apply IZR_le; exact Mhi).
  assert (El : bpow radix2 (-260)<=bpow radix2 e) by (apply bpow_le; exact Elo).
  assert (Eh : bpow radix2 e<=bpow radix2 (-255)) by (apply bpow_le; exact Ehi).
  assert (Low : bpow radix2 (-5)<=qval(q_center i)).
  { unfold q_center; rewrite Value. fold m e.
    replace (-5)%Z with (255+ -260)%Z by reflexivity. rewrite bpow_plus.
    apply Rmult_le_compat; [apply bpow_ge_0|apply bpow_ge_0|exact Ml|exact El]. }
  assert (High : qval(q_center i)<=bpow radix2 1).
  { unfold q_center; rewrite Value. fold m e.
    replace 1%Z with (256+ -255)%Z by reflexivity. rewrite bpow_plus.
    apply Rmult_le_compat; [pose proof(bpow_gt_0 radix2 255); lra|apply bpow_ge_0|exact Mh|exact Eh]. }
  split.
  - unfold accurate_center. unfold Rdiv. rewrite Rabs_mult,Rabs_Rinv,<- abs_IZR by (apply not_0_IZR; lia).
    assert (D : 0<IZR(center_denominator i)) by (apply IZR_lt; exact Den).
    rewrite (Rabs_pos_eq(IZR(center_denominator i))) by lra.
    apply (Rmult_le_reg_r (IZR(center_denominator i))); [exact D|].
    replace (IZR(Z.abs(center_numerator i))*/IZR(center_denominator i)*IZR(center_denominator i)) with
      (IZR(Z.abs(center_numerator i))) by (field; lra).
    replace (16*IZR(center_denominator i)) with (IZR(16*center_denominator i)) by (rewrite mult_IZR; reflexivity).
    apply IZR_le; exact Center.
  - apply Rabs_le_inv in Error. bpow_num_all. lra.
Qed.
