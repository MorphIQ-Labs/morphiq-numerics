(** Exact-word checks for the accurate path's generated Q256 constants. *)
From Coq Require Import Reals ZArith Lia Lra List Bool.
From Flocq Require Import Core.
From Q Require Import QSpec Q256 Q256Real.
From Q Require Limbs.
Require Import ErfcxAccurateData.
Import ListNotations.
Open Scope R_scope.

Lemma constant_q_ok c : constant_check c=true -> valid (constant_q c) /\
  qval (constant_q c)=IZR (Limbs.v (fst c))*bpow radix2 (snd c).
Proof.
  intros C. apply constant_check_ok in C. split; [apply new_valid; exact C | ].
  unfold constant_q. rewrite new_val by exact C. reflexivity.
Qed.

Definition q_reciprocal i := constant_q (nth i recip_data ([],0%Z)).
Definition reciprocal_check i c :=
  (snd c<=? -255)%Z && (-262<=?snd c)%Z &&
  (Z.abs (Z.of_nat (S i)*Limbs.v (fst c)-2^(-snd c)) <=? 2^(-snd c-255))%Z.

Lemma reciprocal_checks : forallb (fun i => reciprocal_check i (nth i recip_data ([],0%Z))) (seq 0 100)=true.
Proof. vm_compute; reflexivity. Qed.

Lemma reciprocal_checked i : (i<100)%nat ->
  (-262<=snd (nth i recip_data ([],0%Z))<= -255)%Z /\
  (Z.abs (Z.of_nat (S i)*Limbs.v (fst (nth i recip_data ([],0%Z)))-2^(-snd (nth i recip_data ([],0%Z))))
    <=2^(-snd (nth i recip_data ([],0%Z))-255))%Z.
Proof.
  intros I. pose proof reciprocal_checks as C.
  apply forallb_forall with (x:=i) in C; [ | apply in_seq; lia].
  unfold reciprocal_check in C. repeat rewrite andb_true_iff in C.
  repeat rewrite Z.leb_le in C. tauto.
Qed.

Theorem q_reciprocal_ok i : (i<100)%nat -> valid (q_reciprocal i) /\
  Rabs (qval (q_reciprocal i)*INR (S i)-1)<=bpow radix2 (-255).
Proof.
  intros I. destruct (constant_q_ok _ (recip_data_checked i I)) as [Q Value].
  destruct (reciprocal_checked i I) as [Exponent Error].
  set (c := nth i recip_data ([],0%Z)) in *.
  split; [exact Q | ]. unfold q_reciprocal. fold c. rewrite Value,INR_IZR_INZ.
  assert (Id : (IZR (Limbs.v (fst c))*bpow radix2 (snd c)*IZR (Z.of_nat (S i))-1)=
    IZR (Z.of_nat (S i)*Limbs.v (fst c)-2^(-snd c))*bpow radix2 (snd c)).
  { rewrite minus_IZR,mult_IZR,IZR_pow2 by lia.
    rewrite Rmult_minus_distr_r, <- bpow_plus.
    replace (-snd c+snd c)%Z with 0%Z by ring. change (bpow radix2 0) with 1. ring. }
  rewrite Id,Rabs_mult,Rabs_Zabs,(Rabs_pos_eq (bpow radix2 (snd c))) by apply bpow_ge_0.
  eapply Rle_trans with (IZR (2^(-snd c-255))*bpow radix2 (snd c)).
  - apply Rmult_le_compat_r; [apply bpow_ge_0 | apply IZR_le; exact Error].
  - rewrite IZR_pow2 by lia. rewrite <- bpow_plus.
    replace (-snd c-255+snd c)%Z with (-255)%Z by ring. apply Rle_refl.
Qed.
