(** Integer-exact checks of all generated Q256 centered-series coefficients. *)
From Coq Require Import Reals ZArith Lia Lra List Bool.
From Flocq Require Import Core.
From Q Require Import QSpec Q256 Q256Real.
From Q Require Limbs.
Require Import NormalConstants ErfcxAccurateData ErfcxAccurateConstants ErfcxFactorial.
Import ListNotations.
Open Scope R_scope.

Definition normal_center_den n := (factorial_integer n*Z.of_nat(S(2*n)))%Z.
Definition normal_center_coefficient n := /INR(fact n)/INR(S(2*n)).
Definition normal_q_center_coefficient n := constant_q(nth n normal_center_data ([],0%Z)).
Definition normal_center_check n c :=
  (snd c<=? -255)%Z &&
  (Z.abs(Limbs.v(fst c)*normal_center_den n-2^(-snd c))<=?2^(-snd c-255))%Z.

Lemma normal_center_checks :
  forallb (fun n=>normal_center_check n (nth n normal_center_data ([],0%Z))) (seq 0 41)=true.
Proof. vm_compute;reflexivity. Qed.

Lemma normal_center_den_value n : IZR(normal_center_den n)=INR(fact n)*INR(S(2*n)).
Proof. unfold normal_center_den;rewrite mult_IZR,<-factorial_real_integer,<-INR_IZR_INZ;reflexivity. Qed.

Lemma normal_center_coefficient_range n : 0<normal_center_coefficient n<=1.
Proof.
  assert (F : 1<=INR(fact n)).
  { change 1 with(INR 1);apply le_INR;pose proof(lt_O_fact n);lia. }
  assert (N : 1<=INR(S(2*n))) by (change 1 with(INR 1);apply le_INR;lia).
  assert (A : 0</INR(fact n)<=1).
  { split;[apply Rinv_0_lt_compat;lra|rewrite <-Rinv_1;apply Rinv_le_contravar;lra]. }
  assert (B : 0</INR(S(2*n))<=1).
  { split;[apply Rinv_0_lt_compat;lra|rewrite <-Rinv_1;apply Rinv_le_contravar;lra]. }
  unfold normal_center_coefficient,Rdiv;split;nra.
Qed.

Theorem normal_q_center_coefficient_error n : (n<41)%nat ->
  valid(normal_q_center_coefficient n) /\
  Rabs(qval(normal_q_center_coefficient n)-normal_center_coefficient n)<=bpow radix2 (-255).
Proof.
  intros N.
  pose proof normal_center_data_checked as Words.
  apply forallb_forall with(x:=nth n normal_center_data ([],0%Z)) in Words.
  2: apply nth_In;exact N.
  destruct(constant_q_ok _ Words) as [Q Value].
  pose proof normal_center_checks as Check.
  apply forallb_forall with(x:=n) in Check;[|apply in_seq;lia].
  unfold normal_center_check in Check;rewrite andb_true_iff in Check.
  destruct Check as [Exponent Error];apply Z.leb_le in Exponent,Error.
  set(c:=nth n normal_center_data ([],0%Z)) in *.
  assert (Den : 1<=IZR(normal_center_den n)).
  { rewrite normal_center_den_value.
    assert (F : 1<=INR(fact n)) by (change 1 with(INR 1);apply le_INR;pose proof(lt_O_fact n);lia).
    assert (K : 1<=INR(S(2*n))) by (change 1 with(INR 1);apply le_INR;lia).
    nra. }
  assert (Cvalue : normal_center_coefficient n=/IZR(normal_center_den n)).
  { unfold normal_center_coefficient;rewrite normal_center_den_value.
    field. assert (F : 0<INR(fact n)) by (apply lt_0_INR,lt_O_fact).
    assert (K : 0<INR(S(2*n))) by (apply lt_0_INR;lia). split;lra. }
  assert (Relative : Rabs(qval(normal_q_center_coefficient n)*IZR(normal_center_den n)-1)
    <=bpow radix2 (-255)).
  { unfold normal_q_center_coefficient;fold c;rewrite Value.
    assert (Id : IZR(Limbs.v(fst c))*bpow radix2(snd c)*IZR(normal_center_den n)-1=
      IZR(Limbs.v(fst c)*normal_center_den n-2^(-snd c))*bpow radix2(snd c)).
    { rewrite minus_IZR,mult_IZR,IZR_pow2 by lia.
      rewrite Rmult_minus_distr_r,<-bpow_plus.
      replace(-snd c+snd c)%Z with 0%Z by ring;change(bpow radix2 0)with 1;ring. }
    rewrite Id,Rabs_mult,Rabs_Zabs,(Rabs_pos_eq(bpow radix2(snd c))) by apply bpow_ge_0.
    eapply Rle_trans with(IZR(2^(-snd c-255))*bpow radix2(snd c)).
    - apply Rmult_le_compat_r;[apply bpow_ge_0|apply IZR_le;exact Error].
    - rewrite IZR_pow2 by lia;rewrite <-bpow_plus.
      replace(-snd c-255+snd c)%Z with (-255)%Z by ring;apply Rle_refl. }
  split;[exact Q|]. rewrite Cvalue.
  replace(qval(normal_q_center_coefficient n)-/IZR(normal_center_den n)) with
    ((qval(normal_q_center_coefficient n)*IZR(normal_center_den n)-1)/IZR(normal_center_den n))
    by (field;lra).
  unfold Rdiv;rewrite Rabs_mult,Rabs_Rinv,(Rabs_pos_eq(IZR(normal_center_den n))) by lra.
  assert (Reciprocal : 0</IZR(normal_center_den n)<=1).
  { split;[apply Rinv_0_lt_compat;lra|rewrite <-Rinv_1;apply Rinv_le_contravar;lra]. }
  eapply Rle_trans with(bpow radix2 (-255)*1);[|lra].
  apply Rmult_le_compat;[apply Rabs_pos|lra|exact Relative|lra].
Qed.
