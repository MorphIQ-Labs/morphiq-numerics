(** The accurate asymptotic loop's term recurrence over actual Q256 operations.
    The reciprocal-square and integer-factor contracts are explicit. *)
From Coq Require Import Reals ZArith Lia Lra Psatz List.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Q Require Import QSpec Q256 Q256Real Limbs.
Require Import StageGappa ErfcxAccurateSeries.
Import ListNotations.
Open Scope R_scope.

Definition q_one := Q false [0%Z;0%Z;0%Z;(2^63)%Z] (-255).

Lemma q_one_ok : valid q_one /\ qval q_one=1.
Proof.
  split.
  - split.
    + split; [repeat constructor; unfold Limbs.B; lia | reflexivity].
    + right. change (normalized 256 (2^255)). unfold normalized. lia.
  - unfold qval, q_one, val, F2R. cbn [neg m e Fnum Fexp].
    change (v [0%Z;0%Z;0%Z;(2^63)%Z]) with (2^255)%Z.
    rewrite IZR_pow2 by lia. rewrite <- bpow_plus. reflexivity.
Qed.



Fixpoint q_asym_term (qt : q256) (odd : nat -> q256) (n : nat) : q256 :=
  match n with
  | O => q_one
  | S k => neg_q (mul (mul (q_asym_term qt odd k) qt) (odd k))
  end.

Lemma term_factor_error d a b :
  Rabs d<=bpow radix2 (-249) -> Rabs a<=bpow radix2 (-255) -> Rabs b<=bpow radix2 (-255) ->
  Rabs ((1+d)*(1+a)*(1+b)-1)<=bpow radix2 (-247).
Proof.
  intros D A B. apply Rabs_le_inv in D,A,B.
  bpow_num_all. apply Rabs_le; split; interval with (i_prec 300).
Qed.

Lemma term_error_step k e f : (k<400)%nat ->
  Rabs e<=INR k*bpow radix2 (-246) -> Rabs f<=bpow radix2 (-247) ->
  Rabs ((1+e)*(1+f)-1)<=INR (S k)*bpow radix2 (-246).
Proof.
  intros K E F.
  assert (Kr : 0<=INR k<=400).
  { split; [apply pos_INR | rewrite INR_IZR_INZ; apply IZR_le; lia]. }
  assert (Small : Rabs e<=1).
  { eapply Rle_trans; [exact E | ].
    apply Rle_trans with (400*bpow radix2 (-246)).
    - apply Rmult_le_compat_r; [apply bpow_ge_0 | lra].
    - bpow_num. lra. }
  replace ((1+e)*(1+f)-1) with (e+(1+e)*f) by ring.
  eapply Rle_trans; [apply Rabs_triang | ]. rewrite Rabs_mult.
  assert (One : Rabs (1+e)<=2).
  { eapply Rle_trans; [apply Rabs_triang | ]. rewrite Rabs_R1. lra. }
  assert (Product : Rabs (1+e)*Rabs f<=2*bpow radix2 (-247)).
  { apply Rmult_le_compat; try apply Rabs_pos; assumption. }
  rewrite S_INR. replace (2*bpow radix2 (-247)) with (bpow radix2 (-246)) in Product
    by (change 2 with (bpow radix2 1); rewrite <- bpow_plus; reflexivity).
  nra.
Qed.

Theorem q_asym_term_error qt odd t n : (n<=400)%nat -> valid qt ->
  (exists d, Rabs d<=bpow radix2 (-249) /\ qval qt=(t/2)*(1+d)) ->
  (forall k, (k<400)%nat -> valid (odd k) /\ qval (odd k)=2*INR k+1) ->
  valid (q_asym_term qt odd n) /\ exists e,
    Rabs e<=INR n*bpow radix2 (-246) /\
    qval (q_asym_term qt odd n)=asym_term n t*(1+e).
Proof.
  intros N Qt [d [D T]] Odd. induction n as [ | k IH].
  - cbn [q_asym_term]. destruct q_one_ok as [Q V]. split; [exact Q | ].
    exists 0. split; [rewrite Rabs_R0; simpl; lra | ].
    rewrite V. unfold asym_term, ErfcxAsymptotic.asym_coefficient. simpl. field.
  - destruct (IH ltac:(lia)) as [Q [e [E Value]]].
    destruct (Odd k ltac:(lia)) as [O Coeff].
    destruct (mul_relative _ _ Q Qt) as [Q1 [a [A V1]]].
    destruct (mul_relative _ _ Q1 O) as [Q2 [b [Bb V2]]].
    destruct (neg_any _ Q2) as [Q3 V3].
    split; [exact Q3 | ].
    set (f := (1+d)*(1+a)*(1+b)-1).
    exists ((1+e)*(1+f)-1). split.
    + apply term_error_step; [lia | exact E | ]. apply term_factor_error; assumption.
    + cbn [q_asym_term]. rewrite V3,V2,V1,Value,T,Coeff,asym_term_step.
      unfold f. field.
Qed.

Theorem q_asym_stop_remainder qt odd t n : (S n<=400)%nat -> 0<=t -> valid qt ->
  (exists d, Rabs d<=bpow radix2 (-249) /\ qval qt=(t/2)*(1+d)) ->
  (forall k, (k<400)%nat -> valid (odd k) /\ qval (odd k)=2*INR k+1) ->
  (top (q_asym_term qt odd (S n)) < -262)%Z ->
  Rabs (ErfcxTailIntegral.tail_integral t-ErfcxAsymptotic.asym_polynomial n t)<=/2^261.
Proof.
  intros N T Qt Square Odd Stop.
  destruct (q_asym_term_error qt odd t (S n) N Qt Square Odd) as [Q [e [E Value]]].
  assert (Small : Rabs e<=/2).
  { eapply Rle_trans; [exact E | ].
    apply Rle_trans with (400*bpow radix2 (-246)).
    - apply Rmult_le_compat_r; [apply bpow_ge_0 | rewrite INR_IZR_INZ; apply IZR_le; lia].
    - bpow_num. lra. }
  apply (accurate_series_stopped_remainder n t (qval (q_asym_term qt odd (S n)))); [exact T | | ].
  - rewrite Value. replace (asym_term (S n) t*(1+e)-asym_term (S n) t)
      with (e*asym_term (S n) t) by ring.
    rewrite Rabs_mult. apply Rmult_le_compat_r; [apply Rabs_pos | exact Small].
  - pose proof (top_small _ (-262) Q Stop) as B.
    replace (/2^262) with (bpow radix2 (-262)) by (bpow_num; simpl; field). lra.
Qed.
