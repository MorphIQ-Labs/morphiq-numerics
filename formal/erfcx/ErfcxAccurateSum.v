(** Accumulated Q256 rounding error of the accurate asymptotic sum. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Q Require Import Q256 Q256Real.
Require Import StageGappa ErfcxAsymptotic ErfcxAccurateSeries ErfcxAccurateTerms ErfcxAccurateTermBounds.
Open Scope R_scope.

Lemma asym_polynomial_step n t :
  asym_polynomial (S n) t=asym_polynomial n t+asym_term (S n) t.
Proof. reflexivity. Qed.

Lemma asym_polynomial_bound n t : (n<=400)%nat -> 0<=t<=/2^8 ->
  Rabs (asym_polynomial n t)<=INR (S n).
Proof.
  intros N T. induction n as [ | n IH].
  - replace (asym_polynomial 0 t) with 1 by (unfold asym_polynomial,asym_coefficient; simpl; field).
    rewrite Rabs_R1. simpl. lra.
  - rewrite asym_polynomial_step. eapply Rle_trans; [apply Rabs_triang | ].
    pose proof (asym_terms_bounded (S n) t N T) as Term.
    specialize (IH ltac:(lia)). rewrite S_INR. lra.
Qed.



Fixpoint q_asym_sum qt odd n :=
  match n with
  | O => q_one
  | S k => add (q_asym_sum qt odd k) (q_asym_term qt odd (S k))
  end.

Lemma error_to_magnitude q x error bound :
  Rabs (q-x)<=error -> Rabs x<=bound -> Rabs q<=error+bound.
Proof.
  intros E B. pose proof (Rabs_triang (q-x) x) as T.
  replace (q-x+x) with q in T by ring. lra.
Qed.

Theorem q_asym_sum_error qt odd t n : (n<=399)%nat -> 0<=t<=/2^8 -> valid qt ->
  (exists d, Rabs d<=bpow radix2 (-249) /\ qval qt=(t/2)*(1+d)) ->
  (forall k, (k<400)%nat -> valid (odd k) /\ qval (odd k)=2*INR k+1) ->
  valid (q_asym_sum qt odd n) /\
  Rabs (qval (q_asym_sum qt odd n)-asym_polynomial n t)<=INR n*bpow radix2 (-235).
Proof.
  intros N T Qt Square Odd. induction n as [ | k IH].
  - cbn [q_asym_sum]. destruct q_one_ok as [Q V]. split; [exact Q | ].
    rewrite V. replace (asym_polynomial 0 t) with 1 by (unfold asym_polynomial,asym_coefficient; simpl; field).
    rewrite Rminus_diag_eq,Rabs_R0 by reflexivity. simpl. lra.
  - destruct (IH ltac:(lia)) as [Sum SumError].
    destruct (q_asym_term_error qt odd t (S k) ltac:(lia) Qt Square Odd) as [Term [e [E Value]]].
    assert (K : 0<=INR k<=399).
    { split; [apply pos_INR | rewrite INR_IZR_INZ; apply IZR_le; lia]. }
    assert (TermError : Rabs (qval (q_asym_term qt odd (S k))-asym_term (S k) t)<=400*bpow radix2 (-246)).
    { rewrite Value. replace (asym_term (S k) t*(1+e)-asym_term (S k) t)
        with (asym_term (S k) t*e) by ring.
      rewrite Rabs_mult. apply Rle_trans with (1*(INR (S k)*bpow radix2 (-246))).
      - apply Rmult_le_compat; try apply Rabs_pos; [apply asym_terms_bounded; [lia | exact T] | exact E].
      - rewrite Rmult_1_l,S_INR. apply Rmult_le_compat_r; [apply bpow_ge_0 | lra]. }
    assert (SumAbs : Rabs (qval (q_asym_sum qt odd k))<=401).
    { eapply Rle_trans; [eapply error_to_magnitude; [exact SumError | apply asym_polynomial_bound; [lia | exact T]] | ].
      rewrite S_INR. bpow_num_all. nra. }
    assert (TermAbs : Rabs (qval (q_asym_term qt odd (S k)))<=2).
    { eapply Rle_trans; [eapply error_to_magnitude; [exact TermError | apply asym_terms_bounded; [lia | exact T]] | ].
      bpow_num. lra. }
    destruct (add_any _ _ Sum Term) as [Result AddError].
    cbn [q_asym_sum]. split; [exact Result | ].
    assert (Round : Rabs (qval (add (q_asym_sum qt odd k) (q_asym_term qt odd (S k)))-
      (qval (q_asym_sum qt odd k)+qval (q_asym_term qt odd (S k))))<=401*bpow radix2 (-254)).
    { eapply Rle_trans; [exact AddError | ]. rewrite Rmult_comm.
      apply Rmult_le_compat_r; [apply bpow_ge_0 | apply Rmax_lub; lra]. }
    rewrite asym_polynomial_step.
    replace (qval (add (q_asym_sum qt odd k) (q_asym_term qt odd (S k)))-
      (asym_polynomial k t+asym_term (S k) t)) with
      ((qval (add (q_asym_sum qt odd k) (q_asym_term qt odd (S k)))-
        (qval (q_asym_sum qt odd k)+qval (q_asym_term qt odd (S k))))+
       ((qval (q_asym_sum qt odd k)-asym_polynomial k t)+
        (qval (q_asym_term qt odd (S k))-asym_term (S k) t))) by ring.
    eapply Rle_trans; [apply Rabs_triang | ].
    pose proof (Rabs_triang (qval (q_asym_sum qt odd k)-asym_polynomial k t)
      (qval (q_asym_term qt odd (S k))-asym_term (S k) t)) as Triangle.
    assert (Budget : 401*bpow radix2 (-254)+400*bpow radix2 (-246)<=bpow radix2 (-235))
      by (bpow_num; lra).
    rewrite S_INR. nra.
Qed.

Theorem q_asym_sum_integral qt odd t n : (n<=399)%nat -> 0<=t<=/2^8 -> valid qt ->
  (exists d, Rabs d<=bpow radix2 (-249) /\ qval qt=(t/2)*(1+d)) ->
  (forall k, (k<400)%nat -> valid (odd k) /\ qval (odd k)=2*INR k+1) ->
  (n=399%nat \/ (top (q_asym_term qt odd (S n)) < -262)%Z) ->
  valid (q_asym_sum qt odd n) /\
  Rabs (qval (q_asym_sum qt odd n)-ErfcxTailIntegral.tail_integral t)<=bpow radix2 (-226).
Proof.
  intros N T Qt Square Odd Stop.
  destruct (q_asym_sum_error qt odd t n N T Qt Square Odd) as [Q Error].
  split; [exact Q | ].
  assert (Remainder : Rabs (ErfcxTailIntegral.tail_integral t-asym_polynomial n t)<=/2^261).
  { destruct Stop as [-> | Stop].
    - eapply Rle_trans; [apply accurate_series_cap_remainder; exact T | ]. simpl; lra.
    - apply (q_asym_stop_remainder qt odd t n); try assumption; [lia | lra]. }
  replace (qval (q_asym_sum qt odd n)-ErfcxTailIntegral.tail_integral t) with
    ((qval (q_asym_sum qt odd n)-asym_polynomial n t)+
     (asym_polynomial n t-ErfcxTailIntegral.tail_integral t)) by ring.
  eapply Rle_trans; [apply Rabs_triang | ].
  rewrite Rabs_minus_sym in Remainder.
  assert (Count : INR n<=399) by (rewrite INR_IZR_INZ; apply IZR_le; lia).
  assert (Budget : 399*bpow radix2 (-235)+/2^261<=bpow radix2 (-226)) by (bpow_num; simpl; lra).
  pose proof (bpow_ge_0 radix2 (-235)). nra.
Qed.
