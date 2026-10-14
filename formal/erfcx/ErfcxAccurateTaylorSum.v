(** Accumulation of Q256 Taylor terms, including the first addition. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Q Require Import Q256 Q256Real.
Require Import StageGappa ErfcxGaussianTarget ErfcxTaylorCoefficients ErfcxTaylorRemainder
  ErfcxAccurateCenterModel ErfcxAccurateCenters ErfcxAccurateCenterBounds
  ErfcxAccurateTaylorStep ErfcxAccurateTaylorTerms.
Open Scope R_scope.
Fixpoint q_taylor_sum c i h n :=
  match n with O => q_center i | S k => add (q_taylor_sum c i h k) (q_taylor_term c i h k) end.
Lemma taylor_polynomial_zero c h : taylor_polynomial 0 c h=gaussian_erfcx c.
Proof. unfold taylor_polynomial; cbn [sum_f_R0 pow fact INR]. change (1/1*gaussian_erfcx c=gaussian_erfcx c);field. Qed.
Lemma taylor_polynomial_next n c h :
  taylor_polynomial (S n) c h=taylor_polynomial n c h+exact_taylor_term c h (S n).
Proof. unfold taylor_polynomial,exact_taylor_term,taylor_coefficient. cbn [sum_f_R0]. unfold Rdiv;ring. Qed.

Theorem q_taylor_sum_error c i h n : valid c -> valid h -> (i<177)%nat ->
  qval c=accurate_center i -> Rabs(qval h)<=/8 -> (n<=99)%nat ->
  valid(q_taylor_sum c i h n) /\ Rabs(qval(q_taylor_sum c i h n))<=INR(S n)*bpow radix2 70 /\
  Rabs(qval(q_taylor_sum c i h n)-taylor_polynomial n (accurate_center i) (qval h))<=
    bpow radix2 (-251)+INR n*bpow radix2 (-134).
Proof.
  intros C H I Cv Hr. induction n as [|n IH]; intros N.
  - destruct(q_center_ok i I) as [A Ae]. destruct(accurate_center_bounds i I) as [Cr Fr].
    cbn [q_taylor_sum]. rewrite taylor_polynomial_zero. split; [exact A|]. split.
    + change (Rabs(qval(q_center i))<=1*bpow radix2 70).
      apply Rabs_le_inv in Ae. bpow_num_all. apply Rabs_le;lra.
    + change (Rabs(qval(q_center i)-gaussian_erfcx(accurate_center i))<=bpow radix2 (-251)+0*bpow radix2 (-134)). lra.
  - destruct(IH ltac:(lia)) as [SumValid [Sm Se]].
    destruct(q_taylor_term_error c i h n C H I Cv Hr ltac:(lia)) as [T [Tm Te]].
    destruct(q_add_magnitude _ _ _ _ SumValid T Sm Tm) as [Result [Ae Am]].
    assert (Count : INR(S n)<=100).
    { replace 100 with (INR 100) by (rewrite INR_IZR_INZ;reflexivity). apply le_INR;lia. }
    assert (Max : Rmax (INR(S n)*bpow radix2 70) (bpow radix2 69)<=bpow radix2 77).
    { apply Rmax_lub; bpow_num; lra. }
    assert (Round : Rabs(qval(add(q_taylor_sum c i h n)(q_taylor_term c i h n))-
      (qval(q_taylor_sum c i h n)+qval(q_taylor_term c i h n)))<=bpow radix2 (-177)).
    { eapply Rle_trans; [exact Ae|]. eapply Rle_trans with (bpow radix2 (-254)*bpow radix2 77).
      - apply Rmult_le_compat_l; [apply bpow_ge_0|exact Max].
      - rewrite <- bpow_plus. apply Rle_refl. }
    cbn [q_taylor_sum]. split; [exact Result|]. split.
    + eapply Rle_trans; [exact Am|].
      assert (A : bpow radix2 (-254)*Rmax (INR(S n)*bpow radix2 70) (bpow radix2 69)<=bpow radix2 (-177)).
      { eapply Rle_trans with (bpow radix2 (-254)*bpow radix2 77).
        - apply Rmult_le_compat_l; [apply bpow_ge_0|exact Max].
        - rewrite <- bpow_plus. apply Rle_refl. }
      rewrite (S_INR(S n)). bpow_num_all;lra.
    + rewrite taylor_polynomial_next.
      replace (qval(add(q_taylor_sum c i h n)(q_taylor_term c i h n))-
        (taylor_polynomial n (accurate_center i)(qval h)+exact_taylor_term (accurate_center i)(qval h)(S n))) with
        ((qval(add(q_taylor_sum c i h n)(q_taylor_term c i h n))-
          (qval(q_taylor_sum c i h n)+qval(q_taylor_term c i h n)))+
         (qval(q_taylor_sum c i h n)-taylor_polynomial n (accurate_center i)(qval h))+
         (qval(q_taylor_term c i h n)-exact_taylor_term (accurate_center i)(qval h)(S n))) by ring.
      eapply Rle_trans; [apply Rabs_triang|].
      pose proof(Rabs_triang
        (qval(add(q_taylor_sum c i h n)(q_taylor_term c i h n))-
          (qval(q_taylor_sum c i h n)+qval(q_taylor_term c i h n)))
        (qval(q_taylor_sum c i h n)-taylor_polynomial n (accurate_center i)(qval h))) as Add.
      rewrite (S_INR n). bpow_num_all;lra.
Qed.
Theorem q_taylor_prefix_error c i h n : valid c -> valid h -> (i<177)%nat ->
  qval c=accurate_center i -> Rabs(qval h)<=/8 -> (n<=99)%nat ->
  Rabs(qval(q_taylor_sum c i h n)-taylor_polynomial n (accurate_center i)(qval h))<=bpow radix2 (-126).
Proof.
  intros C H I Cv Hr N. pose proof(proj2(proj2(q_taylor_sum_error c i h n C H I Cv Hr N))) as E.
  assert (Count : INR n<=100).
  { replace 100 with (INR 100) by (rewrite INR_IZR_INZ;reflexivity). apply le_INR;lia. }
  bpow_num_all;lra.
Qed.
