(** Connect exact rational recurrence certificates to the Gaussian target. *)
From Coq Require Import Reals ZArith Lia Lra Psatz List QArith Qreals.
From Flocq Require Import Core.
From Q Require Import Q256 Q256Real.
Require Import StageGappa ErfcxConstants ErfcxGaussianTarget ErfcxTaylorCoefficients
  ErfcxAccurateCenterModel ErfcxAccurateCenters ErfcxAccurateCenterBounds
  ErfcxAccurateTaylorInitial ErfcxRationalTaylor ErfcxRationalPolynomial.
Open Scope R_scope.
Lemma rational_first_error c a0 a1 : Rabs c<=16 ->
  Rabs(a0-gaussian_erfcx c)<=bpow radix2 (-251) ->
  a1=2*c*a0-qval q_c2 ->
  Rabs(a1-taylor_coefficient 1 c)<=bpow radix2 (-176).
Proof.
  intros C A0 A1. destruct q_c2_ok as [Q C2].
  rewrite A1,taylor_coefficient_one.
  replace (2*c*a0-qval q_c2-(2*c*gaussian_erfcx c-2*inv_sqrt_pi)) with
    (2*c*(a0-gaussian_erfcx c)-(qval q_c2-2*inv_sqrt_pi)) by ring.
  eapply Rle_trans;[apply Rabs_triang|]. rewrite Rabs_Ropp,!Rabs_mult,(Rabs_pos_eq 2) by lra.
  pose proof(Rabs_pos c);pose proof(Rabs_pos(a0-gaussian_erfcx c)). bpow_num_all;nra.
Qed.
Theorem rational_table_error i c a0 a1 cs h : (i<177)%nat ->
  Q2R c=accurate_center i -> Q2R a0=qval(q_center i) ->
  Q2R a1=2*Q2R c*Q2R a0-qval q_c2 ->
  rat_recurrence_check c a0 a1 cs=true -> length cs=49%nat -> Rabs h<=/8 ->
  Rabs(rat_horner h cs-gaussian_erfcx(accurate_center i+h))<=bpow radix2 (-84).
Proof.
  intros I C A0 A1 Check Len H.
  destruct(accurate_center_bounds i I) as [Cr Fr].
  destruct(q_center_ok i I) as [_ CenterError].
  rewrite <- C in CenterError,Cr,Fr |- *.
  rewrite <- A0 in CenterError.
  rewrite (rat_horner_taylor c a0 a1 cs h Check Len).
  apply real_taylor_48_error;[exact Cr|exact H|apply Rabs_le;lra| |].
  - rewrite taylor_coefficient_zero. eapply Rle_trans;[exact CenterError|apply bpow_le;lia].
  - apply rational_first_error with(a0:=Q2R a0);assumption.
Qed.
Lemma rational_enclosure_relative p t f a0 : /128<=a0 ->
  Rabs(t-f)<=bpow radix2 (-84) -> 0.9*a0<=t ->
  Rabs(p-t)<=3*bpow radix2 (-71)*a0 ->
  0<f /\ Rabs((p-f)/f)<=bpow radix2 (-69).
Proof.
  intros A0 Trunc Lower Difference.
  pose proof(Rabs_le_inv _ _ Trunc) as T.
  assert (F : 0<f) by (bpow_num_all;lra).
  assert (Error : Rabs(p-f)<=bpow radix2 (-69)*f).
  { replace (p-f) with ((p-t)+(t-f)) by ring.
    eapply Rle_trans;[apply Rabs_triang|]. bpow_num_all;lra. }
  split;[exact F|]. unfold Rdiv.
  rewrite Rabs_mult,Rabs_Rinv,(Rabs_pos_eq f) by lra.
  apply (Rmult_le_reg_r f);[exact F|].
  rewrite Rmult_assoc,Rinv_l,Rmult_1_r by lra;exact Error.
Qed.
