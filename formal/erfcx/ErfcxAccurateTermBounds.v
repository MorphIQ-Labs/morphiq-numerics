(** Uniform magnitude bounds for all terms visited by the accurate tail. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
Require Import StageGappa ErfcxFactorial ErfcxAccurateSeries.
Open Scope R_scope.

Lemma asym_term_abs_step k t : 0<=t ->
  Rabs (asym_term (S k) t)=(t*(2*INR k+1)/2)*Rabs (asym_term k t).
Proof.
  intros T. rewrite asym_term_step,Rabs_mult.
  replace (-t*(2*INR k+1)/2) with (-(t*(2*INR k+1)/2)) by field.
  rewrite Rabs_Ropp,Rabs_pos_eq; [reflexivity | pose proof (pos_INR k); nra].
Qed.

Lemma asym_term_step_bound k t : (k<400)%nat -> 0<=t<=/2^8 ->
  Rabs (asym_term (S k) t)<=2*Rabs (asym_term k t).
Proof.
  intros K T. rewrite asym_term_abs_step by lra.
  apply Rmult_le_compat_r; [apply Rabs_pos | ].
  assert (0<=INR k<=400) by (split; [apply pos_INR | rewrite INR_IZR_INZ; apply IZR_le; lia]).
  simpl in T. nra.
Qed.

Lemma asym_term_initial_bound n t : (n<=128)%nat -> 0<=t<=/2^8 ->
  Rabs (asym_term n t)<=1.
Proof.
  intros N T. induction n as [ | k IH].
  - assert (Zero : asym_term 0 t=1) by (unfold asym_term, ErfcxAsymptotic.asym_coefficient; simpl; field).
    rewrite Zero,Rabs_R1. lra.
  - rewrite asym_term_abs_step by lra.
    apply Rle_trans with (1*Rabs (asym_term k t)).
    + apply Rmult_le_compat_r; [apply Rabs_pos | ].
      assert (0<=INR k<=128) by (split; [apply pos_INR | rewrite INR_IZR_INZ; apply IZR_le; lia]).
      simpl in T. nra.
    + rewrite Rmult_1_l. apply IH. lia.
Qed.

Lemma asym_term_128_bound t : 0<=t<=/2^8 ->
  Rabs (asym_term 128 t)<=bpow radix2 (-300).
Proof.
  intros T. rewrite asym_term_magnitude by lra. binary_factorials.
  bpow_num. interval with (i_prec 400).
Qed.

Lemma asym_term_later_bound j t : (128+j<=400)%nat -> 0<=t<=/2^8 ->
  Rabs (asym_term (128+j) t)<=2^j*bpow radix2 (-300).
Proof.
  intros N T. induction j as [ | j IH].
  - replace (128+0)%nat with 128%nat by lia.
    cbn [pow]. rewrite Rmult_1_l. apply asym_term_128_bound. exact T.
  - replace (128+S j)%nat with (S (128+j)) by lia.
    eapply Rle_trans; [apply asym_term_step_bound; [lia | exact T] | ].
    cbn [pow]. rewrite Rmult_assoc.
    apply Rmult_le_compat_l; [lra | apply IH; lia].
Qed.

Theorem asym_terms_bounded n t : (n<=400)%nat -> 0<=t<=/2^8 ->
  Rabs (asym_term n t)<=1.
Proof.
  intros N T. destruct (le_dec n 128) as [Small | Large].
  - apply asym_term_initial_bound; assumption.
  - replace n with (128+(n-128))%nat by lia.
    eapply Rle_trans; [apply asym_term_later_bound; [lia | exact T] | ].
    replace (2^(n-128)) with (bpow radix2 (Z.of_nat (n-128)))
      by (rewrite bpow_powerRZ, <- pow_powerRZ; reflexivity).
    rewrite <- bpow_plus. change 1 with (bpow radix2 0). apply bpow_le. lia.
Qed.
