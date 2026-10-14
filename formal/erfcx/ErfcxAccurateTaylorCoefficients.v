(** The complete Q256 Taylor coefficient recurrence, with a checked integer
    error majorant. No sign assumption is made about a coefficient. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Q Require Import QSpec Q256 Q256Real.
Require Import StageGappa ErfcxGaussianTarget ErfcxTaylorCoefficients ErfcxTaylorErrorBudget
  ErfcxAccurateCenterModel ErfcxAccurateCenters ErfcxAccurateCenterBounds
  ErfcxAccurateTaylorStep ErfcxAccurateTaylorInitial.
Open Scope R_scope.
Fixpoint q_taylor_coefficients c i n : q256*q256 :=
  match n with
  | O => (q_center i,q_taylor_first c i)
  | S k => let '(prev,cur):=q_taylor_coefficients c i k in
      (cur,q_taylor_step c prev cur (S k))
  end.

Lemma coefficient_approx_magnitude v a budget : Rabs a<=bpow radix2 67 ->
  (0<=budget<=2^40)%Z -> Rabs(v-a)<=IZR budget*bpow radix2 (-176) -> Rabs v<=bpow radix2 68.
Proof.
  intros A Budget Error.
  assert (K : IZR budget<=bpow radix2 40) by (rewrite <- IZR_pow2 by lia; apply IZR_le;lia).
  assert (Bound : Rabs(v-a)<=bpow radix2 (-136)).
  { replace (-136)%Z with (40+ -176)%Z by reflexivity. rewrite bpow_plus.
    eapply Rle_trans; [exact Error|]. apply Rmult_le_compat_r; [apply bpow_ge_0|exact K]. }
  replace v with ((v-a)+a) by ring. eapply Rle_trans; [apply Rabs_triang|]. bpow_num_all; lra.
Qed.

Lemma coefficient_error_propagation c p u ap au ep eu d : Rabs c<=16 -> 0<d ->
  Rabs(p-ap)<=ep -> Rabs(u-au)<=eu ->
  Rabs((2*c*u+2*p)/d-(2*c*au+2*ap)/d)<=(32*eu+2*ep)/d.
Proof.
  intros C D P U.
  replace ((2*c*u+2*p)/d-(2*c*au+2*ap)/d) with
    ((2*c*(u-au)+2*(p-ap))*(/d)) by (unfold Rdiv;ring).
  rewrite Rabs_mult,(Rabs_pos_eq(/d)) by (left;apply Rinv_0_lt_compat;exact D).
  unfold Rdiv. apply Rmult_le_compat_r; [apply Rlt_le,Rinv_0_lt_compat;exact D|].
  eapply Rle_trans; [apply Rabs_triang|]. rewrite !Rabs_mult,(Rabs_pos_eq 2) by lra.
  pose proof(Rabs_pos c);pose proof(Rabs_pos(u-au));pose proof(Rabs_pos(p-ap)). nra.
Qed.

Theorem q_taylor_coefficients_error c i n : valid c -> (i<177)%nat -> qval c=accurate_center i -> (n<=98)%nat ->
  valid(fst(q_taylor_coefficients c i n)) /\ valid(snd(q_taylor_coefficients c i n)) /\
  Rabs(qval(fst(q_taylor_coefficients c i n))-taylor_coefficient n (accurate_center i))<=
    IZR(fst(taylor_error_budget n))*bpow radix2 (-176) /\
  Rabs(qval(snd(q_taylor_coefficients c i n))-taylor_coefficient (S n) (accurate_center i))<=
    IZR(snd(taylor_error_budget n))*bpow radix2 (-176).
Proof.
  intros C I Cv. induction n as [|n IH]; intros N.
  - destruct(q_center_ok i I) as [A Ae]. destruct(q_taylor_first_error c i C I Cv) as [First Fe].
    cbn [q_taylor_coefficients taylor_error_budget fst snd].
    split; [exact A|]. split; [exact First|]. split.
    + rewrite taylor_coefficient_zero. eapply Rle_trans; [exact Ae|]. bpow_num; lra.
    + lra.
  - destruct(IH ltac:(lia)) as [Prev [Cur [Pe Ce]]].
    destruct(accurate_center_bounds i I) as [Cr Fr].
    assert (F : Rabs(gaussian_erfcx(accurate_center i))<=3) by (apply Rabs_le;lra).
    destruct(taylor_error_budget_range n ltac:(lia)) as [Bp Bc].
    assert (Pm : Rabs(qval(fst(q_taylor_coefficients c i n)))<=bpow radix2 68).
    { eapply (coefficient_approx_magnitude _ (taylor_coefficient n (accurate_center i)) (fst(taylor_error_budget n))); [apply taylor_coefficient_bound; [lia|exact Cr|exact F]|lia|exact Pe]. }
    assert (Cm : Rabs(qval(snd(q_taylor_coefficients c i n)))<=bpow radix2 68).
    { eapply (coefficient_approx_magnitude _ (taylor_coefficient (S n) (accurate_center i)) (snd(taylor_error_budget n))); [apply taylor_coefficient_bound; [lia|exact Cr|exact F]|lia|exact Ce]. }
    assert (Cmag : Rabs(qval c)<=16) by (rewrite Cv;exact Cr).
    destruct(q_taylor_step_error c _ _ (S n) C Prev Cur Cmag Pm Cm ltac:(lia)) as [Result StepError].
    pose proof (coefficient_error_propagation (qval c)
      (qval(fst(q_taylor_coefficients c i n))) (qval(snd(q_taylor_coefficients c i n)))
      (taylor_coefficient n (accurate_center i)) (taylor_coefficient (S n) (accurate_center i))
      _ _ (INR(S(S n))) Cmag ltac:(apply lt_0_INR;lia) Pe Ce) as Propagate.
    assert (NextError : Rabs(qval(q_taylor_step c (fst(q_taylor_coefficients c i n))
      (snd(q_taylor_coefficients c i n)) (S n))-taylor_coefficient (S(S n)) (accurate_center i))<=
      IZR(snd(taylor_error_budget (S n)))*bpow radix2 (-176)).
    { rewrite taylor_coefficient_step. rewrite <- Cv at 1.
      set (ideal := (2*qval c*qval(snd(q_taylor_coefficients c i n))+
        2*qval(fst(q_taylor_coefficients c i n)))/INR(S(S n))) in *.
      replace (qval(q_taylor_step c (fst(q_taylor_coefficients c i n))
        (snd(q_taylor_coefficients c i n)) (S n))-
        (2*qval c*taylor_coefficient (S n) (accurate_center i)+2*taylor_coefficient n (accurate_center i))/INR(S(S n))) with
        ((qval(q_taylor_step c (fst(q_taylor_coefficients c i n))
          (snd(q_taylor_coefficients c i n)) (S n))-ideal)+
         (ideal-(2*qval c*taylor_coefficient (S n) (accurate_center i)+2*taylor_coefficient n (accurate_center i))/INR(S(S n)))) by ring.
      eapply Rle_trans; [apply Rabs_triang|].
      eapply Rle_trans with (bpow radix2 (-176)+
        (32*(IZR(snd(taylor_error_budget n))*bpow radix2 (-176))+
         2*(IZR(fst(taylor_error_budget n))*bpow radix2 (-176)))/INR(S(S n))); [lra|].
      replace (bpow radix2 (-176)+
        (32*(IZR(snd(taylor_error_budget n))*bpow radix2 (-176))+
         2*(IZR(fst(taylor_error_budget n))*bpow radix2 (-176)))/INR(S(S n))) with
        (((32*IZR(snd(taylor_error_budget n))+2*IZR(fst(taylor_error_budget n)))/INR(S(S n))+1)*bpow radix2 (-176))
        by (unfold Rdiv;ring).
      apply Rmult_le_compat_r; [apply bpow_ge_0|apply taylor_error_budget_step]. }
    rewrite taylor_error_budget_next.
    cbn [q_taylor_coefficients]. destruct(q_taylor_coefficients c i n) as [p u] eqn:Pair.
    cbn [fst snd] in Prev,Cur,Pe,Ce,Result,NextError |- *.
    split; [exact Cur|]. split; [exact Result|]. split; assumption.
Qed.

Theorem q_taylor_coefficient_errors c i n : valid c -> (i<177)%nat -> qval c=accurate_center i -> (n<=98)%nat ->
  Rabs(qval(fst(q_taylor_coefficients c i n))-taylor_coefficient n (accurate_center i))<=bpow radix2 (-136) /\
  Rabs(qval(snd(q_taylor_coefficients c i n))-taylor_coefficient (S n) (accurate_center i))<=bpow radix2 (-136).
Proof.
  intros C I Cv N. destruct(q_taylor_coefficients_error c i n C I Cv N) as [_ [_ [P U]]].
  destruct(taylor_error_budget_range n ltac:(lia)) as [Bp Bc].
  assert (Upper : forall b : Z, (b<=2^40)%Z -> IZR b*bpow radix2 (-176)<=bpow radix2 (-136)).
  { intros b B. replace (-136)%Z with (40+ -176)%Z by reflexivity. rewrite bpow_plus.
    apply Rmult_le_compat_r; [apply bpow_ge_0|]. rewrite <- IZR_pow2 by lia. apply IZR_le;exact B. }
  split; eapply Rle_trans; [exact P|apply Upper;lia|exact U|apply Upper;lia].
Qed.
