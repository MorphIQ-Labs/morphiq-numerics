(** Exact rational Taylor coefficients and their analytic error budget. *)
From Coq Require Import Reals ZArith Lia Lra Psatz QArith Qreals Qreduction.
From Coquelicot Require Import Coquelicot.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Q Require Import QSpec.
Require Import StageGappa ErfcxFactorial ErfcxGaussianTarget ErfcxTaylorCoefficients ErfcxTaylorErrorBudget
  ErfcxAccurateTaylorCoefficients ErfcxTaylorRemainder.
Open Scope R_scope.
Fixpoint real_taylor_pair c a0 a1 n : R*R :=
  match n with O => (a0,a1) | S k =>
    let '(p,u):=real_taylor_pair c a0 a1 k in
    (u,(2*c*u+2*p)/INR(S(S k))) end.
Lemma real_taylor_pair_next c a0 a1 n :
  fst(real_taylor_pair c a0 a1 (S n))=snd(real_taylor_pair c a0 a1 n).
Proof. cbn [real_taylor_pair];destruct(real_taylor_pair c a0 a1 n);reflexivity. Qed.
Theorem real_taylor_pair_error c a0 a1 n : Rabs c<=16 ->
  Rabs(a0-taylor_coefficient 0 c)<=bpow radix2 (-176) ->
  Rabs(a1-taylor_coefficient 1 c)<=bpow radix2 (-176) ->
  (n<=98)%nat ->
  Rabs(fst(real_taylor_pair c a0 a1 n)-taylor_coefficient n c)<=
    IZR(fst(taylor_error_budget n))*bpow radix2 (-176) /\
  Rabs(snd(real_taylor_pair c a0 a1 n)-taylor_coefficient (S n) c)<=
    IZR(snd(taylor_error_budget n))*bpow radix2 (-176).
Proof.
  intros C A0 A1. induction n as [|n IH];intros N.
  - cbn [real_taylor_pair taylor_error_budget fst snd];split;lra.
  - destruct(IH ltac:(lia)) as [P U].
    pose proof(coefficient_error_propagation c
      (fst(real_taylor_pair c a0 a1 n))(snd(real_taylor_pair c a0 a1 n))
      (taylor_coefficient n c)(taylor_coefficient (S n) c)
      _ _ (INR(S(S n))) C ltac:(apply lt_0_INR;lia) P U) as Error.
    split.
    + rewrite real_taylor_pair_next,taylor_error_budget_next;exact U.
    + rewrite taylor_coefficient_step. cbn [real_taylor_pair].
      destruct(real_taylor_pair c a0 a1 n) as [p u] eqn:Pair.
      cbn [fst snd] in Error |- *.
      eapply Rle_trans;[exact Error|].
      replace ((32*(IZR(snd(taylor_error_budget n))*bpow radix2 (-176))+
        2*(IZR(fst(taylor_error_budget n))*bpow radix2 (-176)))/INR(S(S n))) with
        (((32*IZR(snd(taylor_error_budget n))+2*IZR(fst(taylor_error_budget n)))/INR(S(S n)))*bpow radix2 (-176)) by (unfold Rdiv;ring).
      apply Rmult_le_compat_r;[apply bpow_ge_0|].
      pose proof(taylor_error_budget_step n);lra.
Qed.
Lemma real_taylor_coefficient_error c a0 a1 n : Rabs c<=16 ->
  Rabs(a0-taylor_coefficient 0 c)<=bpow radix2 (-176) ->
  Rabs(a1-taylor_coefficient 1 c)<=bpow radix2 (-176) -> (n<=98)%nat ->
  Rabs(fst(real_taylor_pair c a0 a1 n)-taylor_coefficient n c)<=bpow radix2 (-136).
Proof.
  intros C A0 A1 N. destruct(real_taylor_pair_error c a0 a1 n C A0 A1 N) as [P _].
  destruct(taylor_error_budget_range n ltac:(lia)) as [Budget _].
  eapply Rle_trans;[exact P|].
  replace (-136)%Z with (40+ -176)%Z by reflexivity;rewrite bpow_plus.
  apply Rmult_le_compat_r;[apply bpow_ge_0|]. rewrite <- IZR_pow2 by lia;apply IZR_le;lia.
Qed.
Definition real_taylor_polynomial n c a0 a1 h :=
  sum_f_R0(fun k=>fst(real_taylor_pair c a0 a1 k)*h^k)n.
Lemma real_taylor_polynomial_error n c a0 a1 h : Rabs c<=16 -> Rabs h<=1 ->
  Rabs(a0-taylor_coefficient 0 c)<=bpow radix2 (-176) ->
  Rabs(a1-taylor_coefficient 1 c)<=bpow radix2 (-176) -> (n<=98)%nat ->
  Rabs(real_taylor_polynomial n c a0 a1 h-taylor_polynomial n c h)<=INR(S n)*bpow radix2 (-136).
Proof.
  intros C H A0 A1 N. unfold real_taylor_polynomial,taylor_polynomial.
  assert (Same : sum_f_R0(fun k=>h^k/INR(fact k)*Derive_n gaussian_erfcx k c)n=
    sum_f_R0(fun k=>taylor_coefficient k c*h^k)n).
  { apply sum_eq. intros k K. unfold taylor_coefficient,Rdiv;ring. }
  rewrite Same,<- minus_sum. apply Rle_trans with
    (sum_f_R0(fun _=>bpow radix2 (-136))n).
  - eapply Rle_trans;[apply sum_f_R0_triangle|]. apply sum_Rle. intros k K.
    replace (fst(real_taylor_pair c a0 a1 k)*h^k-taylor_coefficient k c*h^k) with
      ((fst(real_taylor_pair c a0 a1 k)-taylor_coefficient k c)*h^k) by ring.
    rewrite Rabs_mult,<- RPow_abs.
    assert (Hp : Rabs h^k<=1) by (replace 1 with (1^k) by apply pow1;apply pow_incr;split;[apply Rabs_pos|exact H]).
    pose proof(real_taylor_coefficient_error c a0 a1 k C A0 A1 ltac:(lia)) as E.
    pose proof(pow_le(Rabs h)k(Rabs_pos h));pose proof(Rabs_pos(fst(real_taylor_pair c a0 a1 k)-taylor_coefficient k c));nra.
  - rewrite sum_cte;right;ring.
Qed.
Theorem real_taylor_48_error c a0 a1 h : Rabs c<=16 -> Rabs h<=/8 ->
  Rabs(gaussian_erfcx c)<=3 ->
  Rabs(a0-taylor_coefficient 0 c)<=bpow radix2 (-176) ->
  Rabs(a1-taylor_coefficient 1 c)<=bpow radix2 (-176) ->
  Rabs(real_taylor_polynomial 48 c a0 a1 h-gaussian_erfcx(c+h))<=bpow radix2 (-84).
Proof.
  intros C H F A0 A1.
  pose proof(real_taylor_polynomial_error 48 c a0 a1 h C ltac:(lra) A0 A1 ltac:(lia)) as Error.
  pose proof(taylor_local_remainder 48 c h ltac:(lia) C H F) as Trunc.
  replace (real_taylor_polynomial 48 c a0 a1 h-gaussian_erfcx(c+h)) with
    ((real_taylor_polynomial 48 c a0 a1 h-taylor_polynomial 48 c h)+
     (taylor_polynomial 48 c h-gaussian_erfcx(c+h))) by ring.
  eapply Rle_trans;[apply Rabs_triang|]. rewrite (Rabs_minus_sym(taylor_polynomial 48 c h)).
  eapply Rle_trans with (INR(49)*bpow radix2 (-136)+512*5^49/INR(fact 49));[lra|].
  binary_factorials. bpow_num. interval with(i_prec 400).
Qed.
