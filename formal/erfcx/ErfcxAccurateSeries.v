(** Exact asymptotic terms and the accurate tail's truncation remainder.
    Q256 evaluation error is a separate obligation. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
Require Import StageGappa Expm1Series ErfcxFactorial ErfcxAsymptotic ErfcxTailIntegral.
Open Scope R_scope.

Definition asym_term k t := asym_coefficient k t*INR(fact(2*k)).

Lemma asym_term_step k t :
  asym_term (S k) t= -t*(2*INR k+1)/2*asym_term k t.
Proof.
  unfold asym_term, asym_coefficient.
  replace (2*S k)%nat with (S (S (2*k))) by lia.
  rewrite !INR_fact_succ, !S_INR, mult_INR. cbn [pow].
  assert (F : INR(fact k)<>0) by (pose proof (lt_0_INR _ (lt_O_fact k)); lra).
  assert (K : INR k+1<>0) by (pose proof (pos_INR k); lra).
  change (INR 2) with 2. field; split; assumption.
Qed.

Lemma asym_term_magnitude k t : 0<=t ->
  Rabs (asym_term k t)=(t/4)^k/INR(fact k)*INR(fact(2*k)).
Proof.
  intros T. unfold asym_term, asym_coefficient, Rdiv.
  rewrite !Rabs_mult, <- RPow_abs, Rabs_mult, Rabs_Ropp, !Rabs_Rinv.
  rewrite (Rabs_pos_eq t) by exact T.
  rewrite (Rabs_pos_eq 4) by lra.
  rewrite (Rabs_pos_eq (INR(fact k))) by apply pos_INR.
  rewrite (Rabs_pos_eq (INR(fact(2*k)))) by apply pos_INR.
  reflexivity.
  all: pose proof (lt_0_INR _ (lt_O_fact k)); lra.
Qed.

Theorem accurate_series_remainder n t : 0<=t ->
  Rabs (tail_integral t-asym_polynomial n t)<=Rabs (asym_term (S n) t).
Proof.
  intros T. pose proof (tail_integral_asymptotic n t T) as E.
  assert (AbsSign : Rabs ((-1)^S n)=1).
  { pose proof (alternating_sign_square (S n)) as Sign2.
    apply (f_equal Rabs) in Sign2. rewrite Rabs_mult,Rabs_R1 in Sign2.
    pose proof (Rabs_pos ((-1)^S n)). nra. }
  rewrite asym_term_magnitude by exact T.
  fold (asym_next_coefficient n t).
  rewrite <- (Rmult_1_l (Rabs (tail_integral t-asym_polynomial n t))), <- AbsSign, <- Rabs_mult.
  rewrite Rabs_pos_eq by lra. exact (proj2 E).
Qed.

Lemma accurate_series_cap_term t : 0<=t<=/2^8 ->
  Rabs (asym_term 400 t)<=/2^319.
Proof.
  intros T. rewrite asym_term_magnitude by lra. binary_factorials.
  interval with (i_prec 512).
Qed.

Theorem accurate_series_cap_remainder t : 0<=t<=/2^8 ->
  Rabs (tail_integral t-asym_polynomial 399 t)<=/2^319.
Proof.
  intros T. eapply Rle_trans; [apply accurate_series_remainder; lra | ].
  apply accurate_series_cap_term. exact T.
Qed.

(** A computed stopping term need only retain half its exact magnitude.
    The Q256 loop must separately establish that relation and its top-bit test. *)
Theorem accurate_series_stopped_remainder n t term : 0<=t ->
  Rabs (term-asym_term (S n) t)<=/2*Rabs (asym_term (S n) t) ->
  Rabs term<=/2^262 ->
  Rabs (tail_integral t-asym_polynomial n t)<=/2^261.
Proof.
  intros T Error Small.
  assert (Exact : Rabs (asym_term (S n) t)<=/2^261).
  { pose proof (Rabs_triang (asym_term (S n) t-term) term) as Triangle.
    replace (asym_term (S n) t-term+term) with (asym_term (S n) t) in Triangle by ring.
    rewrite Rabs_minus_sym in Triangle.
    assert (Budget : 2*(/2^262)=/2^261) by (simpl; field). lra. }
  eapply Rle_trans; [apply accurate_series_remainder; exact T | exact Exact].
Qed.
