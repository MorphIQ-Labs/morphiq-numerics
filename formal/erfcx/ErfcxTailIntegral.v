(** The normalized positive-tail integral. Its exponential weight has exact
    factorial moments, and the remaining factor is between zero and one. *)
From Coq Require Import Reals Lia Lra Psatz.
From Coquelicot Require Import Coquelicot.
Require Import ErfcxMoments.
Open Scope R_scope.

Definition tail_integrand t u := exp(-u)*exp(-t*u*u/4).
Definition tail_integral_sequence t k := RInt (tail_integrand t) 0 (INR k).
Definition tail_integral t := real (Lim_seq (tail_integral_sequence t)).

Lemma tail_integrand_continuous t u : continuous (tail_integrand t) u.
Proof.
  unfold tail_integrand. apply (@ex_derive_continuous R_AbsRing R_CompleteNormedModule).
  eexists. auto_derive; trivial.
Qed.
Lemma tail_integrand_integrable t a b : ex_RInt (tail_integrand t) a b.
Proof. apply (@ex_RInt_continuous R_CompleteNormedModule). intros. apply tail_integrand_continuous. Qed.

Lemma tail_integrand_bounds t u : 0<=t ->
  0<=tail_integrand t u<=exponential_moment 0 u.
Proof.
  intros T. unfold tail_integrand, exponential_moment. change (u^0) with 1. rewrite Rmult_1_l.
  pose proof (exp_pos (-u)). pose proof (exp_pos (-t*u*u/4)). split; [nra | ].
  assert (Power : -t*u*u/4<=0) by nra.
  assert (Bound : exp(-t*u*u/4)<=1).
  { destruct (Rle_lt_or_eq_dec _ _ Power) as [Neg | Zero].
    - apply Rlt_le. rewrite <- exp_0. apply exp_increasing. exact Neg.
    - rewrite Zero, exp_0. lra. }
  nra.
Qed.

Lemma tail_integral_partial_bounds t b : 0<=t -> 0<=b ->
  0<=RInt (tail_integrand t) 0 b<=1.
Proof.
  intros T B. split.
  - apply RInt_ge_0; [exact B | apply tail_integrand_integrable | ].
    intros u U. exact (proj1 (tail_integrand_bounds t u T)).
  - apply Rle_trans with (RInt (exponential_moment 0) 0 b).
    + apply RInt_le; [exact B | apply tail_integrand_integrable | | ].
      * apply exponential_moment_integrable.
      * intros u U. exact (proj2 (tail_integrand_bounds t u T)).
    + rewrite exponential_moment_integral. change (INR(fact 0)) with 1.
      pose proof (moment_primitive_nonpositive 0 b B). lra.
Qed.

Lemma tail_integral_sequence_increasing t : 0<=t -> forall k,
  tail_integral_sequence t k<=tail_integral_sequence t (S k).
Proof.
  intros T k. unfold tail_integral_sequence.
  pose proof (RInt_Chasles (tail_integrand t) 0 (INR k) (INR(S k))
    (tail_integrand_integrable t 0 (INR k)) (tail_integrand_integrable t (INR k) (INR(S k)))) as Split.
  assert (Positive : 0<=RInt (tail_integrand t) (INR k) (INR(S k))).
  { apply RInt_ge_0.
    - rewrite S_INR. lra.
    - apply tail_integrand_integrable.
    - intros u U. exact (proj1 (tail_integrand_bounds t u T)). }
  change (RInt (tail_integrand t) 0 (INR k)+RInt (tail_integrand t) (INR k) (INR(S k))=
    RInt (tail_integrand t) 0 (INR(S k))) in Split. lra.
Qed.

Theorem tail_integral_limit t : 0<=t ->
  is_lim_seq (tail_integral_sequence t) (tail_integral t) /\ 0<=tail_integral t<=1.
Proof.
  intros T.
  pose proof (Lim_seq_correct _ (ex_lim_seq_incr _ (tail_integral_sequence_increasing t T))) as Limit.
  assert (Bounds : forall k, 0<=tail_integral_sequence t k<=1).
  { intros k. apply tail_integral_partial_bounds; [exact T | apply pos_INR]. }
  pose proof (is_lim_seq_le (fun _ => 0) _ 0 _ (fun k => proj1 (Bounds k))
    (is_lim_seq_const 0) Limit) as Lower.
  pose proof (is_lim_seq_le _ (fun _ => 1) _ 1 (fun k => proj2 (Bounds k))
    Limit (is_lim_seq_const 1)) as Upper.
  unfold tail_integral. destruct (Lim_seq (tail_integral_sequence t)); simpl in Lower, Upper;
    try contradiction. split; [exact Limit | split; assumption].
Qed.

Lemma tail_integrand_first_order t u :
  exponential_moment 0 u-(t/4)*exponential_moment 2 u<=tail_integrand t u.
Proof.
  pose proof (exp_ineq1_le (-t*u*u/4)) as E.
  pose proof (exp_pos (-u)) as Positive.
  unfold exponential_moment, tail_integrand. simpl pow. nra.
Qed.

Lemma tail_integral_first_order_partial t b : 0<=b ->
  RInt (exponential_moment 0) 0 b-(t/4)*RInt (exponential_moment 2) 0 b<=
  RInt (tail_integrand t) 0 b.
Proof.
  intros B.
  assert (Moment : forall n, ex_RInt (exponential_moment n) 0 b)
    by (intros; apply exponential_moment_integrable).
  assert (Scaled : ex_RInt (fun u => (t/4)*exponential_moment 2 u) 0 b).
  { exact (@ex_RInt_scal R_NormedModule (exponential_moment 2) 0 b (t/4) (Moment 2%nat)). }
  assert (Low : ex_RInt (fun u => exponential_moment 0 u-(t/4)*exponential_moment 2 u) 0 b).
  { exact (@ex_RInt_minus R_NormedModule (exponential_moment 0)
      (fun u => (t/4)*exponential_moment 2 u) 0 b (Moment 0%nat) Scaled). }
  assert (Integral : RInt (fun u => exponential_moment 0 u-(t/4)*exponential_moment 2 u) 0 b=
      RInt (exponential_moment 0) 0 b-(t/4)*RInt (exponential_moment 2) 0 b).
  { pose proof (@RInt_minus R_CompleteNormedModule (exponential_moment 0)
      (fun u => (t/4)*exponential_moment 2 u) 0 b (Moment 0%nat) Scaled) as Minus.
    pose proof (@RInt_scal R_CompleteNormedModule (exponential_moment 2) 0 b (t/4) (Moment 2%nat)) as Scale.
    change (RInt (fun u => exponential_moment 0 u-(t/4)*exponential_moment 2 u) 0 b=
      RInt (exponential_moment 0) 0 b-RInt (fun u => (t/4)*exponential_moment 2 u) 0 b) in Minus.
    change (RInt (fun u => (t/4)*exponential_moment 2 u) 0 b=(t/4)*RInt (exponential_moment 2) 0 b) in Scale.
    rewrite Scale in Minus. exact Minus. }
  rewrite <- Integral. apply RInt_le; [exact B | exact Low | apply tail_integrand_integrable | ].
  intros u U. apply tail_integrand_first_order.
Qed.

Theorem tail_integral_correction t : 0<=t -> 0<=1-tail_integral t<=t/2.
Proof.
  intros T. destruct (tail_integral_limit t T) as [Limit Range].
  assert (First : is_lim_seq
      (fun k => RInt (exponential_moment 0) 0 (INR k)-(t/4)*RInt (exponential_moment 2) 0 (INR k))
      (1-t/2)).
  { replace (1-t/2) with (INR(fact 0)-(t/4)*INR(fact 2)) by (simpl; field).
    apply is_lim_seq_minus'; [apply exponential_moment_integral_limit | ].
    apply is_lim_seq_mult'; [apply is_lim_seq_const | apply exponential_moment_integral_limit]. }
  pose proof (is_lim_seq_le _ _ _ _ (fun k => tail_integral_first_order_partial t (INR k) (pos_INR k))
    First Limit) as Lower.
  change (1-t/2<=tail_integral t) in Lower. lra.
Qed.
