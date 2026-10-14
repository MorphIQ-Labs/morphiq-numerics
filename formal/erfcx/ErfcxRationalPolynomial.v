(** Exact rational lists checked by the ODE recurrence. *)
From Coq Require Import Reals ZArith Lia Lra List Bool QArith Qreals Qreduction.
Require Import ErfcxRationalTaylor.
Import ListNotations.
Open Scope R_scope.
Definition rat_at cs n := nth n cs (0%Q).
Definition rat_step c p u n := ((2*c*u+2*p)/inject_Z(Z.of_nat(S(S n))))%Q.
Definition rat_recurrence_check c a0 a1 cs :=
  Qeq_bool (rat_at cs 0) a0 && Qeq_bool (rat_at cs 1) a1 &&
  forallb (fun n=>Qeq_bool (rat_at cs (S(S n)))
    (rat_step c (rat_at cs n) (rat_at cs (S n)) n)) (seq 0 47).
Lemma q2r_integer z : Q2R(inject_Z z)=IZR z.
Proof. unfold Q2R,inject_Z;cbn [Qnum Qden];field. Qed.
Lemma rat_step_real c p u n : Q2R(rat_step c p u n)=
  (2*Q2R c*Q2R u+2*Q2R p)/INR(S(S n)).
Proof.
  unfold rat_step. rewrite Q2R_div.
  - rewrite Q2R_plus,!Q2R_mult,q2r_integer,<- INR_IZR_INZ.
    change (Q2R 2) with (2/1);field;apply not_0_INR;lia.
  - intro Z. apply Qeq_eqR in Z. rewrite q2r_integer in Z.
    change (Q2R 0) with (0/1) in Z.
    assert (0<IZR(Z.of_nat(S(S n)))) by (apply IZR_lt;lia). lra.
Qed.
Theorem rat_recurrence_correct c a0 a1 cs n : rat_recurrence_check c a0 a1 cs=true ->
  (n<=47)%nat ->
  Q2R(rat_at cs n)=fst(real_taylor_pair (Q2R c)(Q2R a0)(Q2R a1)n) /\
  Q2R(rat_at cs (S n))=snd(real_taylor_pair (Q2R c)(Q2R a0)(Q2R a1)n).
Proof.
  intros Check. unfold rat_recurrence_check in Check.
  repeat rewrite andb_true_iff in Check. destruct Check as [[A0 A1] Steps].
  apply Qeq_bool_eq,Qeq_eqR in A0,A1.
  induction n as [|n IH];intros N.
  - cbn [real_taylor_pair fst snd];split;assumption.
  - destruct(IH ltac:(lia)) as [P U].
    assert (Step : Q2R(rat_at cs(S(S n)))=Q2R(rat_step c (rat_at cs n)(rat_at cs(S n)) n)).
    { apply Qeq_eqR,Qeq_bool_eq. apply forallb_forall with(x:=n) in Steps;[exact Steps|apply in_seq;lia]. }
    rewrite rat_step_real,P,U in Step.
    cbn [real_taylor_pair]. destruct(real_taylor_pair (Q2R c)(Q2R a0)(Q2R a1)n) as [p u].
    cbn [fst snd] in P,U,Step |- *;split;assumption.
Qed.
Fixpoint rat_horner h cs : R :=
  match cs with []=>0 | a::rest=>Q2R a+h*rat_horner h rest end.
Lemma rat_horner_sum h cs n : length cs=S n ->
  rat_horner h cs=sum_f_R0(fun k=>Q2R(rat_at cs k)*h^k)n.
Proof.
  revert cs. induction n as [|n IH];intros cs Len.
  - destruct cs as [|a rest];[discriminate|]. destruct rest;[|discriminate].
    cbn [rat_horner sum_f_R0 rat_at nth pow];ring.
  - destruct cs as [|a rest];[discriminate|].
    cbn [length] in Len. cbn [rat_horner]. rewrite (IH rest ltac:(lia)).
    rewrite (decomp_sum (fun k=>Q2R(rat_at(a::rest)k)*h^k) (S n) ltac:(lia)). cbn [Nat.pred rat_at nth pow].
    rewrite scal_sum,Rmult_1_r. f_equal. apply sum_eq. intros k K;cbn [pow];unfold rat_at;ring.
Qed.
Theorem rat_horner_taylor c a0 a1 cs h : rat_recurrence_check c a0 a1 cs=true ->
  length cs=49%nat ->
  rat_horner h cs=real_taylor_polynomial 48 (Q2R c)(Q2R a0)(Q2R a1)h.
Proof.
  intros Check Len. rewrite (rat_horner_sum h cs 48 Len).
  unfold real_taylor_polynomial. apply sum_eq. intros k K.
  destruct k as [|k].
  - rewrite (proj1(rat_recurrence_correct c a0 a1 cs 0 Check ltac:(lia)));reflexivity.
  - rewrite real_taylor_pair_next.
    rewrite (proj2(rat_recurrence_correct c a0 a1 cs k Check ltac:(lia)));reflexivity.
Qed.
Definition rat_difference cs ds := map (fun ab=>Qred(fst ab-snd ab)%Q) (combine cs ds).
Lemma q2r_red q : Q2R(Qred q)=Q2R q.
Proof. apply Qeq_eqR,Qred_correct. Qed.
Lemma rat_horner_difference h cs ds : length cs=length ds ->
  rat_horner h (rat_difference cs ds)=rat_horner h cs-rat_horner h ds.
Proof.
  revert ds. induction cs as [|c cs IH];intros ds Len;destruct ds as [|d ds];try discriminate.
  - cbn [rat_difference combine map rat_horner];ring.
  - cbn [length] in Len. unfold rat_difference;cbn [combine map fst snd rat_horner].
    fold(rat_difference cs ds). rewrite q2r_red,Q2R_minus,IH by lia;ring.
Qed.
