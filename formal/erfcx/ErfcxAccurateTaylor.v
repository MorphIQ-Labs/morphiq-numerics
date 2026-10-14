(** The accurate Taylor series with both termination conditions. *)
From Coq Require Import Reals ZArith Lia Lra List Bool.
From Flocq Require Import Core.
From Q Require Import Q256 Q256Real.
Require Import StageGappa ErfcxGaussianTarget ErfcxTaylorRemainder ErfcxTaylorStopped
  ErfcxAccurateCenterModel ErfcxAccurateCenterBounds ErfcxAccurateTaylorTerms
  ErfcxAccurateTaylorSum ErfcxAccurateTaylorLoop.
Import ListNotations.
Open Scope R_scope.
Lemma center_top_checked : forallb (fun i => (top(q_center i)<=?1)%Z) (seq 0 177)=true.
Proof. vm_compute;reflexivity. Qed.
Lemma center_top_bound i : (i<177)%nat -> (top(q_center i)<=1)%Z.
Proof.
  intros I. pose proof center_top_checked as C.
  apply forallb_forall with (x:=i) in C; [|apply in_seq;lia]. apply Z.leb_le;exact C.
Qed.
Lemma q_taylor_small_term c i h n : valid c -> valid h -> (i<177)%nat ->
  qval c=accurate_center i -> Rabs(qval h)<=/8 -> (n<=98)%nat ->
  q_taylor_small i (q_taylor_term c i h n)=true ->
  Rabs(exact_taylor_term (accurate_center i) (qval h) (S n))<=bpow radix2 (-134).
Proof.
  intros C H I Cv Hr N Small.
  destruct(q_taylor_term_error c i h n C H I Cv Hr N) as [T [_ Error]].
  unfold q_taylor_small in Small. apply Z.ltb_lt in Small.
  pose proof(center_top_bound i I) as Center.
  pose proof(top_small _ (-261) T ltac:(lia)) as Tiny.
  replace (exact_taylor_term (accurate_center i)(qval h)(S n)) with
    ((exact_taylor_term (accurate_center i)(qval h)(S n)-qval(q_taylor_term c i h n))+
      qval(q_taylor_term c i h n)) by ring.
  eapply Rle_trans; [apply Rabs_triang|]. rewrite Rabs_minus_sym. bpow_num_all;lra.
Qed.

Theorem q_taylor_series_error c i h : valid c -> valid h -> (i<177)%nat ->
  qval c=accurate_center i -> Rabs(qval h)<=/8 ->
  valid(q_taylor_series c i h) /\
  Rabs(qval(q_taylor_series c i h)-gaussian_erfcx(accurate_center i+qval h))<=bpow radix2 (-124).
Proof.
  intros C H I Cv Hr. destruct(q_taylor_series_prefix c i h) as [j [J [Value Stop]]].
  rewrite Value. destruct(q_taylor_sum_error c i h j C H I Cv Hr ltac:(lia)) as [Valid _].
  split; [exact Valid|].
  pose proof(q_taylor_prefix_error c i h j C H I Cv Hr ltac:(lia)) as Eval.
  pose proof(table_taylor_cap_remainder i (qval h) I Hr) as Cap.
  assert (Tail : Rabs(taylor_polynomial 99 (accurate_center i)(qval h)-
    taylor_polynomial j (accurate_center i)(qval h))<=bpow radix2 (-125)).
  { destruct Stop as [End|[J3 [Previous Current]]].
    - rewrite End,Rminus_diag_eq,Rabs_R0 by reflexivity. apply bpow_ge_0.
    - destruct(accurate_center_bounds i I) as [Cr Fr].
      pose proof(q_taylor_small_term c i h (j-2) C H I Cv Hr ltac:(lia) Previous) as P.
      pose proof(q_taylor_small_term c i h (j-1) C H I Cv Hr ltac:(lia) Current) as U.
      replace (S(j-2)) with (j-1)%nat in P by lia. replace (S(j-1)) with j in U by lia.
      apply taylor_stopped_remainder; [exact Cr|exact Hr|lia|exact P|exact U]. }
  replace (qval(q_taylor_sum c i h j)-gaussian_erfcx(accurate_center i+qval h)) with
    ((qval(q_taylor_sum c i h j)-taylor_polynomial j (accurate_center i)(qval h))+
     (taylor_polynomial j (accurate_center i)(qval h)-taylor_polynomial 99 (accurate_center i)(qval h))+
     (taylor_polynomial 99 (accurate_center i)(qval h)-gaussian_erfcx(accurate_center i+qval h))) by ring.
  eapply Rle_trans; [apply Rabs_triang|].
  pose proof(Rabs_triang
    (qval(q_taylor_sum c i h j)-taylor_polynomial j (accurate_center i)(qval h))
    (taylor_polynomial j (accurate_center i)(qval h)-taylor_polynomial 99 (accurate_center i)(qval h))) as Add.
  rewrite Rabs_minus_sym in Tail,Cap. bpow_num_all;lra.
Qed.
