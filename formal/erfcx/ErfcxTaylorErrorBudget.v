(** Integer majorants for propagation of coefficient errors. The unit is
    chosen separately from this recurrence by the Q256 arithmetic proof. *)
From Coq Require Import Reals ZArith Lia Lra List Bool.
Require Import ErfcxGaussianBox.
Import ListNotations.
Open Scope R_scope.
Fixpoint taylor_error_budget n : Z*Z :=
  match n with
  | O => (1,1)%Z
  | S k => let '(prev,cur):=taylor_error_budget k in
      (cur,((32*cur+2*prev)/Z.of_nat(S(S k))+2)%Z)
  end.
Definition budget_check n := let '(a,b):=taylor_error_budget n in
  (0<?a)%Z && (0<?b)%Z && (a<=?2^40)%Z && (b<=?2^40)%Z.
Lemma budgets_checked : forallb budget_check (seq 0 100)=true.
Proof. vm_compute; reflexivity. Qed.
Lemma taylor_error_budget_range n : (n<100)%nat ->
  (0<fst(taylor_error_budget n)<=2^40 /\ 0<snd(taylor_error_budget n)<=2^40)%Z.
Proof.
  intros N. pose proof budgets_checked as B.
  apply forallb_forall with (x:=n) in B; [|apply in_seq;lia].
  unfold budget_check in B. destruct(taylor_error_budget n) as [a b]; cbn [fst snd].
  repeat rewrite andb_true_iff in B. repeat rewrite Z.ltb_lt in B. repeat rewrite Z.leb_le in B. lia.
Qed.
Lemma taylor_error_budget_next n : fst(taylor_error_budget (S n))=snd(taylor_error_budget n).
Proof. cbn [taylor_error_budget]. destruct(taylor_error_budget n); reflexivity. Qed.
Lemma taylor_error_budget_step n :
  (32*IZR(snd(taylor_error_budget n))+2*IZR(fst(taylor_error_budget n)))/INR(S(S n))+1<=
    IZR(snd(taylor_error_budget (S n))).
Proof.
  cbn [taylor_error_budget]. destruct(taylor_error_budget n) as [prev cur]. cbn [fst snd].
  pose proof (integer_division_bounds (32*cur+2*prev) (Z.of_nat(S(S n))) ltac:(lia)) as Bound.
  rewrite !plus_IZR,!mult_IZR,<- INR_IZR_INZ in Bound.
  rewrite plus_IZR. lra.
Qed.
