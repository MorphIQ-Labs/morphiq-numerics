(** The accurate reflected exponential's 24-level Q256 Horner evaluation. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Q Require Import Q256 Q256Real.
Require Import StageGappa ErfcxAccurateTerms ErfcxAccurateConstants.
Open Scope R_scope.

Fixpoint q_exp_horner r count :=
  match count with
  | O => q_one
  | S previous => add q_one
      (mul (mul r (q_reciprocal (24-S previous))) (q_exp_horner r previous))
  end.
Fixpoint exp_horner r count : R :=
  match count with
  | O => 1
  | S previous => 1+r/INR (25-S previous)*exp_horner r previous
  end.

Lemma exp_horner_range r count : Rabs r<=/256 -> (count<=24)%nat ->
  0.99<=exp_horner r count<=1.01.
Proof.
  intros R. induction count as [|count IH]; intros Count; [cbn [exp_horner]; lra | ].
  specialize (IH ltac:(lia)). cbn [exp_horner].
  assert (D : 1<=INR (25-S count)).
  { change 1 with (INR 1). apply le_INR. lia. }
  assert (V : 0</INR (25-S count)<=1).
  { split; [apply Rinv_0_lt_compat; lra | rewrite <- Rinv_1; apply Rinv_le_contravar; lra]. }
  apply Rabs_le_inv in R. unfold Rdiv. split; interval with (i_prec 80).
Qed.

Lemma exp_horner_product_range r v x e k a b :
  Rabs r<=/256 -> 0<=v<=1 -> 0.99<=x<=1.01 ->
  Rabs e<=bpow radix2 (-252) -> Rabs k<=bpow radix2 (-255) ->
  Rabs a<=bpow radix2 (-255) -> Rabs b<=bpow radix2 (-255) ->
  Rabs (r*v*(1+k)*(1+a)*(x+e)*(1+b))<=1.
Proof.
  intros R V X E K A B. apply Rabs_le_inv in R,E,K,A,B.
  bpow_num_all. apply Rabs_le; split; interval with (i_prec 300).
Qed.

Lemma exp_horner_step_error r v x e k a b s :
  Rabs r<=/256 -> 0<=v<=1 -> 0.99<=x<=1.01 ->
  Rabs e<=bpow radix2 (-252) -> Rabs k<=bpow radix2 (-255) ->
  Rabs a<=bpow radix2 (-255) -> Rabs b<=bpow radix2 (-255) ->
  Rabs s<=bpow radix2 (-254) ->
  Rabs (1+r*v*(1+k)*(1+a)*(x+e)*(1+b)+s-(1+r*v*x))<=bpow radix2 (-252).
Proof.
  intros R V X E K A B S. apply Rabs_le_inv in R,E,K,A,B,S.
  replace (1+r*v*(1+k)*(1+a)*(x+e)*(1+b)+s-(1+r*v*x)) with
    (r*v*(e+(x+e)*(k+(1+k)*(a+(1+a)*b)))+s) by ring.
  bpow_num_all. apply Rabs_le; split; interval with (i_prec 300).
Qed.

Theorem q_exp_horner_error r count : valid r -> Rabs (qval r)<=/256 -> (count<=24)%nat ->
  valid (q_exp_horner r count) /\
  Rabs (qval (q_exp_horner r count)-exp_horner (qval r) count)<=bpow radix2 (-252).
Proof.
  intros R Rrange. induction count as [|count IH]; intros Count.
  - cbn [q_exp_horner exp_horner]. destruct q_one_ok as [Q V].
    split; [exact Q | rewrite V,Rminus_diag_eq,Rabs_R0 by reflexivity; apply bpow_ge_0].
  - destruct (IH ltac:(lia)) as [H E].
    destruct (q_reciprocal_ok (24-S count) ltac:(lia)) as [C Cerror].
    replace (S (24-S count)) with (25-S count)%nat in Cerror by lia.
    set (d := INR (25-S count)) in *.
    assert (D : 1<=d) by (unfold d; change 1 with (INR 1); apply le_INR; lia).
    assert (V : 0<=/d<=1).
    { split; [apply Rlt_le,Rinv_0_lt_compat; lra | rewrite <- Rinv_1; apply Rinv_le_contravar; lra]. }
    set (k := qval (q_reciprocal (24-S count))*d-1) in *.
    assert (Cvalue : qval (q_reciprocal (24-S count))=(/d)*(1+k)) by (unfold k; field; lra).
    destruct (mul_relative _ _ R C) as [P [a [A Pvalue]]].
    destruct (mul_relative _ _ P H) as [M [b [Berr Mvalue]]].
    destruct q_one_ok as [One Onevalue].
    destruct (add_any _ _ One M) as [Result Error].
    set (x := exp_horner (qval r) count) in *.
    set (e := qval (q_exp_horner r count)-x) in *.
    assert (Hvalue : qval (q_exp_horner r count)=x+e) by (unfold e; ring).
    assert (X : 0.99<=x<=1.01) by (apply exp_horner_range; [exact Rrange | lia]).
    assert (Value : qval (mul (mul r (q_reciprocal (24-S count))) (q_exp_horner r count))=
      qval r*(/d)*(1+k)*(1+a)*(x+e)*(1+b)).
    { rewrite Mvalue,Pvalue,Cvalue,Hvalue. ring. }
    assert (Magnitude : Rabs (qval (mul (mul r (q_reciprocal (24-S count))) (q_exp_horner r count)))<=1).
    { rewrite Value. apply exp_horner_product_range; assumption. }
    rewrite Onevalue,Rabs_R1,Rmax_left in Error by exact Magnitude.
    set (s := qval (add q_one (mul (mul r (q_reciprocal (24-S count))) (q_exp_horner r count)))-
      (1+qval (mul (mul r (q_reciprocal (24-S count))) (q_exp_horner r count)))) in *.
    cbn [q_exp_horner exp_horner]. fold d x. split; [exact Result | ].
    replace (qval (add q_one (mul (mul r (q_reciprocal (24-S count))) (q_exp_horner r count)))-
      (1+qval r/d*x)) with
      (1+qval r*(/d)*(1+k)*(1+a)*(x+e)*(1+b)+s-(1+qval r*(/d)*x))
      by (unfold s; rewrite Value; unfold Rdiv; ring).
    apply exp_horner_step_error; try assumption. lra.
Qed.
