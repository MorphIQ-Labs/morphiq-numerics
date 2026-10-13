(** Newton refinement in actual Q256 arithmetic, including zero residuals. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Q Require Import Q256 Q256Real.
Require Import StageGappa ErfcxAccurateTerms.
Open Scope R_scope.

Definition q_newton x y :=
  let p := mul x y in
  let g := add q_one (neg_q p) in
  add y (mul y g).

Lemma newton_real_error e a b s1 s2 : Rabs e<=bpow radix2 (-50) ->
  Rabs a<=bpow radix2 (-255) -> Rabs b<=bpow radix2 (-255) ->
  Rabs s1<=3*bpow radix2 (-255) -> Rabs s2<=2*bpow radix2 (-255) ->
  Rabs ((1+e)*(1+(1-(1+e)*(1+a)+s1)*(1+b)+s2)-1)<=e*e+7*bpow radix2 (-255).
Proof.
  intros E A B S1 S2. apply Rabs_le_inv in E,A,B,S1,S2.
  assert (Corrected : Rabs (((1+e)*(1+(1-(1+e)*(1+a)+s1)*(1+b)+s2)-1)+e*e)<=7*bpow radix2 (-255)).
  { replace (((1+e)*(1+(1-(1+e)*(1+a)+s1)*(1+b)+s2)-1)+e*e) with
      (-e*b-e*e*b+(1+e)*(1+b)*(s1-(1+e)*a)+(1+e)*s2) by ring.
    bpow_num_all. apply Rabs_le; split; interval with (i_prec 300). }
  apply Rabs_le_inv in Corrected. apply Rabs_le; split; nra.
Qed.

Lemma newton_product_range e a : Rabs e<=bpow radix2 (-50) -> Rabs a<=bpow radix2 (-255) ->
  Rabs ((1+e)*(1+a))<=3/2.
Proof.
  intros E A. apply Rabs_le_inv in E,A. bpow_num_all.
  apply Rabs_le; split; interval with (i_prec 80).
Qed.

Lemma newton_residual_range e a s : Rabs e<=bpow radix2 (-50) -> Rabs a<=bpow radix2 (-255) ->
  Rabs s<=3*bpow radix2 (-255) -> Rabs (1-(1+e)*(1+a)+s)<=/2.
Proof.
  intros E A S. apply Rabs_le_inv in E,A,S. bpow_num_all.
  apply Rabs_le; split; interval with (i_prec 80).
Qed.

Theorem q_newton_error x y e : valid x -> valid y ->
  Rabs e<=bpow radix2 (-50) -> qval x*qval y=1+e ->
  valid (q_newton x y) /\ Rabs (qval x*qval (q_newton x y)-1)<=e*e+7*bpow radix2 (-255).
Proof.
  intros X Y E Exact. destruct q_one_ok as [One OneValue].
  destruct (mul_relative x y X Y) as [P [a [A PValue]]].
  rewrite Exact in PValue.
  destruct (neg_any _ P) as [Neg NegValue].
  destruct (add_any q_one _ One Neg) as [G GError].
  set (p := mul x y) in *. set (g := add q_one (neg_q p)) in *.
  rewrite OneValue,NegValue in GError.
  set (s1 := qval g-(1-qval p)).
  assert (S1 : Rabs s1<=3*bpow radix2 (-255)).
  { unfold s1. replace (1-qval p) with (1+-qval p) by ring.
    eapply Rle_trans; [exact GError | ]. rewrite Rabs_R1,Rabs_Ropp,PValue.
    pose proof (newton_product_range e a E A) as Range.
    replace (3*bpow radix2 (-255)) with (bpow radix2 (-254)*(3/2))
      by (bpow_num; field).
    apply Rmult_le_compat_l; [apply bpow_ge_0 | apply Rmax_lub; lra]. }
  assert (GValue : qval g=1-(1+e)*(1+a)+s1) by (unfold s1; rewrite PValue; ring).
  assert (GSmall : Rabs (qval g)<=/2).
  { rewrite GValue. apply newton_residual_range; assumption. }
  destruct (mul_relative y g Y G) as [Q [b [B QValue]]].
  assert (QSmall : Rabs (qval (mul y g))<=Rabs (qval y)).
  { rewrite QValue,!Rabs_mult.
    assert (Factor : Rabs (1+b)<=2).
    { pose proof (Rabs_triang 1 b) as Triangle. rewrite Rabs_R1 in Triangle.
      assert (bpow radix2 (-255)<=1) by (change 1 with (bpow radix2 0); apply bpow_le; lia). lra. }
    assert (Product : Rabs (qval g)*Rabs (1+b)<=1).
    { apply Rle_trans with ((/2)*2); [apply Rmult_le_compat; try apply Rabs_pos; assumption | lra]. }
    rewrite Rmult_assoc. replace (Rabs (qval y)) with (Rabs (qval y)*1) at 2 by ring.
    apply Rmult_le_compat_l; [apply Rabs_pos | exact Product]. }
  destruct (add_any y (mul y g) Y Q) as [Result ResultError].
  assert (Ynonzero : qval y<>0).
  { intros Zero. rewrite Zero,Rmult_0_r in Exact.
    apply Rabs_le_inv in E. bpow_num_all. lra. }
  set (s2 := (qval (add y (mul y g))-(qval y+qval (mul y g)))/qval y).
  assert (S2 : Rabs s2<=2*bpow radix2 (-255)).
  { unfold s2,Rdiv. rewrite Rabs_mult,Rabs_Rinv by exact Ynonzero.
    assert (Yabs : 0<Rabs (qval y)) by (apply Rabs_pos_lt; exact Ynonzero).
    apply (Rmult_le_reg_r (Rabs (qval y))); [exact Yabs | ].
    rewrite Rmult_assoc,Rinv_l,Rmult_1_r by lra.
    rewrite Rmax_left in ResultError by exact QSmall.
    replace (2*bpow radix2 (-255)) with (bpow radix2 (-254)) by
      (change 2 with (bpow radix2 1); rewrite <- bpow_plus; reflexivity).
    exact ResultError. }
  assert (ResultValue : qval (add y (mul y g))=qval y*(1+qval g*(1+b)+s2)).
  { unfold s2. rewrite QValue. field. exact Ynonzero. }
  unfold q_newton. fold p g. split; [exact Result | ].
  rewrite ResultValue,GValue, <- Rmult_assoc,Exact.
  apply newton_real_error; assumption.
Qed.

Lemma newton_error_bounds e :
  (Rabs e<=bpow radix2 (-50) -> e*e+7*bpow radix2 (-255)<=bpow radix2 (-99)) /\
  (Rabs e<=bpow radix2 (-99) -> e*e+7*bpow radix2 (-255)<=bpow radix2 (-197)) /\
  (Rabs e<=bpow radix2 (-197) -> e*e+7*bpow radix2 (-255)<=bpow radix2 (-252)).
Proof.
  repeat split; intros E; apply Rabs_le_inv in E; bpow_num_all;
    interval with (i_prec 500).
Qed.

Definition q_refine3 x y := q_newton x (q_newton x (q_newton x y)).

Theorem q_refine3_error x y : valid x -> valid y ->
  Rabs (qval x*qval y-1)<=bpow radix2 (-50) ->
  valid (q_refine3 x y) /\
    Rabs (qval x*qval (q_refine3 x y)-1)<=bpow radix2 (-252).
Proof.
  intros X Y Seed.
  destruct (q_newton_error x y (qval x*qval y-1) X Y Seed ltac:(ring)) as [Y1 E1].
  assert (B1 : Rabs (qval x*qval (q_newton x y)-1)<=bpow radix2 (-99)).
  { eapply Rle_trans; [exact E1 | ]. apply (proj1 (newton_error_bounds _)); exact Seed. }
  assert (Small1 : Rabs (qval x*qval (q_newton x y)-1)<=bpow radix2 (-50)).
  { eapply Rle_trans; [exact B1 | apply bpow_le; lia]. }
  destruct (q_newton_error x (q_newton x y) _ X Y1 Small1 ltac:(ring)) as [Y2 E2].
  assert (B2 : Rabs (qval x*qval (q_newton x (q_newton x y))-1)<=bpow radix2 (-197)).
  { eapply Rle_trans; [exact E2 | ]. apply (proj1 (proj2 (newton_error_bounds _))); exact B1. }
  assert (Small2 : Rabs (qval x*qval (q_newton x (q_newton x y))-1)<=bpow radix2 (-50)).
  { eapply Rle_trans; [exact B2 | apply bpow_le; lia]. }
  destruct (q_newton_error x (q_newton x (q_newton x y)) _ X Y2 Small2 ltac:(ring)) as [Y3 E3].
  split; [exact Y3 | ]. eapply Rle_trans; [exact E3 | ].
  apply (proj2 (proj2 (newton_error_bounds _))); exact B2.
Qed.
