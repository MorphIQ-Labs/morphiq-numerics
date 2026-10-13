(** Two small consecutive exact terms bound every remaining term through
    degree 99; this does not assume a convergent infinite Taylor tail. *)
From Coq Require Import Reals Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
Require Import StageGappa ErfcxTaylorCoefficients ErfcxTaylorRemainder ErfcxAccurateTaylorTerms ErfcxAccurateTaylorSum.
Open Scope R_scope.
Lemma exact_taylor_term_step c h n :
  exact_taylor_term c h (S(S n))=
    (2*c*h*exact_taylor_term c h (S n)+2*h*h*exact_taylor_term c h n)/INR(S(S n)).
Proof.
  unfold exact_taylor_term. rewrite taylor_coefficient_step. cbn [pow]. unfold Rdiv;ring.
Qed.
Lemma exact_taylor_step_bound c h n m : Rabs c<=16 -> Rabs h<=/8 -> (2<=n)%nat ->
  Rabs(exact_taylor_term c h n)<=m -> Rabs(exact_taylor_term c h (S n))<=m ->
  Rabs(exact_taylor_term c h (S(S n)))<=(129/128)*m.
Proof.
  intros C H N P U.
  assert (M : 0<=m) by (pose proof(Rabs_pos(exact_taylor_term c h n));lra).
  assert (D : 4<=INR(S(S n))).
  { replace 4 with (INR 4) by (rewrite INR_IZR_INZ;reflexivity). apply le_INR;lia. }
  assert (Inv : 0</INR(S(S n))<=/4).
  { split; [apply Rinv_0_lt_compat;lra|apply Rinv_le_contravar;lra]. }
  rewrite exact_taylor_term_step. unfold Rdiv.
  rewrite Rabs_mult,(Rabs_pos_eq(/INR(S(S n)))) by lra.
  assert (Numerator : Rabs(2*c*h*exact_taylor_term c h (S n)+2*h*h*exact_taylor_term c h n)<=(4+/32)*m).
  { eapply Rle_trans; [apply Rabs_triang|]. rewrite !Rabs_mult,(Rabs_pos_eq 2) by lra.
    pose proof(Rabs_pos c);pose proof(Rabs_pos h).
    assert (A : 0<=2*Rabs c*Rabs h<=4) by nra.
    assert (B : 0<=2*Rabs h*Rabs h<=/32) by nra.
    pose proof(Rabs_pos(exact_taylor_term c h n));pose proof(Rabs_pos(exact_taylor_term c h (S n))). nra. }
  eapply Rle_trans with (((4+/32)*m)*(/4)); [|right;field].
  apply Rmult_le_compat; [apply Rabs_pos|lra|exact Numerator|exact(proj2 Inv)].
Qed.

Lemma exact_taylor_pair_bound c h n steps m : Rabs c<=16 -> Rabs h<=/8 -> (2<=n)%nat ->
  Rabs(exact_taylor_term c h n)<=m -> Rabs(exact_taylor_term c h (S n))<=m ->
  Rabs(exact_taylor_term c h (n+steps))<=m*(129/128)^steps /\
  Rabs(exact_taylor_term c h (S(n+steps)))<=m*(129/128)^steps.
Proof.
  intros C H N P U. induction steps as [|steps [Prev Cur]].
  - rewrite Nat.add_0_r. cbn [pow]. split;lra.
  - rewrite Nat.add_succ_r. split.
    + eapply Rle_trans; [exact Cur|]. cbn [pow].
      assert (M : 0<=m) by (pose proof(Rabs_pos(exact_taylor_term c h n));lra).
      assert (Power : 0<=(129/128)^steps) by (apply pow_le;lra). nra.
    + pose proof(exact_taylor_step_bound c h (n+steps) (m*(129/128)^steps) C H ltac:(lia) Prev Cur) as Next.
      cbn [pow]. nra.
Qed.

Lemma exact_taylor_following_bound c h j k m : Rabs c<=16 -> Rabs h<=/8 ->
  (3<=j /\ j<=k<=99)%nat -> Rabs(exact_taylor_term c h (j-1))<=m -> Rabs(exact_taylor_term c h j)<=m ->
  Rabs(exact_taylor_term c h k)<=3*m.
Proof.
  intros C H Range P U.
  assert (Base : S(j-1)=j) by lia.
  pose proof(exact_taylor_pair_bound c h (j-1) (k-j) m C H ltac:(lia) P ltac:(rewrite Base;exact U)) as [_ Bound].
  replace (S(j-1+(k-j))) with k in Bound by lia.
  assert (M : 0<=m) by (pose proof(Rabs_pos(exact_taylor_term c h j));lra).
  assert (Power : (129/128)^(k-j)<=3).
  { eapply Rle_trans; [apply Rle_pow with (n:=100%nat);[lra|lia]|]. interval with (i_prec 100). }
  eapply Rle_trans; [exact Bound|]. nra.
Qed.

Lemma taylor_sum_tail_bound c h start steps m :
  (forall k,(start<k<=start+steps)%nat -> Rabs(exact_taylor_term c h k)<=m) ->
  Rabs(taylor_polynomial (start+steps) c h-taylor_polynomial start c h)<=INR steps*m.
Proof.
  induction steps as [|steps IH]; intros Terms.
  - rewrite Nat.add_0_r,Rminus_diag_eq,Rabs_R0 by reflexivity. change (0<=0*m);lra.
  - specialize(IH ltac:(intros k K;apply Terms;lia)).
    rewrite Nat.add_succ_r,taylor_polynomial_next.
    replace (taylor_polynomial (start+steps) c h+exact_taylor_term c h (S(start+steps))-taylor_polynomial start c h) with
      ((taylor_polynomial (start+steps) c h-taylor_polynomial start c h)+exact_taylor_term c h (S(start+steps))) by ring.
    eapply Rle_trans; [apply Rabs_triang|].
    pose proof(Terms (S(start+steps)) ltac:(lia)). rewrite S_INR;nra.
Qed.

Theorem taylor_stopped_remainder c h j : Rabs c<=16 -> Rabs h<=/8 -> (3<=j<=99)%nat ->
  Rabs(exact_taylor_term c h (j-1))<=bpow radix2 (-134) ->
  Rabs(exact_taylor_term c h j)<=bpow radix2 (-134) ->
  Rabs(taylor_polynomial 99 c h-taylor_polynomial j c h)<=bpow radix2 (-125).
Proof.
  intros C H J P U.
  pose proof(taylor_sum_tail_bound c h j (99-j) (3*bpow radix2 (-134))) as Bound.
  replace (j+(99-j))%nat with 99%nat in Bound by lia.
  assert (Terms : forall k,(j<k<=99)%nat -> Rabs(exact_taylor_term c h k)<=3*bpow radix2 (-134)).
  { intros k K. exact(exact_taylor_following_bound c h j k (bpow radix2 (-134)) C H ltac:(lia) P U). }
  specialize(Bound Terms).
  assert (Count : INR(99-j)<=100).
  { replace 100 with (INR 100) by (rewrite INR_IZR_INZ;reflexivity). apply le_INR;lia. }
  bpow_num_all;nra.
Qed.
