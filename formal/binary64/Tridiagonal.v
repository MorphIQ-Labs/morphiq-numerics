(** A posteriori error bound for a strictly row-dominant tridiagonal system.
    Coefficients outside the tridiagonal band are zero. The real residual
    enclosures are supplied by FiniteInterval's outward arithmetic lemmas.
    This is not a transcription of the floating-point Thomas recurrence. *)
From Coq Require Import Reals Lra Psatz Lia.
From Binary64 Require Import FiniteInterval.
Open Scope R_scope.

Theorem margin_step lower exact_row neighbour :
  lower <= exact_row -> down (lower - Rabs neighbour) <= exact_row - Rabs neighbour.
Proof.
  intro L. destruct (neighbour_enclosure (lower - Rabs neighbour)) as [D _]. lra.
Qed.

Lemma dominant_row d l u e el eu rho m :
  0 < m -> m <= Rabs d - Rabs l - Rabs u ->
  Rabs el <= Rabs e -> Rabs eu <= Rabs e ->
  Rabs (d*e + l*el + u*eu) <= rho -> Rabs e <= rho/m.
Proof.
  intros M D L U B.
  assert (T : Rabs (d*e) <=
    Rabs (d*e+l*el+u*eu) + Rabs (l*el) + Rabs (u*eu)).
  { replace (d*e) with ((d*e+l*el+u*eu) - l*el - u*eu) at 1 by ring.
    eapply Rle_trans; [apply Rabs_triang |].
    unfold Rminus. rewrite Rabs_Ropp.
    pose proof (Rabs_triang (d*e+l*el+u*eu) (- (l*el))).
    rewrite Rabs_Ropp in H. lra. }
  rewrite !Rabs_mult in T.
  pose proof (Rabs_pos l). pose proof (Rabs_pos u). pose proof (Rabs_pos e).
  assert (E : m * Rabs e <= rho) by nra.
  apply (Rmult_le_reg_r m); [exact M |].
  replace (rho / m * m) with rho by (field; lra). nra.
Qed.

Lemma finite_abs_max (e : nat -> R) n :
  (0 < n)%nat -> exists k, (k < n)%nat /\
    forall i, (i < n)%nat -> Rabs (e i) <= Rabs (e k).
Proof.
  induction n as [|n IH]; intros N; [lia |].
  destruct n as [|n].
  - exists 0%nat. split; [lia |]. intros i I. assert (i = 0)%nat by lia. subst. lra.
  - destruct (IH ltac:(lia)) as [k [K H]].
    destruct (Rle_dec (Rabs (e (S n))) (Rabs (e k))) as [LE | GT].
    + exists k. split; [lia |]. intros i I.
      destruct (Nat.eq_dec i (S n)); [subst; exact LE | apply H; lia].
    + exists (S n). split; [lia |]. intros i I.
      destruct (Nat.eq_dec i (S n)); [subst; lra |].
      specialize (H i ltac:(lia)). lra.
Qed.

Theorem tridiagonal_error_bound n (d l u e : nat -> R) rho m :
  0 < m ->
  (forall i, (n <= i)%nat -> e i = 0) ->
  (forall i, (i < n)%nat -> m <= Rabs (d i) - Rabs (l i) - Rabs (u i)) ->
  (forall i, (i < n)%nat ->
    Rabs (d i * e i + l i * e (i-1)%nat + u i * e (S i)) <= rho) ->
  forall i, (i < n)%nat -> Rabs (e i) <= rho/m.
Proof.
  intros M Z D B i I.
  destruct (finite_abs_max e n ltac:(lia)) as [k [K H]].
  assert (A : forall j, Rabs (e j) <= Rabs (e k)).
  { intros j. destruct (Nat.lt_ge_cases j n).
    - apply H; assumption.
    - rewrite Z by assumption. rewrite Rabs_R0. apply Rabs_pos. }
  eapply Rle_trans; [apply H; exact I |].
  eapply dominant_row; [exact M | apply D; exact K | apply A | apply A | apply B; exact K].
Qed.

Theorem tridiagonal_zero_kernel n (d l u e : nat -> R) m :
  0 < m ->
  (forall i, (n <= i)%nat -> e i = 0) ->
  (forall i, (i < n)%nat -> m <= Rabs (d i) - Rabs (l i) - Rabs (u i)) ->
  (forall i, (i < n)%nat -> d i * e i + l i * e (i-1)%nat + u i * e (S i) = 0) ->
  forall i, (i < n)%nat -> e i = 0.
Proof.
  intros M Z D B i I.
  assert (E : Rabs (e i) <= 0/m).
  { eapply tridiagonal_error_bound; eauto.
    intros j J. rewrite B by exact J. rewrite Rabs_R0. lra. }
  unfold Rdiv in E. rewrite Rmult_0_l in E.
  unfold Rabs in E. destruct (Rcase_abs (e i)); lra.
Qed.

Theorem rounded_error_bound error rho m :
  error <= rho/m -> error <= up (rho/m).
Proof.
  intro E. destruct (neighbour_enclosure (rho/m)) as [_ U]. lra.
Qed.
