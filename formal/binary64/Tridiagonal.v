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

(** Explicit opposite-sign-link domain. These lemmas model finite operations
    with gradual underflow; the Rust kernel refuses nonfinite intermediates. *)
From Flocq Require Import Core.
#[local] Instance sign_prec53 : Prec_gt_0 53 := eq_refl.

Lemma sign_rounded_zero : rn 0 = 0.
Proof. unfold rn. apply round_0. auto with typeclass_instances. Qed.

Lemma sign_rounded_monotone x y : x <= y -> rn x <= rn y.
Proof. unfold rn. intro H. apply round_le; auto with typeclass_instances. Qed.

Lemma sign_rounded_nonnegative x : 0 <= x -> 0 <= rn x.
Proof. intro H. rewrite <- sign_rounded_zero. now apply sign_rounded_monotone. Qed.

Lemma sign_rounded_nonpositive x : x <= 0 -> rn x <= 0.
Proof. intro H. rewrite <- sign_rounded_zero. now apply sign_rounded_monotone. Qed.

Theorem sign_normalized_product a c p :
  0 < p -> a*c <= 0 -> a * rn (c/p) <= 0.
Proof.
  intros P S. assert (I : 0 < /p) by (apply Rinv_0_lt_compat; exact P).
  destruct (Rle_dec 0 a) as [A|A]; destruct (Rle_dec 0 c) as [C|C].
  - assert (a = 0 \/ c = 0) by nra.
    destruct H as [H|H]; rewrite H; [nra|].
    unfold Rdiv. rewrite Rmult_0_l, sign_rounded_zero. nra.
  - assert (rn (c/p) <= 0) by (apply sign_rounded_nonpositive; unfold Rdiv; nra). nra.
  - assert (0 <= rn (c/p)) by (apply sign_rounded_nonnegative; unfold Rdiv; nra). nra.
  - nra.
Qed.

Theorem sign_rounded_pivot_step b a c p :
  0 < b -> rn b = b -> 0 < p -> a*c <= 0 ->
  b <= rn (b - rn (a * rn (c/p))).
Proof.
  intros B F P S.
  pose proof (sign_normalized_product a c p P S) as N.
  pose proof (sign_rounded_nonpositive _ N) as T.
  rewrite <- F at 1. apply sign_rounded_monotone. lra.
Qed.

Fixpoint sign_pivot (d l u : nat -> R) (n : nat) : R :=
  match n with
  | O => d O
  | S k => d (S k) - l k * (u k / sign_pivot d l u k)
  end.

Theorem sign_exact_pivots_positive d l u :
  (forall i, 0 < d i) -> (forall i, l i * u i <= 0) ->
  forall i, d i <= sign_pivot d l u i /\ 0 < sign_pivot d l u i.
Proof.
  intros D L i. induction i as [|i [B P]]; simpl; [split; [lra|apply D]|].
  assert (I : 0 < / sign_pivot d l u i) by (apply Rinv_0_lt_compat; exact P).
  pose proof (L i). pose proof (D (S i)). unfold Rdiv. split; nra.
Qed.

Fixpoint sign_rounded_pivot (d l u : nat -> R) (n : nat) : R :=
  match n with
  | O => d O
  | S k => rn (d (S k) - rn (l k * rn (u k / sign_rounded_pivot d l u k)))
  end.

Theorem sign_finite_pivots_positive d l u :
  (forall i, 0 < d i) -> (forall i, rn (d i) = d i) ->
  (forall i, l i * u i <= 0) ->
  forall i, d i <= sign_rounded_pivot d l u i /\ 0 < sign_rounded_pivot d l u i.
Proof.
  intros D F L i. induction i as [|i [B P]]; simpl; [split; [lra|apply D]|].
  pose proof (sign_rounded_pivot_step (d (S i)) (l i) (u i)
    (sign_rounded_pivot d l u i) (D (S i)) (F (S i)) P (L i)) as T.
  pose proof (D (S i)). split; lra.
Qed.

(** The continuant recurrence for leading tridiagonal determinants, with
    det(empty)=1 and det(singleton)=d[0]. *)
Fixpoint sign_continuant (d l u : nat -> R) (n : nat) : R :=
  match n with
  | O => 1
  | S k => match k with
           | O => d O
           | S j => d k * sign_continuant d l u k -
                    l j * u j * sign_continuant d l u j
           end
  end.

Theorem sign_continuants_positive d l u :
  (forall i, 0 < d i) -> (forall i, l i * u i <= 0) ->
  forall n, 0 < sign_continuant d l u n.
Proof.
  intros D L n.
  assert (H : forall k, 0 < sign_continuant d l u k /\
                         0 < sign_continuant d l u (S k)).
  { intro k. induction k as [|k [A B]].
    - simpl. split; [lra|apply D].
    - split; [exact B|].
      change (0 < d (S k) * sign_continuant d l u (S k) -
        l k * u k * sign_continuant d l u k).
      pose proof (D (S k)). pose proof (L k). nra. }
  exact (proj1 (H n)).
Qed.
