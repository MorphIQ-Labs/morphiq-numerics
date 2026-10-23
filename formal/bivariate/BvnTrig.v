(** Elementary trigonometric facts for the node angles, which stay below
    [6/5 < pi/2]. *)
From Coq Require Import Reals Lra Psatz.
From Interval Require Import Tactic.
Require Import BvnRound.
Open Scope R_scope.

Lemma sin_ge_half x : 0 <= x <= 1 -> x / 2 <= sin x.
Proof.
  intros [H0 H1].
  pose proof (sin_bound x 0 H0 ltac:(pose proof PI_RGT_0; interval)) as [Hl _].
  simpl in Hl. unfold sin_term in Hl. simpl in Hl.
  assert (E : sin_approx x 1 = x - x * x * x / 6).
  { unfold sin_approx. simpl. unfold sin_term. simpl. field. }
  rewrite E in Hl.
  assert (Hxx : x * x <= 1) by nra.
  assert (Hx3 : x * x * x <= x) by nra.
  nra.
Qed.

Lemma PI_gt_3 : 3 < PI.
Proof. pose proof PI_RGT_0. interval. Qed.

Lemma PI2_gt : 15 / 10 < PI / 2.
Proof. interval. Qed.

(** [|sin t| < 1] below [pi/2]. *)
Lemma sin_abs_lt_1 t : Rabs t <= 3 / 2 -> Rabs (sin t) < 1.
Proof.
  intros H. apply Rabs_le_between in H. destruct H as [H1 H2].
  pose proof PI2_gt as Hp.
  assert (Hc : 0 < cos t) by (apply cos_gt_0; lra).
  pose proof (sin2_cos2 t) as E. unfold Rsqr in E.
  apply Rabs_lt_between. nra.
Qed.

Lemma cos_lb x : Rabs x <= 6 / 5 -> 3 / 10 <= cos x.
Proof.
  intros H.
  assert (Hc : cos x = cos (Rabs x)).
  { destruct (Rcase_abs x) as [Hn | Hp].
    - rewrite (Rabs_left x Hn), cos_neg. reflexivity.
    - rewrite (Rabs_right x Hp). reflexivity. }
  rewrite Hc. set (y := Rabs x) in *.
  assert (Hy0 : 0 <= y) by apply Rabs_pos.
  interval with (i_bisect y).
Qed.

Lemma sin_mono_pos a b : 0 <= a -> a <= b -> b <= 3 / 2 -> sin a <= sin b.
Proof.
  intros Ha Hab Hb. pose proof PI2_gt as Hp.
  apply sin_incr_1; lra.
Qed.

(** [|sin th| = sin |th|] for [|th| <= 3/2]. *)
Lemma abs_sin_eq th : Rabs th <= 3 / 2 -> Rabs (sin th) = sin (Rabs th).
Proof.
  intros H. pose proof PI2_gt as Hp.
  apply Rabs_le_between in H. destruct H as [H1 H2].
  destruct (Rcase_abs th) as [Hn | Hpos].
  - rewrite (Rabs_left th Hn). rewrite sin_neg.
    assert (H0 : 0 <= sin (- th)) by (apply sin_ge_0; lra).
    rewrite sin_neg in H0.
    apply Rabs_left1. lra.
  - rewrite (Rabs_right th Hpos). rewrite Rabs_right; [reflexivity |].
    apply Rle_ge. apply sin_ge_0; lra.
Qed.

(** [|sin|] of a perturbed angle. *)
Lemma sin_abs_le a d : 0 <= a -> a + d <= 3 / 2 -> 0 <= d ->
  forall th, Rabs (th - a) <= d -> Rabs (sin th) <= sin (a + d).
Proof.
  intros Ha Had Hd th Hth.
  assert (Hab : Rabs th <= a + d).
  { assert (E : th = a + (th - a)) by ring.
    assert (Rabs th <= Rabs a + Rabs (th - a)) by (rewrite E at 1; apply Rabs_triang).
    rewrite (Rabs_pos_eq a Ha) in H. lra. }
  rewrite abs_sin_eq by lra.
  apply sin_mono_pos; [apply Rabs_pos | exact Hab | lra].
Qed.
