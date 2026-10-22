(** [asin] is [1.092]-Lipschitz on [[0, 0.4]], the range of the complement's
    [sqrt ((1 - x)/2)] (at most [0.3827]): the mean value theorem with
    [asin' = 1/sqrt (1 - x^2)]. *)
From Coq Require Import Reals ZArith Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
Require Import AsinWithin.
Open Scope R_scope.

Lemma asin_step_wide a b : 0 <= a -> a < b -> b <= 0.4 ->
  exists xi, a <= xi <= b /\ asin b - asin a = (b - a) * (1 / sqrt (1 - xi * xi)).
Proof.
  intros Ha Hab Hb.
  assert (Hd : forall c, a <= c <= b -> derivable_pt_lim asin c (1 / sqrt (1 - c * c))).
  { intros c Hc. assert (Hr : -1 < c < 1) by lra.
    pose proof (derive_pt_asin c Hr) as E.
    apply (derive_pt_eq_1 asin c _ (derivable_pt_asin c Hr)). rewrite E. unfold Rsqr. reflexivity. }
  destruct (MVT_cor2 asin (fun c => 1 / sqrt (1 - c * c)) a b Hab Hd) as [xi [E Hxi]].
  exists xi. cbv beta in E. split; [split; lra | rewrite E; ring].
Qed.

Lemma inv_sqrt_wide s : 0 <= s <= 0.16 -> 1 <= 1 / sqrt (1 - s) <= 1.092.
Proof.
  intros [H0 H1].
  assert (P : 0 < sqrt (1 - s)) by (apply sqrt_lt_R0; lra).
  assert (U : sqrt (1 - s) <= 1) by (pose proof (sqrt_le_1_alt (1 - s) 1 ltac:(lra)) as U0; rewrite sqrt_1 in U0; exact U0).
  assert (Lo : 0.9158 <= sqrt (1 - s)).
  { rewrite <- (sqrt_Rsqr 0.9158) by lra. apply sqrt_le_1_alt. unfold Rsqr. nra. }
  split.
  - unfold Rdiv. rewrite Rmult_1_l. apply Rle_trans with (/ 1); [lra | apply Rinv_le_contravar; lra].
  - unfold Rdiv. rewrite Rmult_1_l. apply Rle_trans with (/ 0.9158); [apply Rinv_le_contravar; lra | ].
    apply Rmult_le_reg_r with 0.9158; [lra | ]. rewrite Rinv_l by lra. lra.
Qed.

Lemma asin_lip a b : 0 <= a -> a <= b -> b <= 0.4 -> asin b - asin a <= 1.092 * (b - a).
Proof.
  intros Ha Hab Hb. destruct (Req_dec a b) as [E | N]; [subst; lra | ].
  destruct (asin_step_wide a b Ha ltac:(lra) Hb) as [xi [Hxi E]].
  assert (Hs : 0 <= xi * xi <= 0.16) by (split; nra).
  pose proof (inv_sqrt_wide (xi * xi) Hs) as [G1 G2].
  rewrite E. set (g := 1 / sqrt (1 - xi * xi)) in *. nra.
Qed.

Lemma asin_close a b : 0 <= a -> 0 <= b -> a <= 0.4 -> b <= 0.4 -> Rabs (asin a - asin b) <= 1.092 * Rabs (a - b).
Proof.
  intros Ha Hb Ha4 Hb4.
  destruct (Rle_dec a b) as [H | H].
  - pose proof (asin_lip a b Ha H Hb4). pose proof (asin_nonneg a ltac:(split; lra)). 
    assert (asin a <= asin b).
    { destruct (Req_dec a b) as [E | N]; [subst; lra | ].
      destruct (asin_step_wide a b Ha ltac:(lra) Hb4) as [xi [Hxi E]].
      assert (Hs : 0 <= xi * xi <= 0.16) by (split; nra).
      pose proof (inv_sqrt_wide (xi * xi) Hs) as [G1 G2].
      assert (0 <= (b - a) * (1 / sqrt (1 - xi * xi))) by (apply Rmult_le_pos; lra). lra. }
    rewrite Rabs_left1 by lra. rewrite (Rabs_left1 (a - b)) by lra. lra.
  - assert (Hba : b <= a) by lra.
    pose proof (asin_lip b a Hb Hba Ha4). pose proof (asin_nonneg b ltac:(split; lra)).
    assert (asin b <= asin a).
    { destruct (Req_dec a b) as [E | N]; [subst; lra | ].
      destruct (asin_step_wide b a Hb ltac:(lra) Ha4) as [xi [Hxi E]].
      assert (Hs : 0 <= xi * xi <= 0.16) by (split; nra).
      pose proof (inv_sqrt_wide (xi * xi) Hs) as [G1 G2].
      assert (0 <= (a - b) * (1 / sqrt (1 - xi * xi))) by (apply Rmult_le_pos; lra). lra. }
    rewrite Rabs_right by lra. rewrite (Rabs_right (a - b)) by lra. lra.
Qed.
