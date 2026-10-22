(** Real-analysis facts for asinh, over Coq's [arcsinh = ln (x + sqrt (x^2 + 1))]:
    enclosure through [sinh] monotonicity, [arcsinh] against [x] and its cubic,
    the large-argument expansion, and the half-argument bound. *)
From Coq Require Import Reals ZArith Lra Psatz.
From Interval Require Import Tactic.
Open Scope R_scope.

(** [S - E <= arcsinh v <= S + E] from [sinh] at the two ends. *)
Lemma asinh_within v S E : sinh (S - E) - v <= 0 -> 0 <= sinh (S + E) - v -> Rabs (arcsinh v - S) <= E.
Proof.
  intros Hl Hu.
  assert (Hs : sinh (arcsinh v) = v) by apply sinh_arcsinh.
  assert (E0 : 0 <= E).
  { destruct (Rle_lt_dec 0 E) as [c | c]; [exact c | exfalso].
    pose proof (sinh_lt (S + E) (S - E) ltac:(lra)). lra. }
  apply Rabs_le. split.
  - destruct (Rle_lt_dec (S - E) (arcsinh v)) as [Hc | Hc]; [lra | exfalso].
    pose proof (sinh_lt _ _ Hc). lra.
  - destruct (Rle_lt_dec (arcsinh v) (S + E)) as [Hc | Hc]; [lra | exfalso].
    pose proof (sinh_lt _ _ Hc). lra.
Qed.

Lemma arcsinh_nonneg v : 0 <= v -> 0 <= arcsinh v.
Proof. intros H. rewrite <- arcsinh_0. apply arcsinh_le. exact H. Qed.

Lemma sqrt_sq1_pos x : 0 < sqrt (x ^ 2 + 1).
Proof. apply sqrt_lt_R0. pose proof (pow2_ge_0 x). lra. Qed.

(** From [f 0 = 0] and a nonnegative derivative on [[0, b]], [f >= 0] there. *)
Lemma nonneg_from_zero (f f' : R -> R) b :
  (forall x, derivable_pt_lim f x (f' x)) -> (forall x, 0 <= x <= b -> 0 <= f' x) -> f 0 = 0 ->
  forall x, 0 <= x <= b -> 0 <= f x.
Proof.
  intros D P F0 x Hx.
  assert (Dv : derivable f) by (intro t; exists (f' t); apply D).
  destruct (Req_dec x 0) as [-> | Hn]; [rewrite F0; lra | ].
  assert (Hb : 0 < b) by lra.
  assert (Hxp : 0 < x) by lra.
  pose proof (derive_increasing_interv_var 0 b f Dv Hb) as Inc.
  assert (Hmon : f 0 <= f x).
  { apply Inc; [ | lra | lra | lra].
    intros t Ht. rewrite (derive_pt_eq_0 f t (f' t) (Dv t) (D t)). apply P. lra. }
  lra.
Qed.

Lemma d_arcsinh x : derivable_pt_lim arcsinh x (/ sqrt (x ^ 2 + 1)).
Proof. apply derivable_pt_lim_arcsinh. Qed.

(** [arcsinh a <= a]. *)
Lemma arcsinh_le_id a : 0 <= a -> arcsinh a <= a.
Proof.
  intros Ha.
  set (f := fun x => x - arcsinh x). set (f' := fun x => 1 - / sqrt (x ^ 2 + 1)).
  assert (D : forall x, derivable_pt_lim f x (f' x)).
  { intro x. unfold f, f'. apply derivable_pt_lim_minus; [apply derivable_pt_lim_id | apply d_arcsinh]. }
  assert (P : forall x, 0 <= x <= a + 1 -> 0 <= f' x).
  { intros x _. unfold f'. pose proof (sqrt_sq1_pos x) as S0.
    assert (1 <= sqrt (x ^ 2 + 1)).
    { apply Rle_trans with (sqrt 1); [rewrite sqrt_1; lra | apply sqrt_le_1_alt; pose proof (pow2_ge_0 x); lra]. }
    assert (/ sqrt (x ^ 2 + 1) <= 1).
    { apply Rle_trans with (/ 1); [apply Rinv_le_contravar; lra | rewrite Rinv_1; lra]. }
    lra. }
  assert (F0 : f 0 = 0) by (unfold f; rewrite arcsinh_0; ring).
  pose proof (nonneg_from_zero f f' (a + 1) D P F0 a ltac:(lra)). unfold f in H. lra.
Qed.

(** [a - a^3/6 <= arcsinh a] on [[0, 1]]. *)
Lemma arcsinh_ge_cubic a : 0 <= a <= 1 -> a - a * a * a / 6 <= arcsinh a.
Proof.
  intros [Ha0 Ha1].
  set (f := fun x => arcsinh x - x + / 6 * x ^ 3). set (f' := fun x => / sqrt (x ^ 2 + 1) - 1 + x * x / 2).
  assert (D : forall x, derivable_pt_lim f x (f' x)).
  { intro x. unfold f, f'.
    pose proof (derivable_pt_lim_scal (fun y => y ^ 3) (/ 6) x _ (derivable_pt_lim_pow x 3)) as Dc.
    pose proof (derivable_pt_lim_minus arcsinh id x _ _ (d_arcsinh x) (derivable_pt_lim_id x)) as Dm.
    pose proof (derivable_pt_lim_plus _ _ x _ _ Dm Dc) as Dp.
    assert (Hp : x * x / 2 = / 6 * (INR 3 * x ^ Init.Nat.pred 3)) by (simpl; field).
    rewrite Hp. exact Dp. }
  assert (P : forall x, 0 <= x <= 1 -> 0 <= f' x).
  { intros x [X0 X1]. unfold f'. set (s := sqrt (x ^ 2 + 1)).
    pose proof (sqrt_sq1_pos x) as S0. fold s in S0.
    assert (S2 : s * s = x ^ 2 + 1) by (unfold s; apply sqrt_def; pose proof (pow2_ge_0 x); lra).
    assert (Hs1 : 1 <= s).
    { apply Rle_trans with (sqrt 1); [rewrite sqrt_1; lra | apply sqrt_le_1_alt; pose proof (pow2_ge_0 x); lra]. }
    assert (H : (3 - s * s) / 2 * s <= 1).
    { pose proof (Rmult_le_pos _ _ (pow2_ge_0 (s - 1)) (ltac:(lra) : 0 <= s + 2)) as Q. nra. }
    assert (Hi : (3 - s * s) / 2 <= / s).
    { apply Rmult_le_reg_r with s; [exact S0 | ]. rewrite Rinv_l by lra. exact H. }
    nra. }
  assert (F0 : f 0 = 0) by (unfold f; rewrite arcsinh_0; ring).
  pose proof (nonneg_from_zero f f' 1 D P F0 a ltac:(lra)). unfold f in H. lra.
Qed.

(** Pointwise equal functions have the same derivative. *)
Lemma dpl_ext f g x l : (forall y, f y = g y) -> derivable_pt_lim f x l -> derivable_pt_lim g x l.
Proof.
  intros E D eps Heps. destruct (D eps Heps) as [d Hd]. exists d. intros h H0 Hh.
  rewrite <- (E (x + h)), <- (E x). exact (Hd h H0 Hh).
Qed.

(** From [f 0 = 0] and a nonnegative derivative inside [(0, b)], [f >= 0] on [[0, b]];
    the derivative need only exist on [[0, b]]. *)
Lemma nonneg_mvt (f f' : R -> R) b :
  (forall c, 0 <= c <= b -> derivable_pt_lim f c (f' c)) -> (forall c, 0 < c < b -> 0 <= f' c) -> f 0 = 0 ->
  forall x, 0 <= x <= b -> 0 <= f x.
Proof.
  intros D P F0 x Hx.
  destruct (Req_dec x 0) as [-> | Hn]; [rewrite F0; lra | ].
  assert (Hxp : 0 < x) by lra.
  destruct (MVT_cor2 f f' 0 x Hxp (fun c Hc => D c ltac:(lra))) as [c [Hc E]].
  assert (0 <= f' c) by (apply P; lra).
  assert (0 <= f' c * (x - 0)) by (apply Rmult_le_pos; lra).
  lra.
Qed.

(** Derivative of [ln (1 + t)]. *)
Lemma d_ln1p t : -1 < t -> derivable_pt_lim (fun t => ln (1 + t)) t (/ (1 + t)).
Proof.
  intros H.
  assert (Hc : derivable_pt_lim (fun t => 1 + t) t 1).
  { apply (dpl_ext (fct_cte 1 + id)%F); [intro y; reflexivity | ].
    replace 1 with (0 + 1) at 2 by ring.
    apply derivable_pt_lim_plus; [apply derivable_pt_lim_const | apply derivable_pt_lim_id]. }
  pose proof (derivable_pt_lim_comp (fun t => 1 + t) ln t 1 (/ (1 + t)) Hc (derivable_pt_lim_ln (1 + t) ltac:(lra))) as D.
  apply (dpl_ext (comp ln (fun t : R => (1 + t)%R))); [intro y; reflexivity | ].
  replace (/ (1 + t)) with (/ (1 + t) * 1) by ring. exact D.
Qed.

(** [ln (1 + t) <= t]. *)
Lemma ln1p_le t : -1 < t -> ln (1 + t) <= t.
Proof.
  intros H.
  destruct (Req_dec (ln (1 + t)) 0) as [Z | NZ].
  - rewrite Z. destruct (Rle_lt_dec 0 t) as [c | c]; [lra | ].
    exfalso. assert (1 + t = 1) by (rewrite <- (exp_ln (1 + t)) by lra; rewrite Z, exp_0; reflexivity). lra.
  - pose proof (exp_ineq1 (ln (1 + t)) NZ). rewrite exp_ln in H0 by lra. lra.
Qed.

(** [t - t^2 <= ln (1 + t)] on [[-1/2, 1/2]]. *)
Lemma ln1p_ge t : -1 / 2 <= t <= 1 / 2 -> t - t * t <= ln (1 + t).
Proof.
  intros [Hl Hu].
  destruct (Rle_lt_dec 0 t) as [Hp | Hn].
  - set (f := fun t => ln (1 + t) - t + t * t). set (f' := fun t => / (1 + t) - 1 + 2 * t).
    assert (D : forall c, 0 <= c <= 1 / 2 -> derivable_pt_lim f c (f' c)).
    { intros c Hc. unfold f, f'.
      pose proof (derivable_pt_lim_minus _ _ c _ _ (d_ln1p c ltac:(lra)) (derivable_pt_lim_id c)) as D1.
      pose proof (derivable_pt_lim_mult _ _ c _ _ (derivable_pt_lim_id c) (derivable_pt_lim_id c)) as D2.
      pose proof (derivable_pt_lim_plus _ _ c _ _ D1 D2) as D3.
      apply (dpl_ext (((fun t : R => ln (1 + t)%R) - id) + (id * id))%F); [intro y; reflexivity | ].
      replace (/ (1 + c) - 1 + 2 * c) with (/ (1 + c) - 1 + (1 * id c + id c * 1)) by (unfold id; ring).
      exact D3. }
    assert (P : forall c, 0 < c < 1 / 2 -> 0 <= f' c).
    { intros c Hc. unfold f'. assert (Hi : / (1 + c) * (1 + c) = 1) by (apply Rinv_l; lra).
      assert (0 < / (1 + c)) by (apply Rinv_0_lt_compat; lra). nra. }
    assert (F0 : f 0 = 0) by (unfold f; rewrite Rplus_0_r, ln_1; ring).
    pose proof (nonneg_mvt f f' (1 / 2) D P F0 t ltac:(lra)). unfold f in H. lra.
  - set (g := fun s => ln (1 - s) + s + s * s). set (g' := fun s => - / (1 - s) + 1 + 2 * s).
    assert (D : forall c, 0 <= c <= 1 / 2 -> derivable_pt_lim g c (g' c)).
    { intros c Hc. unfold g, g'.
      assert (Hd1 : derivable_pt_lim (fun s => 1 - s) c (-1)).
      { apply (dpl_ext (fct_cte 1 - id)%F); [intro y; reflexivity | ].
        replace (-1) with (0 - 1) by ring.
        apply derivable_pt_lim_minus; [apply derivable_pt_lim_const | apply derivable_pt_lim_id]. }
      pose proof (derivable_pt_lim_comp (fun s => 1 - s) ln c (-1) (/ (1 - c)) Hd1 (derivable_pt_lim_ln (1 - c) ltac:(lra))) as D0.
      pose proof (derivable_pt_lim_plus _ _ c _ _ D0 (derivable_pt_lim_id c)) as D1.
      pose proof (derivable_pt_lim_mult _ _ c _ _ (derivable_pt_lim_id c) (derivable_pt_lim_id c)) as D2.
      pose proof (derivable_pt_lim_plus _ _ c _ _ D1 D2) as D3.
      apply (dpl_ext ((comp ln (fun s : R => (1 - s)%R) + id) + (id * id))%F); [intro y; reflexivity | ].
      replace (- / (1 - c) + 1 + 2 * c) with (/ (1 - c) * -1 + 1 + (1 * id c + id c * 1)) by (unfold id; ring).
      exact D3. }
    assert (P : forall c, 0 < c < 1 / 2 -> 0 <= g' c).
    { intros c Hc. unfold g'. assert (Hi : / (1 - c) * (1 - c) = 1) by (apply Rinv_l; lra).
      assert (0 < / (1 - c)) by (apply Rinv_0_lt_compat; lra). nra. }
    assert (G0 : g 0 = 0) by (unfold g; rewrite Rminus_0_r, ln_1; ring).
    pose proof (nonneg_mvt g g' (1 / 2) D P G0 (- t) ltac:(lra)). unfold g in H.
    replace (1 - - t) with (1 + t) in H by ring. nra.
Qed.

(** [|ln (1 + t) - t| <= t^2] on [[-1/2, 1/2]]. *)
Lemma ln1p_abs t : -1 / 2 <= t <= 1 / 2 -> Rabs (ln (1 + t) - t) <= t * t.
Proof.
  intros H. pose proof (ln1p_ge t H). pose proof (ln1p_le t ltac:(lra)).
  pose proof (Rle_0_sqr t). unfold Rsqr in H2.
  apply Rabs_le. split; nra.
Qed.

Lemma ln_mono x y : 0 < x -> x <= y -> ln x <= ln y.
Proof.
  intros Hx H. destruct (Req_dec x y) as [-> | Hn]; [lra | ].
  pose proof (ln_increasing x y Hx ltac:(lra)). lra.
Qed.
