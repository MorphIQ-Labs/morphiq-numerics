(** Real-analysis facts for asin's fast path: [asin] enclosed through [sin]
    monotonicity, the composition of an approximation error with an evaluation
    error, the complement's half-angle identity and the Lipschitz bound of
    [asin] on the complement's argument range. *)
From Coq Require Import Reals ZArith Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
Open Scope R_scope.

(** [S - E <= asin v <= S + E] from [sin] at the two ends. *)
Lemma asin_within v S E : 0 <= E ->
  - (PI / 2) - (S - E) <= 0 -> (S + E) - PI / 2 <= 0 ->
  sin (S - E) - v <= 0 -> 0 <= sin (S + E) - v -> Rabs (asin v - S) <= E.
Proof.
  intros HE L U Hl Hu.
  assert (L' : - (PI / 2) <= S - E) by lra. assert (U' : S + E <= PI / 2) by lra.
  assert (Hl' : sin (S - E) <= v) by lra. assert (Hu' : v <= sin (S + E)) by lra. clear L U Hl Hu.
  assert (Hv : -1 <= v <= 1).
  { pose proof (SIN_bound (S - E)) as B1. pose proof (SIN_bound (S + E)) as B2. lra. }
  assert (Hs : sin (asin v) = v) by (apply sin_asin; exact Hv).
  pose proof (asin_bound v) as [A1 A2].
  apply Rabs_le. split.
  - destruct (Rle_lt_dec (S - E) (asin v)) as [Hc | Hc]; [lra | exfalso].
    pose proof (sin_increasing_1 (asin v) (S - E) A1 A2 L' ltac:(lra) Hc). lra.
  - destruct (Rle_lt_dec (asin v) (S + E)) as [Hc | Hc]; [lra | exfalso].
    pose proof (sin_increasing_1 (S + E) (asin v) ltac:(lra) U' A1 A2 Hc). lra.
Qed.

(** [asin v >= 0] and [asin v >= v] on [[0, 1]]. *)
Lemma asin_nonneg v : 0 <= v <= 1 -> 0 <= asin v.
Proof.
  intros [H0 H1]. pose proof (asin_bound v) as [A1 A2].
  assert (Hs : sin (asin v) = v) by (apply sin_asin; lra).
  destruct (Rle_lt_dec 0 (asin v)) as [Hc | Hc]; [exact Hc | exfalso].
  pose proof PI_RGT_0.
  pose proof (sin_increasing_1 (asin v) 0 A1 A2 ltac:(lra) ltac:(lra) Hc) as Hlt. rewrite sin_0 in Hlt. lra.
Qed.

Lemma asin_ge v : 0 <= v <= 1 -> v <= asin v.
Proof.
  intros H. pose proof (asin_nonneg v H) as N.
  assert (Hs : sin (asin v) = v) by (apply sin_asin; lra).
  pose proof (asin_bound v) as [A1 A2]. pose proof PI_RGT_0. pose proof PI_4.
  pose proof (sin_bound (asin v) 0 ltac:(lra) ltac:(lra)) as [L U].
  unfold sin_approx, sin_term in U. simpl in U.
  set (a := asin v) in *.
  assert (Q : a * (a * a) * (a * a - 20) <= 0).
  { assert (a * a <= 20) by nra. assert (0 <= a * (a * a)) by (apply Rmult_le_pos; [lra | nra]). nra. }
  nra.
Qed.

(** The fast path's composition: [(S + e1)(1 + ea)] against [A], given the
    approximation error of [S], the evaluation error [e1] and the rounding [ea]. *)
Lemma fast_compose A S e1 ea E b Ea Amin rel :
  Rabs (A - S) <= E -> Rabs e1 <= b -> Rabs ea <= Ea -> Amin <= A -> 0 < Amin -> 0 <= Ea ->
  (E + b) * (1 + Ea) + Ea * Amin <= rel * Amin ->
  Rabs ((S + e1) * (1 + ea) - A) <= rel * A.
Proof.
  intros HA Hb Hea HAm Hp HE Hr.
  pose proof (Rabs_pos e1). pose proof (Rabs_pos ea). pose proof (Rabs_pos (A - S)).
  pose proof Hb as Hb0. pose proof Hea as Hea0.
  apply Rabs_le_inv in HA. apply Rabs_le_inv in Hb. apply Rabs_le_inv in Hea.
  assert (Hrel : Ea <= rel).
  { destruct (Rle_lt_dec Ea rel) as [c | c]; [exact c | exfalso].
    assert (0 <= (E + b)) by lra. nra. }
  apply Rabs_le.
  assert (Hd : (S + e1) * (1 + ea) - A = (S - A) + e1 + (S + e1) * ea) by ring.
  rewrite Hd.
  assert (HSe : Rabs (S + e1) <= A + E + b).
  { apply Rle_trans with (Rabs S + Rabs e1); [apply Rabs_triang | ].
    assert (Rabs S <= A + E) by (apply Rabs_le; split; lra).
    pose proof Hb0. lra. }
  assert (Hm : Rabs ((S + e1) * ea) <= (A + E + b) * Ea).
  { rewrite Rabs_mult. apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | exact HSe | exact Hea0]. }
  apply Rabs_le_inv in Hm. 
  assert (E + b <= (rel - Ea) * A).
  { assert (E + b <= (rel - Ea) * Amin) by nra. nra. }
  nra.
Qed.

(** The complement's half-angle identity: [asin x = pi/2 - 2 asin (sqrt ((1 - x)/2))]. *)
Lemma complement_identity x : 0 <= x <= 1 -> asin x = PI / 2 - 2 * asin (sqrt ((1 - x) / 2)).
Proof.
  intros [H0 H1]. set (w := sqrt ((1 - x) / 2)).
  assert (Hw2 : w * w = (1 - x) / 2) by (unfold w; apply sqrt_def; lra).
  assert (Hw0 : 0 <= w) by (unfold w; apply sqrt_pos).
  assert (Hw1 : w <= 1) by nra.
  pose proof (asin_bound w) as [B1 B2].
  assert (Hs : sin (asin w) = w) by (apply sin_asin; lra).
  assert (Hy : sin (PI / 2 - 2 * asin w) = x).
  { rewrite sin_minus, sin_PI2, cos_PI2, cos_2a_sin, Hs. lra. }
  rewrite <- Hy. pose proof (asin_nonneg w ltac:(lra)). rewrite asin_sin; [reflexivity | split; lra].
Qed.

(** [asin] over a short interval: the mean value theorem with
    [asin' = 1/sqrt (1 - x^2)]. *)
Lemma asin_step a b : 0 <= a -> a < b -> b <= 0.0079 ->
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

(** [1/sqrt (1 - s) - 1 <= 0.5003 s] for [0 <= s <= 0.0004]. *)
Lemma inv_sqrt_small s : 0 <= s <= 0.0004 -> 1 <= 1 / sqrt (1 - s) <= 1 + 0.5003 * s.
Proof.
  intros [H0 H1].
  assert (P : 0 < sqrt (1 - s)) by (apply sqrt_lt_R0; lra).
  assert (U : sqrt (1 - s) <= 1) by (pose proof (sqrt_le_1_alt (1 - s) 1 ltac:(lra)) as U0; rewrite sqrt_1 in U0; exact U0).
  assert (Lo : 1 - 0.5001 * s <= sqrt (1 - s)).
  { rewrite <- (sqrt_Rsqr (1 - 0.5001 * s)) by lra. apply sqrt_le_1_alt. unfold Rsqr. nra. }
  split.
  - rewrite <- (Rinv_1) at 1. apply Rle_trans with (1 / 1); [lra | ]. unfold Rdiv. rewrite Rmult_1_l, Rmult_1_l.
    apply Rinv_le_contravar; lra.
  - unfold Rdiv. rewrite Rmult_1_l. apply Rle_trans with (/ (1 - 0.5001 * s)).
    + apply Rinv_le_contravar; lra.
    + apply Rmult_le_reg_r with (1 - 0.5001 * s); [lra | ]. rewrite Rinv_l by lra. nra.
Qed.

(** [asin] over [[a, b]] within [[0, 0.0079]]: its increment is the interval's
    length, up to [0.5003 b^2] relatively. *)
Lemma asin_gap a b : 0 <= a -> a < b -> b <= 0.0079 ->
  b - a <= asin b - asin a <= (b - a) * (1 + 0.5003 * (b * b)).
Proof.
  intros Ha Hab Hb.
  destruct (asin_step a b Ha Hab Hb) as [xi [Hxi E]].
  assert (Hs : 0 <= xi * xi <= 0.0004) by (split; nra).
  pose proof (inv_sqrt_small (xi * xi) Hs) as [G1 G2].
  assert (Hxb : xi * xi <= b * b) by nra.
  rewrite E. set (g := 1 / sqrt (1 - xi * xi)) in *.
  split; nra.
Qed.

(** A double-word's low part shifts [asin] by itself, to relative [x^2/2]:
    [|asin (x + d) - asin x - d| <= 0.51 x^2 |d|] for [|d| <= 2^-52 x]. *)
Lemma asin_shift x d : / 268435456 <= x <= 0.0078126 -> Rabs d <= / 4503599627370496 * x ->
  Rabs (asin (x + d) - asin x - d) <= 0.51 * (x * x) * Rabs d.
Proof.
  intros [Hx0 Hx1] Hd.
  assert (Hdl : Rabs d <= 0.0000001 * x).
  { apply Rle_trans with (/ 4503599627370496 * x); [exact Hd | ]. nra. }
  assert (Hxp : 0 < x) by (assert (0 < / 268435456) by (apply Rinv_0_lt_compat; lra); lra).
  pose proof (Rabs_pos d) as Hp. pose proof Hdl as Hdl0. apply Rabs_le_inv in Hdl.
  assert (Hx2 : (x + Rabs d) * (x + Rabs d) <= 1.0001 * (x * x)) by nra.
  destruct (Rtotal_order d 0) as [Hneg | [Hz | Hpos]].
  - destruct (asin_gap (x + d) x ltac:(lra) ltac:(lra) ltac:(lra)) as [G1 G2].
    rewrite (Rabs_left d Hneg) in *. apply Rabs_le. split; nra.
  - subst d. rewrite Rplus_0_r. replace (asin x - asin x - 0) with 0 by ring. rewrite Rabs_R0. nra.
  - destruct (asin_gap x (x + d) ltac:(lra) ltac:(lra) ltac:(lra)) as [G1 G2].
    rewrite (Rabs_right d) in * by lra. apply Rabs_le. split; nra.
Qed.
