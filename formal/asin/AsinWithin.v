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
