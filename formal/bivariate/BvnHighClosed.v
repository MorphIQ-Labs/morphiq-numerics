(** Rounding of Genz's closed form on the last scale [s <= 0.003]
    (docs/bivariate_normal_high.md section 4.4). *)
From Coq Require Import Reals Lra Psatz ZArith Lia.
From Interval Require Import Tactic.
From Flocq Require Import Core.
Require Import BvnHighAssembly BvnHighRound BvnHighSteps BvnHighBudget BvnHighErr BvnHighErrTree.
Open Scope R_scope.

Lemma xe_half q : 0 <= q -> q * exp (- (q * q / 2)) <= 607 / 1000.
Proof.
  intros Hq.
  pose proof (exp_ineq1_le (q * q / 2 - 1 / 2)) as H.
  assert (E : exp (q * q / 2 - 1 / 2) = exp (q * q / 2) * exp (- (1 / 2))) by (rewrite <- exp_plus; f_equal; ring).
  assert (Hm : exp (- (1 / 2)) <= 6066 / 10000) by interval.
  assert (Hp : 0 < exp (q * q / 2)) by apply exp_pos.
  assert (Hp' : 0 < exp (- (1 / 2))) by apply exp_pos.
  assert (H2 : q <= exp (q * q / 2) * exp (- (1 / 2))).
  { pose proof (pow2_ge_0 (q - 1)). assert (q <= 1 + (q * q / 2 - 1 / 2)) by nra. lra. }
  rewrite exp_Ropp.
  assert (Hx : q * / exp (q * q / 2) <= exp (- (1 / 2))).
  { apply Rmult_le_reg_r with (exp (q * q / 2)); [exact Hp|]. rewrite Rmult_assoc, Rinv_l by lra. lra. }
  lra.
Qed.

Lemma half_abs X S A : Rabs (X - S) <= A -> Rabs (X / 2 - S / 2) <= A / 2.
Proof.
  intros H. replace (X / 2 - S / 2) with ((X - S) / 2) by field.
  unfold Rdiv. rewrite Rabs_mult. rewrite (Rabs_right (/ 2)) by lra. lra.
Qed.

Lemma half_le a T : 0 <= T -> (64 / 10 * u * a + T) / 2 <= 32 / 10 * u * a + T.
Proof. intros HT. lra. Qed.



(** The square root of a quantity known to within a relative error and a tiny
    absolute one: the root is known to within the half and a tiny absolute one. *)
Lemma sqrt_rela a a' e0 : 0 <= a -> 0 <= a' -> 0 <= e0 <= / 10 ^ 200 ->
  Rabs (a' - a) <= 31 / 10 * u * a + e0 ->
  Rabs (sqrt a' - sqrt a) <= 31 / 10 * u * sqrt a + 2 / 10 ^ 100.
Proof.
  intros Ha Ha' [He0 He1] H. pose proof u_pos as Hu. pose proof u_lt as Hu2.
  pose proof (sqrt_pos a) as Sa. pose proof (sqrt_pos a') as Sa'.
  pose proof (sqrt_sqrt a Ha) as Ea. pose proof (sqrt_sqrt a' Ha') as Ea'.
  apply Rabs_le_inv in H.
  assert (HT : 0 < 1 / 10 ^ 100) by interval.
  destruct (Rlt_le_dec a (1 / 10 ^ 200)) as [Hs|Hl].
  - (* both are tiny *)
    assert (Ha'1 : a' <= 3 / 10 ^ 200).
    { assert (31 / 10 * u * a <= 31 / 10 * u * (1 / 10 ^ 200)) by (apply Rmult_le_compat_l; [lra | lra]).
      assert (31 / 10 * u * (1 / 10 ^ 200) <= 1 / 10 ^ 200) by (assert (31 / 10 * (12 / 10 ^ 17) * (1 / 10 ^ 200) <= 1 / 10 ^ 200) by interval; nra).
      assert (/ 10 ^ 200 = 1 / 10 ^ 200) by field. lra. }
    assert (Hr : forall x, 0 <= x -> x <= 3 / 10 ^ 200 -> sqrt x <= 18 / 10 ^ 101).
    { intros x Hx0 Hx1. pose proof (sqrt_pos x). pose proof (sqrt_sqrt x Hx0).
      apply Rnot_lt_le. intro Hc. assert (18 / 10 ^ 101 * (18 / 10 ^ 101) < sqrt x * sqrt x) by (apply Rmult_le_0_lt_compat; [interval | interval | exact Hc | exact Hc]).
      assert (3 / 10 ^ 200 < 18 / 10 ^ 101 * (18 / 10 ^ 101)) by interval. lra. }
    pose proof (Hr a Ha ltac:(lra)). pose proof (Hr a' Ha' Ha'1).
    assert (0 <= u * sqrt a) by nra.
    assert (E1 : 18 / 10 ^ 101 = 18 * (1 / 10 ^ 101)) by field.
    assert (E2 : 2 / 10 ^ 100 = 20 * (1 / 10 ^ 101)) by field.
    assert (0 < 1 / 10 ^ 101) by interval.
    apply Rabs_le. split; lra.
  - assert (HsA : 1 / 10 ^ 100 <= sqrt a).
    { apply Rnot_lt_le. intro Hc. assert (sqrt a * sqrt a < 1 / 10 ^ 100 * (1 / 10 ^ 100)) by (apply Rmult_le_0_lt_compat; [lra | lra | exact Hc | exact Hc]).
      assert (1 / 10 ^ 100 * (1 / 10 ^ 100) = 1 / 10 ^ 200) by field. lra. }
    assert (Hp : (sqrt a' - sqrt a) * (sqrt a' + sqrt a) = a' - a).
    { replace ((sqrt a' - sqrt a) * (sqrt a' + sqrt a)) with (sqrt a' * sqrt a' - sqrt a * sqrt a) by ring. rewrite Ea, Ea'. reflexivity. }
    assert (Hsum : sqrt a <= sqrt a' + sqrt a) by lra.
    set (d := sqrt a' - sqrt a) in *.
    assert (Hd1 : d * sqrt a <= 31 / 10 * u * a + e0).
    { destruct (Rle_dec d 0) as [Hd|Hd].
      - assert (0 <= 31 / 10 * u * a) by nra. nra.
      - assert (0 < d) by lra. assert (d * sqrt a <= d * (sqrt a' + sqrt a)) by (apply Rmult_le_compat_l; lra). lra. }
    assert (Hd2 : - d * sqrt a <= 31 / 10 * u * a + e0).
    { destruct (Rle_dec 0 d) as [Hd|Hd].
      - assert (0 <= 31 / 10 * u * a) by nra. nra.
      - assert (0 < - d) by lra. assert (- d * sqrt a <= - d * (sqrt a' + sqrt a)) by (apply Rmult_le_compat_l; lra). nra. }
    assert (Ef : 31 / 10 * u * a = (31 / 10 * u * sqrt a) * sqrt a) by (rewrite <- (sqrt_sqrt a Ha) at 1; nra).
    assert (He0s : e0 <= 1 / 10 ^ 100 * sqrt a).
    { assert (e0 <= 1 / 10 ^ 200) by (assert (/ 10 ^ 200 = 1 / 10 ^ 200) by field; lra).
      assert (1 / 10 ^ 200 <= 1 / 10 ^ 100 * sqrt a) by (assert (1 / 10 ^ 100 * (1 / 10 ^ 100) <= 1 / 10 ^ 100 * sqrt a) by (apply Rmult_le_compat_l; [interval | exact HsA]); assert (1 / 10 ^ 100 * (1 / 10 ^ 100) = 1 / 10 ^ 200) by field; lra). lra. }
    assert (Hdf : d <= 31 / 10 * u * sqrt a + 1 / 10 ^ 100).
    { apply Rmult_le_reg_r with (sqrt a); [lra|]. nra. }
    assert (Hdf2 : - d <= 31 / 10 * u * sqrt a + 1 / 10 ^ 100).
    { apply Rmult_le_reg_r with (sqrt a); [lra|]. nra. }
    apply Rabs_le. split; nra.
Qed.

Section ECore.
Variable expT : R -> R.
Hypothesis Hex7 : forall x, -700 <= x -> x <= 1 -> rel (exp x) (expT x) u.

(** The exponential of the closed form's first term, for [w = (Q + hk)/2]. *)
Lemma E_core Q hk sig :
  0 <= Q -> Q <= 4001 / 10 -> - (91 / 100000) <= hk -> hk <= 100 -> 0 <= Q + hk ->
  Rabs (sig - (Q + hk)) <= 64 / 10 * u * (Q + Rabs hk) + 1 / 10 ^ 170 ->
  ab (exp (- ((Q + hk) / 2))) (expT (- (sig / 2))) 1 (35 / 10 * u).
Proof.
  intros Q0 Q1 Hl Hh Hw Hsg.
  pose proof u_pos as Hu. pose proof u_lt as Hu2.
  assert (Hw0 : 0 <= (Q + hk) / 2) by lra.
  assert (HQa : Q + Rabs hk <= 2 * ((Q + hk) / 2) + 2 / 1000).
  { destruct (Rle_dec 0 hk) as [Hk|Hk].
    - rewrite (Rabs_right hk) by lra. lra.
    - rewrite (Rabs_left hk) by lra. lra. }
  assert (HQh : 0 <= Q + Rabs hk) by (pose proof (Rabs_pos hk); lra).
  assert (Hhk100 : Rabs hk <= 100) by (apply Rabs_le; lra).
  assert (HT : 0 < 1 / 10 ^ 170) by interval.
  assert (HDs : 32 / 10 * u * (Q + Rabs hk) + 1 / 10 ^ 170 <= 1 / 10 ^ 12).
  { assert (u * (Q + Rabs hk) <= u * (4001 / 10 + 100)) by (apply Rmult_le_compat_l; [lra | lra]).
    assert (u * (4001 / 10 + 100) <= 12 / 10 ^ 17 * (4001 / 10 + 100)) by (apply Rmult_le_compat_r; [lra | lra]).
    assert (32 / 10 * (12 / 10 ^ 17 * (4001 / 10 + 100)) + 1 / 10 ^ 170 <= 1 / 10 ^ 12) by interval. nra. }
  set (D := 32 / 10 * u * (Q + Rabs hk) + 1 / 10 ^ 170) in *.
  assert (HD0 : 0 <= D) by (unfold D; assert (0 <= u * (Q + Rabs hk)) by nra; lra).
  assert (HDh : D <= 1 / 2) by (assert (1 / 10 ^ 12 <= 1 / 2) by interval; lra).
  assert (Hd : Rabs (sig / 2 - (Q + hk) / 2) <= D).
  { pose proof (half_abs sig (Q + hk) _ Hsg) as Hhf.
    eapply Rle_trans; [exact Hhf|]. unfold D. apply (half_le (Q + Rabs hk) (1 / 10 ^ 170) (Rlt_le _ _ HT)). }
  pose proof (exp_pert ((Q + hk) / 2) (sig / 2) D Hd HD0 HDh) as Hp1.
  pose proof (Rabs_le_inv _ _ Hd) as [Hd1 Hd2].
  assert (Hr1 : -700 <= - (sig / 2)) by lra.
  assert (Hr2 : - (sig / 2) <= 1) by lra.
  pose proof (Hex7 (- (sig / 2)) Hr1 Hr2) as Hp1b.
  pose proof (rel_trans (exp (- ((Q + hk) / 2))) (exp (- (sig / 2))) (expT (- (sig / 2))) (D + 2 * (D * D)) u ltac:(nra) (Rlt_le _ _ Hu) Hp1 Hp1b) as Hp2.
  unfold ab, rel in *.
  set (w := (Q + hk) / 2) in *.
  assert (Hle1 : exp (- w) <= 1).
  { rewrite <- exp_0. destruct (Rle_lt_or_eq_dec 0 w Hw0) as [Hl2|Heq]; [left; apply exp_increasing; lra | right; f_equal; lra]. }
  pose proof (exp_pos (- w)) as Hpos.
  split.
  - rewrite Rabs_right by lra. exact Hle1.
  - pose proof (xe_bound w Hw0) as Hxe.
    rewrite (Rabs_right (exp (- w))) in Hp2 by lra.
    set (E := exp (- w)) in *.
    assert (HEQ : E * (Q + Rabs hk) <= 7378 / 10000).
    { assert (Hm : E * (Q + Rabs hk) <= E * (2 * w + 2 / 1000)) by (apply Rmult_le_compat_l; lra).
      assert (Hr : E * (2 * w + 2 / 1000) = 2 * (w * E) + 2 / 1000 * E) by ring.
      lra. }
    assert (HEw : E * D <= 32 / 10 * u * (7378 / 10000) + E * (1 / 10 ^ 170)).
    { unfold D. assert (E * (32 / 10 * u * (Q + Rabs hk)) = 32 / 10 * u * (E * (Q + Rabs hk))) by ring.
      assert (32 / 10 * u * (E * (Q + Rabs hk)) <= 32 / 10 * u * (7378 / 10000)) by (apply Rmult_le_compat_l; [nra | exact HEQ]). nra. }
    assert (HDD : D * D <= D * (1 / 10 ^ 12)) by (apply Rmult_le_compat_l; lra).
    assert (HD1 : D + 2 * (D * D) <= 1 / 10 ^ 11).
    { assert (D * (1 / 10 ^ 12) <= 1 / 10 ^ 12 * (1 / 10 ^ 12)) by (apply Rmult_le_compat_r; [interval | lra]).
      assert (1 / 10 ^ 12 * (1 / 10 ^ 12) <= 1 / 10 ^ 13) by interval.
      assert (1 / 10 ^ 12 + 2 * (1 / 10 ^ 13) <= 1 / 10 ^ 11) by interval. lra. }
    assert (Hu4 : u * (1 + (D + 2 * (D * D))) <= u * (1 + 1 / 10 ^ 11)) by (apply Rmult_le_compat_l; lra).
    assert (Hth : (D + 2 * (D * D)) + u * (1 + (D + 2 * (D * D))) <= D + 2 * (D * (1 / 10 ^ 12)) + u * (1 + 1 / 10 ^ 11)) by lra.
    assert (Hm : (D + 2 * (D * D) + u * (1 + (D + 2 * (D * D)))) * E <= (D + 2 * (D * (1 / 10 ^ 12)) + u * (1 + 1 / 10 ^ 11)) * E) by (apply Rmult_le_compat_r; lra).
    assert (E2 : (D + 2 * (D * (1 / 10 ^ 12)) + u * (1 + 1 / 10 ^ 11)) * E = E * D * (1 + 2 / 10 ^ 12) + (1 + 1 / 10 ^ 11) * (u * E)) by field.
    assert (Hu3 : (1 + 1 / 10 ^ 11) * (u * E) <= (1 + 1 / 10 ^ 11) * u) by (apply Rmult_le_compat_l; [interval | nra]).
    assert (HEw' : E * D * (1 + 2 / 10 ^ 12) <= (32 / 10 * u * (7378 / 10000) + E * (1 / 10 ^ 170)) * (1 + 2 / 10 ^ 12)) by (apply Rmult_le_compat_r; [interval | lra]).
    assert (HE170 : E * (1 / 10 ^ 170) <= 1 * (1 / 10 ^ 170)) by (apply Rmult_le_compat_r; [interval | lra]).
    assert (Hu170 : 1 / 10 ^ 170 <= u / 1000) by (rewrite u_value; interval).
    assert (Hcc : (32 / 10 * u * (7378 / 10000) + 1 / 10 ^ 170) * (1 + 2 / 10 ^ 12) <= 24 / 10 * u).
    { assert (32 / 10 * (7378 / 10000) * (1 + 2 / 10 ^ 12) + 1 / 1000 * (1 + 2 / 10 ^ 12) <= 24 / 10) by interval.
      assert ((32 / 10 * u * (7378 / 10000) + 1 / 10 ^ 170) * (1 + 2 / 10 ^ 12) <= (32 / 10 * u * (7378 / 10000) + u / 1000) * (1 + 2 / 10 ^ 12)) by (apply Rmult_le_compat_r; [interval | lra]).
      nra. }
    assert (Hc2 : (32 / 10 * u * (7378 / 10000) + E * (1 / 10 ^ 170)) * (1 + 2 / 10 ^ 12) <= (32 / 10 * u * (7378 / 10000) + 1 / 10 ^ 170) * (1 + 2 / 10 ^ 12)) by (apply Rmult_le_compat_r; [interval | lra]).
    assert (Hfin2 : (1 + 1 / 10 ^ 11) * u <= 101 / 100 * u) by (assert (1 + 1 / 10 ^ 11 <= 101 / 100) by interval; nra).
    nra.
Qed.
End ECore.

Section Closed.
Variables s bs hk bsT hkT e0 : R.
Hypothesis Hs : 1 / 10 ^ 8 <= s <= 3 / 1000.
Hypothesis Hbs : 0 <= bs.
Hypothesis Hbsq : bs <= 4001 / 10 * (s * s).
Hypothesis Hc : - (4 * hk) <= bs.
Hypothesis Hhk : hk < 100.
Hypothesis He0 : 0 <= e0 <= / 10 ^ 200.
Hypothesis Hbs2 : rela bs bsT (31 / 10 * u) e0.
Hypothesis Hhk2 : rela hk hkT u e0.

Lemma ss_bounds : 1 / 10 ^ 16 <= s * s <= 9 / 10 ^ 6.
Proof.
  destruct Hs as [H1 H2].
  split.
  - pose proof (Rmult_le_compat (1 / 10 ^ 8) s (1 / 10 ^ 8) s ltac:(interval) ltac:(interval) H1 H1).
    assert (1 / 10 ^ 8 * (1 / 10 ^ 8) = 1 / 10 ^ 16) by field. lra.
  - pose proof (Rmult_le_compat s (3 / 1000) s (3 / 1000) ltac:(interval) ltac:(interval) H2 H2).
    assert (3 / 1000 * (3 / 1000) = 9 / 10 ^ 6) by field. lra.
Qed.

Lemma hk_lo : - (91 / 100000) <= hk.
Proof.
  pose proof ss_bounds as [A B]. destruct Hs as [H1 H2].
  assert (bs <= 4001 / 10 * (9 / 10 ^ 6)) by (apply Rle_trans with (4001 / 10 * (s * s)); [exact Hbsq | apply Rmult_le_compat_l; [interval | exact B]]).
  assert (4001 / 10 * (9 / 10 ^ 6) <= 4 * (91 / 100000)) by interval.
  lra.
Qed.

Lemma ass_rel : rel (s * s) (rnd (s * s)) u.
Proof.
  pose proof ss_bounds as [A B]. pose proof u_pos.
  assert (Hp : 0 < s * s) by (assert (0 < 1 / 10 ^ 16) by interval; lra).
  unfold rel. rewrite (Rabs_right (s * s)) by lra.
  pose proof (rnd_rel (s * s) (nrm_pos (s * s) ltac:(assert (1 / 10 ^ 100 <= 1 / 10 ^ 16) by interval; lra))) as Hr.
  rewrite (Rabs_right (s * s)) in Hr by lra. exact Hr.
Qed.

Lemma q2_rela : rela (bs / (s * s)) (rnd (bsT / rnd (s * s))) (52 / 10 * u) (1 / 10 ^ 180).
Proof.
  pose proof ss_bounds as [A B]. pose proof u_pos as Hu. pose proof u_lt as Hu2. pose proof eta_small as Hη.
  destruct He0 as [He0a He0b].
  assert (Hp : 0 < s * s) by (assert (0 < 1 / 10 ^ 16) by interval; lra).
  pose proof (rela_div_rel bs bsT (s * s) (rnd (s * s)) (31 / 10 * u) e0 u Hp ltac:(lra) He0a (Rlt_le _ _ Hu) ltac:(lra) ass_rel Hbs2) as Hd.
  assert (Ht : 0 <= (31 / 10 * u + u) / (1 - u)).
  { unfold Rdiv. apply Rmult_le_pos; [lra | left; apply Rinv_0_lt_compat; lra]. }
  assert (He : 0 <= e0 / ((1 - u) * (s * s))).
  { apply Rmult_le_pos; [exact He0a | left; apply Rinv_0_lt_compat; apply Rmult_lt_0_compat; lra]. }
  pose proof (rela_rnd _ _ _ _ Ht He Hd) as Hr.
  unfold rela in *.
  assert (Hc1 : (31 / 10 * u + u) / (1 - u) + u + u * ((31 / 10 * u + u) / (1 - u)) <= 52 / 10 * u).
  { assert (Hq : (31 / 10 * u + u) / (1 - u) <= 411 / 100 * u).
    { apply Rmult_le_reg_r with (1 - u); [lra|]. unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. nra. }
    nra. }
  assert (Hinv : / ((1 - u) * (s * s)) <= 2 * 10 ^ 16).
  { assert (HH : 99 / 100 * (1 / 10 ^ 16) <= (1 - u) * (s * s)) by nra.
    apply Rle_trans with (/ (99 / 100 * (1 / 10 ^ 16))).
    - apply Rinv_le_contravar; [interval | exact HH].
    - assert (/ (99 / 100 * (1 / 10 ^ 16)) = 10 ^ 16 * (100 / 99)) by field. rewrite H. interval. }
  assert (Hq : e0 / ((1 - u) * (s * s)) <= / 10 ^ 200 * (2 * 10 ^ 16)).
  { unfold Rdiv. apply Rle_trans with (/ 10 ^ 200 * / ((1 - u) * (s * s))).
    - apply Rmult_le_compat_r; [left; apply Rinv_0_lt_compat; nra | exact He0b].
    - apply Rmult_le_compat_l; [left; apply Rinv_0_lt_compat; apply pow_lt; lra | exact Hinv]. }
  assert (E1 : / 10 ^ 200 * (2 * 10 ^ 16) = 2 / 10 ^ 184) by field.
  assert (E2 : 2 / 10 ^ 184 + / 10 ^ 300 + 1 / 10 ^ 10 * (2 / 10 ^ 184) <= 1 / 10 ^ 180) by interval.
  assert (Hp0 : 0 <= e0 / ((1 - u) * (s * s))) by exact He.
  pose proof (Rmult_le_compat_r (Rabs (bs / (s * s))) _ _ (Rabs_pos _) Hc1) as Hm.
  assert (u * (e0 / ((1 - u) * (s * s))) <= 1 / 10 ^ 10 * (2 / 10 ^ 184)).
  { assert (u <= 1 / 10 ^ 10) by (assert (12 / 10 ^ 17 <= 1 / 10 ^ 10) by interval; lra). nra. }
  lra.
Qed.

Lemma Q_bounds : 0 <= bs / (s * s) <= 4001 / 10.
Proof.
  pose proof ss_bounds as [A B]. split.
  - apply Rmult_le_pos; [exact Hbs | left; apply Rinv_0_lt_compat; assert (0 < 1 / 10 ^ 16) by interval; lra].
  - assert (Hp : 0 < s * s) by (assert (0 < 1 / 10 ^ 16) by interval; lra).
    apply Rmult_le_reg_r with (s * s); [exact Hp|]. unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. lra.
Qed.

Lemma sig_err : Rabs (rnd (rnd (bsT / rnd (s * s)) + hkT) - (bs / (s * s) + hk))
  <= 64 / 10 * u * (bs / (s * s) + Rabs hk) + 1 / 10 ^ 170.
Proof.
  pose proof q2_rela as H1. pose proof Hhk2 as H2. pose proof Q_bounds as [Q0 Q1].
  set (Q := bs / (s * s)) in *. set (q2T := rnd (bsT / rnd (s * s))) in *.
  unfold rela in H1, H2. rewrite (Rabs_right Q) in H1 by lra.
  pose proof u_pos as Hu. pose proof u_lt as Hu2. pose proof eta_small as Hη. destruct He0 as [He0a He0b].
  pose proof (rnd_abs (q2T + hkT)) as Hr.
  assert (Hs1 : Rabs (q2T + hkT - (Q + hk)) <= 52 / 10 * u * Q + u * Rabs hk + 1 / 10 ^ 180 + e0).
  { pose proof (Rabs_triang (q2T - Q) (hkT - hk)). replace (q2T + hkT - (Q + hk)) with ((q2T - Q) + (hkT - hk)) by ring. lra. }
  assert (Hy : Rabs (q2T + hkT) <= (1 + 52 / 10 * u) * Q + (1 + u) * Rabs hk + 1 / 10 ^ 180 + e0).
  { pose proof (Rabs_triang (q2T + hkT - (Q + hk)) (Q + hk)). pose proof (Rabs_triang Q hk).
    replace (q2T + hkT - (Q + hk) + (Q + hk)) with (q2T + hkT) in H by ring.
    rewrite (Rabs_right Q) in H0 by lra. nra. }
  pose proof (Rabs_triang (rnd (q2T + hkT) - (q2T + hkT)) (q2T + hkT - (Q + hk))) as Ht.
  replace (rnd (q2T + hkT) - (q2T + hkT) + (q2T + hkT - (Q + hk))) with (rnd (q2T + hkT) - (Q + hk)) in Ht by ring.
  assert (Hu' : u * Rabs (q2T + hkT) <= u * ((1 + 52 / 10 * u) * Q + (1 + u) * Rabs hk + 1 / 10 ^ 180 + e0)) by (apply Rmult_le_compat_l; [lra | exact Hy]).
  pose proof (Rabs_pos hk).
  assert (A0 : 0 <= u * Q) by nra. assert (B0 : 0 <= u * Rabs hk) by nra.
  assert (A1 : u * (u * Q) <= 1 / 100 * (u * Q)) by nra.
  assert (B1 : u * (u * Rabs hk) <= 1 / 100 * (u * Rabs hk)) by nra.
  assert (Ex : u * ((1 + 52 / 10 * u) * Q + (1 + u) * Rabs hk + 1 / 10 ^ 180 + e0)
               = u * Q + 52 / 10 * (u * (u * Q)) + u * Rabs hk + u * (u * Rabs hk) + u * (1 / 10 ^ 180 + e0)) by ring.
  assert (Ex2 : 64 / 10 * u * (Q + Rabs hk) = 64 / 10 * (u * Q) + 64 / 10 * (u * Rabs hk)) by ring.
  assert (Ex3 : 52 / 10 * u * Q = 52 / 10 * (u * Q)) by ring.
  assert (Hz : 1 / 10 ^ 180 + e0 + u * (1 / 10 ^ 180 + e0) + eta <= 1 / 10 ^ 170).
  { assert (u <= 1) by lra. assert (1 / 10 ^ 180 + 1 / 10 ^ 200 + 1 * (1 / 10 ^ 180 + 1 / 10 ^ 200) + / 10 ^ 300 <= 1 / 10 ^ 170) by interval.
    assert (u * (1 / 10 ^ 180 + e0) <= 1 * (1 / 10 ^ 180 + 1 / 10 ^ 200)) by (apply Rmult_le_compat; [lra | lra | lra | lra]). lra. }
  lra.
Qed.

End Closed.
