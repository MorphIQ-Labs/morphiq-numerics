(** One quadrature node: the computed term [rndF (w * rndF (exp a))] against
    the exact [W exp(-Q(sin t))] at the exact node angle [t], where [a] is the
    computed exponent argument of BvnArg.v at the rounded sine and cosine of
    the computed angle [th], [|th - t| <= dth]. *)
From Coq Require Import Reals Lra Psatz ZArith Lia.
From Flocq Require Import Core.
From Flocq Require Import Relative.
Require Import BvnRound BvnArg.
Open Scope R_scope.

(** [sin] is 1-Lipschitz. *)
Lemma sin_lip a b : Rabs (sin a - sin b) <= Rabs (a - b).
Proof.
  rewrite form4. rewrite Rabs_mult, Rabs_mult.
  assert (H2 : Rabs 2 = 2) by (apply Rabs_pos_eq; lra). rewrite H2.
  pose proof (Rabs_pos (cos ((a + b) / 2))). pose proof (Rabs_pos (sin ((a - b) / 2))).
  assert (Hc : Rabs (cos ((a + b) / 2)) <= 1) by (apply Rabs_le; apply COS_bound).
  assert (Hs : Rabs (sin ((a - b) / 2)) <= Rabs ((a - b) / 2)).
  { set (d := (a - b) / 2).
    destruct (Rle_or_lt 0 d) as [Hd | Hd].
    - rewrite (Rabs_pos_eq d Hd).
      destruct Hd as [Hd | Hd].
      + pose proof (sin_lt_x d Hd) as Hl. pose proof (SIN_bound d) as [Hb1 Hb2].
        rewrite Rabs_le_between. split; lra.
      + rewrite <- Hd. rewrite sin_0, Rabs_R0. lra.
    - rewrite (Rabs_left d Hd).
      pose proof (sin_lt_x (- d) ltac:(lra)) as Hl. pose proof (SIN_bound d) as [Hb1 Hb2].
      rewrite sin_neg in Hl.
      rewrite Rabs_le_between. split; lra. }
  assert (Hd2 : Rabs ((a - b) / 2) = Rabs (a - b) / 2).
  { unfold Rdiv. rewrite Rabs_mult, (Rabs_pos_eq (/ 2)) by lra. reflexivity. }
  rewrite Hd2 in Hs. nra.
Qed.

(** The exponent at a perturbed [S] against the exponent at [s], relative to
    the latter, for every [p] with [|p| <= r/2]. *)
Lemma Q_diff r p S s : 0 <= r -> Rabs p <= r / 2 -> Rabs S < 1 -> Rabs s < 1 ->
  Rabs (Qf r p S - Qf r p s) <= Rabs (S - s) / (1 - Rabs S) * Qf r p s.
Proof.
  intros Hr Hp HS Hs.
  apply Rabs_le_inv in Hp.
  pose proof (Rabs_pos S) as HSa. pose proof (Rabs_pos s) as Hsa.
  assert (HS1 : -1 < S < 1) by (apply Rabs_lt_between; exact HS).
  assert (Hs1 : -1 < s < 1) by (apply Rabs_lt_between; exact Hs).
  assert (HD1 : 0 < 1 - S * S) by nra.
  assert (HD2 : 0 < 1 - s * s) by nra.
  set (A := r / 2 * (S + s) - p * (1 + S * s)).
  assert (Hdiff : Qf r p S - Qf r p s = (S - s) * A / ((1 - S * S) * (1 - s * s))).
  { unfold Qf, A. field. split; lra. }
  set (a1 := r / 2 - p). set (a2 := r / 2 + p).
  assert (Ha1 : 0 <= a1) by (unfold a1; lra).
  assert (Ha2 : 0 <= a2) by (unfold a2; lra).
  assert (HA : A = a1 * (1 + S) * (1 + s) / 2 - a2 * (1 - S) * (1 - s) / 2).
  { unfold A, a1, a2. ring. }
  assert (HN : r / 2 - p * s = a1 * (1 + s) / 2 + a2 * (1 - s) / 2).
  { unfold a1, a2. ring. }
  assert (HAb : Rabs A <= (1 + Rabs S) * (r / 2 - p * s)).
  { rewrite HN. rewrite HA.
    assert (Hm : 1 + Rabs S >= 1 + S /\ 1 + Rabs S >= 1 - S).
    { split; [pose proof (Rle_abs S) | pose proof (Rle_abs (- S)); rewrite Rabs_Ropp in H]; lra. }
    destruct Hm as [Hm1 Hm2].
    rewrite Rabs_le_between. split; nra. }
  assert (HNp : 0 < r / 2 - p * s \/ r / 2 - p * s = 0).
  { assert (0 <= r / 2 - p * s) by (rewrite HN; nra). lra. }
  assert (HQ : Qf r p s = (r / 2 - p * s) / (1 - s * s)) by reflexivity.
  assert (HNN : 0 <= r / 2 - p * s) by (rewrite HN; nra).
  rewrite Hdiff, HQ.
  rewrite Rabs_div by nra. rewrite Rabs_mult.
  rewrite (Rabs_pos_eq ((1 - S * S) * (1 - s * s))) by nra.
  assert (H1S : 0 < 1 - Rabs S) by lra.
  assert (Hden : (1 - S * S) = (1 - Rabs S) * (1 + Rabs S)).
  { pose proof (Rabs_sq S). nra. }
  (* |S-s| |A| / ((1-S^2)(1-s^2)) <= |S-s|/(1-|S|) * N/(1-s^2) *)
  apply Rmult_le_reg_r with ((1 - S * S) * (1 - s * s)); [nra |].
  unfold Rdiv. rewrite Rmult_assoc, Rinv_l by nra. rewrite Rmult_1_r.
  assert (E : Rabs (S - s) * (1 / (1 - Rabs S)) * ((r / 2 - p * s) * / (1 - s * s)) * ((1 - S * S) * (1 - s * s))
            = Rabs (S - s) * (r / 2 - p * s) * (1 + Rabs S)).
  { rewrite Hden. field. split; lra. }
  replace (Rabs (S - s) / (1 - Rabs S)) with (Rabs (S - s) * (1 / (1 - Rabs S))) by (field; lra).
  rewrite E.
  pose proof (Rabs_pos (S - s)). nra.
Qed.
