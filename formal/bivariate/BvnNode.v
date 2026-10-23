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
Lemma sin_lip_lt a b : a < b -> Rabs (sin b - sin a) <= Rabs (b - a).
Proof.
  intros H.
  destruct (MVT_cor2 sin cos a b H (fun c _ => derivable_pt_lim_sin c)) as [c [E _]].
  rewrite E, Rabs_mult.
  assert (Hc : Rabs (cos c) <= 1) by (apply Rabs_le; apply COS_bound).
  pose proof (Rabs_pos (b - a)). nra.
Qed.

Lemma sin_lip a b : Rabs (sin a - sin b) <= Rabs (a - b).
Proof.
  destruct (Rtotal_order a b) as [H | [H | H]].
  - pose proof (sin_lip_lt a b H). rewrite Rabs_minus_sym. rewrite (Rabs_minus_sym a b). exact H0.
  - subst. replace (sin b - sin b) with 0 by ring. rewrite Rabs_R0. apply Rabs_pos.
  - exact (sin_lip_lt b a H).
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
  { unfold A, a1, a2. field. }
  assert (HN : r / 2 - p * s = a1 * (1 + s) / 2 + a2 * (1 - s) / 2).
  { unfold a1, a2. field. }
  assert (Hs1p : 0 <= 1 + s) by lra.
  assert (Hs1m : 0 <= 1 - s) by lra.
  assert (HSa1 : 0 <= Rabs S - S) by (pose proof (Rle_abs S); lra).
  assert (HSa2 : 0 <= Rabs S + S) by (pose proof (Rle_abs (- S)); rewrite Rabs_Ropp in H; lra).
  assert (T1 : 0 <= a1 * (1 + s) * (Rabs S - S)) by (apply Rmult_le_pos; [apply Rmult_le_pos |]; assumption).
  assert (T2 : 0 <= a2 * (1 - s) * (2 + Rabs S - S)) by (apply Rmult_le_pos; [apply Rmult_le_pos | lra]; assumption).
  assert (T3 : 0 <= a1 * (1 + s) * (2 + Rabs S + S)) by (apply Rmult_le_pos; [apply Rmult_le_pos | lra]; assumption).
  assert (T4 : 0 <= a2 * (1 - s) * (Rabs S + S)) by (apply Rmult_le_pos; [apply Rmult_le_pos |]; assumption).
  assert (HAb : Rabs A <= (1 + Rabs S) * (r / 2 - p * s)).
  { rewrite HN. rewrite HA.
    rewrite Rabs_le_between. split; nra. }
  assert (HQ : Qf r p s = (r / 2 - p * s) / (1 - s * s)) by reflexivity.
  assert (HNN : 0 <= r / 2 - p * s).
  { rewrite HN. assert (0 <= a1 * (1 + s)) by (apply Rmult_le_pos; assumption).
    assert (0 <= a2 * (1 - s)) by (apply Rmult_le_pos; assumption). lra. }
  rewrite Hdiff, HQ.
  assert (HD : 0 < (1 - S * S) * (1 - s * s)) by nra.
  rewrite Rabs_div_pos by exact HD. rewrite Rabs_mult.
  assert (H1S : 0 < 1 - Rabs S) by lra.
  assert (Hden : 1 - S * S = (1 - Rabs S) * (1 + Rabs S)).
  { pose proof (Rabs_sq S). nra. }
  assert (Hstep : Rabs (S - s) * Rabs A / ((1 - S * S) * (1 - s * s))
                  <= Rabs (S - s) * ((1 + Rabs S) * (r / 2 - p * s)) / ((1 - S * S) * (1 - s * s))).
  { unfold Rdiv. apply Rmult_le_compat_r; [apply Rlt_le, Rinv_0_lt_compat; exact HD |].
    apply Rmult_le_compat_l; [apply Rabs_pos | exact HAb]. }
  eapply Rle_trans; [exact Hstep |].
  right. rewrite Hden. field. split; [lra | split; [lra | lra]].
Qed.
