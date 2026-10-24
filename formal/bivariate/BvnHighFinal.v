(** The last lines of the high-correlation branch under the documented [norm_cdf]
    contract (docs/bivariate_normal_high.md section 5): the result is
    [RN(Z)] with [|Z - Phi| <= 2^-112 Phi], and lies in [[0, 1]].  Combined with the
    integral's bound, the proved absolute error of the branch for each sign of the
    correlation. *)
From Coq Require Import Reals Lra Psatz ZArith Lia.
From Interval Require Import Tactic.
From Flocq Require Import Core.
Require Import BvnHighAssembly BvnHighRound BvnHighSteps BvnHighBudget.
Open Scope R_scope.

(** One [norm_cdf] value against [Phi]: [p = rnd Z], [p] in [[0, 1]], [|Z - Phi| <= tz]. *)
Definition tz : R := 1 / 10 ^ 33.

Lemma nc_err Z p Ph :
  0 <= Ph <= 1 -> p = rnd Z -> 0 <= p <= 1 -> Rabs (Z - Ph) <= tz -> Rabs (p - Ph) <= c54 + tz.
Proof.
  intros [HPh0 HPh1] Hp [Hp0 Hp1] HZ. pose proof c54_pos as Hc.
  destruct (Rlt_le_dec Z 0) as [Hn|Hn].
  - assert (p <= 0) by (rewrite Hp, <- rnd_0; apply rnd_le; lra).
    assert (p = 0) by lra.
    apply Rabs_le_inv in HZ. apply Rabs_le. split; lra.
  - destruct (Rlt_le_dec 1 Z) as [Hb|Hb].
    + assert (1 <= p) by (rewrite Hp, <- rnd_one; apply rnd_le; lra).
      assert (p = 1) by lra.
      apply Rabs_le_inv in HZ. apply Rabs_le. split; lra.
    + pose proof (rnd_err_unit Z (conj Hn Hb)) as Hr. rewrite <- Hp in Hr.
      pose proof (Rabs_triang (p - Z) (Z - Ph)) as Ht. replace (p - Z + (Z - Ph)) with (p - Ph) in Ht by ring. lra.
Qed.

(** Positive correlation: [p = nc(-max)]. *)
Theorem pos_final Pm G g p D ep :
  0 <= Pm - G <= 1 -> Rabs (g + G) <= D -> Rabs (p - Pm) <= ep ->
  Rabs (clamp (rnd (g + p)) - (Pm - G)) <= D + ep + c54.
Proof.
  intros HP Hg Hp.
  pose proof (round_clamp (g + p) (Pm - G) HP) as H.
  assert (Rabs (g + p - (Pm - G)) <= D + ep).
  { replace (g + p - (Pm - G)) with ((g + G) + (p - Pm)) by ring.
    eapply Rle_trans; [apply Rabs_triang|]. lra. }
  lra.
Qed.

Section Neg.
Variable ts : R -> R -> R * R.
Hypothesis Hts : forall a b, fst (ts a b) = rnd (a + b) /\ fst (ts a b) + snd (ts a b) = a + b.

(** Negative correlation when [Phi(-dh) > Phi(dk)]: [(hi, lo) = two_sum (p1, -p2)] and
    the result [hi + (lo + g)]. *)
Theorem neg_final_diff P1 P2 G g p1 p2 ep D :
  0 <= P2 -> P2 <= P1 -> P1 <= 1 -> 0 <= G -> Rabs (g - G) <= D -> - / 10 <= g <= / 10 ->
  0 <= G + (P1 - P2) <= 1 -> Rabs (p1 - P1) <= ep -> Rabs (p2 - P2) <= ep -> ep <= / 100 ->
  let hl := ts p1 (- p2) in
  Rabs (clamp (rnd (fst hl + rnd (snd hl + g))) - (G + (P1 - P2))) <= D + 2 * ep + 9 / 8 * c54.
Proof.
  intros H0 H1 H2 HG Hg Hg01 HP Hp1 Hp2 Hep hl.
  pose proof c54_pos as Hc. pose proof c54_small as Hsm.
  destruct (Hts p1 (- p2)) as [E1 E2]. fold hl in E1, E2.
  set (y := p1 + - p2) in *.
  assert (Hy : Rabs y <= 1 + 2 * ep).
  { unfold y. apply Rabs_le_inv in Hp1. apply Rabs_le_inv in Hp2. apply Rabs_le. split; lra. }
  pose proof (rnd_abs y) as Hr. rewrite <- E1 in Hr.
  assert (Hlo : Rabs (snd hl) <= u * (1 + 2 * ep) + eta).
  { replace (snd hl) with (- (fst hl - y)) by lra. rewrite Rabs_Ropp.
    assert (u * Rabs y <= u * (1 + 2 * ep)) by (apply Rmult_le_compat_l; [apply Rlt_le; apply u_pos | lra]). lra. }
  assert (Hub : u * (1 + 2 * ep) + eta <= 1 / 50).
  { pose proof u_pos as Hu. pose proof u_lt as Hu2. pose proof eta_small as Hη. pose proof (Rabs_pos (p1 - P1)) as Hep0.
    assert (u * (1 + 2 * ep) <= 12 / 10 ^ 17 * (1 + 2 * (1 / 100))) by (apply Rmult_le_compat; [lra | lra | lra | lra]).
    assert (12 / 10 ^ 17 * (1 + 2 * (1 / 100)) + / 10 ^ 300 <= 1 / 50) by interval. lra. }
  assert (Heg : Rabs (snd hl + g) < / 8).
  { pose proof (Rabs_le_inv _ _ Hlo) as [A B]. apply Rabs_lt. lra. }
  pose proof (rnd_err_eighth _ Heg) as Hy8.
  set (T := G + (P1 - P2)) in *.
  pose proof (round_clamp (fst hl + rnd (snd hl + g)) T HP) as Hfin.
  assert (Hx : Rabs (fst hl + rnd (snd hl + g) - T) <= D + 2 * ep + c54 / 8).
  { assert (Hv : fst hl + rnd (snd hl + g) - T
      = (g - G) + (p1 - P1) - (p2 - P2) + (rnd (snd hl + g) - (snd hl + g))).
    { unfold T. replace (fst hl) with (y - snd hl) by lra. unfold y. ring. }
    rewrite Hv.
    pose proof (Rabs_triang ((g - G) + (p1 - P1) - (p2 - P2)) (rnd (snd hl + g) - (snd hl + g))) as T1.
    pose proof (Rabs_triang ((g - G) + (p1 - P1)) (- (p2 - P2))) as T2.
    pose proof (Rabs_triang (g - G) (p1 - P1)) as T3. rewrite Rabs_Ropp in T2.
    replace ((g - G) + (p1 - P1) + - (p2 - P2)) with ((g - G) + (p1 - P1) - (p2 - P2)) in T2 by ring.
    lra. }
  lra.
Qed.
End Neg.

(** Negative correlation when [Phi(-dh) <= Phi(dk)]: the result is [clamp g]. *)
Theorem neg_final_zero G g D :
  0 <= G <= 1 -> Rabs (g - G) <= D -> Rabs (clamp g - G) <= D.
Proof.
  intros HG Hg. pose proof (clamp_lipschitz g G) as H. rewrite (clamp_in G HG) in H. lra.
Qed.

(** The integral's computed value against the exact, and the division by [TAU]. *)
Theorem div_final Jt J dJ :
  0 <= J <= 21 / 50 -> Rabs (Jt - J) <= dJ -> dJ <= 1 / 1000 ->
  Rabs (rnd (- Jt / TAU) + J / (2 * PI)) <= 1593 / 10000 * dJ + 1 / 10 ^ 17 /\ Rabs (rnd (- Jt / TAU)) <= 1 / 10.
Proof.
  intros HJ Hd HdJ. split.
  - pose proof (division_step Jt J dJ HJ Hd HdJ) as H.
    replace (rnd (- Jt / TAU) + J / (2 * PI)) with (rnd (- Jt / TAU) - (- (J / (2 * PI)))) by ring. exact H.
  - exact (g_small Jt J dJ HJ Hd HdJ).
Qed.

(** The proved bounds, [dJ = 9.4e-16]. *)
Definition dJ : R := 94 / 10 ^ 17.
Definition D_div : R := 1593 / 10000 * dJ + 1 / 10 ^ 17.

Lemma bound_pos_value : D_div + (c54 + tz) + c54 <= 2708 / 10 ^ 19.
Proof. unfold D_div, dJ, tz. rewrite c54_value. interval. Qed.

Lemma bound_neg_value : D_div + 2 * (c54 + tz) + 9 / 8 * c54 <= 3333 / 10 ^ 19.
Proof. unfold D_div, dJ, tz. rewrite c54_value. interval. Qed.
