(** The high-correlation branch, end to end (docs/bivariate_normal_high.md section 6):
    the certificate constants, the closed form's bound on the last scale, and the
    proved absolute error of the branch for each sign of the correlation. *)
From Coq Require Import Reals Lra Psatz ZArith Lia.
From Interval Require Import Tactic.
From Flocq Require Import Core.
Require Import BvnHighAssembly BvnHighRound BvnHighSteps BvnHighBudget BvnHighPanels BvnHighFinal.
Open Scope R_scope.

(** The closed form's value [Cl] (zero where the kernel skips it) against the integral over
    [[0, s]]. *)
Lemma closed_total Cl I0 s ck :
  0 <= s -> s <= 3 / 1000 ->
  Rabs (ck - Cl) <= 15 / 10 ^ 17 -> Rabs (I0 - Cl) <= 72 / 10 * s ^ 7 / 7 ->
  Rabs (ck - I0) <= 161 / 10 ^ 18.
Proof.
  intros H0 H1 Hc Ht. pose proof (tail_monotone s H0 H1) as Hm. pose proof tail_constant as Hk.
  pose proof (Rabs_triang (ck - Cl) (Cl - I0)) as T. replace (ck - Cl + (Cl - I0)) with (ck - I0) in T by ring.
  rewrite Rabs_minus_sym in Ht.
  assert (Hq : 23 / 10 ^ 19 <= 11 / 10 ^ 18) by interval.
  assert (Hr : 15 / 10 ^ 17 + 11 / 10 ^ 18 = 161 / 10 ^ 18) by field. lra.
Qed.

(** The closed form with the remainder correction added ([closed_form] of the kernel from [HK_SPLIT]
    on): the correction is within [2^-66] (it is discarded otherwise), and its addition rounds. *)
Lemma closed_total_rem Cl I0 s ck r :
  0 <= s -> s <= 3 / 1000 ->
  Rabs (ck - Cl) <= 15 / 10 ^ 17 -> Rabs (I0 - Cl) <= 72 / 10 * s ^ 7 / 7 -> 0 <= I0 <= 4 / 1000 ->
  Rabs r <= 2 / 10 ^ 20 ->
  Rabs (rnd (ck + r) - I0) <= 161 / 10 ^ 18.
Proof.
  intros H0 H1 Hc Ht [HI0 HI1] Hr.
  pose proof u_pos as Hu. pose proof u_lt as Hu2. pose proof eta_small as Hη.
  pose proof (tail_monotone s H0 H1) as Hm. pose proof tail_constant as Hk.
  pose proof Hr as Hr'.
  pose proof (Rabs_triang (ck - Cl) (Cl - I0)) as T. replace (ck - Cl + (Cl - I0)) with (ck - I0) in T by ring.
  rewrite Rabs_minus_sym in Ht.
  assert (Hck : Rabs (ck - I0) <= 15 / 10 ^ 17 + 23 / 10 ^ 19) by (assert (72 / 10 * s ^ 7 / 7 <= 72 / 10 * (3 / 1000) ^ 7 / 7) by lra; lra).
  assert (Hck2 : Rabs (ck + r) <= 5 / 1000).
  { pose proof (Rabs_triang (ck - I0) I0) as T2. replace (ck - I0 + I0) with ck in T2 by ring.
    rewrite (Rabs_right I0) in T2 by lra.
    pose proof (Rabs_triang ck r) as T3.
    assert (15 / 10 ^ 17 + 23 / 10 ^ 19 + 2 / 10 ^ 20 <= 1 / 1000) by interval. lra. }
  pose proof (rnd_abs (ck + r)) as Hra.
  assert (Hu5 : u * Rabs (ck + r) <= u * (5 / 1000)) by (apply Rmult_le_compat_l; lra).
  assert (Hu6 : u * (5 / 1000) <= 1 / 10 ^ 18) by (assert (12 / 10 ^ 17 * (5 / 1000) <= 1 / 10 ^ 18) by interval; nra).
  assert (Hη2 : eta <= 1 / 10 ^ 290) by (assert (/ 10 ^ 300 <= 1 / 10 ^ 290) by interval; lra).
  pose proof (Rabs_triang (rnd (ck + r) - (ck + r)) (ck + r - I0)) as T4.
  replace (rnd (ck + r) - (ck + r) + (ck + r - I0)) with (rnd (ck + r) - I0) in T4 by ring.
  pose proof (Rabs_triang (ck - I0) r) as T5. replace (ck - I0 + r) with (ck + r - I0) in T5 by ring.
  assert (Hfin : 15 / 10 ^ 17 + 23 / 10 ^ 19 + 2 / 10 ^ 20 + 1 / 10 ^ 18 + 1 / 10 ^ 290 <= 161 / 10 ^ 18) by interval.
  lra.
Qed.

Lemma closed_skip I0 :
  Rabs I0 <= 1 / 10 ^ 45 -> Rabs (0 - I0) <= 161 / 10 ^ 18.
Proof.
  intros H. rewrite Rabs_minus_sym. replace (I0 - 0) with I0 by ring.
  assert (1 / 10 ^ 45 <= 161 / 10 ^ 18) by interval. lra.
Qed.

Section End.
Variables nc Phi : R -> R.
Variable ts : R -> R -> R * R.
Hypothesis Hts : forall a b, fst (ts a b) = rnd (a + b) /\ fst (ts a b) + snd (ts a b) = a + b.
(** The documented [norm_cdf] contract: its result is [RN(Z)] with [|Z - Phi| <= 2^-112 Phi],
    in [[0, 1]]. *)
Hypothesis Hcon : forall x, exists Z, nc x = rnd Z /\ Rabs (Z - Phi x) <= tz.
Hypothesis Hrg : forall x, 0 <= nc x <= 1.
Hypothesis PhiRg : forall x, 0 <= Phi x <= 1.
Hypothesis PhiMono : forall x y, x <= y -> Phi x <= Phi y.

Lemma nc_close x : Rabs (nc x - Phi x) <= c54 + tz.
Proof.
  destruct (Hcon x) as [Z [H1 H2]]. exact (nc_err Z (nc x) (Phi x) (PhiRg x) H1 (Hrg x) H2).
Qed.

(** [rho > 0]: [P = Phi(-max) - J / 2 pi]; the result [clamp (rnd (-Jk / TAU + nc (-max)))]. *)
Theorem high_pos_end xm Jk J :
  0 <= J <= 21 / 50 -> Rabs (Jk - J) <= dJ -> 0 <= Phi xm - J / (2 * PI) <= 1 ->
  Rabs (clamp (rnd (rnd (- Jk / TAU) + nc xm)) - (Phi xm - J / (2 * PI))) <= 2708 / 10 ^ 19.
Proof.
  intros HJ Hd HP.
  assert (HdJ : dJ <= 1 / 1000) by (unfold dJ; interval).
  destruct (div_final Jk J dJ HJ Hd HdJ) as [Hg _].
  replace (rnd (- Jk / TAU)) with (rnd (- Jk / TAU)) by reflexivity.
  pose proof (pos_final (Phi xm) (J / (2 * PI)) (rnd (- Jk / TAU)) (nc xm) D_div (c54 + tz) HP Hg (nc_close xm)) as H.
  pose proof bound_pos_value as Hv. lra.
Qed.

(** [rho < 0], [Phi(-dh) > Phi(dk)]. *)
Theorem high_neg_end_diff dh dk Jk J :
  0 <= J <= 21 / 50 -> Rabs (Jk - J) <= dJ -> Phi dk <= Phi (- dh) ->
  0 <= J / (2 * PI) + (Phi (- dh) - Phi dk) <= 1 ->
  let g := - rnd (- Jk / TAU) in
  let hl := ts (nc (- dh)) (- nc dk) in
  Rabs (clamp (rnd (fst hl + rnd (snd hl + g))) - (J / (2 * PI) + (Phi (- dh) - Phi dk))) <= 3333 / 10 ^ 19.
Proof.
  intros HJ Hd Hm HP g hl.
  assert (HdJ : dJ <= 1 / 1000) by (unfold dJ; interval).
  destruct (div_final Jk J dJ HJ Hd HdJ) as [Hg Hgs].
  pose proof PI_RGT_0 as Hpi.
  assert (HG : 0 <= J / (2 * PI)) by (apply Rmult_le_pos; [lra | left; apply Rinv_0_lt_compat; lra]).
  assert (Hg' : Rabs (g - J / (2 * PI)) <= D_div).
  { unfold g, D_div, dJ. replace (- rnd (- Jk / TAU) - J / (2 * PI)) with (- (rnd (- Jk / TAU) + J / (2 * PI))) by ring.
    rewrite Rabs_Ropp. exact Hg. }
  assert (Hgb : - / 10 <= g <= / 10) by (unfold g; pose proof (Rabs_le_inv _ _ Hgs) as [A B]; lra).
  assert (Hep : c54 + tz <= / 100) by (rewrite c54_value; unfold tz; interval).
  pose proof (PhiRg (- dh)) as [A1 A2]. pose proof (PhiRg dk) as [B1 B2].
  pose proof (neg_final_diff ts Hts (Phi (- dh)) (Phi dk) (J / (2 * PI)) g (nc (- dh)) (nc dk) (c54 + tz) D_div
    B1 Hm A2 HG Hg' Hgb HP (nc_close (- dh)) (nc_close dk) Hep) as H.
  cbv zeta in H. fold hl in H.
  pose proof bound_neg_value as Hv. lra.
Qed.

(** [rho < 0], [Phi(-dh) <= Phi(dk)]: the result is [clamp g]. *)
Theorem high_neg_end_zero dh dk Jk J :
  0 <= J <= 21 / 50 -> Rabs (Jk - J) <= dJ -> Phi (- dh) <= Phi dk ->
  0 <= J / (2 * PI) <= 1 ->
  Rabs (clamp (- rnd (- Jk / TAU)) - (J / (2 * PI) + Rmax 0 (Phi (- dh) - Phi dk))) <= 3333 / 10 ^ 19.
Proof.
  intros HJ Hd Hm HP.
  assert (HdJ : dJ <= 1 / 1000) by (unfold dJ; interval).
  destruct (div_final Jk J dJ HJ Hd HdJ) as [Hg _].
  assert (E : Rmax 0 (Phi (- dh) - Phi dk) = 0) by (unfold Rmax; destruct (Rle_dec 0 (Phi (- dh) - Phi dk)); lra).
  rewrite E, Rplus_0_r.
  assert (Hg' : Rabs (- rnd (- Jk / TAU) - J / (2 * PI)) <= D_div).
  { unfold D_div, dJ. replace (- rnd (- Jk / TAU) - J / (2 * PI)) with (- (rnd (- Jk / TAU) + J / (2 * PI))) by ring.
    rewrite Rabs_Ropp. exact Hg. }
  pose proof (neg_final_zero (J / (2 * PI)) (- rnd (- Jk / TAU)) D_div HP Hg') as H.
  pose proof bound_neg_value as Hv. pose proof c54_pos. unfold tz in Hv. lra.
Qed.
End End.
