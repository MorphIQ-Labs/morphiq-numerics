(** The accurate path's Newton step for [atan (n/d)]: with [t = n/d], the exact step
    from a start [r] is [r + tan (atan t - r)] and its truncation error is cubic. *)
From Coq Require Import Reals ZArith Lia Lra Psatz Rtrigo_calc.
From Flocq Require Import Core.
From Interval Require Import Tactic.
Require Import AsinFacts AsinSeries Atan2Within.
Open Scope R_scope.

Lemma atan_small_pos x : 0 < x < / 10 -> - (x * x * x / 3) <= atan x - x <= 0.
Proof.
  intros [H0 H1]. assert (Hq : 0 < x < 1) by lra.
  pose proof (atan_taylor x Hq) as T. apply Rabs_le_inv in T.
  assert (X2 : 0 < x * x <= / 100) by (split; nra).
  assert (X3 : 0 < x * x * x) by (apply Rmult_lt_0_compat; [nra | lra]).
  assert (E5 : x * x * x * x * x = (x * x * x) * (x * x)) by ring.
  assert (E7 : x * x * x * x * x * x * x = (x * x * x) * ((x * x) * (x * x))) by ring.
  assert (X4 : (x * x) * (x * x) <= / 100 * (x * x)) by nra.
  set (a := x * x * x) in *. set (u := x * x) in *.
  split; nra.
Qed.

Lemma atan_small w : Rabs w <= / 100000 -> Rabs (atan w - w) <= Rabs w * Rabs w * Rabs w / 3.
Proof.
  intros H. destruct (Rtotal_order w 0) as [Hn | [Hz | Hp]].
  - assert (Hq : 0 < - w < / 10) by (apply Rabs_le_inv in H; lra).
    pose proof (atan_small_pos (- w) Hq) as T. rewrite atan_opp in T.
    rewrite (Rabs_left w Hn). assert (E : - w * - w * - w = - (w * w * w)) by ring. rewrite E. apply Rabs_le.
    assert (E2 : - w * - w * - w = - (w * w * w)) by ring. rewrite E2 in T. split; lra.
  - subst w. rewrite atan_0. replace (0 - 0) with 0 by ring. rewrite !Rabs_R0. lra.
  - assert (Hq : 0 < w < / 10) by (apply Rabs_le_inv in H; lra).
    pose proof (atan_small_pos w Hq) as T. rewrite (Rabs_pos_eq w) by lra. apply Rabs_le. split; lra.
Qed.

(** The exact step: [t cos r - sin r = w (cos r + t sin r)] with [w = tan (atan t - r)]. *)
Lemma newton_exact t r : 0 < t -> Rabs (atan t - r) <= / 1000000 ->
  exists w, t * cos r - sin r = w * (cos r + t * sin r) /\ 0 < cos r + t * sin r /\
    Rabs (atan t - r - w) <= Rabs w * Rabs w * Rabs w / 3 /\ Rabs w <= 1.0001 * Rabs (atan t - r).
Proof.
  intros Ht Hd.
  set (Y := atan t) in *. set (dl := Y - r).
  pose proof Hd as Hdi. apply Rabs_le_inv in Hdi as [Hd1 Hd2'].
  pose proof (atan_bound t) as [Yl Yh]. fold Y in Yl, Yh.
  pose proof (cos_gt_0 Y ltac:(lra) ltac:(lra)) as CY.
  assert (HtY : sin Y = t * cos Y).
  { pose proof (tan_atan t) as T. fold Y in T. unfold tan in T.
    assert (Hnz : cos Y <> 0) by lra. apply (Rmult_eq_compat_r (cos Y)) in T. unfold Rdiv in T. rewrite Rmult_assoc, Rinv_l, Rmult_1_r in T by exact Hnz. exact T. }
  assert (Hs : sin dl = cos Y * (t * cos r - sin r)) by (unfold dl; rewrite sin_minus, HtY; ring).
  assert (Hc : cos dl = cos Y * (cos r + t * sin r)) by (unfold dl; rewrite cos_minus, HtY; ring).
  assert (Hdl1 : Rabs dl <= 1).
  { unfold dl. apply Rabs_le. split; lra. }
  pose proof (cos_taylor dl Hdl1) as [Cl Cu].
  assert (Hd2 : dl * dl <= / 1000000000000).
  { unfold dl in *. nra. }
  assert (Cpos : 0.99999 <= cos dl) by lra.
  assert (Dpos : 0 < cos r + t * sin r).
  { apply Rmult_lt_reg_l with (cos Y); [exact CY | ]. rewrite <- Hc. lra. }
  set (w := sin dl / cos dl).
  assert (Hw : t * cos r - sin r = w * (cos r + t * sin r)).
  { unfold w. rewrite Hs, Hc. field. split; lra. }
  assert (Hsd : Rabs (sin dl) <= 1.00001 * Rabs dl).
  { pose proof (sin_taylor dl ltac:(unfold dl; apply Rabs_le; lra)) as T.
    pose proof (Rabs_pos dl).
    assert (Rabs (sin dl) <= Rabs dl + dl * dl * Rabs dl / 6).
    { replace (sin dl) with (dl + (sin dl - dl)) by ring. apply Rle_trans with (Rabs dl + Rabs (sin dl - dl)); [apply Rabs_triang | lra]. }
    nra. }
  assert (Hwb : Rabs w <= 1.0001 * Rabs dl).
  { unfold w. unfold Rdiv. rewrite Rabs_mult, Rabs_Rinv by lra. rewrite (Rabs_pos_eq (cos dl)) by lra.
    pose proof (Rabs_pos dl). pose proof (Rabs_pos (sin dl)).
    assert (Hi : / cos dl <= 1.00002) by (apply Rmult_le_reg_l with (cos dl); [lra | rewrite Rinv_r by lra; nra]).
    assert (Hi0 : 0 < / cos dl) by (apply Rinv_0_lt_compat; lra).
    nra. }
  assert (Hws : Rabs w <= / 100000).
  { apply Rle_trans with (1.0001 * Rabs dl); [exact Hwb | ]. unfold dl. nra. }
  assert (Hdw : dl = atan w).
  { apply tan_inj; [ | apply atan_bound | ].
    - pose proof pi_gt_3 as PP. unfold dl in *. split; lra.
    - rewrite tan_atan. unfold w, tan. reflexivity. }
  exists w. refine (conj Hw (conj Dpos (conj _ Hwb))).
  pose proof (atan_small w Hws) as Hfin. rewrite <- Hdw in Hfin.
  change (Y - r - w) with (dl - w). exact Hfin.
Qed.
