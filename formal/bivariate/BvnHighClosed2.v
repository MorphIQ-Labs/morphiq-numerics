(** Rounding of Genz's closed form on the last scale, second part: the leaves of
    the second term -- [exp(-hk/2)], [SQRT_TAU], [sqrt(bs)] and [norm_cdf(-b/s)]
    (docs/bivariate_normal_high.md section 4.4). *)
From Coq Require Import Reals Lra Psatz ZArith Lia.
From Interval Require Import Tactic.
From Flocq Require Import Core.
Require Import BvnHighAssembly BvnHighRound BvnHighSteps BvnHighBudget BvnHighErr BvnHighErrTree BvnHighClosed.
Open Scope R_scope.

Lemma S_leaf : ab (sqrt (2 * PI)) SQRT_TAU (2507 / 1000) (2 / 10 ^ 16).
Proof.
  pose proof sqrt_tau_error as H.
  assert (Hs : sqrt (2 * PI) <= 2507 / 1000) by interval.
  assert (Hs0 : 0 <= sqrt (2 * PI)) by apply sqrt_pos.
  unfold ab. split.
  - rewrite Rabs_right by lra. exact Hs.
  - assert (74 / 10 ^ 18 * sqrt (2 * PI) <= 74 / 10 ^ 18 * (2507 / 1000)) by (apply Rmult_le_compat_l; [interval | exact Hs]).
    assert (74 / 10 ^ 18 * (2507 / 1000) <= 2 / 10 ^ 16) by interval.
    lra.
Qed.

Section Leaves.
Variable expT sqrtT : R -> R.
Hypothesis Hex7 : forall x, -700 <= x -> x <= 1 -> rel (exp x) (expT x) u.
Hypothesis Hsq0 : forall x, 0 <= x -> rel (sqrt x) (sqrtT x) u.

(** [exp(-hk/2)] for [hk] in [[-9.1e-4, 100]] known to a relative error [u]. *)
Lemma eh_leaf hk hkT e0 :
  - (91 / 100000) <= hk -> hk <= 100 -> 0 <= e0 <= / 10 ^ 200 -> rela hk hkT u e0 ->
  ab (exp (- (hk / 2))) (expT (- (hkT / 2))) (10005 / 10000) (15 / 10 * u).
Proof.
  intros Hl Hh [He0 He1] Hr. pose proof u_pos as Hu. pose proof u_lt as Hu2.
  unfold rela in Hr.
  assert (Hhk : Rabs hk <= 100) by (apply Rabs_le; lra).
  set (D := (u * Rabs hk + e0) / 2).
  assert (HD0 : 0 <= D) by (unfold D; assert (0 <= u * Rabs hk) by (apply Rmult_le_pos; [lra | apply Rabs_pos]); lra).
  assert (HDs : D <= 1 / 10 ^ 12).
  { unfold D. assert (u * Rabs hk <= u * 100) by (apply Rmult_le_compat_l; lra).
    assert (u * 100 <= 12 / 10 ^ 17 * 100) by (apply Rmult_le_compat_r; lra).
    assert (12 / 10 ^ 17 * 100 + / 10 ^ 200 <= 2 / 10 ^ 12) by interval. lra. }
  assert (HDh : D <= 1 / 2) by (assert (1 / 10 ^ 12 <= 1 / 2) by interval; lra).
  assert (Hd : Rabs (hkT / 2 - hk / 2) <= D).
  { replace (hkT / 2 - hk / 2) with ((hkT - hk) / 2) by field. unfold Rdiv. rewrite Rabs_mult, (Rabs_right (/ 2)) by lra.
    unfold D. unfold Rdiv. lra. }
  pose proof (exp_pert (hk / 2) (hkT / 2) D Hd HD0 HDh) as Hp1.
  pose proof (Rabs_le_inv _ _ Hd) as [Hd1 Hd2].
  assert (Hr1 : -700 <= - (hkT / 2)) by lra.
  assert (Hr2 : - (hkT / 2) <= 1) by lra.
  pose proof (Hex7 (- (hkT / 2)) Hr1 Hr2) as Hp1b.
  pose proof (rel_trans (exp (- (hk / 2))) (exp (- (hkT / 2))) (expT (- (hkT / 2))) (D + 2 * (D * D)) u ltac:(nra) (Rlt_le _ _ Hu) Hp1 Hp1b) as Hp2.
  unfold ab, rel in *.
  set (E := exp (- (hk / 2))) in *.
  assert (HEpos : 0 < E) by apply exp_pos.
  assert (HE1 : E <= 10005 / 10000).
  { assert (Hx : - (hk / 2) <= 455 / 1000000) by lra.
    assert (exp (455 / 1000000) <= 10005 / 10000) by interval.
    assert (E <= exp (455 / 1000000)).
    { unfold E. destruct (Rle_lt_or_eq_dec _ _ Hx) as [Hl2|Heq]; [left; apply exp_increasing; exact Hl2 | right; f_equal; exact Heq]. }
    lra. }
  split.
  - rewrite Rabs_right by lra. exact HE1.
  - rewrite (Rabs_right E) in Hp2 by lra.
    assert (HED : E * D <= 37 / 100 * u + E * (e0 / 2)).
    { unfold D. replace (E * ((u * Rabs hk + e0) / 2)) with (u * (E * (Rabs hk / 2)) + E * (e0 / 2)) by field.
      destruct (Rle_dec 0 hk) as [Hk|Hk].
      - rewrite (Rabs_right hk) by lra.
        pose proof (xe_bound (hk / 2) ltac:(lra)) as Hx.
        assert (Hc : (hk / 2) * E <= 3679 / 10000) by exact Hx.
        assert (Hm : E * (hk / 2) = (hk / 2) * E) by ring.
        assert (u * (E * (hk / 2)) <= u * (3679 / 10000)) by (apply Rmult_le_compat_l; [lra | lra]). lra.
      - rewrite (Rabs_left hk) by lra.
        assert (E * (- hk / 2) <= 10005 / 10000 * (455 / 1000000)) by (apply Rmult_le_compat; [lra | lra | lra | lra]).
        assert (u * (E * (- hk / 2)) <= u * (10005 / 10000 * (455 / 1000000))) by (apply Rmult_le_compat_l; [lra | lra]).
        assert (u * (10005 / 10000 * (455 / 1000000)) <= 1 / 100 * u) by nra. lra. }
    assert (He0E : E * (e0 / 2) <= 1 / 10 ^ 100 * u).
    { assert (E * (e0 / 2) <= 10005 / 10000 * (/ 10 ^ 200 / 2)) by (apply Rmult_le_compat; [lra | lra | lra | lra]).
      assert (10005 / 10000 * (/ 10 ^ 200 / 2) <= 1 / 10 ^ 100 * u) by (rewrite u_value; interval). lra. }
    assert (HDD : D * D <= D * (1 / 10 ^ 12)) by (apply Rmult_le_compat_l; lra).
    assert (Hth : (D + 2 * (D * D)) + u * (1 + (D + 2 * (D * D))) <= D + 2 * (D * (1 / 10 ^ 12)) + u * (1 + 1 / 10 ^ 11)).
    { assert (HD1 : D + 2 * (D * D) <= 1 / 10 ^ 11).
      { assert (D * (1 / 10 ^ 12) <= 1 / 10 ^ 12 * (1 / 10 ^ 12)) by (apply Rmult_le_compat_r; [interval | lra]).
        assert (1 / 10 ^ 12 * (1 / 10 ^ 12) <= 1 / 10 ^ 13) by interval.
        assert (1 / 10 ^ 12 + 2 * (1 / 10 ^ 13) <= 1 / 10 ^ 11) by interval. lra. }
      assert (u * (1 + (D + 2 * (D * D))) <= u * (1 + 1 / 10 ^ 11)) by (apply Rmult_le_compat_l; lra). lra. }
    assert (Hm : (D + 2 * (D * D) + u * (1 + (D + 2 * (D * D)))) * E <= (D + 2 * (D * (1 / 10 ^ 12)) + u * (1 + 1 / 10 ^ 11)) * E) by (apply Rmult_le_compat_r; lra).
    assert (E2 : (D + 2 * (D * (1 / 10 ^ 12)) + u * (1 + 1 / 10 ^ 11)) * E = E * D * (1 + 2 / 10 ^ 12) + (1 + 1 / 10 ^ 11) * (u * E)) by field.
    assert (Hu3 : (1 + 1 / 10 ^ 11) * (u * E) <= (1 + 1 / 10 ^ 11) * (u * (10005 / 10000))).
    { apply Rmult_le_compat_l; [interval | apply Rmult_le_compat_l; lra]. }
    assert (Hk1 : E * D * (1 + 2 / 10 ^ 12) <= (37 / 100 * u + E * (e0 / 2)) * (1 + 2 / 10 ^ 12)) by (apply Rmult_le_compat_r; [interval | lra]).
    assert (Hk2 : (37 / 100 * u + 1 / 10 ^ 100 * u) * (1 + 2 / 10 ^ 12) + (1 + 1 / 10 ^ 11) * (u * (10005 / 10000)) <= 15 / 10 * u).
    { assert ((37 / 100 + 1 / 10 ^ 100) * (1 + 2 / 10 ^ 12) + (1 + 1 / 10 ^ 11) * (10005 / 10000) <= 15 / 10) by interval. nra. }
    assert (Hk3 : (37 / 100 * u + E * (e0 / 2)) * (1 + 2 / 10 ^ 12) <= (37 / 100 * u + 1 / 10 ^ 100 * u) * (1 + 2 / 10 ^ 12)) by (apply Rmult_le_compat_r; [interval | lra]).
    nra.
Qed.
End Leaves.

(** The normal CDF: the properties of the exact function that the closed form's
    error analysis uses.  [Phi x = P(Z <= x)]; the three properties are
    classical (the density is [exp(-x^2/2)/sqrt(2 pi)] and decreasing in [|x|]). *)
Section PhiLeaf.
Variable sqrtT nc Phi : R -> R.
Hypothesis Hsq0 : forall x, 0 <= x -> rel (sqrt x) (sqrtT x) u.
(** [norm_cdf]'s documented contract: relative [2^-53 + 2^-111], absolute [2^-1075]. *)
Hypothesis Hnc : forall x, x <= 0 -> Rabs (nc x - Phi x) <= (u + bpow radix2 (-111)) * Phi x + eta.
Hypothesis PhiA : forall x, x <= 0 -> 0 <= Phi x <= 1 / 2.
Hypothesis PhiL : forall x1 x2, x1 <= 0 -> x2 <= 0 ->
  Rabs (Phi x1 - Phi x2) <= Rabs (x1 - x2) * exp (- (Rmin (- x1) (- x2) * Rmin (- x1) (- x2) / 2)) / (25066 / 10000).

Lemma b_rel bs bsT e0 :
  0 <= bs -> 0 <= bsT -> 0 <= e0 <= / 10 ^ 200 -> Rabs (bsT - bs) <= 31 / 10 * u * bs + e0 ->
  Rabs (sqrtT bsT - sqrt bs) <= 43 / 10 * u * sqrt bs + 3 / 10 ^ 100.
Proof.
  intros Hb Hb' He H. pose proof u_pos as Hu. pose proof u_lt as Hu2.
  pose proof (sqrt_rela bs bsT e0 Hb Hb' He H) as Hs.
  pose proof (Hsq0 bsT Hb') as Hc. unfold rel in Hc. pose proof (sqrt_pos bsT) as S'. pose proof (sqrt_pos bs) as S.
  rewrite (Rabs_right (sqrt bsT)) in Hc by lra.
  apply Rabs_le_inv in Hs. destruct Hs as [Hs1 Hs2].
  apply Rabs_le_inv in Hc. destruct Hc as [Hc1 Hc2].
  assert (Hsb : sqrt bsT <= (1 + 31 / 10 * u) * sqrt bs + 2 / 10 ^ 100) by lra.
  assert (Hu' : u * sqrt bsT <= u * ((1 + 31 / 10 * u) * sqrt bs + 2 / 10 ^ 100)) by (apply Rmult_le_compat_l; lra).

  assert (Hq : 0 <= u * sqrt bs) by nra.
  assert (Hq2 : u * (u * sqrt bs) <= 1 / 100 * (u * sqrt bs)) by nra.
  assert (E1 : u * ((1 + 31 / 10 * u) * sqrt bs + 2 / 10 ^ 100) = u * sqrt bs + 31 / 10 * (u * (u * sqrt bs)) + u * (2 / 10 ^ 100)) by ring.
  assert (Hq3 : u * (2 / 10 ^ 100) <= 1 / 10 ^ 100) by (assert (u <= 1 / 2) by lra; nra).
  assert (E2 : 43 / 10 * u * sqrt bs = 43 / 10 * (u * sqrt bs)) by ring.
  assert (E3 : 31 / 10 * u * sqrt bs = 31 / 10 * (u * sqrt bs)) by ring.
  apply Rabs_le. split; lra.
Qed.

Lemma Phi_diff q xT : 0 <= q -> q <= 2001 / 100 -> xT <= 0 ->
  Rabs (xT - - q) <= 54 / 10 * u * q + 4 / 10 ^ 92 ->
  Rabs (Phi xT - Phi (- q)) <= 132 / 100 * u.
Proof.
  intros Hq0 Hq1 HxT Hd. pose proof u_pos as Hu. pose proof u_lt as Hu2.
  set (d := Rabs (xT - - q)) in *.
  assert (Hd0 : 0 <= d) by apply Rabs_pos.
  pose proof (PhiL xT (- q) HxT ltac:(lra)) as H.
  rewrite Ropp_involutive in H.
  set (m := Rmin (- xT) q) in *.
  assert (Hmq : m <= q) by apply Rmin_r.
  assert (Hm2 : q * q - 2 * q * d <= m * m).
  { destruct (Rle_dec d q) as [Hl|Hl].
    - assert (Hxd : q - d <= - xT).
      { pose proof (Rabs_le_inv _ _ (Rle_refl (Rabs (xT - - q)))) as [A B]. unfold d. lra. }
      assert (Hm : q - d <= m) by (unfold m; apply Rmin_glb; lra).
      nra.
    - assert (q * q - 2 * q * d <= 0) by nra. nra. }
  assert (Hex : exp (- (m * m / 2)) <= exp (- (q * q / 2)) * exp (q * d)).
  { rewrite <- exp_plus.
    assert (Hl0 : - (m * m / 2) <= - (q * q / 2) + q * d) by lra.
    destruct (Rle_lt_or_eq_dec _ _ Hl0) as [Hl|Heq].
    - left. apply exp_increasing. exact Hl.
    - right. f_equal. exact Heq. }
  assert (Hqd : q * d <= 1 / 10 ^ 12).
  { assert (q * d <= q * (54 / 10 * u * q + 4 / 10 ^ 92)) by (apply Rmult_le_compat_l; lra).
    assert (q * (54 / 10 * u * q + 4 / 10 ^ 92) <= 2001 / 100 * (54 / 10 * u * (2001 / 100) + 4 / 10 ^ 92)).
    { apply Rmult_le_compat; [lra | nra | lra | assert (54 / 10 * u * q <= 54 / 10 * u * (2001 / 100)) by (apply Rmult_le_compat_l; nra); lra]. }
    assert (2001 / 100 * (54 / 10 * (12 / 10 ^ 17) * (2001 / 100) + 4 / 10 ^ 92) <= 1 / 10 ^ 12) by interval.
    assert (54 / 10 * u * (2001 / 100) <= 54 / 10 * (12 / 10 ^ 17) * (2001 / 100)) by (apply Rmult_le_compat_r; [lra | nra]).
    nra. }
  assert (Hex2 : exp (q * d) <= 1 + 2 / 10 ^ 12).
  { pose proof (exp_ineq1_le (- (q * d))) as Hb. rewrite exp_Ropp in Hb.
    assert (Hp : 0 < exp (q * d)) by apply exp_pos.
    assert (Hb3 : (1 - q * d) * exp (q * d) <= 1).
    { apply Rmult_le_reg_r with (/ exp (q * d)); [apply Rinv_0_lt_compat; lra|]. rewrite Rmult_assoc, Rinv_r by lra. nra. }
    assert (Hd1 : 0 < 1 - q * d) by (assert (1 / 10 ^ 12 <= 1 / 2) by interval; lra).
    assert (exp (q * d) <= 1 + q * d + 2 * (q * d) * (q * d)) by nra.
    assert (q * d * (q * d) <= q * d * (1 / 10 ^ 12)) by (apply Rmult_le_compat_l; [nra | lra]).
    assert (2 * (1 / 10 ^ 12) * (1 / 10 ^ 12) <= 1 / 10 ^ 12) by interval.
    nra. }
  pose proof (xe_half q Hq0) as Hxe.
  assert (Hxe' : q * exp (- (q * q / 2)) <= 607 / 1000) by exact Hxe.
  assert (Hep : 0 < exp (- (q * q / 2))) by apply exp_pos.
  assert (Hep1 : exp (- (q * q / 2)) <= 1).
  { rewrite <- exp_0. destruct (Rle_lt_or_eq_dec (- (q * q / 2)) 0) as [Hl|Heq]; [nra | left; apply exp_increasing; exact Hl | right; f_equal; exact Heq]. }
  set (E := exp (- (q * q / 2))) in *.
  assert (Hdd : d * E <= 54 / 10 * u * (607 / 1000) + 4 / 10 ^ 92).
  { assert (d * E <= (54 / 10 * u * q + 4 / 10 ^ 92) * E) by (apply Rmult_le_compat_r; lra).
    assert (E2 : (54 / 10 * u * q + 4 / 10 ^ 92) * E = 54 / 10 * u * (q * E) + 4 / 10 ^ 92 * E) by ring.
    assert (u * (q * E) <= u * (607 / 1000)) by (apply Rmult_le_compat_l; lra).
    assert (4 / 10 ^ 92 * E <= 4 / 10 ^ 92) by (assert (0 <= 4 / 10 ^ 92) by interval; nra).
    nra. }
  assert (Hmain : Rabs (Phi xT - Phi (- q)) <= d * (E * exp (q * d)) / (25066 / 10000)).
  { eapply Rle_trans; [exact H|]. unfold Rdiv. apply Rmult_le_compat_r; [left; apply Rinv_0_lt_compat; lra|].
    apply Rmult_le_compat_l; [exact Hd0|]. exact Hex. }
  assert (Hq1' : d * (E * exp (q * d)) <= (d * E) * (1 + 2 / 10 ^ 12)).
  { assert (d * E >= 0) by nra. assert (E1 : d * (E * exp (q * d)) = (d * E) * exp (q * d)) by ring. rewrite E1. apply Rmult_le_compat_l; lra. }
  assert (Hfin : (54 / 10 * u * (607 / 1000) + 4 / 10 ^ 92) * (1 + 2 / 10 ^ 12) / (25066 / 10000) <= 132 / 100 * u).
  { assert (Hc : 4 / 10 ^ 92 <= 1 / 10 ^ 30 * u) by (rewrite u_value; interval).
    assert ((54 / 10 * (607 / 1000) + 1 / 10 ^ 30) * (1 + 2 / 10 ^ 12) / (25066 / 10000) <= 132 / 100) by interval.
    assert ((54 / 10 * u * (607 / 1000) + 4 / 10 ^ 92) * (1 + 2 / 10 ^ 12) <= (54 / 10 * (607 / 1000) + 1 / 10 ^ 30) * u * (1 + 2 / 10 ^ 12)) by (apply Rmult_le_compat_r; [interval | nra]).
    assert (E3 : (54 / 10 * (607 / 1000) + 1 / 10 ^ 30) * u * (1 + 2 / 10 ^ 12) / (25066 / 10000) = u * ((54 / 10 * (607 / 1000) + 1 / 10 ^ 30) * (1 + 2 / 10 ^ 12) / (25066 / 10000))) by field.
    assert (E4 : (54 / 10 * u * (607 / 1000) + 4 / 10 ^ 92) * (1 + 2 / 10 ^ 12) / (25066 / 10000) <= (54 / 10 * (607 / 1000) + 1 / 10 ^ 30) * u * (1 + 2 / 10 ^ 12) / (25066 / 10000)).
    { unfold Rdiv. apply Rmult_le_compat_r; [left; apply Rinv_0_lt_compat; lra | lra]. }
    nra. }
  assert (Hq2 : d * (E * exp (q * d)) / (25066 / 10000) <= (d * E) * (1 + 2 / 10 ^ 12) / (25066 / 10000)).
  { unfold Rdiv. apply Rmult_le_compat_r; [left; apply Rinv_0_lt_compat; lra | exact Hq1']. }
  assert (Hq3 : (d * E) * (1 + 2 / 10 ^ 12) / (25066 / 10000) <= (54 / 10 * u * (607 / 1000) + 4 / 10 ^ 92) * (1 + 2 / 10 ^ 12) / (25066 / 10000)).
  { unfold Rdiv. apply Rmult_le_compat_r; [left; apply Rinv_0_lt_compat; lra|]. apply Rmult_le_compat_r; [interval | exact Hdd]. }
  lra.
Qed.
End PhiLeaf.
