(** The scale [a = sqrt (1 - rho^2)] as the kernel computes it, and the effect of its
    rounding on the integral (docs/bivariate_normal_high.md section 4.5). *)
From Coq Require Import Reals Lra Psatz ZArith Lia.
From Interval Require Import Tactic.
From Flocq Require Import Core Sterbenz.
Require Import BvnHighAssembly BvnHighRound BvnHighSteps.
Open Scope R_scope.

(** [a~ = sqrt (rnd (rnd (1 - r) * rnd (1 + r)))], for [r = |rho|]. *)
Definition ass_k (r : R) : R := rnd (rnd (1 - r) * rnd (1 + r)).

Section ASetup.
Variable sqrtT : R -> R.
Hypothesis Hsq0 : forall x, 0 <= x -> rel (sqrt x) (sqrtT x) u.

Lemma a_setup r :
  925 / 1000 <= r -> r <= 1 - u -> generic_format radix2 fexp r ->
  let a := sqrt ((1 - r) * (1 + r)) in
  rel a (sqrtT (ass_k r)) (203 / 100 * u) /\ 14 / 10 ^ 9 <= a /\ a <= 38 / 100.
Proof.
  intros Hr1 Hr2 Hf a.
  pose proof u_pos as Hu. pose proof u_lt as Hu2. pose proof u_value as Huv.
  assert (F1 : generic_format radix2 fexp 1) by (pose proof (rnd_format 1) as F; rewrite rnd_one in F; exact F).
  assert (Hex : rnd (1 - r) = 1 - r).
  { apply rnd_fix. replace (1 - r) with (1 - r) by ring.
    apply sterbenz; [apply fexp_valid | apply fexp_mono | exact F1 | exact Hf | lra]. }
  assert (Hass : 1 / 10 ^ 100 <= (1 - r) * (1 + r)).
  { assert (u * (19 / 10) <= (1 - r) * (1 + r)) by nra.
    assert (1 / 10 ^ 100 <= u * (19 / 10)) by (rewrite Huv; interval). lra. }
  assert (Hass1 : (1 - r) * (1 + r) <= 144375 / 10 ^ 6) by nra.
  assert (Hy1 : 1 / 10 ^ 100 <= 1 + r) by (assert (1 / 10 ^ 100 <= 1) by interval; lra).
  pose proof (rnd_rel (1 + r) (nrm_pos _ Hy1)) as Hy.
  assert (Hrel1 : rel (1 + r) (rnd (1 + r)) u).
  { unfold rel. rewrite (Rabs_right (1 + r)) in * by lra. exact Hy. }
  assert (Hrel2 : rel ((1 - r) * (1 + r)) (rnd (1 - r) * rnd (1 + r)) (0 + u + 0 * u)).
  { rewrite Hex. replace (0 + u + 0 * u) with (0 + u + 0 * u) by ring.
    pose proof (rel_mul (1 - r) (1 - r) (1 + r) (rnd (1 + r)) 0 u (Rle_refl 0) (Rlt_le _ _ Hu)
      ltac:(unfold rel; replace (1 - r - (1 - r)) with 0 by ring; rewrite Rabs_R0; nra) Hrel1) as H.
    exact H. }
  assert (Hp : 1 / 10 ^ 100 <= rnd (1 - r) * rnd (1 + r)).
  { rewrite Hex. assert (Hq : (1 - r) * (1 + r) * (1 - u) <= (1 - r) * rnd (1 + r)).
    { pose proof (rel_lo (1 + r) (rnd (1 + r)) u ltac:(lra) Hrel1) as Hl.
      assert (0 <= 1 - r) by lra. nra. }
    assert (1 / 10 ^ 100 <= (1 - r) * (1 + r) * (1 - u)).
    { assert (u * (19 / 10) * (1 - u) <= (1 - r) * (1 + r) * (1 - u)) by (apply Rmult_le_compat_r; [lra | nra]).
      assert (1 / 10 ^ 100 <= u * (19 / 10) * (1 - u)) by (rewrite Huv; interval). lra. }
    lra. }
  assert (Hrel3 : rel ((1 - r) * (1 + r)) (ass_k r) (0 + u + 0 * u + u + u * (0 + u + 0 * u))).
  { unfold ass_k. apply rel_rnd; [apply nrm_pos; exact Hp | lra | exact Hrel2]. }
  assert (Hpos : 0 < (1 - r) * (1 + r)) by (assert (0 < 1 / 10 ^ 100) by interval; lra).
  assert (Hak : 1 / 10 ^ 100 <= ass_k r).
  { unfold rel in Hrel3. rewrite (Rabs_right ((1 - r) * (1 + r))) in Hrel3 by lra.
    apply Rabs_le_inv in Hrel3. destruct Hrel3 as [A B].
    assert (1 / 10 ^ 100 <= (1 - r) * (1 + r) * (1 - 3 * u)).
    { assert (u * (19 / 10) * (1 - 3 * u) <= (1 - r) * (1 + r) * (1 - 3 * u)) by (apply Rmult_le_compat_r; [lra | nra]).
      assert (1 / 10 ^ 100 <= u * (19 / 10) * (1 - 3 * u)) by (rewrite Huv; interval). lra. }
    nra. }
  assert (Hrs : rel a (sqrt (ass_k r)) (51 / 100 * (0 + u + 0 * u + u + u * (0 + u + 0 * u)))).
  { apply rel_sqrt; [exact Hpos | lra | nra | nra | exact Hrel3]. }
  pose proof (Hsq0 (ass_k r) ltac:(lra)) as Hq.
  assert (Hcomp : rel a (sqrtT (ass_k r)) (51 / 100 * (0 + u + 0 * u + u + u * (0 + u + 0 * u)) + u * (1 + 51 / 100 * (0 + u + 0 * u + u + u * (0 + u + 0 * u))))).
  { eapply (rel_trans a (sqrt (ass_k r)) (sqrtT (ass_k r)) _ u); [nra | lra | exact Hrs | exact Hq]. }
  assert (Hsa : 0 < a) by (unfold a; apply sqrt_lt_R0; lra).
  pose proof (sqrt_sqrt ((1 - r) * (1 + r)) ltac:(lra)) as Ea. fold a in Ea.
  repeat split.
  - eapply rel_mono; [exact Hcomp|]. nra.
  - apply Rnot_lt_le. intro Hc.
    assert (a * a < 14 / 10 ^ 9 * (14 / 10 ^ 9)) by (apply Rmult_le_0_lt_compat; [lra | lra | exact Hc | exact Hc]).
    assert (14 / 10 ^ 9 * (14 / 10 ^ 9) <= u * (19 / 10)) by (rewrite Huv; interval).
    nra.
  - apply Rnot_lt_le. intro Hc.
    assert (38 / 100 * (38 / 100) < a * a) by (apply Rmult_le_0_lt_compat; [lra | lra | exact Hc | exact Hc]).
    nra.
Qed.

(** The kernel's [a~] is in the closed-form range, and within [2.03 u] of [a]. *)
Lemma a_range r :
  925 / 1000 <= r -> r <= 1 - u -> generic_format radix2 fexp r ->
  1 / 10 ^ 8 <= sqrtT (ass_k r) /\ sqrtT (ass_k r) <= 381 / 1000.
Proof.
  intros H1 H2 H3. destruct (a_setup r H1 H2 H3) as [Hr [Ha1 Ha2]]. cbv zeta in *.
  pose proof u_pos as Hu. pose proof u_lt as Hu2.
  set (a := sqrt ((1 - r) * (1 + r))) in *.
  unfold rel in Hr. rewrite (Rabs_right a) in Hr by lra. apply Rabs_le_inv in Hr. destruct Hr as [A B].
  assert (Hq : u * a <= u * (38 / 100)) by (apply Rmult_le_compat_l; lra).
  assert (Hq2 : u * a >= 0) by nra.
  split.
  - assert (14 / 10 ^ 9 * (1 - 203 / 100 * u) <= a * (1 - 203 / 100 * u)) by (apply Rmult_le_compat_r; [lra | lra]).
    assert (E : 203 / 100 * u * a = 203 / 100 * (u * a)) by ring.
    assert (14 / 10 ^ 9 * (1 - 203 / 100 * u) >= 1 / 10 ^ 8) by (rewrite u_value; interval).
    nra.
  - assert (E : 203 / 100 * u * a = 203 / 100 * (u * a)) by ring.
    assert (203 / 100 * (u * (38 / 100)) <= 1 / 1000) by (rewrite u_value; interval).
    lra.
Qed.
End ASetup.

(** The branch's two inputs to the integrand as the kernel forms them.  With [d = dh - k]
    ([k = dk] for positive correlation, [-dk] for negative) and [d1 = rnd d], the computed
    [bs] is [rnd (d1 d1)]; the computed [hk] is [rnd (dh dk)], negated for negative
    correlation.  [|d| <= 0.061] is the range where the integral is evaluated at all
    ([bs <= 400.1 s^2 <= 3.6e-3]). *)
Lemma bs_rela d :
  Rabs d <= 61 / 1000 -> rela (d * d) (rnd (rnd d * rnd d)) (31 / 10 * u) (1 / 10 ^ 200).
Proof.
  intros Hd.
  pose proof u_pos as Hu. pose proof u_lt as Hu2. pose proof eta_small as Hη.
  pose proof (rnd_abs d) as H1. set (d1 := rnd d) in *.
  assert (He : eta <= 1 / 10 ^ 250) by (assert (/ 10 ^ 300 <= 1 / 10 ^ 250) by interval; lra).
  pose proof (Rabs_pos d) as Hd0.
  assert (Hd1 : Rabs d1 <= 62 / 1000).
  { pose proof (Rabs_triang (d1 - d) d) as T. replace (d1 - d + d) with d1 in T by ring.
    assert (u * Rabs d <= u * (61 / 1000)) by (apply Rmult_le_compat_l; lra).
    assert (u * (61 / 1000) + 1 / 10 ^ 250 <= 1 / 1000) by (rewrite u_value; interval). lra. }
  pose proof (rnd_abs (d1 * d1)) as H2.
  assert (Hq : Rabs (d1 * d1 - d * d) <= (2 * u + u * u) * (d * d) + 4 / 10 ^ 250 * Rabs d + (1 / 10 ^ 250) * (1 / 10 ^ 250) + 2 * u * (1 / 10 ^ 250) * Rabs d).
  { replace (d1 * d1 - d * d) with ((d1 - d) * (d1 + d)) by ring.
    rewrite Rabs_mult.
    pose proof (Rabs_triang (d1 - d) (2 * d)) as T3. 
    assert (Hs : Rabs (d1 + d) <= (2 + u) * Rabs d + 1 / 10 ^ 250).
    { replace (d1 + d) with ((d1 - d) + 2 * d) by ring.
      pose proof (Rabs_triang (d1 - d) (2 * d)) as T4. rewrite Rabs_mult in T4. rewrite (Rabs_right 2) in T4 by lra. lra. }
    assert (Hp : Rabs (d1 - d) * Rabs (d1 + d) <= (u * Rabs d + 1 / 10 ^ 250) * ((2 + u) * Rabs d + 1 / 10 ^ 250)).
    { apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | lra | lra]. }
    assert (Hdd : Rabs d * Rabs d = d * d) by (rewrite <- Rabs_mult; apply Rabs_right; nra).
    nra. }
  unfold rela. rewrite (Rabs_right (d * d)) by nra.
  assert (Hdd : Rabs d * Rabs d = d * d) by (rewrite <- Rabs_mult; apply Rabs_right; nra).
  assert (Hdd0 : 0 <= d * d) by nra.
  assert (Hpr : Rabs (d1 * d1) <= (1 + 2 * u + u * u) * (d * d) + 5 / 10 ^ 250).
  { pose proof (Rabs_triang (d1 * d1 - d * d) (d * d)) as T. replace (d1 * d1 - d * d + d * d) with (d1 * d1) in T by ring.
    rewrite (Rabs_right (d * d)) in T by nra.
    assert (4 / 10 ^ 250 * Rabs d <= 4 / 10 ^ 250 * (61 / 1000)) by (apply Rmult_le_compat_l; [interval | lra]).
    assert (2 * u * (1 / 10 ^ 250) * Rabs d <= 1 / 10 ^ 260) by (rewrite u_value; assert (0 <= 1 / 10 ^ 250 * Rabs d) by (apply Rmult_le_pos; [interval | lra]); nra).
    assert (4 / 10 ^ 250 * (61 / 1000) + 1 / 10 ^ 260 + (1 / 10 ^ 250) * (1 / 10 ^ 250) <= 5 / 10 ^ 250) by interval. lra. }
  assert (Hfin : Rabs (rnd (d1 * d1) - d * d) <= 31 / 10 * u * (d * d) + 1 / 10 ^ 200).
  { pose proof (Rabs_triang (rnd (d1 * d1) - d1 * d1) (d1 * d1 - d * d)) as T.
    replace (rnd (d1 * d1) - d1 * d1 + (d1 * d1 - d * d)) with (rnd (d1 * d1) - d * d) in T by ring.
    assert (u * Rabs (d1 * d1) <= u * ((1 + 2 * u + u * u) * (d * d) + 5 / 10 ^ 250)) by (apply Rmult_le_compat_l; lra).
    assert (E : u * ((1 + 2 * u + u * u) * (d * d) + 5 / 10 ^ 250) = u * (d * d) + 2 * (u * u) * (d * d) + (u * u * u) * (d * d) + u * (5 / 10 ^ 250)) by ring.
    assert (Hu3 : u * u <= u / 1000) by (rewrite u_value; interval).
    assert (Hu4 : u * u * u <= u / 1000) by (rewrite u_value; interval).
    assert (Hz : 0 <= u * (d * d)) by nra.
    assert (Hm1 : (u * u) * (d * d) <= u / 1000 * (d * d)) by (apply Rmult_le_compat_r; [exact Hdd0 | exact Hu3]).
    assert (Hm2 : (u * u * u) * (d * d) <= u / 1000 * (d * d)) by (apply Rmult_le_compat_r; [exact Hdd0 | exact Hu4]).
    assert (Hm3 : u * (5 / 10 ^ 250) <= 1 / 10 ^ 260) by (rewrite u_value; interval).
    assert (Hs1 : (2 * u + u * u) * (d * d) = 2 * (u * (d * d)) + (u * u) * (d * d)) by ring.
    assert (Hs2 : 4 / 10 ^ 250 * Rabs d <= 4 / 10 ^ 250 * (61 / 1000)) by (apply Rmult_le_compat_l; [interval | lra]).
    assert (Hs3 : 2 * u * (1 / 10 ^ 250) * Rabs d <= 1 / 10 ^ 260) by (rewrite u_value; assert (0 <= 1 / 10 ^ 250 * Rabs d) by (apply Rmult_le_pos; [interval | lra]); nra).
    assert (Hs4 : 4 / 10 ^ 250 * (61 / 1000) + 1 / 10 ^ 260 + (1 / 10 ^ 250) * (1 / 10 ^ 250) + 1 / 10 ^ 260 + 1 / 10 ^ 250 + 1 / 10 ^ 250 <= 1 / 10 ^ 200) by interval.
    assert (Hs5 : u * (d * d) = 1 * (u * (d * d))) by ring.
    assert (Ha : (u * u) * (d * d) >= 0) by nra.
    nra. }
  exact Hfin.
Qed.

Lemma hk_rela x : rela x (rnd x) u (1 / 10 ^ 200).
Proof.
  unfold rela. pose proof (rnd_abs x) as H. pose proof eta_small as Hη.
  assert (/ 10 ^ 300 <= 1 / 10 ^ 200) by interval. lra.
Qed.

Lemma hk_rela_neg x : rela (- x) (- rnd x) u (1 / 10 ^ 200).
Proof.
  pose proof (hk_rela x) as H. unfold rela in *.
  replace (- rnd x - - x) with (- (rnd x - x)) by ring. rewrite Rabs_Ropp, Rabs_Ropp. exact H.
Qed.

(** The identity behind [bs >= -4 hk]: [(dh - k)^2 + 4 dh k = (dh + k)^2]. *)
Lemma bs_hk_identity dh k : (dh - k) * (dh - k) + 4 * (dh * k) = (dh + k) * (dh + k).
Proof. ring. Qed.
