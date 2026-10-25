(** The node of the high-correlation integral from [HK_SPLIT = 16] on: the exponent
    [phi = hk / 2 + bs / (2 xs) + hk xs / (2 (1 + rs)^2)] is two exponentials,
    [exp(-big) exp(-small)] with [big = hk / 2 + bs / (2 xs)] and
    [small = hk xs / (2 (1 + rs)^2)], and the cutoff is on [big]. Its computed exponent is
    closer to [phi] than the single-exponential form's, so the node's bound is the same one
    ([BvnHighNode.node_error]); the two forms are told apart by [hkT >= 16], as the kernel's
    [integrand_term] does. *)
From Coq Require Import Reals Lra Psatz ZArith Lia.
From Interval Require Import Tactic.
From Flocq Require Import Core.
Require Import BvnHighAssembly BvnHighRound BvnHighSteps BvnHighNodeExp BvnHighNodeMul BvnHighNode.
Open Scope R_scope.

(** Where the computed exponent argument is at least 99.9, the exact integrand is below [1e-39]. *)
Lemma small_F2 phi ph pabs F rs :
  999 / 10 <= ph -> Rabs (ph - phi) <= 85 / 10 * u * pabs + 1 / 10 ^ 40 -> pabs <= 1157 / 1000 * phi ->
  0 <= phi -> 9244 / 10000 <= rs -> F = exp (- phi) / rs -> F <= 1 / 10 ^ 39.
Proof.
  intros Hph H_phi40 Hpa Hph0 Hrs HF.
  pose proof u_pos as Hu. pose proof u_lt as Hu2.
  assert (Hphi98 : 98 <= phi).
  { pose proof (Rabs_le_inv _ _ H_phi40) as [Hl1 Hl2].
    assert (Hup : 85 / 10 * u * pabs <= 85 / 10 * u * (1157 / 1000 * phi)) by (apply Rmult_le_compat_l; [lra | exact Hpa]).
    assert (Hu3 : u * phi <= 12 / 10 ^ 17 * phi) by (apply Rmult_le_compat_r; lra).
    assert (E1 : 85 / 10 * u * (1157 / 1000 * phi) = 98345 / 10000 * (u * phi)) by field.
    assert (1 / 10 ^ 40 <= 1 / 10) by interval.
    assert (Hc1 : 98345 / 10000 * (12 / 10 ^ 17) <= 1 / 10 ^ 14) by interval.
    assert (Hc2 : 98345 / 10000 * (12 / 10 ^ 17 * phi) <= 1 / 10 ^ 14 * phi) by (nra).
    assert (Hc3 : 1 / 10 ^ 14 * phi <= 1 / 100 * phi) by (assert (1 / 10 ^ 14 <= 1 / 100) by interval; nra).
    lra. }
  assert (Hex98 : exp (- 98) <= 1 / 10 ^ 42) by interval.
  assert (Hex1 : exp (- phi) <= exp (- 98)).
  { destruct (Rle_lt_or_eq_dec _ _ Hphi98) as [Hl|Heq].
    - left. apply exp_increasing. lra.
    - right. f_equal. lra. }
  assert (HFl : F <= exp (- phi) * (10818 / 10000)).
  { rewrite HF. unfold Rdiv. assert (Hi : / rs <= / (9244 / 10000)) by (apply Rinv_le_contravar; lra).
    assert (Hi2 : / (9244 / 10000) <= 10818 / 10000) by lra.
    pose proof (exp_pos (- phi)). nra. }
  assert (1 / 10 ^ 42 * (10818 / 10000) <= 1 / 10 ^ 39) by interval.
  pose proof (exp_pos (- phi)). nra.
Qed.

(** [hk / (1 + rs) = hk / 2 + hk xs / (2 (1 + rs)^2)] where [rs^2 = 1 - xs]. *)
Lemma split_identity hk xs rs :
  rs * rs = 1 - xs -> 0 < 1 + rs ->
  hk / (1 + rs) = hk / 2 + hk * xs / (2 * ((1 + rs) * (1 + rs))).
Proof.
  intros H Hp.
  assert (Hx : xs = 1 - rs * rs) by lra.
  rewrite Hx. field. lra.
Qed.

(** A value within [t] of [exp(-ph)] is [exp] of a number within [1.02 t] of [-ph]. *)
Lemma ln_lump ph y t :
  0 <= t -> t <= 1 / 100 -> rel (exp (- ph)) y t ->
  0 < y /\ exp (- (- ln y)) = y /\ Rabs (- ln y - ph) <= 102 / 100 * t.
Proof.
  intros Ht0 Ht1 H.
  pose proof (exp_pos (- ph)) as Hp.
  pose proof (rel_lo (exp (- ph)) y t Hp H) as Hlo.
  pose proof (rel_hi (exp (- ph)) y t Hp H) as Hhi.
  assert (Hy : 0 < y) by nra.
  split; [exact Hy|]. split.
  { rewrite Ropp_involutive. apply exp_ln. exact Hy. }
  set (r := y / exp (- ph)).
  assert (Hr0 : 0 < r) by (unfold r; apply Rdiv_lt_0_compat; assumption).
  assert (Hr : y = r * exp (- ph)) by (unfold r; field; lra).
  assert (Hlny : ln y = ln r + (- ph)).
  { rewrite Hr at 1. rewrite ln_mult by lra. rewrite ln_exp. reflexivity. }
  assert (Hrlo : 1 - t <= r).
  { apply (Rmult_le_reg_r (exp (- ph)) _ _ Hp). rewrite <- Hr. lra. }
  assert (Hrhi : r <= 1 + t).
  { apply (Rmult_le_reg_r (exp (- ph)) _ _ Hp). rewrite <- Hr. lra. }
  set (L := ln r).
  assert (HeL : exp L = r) by (unfold L; apply exp_ln; exact Hr0).
  pose proof (exp_ineq1_le L) as HL1.
  pose proof (exp_ineq1_le (- L)) as HL2. rewrite exp_Ropp, HeL in HL2.
  assert (HLup : L <= t) by lra.
  assert (Hinv : / r <= 1 + 102 / 100 * t).
  { apply Rle_trans with (/ (1 - t)); [apply Rinv_le_contravar; lra|].
    apply Rmult_le_reg_r with (1 - t); [lra|]. rewrite Rinv_l by lra. nra. }
  assert (HLlo : - (102 / 100 * t) <= L) by lra.
  replace (- ln y - ph) with (- L) by (rewrite Hlny; unfold L; ring).
  apply Rabs_le. lra.
Qed.

Lemma rnd_nonneg x : 0 <= x -> 0 <= rnd x.
Proof. intros H. pose proof (rnd_le 0 x H) as H1. rewrite rnd_0 in H1. exact H1. Qed.

Lemma u_lo30 : 1 / 10 ^ 30 <= u.
Proof. rewrite u_value. interval. Qed.

Lemma uu_small : u * u <= 1 / 10 ^ 15 * u.
Proof.
  pose proof u_pos as Hu. pose proof u_lt as Hu2.
  assert (u <= 1 / 10 ^ 15) by (assert (12 / 10 ^ 17 <= 1 / 10 ^ 15) by interval; lra). nra.
Qed.

Lemma e200_pos : 0 < 1 / 10 ^ 200.
Proof. interval. Qed.

Lemma e200_small : 1 / 10 ^ 200 <= 1 / 100 * u.
Proof.
  pose proof u_lo30 as H. assert (1 / 10 ^ 200 <= 1 / 100 * (1 / 10 ^ 30)) by interval. nra.
Qed.

Lemma num1 :
  (u + 1 / 10 ^ 200 + 31 / 10 * u + (u + 1 / 10 ^ 200) * (31 / 10 * u)) + u
  + u * (u + 1 / 10 ^ 200 + 31 / 10 * u + (u + 1 / 10 ^ 200) * (31 / 10 * u)) <= 52 / 10 * u.
Proof.
  pose proof u_pos as Hu. pose proof u_lt as Hu2. pose proof uu_small as H1. pose proof e200_small as H2.
  set (e := 1 / 10 ^ 200) in *.
  assert (Ha : u + e <= 101 / 100 * u) by lra.
  assert (Ha0 : 0 <= u + e) by (unfold e; assert (0 < 1 / 10 ^ 200) by interval; lra).
  assert (Hb : (u + e) * (31 / 10 * u) <= 1 / 1000 * u).
  { assert ((u + e) * (31 / 10 * u) <= (101 / 100 * u) * (31 / 10 * u)) by (apply Rmult_le_compat_r; lra).
    assert ((101 / 100 * u) * (31 / 10 * u) = 3131 / 1000 * (u * u)) by field.
    assert (3131 / 1000 * (u * u) <= 3131 / 1000 * (1 / 10 ^ 15 * u)) by (apply Rmult_le_compat_l; lra).
    assert (3131 / 1000 * (1 / 10 ^ 15 * u) <= 1 / 1000 * u) by (assert (3131 / 1000 * (1 / 10 ^ 15) <= 1 / 1000) by interval; nra).
    lra. }
  set (t := u + e + 31 / 10 * u + (u + e) * (31 / 10 * u)) in *.
  assert (Ht : t <= 412 / 100 * u) by (unfold t; lra).
  assert (Ht0 : 0 <= t) by (unfold t; assert (0 <= (u + e) * (31 / 10 * u)) by (apply Rmult_le_pos; lra); lra).
  assert (Hut : u * t <= u * (412 / 100 * u)) by (apply Rmult_le_compat_l; lra).
  assert (Huu2 : u * (412 / 100 * u) <= 412 / 100 * (1 / 10 ^ 15 * u)) by nra.
  assert (412 / 100 * (1 / 10 ^ 15) <= 1 / 100) by interval.
  nra.
Qed.

Lemma num2 : 2 * u + u + u * (2 * u) <= 31 / 10 * u.
Proof. pose proof u_pos as Hu. pose proof uu_small as H1. nra. Qed.

Lemma num3 :
  (31 / 10 * u + 2 * u + 31 / 10 * u * (2 * u)) + u + u * (31 / 10 * u + 2 * u + 31 / 10 * u * (2 * u)) <= 62 / 10 * u.
Proof.
  pose proof u_pos as Hu. pose proof uu_small as H1.
  assert (Hv : u * (u * u) <= 1 / 10 ^ 15 * (u * u)) by (assert (u <= 1 / 10 ^ 15) by (pose proof u_lt; assert (12 / 10 ^ 17 <= 1 / 10 ^ 15) by interval; lra); nra).
  nra.
Qed.

Lemma num4 : (52 / 10 * u + 62 / 10 * u) / (1 - 62 / 10 * u) <= 115 / 10 * u.
Proof.
  pose proof u_pos as Hu. pose proof u_lt as Hu2.
  assert (Hd : 0 < 1 - 62 / 10 * u) by (assert (62 / 10 * (12 / 10 ^ 17) < 1) by interval; nra).
  apply (Rmult_le_reg_r (1 - 62 / 10 * u)); [exact Hd|].
  unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra.
  pose proof uu_small as H1. nra.
Qed.

Lemma num5 : 115 / 10 * u + u + u * (115 / 10 * u) <= 126 / 10 * u.
Proof. pose proof u_pos as Hu. pose proof uu_small as H1. nra. Qed.

(** The relative closeness of the computed [small] to [hk xs / (2 (1 + rs)^2)]. *)
Lemma small_rel hk hkT xs xsT rs dT :
  159 / 10 <= hk -> 16 <= hkT -> rel hk hkT (u + 1 / 10 ^ 200) ->
  2 / 10 ^ 6 <= xs -> xs <= 1453 / 10000 -> rel xs xsT (31 / 10 * u) ->
  9244 / 10000 <= rs -> rs <= 1 -> rel (1 + rs) dT (2 * u) ->
  rel (hk * xs / (2 * ((1 + rs) * (1 + rs)))) (rnd (rnd (hkT * xsT) / rnd (rnd (2 * dT) * dT))) (126 / 10 * u).
Proof.
  intros Hk1 Hk2 Hrh Hx0 Hx1 H_xs R0 R1 H_o.
  pose proof u_pos as Hu. pose proof u_lt as Hu2.
  pose proof (rel_lo xs xsT (31 / 10 * u) ltac:(lra) H_xs) as Hxl.
  assert (Hxl' : 19 / 10 ^ 7 <= xsT).
  { assert (99 / 100 * xs <= (1 - 31 / 10 * u) * xs) by (apply Rmult_le_compat_r; [lra | lra]). 
    assert (99 / 100 * (2 / 10 ^ 6) <= 99 / 100 * xs) by (apply Rmult_le_compat_l; lra).
    assert (19 / 10 ^ 7 <= 99 / 100 * (2 / 10 ^ 6)) by interval. lra. }
  pose proof (rel_mul hk hkT xs xsT (u + 1 / 10 ^ 200) (31 / 10 * u) ltac:(lra) ltac:(lra) Hrh H_xs) as Hm1.
  assert (Hn1 : nrm (hkT * xsT)).
  { apply nrm_pos. pose proof (Rmult_le_compat 16 hkT (19 / 10 ^ 7) xsT ltac:(lra) ltac:(lra) Hk2 Hxl') as H.
    assert (1 / 10 ^ 100 <= 16 * (19 / 10 ^ 7)) by interval. lra. }
  assert (Hth1 : 0 <= u + 1 / 10 ^ 200 + 31 / 10 * u + (u + 1 / 10 ^ 200) * (31 / 10 * u)).
  { pose proof e200_pos as He2. assert (0 <= (u + 1 / 10 ^ 200) * (31 / 10 * u)) by (apply Rmult_le_pos; lra). lra. }
  pose proof (rel_rnd _ _ _ Hn1 Hth1 Hm1) as Hn1r.
  pose proof (rel_mono _ _ _ _ Hn1r num1) as Hn1'.
  set (n1 := rnd (hkT * xsT)) in *.
  pose proof (rel_lo (1 + rs) dT (2 * u) ltac:(lra) H_o) as Hdl.
  assert (Hdl' : 19 / 10 <= dT).
  { assert (99 / 100 * (1 + rs) <= (1 - 2 * u) * (1 + rs)) by (apply Rmult_le_compat_r; [lra | lra]). lra. }
  assert (Hd2 : rel (2 * (1 + rs)) (2 * dT) (2 * u)).
  { unfold rel in *. replace (2 * dT - 2 * (1 + rs)) with (2 * (dT - (1 + rs))) by field.
    rewrite Rabs_mult, (Rabs_right 2) by lra.
    rewrite (Rabs_right (1 + rs)) in H_o by lra.
    rewrite (Rabs_right (2 * (1 + rs))) by lra. lra. }
  assert (Hnd2 : nrm (2 * dT)) by (apply nrm_pos; assert (1 / 10 ^ 100 <= 1) by interval; lra).
  pose proof (rel_rnd (2 * (1 + rs)) (2 * dT) (2 * u) Hnd2 ltac:(lra) Hd2) as Hd2r.
  pose proof (rel_mono _ _ _ _ Hd2r num2) as Hd2'.
  set (d2 := rnd (2 * dT)) in *.
  pose proof (rel_lo (2 * (1 + rs)) d2 (31 / 10 * u) ltac:(lra) Hd2') as Hd2l.
  assert (Hd2g : 3 <= d2).
  { assert (99 / 100 * (2 * (1 + rs)) <= (1 - 31 / 10 * u) * (2 * (1 + rs))) by (apply Rmult_le_compat_r; [lra | lra]). lra. }
  pose proof (rel_mul (2 * (1 + rs)) d2 (1 + rs) dT (31 / 10 * u) (2 * u) ltac:(lra) ltac:(lra) Hd2' H_o) as Hm3.
  assert (Hn3 : nrm (d2 * dT)).
  { apply nrm_pos. pose proof (Rmult_le_compat 3 d2 (19 / 10) dT ltac:(lra) ltac:(lra) Hd2g Hdl') as H.
    assert (1 / 10 ^ 100 <= 3 * (19 / 10)) by interval. lra. }
  assert (Hth3 : 0 <= 31 / 10 * u + 2 * u + 31 / 10 * u * (2 * u)).
  { assert (0 <= 31 / 10 * u * (2 * u)) by (apply Rmult_le_pos; lra). lra. }
  pose proof (rel_rnd _ _ _ Hn3 Hth3 Hm3) as Hm3r.
  assert (Hm3' : rel (2 * ((1 + rs) * (1 + rs))) (rnd (d2 * dT)) (62 / 10 * u)).
  { replace (2 * ((1 + rs) * (1 + rs))) with (2 * (1 + rs) * (1 + rs)) by field.
    eapply rel_mono; [exact Hm3r | exact num3]. }
  set (m3 := rnd (d2 * dT)) in *.
  assert (Hnum0 : 0 < hk * xs) by (apply Rmult_lt_0_compat; lra).
  assert (Hden0 : 0 < 2 * ((1 + rs) * (1 + rs))) by nra.
  pose proof (rel_div (hk * xs) n1 (2 * ((1 + rs) * (1 + rs))) m3 (52 / 10 * u) (62 / 10 * u)
    (Rgt_not_eq _ _ Hden0) ltac:(lra) ltac:(lra) ltac:(lra) Hn1' Hm3') as Hqd.
  assert (Hqn : nrm (n1 / m3)).
  { apply nrm_pos.
    pose proof (rel_lo (hk * xs) n1 (52 / 10 * u) Hnum0 Hn1') as Hnl.
    pose proof (rel_hi (2 * ((1 + rs) * (1 + rs))) m3 (62 / 10 * u) Hden0 Hm3') as Hmh.
    assert (Hnl' : 2 / 10 ^ 5 <= n1).
    { pose proof (Rmult_le_compat (159 / 10) hk (2 / 10 ^ 6) xs ltac:(lra) ltac:(lra) Hk1 Hx0) as Hp0.
      assert (99 / 100 * (hk * xs) <= (1 - 52 / 10 * u) * (hk * xs)) by (apply Rmult_le_compat_r; [lra | lra]).
      assert (2 / 10 ^ 5 <= 99 / 100 * (159 / 10 * (2 / 10 ^ 6))) by interval. lra. }
    assert (Hmh' : m3 <= 9).
    { assert ((1 + 62 / 10 * u) * (2 * ((1 + rs) * (1 + rs))) <= (1 + 62 / 10 * u) * 8) by (apply Rmult_le_compat_l; [lra | nra]).
      assert ((1 + 62 / 10 * u) * 8 <= 9) by (assert (62 / 10 * u * 8 <= 1) by (assert (62 / 10 * (12 / 10 ^ 17) * 8 <= 1) by interval; nra); lra). lra. }
    assert (Hm3p : 0 < m3) by (pose proof (rel_lo (2 * ((1 + rs) * (1 + rs))) m3 (62 / 10 * u) Hden0 Hm3'); nra).
    assert (n1 / m3 >= 2 / 10 ^ 5 / 9).
    { apply Rle_ge. unfold Rdiv. apply Rmult_le_compat; [lra | left; apply Rinv_0_lt_compat; lra | lra | apply Rinv_le_contravar; lra]. }
    assert (1 / 10 ^ 100 <= 2 / 10 ^ 5 / 9) by interval. lra. }
  assert (Hqd' : rel (hk * xs / (2 * ((1 + rs) * (1 + rs)))) (n1 / m3) (115 / 10 * u)).
  { eapply rel_mono; [exact Hqd | exact num4]. }
  pose proof (rel_rnd (hk * xs / (2 * ((1 + rs) * (1 + rs)))) (n1 / m3) (115 / 10 * u) Hqn ltac:(lra) Hqd') as Hf.
  eapply rel_mono; [exact Hf | exact num5].
Qed.

Lemma mul_small x : 0 <= x -> u * x <= 1 / 10 ^ 15 * x.
Proof.
  intros H. pose proof u_lt as Hu2.
  assert (u <= 1 / 10 ^ 15) by (assert (12 / 10 ^ 17 <= 1 / 10 ^ 15) by interval; lra).
  apply Rmult_le_compat_r; assumption.
Qed.

(** The rounded exponent [big] against [hk / 2 + q]. *)
Lemma big_err hk hkT q qT hh bigT e0 :
  159 / 10 <= hk -> 16 <= hkT -> 0 <= e0 -> e0 <= 1 / 10 ^ 200 -> 0 <= q ->
  Rabs (hkT - hk) <= u * hk + e0 ->
  Rabs (hh - hkT * (1 / 2)) <= u * (hkT * (1 / 2)) + eta ->
  Rabs (qT - q) <= 74 / 10 * u * q + 1 / 10 ^ 190 ->
  Rabs (bigT - (hh + qT)) <= u * Rabs (hh + qT) + eta ->
  Rabs (bigT - (hk / 2 + q)) <= 841 / 100 * (u * q) + 301 / 100 * (u * (hk / 2)) + 1 / 10 ^ 188.
Proof.
  intros Hk1 Hk2 He0 He1 Hq0 Hhk Hhh Hq Hbg.
  pose proof u_pos as Hu. pose proof u_lt as Hu2. pose proof eta_small as Hη.
  assert (Hη0 : 0 < eta) by (unfold eta; apply bpow_gt_0).
  pose proof (Rabs_le_inv _ _ Hhk) as [Hk_a Hk_b].
  pose proof (Rabs_le_inv _ _ Hhh) as [Hh_a Hh_b].
  pose proof (Rabs_le_inv _ _ Hq) as [Hq_a Hq_b].
  assert (HP : 0 <= u * hk) by (apply Rmult_le_pos; lra).
  assert (HQ : 0 <= u * q) by (apply Rmult_le_pos; lra).
  pose proof (mul_small (u * hk) HP) as HuP.
  pose proof (mul_small (u * q) HQ) as HuQ.
  pose proof (mul_small e0 He0) as Hue.
  pose proof (mul_small eta (Rlt_le _ _ Hη0)) as Hueta.
  assert (Hc1 : 0 < 1 / 10 ^ 190) by interval.
  pose proof (mul_small (1 / 10 ^ 190) (Rlt_le _ _ Hc1)) as Huc1.
  assert (Hq74 : u * (74 / 10 * u * q) = 74 / 10 * (u * (u * q))) by field.
  assert (E4 : 74 / 10 * u * q = 74 / 10 * (u * q)) by field.
  (* hkT *)
  assert (Hhk_up : hkT <= hk + u * hk + e0) by lra.
  assert (HW : u * hkT <= u * hk + u * (u * hk) + u * e0).
  { assert (u * hkT <= u * (hk + u * hk + e0)) by (apply Rmult_le_compat_l; lra).
    assert (u * (hk + u * hk + e0) = u * hk + u * (u * hk) + u * e0) by field. lra. }
  assert (HW0 : 0 <= u * hkT) by (apply Rmult_le_pos; lra).
  pose proof (mul_small (u * hkT) HW0) as HuW.
  (* |hh + qT| *)
  assert (Hhh0 : 0 <= hh).
  { assert (u * (hkT * (1 / 2)) <= 1 / 2 * (hkT * (1 / 2))) by (apply Rmult_le_compat_r; lra).
    assert (/ 10 ^ 300 <= 1) by interval. assert (eta <= 1) by lra. lra. }
  assert (HqT0 : - (1 / 10 ^ 190) <= qT).
  { assert (74 / 10 * u * q <= q) by (assert (74 / 10 * u <= 1) by lra; nra). lra. }
  assert (Hmag : Rabs (hh + qT) <= hkT * (1 / 2) + (u * (hkT * (1 / 2)) + eta) + (q + (74 / 10 * u * q + 1 / 10 ^ 190))).
  { apply Rabs_le. split.
    - assert (0 <= u * (hkT * (1 / 2)) + eta) by (assert (0 <= u * (hkT * (1 / 2))) by (apply Rmult_le_pos; lra); lra).
      assert (0 <= 74 / 10 * u * q) by lra.
      lra.
    - lra. }
  assert (HuA : u * Rabs (hh + qT) <= u * (hkT * (1 / 2) + (u * (hkT * (1 / 2)) + eta) + (q + (74 / 10 * u * q + 1 / 10 ^ 190))))
    by (apply Rmult_le_compat_l; lra).
  assert (E1 : u * (hkT * (1 / 2) + (u * (hkT * (1 / 2)) + eta) + (q + (74 / 10 * u * q + 1 / 10 ^ 190)))
              = (u * hkT) / 2 + (u * (u * hkT)) / 2 + u * eta + u * q + 74 / 10 * (u * (u * q)) + u * (1 / 10 ^ 190)) by field.
  assert (E2 : u * (hkT * (1 / 2)) = (u * hkT) / 2) by field.
  assert (E3 : u * (hk / 2) = (u * hk) / 2) by field.
  assert (Hconst : 3 * (1 / 10 ^ 200) + 8 * eta + 4 * (1 / 10 ^ 190) <= 1 / 10 ^ 188) by interval.
  pose proof (Rabs_le_inv _ _ Hbg) as [Hb_a Hb_b].
  assert (U2 : u * Rabs (hh + qT) <= (u * hkT) / 2 + (u * (u * hkT)) / 2 + u * eta + u * q + 74 / 10 * (u * (u * q)) + u * (1 / 10 ^ 190)) by lra.
  assert (U3 : u * Rabs (hh + qT) <= (u * hkT) / 2 + 1 / 10 ^ 15 * (u * hkT) / 2 + 1 / 10 ^ 15 * eta + u * q + 74 / 10 * (1 / 10 ^ 15 * (u * q)) + 1 / 10 ^ 15 * (1 / 10 ^ 190)) by lra.
  assert (U4 : hkT * (1 / 2) - hkT * (1 / 2) + u * (hkT * (1 / 2)) = (u * hkT) / 2) by lra.
  apply Rabs_le. split.
  - lra.
  - lra.
Qed.

Lemma rel_hk hk hkT e0 :
  159 / 10 <= hk -> 0 <= e0 -> e0 <= 1 / 10 ^ 200 -> Rabs (hkT - hk) <= u * Rabs hk + e0 ->
  rel hk hkT (u + 1 / 10 ^ 200).
Proof.
  intros H1 H2 H3 H4. unfold rel. rewrite (Rabs_right hk) in * by lra.
  assert (1 / 10 ^ 200 * 1 <= 1 / 10 ^ 200 * hk) by (apply Rmult_le_compat_l; [interval | lra]).
  assert ((u + 1 / 10 ^ 200) * hk = u * hk + 1 / 10 ^ 200 * hk) by field.
  lra.
Qed.

Section NodeHi.
Variable expT sqrtT : R -> R.
Hypothesis Hsq : forall x, 8 / 10 <= x -> x <= 1 -> rel (sqrt x) (sqrtT x) u.
Hypothesis Hex : forall x, -700 <= x -> x <= 1 -> rel (exp x) (expT x) u.

Definition node_bigT s2T xuT bsT hkT :=
  rnd (rnd (hkT * (1 / 2)) + rnd (bsT / (2 * node_xsT s2T xuT))).
Definition node_dT s2T xuT := rnd (1 + node_rsT sqrtT s2T xuT).
Definition node_smallT s2T xuT hkT :=
  rnd (rnd (hkT * node_xsT s2T xuT) / rnd (rnd (2 * node_dT s2T xuT) * node_dT s2T xuT)).
Definition node_term_hi s2T xuT wT bsT hkT hw :=
  if Rlt_dec (node_bigT s2T xuT bsT hkT) 700
  then rnd (hw * rnd (wT * rnd (rnd (expT (- node_bigT s2T xuT bsT hkT) * expT (- node_smallT s2T xuT hkT))
                               / node_rsT sqrtT s2T xuT)))
  else 0.

(** The computed [big + small] against the exact exponent [phi = q + r2]. *)
Lemma split_exponent s xu bs hk s2T xuT bsT hkT e0 xs rs q r2 :
  xs = s * s * xu -> rs = sqrt (1 - xs) -> q = bs / (2 * xs) -> r2 = hk / (1 + rs) ->
  3 / 1000 < s <= 381 / 1000 -> 1 / 4 <= xu <= 1 ->
  0 <= bs -> 0 <= e0 <= / 10 ^ 200 ->
  rel (s * s) s2T u -> rel xu xuT u ->
  rela bs bsT (31 / 10 * u) e0 -> rela hk hkT u e0 -> 16 <= hkT ->
  159 / 10 <= hk /\ 0 <= node_smallT s2T xuT hkT /\ 78 / 10 <= node_bigT s2T xuT bsT hkT /\
  Rabs (node_bigT s2T xuT bsT hkT + node_smallT s2T xuT hkT - (q + r2))
    <= 841 / 100 * (u * q) + 35 / 10 * (u * r2) + 1 / 10 ^ 188 /\
  node_smallT s2T xuT hkT <= 1 / 10 * r2 /\ hk / 2 <= r2 /\
  hk / 2 + q <= 102 / 100 * node_bigT s2T xuT bsT hkT.
Proof.
  intros Hxs_d Hrs_d Hq_d Hr2_d Hs Hxu Hbs He0 Hs2 Hxu2 Hbs2 Hhk2 Hk16.
  destruct Hs as [Hs0 Hs1]. destruct Hxu as [Hxu0 Hxu1].
  pose proof u_pos as Hu. pose proof u_lt as Hu2. pose proof eta_small as Hη.
  pose proof He0 as [He00 He01].
  assert (He0s : e0 <= 1 / 10 ^ 200) by (assert (/ 10 ^ 200 = 1 / 10 ^ 200) by field; lra).
  assert (Hss : 9 / 1000000 <= s * s).
  { pose proof (Rmult_le_compat (3 / 1000) s (3 / 1000) s ltac:(lra) ltac:(lra) (Rlt_le _ _ Hs0) (Rlt_le _ _ Hs0)). lra. }
  assert (Hxs0 : 2 / 10 ^ 6 <= xs).
  { rewrite Hxs_d. assert (2 / 10 ^ 6 <= 9 / 1000000 * (1 / 4)) by interval.
    pose proof (Rmult_le_compat (9 / 1000000) (s * s) (1 / 4) xu ltac:(lra) ltac:(lra) Hss Hxu0). lra. }
  assert (Hxs1 : xs <= 1453 / 10000).
  { rewrite Hxs_d. assert (s * s <= 1453 / 10000).
    { pose proof (Rmult_le_compat s (381 / 1000) s (381 / 1000) ltac:(lra) ltac:(lra) Hs1 Hs1). lra. }
    pose proof (Rmult_le_compat (s * s) (1453 / 10000) xu 1 ltac:(nra) ltac:(lra) H Hxu1). lra. }
  assert (Hxsp : 0 < xs) by (assert (0 < 2 / 10 ^ 6) by interval; lra).
  pose proof (st_xs s xu s2T xuT (conj Hs0 Hs1) (conj Hxu0 Hxu1) Hs2 Hxu2) as H_xs.
  rewrite <- Hxs_d in H_xs. fold (node_xsT s2T xuT) in H_xs.
  set (xsT := node_xsT s2T xuT) in *.
  pose proof (st_om xs xsT (conj Hxsp Hxs1) H_xs) as H_om.
  pose proof (st_rs sqrtT Hsq xs xsT (rnd (1 - xsT)) (conj Hxsp Hxs1) H_xs eq_refl H_om) as H_rs.
  pose proof (rs_bounds xs (conj Hxsp Hxs1)) as [R0 R1].
  rewrite <- Hrs_d in R0, R1, H_rs.
  set (rsT := node_rsT sqrtT s2T xuT) in *.
  assert (H_rs' : rel rs rsT (192 / 100 * u)) by exact H_rs.
  assert (R0' : 924 / 1000 <= rs) by lra.
  pose proof (st_o rs rsT (conj R0' R1) H_rs') as H_o.
  assert (Hxs0b : 2 / 1000000 <= xs) by (assert (2 / 10 ^ 6 = 2 / 1000000) by (simpl; lra); lra).
  pose proof (st_q bs bsT xs xsT e0 (conj Hxs0b Hxs1) He0 H_xs Hbs2) as H_q.
  rewrite <- Hq_d in H_q.
  set (dT := node_dT s2T xuT) in *.
  change (rel (1 + rs) dT (2 * u)) in H_o.
  (* hk *)
  unfold rela in Hhk2.
  assert (Hhk_lo : 159 / 10 <= hk).
  { destruct (Rle_dec 0 hk) as [Hp|Hn].
    - rewrite (Rabs_right hk) in Hhk2 by lra.
      apply Rabs_le_inv in Hhk2. destruct Hhk2 as [A B].
      destruct (Rlt_le_dec hk (159 / 10)) as [Hlt|Hge]; [|exact Hge].
      exfalso.
      assert (u * hk <= u * (159 / 10)) by (apply Rmult_le_compat_l; lra).
      assert (u * (159 / 10) <= 1 / 10 ^ 14) by (assert (12 / 10 ^ 17 * (159 / 10) <= 1 / 10 ^ 14) by interval; nra).
      assert (e0 <= 1 / 10 ^ 14) by (assert (1 / 10 ^ 200 <= 1 / 10 ^ 14) by interval; lra).
      lra.
    - exfalso. rewrite (Rabs_left hk) in Hhk2 by lra.
      apply Rabs_le_inv in Hhk2. destruct Hhk2 as [A B].
      assert (u * - hk <= 1 * - hk) by (apply Rmult_le_compat_r; lra).
      lra. }
  pose proof (rel_hk hk hkT e0 Hhk_lo He00 He0s Hhk2) as Hrh.
  (* r2 and sm *)
  assert (Hrs2 : rs * rs = 1 - xs) by (rewrite Hrs_d; apply sqrt_sqrt; lra).
  pose proof (split_identity hk xs rs Hrs2 ltac:(lra)) as Hid.
  rewrite <- Hr2_d in Hid.
  set (sm := hk * xs / (2 * ((1 + rs) * (1 + rs)))) in *.
  assert (Hsm0 : 0 <= sm).
  { unfold sm. apply Rmult_le_pos; [apply Rmult_le_pos; lra | left; apply Rinv_0_lt_compat; nra]. }
  assert (Hr2h : hk / 2 <= r2) by lra.
  assert (Hsm_eq : sm = r2 * (xs / (2 * (1 + rs)))) by (unfold sm; rewrite Hr2_d; field; lra).
  assert (Hfac : xs / (2 * (1 + rs)) <= 378 / 10000).
  { apply Rmult_le_reg_r with (2 * (1 + rs)); [lra|]. unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. nra. }
  assert (Hfac0 : 0 <= xs / (2 * (1 + rs))) by (apply Rmult_le_pos; [lra | left; apply Rinv_0_lt_compat; lra]).
  assert (Hsmr : sm <= 378 / 10000 * r2).
  { rewrite Hsm_eq. assert (0 <= r2) by lra. apply Rmult_le_compat_l with (r := r2) in Hfac; [|lra]. lra. }
  assert (Hr2lo : 79 / 10 <= r2) by lra.
  (* small *)
  pose proof (small_rel hk hkT xs xsT rs dT Hhk_lo Hk16 Hrh Hxs0 Hxs1 H_xs R0 R1 H_o) as Hsm_rel.
  change (rel sm (node_smallT s2T xuT hkT) (126 / 10 * u)) in Hsm_rel.
  set (smallT := node_smallT s2T xuT hkT) in *.
  assert (HsmT0 : 0 <= smallT).
  { pose proof (rel_lo sm smallT (126 / 10 * u)) as H. 
    assert (Hn : 0 <= sm) by exact Hsm0.
    destruct (Rle_lt_or_eq_dec 0 sm Hn) as [Hlt|Heq].
    - pose proof (H Hlt Hsm_rel) as H1. assert (0 <= (1 - 126 / 10 * u) * sm) by (apply Rmult_le_pos; lra). lra.
    - exfalso. unfold sm in Heq. assert (0 < hk * xs / (2 * ((1 + rs) * (1 + rs)))).
      { apply Rmult_lt_0_compat; [apply Rmult_lt_0_compat; lra | apply Rinv_0_lt_compat; nra]. }
      lra. }
  assert (HsmE : Rabs (smallT - sm) <= 126 / 10 * u * sm).
  { unfold rel in Hsm_rel. rewrite (Rabs_right sm) in Hsm_rel by lra. exact Hsm_rel. }
  (* big *)
  pose proof (rnd_abs (hkT * (1 / 2))) as Hhh.
  rewrite (Rabs_right (hkT * (1 / 2))) in Hhh by lra.
  assert (Hq0 : 0 <= q) by (rewrite Hq_d; apply Rmult_le_pos; [exact Hbs | left; apply Rinv_0_lt_compat; lra]).
  unfold rela in H_q. rewrite (Rabs_right q) in H_q by lra.
  assert (Hbg := rnd_abs (rnd (hkT * (1 / 2)) + rnd (bsT / (2 * xsT)))).
  assert (Hhk3 : Rabs (hkT - hk) <= u * hk + e0) by (rewrite (Rabs_right hk) in Hhk2 by lra; exact Hhk2).
  pose proof (big_err hk hkT q (rnd (bsT / (2 * xsT))) (rnd (hkT * (1 / 2))) (node_bigT s2T xuT bsT hkT) e0
    Hhk_lo Hk16 He00 He0s Hq0 Hhk3 Hhh H_q Hbg) as Hbig.
  assert (Hbigl : 78 / 10 <= node_bigT s2T xuT bsT hkT).
  { apply Rabs_le_inv in Hbig. destruct Hbig as [Hb1 Hb2].
    assert (0 <= u * q) by (apply Rmult_le_pos; lra).
    assert (0 <= u * (hk / 2)) by (apply Rmult_le_pos; lra).
    assert (u * (hk / 2) <= 1 / 100 * (hk / 2)) by (apply Rmult_le_compat_r; lra).
    assert (u * q <= 1 / 100 * q) by (apply Rmult_le_compat_r; lra).
    assert (1 / 10 ^ 188 <= 1 / 100) by interval. nra. }
  assert (Hphi : q + r2 = (hk / 2 + q) + sm) by (rewrite Hid; ring).
  split; [exact Hhk_lo|]. split; [exact HsmT0|]. split; [exact Hbigl|].
  split; [|split; [|split; [exact Hr2h|]]].
  - rewrite Hphi.
    apply Rabs_le_inv in Hbig. destruct Hbig as [Eb1 Eb2].
    apply Rabs_le_inv in HsmE. destruct HsmE as [Es1 Es2].
    assert (Hu1 : u * (hk / 2) <= u * r2) by (apply Rmult_le_compat_l; lra).
    assert (HsE : 126 / 10 * u * sm <= 126 / 10 * u * (378 / 10000 * r2)) by (apply Rmult_le_compat_l; [lra | exact Hsmr]).
    assert (E2 : 126 / 10 * u * (378 / 10000 * r2) = 47628 / 100000 * (u * r2)) by field.
    assert (Hu0 : 0 <= u * r2) by (apply Rmult_le_pos; lra).
    apply Rabs_le. split; lra.
  - apply Rle_trans with ((1 + 126 / 10 * u) * sm).
    + apply Rabs_le_inv in HsmE. destruct HsmE as [Es1 Es2]. nra.
    + assert (Hu3 : u <= 1 / 100) by lra.
      assert (0 <= r2) by lra.
      assert ((1 + 126 / 10 * u) * sm <= (101 / 100) * (378 / 10000 * r2)).
      { apply Rmult_le_compat; [lra | exact Hsm0 | lra | exact Hsmr]. }
      lra.
  - apply Rabs_le_inv in Hbig. destruct Hbig as [Eb1 Eb2].
    assert (Hu1 : u * (hk / 2) <= 1 / 100 * (hk / 2)) by (apply Rmult_le_compat_r; lra).
    assert (Hu2' : u * q <= 1 / 100 * q) by (apply Rmult_le_compat_r; lra).
    assert (1 / 10 ^ 188 <= 1 / 100) by interval.
    nra.
Qed.

Theorem node_error_hi s xu w bs hk s2T xuT wT bsT hkT e0 :
  3 / 1000 < s <= 381 / 1000 -> 1 / 4 <= xu <= 1 -> 1 / 1000 <= w <= 1 / 2 ->
  0 <= bs -> - (4 * hk) <= bs -> 0 <= e0 <= / 10 ^ 200 ->
  rel (s * s) s2T u -> rel xu xuT u -> rel w wT u ->
  rela bs bsT (31 / 10 * u) e0 -> rela hk hkT u e0 -> 16 <= hkT ->
  let xs := s * s * xu in
  let F := exp (- (bs / (2 * xs) + hk / (1 + sqrt (1 - xs)))) / sqrt (1 - xs) in
  Rabs (node_term_hi s2T xuT wT bsT hkT (s / 4) - (s / 4) * w * F)
  <= (s / 4) * w * (117 / 10 * u + 1 / 10 ^ 39).
Proof.
  intros Hs Hxu Hw Hbs Hc He0 Hs2 Hxu2 Hw2 Hbs2 Hhk2 Hk16 xs F.
  destruct Hs as [Hs0 Hs1]. destruct Hxu as [Hxu0 Hxu1]. destruct Hw as [Hw0 Hw1].
  pose proof u_pos as Hu. pose proof u_lt as Hu2.
  assert (Hss : 9 / 1000000 <= s * s).
  { pose proof (Rmult_le_compat (3 / 1000) s (3 / 1000) s ltac:(lra) ltac:(lra) (Rlt_le _ _ Hs0) (Rlt_le _ _ Hs0)). lra. }
  assert (Hxs0 : 2 / 10 ^ 6 <= xs).
  { unfold xs. assert (2 / 10 ^ 6 <= 9 / 1000000 * (1 / 4)) by interval.
    pose proof (Rmult_le_compat (9 / 1000000) (s * s) (1 / 4) xu ltac:(lra) ltac:(lra) Hss Hxu0). lra. }
  assert (Hxs1 : xs <= 1453 / 10000).
  { unfold xs. assert (s * s <= 1453 / 10000).
    { pose proof (Rmult_le_compat s (381 / 1000) s (381 / 1000) ltac:(lra) ltac:(lra) Hs1 Hs1). lra. }
    pose proof (Rmult_le_compat (s * s) (1453 / 10000) xu 1 ltac:(nra) ltac:(lra) H Hxu1). lra. }
  assert (Hxsp : 0 < xs) by (assert (0 < 2 / 10 ^ 6) by interval; lra).
  pose proof (st_xs s xu s2T xuT (conj Hs0 Hs1) (conj Hxu0 Hxu1) Hs2 Hxu2) as H_xs.
  fold xs in H_xs. fold (node_xsT s2T xuT) in H_xs.
  set (xsT := node_xsT s2T xuT) in *.
  pose proof (st_om xs xsT (conj Hxsp Hxs1) H_xs) as H_om.
  pose proof (st_rs sqrtT Hsq xs xsT (rnd (1 - xsT)) (conj Hxsp Hxs1) H_xs eq_refl H_om) as H_rs.
  pose proof (rs_bounds xs (conj Hxsp Hxs1)) as [R0 R1].
  set (rs := sqrt (1 - xs)) in *.
  set (rsT := node_rsT sqrtT s2T xuT) in *.
  assert (H_rs' : rel rs rsT (192 / 100 * u)) by exact H_rs.
  assert (R0' : 924 / 1000 <= rs) by lra.
  pose proof (F_mag xs bs hk (conj Hxs0 Hxs1) Hbs Hc) as [Hph0 [Hpa Hpe]].
  change (0 <= bs / (2 * xs) + hk / (1 + rs)) in Hph0.
  change (bs / (2 * xs) + Rabs (hk / (1 + rs)) <= 1157 / 1000 * (bs / (2 * xs) + hk / (1 + rs))) in Hpa.
  change (exp (- (bs / (2 * xs) + hk / (1 + rs))) * (bs / (2 * xs) + Rabs (hk / (1 + rs))) <= 426 / 1000) in Hpe.
  set (q := bs / (2 * xs)) in *. set (r2 := hk / (1 + rs)) in *.
  set (phi := q + r2) in *. set (pabs := q + Rabs r2) in *.
  pose proof (split_exponent s xu bs hk s2T xuT bsT hkT e0 xs rs q r2 eq_refl eq_refl eq_refl eq_refl
    (conj Hs0 Hs1) (conj Hxu0 Hxu1) Hbs He0 Hs2 Hxu2 Hbs2 Hhk2 Hk16)
    as [Hhk_lo [HsmT0 [Hbigl [Hph [Hsmr [Hr2h Hbigr]]]]]].
  set (bigT := node_bigT s2T xuT bsT hkT) in *.
  set (smallT := node_smallT s2T xuT hkT) in *.
  set (ph := bigT + smallT) in *.
  fold phi in Hph.
  assert (Hq0 : 0 <= q) by (unfold q; apply Rmult_le_pos; [exact Hbs | left; apply Rinv_0_lt_compat; lra]).
  assert (Hr2pos : 79 / 10 <= r2) by lra.
  assert (Hrabs : Rabs r2 = r2) by (apply Rabs_right; lra).
  assert (Hphph : Rabs (ph - phi) <= 85 / 10 * u * pabs + 1 / 10 ^ 40).
  { apply Rabs_le_inv in Hph. destruct Hph as [Ha Hb].
    assert (Hq1 : 0 <= u * q) by (apply Rmult_le_pos; lra).
    assert (Hq2 : 0 <= u * r2) by (apply Rmult_le_pos; lra).
    assert (E1 : 85 / 10 * u * pabs = 85 / 10 * (u * q) + 85 / 10 * (u * r2)) by (unfold pabs; rewrite Hrabs; field).
    assert (1 / 10 ^ 188 <= 1 / 10 ^ 40) by interval.
    apply Rabs_le. split; lra. }
  unfold node_term_hi. fold bigT. fold smallT. fold rsT.
  assert (Hrs0 : 0 < rs) by lra.
  assert (HFp : 0 < F) by (unfold F; apply Rmult_lt_0_compat; [apply exp_pos | apply Rinv_0_lt_compat; lra]).
  assert (Hpabs0 : 0 <= pabs) by (unfold pabs; pose proof (Rabs_pos r2); lra).
  assert (Hhw : 0 < s / 4) by lra.
  assert (HW : 0 < s / 4 * w) by (apply Rmult_lt_0_compat; lra).
  assert (HFup : F <= 10818 / 10000).
  { unfold F. unfold Rdiv.
    assert (Hi : / rs <= / (9244 / 10000)) by (apply Rinv_le_contravar; lra).
    assert (Hi2 : / (9244 / 10000) <= 10818 / 10000) by lra.
    assert (He1 : exp (- phi) <= 1).
    { rewrite <- exp_0. destruct (Rle_lt_or_eq_dec 0 phi Hph0) as [Hl|Heq].
      - left. apply exp_increasing. lra.
      - right. f_equal. lra. }
    pose proof (exp_pos (- phi)). assert (Hi0 : 0 < / rs) by (apply Rinv_0_lt_compat; lra).
    assert (exp (- phi) * / rs <= 1 * (10818 / 10000)) by (apply Rmult_le_compat; [lra | lra | exact He1 | lra]). lra. }
  assert (HFpa : F * pabs <= 4609 / 10000).
  { assert (Hi : / rs <= 10818 / 10000).
    { apply Rle_trans with (/ (9244 / 10000)); [apply Rinv_le_contravar; lra|]. lra. }
    assert (Hi0 : 0 < / rs) by (apply Rinv_0_lt_compat; lra).
    assert (E : F * pabs = / rs * (exp (- phi) * pabs)) by (unfold F; field; lra).
    rewrite E.
    assert (Hp0 : 0 <= exp (- phi) * pabs) by (apply Rmult_le_pos; [left; apply exp_pos | exact Hpabs0]).
    assert (Hm : / rs * (exp (- phi) * pabs) <= 10818 / 10000 * (426 / 1000)).
    { apply Rmult_le_compat; [left; exact Hi0 | exact Hp0 | exact Hi | exact Hpe]. }
    lra. }
  assert (HFdef : F = exp (- phi) / rs) by reflexivity.
  destruct (Rlt_dec bigT 700) as [Hb700|Hb700].
  - (* computed *)
    assert (Hhk1428 : hk <= 1428) by lra.
    assert (Hr2up : r2 <= 52 / 100 * hk).
    { unfold r2. assert (Hinv : / (1 + rs) <= 52 / 100).
      { apply Rmult_le_reg_l with (1 + rs); [lra|]. rewrite Rinv_r by lra. lra. }
      unfold Rdiv. assert (0 <= hk) by lra. nra. }
    assert (HsmT700 : smallT <= 700) by lra.
    pose proof (Hex (- bigT) ltac:(lra) ltac:(lra)) as Hexb.
    pose proof (Hex (- smallT) ltac:(lra) ltac:(lra)) as Hexs.
    set (e1 := expT (- bigT)) in *. set (e2 := expT (- smallT)) in *.
    assert (Hphe : exp (- bigT) * exp (- smallT) = exp (- ph)) by (rewrite <- exp_plus; f_equal; unfold ph; ring).
    destruct (Rlt_dec ph (999 / 10)) as [Hlt|Hge].
    + (* the exponent is under 99.9: the relative bound *)
      pose proof (rel_mul (exp (- bigT)) e1 (exp (- smallT)) e2 u u (Rlt_le _ _ Hu) (Rlt_le _ _ Hu) Hexb Hexs) as Hprod.
      rewrite Hphe in Hprod.
      assert (Hn : nrm (e1 * e2)).
      { apply nrm_pos.
        pose proof (rel_lo (exp (- bigT)) e1 u (exp_pos _) Hexb) as L1.
        pose proof (rel_lo (exp (- smallT)) e2 u (exp_pos _) Hexs) as L2.
        assert (Hexph : exp (- (999 / 10)) <= exp (- ph)) by (left; apply exp_increasing; lra).
        assert (H44 : 1 / 10 ^ 44 <= exp (- (999 / 10))) by interval.
        assert (0 < exp (- bigT)) by apply exp_pos. assert (0 < exp (- smallT)) by apply exp_pos.
        assert (Hp1 : 99 / 100 * exp (- bigT) <= e1) by nra.
        assert (Hp2 : 99 / 100 * exp (- smallT) <= e2) by nra.
        pose proof (Rmult_le_compat (99 / 100 * exp (- bigT)) e1 (99 / 100 * exp (- smallT)) e2 ltac:(nra) ltac:(nra) Hp1 Hp2) as Hp3.
        assert (Hp4 : 99 / 100 * exp (- bigT) * (99 / 100 * exp (- smallT)) = 9801 / 10000 * exp (- ph)) by (rewrite <- Hphe; field).
        assert (1 / 10 ^ 100 <= 9801 / 10000 * (1 / 10 ^ 44)) by interval. nra. }
      assert (Hth0 : 0 <= u + u + u * u) by nra.
      pose proof (rel_rnd (exp (- ph)) (e1 * e2) (u + u + u * u) Hn Hth0 Hprod) as Hrp.
      assert (Hth : (u + u + u * u) + u + u * (u + u + u * u) <= 301 / 100 * u).
      { pose proof uu_small as Huu. pose proof (mul_small (u * u) ltac:(nra)). nra. }
      pose proof (rel_mono _ _ _ _ Hrp Hth) as Hrp'.
      set (eT := rnd (e1 * e2)) in *.
      destruct (ln_lump ph eT (301 / 100 * u) ltac:(lra) ltac:(assert (301 / 100 * (12 / 10 ^ 17) <= 1 / 100) by interval; nra) Hrp') as [HeT0 [HeTe Hln]].
      set (phiT := - ln eT) in *.
      assert (H_phi40 : Rabs (phiT - phi) <= 85 / 10 * u * pabs + 1 / 10 ^ 40).
      { apply Rabs_le_inv in Hln. destruct Hln as [Hl1 Hl2].
        apply Rabs_le_inv in Hph. destruct Hph as [Hp1 Hp2].
        assert (Hq1 : 0 <= u * q) by (apply Rmult_le_pos; lra).
        assert (Hq2 : u * (79 / 10) <= u * r2) by (apply Rmult_le_compat_l; lra).
        assert (E1 : 85 / 10 * u * pabs = 85 / 10 * (u * q) + 85 / 10 * (u * r2)) by (unfold pabs; rewrite Hrabs; field).
        assert (E2 : 102 / 100 * (301 / 100 * u) = 30702 / 10000 * u) by field.
        assert (1 / 10 ^ 188 <= 1 / 10 ^ 40) by interval.
        apply Rabs_le. split; lra. }
      assert (Hlt100 : phiT < 100).
      { apply Rabs_le_inv in Hln. destruct Hln as [Hl1 Hl2]. assert (30702 / 10000 * u <= 1 / 100) by (assert (30702 / 10000 * (12 / 10 ^ 17) <= 1 / 100) by interval; nra). 
        assert (102 / 100 * (301 / 100 * u) = 30702 / 10000 * u) by field. lra. }
      assert (Hp1b : rel (exp (- phiT)) eT u).
      { unfold rel. rewrite HeTe. replace (eT - eT) with 0 by ring. rewrite Rabs_R0. apply Rmult_le_pos; [lra | apply Rabs_pos]. }
      pose proof (exp_stage phi phiT pabs eT rs rsT Hph0 Hpabs0 Hpa H_phi40 Hlt100 (conj R0 R1) H_rs' Hp1b) as [Hp116 [Hrelf [Hef HfT]]].
      set (fT := rnd (eT / rsT)) in *.
      assert (HXu : u * pabs <= 15 / 10 ^ 15).
      { assert (u * pabs <= u * 116) by (apply Rmult_le_compat_l; [lra | exact Hp116]).
        assert (u * 116 <= 15 / 10 ^ 15) by (assert (12 / 10 ^ 17 * 116 <= 15 / 10 ^ 15) by interval; nra). lra. }
      set (th2 := u + 851 / 100 * (u * pabs) + 2 / 10 ^ 40 + 3002 / 1000 * u) in *.
      assert (Hth2a : 0 <= th2) by (unfold th2; assert (0 <= u * pabs) by (apply Rmult_le_pos; lra); assert (0 < 2 / 10 ^ 40) by interval; lra).
      assert (Hth2b : th2 <= 3 / 10 ^ 13).
      { unfold th2. assert (12 / 10 ^ 17 + 851 / 100 * (15 / 10 ^ 15) + 2 / 10 ^ 40 + 3002 / 1000 * (12 / 10 ^ 17) <= 3 / 10 ^ 13) by interval. lra. }
      assert (HF45 : 1 / 10 ^ 45 <= F).
      { assert (Hge' : exp (- phi) <= F).
        { unfold F. unfold Rdiv. assert (Hi : 1 <= / rs) by (rewrite <- Rinv_1; apply Rinv_le_contravar; lra).
          pose proof (exp_pos (- phi)). nra. }
        assert (1 / 10 ^ 45 <= 1 / 10 ^ 44) by interval. lra. }
      pose proof (mul_stage s w wT F fT th2 (conj Hs0 Hs1) (conj Hw0 Hw1) Hw2 Hrelf Hth2a Hth2b HF45 HfT) as Hm.
      unfold rel in Hm.
      set (term := rnd (s / 4 * rnd (wT * fT))) in *.
      replace (s / 4 * w * F) with (s / 4 * (w * F)) by ring.
      assert (HWF : 0 < s / 4 * (w * F)) by (apply Rmult_lt_0_compat; [lra | apply Rmult_lt_0_compat; lra]).
      rewrite (Rabs_right (s / 4 * (w * F))) in Hm by lra.
      pose proof (final_num (s / 4 * w) F pabs u HW HFp HFup HFpa Hpabs0 Hu Hu2) as Hfin.
      assert (E2 : s / 4 * (w * F) = s / 4 * w * F) by ring.
      unfold th2 in Hm. rewrite <- E2 in Hfin.
      lra.
    + (* the exponent is at least 99.9: computed, but tiny *)
      pose proof (Rnot_lt_le _ _ Hge) as Hge2.
      pose proof (small_F2 phi ph pabs F rs Hge2 Hphph Hpa Hph0 R0 HFdef) as HFs.
      pose proof (rel_lo (exp (- bigT)) e1 u (exp_pos _) Hexb) as L1.
      pose proof (rel_hi (exp (- bigT)) e1 u (exp_pos _) Hexb) as U1.
      pose proof (rel_lo (exp (- smallT)) e2 u (exp_pos _) Hexs) as L2.
      pose proof (rel_hi (exp (- smallT)) e2 u (exp_pos _) Hexs) as U2.
      assert (He1 : 0 <= e1) by (pose proof (exp_pos (- bigT)); nra).
      assert (He2 : 0 <= e2) by (pose proof (exp_pos (- smallT)); nra).
      assert (Hp : e1 * e2 <= (1 + u) * (1 + u) * exp (- ph)).
      { rewrite <- Hphe. pose proof (Rmult_le_compat e1 ((1 + u) * exp (- bigT)) e2 ((1 + u) * exp (- smallT)) He1 He2 ltac:(nra) ltac:(nra)). nra. }
      assert (Hp0 : 0 <= e1 * e2) by (apply Rmult_le_pos; assumption).
      destruct (rnd_up (e1 * e2) Hp0) as [Hq0' Hq1'].
      set (eT := rnd (e1 * e2)) in *.
      set (E := (1 + u) * (1 + u) * exp (- ph) + eta).
      assert (Hexph : exp (- ph) <= exp (- (999 / 10))) by (destruct (Rle_lt_or_eq_dec _ _ Hge2) as [Hl|Heq]; [left; apply exp_increasing; lra | right; f_equal; lra]).
      assert (H43 : exp (- (999 / 10)) <= 5 / 10 ^ 44) by interval.
      assert (Hη : eta <= / 10 ^ 300) by exact eta_small.
      assert (HE1 : E <= 1 / 10 ^ 43).
      { unfold E. assert ((1 + u) * (1 + u) * exp (- ph) <= (1 + u) * (1 + u) * (5 / 10 ^ 44)) by (apply Rmult_le_compat_l; [nra | lra]).
        assert (Hu1 : (1 + u) * (1 + u) * (5 / 10 ^ 44) <= (1 + 1 / 10 ^ 12) * (5 / 10 ^ 44)) by (apply Rmult_le_compat_r; [interval | nra]).
        assert ((1 + 1 / 10 ^ 12) * (5 / 10 ^ 44) + / 10 ^ 300 <= 1 / 10 ^ 43) by interval.
        lra. }
      assert (HE0 : 0 <= E).
      { unfold E. pose proof (exp_pos (- ph)) as Hx. assert (0 < eta) by (unfold eta; apply bpow_gt_0).
        assert (0 <= (1 + u) * (1 + u) * exp (- ph)) by (apply Rmult_le_pos; [apply Rmult_le_pos; lra | lra]). lra. }
      assert (HeTE : eT <= (1 + u) * E).
      { assert (Hm1 : (1 + u) * (e1 * e2) <= (1 + u) * ((1 + u) * (1 + u) * exp (- ph))) by (apply Rmult_le_compat_l; lra).
        assert (Eq : (1 + u) * E = (1 + u) * ((1 + u) * (1 + u) * exp (- ph)) + (1 + u) * eta) by (unfold E; ring).
        assert (0 < eta) by (unfold eta; apply bpow_gt_0).
        assert (0 <= u * eta) by (apply Rmult_le_pos; lra).
        lra. }
      assert (HrsT : 9 / 10 <= rsT).
      { pose proof (rel_lo rs rsT (192 / 100 * u) ltac:(lra) H_rs') as Hl.
        assert ((1 - 192 / 100 * u) * rs >= (1 - 192 / 100 * u) * (924 / 1000)) by (apply Rle_ge; apply Rmult_le_compat_l; lra).
        assert (924 / 1000 * (1 - 192 / 100 * u) >= 9 / 10) by (assert (u <= 12 / 10 ^ 17) by lra; nra).
        nra. }
      pose proof (tiny_term (s / 4) w wT eT rsT E
        ltac:(lra) ltac:(lra) Hw0 Hw1 Hw2 Hq0' HeTE HE0 HE1 HrsT) as [Hc0 Hc1].
      assert (HWF : 0 < s / 4 * w * F) by (apply Rmult_lt_0_compat; lra).
      assert (Hbig : s / 4 * w * (1 / 10 ^ 42) <= s / 4 * w * (117 / 10 * u + 1 / 10 ^ 39)).
      { apply Rmult_le_compat_l; [lra|]. assert (1 / 10 ^ 42 <= 1 / 10 ^ 39) by interval. lra. }
      assert (Hwf : s / 4 * w * F <= s / 4 * w * (1 / 10 ^ 39)) by (apply Rmult_le_compat_l; lra).
      assert (Hw39 : s / 4 * w * (1 / 10 ^ 39) <= s / 4 * w * (117 / 10 * u + 1 / 10 ^ 39)).
      { apply Rmult_le_compat_l; lra. }
      apply Rabs_le. split; lra.
  - (* the term is dropped; the exact integrand there is below 1e-39 *)
    assert (Hge : 999 / 10 <= ph) by (unfold ph; lra).
    pose proof (small_F2 phi ph pabs F rs Hge Hphph Hpa Hph0 R0 HFdef) as HFs.
    replace (0 - s / 4 * w * F) with (- (s / 4 * w * F)) by ring.
    rewrite Rabs_Ropp, Rabs_right by (assert (0 < s / 4 * w * F) by (apply Rmult_lt_0_compat; lra); lra).
    pose proof (Rmult_le_compat_l (s / 4 * w) _ _ (Rlt_le _ _ HW) HFs) as Hmm.
    assert (s / 4 * w * (1 / 10 ^ 39) <= s / 4 * w * (117 / 10 * u + 1 / 10 ^ 39)).
    { apply Rmult_le_compat_l; [lra | lra]. }
    lra.
Qed.
End NodeHi.

(** The node as the kernel computes it: [hkT >= 16] selects the split form. *)
Section NodeDispatch.
Variable expT sqrtT : R -> R.
Hypothesis Hsq : forall x, 8 / 10 <= x -> x <= 1 -> rel (sqrt x) (sqrtT x) u.
Hypothesis Hex : forall x, -700 <= x -> x <= 1 -> rel (exp x) (expT x) u.

Definition node_term s2T xuT wT bsT hkT hw :=
  if Rle_dec 16 hkT then node_term_hi expT sqrtT s2T xuT wT bsT hkT hw
  else node_term_lo expT sqrtT s2T xuT wT bsT hkT hw.

Theorem node_error s xu w bs hk s2T xuT wT bsT hkT e0 :
  3 / 1000 < s <= 381 / 1000 -> 1 / 4 <= xu <= 1 -> 1 / 1000 <= w <= 1 / 2 ->
  0 <= bs -> - (4 * hk) <= bs -> 0 <= e0 <= / 10 ^ 200 ->
  rel (s * s) s2T u -> rel xu xuT u -> rel w wT u ->
  rela bs bsT (31 / 10 * u) e0 -> rela hk hkT u e0 ->
  let xs := s * s * xu in
  let F := exp (- (bs / (2 * xs) + hk / (1 + sqrt (1 - xs)))) / sqrt (1 - xs) in
  Rabs (node_term s2T xuT wT bsT hkT (s / 4) - (s / 4) * w * F)
  <= (s / 4) * w * (117 / 10 * u + 1 / 10 ^ 39).
Proof.
  intros H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 xs F.
  unfold node_term. destruct (Rle_dec 16 hkT) as [Hk|Hk].
  - exact (node_error_hi expT sqrtT Hsq Hex s xu w bs hk s2T xuT wT bsT hkT e0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 Hk).
  - exact (node_error_lo expT sqrtT Hsq Hex s xu w bs hk s2T xuT wT bsT hkT e0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11).
Qed.
End NodeDispatch.
