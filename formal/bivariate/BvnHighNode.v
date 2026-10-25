From Coq Require Import Reals Lra Psatz ZArith Lia.
From Interval Require Import Tactic.
From Flocq Require Import Core.
Require Import BvnHighAssembly BvnHighRound BvnHighSteps BvnHighNodeExp BvnHighNodeMul.
Open Scope R_scope.

Lemma final_num W F pabs u0 :
  0 < W -> 0 < F -> F <= 10818 / 10000 -> F * pabs <= 4609 / 10000 -> 0 <= pabs -> 0 < u0 -> u0 < 12 / 10 ^ 17 ->
  (u0 + 851 / 100 * (u0 * pabs) + 2 / 10 ^ 40 + 3002 / 1000 * u0 + 3004 / 1000 * u0) * (W * F)
  <= W * (117 / 10 * u0 + 1 / 10 ^ 39).
Proof.
  intros HW HF HF1 HFp Hp Hu Hu2.
  assert (E1 : (u0 + 851 / 100 * (u0 * pabs) + 2 / 10 ^ 40 + 3002 / 1000 * u0 + 3004 / 1000 * u0) * (W * F)
              = W * (7006 / 1000 * (u0 * F) + 851 / 100 * (u0 * (F * pabs)) + 2 / 10 ^ 40 * F)) by (field).
  rewrite E1. apply Rmult_le_compat_l; [lra|].
  assert (A1 : u0 * F <= u0 * (10818 / 10000)) by (apply Rmult_le_compat_l; lra).
  assert (A2 : u0 * (F * pabs) <= u0 * (4609 / 10000)) by (apply Rmult_le_compat_l; lra).
  assert (A3 : 2 / 10 ^ 40 * F <= 2 / 10 ^ 40 * (10818 / 10000)) by (apply Rmult_le_compat_l; [interval | lra]).
  assert (A4 : 2 / 10 ^ 40 * (10818 / 10000) <= 1 / 10 ^ 39) by interval.
  lra.
Qed.

(** Where the computed exponent argument is at least 100, the exact integrand is below [1e-39]. *)
Lemma small_F phi phiT pabs F rs :
  100 <= phiT -> Rabs (phiT - phi) <= 85 / 10 * u * pabs + 1 / 10 ^ 40 -> pabs <= 1157 / 1000 * phi ->
  0 <= phi -> 9244 / 10000 <= rs -> F = exp (- phi) / rs -> F <= 1 / 10 ^ 39 /\ 999 / 10 <= phi.
Proof.
  intros HphiT H_phi40 Hpa Hph0 Hrs HF.
  pose proof u_pos as Hu. pose proof u_lt as Hu2.
  assert (Hphi99 : 999 / 10 <= phi).
  { pose proof (Rabs_le_inv _ _ H_phi40) as [Hl1 Hl2].
    assert (Hup : 85 / 10 * u * pabs <= 85 / 10 * u * (1157 / 1000 * phi)) by (apply Rmult_le_compat_l; [lra | exact Hpa]).
    assert (Hu3 : u * phi <= 12 / 10 ^ 17 * phi) by (apply Rmult_le_compat_r; lra).
    assert (E1 : 85 / 10 * u * (1157 / 1000 * phi) = 98345 / 10000 * (u * phi)) by field.
    assert (1 / 10 ^ 40 <= 1 / 10) by interval.
    assert (Hc1 : 98345 / 10000 * (12 / 10 ^ 17) <= 1 / 10 ^ 14) by interval.
    assert (Hc2 : 98345 / 10000 * (12 / 10 ^ 17 * phi) <= 1 / 10 ^ 14 * phi) by (nra).
    assert (Hc3 : 1 / 10 ^ 14 * phi <= 1 / 100 * phi) by (assert (1 / 10 ^ 14 <= 1 / 100) by interval; nra).
    lra. }
  split; [|exact Hphi99].
  assert (Hex99 : exp (- (999 / 10)) <= 1 / 10 ^ 43) by interval.
  assert (Hex1 : exp (- phi) <= exp (- (999 / 10))).
  { destruct (Rle_lt_or_eq_dec _ _ Hphi99) as [Hl|Heq].
    - left. apply exp_increasing. lra.
    - right. f_equal. lra. }
  assert (HFl : F <= exp (- phi) * (10818 / 10000)).
  { rewrite HF. unfold Rdiv. assert (Hi : / rs <= / (9244 / 10000)) by (apply Rinv_le_contravar; lra).
    assert (Hi2 : / (9244 / 10000) <= 10818 / 10000) by lra.
    pose proof (exp_pos (- phi)). nra. }
  assert (1 / 10 ^ 43 * (10818 / 10000) <= 1 / 10 ^ 39) by interval.
  pose proof (exp_pos (- phi)). nra.
Qed.

Lemma rnd_up x : 0 <= x -> 0 <= rnd x /\ rnd x <= (1 + u) * x + eta.
Proof.
  intros H. split.
  - pose proof (rnd_le 0 x H) as H1. rewrite rnd_0 in H1. exact H1.
  - pose proof (rnd_abs x) as H2. apply Rabs_le_inv in H2. destruct H2 as [_ H2].
    rewrite (Rabs_right x) in H2 by lra. lra.
Qed.

(** A node whose [phi] is at least 100 but under the kernel's cutoff is computed, and is tiny:
    [exp(-phiT) <= e^-100], so the term is under [hw w e^-100 (1 + tiny)]. *)
Lemma tiny_term hw w wT eT rsT E :
  3 / 4000 <= hw -> hw <= 1 / 10 -> 1 / 1000 <= w -> w <= 1 / 2 -> rel w wT u ->
  0 <= eT -> eT <= (1 + u) * E -> 0 <= E -> E <= 1 / 10 ^ 43 -> 9 / 10 <= rsT ->
  0 <= rnd (hw * rnd (wT * rnd (eT / rsT))) <= hw * w * (1 / 10 ^ 42).
Proof.
  intros Hh0 Hh1 Hw0 Hw1 Hw HeT0 HeT1 HE0 HE1 Hrs.
  pose proof u_pos as Hu. pose proof u_lt as Hu2. pose proof eta_small as Het.
  assert (Hetp : 0 < eta) by (unfold eta; apply bpow_gt_0).
  assert (Hu4 : u <= 1 / 10 ^ 4) by (assert (12 / 10 ^ 17 <= 1 / 10 ^ 4) by interval; lra).
  assert (Het3 : eta <= 1 / 10 ^ 300) by lra.
  assert (Hq0 : 0 <= eT / rsT) by (apply Rmult_le_pos; [exact HeT0 | left; apply Rinv_0_lt_compat; lra]).
  assert (Hq1 : eT / rsT <= 12 / 10 * (1 / 10 ^ 43)).
  { unfold Rdiv. assert (Hi : / rsT <= / (9 / 10)) by (apply Rinv_le_contravar; lra).
    assert (Hi0 : 0 <= / rsT) by (left; apply Rinv_0_lt_compat; lra).
    assert (HeT2 : eT <= 10001 / 10000 * (1 / 10 ^ 43)).
    { assert ((1 + u) * E <= (1 + 1 / 10 ^ 4) * (1 / 10 ^ 43)) by (apply Rmult_le_compat; lra).
      assert ((1 + 1 / 10 ^ 4) * (1 / 10 ^ 43) = 10001 / 10000 * (1 / 10 ^ 43)) by field. lra. }
    assert (Hp : eT * / rsT <= (10001 / 10000 * (1 / 10 ^ 43)) * / (9 / 10)) by (apply Rmult_le_compat; [exact HeT0 | exact Hi0 | exact HeT2 | exact Hi]).
    assert ((10001 / 10000 * (1 / 10 ^ 43)) * / (9 / 10) <= 12 / 10 * (1 / 10 ^ 43)) by interval.
    lra. }
  destruct (rnd_up _ Hq0) as [F0 F1].
  set (f := rnd (eT / rsT)) in *.
  assert (Hf : f <= 2 / 10 ^ 43).
  { assert ((1 + u) * (eT / rsT) <= (1 + 1 / 10 ^ 4) * (12 / 10 * (1 / 10 ^ 43))) by (apply Rmult_le_compat; lra).
    assert ((1 + 1 / 10 ^ 4) * (12 / 10 * (1 / 10 ^ 43)) + 1 / 10 ^ 300 <= 2 / 10 ^ 43) by interval. lra. }
  assert (HwT0 : 0 <= wT).
  { pose proof (rel_lo w wT u ltac:(lra) Hw) as Hl. assert (0 <= (1 - u) * w) by (apply Rmult_le_pos; lra). lra. }
  assert (HwT1 : wT <= (1 + 1 / 10 ^ 4) * w).
  { pose proof (rel_hi w wT u ltac:(lra) Hw) as Hl.
    assert ((1 + u) * w <= (1 + 1 / 10 ^ 4) * w) by (apply Rmult_le_compat_r; lra). lra. }
  assert (F00 : 0 <= f) by exact F0.
  assert (Hg0 : 0 <= wT * f) by (apply Rmult_le_pos; lra).
  assert (Hwf : wT * f <= ((1 + 1 / 10 ^ 4) * w) * (2 / 10 ^ 43)) by (apply Rmult_le_compat; lra).
  destruct (rnd_up _ Hg0) as [G0 G1].
  set (g := rnd (wT * f)) in *.
  assert (Hg : g <= (1 + 1 / 10 ^ 4) * (((1 + 1 / 10 ^ 4) * w) * (2 / 10 ^ 43)) + 1 / 10 ^ 300).
  { assert ((1 + u) * (wT * f) <= (1 + 1 / 10 ^ 4) * (((1 + 1 / 10 ^ 4) * w) * (2 / 10 ^ 43))) by (apply Rmult_le_compat; lra). lra. }
  assert (Hc0 : 0 <= hw * g) by (apply Rmult_le_pos; lra).
  destruct (rnd_up _ Hc0) as [C0 C1].
  split; [exact C0|].
  assert (Hhg : hw * g <= hw * ((1 + 1 / 10 ^ 4) * (((1 + 1 / 10 ^ 4) * w) * (2 / 10 ^ 43)) + 1 / 10 ^ 300)) by (apply Rmult_le_compat_l; lra).
  assert (Eq : hw * ((1 + 1 / 10 ^ 4) * (((1 + 1 / 10 ^ 4) * w) * (2 / 10 ^ 43)) + 1 / 10 ^ 300)
               = (hw * w) * ((1 + 1 / 10 ^ 4) * (1 + 1 / 10 ^ 4) * (2 / 10 ^ 43)) + hw * (1 / 10 ^ 300)) by ring.
  assert (Hhe : hw * (1 / 10 ^ 300) <= 1 * (1 / 10 ^ 300)) by (apply Rmult_le_compat_r; [interval | lra]).
  assert (HP : 7 / 10 ^ 7 <= hw * w).
  { assert (3 / 4000 * (1 / 1000) <= hw * w) by (apply Rmult_le_compat; [interval | interval | lra | lra]).
    assert (7 / 10 ^ 7 <= 3 / 4000 * (1 / 1000)) by interval. lra. }
  set (P := hw * w) in *.
  assert (Hcc : (1 + u) * (hw * g) + eta <= (1 + 1 / 10 ^ 4) * (P * (1 + 1 / 10 ^ 4) * (1 + 1 / 10 ^ 4) * (2 / 10 ^ 43) + 1 / 10 ^ 300) + 1 / 10 ^ 300).
  { assert ((1 + u) * (hw * g) <= (1 + 1 / 10 ^ 4) * (hw * ((1 + 1 / 10 ^ 4) * (((1 + 1 / 10 ^ 4) * w) * (2 / 10 ^ 43)) + 1 / 10 ^ 300)))
      by (apply Rmult_le_compat; lra).
    rewrite Eq in H. nra. }
  assert (Hfin : (1 + 1 / 10 ^ 4) * (P * (1 + 1 / 10 ^ 4) * (1 + 1 / 10 ^ 4) * (2 / 10 ^ 43) + 1 / 10 ^ 300) + 1 / 10 ^ 300 <= P * (1 / 10 ^ 42)).
  { assert (Hk : (1 + 1 / 10 ^ 4) * ((1 + 1 / 10 ^ 4) * (1 + 1 / 10 ^ 4)) * (2 / 10 ^ 43) <= 3 / 10 ^ 43) by interval.
    assert (E3 : (1 + 1 / 10 ^ 4) * (P * (1 + 1 / 10 ^ 4) * (1 + 1 / 10 ^ 4) * (2 / 10 ^ 43) + 1 / 10 ^ 300) + 1 / 10 ^ 300
              = P * ((1 + 1 / 10 ^ 4) * ((1 + 1 / 10 ^ 4) * (1 + 1 / 10 ^ 4)) * (2 / 10 ^ 43)) + ((1 + 1 / 10 ^ 4) * (1 / 10 ^ 300) + 1 / 10 ^ 300)) by ring.
    rewrite E3.
    assert (Hm : P * ((1 + 1 / 10 ^ 4) * ((1 + 1 / 10 ^ 4) * (1 + 1 / 10 ^ 4)) * (2 / 10 ^ 43)) <= P * (3 / 10 ^ 43)) by (apply Rmult_le_compat_l; [lra | exact Hk]).
    assert (Hrest : (1 + 1 / 10 ^ 4) * (1 / 10 ^ 300) + 1 / 10 ^ 300 <= 7 / 10 ^ 7 * (7 / 10 ^ 43)) by interval.
    assert (Hr2 : 7 / 10 ^ 7 * (7 / 10 ^ 43) <= P * (7 / 10 ^ 43)) by (apply Rmult_le_compat_r; [interval | lra]).
    assert (P * (3 / 10 ^ 43) + P * (7 / 10 ^ 43) = P * (1 / 10 ^ 42)) by field.
    lra. }
  lra.
Qed.

Section NodeThm.
Variable expT sqrtT : R -> R.
Hypothesis Hsq : forall x, 8 / 10 <= x -> x <= 1 -> rel (sqrt x) (sqrtT x) u.
Hypothesis Hex : forall x, -700 <= x -> x <= 1 -> rel (exp x) (expT x) u.

Definition node_xsT s2T xuT := rnd (s2T * xuT).
Definition node_rsT s2T xuT := sqrtT (rnd (1 - node_xsT s2T xuT)).
Definition node_phiT s2T xuT bsT hkT :=
  rnd (rnd (bsT / (2 * node_xsT s2T xuT)) + rnd (hkT / rnd (1 + node_rsT s2T xuT))).
Definition node_term s2T xuT wT bsT hkT hw :=
  if Rlt_dec (node_phiT s2T xuT bsT hkT) 700
  then rnd (hw * rnd (wT * rnd (expT (- node_phiT s2T xuT bsT hkT) / node_rsT s2T xuT)))
  else 0.

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
  intros Hs Hxu Hw Hbs Hc He0 Hs2 Hxu2 Hw2 Hbs2 Hhk2 xs F.
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
  set (rsT := node_rsT s2T xuT) in *.
  assert (H_rs' : rel rs rsT (192 / 100 * u)) by exact H_rs.
  assert (R0' : 924 / 1000 <= rs) by lra.
  pose proof (st_o rs rsT (conj R0' R1) H_rs') as H_o.
  assert (Hxs0b : 2 / 1000000 <= xs) by (assert (2 / 10 ^ 6 = 2 / 1000000) by (simpl; lra); lra).
  pose proof (st_q bs bsT xs xsT e0 (conj Hxs0b Hxs1) He0 H_xs Hbs2) as H_q.
  pose proof (st_r2 hk hkT rs (rnd (1 + rsT)) e0 (conj R0 R1) He0 Hhk2 H_o) as H_r2.
  clear He0 Hbs2 Hhk2.
  assert (Hq0 : 0 <= bs / (2 * xs)) by (apply Rmult_le_pos; [exact Hbs | left; apply Rinv_0_lt_compat; lra]).
  pose proof (st_phi _ _ _ _ Hq0 H_q H_r2) as H_phi.
  pose proof (F_mag xs bs hk (conj Hxs0 Hxs1) Hbs Hc) as [Hph0 [Hpa Hpe]].
  change (0 <= bs / (2 * xs) + hk / (1 + rs)) in Hph0.
  change (bs / (2 * xs) + Rabs (hk / (1 + rs)) <= 1157 / 1000 * (bs / (2 * xs) + hk / (1 + rs))) in Hpa.
  change (exp (- (bs / (2 * xs) + hk / (1 + rs))) * (bs / (2 * xs) + Rabs (hk / (1 + rs))) <= 426 / 1000) in Hpe.
  set (q := bs / (2 * xs)) in *. set (r2 := hk / (1 + rs)) in *.
  set (phi := q + r2) in *. set (pabs := q + Rabs r2) in *.
  set (phiT := node_phiT s2T xuT bsT hkT) in *.
  assert (H_phi' : Rabs (phiT - phi) <= 85 / 10 * u * pabs + 1 / 10 ^ 189) by exact H_phi.
  assert (H_phi40 : Rabs (phiT - phi) <= 85 / 10 * u * pabs + 1 / 10 ^ 40).
  { assert (1 / 10 ^ 189 <= 1 / 10 ^ 40) by interval. lra. }
  unfold node_term. fold phiT. fold rsT.
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
  destruct (Rlt_dec phiT 700) as [H700|H700].
  - destruct (Rlt_dec phiT 100) as [Hlt|Hge].
    + pose proof (Rabs_le_inv _ _ H_phi40) as [Hl1 Hl2].
      assert (HphiT0 : -1 <= phiT).
      { assert (Hu1 : 85 / 10 * u * pabs <= 85 / 10 * u * (1157 / 1000 * phi)) by (apply Rmult_le_compat_l; [lra | exact Hpa]).
        assert (Hu3 : u * phi <= 1 / 20 * phi) by (apply Rmult_le_compat_r; lra).
        assert (E1 : 85 / 10 * u * (1157 / 1000 * phi) = 98345 / 10000 * (u * phi)) by field.
        assert (1 / 10 ^ 40 <= 1) by interval.
        lra. }
      pose proof (Hex (- phiT) ltac:(lra) ltac:(lra)) as Hp1b.
      pose proof (exp_stage phi phiT pabs (expT (- phiT)) rs rsT Hph0 Hpabs0 Hpa H_phi40 Hlt (conj R0 R1) H_rs' Hp1b) as [Hp116 [Hrelf [Hef HfT]]].
      set (fT := rnd (expT (- phiT) / rsT)) in *.
      assert (HXu : u * pabs <= 15 / 10 ^ 15).
      { assert (u * pabs <= u * 116) by (apply Rmult_le_compat_l; [lra | exact Hp116]).
        assert (u * 116 <= 15 / 10 ^ 15) by (assert (12 / 10 ^ 17 * 116 <= 15 / 10 ^ 15) by interval; nra). lra. }
      set (th2 := u + 851 / 100 * (u * pabs) + 2 / 10 ^ 40 + 3002 / 1000 * u) in *.
      assert (Hth2a : 0 <= th2) by (unfold th2; assert (0 <= u * pabs) by (apply Rmult_le_pos; lra); assert (0 < 2 / 10 ^ 40) by interval; lra).
      assert (Hth2b : th2 <= 3 / 10 ^ 13).
      { unfold th2. assert (12 / 10 ^ 17 + 851 / 100 * (15 / 10 ^ 15) + 2 / 10 ^ 40 + 3002 / 1000 * (12 / 10 ^ 17) <= 3 / 10 ^ 13) by interval. lra. }
      assert (HF45 : 1 / 10 ^ 45 <= F).
      { assert (Hge : exp (- phi) <= F).
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
    + (* computed, but tiny: the exact integrand is below 1e-39 and the term below 1e-42 of its weight *)
      destruct (small_F phi phiT pabs F rs (Rnot_lt_le _ _ Hge) H_phi40 Hpa Hph0 R0 HFdef) as [HFs Hphi99].
      pose proof (Hex (- phiT) ltac:(lra) ltac:(lra)) as Hp1b.
      assert (HeT0 : 0 <= expT (- phiT)).
      { pose proof (rel_lo (exp (- phiT)) (expT (- phiT)) u (exp_pos _) Hp1b) as Hl.
        pose proof (exp_pos (- phiT)). nra. }
      assert (HeT1 : expT (- phiT) <= (1 + u) * exp (- phiT)) by exact (rel_hi (exp (- phiT)) (expT (- phiT)) u (exp_pos _) Hp1b).
      assert (HE1 : exp (- phiT) <= 1 / 10 ^ 43).
      { assert (Hx : exp (- 100) <= 1 / 10 ^ 43) by interval.
        assert (exp (- phiT) <= exp (- 100)).
        { destruct (Rle_lt_or_eq_dec 100 phiT (Rnot_lt_le _ _ Hge)) as [Hl|Heq].
          - left. apply exp_increasing. lra.
          - right. f_equal. lra. }
        lra. }
      assert (HrsT : 9 / 10 <= rsT).
      { pose proof (rel_lo rs rsT (192 / 100 * u) ltac:(lra) H_rs') as Hl.
        assert ((1 - 192 / 100 * u) * rs >= (1 - 192 / 100 * u) * (924 / 1000)) by (apply Rle_ge; apply Rmult_le_compat_l; lra).
        assert (924 / 1000 * (1 - 192 / 100 * u) >= 9 / 10) by (assert (u <= 12 / 10 ^ 17) by lra; nra).
        nra. }
      pose proof (tiny_term (s / 4) w wT (expT (- phiT)) rsT (exp (- phiT))
        ltac:(lra) ltac:(lra) Hw0 Hw1 Hw2 HeT0 HeT1 (Rlt_le _ _ (exp_pos _)) HE1 HrsT) as [Hc0 Hc1].
      change (rnd (s / 4 * rnd (wT * rnd (expT (- phiT) / rsT)))) with (rnd (s / 4 * rnd (wT * rnd (expT (- phiT) / rsT)))) in *.
      assert (HWF : 0 < s / 4 * w * F) by (apply Rmult_lt_0_compat; lra).
      assert (Hbig : s / 4 * w * (1 / 10 ^ 42) <= s / 4 * w * (117 / 10 * u + 1 / 10 ^ 39)).
      { apply Rmult_le_compat_l; [lra|]. assert (1 / 10 ^ 42 <= 1 / 10 ^ 39) by interval. lra. }
      assert (Hwf : s / 4 * w * F <= s / 4 * w * (1 / 10 ^ 39)) by (apply Rmult_le_compat_l; lra).
      assert (Hw39 : s / 4 * w * (1 / 10 ^ 39) <= s / 4 * w * (117 / 10 * u + 1 / 10 ^ 39)).
      { apply Rmult_le_compat_l; lra. }
      apply Rabs_le. split; nra.
  - (* the term is dropped; the exact integrand there is below 1e-39 *)
    assert (Hge : 100 <= phiT) by lra.
    destruct (small_F phi phiT pabs F rs Hge H_phi40 Hpa Hph0 R0 HFdef) as [HFs _].
    replace (0 - s / 4 * w * F) with (- (s / 4 * w * F)) by ring.
    rewrite Rabs_Ropp, Rabs_right by (assert (0 < s / 4 * w * F) by (apply Rmult_lt_0_compat; lra); lra).
    assert (0 <= u) by lra.
    pose proof (Rmult_le_compat_l (s / 4 * w) _ _ (Rlt_le _ _ HW) HFs) as Hmm.
    assert (s / 4 * w * (1 / 10 ^ 39) <= s / 4 * w * (117 / 10 * u + 1 / 10 ^ 39)).
    { apply Rmult_le_compat_l; [lra | lra]. }
    lra.
Qed.
End NodeThm.
