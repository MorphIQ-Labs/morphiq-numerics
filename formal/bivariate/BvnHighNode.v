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

Section NodeThm.
Variable expT sqrtT : R -> R.
Hypothesis Hsq : forall x, 8 / 10 <= x -> x <= 1 -> rel (sqrt x) (sqrtT x) u.
Hypothesis Hex : forall x, -101 <= x -> x <= 1 -> rel (exp x) (expT x) u.

Definition node_xsT s2T xuT := rnd (s2T * xuT).
Definition node_rsT s2T xuT := sqrtT (rnd (1 - node_xsT s2T xuT)).
Definition node_phiT s2T xuT bsT hkT :=
  rnd (rnd (bsT / (2 * node_xsT s2T xuT)) + rnd (hkT / rnd (1 + node_rsT s2T xuT))).
Definition node_term s2T xuT wT bsT hkT hw :=
  if Rlt_dec (node_phiT s2T xuT bsT hkT) 100
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
  destruct (Rlt_dec phiT 100) as [Hlt|Hge].
  - pose proof (Rabs_le_inv _ _ H_phi40) as [Hl1 Hl2].
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
  - (* the term is dropped; the exact integrand there is below 1e-39 *)
    assert (Hphi99 : 999 / 10 <= phi).
    { pose proof (Rabs_le_inv _ _ H_phi40) as [Hl1 Hl2].
      assert (HphiT : 100 <= phiT) by (apply Rnot_lt_le; exact Hge).
      assert (Hup : 85 / 10 * u * pabs <= 85 / 10 * u * (1157 / 1000 * phi)) by (apply Rmult_le_compat_l; [lra | exact Hpa]).
      assert (Hu3 : u * phi <= 12 / 10 ^ 17 * phi) by (apply Rmult_le_compat_r; lra).
      assert (E1 : 85 / 10 * u * (1157 / 1000 * phi) = 98345 / 10000 * (u * phi)) by field.
      assert (1 / 10 ^ 40 <= 1 / 10) by interval.
      assert (Hc1 : 98345 / 10000 * (12 / 10 ^ 17) <= 1 / 10 ^ 14) by interval.
      assert (Hc2 : 98345 / 10000 * (12 / 10 ^ 17 * phi) <= 1 / 10 ^ 14 * phi) by (assert (0 <= phi) by lra; nra).
      assert (Hc3 : 1 / 10 ^ 14 * phi <= 1 / 100 * phi) by (assert (1 / 10 ^ 14 <= 1 / 100) by interval; nra).
      lra. }
    assert (HFs : F <= 1 / 10 ^ 39).
    { assert (Hex99 : exp (- (999 / 10)) <= 1 / 10 ^ 43) by interval.
      assert (Hex1 : exp (- phi) <= exp (- (999 / 10))).
      { destruct (Rle_lt_or_eq_dec _ _ Hphi99) as [Hl|Heq].
        - left. apply exp_increasing. lra.
        - right. f_equal. lra. }
      assert (HFl : F <= exp (- phi) * (10818 / 10000)).
      { unfold F. unfold Rdiv. assert (Hi : / rs <= / (9244 / 10000)) by (apply Rinv_le_contravar; lra).
        assert (Hi2 : / (9244 / 10000) <= 10818 / 10000) by lra.
        pose proof (exp_pos (- phi)). nra. }
      assert (1 / 10 ^ 43 * (10818 / 10000) <= 1 / 10 ^ 39) by interval.
      pose proof (exp_pos (- phi)). nra. }
    replace (0 - s / 4 * w * F) with (- (s / 4 * w * F)) by ring.
    rewrite Rabs_Ropp, Rabs_right by (assert (0 < s / 4 * w * F) by (apply Rmult_lt_0_compat; lra); lra).
    assert (0 <= u) by lra.
    pose proof (Rmult_le_compat_l (s / 4 * w) _ _ (Rlt_le _ _ HW) HFs) as Hmm.
    assert (s / 4 * w * (1 / 10 ^ 39) <= s / 4 * w * (117 / 10 * u + 1 / 10 ^ 39)).
    { apply Rmult_le_compat_l; [lra | lra]. }
    lra.
Qed.
End NodeThm.
