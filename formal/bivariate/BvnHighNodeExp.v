From Coq Require Import Reals Lra Psatz ZArith Lia.
From Interval Require Import Tactic.
From Flocq Require Import Core.
Require Import BvnHighAssembly BvnHighRound BvnHighSteps.
Open Scope R_scope.

Lemma exp_stage phi phiT pabs eT rs rsT :
  0 <= phi -> 0 <= pabs -> pabs <= 1157 / 1000 * phi ->
  Rabs (phiT - phi) <= 85 / 10 * u * pabs + 1 / 10 ^ 40 -> phiT < 100 ->
  9244 / 10000 <= rs <= 1 -> rel rs rsT (192 / 100 * u) -> rel (exp (- phiT)) eT u ->
  pabs <= 116 /\
  rel (exp (- phi) / rs) (rnd (eT / rsT)) (u + 851 / 100 * (u * pabs) + 2 / 10 ^ 40 + 3002 / 1000 * u) /\
  1 / 10 ^ 44 <= exp (- phi) /\ 1 / 10 ^ 50 <= rnd (eT / rsT).
Proof.
  intros Hph0 Hpabs0 Hpa Hphi Hlt [R0 R1] H_rs' Hp1b.
  pose proof u_pos as Hu. pose proof u_lt as Hu2.
  assert (HE0 : 0 < 1 / 10 ^ 40) by interval.
  assert (HE1 : 1 / 10 ^ 40 <= 1 / 10 ^ 30) by interval.
  set (E := 1 / 10 ^ 40) in *.
  pose proof (Rabs_le_inv _ _ Hphi) as [Hl1 Hl2].
  assert (Hpa116 : pabs <= 116).
  { apply Rnot_lt_le. intro Hcc.
    assert (Hup : 85 / 10 * u * pabs * (1157 / 1000) <= 1 / 10 ^ 14 * pabs).
    { assert (85 / 10 * u * (1157 / 1000) <= 1 / 10 ^ 14) by nra. nra. }
    assert (E <= 1 / 10) by (unfold E; interval).
    nra. }
  assert (HX0 : 0 <= u * pabs) by nra.
  assert (HX1 : u * pabs <= 15 / 10 ^ 15).
  { assert (u * pabs <= u * 116) by (apply Rmult_le_compat_l; [lra | exact Hpa116]).
    assert (u * 116 <= 15 / 10 ^ 15) by (assert (12 / 10 ^ 17 * 116 <= 15 / 10 ^ 15) by interval; nra). lra. }
  assert (HX1' : u * pabs <= 2 / 10 ^ 13) by (assert (15 / 10 ^ 15 <= 2 / 10 ^ 13) by interval; lra).
  pose proof (theta1_bound u (u * pabs) E Hu Hu2 HX0 HX1' HE0 HE1) as Hth. cbv zeta in Hth.
  set (D := 85 / 10 * (u * pabs) + E) in *.
  assert (HDeq : D = 85 / 10 * (u * pabs) + E) by reflexivity.
  assert (Hphi' : Rabs (phiT - phi) <= D) by (unfold D; replace (85 / 10 * (u * pabs)) with (85 / 10 * u * pabs) by ring; exact Hphi).
  assert (HD0 : 0 <= D) by (rewrite HDeq; lra).
  assert (HDs : D <= 3 / 10 ^ 12).
  { rewrite HDeq. assert (85 / 10 * (2 / 10 ^ 13) <= 2 / 10 ^ 12) by interval.
    assert (1 / 10 ^ 30 <= 1 / 10 ^ 12) by interval. lra. }
  assert (HDh : D <= 1 / 2) by (assert (3 / 10 ^ 12 <= 1 / 2) by interval; lra).
  pose proof (exp_pert phi phiT D Hphi' HD0 HDh) as Hp1.
  pose proof (rel_trans (exp (- phi)) (exp (- phiT)) eT (D + 2 * (D * D)) u ltac:(nra) (Rlt_le _ _ Hu) Hp1 Hp1b) as Hp2.
  set (L1 := u + 851 / 100 * (u * pabs) + 2 * E).
  assert (HL1' : L1 <= 1 / 10 ^ 12).
  { unfold L1.
    assert (12 / 10 ^ 17 + 851 / 100 * (15 / 10 ^ 15) + 2 * (1 / 10 ^ 30) <= 1 / 10 ^ 12) by interval.
    assert (2 * E <= 2 * (1 / 10 ^ 30)) by lra. lra. }
  assert (HL1s : L1 <= 2 / 10 ^ 13).
  { unfold L1. assert (12 / 10 ^ 17 + 851 / 100 * (15 / 10 ^ 15) + 2 * (1 / 10 ^ 30) <= 2 / 10 ^ 13) by interval.
    assert (2 * E <= 2 * (1 / 10 ^ 30)) by lra. lra. }
  assert (HL10 : 0 <= L1) by (unfold L1; lra).
  assert (Hth' : D + 2 * (D * D) + u * (1 + (D + 2 * (D * D))) <= L1) by (rewrite HDeq; exact Hth).
  pose proof (rel_mono (exp (- phi)) eT _ L1 Hp2 Hth') as Hp3.
  pose proof (rel_div (exp (- phi)) eT rs rsT L1 (192 / 100 * u) ltac:(lra) HL10 ltac:(lra) ltac:(lra) Hp3 H_rs') as Hdv.
  assert (Hau : 0 <= 192 / 100 * u <= 2 * u) by (split; lra).
  pose proof (ch_div L1 (192 / 100 * u) L1 HL10 (Rle_refl L1) HL1' Hau) as Hdv2.
  assert (Hq1 : L1 + 2 * u + 1 / 1000 * u <= L1 + 2001 / 1000 * u) by lra.
  pose proof (rel_mono (exp (- phi) / rs) (eT / rsT) _ (L1 + 2001 / 1000 * u) Hdv (Rle_trans _ _ _ Hdv2 Hq1)) as Hdv3.
  assert (Hex101 : 1 / 10 ^ 44 <= exp (- 101)) by interval.
  assert (Hphi101 : phi <= 101) by (assert (phi <= phiT + D) by lra; lra).
  assert (Hephi : exp (- 101) <= exp (- phi)).
  { destruct (Rle_lt_or_eq_dec _ _ (Ropp_le_contravar _ _ Hphi101)) as [Hl|Heq].
    - left. apply exp_increasing. exact Hl.
    - right. f_equal. lra. }
  assert (Hef : 1 / 10 ^ 44 <= exp (- phi)) by lra.
  pose proof (rel_lo (exp (- phi)) eT L1 (exp_pos _) Hp3) as HeTlo.
  assert (HeT : 9 / 10 * (1 / 10 ^ 44) <= eT).
  { assert (0 <= 1 / 10 ^ 44) by interval. assert (L1 <= 1 / 10) by (assert (1 / 10 ^ 12 <= 1 / 10) by interval; lra).
    assert ((1 - L1) * (1 / 10 ^ 44) <= (1 - L1) * exp (- phi)) by (apply Rmult_le_compat_l; lra).
    assert (9 / 10 * (1 / 10 ^ 44) <= (1 - L1) * (1 / 10 ^ 44)) by nra. lra. }
  pose proof (rel_hi rs rsT (192 / 100 * u) ltac:(lra) H_rs') as HrsTh.
  pose proof (rel_lo rs rsT (192 / 100 * u) ltac:(lra) H_rs') as HrsTl.
  assert (HrsT0 : 0 < rsT).
  { assert (0 < (1 - 192 / 100 * u) * rs) by (apply Rmult_lt_0_compat; lra). lra. }
  assert (HrsT1 : rsT <= 11 / 10).
  { assert ((1 + 192 / 100 * u) * rs <= (1 + 192 / 100 * u) * 1) by (apply Rmult_le_compat_l; lra). lra. }
  assert (HfT0 : 1 / 10 ^ 50 <= eT / rsT).
  { assert (Hi : / (11 / 10) <= / rsT) by (apply Rinv_le_contravar; lra).
    unfold Rdiv.
    assert (Hm : 9 / 10 * (1 / 10 ^ 44) * / (11 / 10) <= eT * / rsT).
    { apply Rmult_le_compat; [interval | lra | exact HeT | exact Hi]. }
    assert (E2 : / (11 / 10) = 10 / 11) by field. rewrite E2 in Hm.
    assert (1 / 10 ^ 50 <= 9 / 10 * (1 / 10 ^ 44) * (10 / 11)) by interval. lra. }
  pose proof (rel_rnd (exp (- phi) / rs) (eT / rsT) (L1 + 2001 / 1000 * u) (nrm_pos (eT / rsT) (ltac:(assert (1 / 10 ^ 100 <= 1 / 10 ^ 50) by interval; lra))) ltac:(lra) Hdv3) as Hf.
  assert (Hch : (L1 + 2001 / 1000 * u) + u + u * (L1 + 2001 / 1000 * u) <= L1 + 2001 / 1000 * u + 1001 / 1000 * u).
  { pose proof (ch_rnd (L1 + 2001 / 1000 * u) (L1 + 2001 / 1000 * u) ltac:(lra) ltac:(lra) ltac:(assert (3 * (12 / 10 ^ 17) <= 1 / 10 ^ 13) by interval; assert (2 / 10 ^ 13 + 1 / 10 ^ 13 <= 1 / 10 ^ 12) by interval; lra)). lra. }
  assert (Hq2 : (L1 + 2001 / 1000 * u) + u + u * (L1 + 2001 / 1000 * u) <= L1 + 3002 / 1000 * u) by lra.
  pose proof (rel_mono (exp (- phi) / rs) (rnd (eT / rsT)) _ (L1 + 3002 / 1000 * u) Hf Hq2) as Hf2.
  split; [exact Hpa116|]. split.
  - unfold L1 in Hf2. replace (u + 851 / 100 * (u * pabs) + 2 / 10 ^ 40 + 3002 / 1000 * u) with (u + 851 / 100 * (u * pabs) + 2 * E + 3002 / 1000 * u) by (unfold E; field). exact Hf2.
  - split; [exact Hef|].
    pose proof (rel_lo (exp (- phi) / rs) (rnd (eT / rsT)) (L1 + 3002 / 1000 * u) ltac:(apply Rdiv_lt_0_compat; [apply exp_pos | lra]) Hf2) as Hlo.
    assert (HF : 1 / 10 ^ 45 <= exp (- phi) / rs).
    { unfold Rdiv. assert (Hi : 1 <= / rs) by (rewrite <- Rinv_1; apply Rinv_le_contravar; lra).
      assert (0 <= exp (- phi)) by (left; apply exp_pos). nra. }
    assert (1 / 10 ^ 50 <= (1 - (L1 + 3002 / 1000 * u)) * (1 / 10 ^ 45)) by (assert (L1 + 3002 / 1000 * u <= 1 / 2) by (assert (1 / 10 ^ 12 + 3002 / 1000 * (12 / 10 ^ 17) <= 1 / 2) by interval; lra); assert (1 / 10 ^ 50 <= 1 / 2 * (1 / 10 ^ 45)) by interval; nra).
    assert ((1 - (L1 + 3002 / 1000 * u)) * (1 / 10 ^ 45) <= (1 - (L1 + 3002 / 1000 * u)) * (exp (- phi) / rs)).
    { apply Rmult_le_compat_l; [|exact HF]. assert (L1 + 3002 / 1000 * u <= 1 / 2) by (assert (1 / 10 ^ 12 + 3002 / 1000 * (12 / 10 ^ 17) <= 1 / 2) by interval; lra). lra. }
    lra.
Qed.
