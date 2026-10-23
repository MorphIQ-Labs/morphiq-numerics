From Coq Require Import Reals Lra Psatz ZArith Lia.
From Interval Require Import Tactic.
From Flocq Require Import Core.
Require Import BvnHighAssembly BvnHighRound N1head N2.
Open Scope R_scope.

Lemma mul_stage s w wT F fT th2 :
  3 / 1000 < s <= 381 / 1000 -> 1 / 1000 <= w <= 1 / 2 -> rel w wT u -> rel F fT th2 ->
  0 <= th2 -> th2 <= 3 / 10 ^ 13 -> 1 / 10 ^ 45 <= F -> 1 / 10 ^ 50 <= fT ->
  rel (s / 4 * (w * F)) (rnd (s / 4 * rnd (wT * fT))) (th2 + 3004 / 1000 * u).
Proof.
  intros [Hs0 Hs1] [Hw0 Hw1] Hw Hf Hth0 Hth1 HF HfT.
  pose proof u_pos as Hu. pose proof u_lt as Hu2.
  assert (Hth1' : th2 <= 1 / 1000) by (assert (3 / 10 ^ 13 <= 1 / 1000) by interval; lra).
  pose proof (rel_mul w wT F fT u th2 (Rlt_le _ _ Hu) Hth0 Hw Hf) as Hg0.
  pose proof (rel_lo w wT u ltac:(lra) Hw) as Hwl.
  assert (HwT : 9 / 10 * (1 / 1000) <= wT).
  { assert (u * (1 / 1000) <= 1 / 10 * (1 / 1000)) by (assert (u <= 1 / 10) by lra; apply Rmult_le_compat_r; lra). nra. }
  assert (Hgn : nrm (wT * fT)).
  { apply nrm_pos.
    assert (Hm : 9 / 10 * (1 / 1000) * (1 / 10 ^ 50) <= wT * fT) by (apply Rmult_le_compat; [lra | interval | exact HwT | exact HfT]).
    assert (1 / 10 ^ 100 <= 9 / 10 * (1 / 1000) * (1 / 10 ^ 50)) by interval. lra. }
  assert (Hq0 : u + th2 + u * th2 <= th2 + 1001 / 1000 * u).
  { assert (u * th2 <= u * (1 / 1000)) by (apply Rmult_le_compat_l; lra). lra. }
  pose proof (rel_mono (w * F) (wT * fT) _ (th2 + 1001 / 1000 * u) Hg0 Hq0) as Hg0b.
  pose proof (rel_rnd (w * F) (wT * fT) (th2 + 1001 / 1000 * u) Hgn ltac:(lra) Hg0b) as Hg1.
  pose proof (ch_rnd (th2 + 1001 / 1000 * u) (th2 + 1001 / 1000 * u) ltac:(lra) (Rle_refl _) ltac:(assert (3 / 10 ^ 13 + 1001 / 1000 * (12 / 10 ^ 17) <= 1 / 10 ^ 12) by interval; lra)) as Hq1.
  assert (Hq1' : (th2 + 1001 / 1000 * u) + u + u * (th2 + 1001 / 1000 * u) <= th2 + 2003 / 1000 * u) by lra.
  pose proof (rel_mono (w * F) (rnd (wT * fT)) _ (th2 + 2003 / 1000 * u) Hg1 Hq1') as Hg2.
  set (gT := rnd (wT * fT)) in *.
  set (th3 := th2 + 2003 / 1000 * u) in *.
  assert (Hth3 : 0 <= th3) by (unfold th3; lra).
  assert (Hhw : rel (s / 4) (s / 4) 0) by (unfold rel; replace (s / 4 - s / 4) with 0 by ring; rewrite Rabs_R0; lra).
  pose proof (rel_mul (s / 4) (s / 4) (w * F) gT 0 th3 (Rle_refl 0) Hth3 Hhw Hg2) as Hh0.
  assert (HwF : 1 / 1000 * (1 / 10 ^ 45) <= w * F) by (apply Rmult_le_compat; [interval | interval | exact Hw0 | exact HF]).
  pose proof (rel_lo (w * F) gT th3 ltac:(assert (0 < 1 / 1000 * (1 / 10 ^ 45)) by interval; lra) Hg2) as HgTl.
  assert (Hth3s : th3 <= 1 / 2) by (unfold th3; assert (3 / 10 ^ 13 + 2003 / 1000 * (12 / 10 ^ 17) <= 1 / 2) by interval; lra).
  assert (HgT : 1 / 2 * (1 / 1000 * (1 / 10 ^ 45)) <= gT).
  { assert (1 / 2 * (1 / 1000 * (1 / 10 ^ 45)) <= (1 - th3) * (w * F)).
    { assert (0 <= w * F) by lra. nra. }
    lra. }
  assert (Hh2n : nrm (s / 4 * gT)).
  { apply nrm_pos.
    assert (Hm : 3 / 4000 * (1 / 2 * (1 / 1000 * (1 / 10 ^ 45))) <= s / 4 * gT)
      by (apply Rmult_le_compat; [lra | interval | lra | exact HgT]).
    assert (1 / 10 ^ 100 <= 3 / 4000 * (1 / 2 * (1 / 1000 * (1 / 10 ^ 45)))) by interval. lra. }
  pose proof (rel_rnd (s / 4 * (w * F)) (s / 4 * gT) (0 + th3 + 0 * th3) Hh2n ltac:(lra) Hh0) as Hh1.
  assert (Hth3b : th3 <= 1 / 10 ^ 12) by (unfold th3; assert (3 / 10 ^ 13 + 2003 / 1000 * (12 / 10 ^ 17) <= 1 / 10 ^ 12) by interval; lra).
  pose proof (ch_rnd th3 th3 Hth3 (Rle_refl _) Hth3b) as Hq2.
  assert (Hq3 : (0 + th3 + 0 * th3) + u + u * (0 + th3 + 0 * th3) <= th2 + 3004 / 1000 * u).
  { replace (0 + th3 + 0 * th3) with th3 by ring. unfold th3 in *. lra. }
  exact (rel_mono _ _ _ _ Hh1 Hq3).
Qed.
