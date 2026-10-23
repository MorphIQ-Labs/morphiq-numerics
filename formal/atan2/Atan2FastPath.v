(** atan2's fast path end to end: for positive finite [n <= d] with [n/d >= 2^-901]
    it returns the form's double-word within [2^-62] of the exact angle, normalized,
    and the start [(ph, pl)] within [2^-63 (1 + 2^-40)] of [atan (n/d)]. *)
From Coq Require Import Reals ZArith Lia Lra Psatz List.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Mul IEEE64Eft Grid RoundingCore.
From Interval Require Import Tactic.
Require Import Ln1pLemmas AsinTables AsinKernel AsinSqrtStep AsinSegment AsinPath
  Atan2Tables Atan2Kernel Atan2Ratio Atan2Within Atan2Approx Atan2Fast Atan2Forms.
Open Scope R_scope.

(** [atan] is 1-Lipschitz on the non-negative reals. *)
Lemma atan_lip a b : 0 <= a -> a <= b -> atan b - atan a <= b - a.
Proof.
  intros Ha Hab. destruct (Rle_lt_or_eq_dec a b Hab) as [Hlt | Heq]; [ | subst b; lra].
  destruct (atan_id_diff a b Ha Hlt) as [c [Hc E]].
  assert (Hq : 0 <= c * c / (1 + c * c)) by (apply Rmult_le_pos; [nra | apply Rlt_le, Rinv_0_lt_compat; nra]).
  nra.
Qed.

(** The ratio on the unscaled operands. *)
Lemma ratio_stage n d : finite n -> finite d -> 0 < B n -> B n <= B d -> bpow radix2 (-901) <= B n / B d ->
  exists th tl, atan2_ratio n d = (th, tl) /\ finite th /\ finite tl /\ B th = rndF (B th + B tl) /\
    Rabs (B tl) <= bpow radix2 (-52) * B th /\ Rabs (B tl) <= bpow radix2 (-53) /\ B th <= 1 /\ bpow radix2 (-902) <= B th /\
    Rabs (B th + B tl - B n / B d) <= bpow radix2 (-104) * (B n / B d) /\
    (bpow radix2 (-8) <= B n / B d -> on_grid (-211) (B tl)).
Proof.
  intros Fn Fd Pn Hnd Hq.
  assert (Pd : 0 < B d) by lra.
  destruct (exponent_ok d Fd Pd) as [e [Hed [Hek [He1 He2]]]].
  pose proof (bpow_cancel e) as Hc. pose proof (bpow_gt_0 radix2 (-e)) as Pe.
  assert (Hds : 1 <= B d * bpow radix2 (-e) < 2).
  { split.
    - pose proof (Rmult_le_compat_r (bpow radix2 (-e)) _ _ (bpow_ge_0 radix2 (-e)) He1). lra.
    - assert (bpow radix2 (e + 1) * bpow radix2 (-e) = 2) by (rewrite <- bpow_plus; replace (e + 1 + - e)%Z with 1%Z by ring; reflexivity).
      pose proof (Rmult_lt_compat_r (bpow radix2 (-e)) _ _ Pe He2). lra. }
  assert (Hq1 : B n / B d <= 1).
  { apply Rmult_le_reg_r with (B d); [exact Pd | ]. unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra. lra. }
  assert (Hns : B n * bpow radix2 (-e) = (B n / B d) * (B d * bpow radix2 (-e))) by (field; lra).
  assert (Hb1000 : bpow radix2 (-1000) <= bpow radix2 (-901)) by (apply bpow_le; lia).
  assert (Hnsb : bpow radix2 (-1000) <= B n * bpow radix2 (-e) <= 2).
  { pose proof (bpow_gt_0 radix2 (-1000)) as P1000. pose proof (bpow_gt_0 radix2 (-901)) as P901. destruct Hds as [X1 X2]. rewrite Hns. split; nra. }
  destruct (scale_exact d e Fd ltac:(lra) Hek ltac:(destruct Hds; pose proof (bpow_gt_0 radix2 (-1000)); lra) ltac:(destruct Hds; lra)) as [Fds Vds].
  destruct (scale_exact n e Fn ltac:(lra) Hek (proj1 Hnsb) (proj2 Hnsb)) as [Fns Vns].
  rewrite atan2_ratio_pair. rewrite Hed.
  assert (Hq' : B (atan2_scale n e) / B (atan2_scale d e) = B n / B d).
  { rewrite Vns, Vds. field. split; lra. }
  destruct (ratio_core (atan2_scale n e) (atan2_scale d e) Fns Fds ltac:(rewrite Vds; exact Hds) ltac:(rewrite Hq'; exact Hq) ltac:(rewrite Hq'; exact Hq1))
    as [th [tl [Hr [Fth [Ftl [Dw [Rl [Rl2 [Th1 [Th2 [Er Gr]]]]]]]]]]].
  rewrite Hq' in Er, Gr. exists th, tl. repeat split; assumption.
Qed.

(** [atan x >= x/2] on [[0, 1]]. *)
Lemma atan_half x : 0 < x -> x <= 1 -> x / 2 <= atan x.
Proof.
  intros H0 H1. destruct (atan_id_diff 0 x ltac:(lra) H0) as [c [[Hc1 Hc2] E]]. rewrite atan_0 in E.
  assert (Hq : c * c / (1 + c * c) <= / 2).
  { apply Rmult_le_reg_r with (1 + c * c); [nra | ]. unfold Rdiv. rewrite Rmult_assoc, Rinv_l by nra. nra. }
  assert (Hq0 : 0 <= c * c / (1 + c * c)) by (apply Rmult_le_pos; [nra | apply Rlt_le, Rinv_0_lt_compat; nra]).
  nra.
Qed.

Theorem atan2_fast_ok n d f : finite n -> finite d -> 0 < B n -> B n <= B d -> bpow radix2 (-901) <= B n / B d ->
  exists yh yl ph pl, atan2_fast n d f = ((yh, yl), (ph, pl)) /\ finite yh /\ finite yl /\ finite ph /\ finite pl /\
    B yh = rndF (B yh + B yl) /\ B ph = rndF (B ph + B pl) /\ bpow radix2 (-905) <= B yh /\ B yh <= 4 /\
    Rabs (B yh + B yl - form_value f (atan (B n / B d))) <= bpow radix2 (-62) * form_value f (atan (B n / B d)) /\
    Rabs (B ph + B pl - atan (B n / B d)) <= bpow radix2 (-63) * (1 + bpow radix2 (-39)) * atan (B n / B d) /\
    0 < B ph /\ Rabs (B pl) <= bpow radix2 (-52) * B ph /\ B ph + B pl <= 0.78541.
Proof.
  intros Fn Fd Pn Hnd Hq.
  destruct (ratio_stage n d Fn Fd Pn Hnd Hq) as [th [tl [Hr [Fth [Ftl [Dw [Rl [Rl2 [Th1 [Th2 [Er Gr]]]]]]]]]]].
  set (tt := B n / B d) in *.
  assert (Pd : 0 < B d) by lra.
  assert (Htt1 : tt <= 1).
  { apply Rmult_le_reg_r with (B d); [exact Pd | ]. unfold tt, Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra. lra. }
  pose proof (bpow_gt_0 radix2 (-901)) as P901. assert (Htt0 : 0 < tt) by lra.
  assert (Hth905 : bpow radix2 (-905) <= B th) by (apply Rle_trans with (bpow radix2 (-902)); [apply bpow_le; lia | exact Th2]).
  assert (Hb104 : bpow radix2 (-104) <= / 1000000000000) by (apply Rle_trans with (bpow radix2 (-40)); [apply bpow_le; lia | bpow_num; interval with (i_prec 60)]).
  assert (P52 : bpow radix2 (-52) = / 4503599627370496) by (bpow_num; reflexivity).
  apply Rabs_le_inv in Er as [Er1 Er2].
  set (t := B th + B tl) in *.
  assert (Ht1 : 0.99 * tt <= t) by nra. assert (Ht2 : t <= 1.01 * tt) by nra.
  assert (Hgrid : bpow radix2 (-7) < B th -> on_grid (-211) (B tl)).
  { intros Hgt. apply Gr. rewrite P52 in Rl. apply Rabs_le_inv in Rl as [Rl1 Rl2'].
    assert (bpow radix2 (-8) * 2 = bpow radix2 (-7)) by (replace (-7)%Z with (-8 + 1)%Z by reflexivity; rewrite bpow_plus; change (bpow radix2 1) with 2; ring).
    pose proof (bpow_gt_0 radix2 (-8)). assert (Htdef : t = B th + B tl) by reflexivity. lra. }
  destruct (fast_dw_a th tl Fth Ftl Hth905 Th1 Dw Rl Rl2 Hgrid) as [ph [pl [Hs [Fph [Fpl [Dp Ep]]]]]].
  set (phi := atan tt).
  (* phi against atan t *)
  assert (Hphi_lo : tt / 2 <= phi) by (apply atan_half; assumption).
  assert (Hphi_hi : phi <= PI / 4).
  { rewrite <- atan_1. unfold phi. apply atan_le. exact Htt1. }
  assert (Hlip : Rabs (atan t - phi) <= bpow radix2 (-104) * tt).
  { destruct (Rle_dec tt t) as [Hle | Hgt].
    - pose proof (atan_lip tt t ltac:(lra) Hle) as L. pose proof (atan_le tt t Hle) as M. fold phi in L, M. apply Rabs_le. split; lra.
    - pose proof (atan_lip t tt ltac:(lra) ltac:(lra)) as L. pose proof (atan_le t tt ltac:(lra)) as M. fold phi in L, M. apply Rabs_le. split; lra. }
  change (B th + B tl) with t in Ep.
  apply Rabs_le_inv in Hlip as [Hl1 Hl2]. apply Rabs_le_inv in Ep as [Ep1 Ep2].
  assert (Hatan_t : 0 < atan t) by (apply atan_pos; lra).
  assert (Hphi_pos : 0 < phi) by lra.
  assert (Hsr : Rabs (B ph + B pl - phi) <= bpow radix2 (-63) * (1 + bpow radix2 (-39)) * phi).
  { bpow_num. bpow_num_in Ep1. bpow_num_in Ep2. bpow_num_in Hl1. bpow_num_in Hl2.
    apply Rabs_le. split; nra. }
  assert (Hlo902 : bpow radix2 (-902) <= phi).
  { assert (Hb : bpow radix2 (-901) = 2 * bpow radix2 (-902)) by (replace (-901)%Z with (-902 + 1)%Z by reflexivity; rewrite bpow_plus; change (bpow radix2 1) with 2; ring).
    pose proof (bpow_gt_0 radix2 (-902)). lra. }
  destruct (post_ok th tl f ph pl phi Hs Fph Fpl Dp Hlo902 Hphi_hi Hsr) as [yh [yl [Hpost [Fyh [Fyl [Dy [Ly [Uy Ey]]]]]]]].
  pose proof pi_bounds as [Pi1 Pi2].
  assert (HeF : bpow radix2 (-63) * (1 + bpow radix2 (-39)) <= / 1000000) by (bpow_num; interval with (i_prec 100)).
  assert (Hsr' := Hsr). apply Rabs_le_inv in Hsr' as [Hq1 Hq2].
  assert (Hphat_lo : 0.99 * phi <= B ph + B pl) by nra.
  assert (Hphat_hi : B ph + B pl <= 0.78541) by nra.
  assert (Hb903 : bpow radix2 (-902) = 2 * bpow radix2 (-903)) by (replace (-902)%Z with (-903 + 1)%Z by reflexivity; rewrite bpow_plus; change (bpow radix2 1) with 2; ring).
  pose proof (bpow_gt_0 radix2 (-903)) as P903.
  assert (Hpn : bpow radix2 (-1022) <= Rabs (B ph + B pl)).
  { rewrite Rabs_pos_eq by lra. apply Rle_trans with (bpow radix2 (-903)); [apply bpow_le; lia | lra]. }
  pose proof (dw_low ph pl Hpn Dp) as Hlow.
  assert (Hphpos : 0 < B ph).
  { rewrite Dp. apply Rlt_le_trans with (bpow radix2 (-903)); [apply bpow_gt_0 | apply rndF_bpow_le; [lia | lra]]. }
  rewrite (Rabs_pos_eq (B ph)) in Hlow by lra.
  exists yh, yl, ph, pl. rewrite atan2_fast_split, Hr. cbv iota. rewrite Hpost.
  split; [reflexivity | ]. repeat split; try assumption.
Qed.
