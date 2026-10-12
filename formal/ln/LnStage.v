(** Natural logarithm reciprocal stage, from the full-domain normalizer to the rounding decision. *)
From Coq Require Import ZArith Reals Lia Lra Psatz List.
From Flocq Require Import Core Mult_error IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Eft Grid Encodings RoundingTest RoundingCore.
From Interval Require Import Tactic.
Require Import Ln1pCheck Ln1pTables Ln1pReduction Ln1pTest Ln1pCertificates Ln1pApprox Ln1pLemmas.
Import ListNotations.

Open Scope R_scope.

Require Import Ln1pStageH Ln1pStageB.
Require LnReduction LnAccurate.
From Q Require Q128.

Require Import LnStageEvaluation.

Local Strategy opaque [ln_parts].

Definition ln_stage (x : f64) : option f64 :=
  let '(e, _, h, _) := LnReduction.reduce x in
  let E := (e + rd_e (bits_of_b64 h))%Z in
  let '(s, lo, eps) := ln_parts E h in decide s lo eps.

(** All finite positive arguments, including subnormals. No bounds on a
    reduction or rounding error are assumed by this theorem. *)
Theorem ln_stage_ok x v : finite x -> 0 < B x -> B x <> 1 ->
  ln_stage x = Some v ->
  finite v /\ B v = rndF (ln (B x)) /\
  forall w, Rabs (w - ln (B x)) <= / 2 ^ 123 * Rabs (ln (B x)) -> rndF w = B v.
Proof.
  intros Fx Px Nx.
  pose proof (LnReduction.reduce_ok x Fx Px) as RD.
  unfold ln_stage. revert RD.
  generalize (LnReduction.reduce x). intros [[[e i] h] r] RD.
  destruct RD as [Hi [_ [Fh [Iy [_ [Ex Er]]]]]].
  destruct (LnReduction.ln_range i Hi) as [Yl [Yu _]].
  assert (Hr : bpow radix2 (-53) <= B h <= bpow radix2 1020).
  { split; [bpow_num; lra | apply Rle_trans with 2; [lra | change 2 with (bpow radix2 1); apply bpow_le; lia]]. }
  pose proof (Ln1pReduction.reduce_ok h Fh Hr) as R1. cbv zeta in R1.
  destruct R1 as [_ [_ [_ [Y _]]]].
  set (re := rd_e (bits_of_b64 h)) in *.
  set (y := B h * bpow radix2 (- re)) in *.
  assert (Hy : B h = y * bpow radix2 re).
  { unfold y. rewrite Rmult_assoc, <- bpow_plus, Z.add_opp_diag_l. simpl. ring. }
  assert (Re : (-1 <= re <= 1)%Z).
  { split.
    - apply Z.nlt_ge. intros Hre.
      assert (bpow radix2 re <= / 4) by (change (/ 4) with (bpow radix2 (-2)); apply bpow_le; lia).
      pose proof (bpow_gt_0 radix2 re). nra.
    - apply Z.nlt_ge. intros Hre.
      assert (4 <= bpow radix2 re) by (change 4 with (bpow radix2 2); apply bpow_le; lia). nra. }
  set (E := (e + re)%Z).
  assert (HE : (-1100 <= E <= 1100)%Z) by (unfold E; lia).
  assert (XY : B x = bpow radix2 E * y).
  { rewrite Ex, Hy. unfold E. rewrite bpow_plus. ring. }
  assert (Ne : E = 0%Z -> y <> 1).
  { intros E0 Y1. apply Nx. rewrite XY, E0, Y1. change (1 * 1 = 1). ring. }
  assert (Lv : ln (B x) = IZR E * ln 2 + ln y).
  { rewrite XY, ln_mult, ln_bpow; [reflexivity | apply bpow_gt_0 | lra]. }
  pose proof (ln_eval E h Fh Hr HE Ne) as EV. fold re y in EV.
  rewrite <- Lv in EV. revert EV.
  generalize (ln_parts E h). intros [[s lo] eps] EV Hd.
  destruct EV as [Fs [Flo [Feps [E0 [Hs [Hl Main]]]]]].
  destruct (decide_ok s lo eps v Fs Flo Feps E0 Hs Hl Hd) as [Fv Dv].
  assert (All : forall w, Rabs (w - ln (B x)) <= / 2 ^ 123 * Rabs (ln (B x)) -> rndF w = B v)
    by (intros w Hw; apply Dv, Main, Hw).
  split; [exact Fv | split; [ | exact All]].
  symmetry. apply All. rewrite Rminus_diag_eq, Rabs_R0 by reflexivity.
  apply Rmult_le_pos; [apply Rlt_le, Rinv_0_lt_compat, pow_lt; lra | apply Rabs_pos].
Qed.

(** Agreement with the integer accurate path does not need a worst-case
    assumption: the interval also encloses its proved error. *)
Theorem ln_stage_accurate_value x v : finite x -> 0 < B x -> B x <> 1 ->
  ln_stage x = Some v -> B v = B (Q128.to_f64 (LnAccurate.ln_acc x)).
Proof.
  intros Fx Px Nx Hd.
  destruct (ln_stage_ok x v Fx Px Nx Hd) as [_ [_ All]].
  destruct (LnAccurate.ln_acc_ok x Fx Px Nx) as [_ [Err Rnd]].
  rewrite Rnd. symmetry. apply All, Err.
Qed.
