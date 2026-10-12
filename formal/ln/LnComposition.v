(** Shared logarithm error composition. The upper bound 900 covers both
    the ln_1p H screen and the full exponent range of ln. *)
From Coq Require Import ZArith Reals Lia Lra Psatz List.
From Flocq Require Import Core Mult_error IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Eft Grid Encodings RoundingTest RoundingCore.
From Interval Require Import Tactic.
Require Import Ln1pCheck Ln1pTables Ln1pReduction Ln1pTest Ln1pCertificates Ln1pApprox Ln1pLemmas.
Import ListNotations.

Open Scope R_scope.

Lemma ln_compose v N ln1 el tl d0 d1 d2 d3 lrt t4 t3 Pz zr L s e1 ln0 w pre q lo z2 da db E1 eps t6 u :
  v = N + (zr + zr * zr * Pz + zr * zr * t3) + (u + t6) -> u = L / (1 + zr) ->
  IZR (-1) * bpow radix2 (-9) <= zr <= IZR 1 * bpow radix2 (-9) ->
  e1 = ln1 + zr - s -> ln0 = (el + tl) * (1 + d0) -> w = (lrt + ln0) * (1 + d1) ->
  pre = (e1 + w) * (1 + d2) -> q = zr * zr * (Pz + t4) -> lo = (pre + q) * (1 + d3) ->
  bpow radix2 (-62) <= Rabs s -> Rabs s <= 900 ->
  Rabs (N - ln1 - (el + tl)) <= IZR 183 * bpow radix2 (-94) * Rabs s ->
  Rabs ln0 <= IZR 183 * bpow radix2 (-41) * Rabs s ->
  Rabs e1 <= bpow radix2 (-53) * Rabs s ->
  IZR (-577) * bpow radix2 (-61) <= t4 <= IZR 577 * bpow radix2 (-61) ->
  IZR (-37) * bpow radix2 (-56) <= t3 <= IZR 37 * bpow radix2 (-56) ->
  IZR (-519) * bpow radix2 (-62) <= L <= IZR 519 * bpow radix2 (-62) ->
  IZR (-513) * bpow radix2 (-10) <= Pz <= IZR (-511) * bpow radix2 (-10) ->
  IZR (-267) * bpow radix2 (-114) <= t6 <= IZR 267 * bpow radix2 (-114) ->
  IZR (-1) * bpow radix2 (-104) <= lrt - L * (1 - zr) <= IZR 1 * bpow radix2 (-104) ->
  IZR (-263) * bpow radix2 (-61) <= lrt <= IZR 263 * bpow radix2 (-61) ->
  Rabs d0 <= bpow radix2 (-53) -> Rabs d1 <= bpow radix2 (-53) -> Rabs d2 <= bpow radix2 (-53) ->
  Rabs d3 <= bpow radix2 (-53) -> Rabs da <= bpow radix2 (-53) -> Rabs db <= bpow radix2 (-53) ->
  0 <= z2 -> Rabs (z2 - zr * zr) <= bpow radix2 (-53) * (zr * zr) ->
  E1 = (Rabs s * bpow radix2 (-83) + bpow radix2 (-102)) * (1 + da) ->
  eps = (z2 * bpow radix2 (-49) + E1) * (1 + db) ->
  0 <= eps /\ Rabs lo + eps <= 1 /\
  forall w0, Rabs (w0 - v) <= / 2 ^ 123 * Rabs v -> Rabs (w0 - (s + lo)) + bpow radix2 (-53) * (Rabs lo + eps) <= eps.
Proof.
  intros Hv Hu Hzr He1 Hln0 Hw Hpre Hq Hlo Slo Shi HT1 Hkap Heta Ht4 Ht3 HL HPz Ht6 Ht5 Hlrt Hd0 Hd1 Hd2 Hd3 Hda Hdb Hz2 Hz2r HE1 Heps.
  assert (U : bpow radix2 (-53) = / 9007199254740992) by reflexivity.
  rewrite U in Heta, Hd0, Hd1, Hd2, Hd3, Hda, Hdb, Hz2r.
  assert (Ps : 0 < Rabs s) by (pose proof (bpow_gt_0 radix2 (-62)); lra).
  assert (Sn : s <> 0) by (intros S0; rewrite S0, Rabs_R0 in Ps; lra).
  assert (Zr : Rabs zr <= / 512) by (bpow_num_in Hzr; apply Rabs_le; lra).
  set (tau := (N - ln1 - (el + tl)) / s). set (kap := ln0 / s). set (eta := e1 / s).
  set (t5 := lrt - L * (1 - zr)).
  assert (R53 : forall d, Rabs d <= / 9007199254740992 -> IZR (-1) * bpow radix2 (-53) <= d <= IZR 1 * bpow radix2 (-53)).
  { intros d Hd. apply (rng_abs d 1). rewrite Rmult_1_l, U. exact Hd. }
  pose proof (stage_h_gz t4 t3 L zr d3 Pz Ht4 Ht3 HL Hzr (R53 d3 Hd3) HPz) as G1.
  pose proof (stage_h_gs tau kap eta d0 d1 d2 d3
                (rng_abs tau 183 (-94) (ratio_bound _ _ _ Ps HT1))
                (rng_abs kap 183 (-41) (ratio_bound _ _ _ Ps Hkap))
                (R53 eta (ratio_bound _ _ _ Ps Heta)) (R53 d0 Hd0) (R53 d1 Hd1) (R53 d2 Hd2) (R53 d3 Hd3)) as G2.
  pose proof (stage_h_ga t5 t6 lrt d1 d2 d3 Ht5 Ht6 Hlrt (R53 d1 Hd1) (R53 d2 Hd2) (R53 d3 Hd3)) as G3.
  apply abs_rng in G1. apply abs_rng in G2. apply abs_rng in G3.
  set (Gz := - t4 + t3 + L / (1 + zr) - d3 * (Pz + t4)) in *.
  set (Gs := tau - d0 * kap / (1 + d0) - d1 * kap - d2 * (eta + kap * (1 + d1)) - d3 * (1 + d2) * (eta + kap * (1 + d1))) in *.
  set (GA := - t5 + t6 - d1 * lrt - d2 * lrt * (1 + d1) - d3 * (1 + d2) * lrt * (1 + d1)) in *.
  assert (Id : v - (s + lo) = zr * zr * Gz + s * Gs + GA).
  { assert (D0 : 1 + d0 <> 0) by (apply Rabs_le_inv in Hd0; lra).
    assert (Z1 : 1 + zr <> 0) by (apply Rabs_le_inv in Zr; lra).
    unfold Gz, Gs, GA, tau, kap, eta, t5. rewrite Hv, Hu, Hlo, Hq, Hpre, Hw, He1, Hln0.
    field. repeat split; assumption. }
  (* the error *)
  set (Z := zr * zr). assert (Z0 : 0 <= Z) by apply Rle_0_sqr.
  assert (Err : Rabs (v - (s + lo)) <= Z * (IZR 543 * bpow radix2 (-59)) + Rabs s * (IZR 925 * bpow radix2 (-94)) + IZR 263 * bpow radix2 (-111)).
  { rewrite Id. apply Rle_trans with (1 := Rabs_triang _ _). apply Rplus_le_compat; [ | exact G3].
    apply Rle_trans with (1 := Rabs_triang _ _). rewrite (Rabs_mult (zr * zr) Gz), (Rabs_mult s Gs), (Rabs_pos_eq (zr * zr)) by exact Z0.
    fold Z. apply Rplus_le_compat; [apply Rmult_le_compat_l; [exact Z0 | exact G1] | apply Rmult_le_compat_l; [apply Rabs_pos | exact G2]]. }
  bpow_num_in Err. bpow_num_in Ht4. bpow_num_in HPz. bpow_num_in Hlrt. bpow_num_in Hkap. bpow_num_in Slo.
  (* |lo| *)
  apply Rabs_le_inv in Hd0. apply Rabs_le_inv in Hd1. apply Rabs_le_inv in Hd2. apply Rabs_le_inv in Hd3.
  apply Rabs_le_inv in Hda. apply Rabs_le_inv in Hdb.
  assert (Aq : Rabs q <= Z * (513 / 1024 + 577 / 2305843009213693952)).
  { rewrite Hq, Rabs_mult, (Rabs_pos_eq (zr * zr)) by exact Z0. fold Z. apply Rmult_le_compat_l; [exact Z0 | ].
    apply Rabs_le. lra. }
  assert (Aw : Rabs w <= (263 / 2305843009213693952 + 183 / 2199023255552 * Rabs s) * (1 + / 9007199254740992)).
  { rewrite Hw, Rabs_mult. apply Rmult_le_compat; try apply Rabs_pos.
    - apply Rle_trans with (1 := Rabs_triang _ _). apply Rplus_le_compat; [apply Rabs_le; lra | lra].
    - apply Rabs_le. lra. }
  assert (Apre : Rabs pre <= (/ 9007199254740992 * Rabs s + (263 / 2305843009213693952 + 183 / 2199023255552 * Rabs s) * (1 + / 9007199254740992)) * (1 + / 9007199254740992)).
  { rewrite Hpre, Rabs_mult. apply Rmult_le_compat; try apply Rabs_pos.
    - apply Rle_trans with (1 := Rabs_triang _ _). apply Rplus_le_compat; lra.
    - apply Rabs_le. lra. }
  assert (Alo : Rabs lo <= ((/ 9007199254740992 * Rabs s + (263 / 2305843009213693952 + 183 / 2199023255552 * Rabs s) * (1 + / 9007199254740992)) * (1 + / 9007199254740992) + Z * (513 / 1024 + 577 / 2305843009213693952)) * (1 + / 9007199254740992)).
  { rewrite Hlo, Rabs_mult. apply Rmult_le_compat; try apply Rabs_pos.
    - apply Rle_trans with (1 := Rabs_triang _ _). apply Rplus_le_compat; lra.
    - apply Rabs_le. lra. }
  (* eps *)
  assert (B83 : bpow radix2 (-83) = / 9671406556917033397649408) by reflexivity.
  assert (B102 : bpow radix2 (-102) = / 5070602400912917605986812821504) by reflexivity.
  assert (B49 : bpow radix2 (-49) = / 562949953421312) by reflexivity.
  rewrite B83, B102 in HE1. rewrite B49 in Heps.
  set (S := Rabs s) in *.
  assert (PS : 0 <= S) by apply Rabs_pos.
  assert (Bse : 0 <= S * / 9671406556917033397649408 + / 5070602400912917605986812821504) by (pose proof (Rinv_0_lt_compat 9671406556917033397649408 ltac:(lra)); nra).
  assert (E1lo : (S * / 9671406556917033397649408 + / 5070602400912917605986812821504) * (1 - / 9007199254740992) <= E1)
    by (rewrite HE1; apply Rmult_le_compat_l; lra).
  assert (E1hi : E1 <= (S * / 9671406556917033397649408 + / 5070602400912917605986812821504) * (1 + / 9007199254740992))
    by (rewrite HE1; apply Rmult_le_compat_l; lra).
  apply Rabs_le_inv in Hz2r.
  assert (Bb : 0 <= z2 * / 562949953421312 + E1) by (assert (0 <= z2 * / 562949953421312) by (apply Rmult_le_pos; lra); lra).
  assert (Elo : (z2 * / 562949953421312 + E1) * (1 - / 9007199254740992) <= eps) by (rewrite Heps; apply Rmult_le_compat_l; lra).
  assert (Ehi : eps <= (z2 * / 562949953421312 + E1) * (1 + / 9007199254740992)) by (rewrite Heps; apply Rmult_le_compat_l; lra).
  assert (Zlo : Z * (1 - / 9007199254740992) <= z2) by (fold Z in Hz2r; lra).
  assert (Zhi : z2 <= Z * (1 + / 9007199254740992)) by (fold Z in Hz2r; lra).
  assert (Zs : Z <= / 262144) by (unfold Z; apply Rabs_le_inv in Zr; nra).
  split; [lra | ]. split; [lra | ].
  intros w0 Hw0.
  assert (Av : Rabs v <= S + Rabs lo + Rabs (v - (s + lo))).
  { replace v with (s + lo + (v - (s + lo))) at 1 by ring. apply Rle_trans with (1 := Rabs_triang _ _).
    apply Rplus_le_compat_r. apply Rabs_triang. }
  assert (Aw0 : Rabs (w0 - (s + lo)) <= Rabs (w0 - v) + Rabs (v - (s + lo))).
  { replace (w0 - (s + lo)) with ((w0 - v) + (v - (s + lo))) by ring. apply Rabs_triang. }
  assert (P123 : 0 < / 2 ^ 123 <= / 10633823966279326983230456482242756608) by (split; [apply Rinv_0_lt_compat, pow_lt; lra | simpl; lra]).
  assert (Hw0' : Rabs (w0 - v) <= / 10633823966279326983230456482242756608 * Rabs v) by (pose proof (Rabs_pos v); nra).
  bpow_num. lra.
Qed.
