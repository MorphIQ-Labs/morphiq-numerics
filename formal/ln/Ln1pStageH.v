(** ln_1p's stage H (docs/ln.md, section 7), transcribed on binary64 as
    crates/morphiq-numerics/src/ln/stages.rs computes it, and proved: for
    [2^-46 <= |x|], [−1 < x < 2^53], [s + lo] is within
    [Kt·z^2 + K2t·|s| + At] of [ln(1 + x)], the bounds the certificates
    formal/ln/stage_h_gz.g, _gs.g and _ga.g prove ([stage_h_err]); the code's
    [eps] exceeds that, today's accurate path's [2^-123] and the test's own
    roundings ([stage_h_margin]); so when the test passes, its result is
    [RN(ln(1 + x))], and so is the rounding of any real within [2^-123] of
    [ln(1 + x)] relatively ([stage_h_ok]). *)

From Coq Require Import ZArith Reals Lia Lra Psatz List.
From Flocq Require Import Core Mult_error IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Eft Grid Encodings RoundingTest RoundingCore.
From Interval Require Import Tactic.
Require Import Ln1pCheck Ln1pTables Ln1pReduction Ln1pTest Ln1pCertificates Ln1pApprox Ln1pLemmas.
Import ListNotations.

Open Scope R_scope.

(** * Constants, by their encodings *)

Definition st_eh (k : nat) : f64 := b64_of_bits (fst (nth k st_el_bits (0%Z, 0%Z))).
Definition st_el (k : nat) : f64 := b64_of_bits (snd (nth k st_el_bits (0%Z, 0%Z))).
Definition st_hc (k : nat) : f64 := b64_of_bits (nth k st_h_bits 0%Z).
Definition c_half : f64 := b64_of_bits 4602678819172646912.   (* 2^-1 *)
Definition c_kh : f64 := b64_of_bits 4386506037058863104.     (* K_H = 2^-49 *)
Definition c_k2h : f64 := b64_of_bits 4233383649728266240.    (* K2_H = 2^-83 *)
Definition c_ah : f64 := b64_of_bits 4147815256808226816.     (* A_H = 2^-102 *)

Lemma c_half_ok : finite c_half /\ B c_half = bpow radix2 (-1).
Proof. exact (enc_pow2 (-1) ltac:(lia)). Qed.
Lemma c_kh_ok : finite c_kh /\ B c_kh = bpow radix2 (-49).
Proof. exact (enc_pow2 (-49) ltac:(lia)). Qed.
Lemma c_k2h_ok : finite c_k2h /\ B c_k2h = bpow radix2 (-83).
Proof. exact (enc_pow2 (-83) ltac:(lia)). Qed.
Lemma c_ah_ok : finite c_ah /\ B c_ah = bpow radix2 (-102).
Proof. exact (enc_pow2 (-102) ltac:(lia)). Qed.

Lemma st_h3_ok : finite (st_hc 0) /\ B (st_hc 0) = h3.
Proof. exact (coef_ok (nth 0 st_h_bits 0%Z) 6004799503155980 (-54) 1501199875788995 (-52) eq_refl ltac:(lia) eq_refl). Qed.
Lemma st_h4_ok : finite (st_hc 1) /\ B (st_hc 1) = h4.
Proof. exact (coef_ok (nth 1 st_h_bits 0%Z) (-9007199254729289) (-55) (-9007199254729289) (-55) eq_refl ltac:(lia) eq_refl). Qed.
Lemma st_h5_ok : finite (st_hc 2) /\ B (st_hc 2) = h5.
Proof. exact (coef_ok (nth 2 st_h_bits 0%Z) 7205779038103950 (-55) 3602889519051975 (-54) eq_refl ltac:(lia) eq_refl). Qed.
Lemma st_h6_ok : finite (st_hc 3) /\ B (st_hc 3) = h6.
Proof. exact (coef_ok (nth 3 st_h_bits 0%Z) (-6004817910265559) (-55) (-6004817910265559) (-55) eq_refl ltac:(lia) eq_refl). Qed.

(** * The transcription *)

Definition stage_h_parts (x : f64) : f64 * f64 * f64 :=
  let s0 := split_s0 x in
  let l := split_l x in
  let hb := bits_of_b64 s0 in
  let e := rd_e hb in
  let i := rd_i hb in
  let rs := rd_rs hb in
  let z := rd_z s0 in
  let k := Z.to_nat (Z.land (e + 64) 127) in
  let ln1 := fadd (st_eh k) (st_th i) in
  let ln0 := fadd (st_el k) (st_tl i) in
  let lr := fmul l rs in
  let z2 := fmul z z in
  let t0 := fsub (fmul z (st_hc 0)) c_half in
  let t1 := fadd (fmul z (st_hc 2)) (st_hc 1) in
  let a1 := fadd (fmul z2 (st_hc 3)) t1 in
  let p := fadd (fmul z2 a1) t0 in
  let q := fmul z2 p in
  let s := fadd ln1 z in
  let e1 := fsub z (fsub s ln1) in
  let pre := fadd e1 (fadd (fmul lr (fsub c_one z)) ln0) in
  let lo := fadd pre q in
  let eps := fadd (fmul z2 c_kh) (fadd (fmul (b64_abs s) c_k2h) c_ah) in
  (s, lo, eps).

Definition stage_h (x : f64) : option f64 :=
  let '(s, lo, eps) := stage_h_parts x in decide s lo eps.

(** The [E·ln 2] table's entry for [−53 <= E <= 53]. *)
Lemma el_entry E : (-53 <= E <= 53)%Z ->
  let k := Z.to_nat (Z.land (E + 64) 127) in
  finite (st_eh k) /\ finite (st_el k) /\ B (st_eh k) = IZR E * B st_l1 /\
  Rabs (B (st_el k) - IZR E * B st_l0) <= / 2 ^ 53 * Rabs (IZR E * B st_l0).
Proof.
  intros HE k. pose proof (l_check_ok st_bounds st_l1_bits st_l0_bits st_el_bits st_l_check) as L.
  destruct L as [_ [_ [_ [_ [_ [_ L]]]]]].
  assert (Kk : k = Z.to_nat (E + 64)).
  { unfold k. change 127%Z with (Z.ones 7). rewrite Z.land_ones by lia. rewrite Z.mod_small by lia. reflexivity. }
  assert (Kr : INR k - 64 = IZR E) by (rewrite Kk, INR_IZR_INZ, Z2Nat.id by lia; rewrite plus_IZR; simpl; ring).
  destruct (L k ltac:(lia)) as [F1 [F2 [V1 V2]]]. rewrite Kr in V1, V2.
  repeat split; assumption.
Qed.

(** The composition, over reals: from stage H's evaluation in the
    relative-error model, the certificates bound [ln(1 + x) − (s + lo)] by
    [543·2^-59·z^2 + 925·2^-94·|s| + 263·2^-111], and [eps] exceeds that, the
    test's own roundings and [2^-123·|ln(1 + x)|]. *)
Lemma h_compose v N ln1 el tl d0 d1 d2 d3 lrt t4 t3 Pz zr L s e1 ln0 w pre q lo z2 da db E1 eps t6 u :
  v = N + (zr + zr * zr * Pz + zr * zr * t3) + (u + t6) -> u = L / (1 + zr) ->
  IZR (-1) * bpow radix2 (-9) <= zr <= IZR 1 * bpow radix2 (-9) ->
  e1 = ln1 + zr - s -> ln0 = (el + tl) * (1 + d0) -> w = (lrt + ln0) * (1 + d1) ->
  pre = (e1 + w) * (1 + d2) -> q = zr * zr * (Pz + t4) -> lo = (pre + q) * (1 + d3) ->
  bpow radix2 (-62) <= Rabs s -> Rabs s <= 56 ->
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

Theorem stage_h_eval x : finite x -> bpow radix2 (-46) <= Rabs (B x) -> -1 < B x < bpow radix2 53 ->
  let '(s, lo, eps) := stage_h_parts x in
  finite s /\ finite lo /\ finite eps /\ 0 <= B eps /\ Rabs (B s) <= bpow radix2 999 /\ Rabs (B lo) + B eps <= 1 /\
  forall w, Rabs (w - ln (1 + B x)) <= / 2 ^ 123 * Rabs (ln (1 + B x)) ->
    Rabs (w - (B s + B lo)) + bpow radix2 (-53) * (Rabs (B lo) + B eps) <= B eps.
Proof.
  intros Fx Hx [Hx1 Hx2].
  pose proof (split_ok x Fx (conj Hx1 Hx2)) as SP. cbv zeta in SP.
  destruct SP as [Fs0 [Fl [Bs0 [Sum [[S0l S0u] Lb]]]]].
  assert (S0u' : B (split_s0 x) <= bpow radix2 1020) by (apply Rle_trans with (1 := S0u); apply bpow_le; lia).
  pose proof (reduce_ok (split_s0 x) Fs0 (conj S0l S0u')) as RD. cbv zeta in RD.
  unfold stage_h_parts. cbv zeta.
  set (s0 := split_s0 x) in *. set (l := split_l x) in *.
  set (hb := bits_of_b64 s0) in *. set (E := rd_e hb) in *. set (i := rd_i hb) in *.
  set (rs := rd_rs hb) in *. set (z := rd_z s0) in *.
  destruct RD as [Er [Hi [RR [Yr [Yi [Frs [Brs [Fz [Bz [Zg [[zi [Zi [Zz [Zn Zf]]]] [Fth [Ftl [Gth [Ttl [Tth Terr]]]]]]]]]]]]]]]].
  set (R := B (st_r i)) in *. set (y := B s0 * bpow radix2 (- E)) in *.
  pose proof (bpow_gt_0 radix2 (-53)) as Pu.
  assert (U53 : bpow radix2 (-53) = / 9007199254740992) by reflexivity.
  assert (Small : forall v, Rabs v <= 64 -> Rabs v <= bpow radix2 1000).
  { intros v Hv. apply Rle_trans with 64; [exact Hv | change 64 with (bpow radix2 6); apply bpow_le; lia]. }
  (* E <= 53: s0 = 2^E y <= 2^53 with y >= 0.7 *)
  assert (Bs0y : B s0 = y * bpow radix2 E).
  { unfold y. rewrite Rmult_assoc, <- bpow_plus. replace (- E + E)%Z with 0%Z by ring. simpl. ring. }
  assert (E53 : (E <= 53)%Z).
  { apply Z.nlt_ge. intros L. assert (bpow radix2 54 <= bpow radix2 E) by (apply bpow_le; lia).
    assert (bpow radix2 53 * 2 = bpow radix2 54) by (rewrite (Rmult_comm _ 2); change 2 with (bpow radix2 1); rewrite <- bpow_plus; reflexivity).
    pose proof (bpow_gt_0 radix2 53). nra. }
  assert (HE : (-53 <= E <= 53)%Z) by lia.
  (* the tables *)
  destruct (el_entry E HE) as [Feh [Fel [Veh Vel]]].
  set (k := Z.to_nat (Z.land (E + 64) 127)) in *.
  pose proof (l_check_ok st_bounds st_l1_bits st_l0_bits st_el_bits st_l_check) as LO.
  destruct LO as [FL1 [FL0 [GL1 [[L1p L1u] [L0b [Lerr _]]]]]].
  fold st_l1 in FL1, GL1, L1p, L1u, Lerr. fold st_l0 in FL0, L0b, Lerr.
  assert (Db : forall d, dval d = IZR (fst d) * bpow radix2 (snd d)) by reflexivity.
  cbn [st_bounds b_l0_max b_l_err b_tl_max b_th_max b_t_err b_s_min] in L0b, Lerr, Ttl, Tth, Terr, Zf.
  rewrite !Db in L0b, Lerr, Ttl, Tth, Terr, Zf. cbn [fst snd] in L0b, Lerr, Ttl, Tth, Terr, Zf.
  bpow_num_in L0b. bpow_num_in Lerr. bpow_num_in Ttl. bpow_num_in Tth. bpow_num_in Terr. bpow_num_in Zf.
  assert (Ln2 : 0.69314718055 <= ln 2 <= 0.69314718056) by (split; interval with (i_prec 64)).
  assert (L1lo : 0.6931 <= B st_l1) by (apply Rabs_le_inv in Lerr; apply Rabs_le_inv in L0b; lra).
  (* ln1 = E L1 + TH, exactly *)
  assert (GE : on_grid 0 (IZR E)) by (exists E; simpl; ring).
  assert (Gln1 : on_grid (-43) (B (st_eh k) + B (st_th i))).
  { rewrite Veh. apply grid_plus; [ | exact Gth]. replace (-43)%Z with (0 + -43)%Z by reflexivity. apply grid_mult; assumption. }
  assert (EI : Rabs (IZR E) <= 53) by (rewrite <- abs_IZR; apply IZR_le; lia).
  assert (Ab1 : Rabs (B (st_eh k) + B (st_th i)) <= 54).
  { rewrite Veh. apply Rle_trans with (1 := Rabs_triang _ _). rewrite Rabs_mult, (Rabs_pos_eq (B st_l1)) by lra.
    assert (Rabs (IZR E) * B st_l1 <= 53 * 1) by (apply Rmult_le_compat; try lra; apply Rabs_pos). lra. }
  destruct (fadd_s (st_eh k) (st_th i) Feh Fth (Small (B (st_eh k) + B (st_th i)) ltac:(lra))) as [Fln1 Bln1].
  rewrite exact_round in Bln1.
  2: { apply (grid_repr (-43)); [lia | exact Gln1 | ]. apply Rle_lt_trans with 54; [exact Ab1 | change (bpow radix2 (-43 + 53)) with 1024; lra]. }
  rewrite Veh in Bln1.
  set (ln1 := fadd (st_eh k) (st_th i)) in *.
  (* ln0 = (el + tl)(1 + d0) *)
  destruct (rnd_sum_rel (B (st_el k)) (B (st_tl i)) (B_fmt _) (B_fmt _)) as [d0 [Hd0 Ed0]].
  assert (Abel : Rabs (B (st_el k)) <= / 2 ^ 37).
  { apply Rabs_le_inv in Vel as ?. assert (Rabs (IZR E * B st_l0) <= 53 * / 17592186044416)
      by (rewrite Rabs_mult; apply Rmult_le_compat; try apply Rabs_pos; [exact EI | lra]).
    pose proof (Rabs_triang_inv (B (st_el k)) (IZR E * B st_l0)).
    assert (/ 2 ^ 53 * Rabs (IZR E * B st_l0) <= Rabs (IZR E * B st_l0)) by (pose proof (Rabs_pos (IZR E * B st_l0)); assert (0 < / 2 ^ 53 <= 1) by (split; [apply Rinv_0_lt_compat, pow_lt; lra | rewrite <- Rinv_1; apply Rinv_le_contravar; [lra | apply pow_R1_Rle; lra]]); nra).
    assert (2 * 53 * / 17592186044416 <= / 2 ^ 37) by (simpl; lra). lra. }
  destruct (fadd_s (st_el k) (st_tl i) Fel Ftl) as [Fln0 Bln0].
  { apply Small. apply Rle_trans with (1 := Rabs_triang _ _). assert (/ 2 ^ 37 <= 1) by (simpl; lra). lra. }
  rewrite Ed0 in Bln0.
  set (ln0 := fadd (st_el k) (st_tl i)) in *.
  assert (One : fmtF 1) by (apply (fmt_pow 0); lia).
  destruct c_one_ok as [F1 B1].
  (* L = l rs, |L| <= 2^-53 (1 + z) *)
  assert (Prs : 0 < B rs) by (rewrite Brs; apply Rmult_lt_0_compat; [lra | apply bpow_gt_0]).
  assert (Hsr : B s0 * B rs = y * R).
  { rewrite Brs, Bs0y. rewrite Rmult_assoc, (Rmult_comm (bpow radix2 E)), Rmult_assoc, <- bpow_plus.
    replace (- E + E)%Z with 0%Z by ring. simpl. ring. }
  assert (Zb : Rabs (B z) <= / 512) by (apply Rle_trans with zi; [exact Zz | apply Rle_trans with (1 := Zi); simpl; lra]).
  apply Rabs_le_inv in Zb as Zb'.
  set (L := B l * B rs).
  assert (HL : Rabs L <= bpow radix2 (-53) * (1 + / 512)).
  { unfold L. rewrite Rabs_mult, (Rabs_pos_eq (B rs)) by lra.
    apply Rle_trans with (bpow radix2 (-53) * B s0 * B rs); [apply Rmult_le_compat_r; lra | ].
    rewrite Rmult_assoc, Hsr. apply Rmult_le_compat_l; [lra | ]. lra. }
  (* lrt = RN(RN(L) RN(1 - z)) *)
  assert (U9 : / 512 <= 1) by lra.
  destruct (fmul_s l rs Fl Frs) as [Flr Blr]; [apply Small; fold L; lra | ].
  destruct (fsub_s c_one z F1 Fz) as [Fomz Bomz]; [apply Small; rewrite B1; apply Rabs_le; lra | ].
  rewrite B1 in Bomz.
  assert (Ablr : Rabs (B (fmul l rs)) <= 1) by (rewrite Blr; apply rnd_bound; [exact One | fold L; lra]).
  assert (Abomz : Rabs (B (fsub c_one z)) <= 2)
    by (rewrite Bomz; apply rnd_bound; [apply (fmt_pow 1); lia | change (bpow radix2 1) with 2; apply Rabs_le; lra]).
  destruct (fmul_s (fmul l rs) (fsub c_one z) Flr Fomz) as [Flrt Blrt].
  { apply Small. rewrite Rabs_mult. apply Rle_trans with (1 * 2); [apply Rmult_le_compat; try apply Rabs_pos; lra | lra]. }
  rewrite Blr, Bomz in Blrt. fold L in Blrt.
  set (lrt := fmul (fmul l rs) (fsub c_one z)) in *.
  assert (HLr : IZR (-519) * bpow radix2 (-62) <= L <= IZR 519 * bpow radix2 (-62)).
  { apply rng_abs. apply Rle_trans with (1 := HL). bpow_num. lra. }
  assert (Hzr : IZR (-1) * bpow radix2 (-9) <= B z <= IZR 1 * bpow radix2 (-9)) by (bpow_num; lra).
  destruct (stage_h_lr L (B z) HLr Hzr) as [LR1 LR2].
  change (round radix2 (FLT_exp (-1074) 53) Gappa_round_def.rndNE) with (round radix2 (FLT_exp emin prec) (Znearest ne)) in LR1, LR2.
  rewrite <- Blrt in LR1, LR2.
  (* the polynomial: q = h_q z *)
  destruct st_h3_ok as [Fh3 Bh3]. destruct st_h4_ok as [Fh4 Bh4]. destruct st_h5_ok as [Fh5 Bh5].
  destruct st_h6_ok as [Fh6 Bh6]. destruct c_half_ok as [Fhf Bhf].
  assert (Hh : Rabs h3 <= 1 /\ Rabs h4 <= 1 /\ Rabs h5 <= 1 /\ Rabs h6 <= 1).
  { unfold h3, h4, h5, h6. bpow_num. repeat split; apply Rabs_le; lra. }
  destruct Hh as [Ah3 [Ah4 [Ah5 Ah6]]].
  assert (Pr : forall a b, Rabs a <= 1 -> Rabs b <= 1 -> Rabs (a * b) <= 1)
    by (intros a b Ha Hb; rewrite Rabs_mult; apply Rle_trans with (1 * 1); [apply Rmult_le_compat; try apply Rabs_pos; lra | lra]).
  assert (Az : Rabs (B z) <= 1) by lra.
  destruct (fmul_s z z Fz Fz) as [Fz2 Bz2]; [apply Small; apply Rle_trans with 1; [apply Pr; lra | lra] | ].
  assert (Az2 : Rabs (B (fmul z z)) <= 1) by (rewrite Bz2; apply rnd_bound; [exact One | apply Pr; lra]).
  destruct (fmul_s z (st_hc 0) Fz Fh3) as [Fm0 Bm0]; [apply Small; rewrite Bh3; apply Rle_trans with 1; [apply Pr; lra | lra] | ].
  assert (Am0 : Rabs (B (fmul z (st_hc 0))) <= 1) by (rewrite Bm0, Bh3; apply rnd_bound; [exact One | apply Pr; lra]).
  destruct (fsub_s (fmul z (st_hc 0)) c_half Fm0 Fhf) as [Ft0 Bt0].
  { apply Small. rewrite Bhf. change (bpow radix2 (-1)) with (/ 2). apply Rabs_le_inv in Am0. apply Rabs_le. lra. }
  assert (At0 : Rabs (B (fsub (fmul z (st_hc 0)) c_half)) <= 2).
  { rewrite Bt0, Bhf. apply rnd_bound; [apply (fmt_pow 1); lia | ]. change (bpow radix2 1) with 2. change (bpow radix2 (-1)) with (/ 2).
    apply Rabs_le_inv in Am0. apply Rabs_le. lra. }
  destruct (fmul_s z (st_hc 2) Fz Fh5) as [Fm2 Bm2]; [apply Small; rewrite Bh5; apply Rle_trans with 1; [apply Pr; lra | lra] | ].
  assert (Am2 : Rabs (B (fmul z (st_hc 2))) <= / 512).
  { rewrite Bm2, Bh5. apply rnd_bound; [apply (fmt_pow (-9)); lia | ]. change (bpow radix2 (-9)) with (/ 512).
    rewrite Rabs_mult. apply Rle_trans with (/ 512 * 1); [apply Rmult_le_compat; try apply Rabs_pos; lra | lra]. }
  destruct (fadd_s (fmul z (st_hc 2)) (st_hc 1) Fm2 Fh4) as [Ft1 Bt1].
  { apply Small. rewrite Bh4. apply Rle_trans with (1 := Rabs_triang _ _). lra. }
  assert (Ah4' : Rabs h4 <= / 2) by (unfold h4; bpow_num; apply Rabs_le; lra).
  assert (At1 : Rabs (B (fadd (fmul z (st_hc 2)) (st_hc 1))) <= 1).
  { rewrite Bt1, Bh4. apply rnd_bound; [exact One | ]. apply Rle_trans with (1 := Rabs_triang _ _). lra. }
  destruct (fmul_s (fmul z z) (st_hc 3) Fz2 Fh6) as [Fm3 Bm3]; [apply Small; rewrite Bh6; apply Rle_trans with 1; [apply Pr; lra | lra] | ].
  assert (Am3 : Rabs (B (fmul (fmul z z) (st_hc 3))) <= / 512).
  { rewrite Bm3, Bh6. apply rnd_bound; [apply (fmt_pow (-9)); lia | ]. change (bpow radix2 (-9)) with (/ 512).
    rewrite Bz2. assert (Rabs (rndF (B z * B z)) <= / 512).
    { apply rnd_bound; [apply (fmt_pow (-9)); lia | ]. change (bpow radix2 (-9)) with (/ 512). rewrite Rabs_mult.
      apply Rle_trans with (/ 512 * 1); [apply Rmult_le_compat; try apply Rabs_pos; lra | lra]. }
    rewrite Rabs_mult. apply Rle_trans with (/ 512 * 1); [apply Rmult_le_compat; try apply Rabs_pos; lra | lra]. }
  destruct (fadd_s (fmul (fmul z z) (st_hc 3)) (fadd (fmul z (st_hc 2)) (st_hc 1)) Fm3 Ft1) as [Fa1 Ba1].
  { apply Small. apply Rle_trans with (1 := Rabs_triang _ _). lra. }
  set (a1 := fadd (fmul (fmul z z) (st_hc 3)) (fadd (fmul z (st_hc 2)) (st_hc 1))) in *.
  assert (Aa1 : Rabs (B a1) <= 2).
  { rewrite Ba1. apply rnd_bound; [apply (fmt_pow 1); lia | ]. change (bpow radix2 1) with 2.
    apply Rle_trans with (1 := Rabs_triang _ _). lra. }
  assert (Az2' : Rabs (B (fmul z z)) <= / 512).
  { rewrite Bz2. apply rnd_bound; [apply (fmt_pow (-9)); lia | ]. change (bpow radix2 (-9)) with (/ 512). rewrite Rabs_mult.
    apply Rle_trans with (/ 512 * 1); [apply Rmult_le_compat; try apply Rabs_pos; lra | lra]. }
  destruct (fmul_s (fmul z z) a1 Fz2 Fa1) as [Fm4 Bm4].
  { apply Small. rewrite Rabs_mult. apply Rle_trans with (1 * 2); [apply Rmult_le_compat; try apply Rabs_pos; lra | lra]. }
  assert (Am4 : Rabs (B (fmul (fmul z z) a1)) <= 1).
  { rewrite Bm4. apply rnd_bound; [exact One | ]. rewrite Rabs_mult.
    apply Rle_trans with (/ 512 * 2); [apply Rmult_le_compat; try apply Rabs_pos; lra | lra]. }
  set (t0 := fsub (fmul z (st_hc 0)) c_half) in *.
  destruct (fadd_s (fmul (fmul z z) a1) t0 Fm4 Ft0) as [Fp Bp].
  { apply Small. apply Rle_trans with (1 := Rabs_triang _ _). lra. }
  set (p := fadd (fmul (fmul z z) a1) t0) in *.
  assert (Ap : Rabs (B p) <= 4).
  { rewrite Bp. apply rnd_bound; [apply (fmt_pow 2); lia | ]. change (bpow radix2 2) with 4.
    apply Rle_trans with (1 := Rabs_triang _ _). lra. }
  destruct (fmul_s (fmul z z) p Fz2 Fp) as [Fq Bq].
  { apply Small. rewrite Rabs_mult. apply Rle_trans with (1 * 4); [apply Rmult_le_compat; try apply Rabs_pos; lra | lra]. }
  set (q := fmul (fmul z z) p) in *.
  assert (Aq : Rabs (B q) <= 1).
  { rewrite Bq. apply rnd_bound; [exact One | ]. rewrite Rabs_mult.
    apply Rle_trans with (/ 512 * 4); [apply Rmult_le_compat; try apply Rabs_pos; lra | lra]. }
  (* q is the certificate's h_q *)
  assert (Eq : B q = h_q (B z)).
  { rewrite Bq, Bp, Bm4, Ba1, Bt1, Bt0, Bm3, Bm2, Bm0, Bz2, Bh3, Bh4, Bh5, Bh6, Bhf.
    unfold h_q, h_p. cbv zeta.
    change (round radix2 (FLT_exp (-1074) 53) Gappa_round_def.rndNE) with (round radix2 (FLT_exp emin prec) (Znearest ne)).
    rewrite Rmult_1_l. reflexivity. }
  (* s = RN(ln1 + z) and e1, by Fast2Sum *)
  assert (Th1 : Rabs (B (st_th i)) <= 711 / 2048) by lra.
  assert (CaseE : (E = 0)%Z \/ 1 <= Rabs (IZR E)).
  { destruct (Z.eq_dec E 0) as [E0 | E0]; [left; exact E0 | right; rewrite <- abs_IZR; apply IZR_le; lia]. }
  assert (Smin : / 512 <= 1) by lra.
  assert (BigE : 1 <= Rabs (IZR E) -> 3439 / 10000 * Rabs (IZR E) <= Rabs (B ln1 + B z)).
  { intros HE1. rewrite Bln1. pose proof (Rabs_triang_inv (IZR E * B st_l1) (- (B (st_th i) + B z))) as T.
    replace (IZR E * B st_l1 - - (B (st_th i) + B z)) with (IZR E * B st_l1 + B (st_th i) + B z) in T by ring.
    rewrite Rabs_Ropp in T. rewrite Rabs_mult, (Rabs_pos_eq (B st_l1)) in T by lra.
    assert (Rabs (B (st_th i) + B z) <= 711 / 2048 + / 512) by (apply Rle_trans with (1 := Rabs_triang _ _); lra).
    assert (Rabs (IZR E) * B st_l1 >= Rabs (IZR E) * 0.6931) by (apply Rle_ge, Rmult_le_compat_l; [apply Rabs_pos | lra]).
    nra. }
  assert (Pre : B ln1 = 0 \/ Rabs (B z) <= Rabs (B ln1)).
  { destruct CaseE as [E0 | HE1].
    - rewrite E0, Rmult_0_l, Rplus_0_l in Bln1.
      destruct (near_b (Z.of_nat i)) eqn:Nb.
      + left. rewrite Bln1. exact (proj1 (Zn eq_refl)).
      + right. rewrite Bln1. specialize (Zf eq_refl). lra.
    - right. pose proof (BigE HE1) as BE. pose proof (Rabs_triang_inv (B ln1 + B z) (B z)) as T.
      replace (B ln1 + B z - B z) with (B ln1) in T by ring. nra. }
  pose proof (fast_two_sum_ieee ln1 z Fln1 Fz
               ltac:(apply Rle_trans with 64; [rewrite Bln1, <- Veh; lra | change 64 with (bpow radix2 6); apply bpow_le; lia])
               ltac:(apply Rle_trans with 1; [lra | change 1 with (bpow radix2 0); apply bpow_le; lia])
               ltac:(destruct Pre as [P | P]; [left; exact P | right; left; exact P])) as FT.
  unfold fast_two_sum64 in FT. cbv beta iota zeta in FT. destruct FT as [Fs [Fe1 [Bs Se1]]].
  set (s := fadd ln1 z) in *. set (e1 := fsub z (fsub s ln1)) in *.
  (* |s| from below, and the ratios tau = T1/s and kap = ln0/s *)
  set (T1 := IZR E * ln 2 - ln R - B ln1 - (B (st_el k) + B (st_tl i))).
  assert (Rp : 0 < R) by lra.
  assert (El0 : (E = 0)%Z -> B (st_el k) = 0).
  { intros E0. rewrite E0 in Vel. rewrite Rmult_0_l, Rminus_0_r, Rabs_R0, Rmult_0_r in Vel.
    apply Rabs_le_inv in Vel. lra. }
  assert (Sfmt : forall c, fmtF c -> c <= Rabs (B ln1 + B z) -> c <= Rabs (B s)).
  { intros c Fc Hc. rewrite Bs. apply abs_round_ge_generic; [exact _ | exact _ | exact Fc | exact Hc]. }
  pose proof (rnd_sum_err (B ln1) (B z) (B_fmt _) (B_fmt _)) as Rs. rewrite <- Bs in Rs.
  assert (Ttl' : Rabs (B (st_tl i)) <= / 17592186044416) by lra.
  assert (Terr' : Rabs (B (st_th i) + B (st_tl i) + ln R) <= / 158456325028528675187087900672) by lra.
  assert (Lerr' : Rabs (B st_l1 + B st_l0 - ln 2) <= / 2535301200456458802993406410752) by lra.
  assert (L0b' : Rabs (B st_l0) <= / 17592186044416) by lra.
  assert (Su : bpow radix2 (-62) <= Rabs (B s) /\
               Rabs T1 <= IZR 183 * bpow radix2 (-94) * Rabs (B s) /\
               Rabs (B ln0) <= IZR 183 * bpow radix2 (-41) * Rabs (B s)).
  { destruct CaseE as [E0 | HE1].
    - assert (Ln1t : B ln1 = B (st_th i)) by (rewrite Bln1, E0, Rmult_0_l, Rplus_0_l; reflexivity).
      destruct (near_b (Z.of_nat i)) eqn:Nb.
      + destruct (Zn eq_refl) as [Th0 [Tl0 R1]].
        assert (Ln10 : B ln1 = 0) by (rewrite Ln1t; exact Th0).
        assert (Sz : B s = B z) by (rewrite Bs, Ln10, Rplus_0_l; apply exact_round, B_fmt).
        assert (Nz : B z <> 0).
        { intros Z0. assert (Ys : B s0 = 1).
          { rewrite Bs0y, E0. change (bpow radix2 0) with 1. rewrite Rmult_1_r. rewrite Bz in Z0. fold R in R1. rewrite R1 in Z0. lra. }
          pose proof (rnd_sum_err 1 (B x) One (B_fmt x)) as RE. rewrite <- Bs0, Ys in RE.
          replace (1 - (1 + B x)) with (- B x) in RE by ring. rewrite Rabs_Ropp in RE.
          assert (Rabs (1 + B x) <= 1 + Rabs (B x)) by (apply Rle_trans with (1 := Rabs_triang _ _); rewrite Rabs_R1; lra).
          bpow_num_in Hx. bpow_num_in RE. lra. }
        destruct Zg as [Z0 | Zg]; [contradiction | ].
        assert (T10 : T1 = 0).
        { unfold T1. rewrite E0, El0 by exact E0. rewrite Ln10, Tl0. fold R in R1. rewrite R1, ln_1, Rmult_0_l. ring. }
        assert (Ln00 : B ln0 = 0) by (rewrite Bln0, El0, Tl0 by exact E0; ring).
        rewrite Sz, T10, Ln00, Rabs_R0. split; [exact Zg | ].
        pose proof (Rabs_pos (B z)). pose proof (bpow_ge_0 radix2 (-94)). pose proof (bpow_ge_0 radix2 (-41)).
        split; apply Rmult_le_pos; try lra; apply Rmult_le_pos; try lra; apply IZR_le; lia.
      + specialize (Zf eq_refl).
        assert (Sm : IZR 181 * bpow radix2 (-18) <= Rabs (B s)).
        { apply Sfmt.
          - apply generic_format_FLT. exists (Float radix2 181 (-18)); [reflexivity | simpl; lia | simpl; unfold emin; lia].
          - rewrite Ln1t. pose proof (Rabs_triang_inv (B (st_th i)) (- B z)) as T.
            replace (B (st_th i) - - B z) with (B (st_th i) + B z) in T by ring. rewrite Rabs_Ropp in T.
            bpow_num. lra. }
        assert (T1v : T1 = - (B (st_th i) + B (st_tl i) + ln R)) by (unfold T1; rewrite E0, El0, Ln1t by exact E0; rewrite Rmult_0_l; ring).
        split; [apply Rle_trans with (2 := Sm); bpow_num; lra | ].
        split.
        * rewrite T1v, Rabs_Ropp. apply Rle_trans with (/ 158456325028528675187087900672); [exact Terr' | ].
          apply Rle_trans with (IZR 183 * bpow radix2 (-94) * (IZR 181 * bpow radix2 (-18)));
            [bpow_num; lra | apply Rmult_le_compat_l; [bpow_num; lra | exact Sm]].
        * rewrite Bln0, El0 by exact E0. rewrite Rplus_0_l, Rabs_mult.
          apply Rle_trans with (/ 17592186044416 * (1 + / 9007199254740992)).
          { apply Rmult_le_compat; try apply Rabs_pos; [exact Ttl' | ]. apply Rle_trans with (1 := Rabs_triang _ _).
            rewrite Rabs_R1, <- U53. lra. }
          apply Rle_trans with (IZR 183 * bpow radix2 (-41) * (IZR 181 * bpow radix2 (-18)));
            [bpow_num; lra | apply Rmult_le_compat_l; [bpow_num; lra | exact Sm]].
    - pose proof (BigE HE1) as BE.
      assert (Ss : (1 - / 9007199254740992) * (3439 / 10000 * Rabs (IZR E)) <= Rabs (B s)).
      { pose proof (Rabs_triang_inv (B ln1 + B z) (B s)) as T. rewrite Rabs_minus_sym in Rs.
        rewrite U53 in Rs. assert (/ 9007199254740992 * Rabs (B ln1 + B z) <= Rabs (B ln1 + B z)) by (pose proof (Rabs_pos (B ln1 + B z)); lra).
        lra. }
      assert (T1v : T1 = IZR E * (ln 2 - B st_l1 - B st_l0) + (IZR E * B st_l0 - B (st_el k)) - (B (st_th i) + B (st_tl i) + ln R))
        by (unfold T1; rewrite Bln1; ring).
      assert (EA : 1 <= Rabs (IZR E) <= 53) by lra.
      assert (Vel' : Rabs (B (st_el k) - IZR E * B st_l0) <= / 9007199254740992 * Rabs (IZR E * B st_l0))
        by (replace (/ 9007199254740992) with (/ 2 ^ 53) by (rewrite <- U53; symmetry; exact (bpow_m 53)); exact Vel).
      split.
      { apply Rle_trans with (2 := Ss). bpow_num. lra. }
      split.
      + rewrite T1v. apply Rle_trans with (Rabs (IZR E) * / 2535301200456458802993406410752 + / 9007199254740992 * (Rabs (IZR E) * / 17592186044416) + / 158456325028528675187087900672).
        { apply Rle_trans with (1 := Rabs_triang _ _). rewrite Rabs_Ropp.
          apply Rplus_le_compat; [ | exact Terr'].
          apply Rle_trans with (1 := Rabs_triang _ _). apply Rplus_le_compat.
          - rewrite Rabs_mult. apply Rmult_le_compat_l; [apply Rabs_pos | ].
            replace (Rabs (ln 2 - B st_l1 - B st_l0)) with (Rabs (B st_l1 + B st_l0 - ln 2))
              by (rewrite <- Rabs_Ropp; f_equal; ring). exact Lerr'.
          - rewrite Rabs_minus_sym. apply Rle_trans with (1 := Vel'). rewrite Rabs_mult.
            apply Rmult_le_compat_l; [simpl; lra | apply Rmult_le_compat_l; [apply Rabs_pos | exact L0b']]. }
        apply Rle_trans with (IZR 183 * bpow radix2 (-94) * ((1 - / 9007199254740992) * (3439 / 10000 * Rabs (IZR E)))).
        { bpow_num. lra. }
        apply Rmult_le_compat_l; [bpow_num; lra | exact Ss].
      + rewrite Bln0, Rabs_mult.
        assert (Ael : Rabs (B (st_el k)) <= Rabs (IZR E) * / 17592186044416 * (1 + / 9007199254740992)).
        { pose proof (Rabs_triang_inv (B (st_el k)) (IZR E * B st_l0)) as T.
          assert (Rabs (IZR E * B st_l0) <= Rabs (IZR E) * / 17592186044416) by (rewrite Rabs_mult; apply Rmult_le_compat_l; [apply Rabs_pos | exact L0b']).
          pose proof (Rabs_pos (IZR E * B st_l0)). pose proof (Rabs_triang_inv (B (st_el k)) (IZR E * B st_l0)). lra. }
        apply Rle_trans with ((Rabs (IZR E) * / 17592186044416 * (1 + / 9007199254740992) + / 17592186044416) * (1 + / 9007199254740992)).
        { apply Rmult_le_compat; try apply Rabs_pos.
          - apply Rle_trans with (1 := Rabs_triang _ _). lra.
          - apply Rle_trans with (1 := Rabs_triang _ _). rewrite Rabs_R1, <- U53. lra. }
        apply Rle_trans with (IZR 183 * bpow radix2 (-41) * ((1 - / 9007199254740992) * (3439 / 10000 * Rabs (IZR E)))).
        { bpow_num. lra. }
        apply Rmult_le_compat_l; [bpow_num; lra | exact Ss]. }
  destruct Su as [Slo [HT1 Hln0]].
  set (zr := B z) in *.
  assert (Pslo : 0 < Rabs (B s)) by (pose proof (bpow_gt_0 radix2 (-62)); lra).
  assert (Snz : B s <> 0) by (intros S0; rewrite S0, Rabs_R0 in Pslo; lra).
  assert (Shi : Rabs (B s) <= 56).
  { pose proof (Rabs_triang_inv (B s) (B ln1 + zr)) as T.
    assert (Rabs (B ln1 + zr) <= 55) by (apply Rle_trans with (1 := Rabs_triang _ _); rewrite Bln1, <- Veh; lra).
    rewrite U53 in Rs. lra. }
  (* eta: Fast2Sum's error is at most 2^-53 |s| *)
  assert (He1 : Rabs (B e1) <= bpow radix2 (-53) * Rabs (B s)).
  { pose proof (rnd_err_out (B ln1 + zr)) as R1. rewrite <- Bs in R1.
    specialize (R1 (Rle_trans _ _ _ (bpow_le radix2 (-1022) (-62) ltac:(lia)) Slo)).
    replace (B e1) with (- (B s - (B ln1 + zr))) by lra. rewrite Rabs_Ropp. exact R1. }
  (* w, pre, lo *)
  assert (Hln0' : Rabs (B ln0) <= 1) by (apply Rle_trans with (1 := Hln0); bpow_num; lra).
  assert (Hlrt : Rabs (B lrt) <= IZR 263 * bpow radix2 (-61)) by (apply abs_rng; exact LR2).
  assert (Hlrt' : Rabs (B lrt) <= 1) by (bpow_num_in Hlrt; lra).
  destruct (rnd_sum_rel (B lrt) (B ln0) (B_fmt _) (B_fmt _)) as [d1 [Hd1 Ed1]].
  destruct (fadd_s lrt ln0 Flrt Fln0) as [Fw Bw]; [apply Small, Rle_trans with (1 := Rabs_triang _ _); lra | ].
  rewrite Ed1 in Bw. set (w := fadd lrt ln0) in *.
  assert (Hw : Rabs (B w) <= 4) by (rewrite Bw, Rabs_mult; apply Rle_trans with (2 * 2);
    [apply Rmult_le_compat; try apply Rabs_pos; [apply Rle_trans with (1 := Rabs_triang _ _); lra
     | apply Rle_trans with (1 := Rabs_triang _ _); rewrite Rabs_R1; bpow_num_in Hd1; lra] | lra]).
  assert (He1' : Rabs (B e1) <= 1) by (bpow_num_in He1; lra).
  destruct (rnd_sum_rel (B e1) (B w) (B_fmt _) (B_fmt _)) as [d2 [Hd2 Ed2]].
  destruct (fadd_s e1 w Fe1 Fw) as [Fpre Bpre]; [apply Small, Rle_trans with (1 := Rabs_triang _ _); lra | ].
  rewrite Ed2 in Bpre. set (pre := fadd e1 w) in *.
  assert (Hpre : Rabs (B pre) <= 10) by (rewrite Bpre, Rabs_mult; apply Rle_trans with (5 * 2);
    [apply Rmult_le_compat; try apply Rabs_pos; [apply Rle_trans with (1 := Rabs_triang _ _); lra
     | apply Rle_trans with (1 := Rabs_triang _ _); rewrite Rabs_R1; bpow_num_in Hd2; lra] | lra]).
  destruct (rnd_sum_rel (B pre) (B q) (B_fmt _) (B_fmt _)) as [d3 [Hd3 Ed3]].
  destruct (fadd_s pre q Fpre Fq) as [Flo Blo]; [apply Small, Rle_trans with (1 := Rabs_triang _ _); lra | ].
  rewrite Ed3 in Blo. set (lo := fadd pre q) in *.
  (* eps *)
  destruct c_kh_ok as [Fkh Bkh]. destruct c_k2h_ok as [Fk2 Bk2]. destruct c_ah_ok as [Fah Bah].
  assert (Z2 : B (fmul z z) = 0 \/ bpow radix2 (-124) <= Rabs (B (fmul z z))).
  { rewrite Bz2. destruct Zg as [Z0 | Zg']; [left; fold zr in Z0; rewrite Z0, Rmult_0_l; apply round_0; exact _ | right].
    apply abs_round_ge_generic; [exact _ | exact _ | apply (fmt_pow (-124)); lia | ].
    rewrite Rabs_mult. replace (-124)%Z with (-62 + -62)%Z by reflexivity. rewrite bpow_plus.
    apply Rmult_le_compat; try apply bpow_ge_0; exact Zg'. }
  destruct (fmul_s (fmul z z) c_kh Fz2 Fkh) as [Fe2 Be2]; [apply Small; rewrite Bkh, Rabs_mult, (Rabs_pos_eq (bpow radix2 (-49))) by apply bpow_ge_0; bpow_num; pose proof (Rabs_pos (B (fmul z z))); lra | ].
  rewrite Bkh, (rnd_scale (B (fmul z z)) (-49) (-124) (B_fmt _) Z2 ltac:(lia)) in Be2.
  pose proof (is_finite_Babs 53 1024 unop_nan_pl64 s) as Fas. fold (b64_abs s) in Fas. rewrite Fs in Fas.
  assert (Bas : B (b64_abs s) = Rabs (B s)) by apply B_abs.
  destruct (fmul_s (b64_abs s) c_k2h Fas Fk2) as [Fe3 Be3]; [apply Small; rewrite Bk2, Bas, Rabs_mult, Rabs_Rabsolu, (Rabs_pos_eq (bpow radix2 (-83))) by apply bpow_ge_0; bpow_num; pose proof (Rabs_pos (B s)); lra | ].
  rewrite Bk2, Bas, (rnd_scale (Rabs (B s)) (-83) (-62) ltac:(rewrite <- Bas; apply B_fmt) ltac:(right; rewrite Rabs_Rabsolu; exact Slo) ltac:(lia)) in Be3.
  destruct (rnd_sum_rel (Rabs (B s) * bpow radix2 (-83)) (bpow radix2 (-102)) ltac:(rewrite <- Be3; apply B_fmt) (fmt_pow (-102) ltac:(lia))) as [da [Hda Eda]].
  destruct (fadd_s (fmul (b64_abs s) c_k2h) c_ah Fe3 Fah) as [Fe4 Be4]; [apply Small; rewrite Be3, Bah; bpow_num; apply Rabs_le; pose proof (Rabs_pos (B s)); lra | ].
  rewrite Be3, Bah, Eda in Be4.
  set (E1 := (Rabs (B s) * bpow radix2 (-83) + bpow radix2 (-102)) * (1 + da)) in *.
  destruct (rnd_sum_rel (B (fmul z z) * bpow radix2 (-49)) E1 ltac:(rewrite <- Be2; apply B_fmt) ltac:(rewrite <- Be4; apply B_fmt)) as [db [Hdb Edb]].
  assert (HE1 : 0 <= E1 <= 1).
  { unfold E1. apply Rabs_le_inv in Hda.
    assert (P83 : 0 < bpow radix2 (-83) <= / 1024) by (split; [apply bpow_gt_0 | change (/ 1024) with (bpow radix2 (-10)); apply bpow_le; lia]).
    assert (P102 : 0 < bpow radix2 (-102) <= / 1024) by (split; [apply bpow_gt_0 | change (/ 1024) with (bpow radix2 (-10)); apply bpow_le; lia]).
    assert (Ub : bpow radix2 (-53) <= / 2) by (change (/ 2) with (bpow radix2 (-1)); apply bpow_le; lia).
    pose proof (Rabs_pos (B s)) as Ps.
    assert (B0 : 0 <= Rabs (B s) * bpow radix2 (-83) <= 56 / 1024)
      by (split; [apply Rmult_le_pos; lra | apply Rmult_le_compat; lra]).
    split; [apply Rmult_le_pos; lra | ].
    apply Rle_trans with ((56 / 1024 + / 1024) * 2); [apply Rmult_le_compat; lra | lra]. }
  assert (Hz2K : 0 <= B (fmul z z) * bpow radix2 (-49) <= 1).
  { assert (Z0 : 0 <= B (fmul z z)).
    { rewrite Bz2. apply round_ge_generic; [exact _ | exact _ | apply generic_format_0 | ]. apply Rle_0_sqr. }
    assert (P49 : 0 < bpow radix2 (-49) <= 1) by (split; [apply bpow_gt_0 | change 1 with (bpow radix2 0); apply bpow_le; lia]).
    apply Rabs_le_inv in Az2.
    split; [apply Rmult_le_pos; lra | apply Rle_trans with (1 * 1); [apply Rmult_le_compat; lra | lra]]. }
  destruct (fadd_s (fmul (fmul z z) c_kh) (fadd (fmul (b64_abs s) c_k2h) c_ah) Fe2 Fe4) as [Feps Beps].
  { apply Small. rewrite Be2, Be4. rewrite Rabs_pos_eq; lra. }
  rewrite Be2, Be4, Edb in Beps.
  set (eps := fadd (fmul (fmul z z) c_kh) (fadd (fmul (b64_abs s) c_k2h) c_ah)) in *.
  (* ln(1 + x) = E ln 2 − ln R + ln(1 + z) + ln(1 + u), u = L/(1 + z) *)
  assert (Hzr1 : 0 < 1 + zr) by lra.
  set (u := L / (1 + zr)).
  assert (Hu : Rabs u <= / 2 ^ 52).
  { unfold u, Rdiv. rewrite Rabs_mult, Rabs_Rinv, (Rabs_pos_eq (1 + zr)) by lra.
    apply Rmult_le_reg_r with (1 + zr); [lra | ]. rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra.
    apply Rle_trans with (1 := HL). bpow_num. simpl. lra. }
  assert (Dec : ln (1 + B x) = IZR E * ln 2 - ln R + ln (1 + zr) + ln (1 + u)).
  { assert (Ex : 1 + B x = (1 + zr) * (1 + u) * bpow radix2 E * / R).
    { replace ((1 + zr) * (1 + u)) with (1 + zr + L) by (unfold u; field; lra).
      rewrite <- Sum, Bs0y. unfold L. rewrite Brs. rewrite Bz.
      assert (Bm : bpow radix2 (- E) * bpow radix2 E = 1) by (rewrite <- bpow_plus, Z.add_opp_diag_l; reflexivity).
      replace (B l) with (B l * (bpow radix2 (- E) * bpow radix2 E)) at 1 by (rewrite Bm; ring).
      field. lra. }
    pose proof (bpow_gt_0 radix2 E) as PE.
    assert (Pu1 : 0 < 1 + u) by (apply Rabs_le_inv in Hu; assert (/ 2 ^ 52 < 1) by (simpl; lra); lra).
    rewrite Ex, ln_mult, ln_mult, ln_mult, ln_Rinv, ln_bpow by (try apply Rinv_0_lt_compat; try apply Rmult_lt_0_compat; try apply Rmult_lt_0_compat; lra).
    ring. }
  (* the polynomial's two errors *)
  set (Pz := h_Pz zr).
  assert (QT : exists t4 t3, B q = zr * zr * (Pz + t4) /\ ln (1 + zr) = zr + zr * zr * Pz + zr * zr * t3 /\
             IZR (-577) * bpow radix2 (-61) <= t4 <= IZR 577 * bpow radix2 (-61) /\
             IZR (-37) * bpow radix2 (-56) <= t3 <= IZR 37 * bpow radix2 (-56) /\
             IZR (-513) * bpow radix2 (-10) <= Pz <= IZR (-511) * bpow radix2 (-10)).
  { destruct (Req_dec zr 0) as [Z0 | Nz].
    - exists 0, 0. rewrite Eq. unfold Pz. rewrite Z0. unfold h_q, h_Pz.
      rewrite !Rmult_0_l, Rplus_0_r, ln_1, round_0 by exact _. rewrite Rmult_0_l, round_0 by exact _.
      split; [ring | ]. split; [ring | ]. bpow_num. split; [lra | ]. split; [lra | ].
      replace (IZR 1 * / IZR 2) with (/ 2) by (simpl; field). split; lra.
    - destruct Zg as [Z0 | Zg']; [contradiction | ].
      destruct (stage_h_q zr ltac:(split; [rewrite Rmult_1_l; exact Zg' | rewrite Rmult_1_l; change (bpow radix2 (-9)) with (/ 512); lra])) as [Q1 Q2].
      assert (Z2p : 0 < zr * zr) by (exact (Rsqr_pos_lt zr Nz)).
      exists ((h_q zr - zr * zr * Pz) / (zr * zr)), ((ln (1 + zr) - zr - zr * zr * Pz) / (zr * zr)).
      split; [rewrite Eq; field; exact Nz | ]. split; [field; exact Nz | ].
      split; [exact Q1 | ]. split; [ | exact Q2].
      apply rng_abs. apply ratio_bound; [rewrite Rabs_pos_eq; lra | ].
      rewrite (Rabs_pos_eq (zr * zr)) by lra.
      pose proof (h_approx zr ltac:(simpl; lra)) as HA. fold Pz in HA.
      apply Rle_trans with (1 := HA). apply Rmult_le_compat_r; [lra | ]. bpow_num. simpl. lra. }
  destruct QT as [t4 [t3 [Eq4 [Eq3 [Ht4 [Ht3 HPz]]]]]].
  set (t6 := ln (1 + u) - u).
  assert (Ht6 : IZR (-267) * bpow radix2 (-114) <= t6 <= IZR 267 * bpow radix2 (-114)).
  { apply (rng_abs t6 267). unfold t6. apply Rle_trans with (u * u / (1 - Rabs u)).
    - apply ln1p_linear. apply Rle_trans with (1 := Hu). simpl. lra.
    - assert (Uu : Rabs u <= IZR 519 * bpow radix2 (-62) / (1 - / 512)).
      { unfold u, Rdiv. rewrite Rabs_mult, Rabs_Rinv, (Rabs_pos_eq (1 + zr)) by lra.
        apply Rmult_le_compat; [apply Rabs_pos | apply Rlt_le, Rinv_0_lt_compat; lra | apply abs_rng; exact HLr | ].
        apply Rinv_le_contravar; lra. }
      bpow_num_in Uu. bpow_num. pose proof (Rabs_pos u).
      assert (u * u <= Rabs u * Rabs u) by (rewrite <- Rabs_mult; apply Rle_abs).
      assert (Rabs u * Rabs u <= (519 * / 4611686018427387904 / (1 - / 512)) * (519 * / 4611686018427387904 / (1 - / 512)))
        by (apply Rmult_le_compat; lra).
      assert (A0 : 0 <= u * u) by apply Rle_0_sqr.
      assert (Hu' : Rabs u <= / 4503599627370496) by (apply Rle_trans with (1 := Hu); simpl; lra).
      unfold Rdiv at 1. apply Rle_trans with ((519 * / 4611686018427387904 / (1 - / 512)) * (519 * / 4611686018427387904 / (1 - / 512)) * / (1 - / 4503599627370496)).
      + apply Rmult_le_compat; [exact A0 | apply Rlt_le, Rinv_0_lt_compat; lra | lra | ].
        apply Rinv_le_contravar; lra.
      + lra. }
  assert (Z2r : 0 <= B (fmul z z) /\ Rabs (B (fmul z z) - zr * zr) <= bpow radix2 (-53) * (zr * zr)).
  { rewrite Bz2. split; [apply round_ge_generic; [exact _ | exact _ | apply generic_format_0 | apply Rle_0_sqr] | ].
    destruct Zg as [Z0 | Zg'].
    - fold zr in Z0. rewrite Z0, Rmult_0_l, round_0, Rminus_0_r, Rabs_R0, Rmult_0_r by exact _. lra.
    - fold zr in Zg'.
      assert (Hb : bpow radix2 (-1022) <= Rabs (zr * zr)).
      { rewrite Rabs_mult. apply Rle_trans with (bpow radix2 (-62) * bpow radix2 (-62)).
        - rewrite <- bpow_plus. apply bpow_le. lia.
        - apply Rmult_le_compat; try apply bpow_ge_0; exact Zg'. }
      pose proof (rnd_rel (zr * zr) Hb) as RZ. rewrite (Rabs_pos_eq (zr * zr) (Rle_0_sqr zr)) in RZ. exact RZ. }
  destruct Z2r as [Z2a Z2b].
  destruct (h_compose (ln (1 + B x)) (IZR E * ln 2 - ln R) (B ln1) (B (st_el k)) (B (st_tl i)) d0 d1 d2 d3 (B lrt) t4 t3 Pz zr L
              (B s) (B e1) (B ln0) (B w) (B pre) (B q) (B lo) (B (fmul z z)) da db E1 (B eps) t6 u)
    as [Ep [Lo1 Main]].
  - rewrite Dec, Eq3. unfold t6. ring.
  - reflexivity.
  - exact Hzr.
  - lra.
  - exact Bln0.
  - exact Bw.
  - exact Bpre.
  - exact Eq4.
  - exact Blo.
  - exact Slo.
  - exact Shi.
  - exact HT1.
  - exact Hln0.
  - exact He1.
  - exact Ht4.
  - exact Ht3.
  - exact HLr.
  - exact HPz.
  - exact Ht6.
  - exact LR1.
  - exact LR2.
  - exact Hd0.
  - exact Hd1.
  - exact Hd2.
  - exact Hd3.
  - exact Hda.
  - exact Hdb.
  - exact Z2a.
  - exact Z2b.
  - reflexivity.
  - exact Beps.
  - split; [exact Fs | ]. split; [exact Flo | ]. split; [exact Feps | ]. split; [exact Ep | ].
    split; [apply Rle_trans with 56; [exact Shi | change 56 with (IZR 56); apply Rle_trans with (bpow radix2 6); [bpow_num; lra | apply bpow_le; lia]] | ].
    split; [exact Lo1 | exact Main].
Qed.
(* The kernel, checking [stage_h_ok]'s proof, otherwise unfolds
   [stage_h_parts] first and takes most of an hour; unfolding it last, it takes
   well under a second. A strategy orders conversion's unfolding and never
   changes what conversion accepts. [stage_h_eval]'s proof unfolds the
   definition, so the strategy starts after it. *)
Local Strategy opaque [stage_h_parts].
(** Stage H, end to end: when its test passes, its result is [RN(ln(1 + x))],
    and every real within [2^-123] of [ln(1 + x)] relatively rounds to it. *)
Theorem stage_h_ok x v : finite x -> bpow radix2 (-46) <= Rabs (B x) -> -1 < B x < bpow radix2 53 ->
  stage_h x = Some v ->
  finite v /\ B v = rndF (ln (1 + B x)) /\
  forall w, Rabs (w - ln (1 + B x)) <= / 2 ^ 123 * Rabs (ln (1 + B x)) -> rndF w = B v.
Proof.
  intros Fx Hx Hr Hd. pose proof (stage_h_eval x Fx Hx Hr) as EV. unfold stage_h in Hd.
  destruct (stage_h_parts x) as [[s lo] eps].
  destruct EV as [Fs [Flo [Feps [E0 [Hs [Hl Main]]]]]].
  destruct (decide_ok s lo eps v Fs Flo Feps E0 Hs Hl Hd) as [Fv Dv].
  assert (All : forall w, Rabs (w - ln (1 + B x)) <= / 2 ^ 123 * Rabs (ln (1 + B x)) -> rndF w = B v)
    by (intros w Hw; apply Dv, Main, Hw).
  split; [exact Fv | split; [ | exact All]].
  symmetry. apply All. rewrite Rminus_diag_eq, Rabs_R0 by reflexivity.
  apply Rmult_le_pos; [apply Rlt_le, Rinv_0_lt_compat, pow_lt; lra | apply Rabs_pos].
Qed.
