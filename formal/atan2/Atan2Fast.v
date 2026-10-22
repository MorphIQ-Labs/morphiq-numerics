(** atan2's fast path against [atan]: for a double-word [(th, tl)] in [(0, 1]] the
    series branch and the table branch return a double-word within [2^-63] of
    [atan] of the value, relatively, composing the transcription's evaluation
    theorems ([atan2_series_eval], [atan2_series_tiny], [series_segment_a]) with
    the approximation theorems ([approx_series_a], [Atan2Approx.approx_<kk>]). *)
From Coq Require Import Reals ZArith Lia Lra Psatz List.
From Flocq Require Import Core.
From Binary64 Require Import Binary64Add IEEE64 RoundingCore Grid.
From Interval Require Import Tactic.
Require Import Ln1pLemmas AsinTables AsinKernel AsinSqrtStep AsinSeriesSmall AsinSegment AsinWithin
  Atan2Tables Atan2Kernel Atan2SeriesSmall Atan2Within Atan2Segment Atan2Approx Atan2Segments.
Open Scope R_scope.

(** [|zl| <= 2^-52 zh] for a double-word whose high part is the rounded sum. *)
Lemma low_part_small_a zh zl : bpow radix2 (-905) <= B zh -> B zh = rndF (B zh + B zl) ->
  Rabs (B zl) <= B zh / 2 -> Rabs (B zl) <= / 4503599627370496 * B zh.
Proof.
  intros L Dw Hl.
  set (z := B zh) in *. set (d := B zl) in *.
  assert (Q1 : bpow radix2 (-1022) <= bpow radix2 (-906)) by (apply bpow_le; lia).
  assert (Q2 : bpow radix2 (-906) = bpow radix2 (-905) / 2).
  { replace (-906)%Z with (-905 + -1)%Z by reflexivity. rewrite bpow_plus. change (bpow radix2 (-1)) with (/ 2). field. }
  assert (Hn : bpow radix2 (-1022) <= Rabs (z + d)).
  { apply Rle_trans with (bpow radix2 (-906)); [exact Q1 | ].
    apply Rabs_le_inv in Hl. rewrite Q2.
    apply Rle_trans with (z + d); [ | apply Rle_abs]. lra. }
  pose proof (rnd_rel (z + d) Hn) as R.
  change (RNE (z + d)) with (rndF (z + d)) in R. rewrite <- Dw in R.
  replace (z - (z + d)) with (- d) in R by ring. rewrite Rabs_Ropp in R.
  pose proof bp53 as P53.
  rewrite P53 in R. apply Rabs_le_inv in Hl.
  assert (Habs : Rabs (z + d) <= 3 / 2 * z) by (apply Rabs_le; split; lra).
  pose proof (Rabs_pos d). nra.
Qed.

(** The series branch: [z = zh + zl] with [zh] in [[2^-900, 2^-7]]. *)
Theorem fast_series_a zh zl : finite zh -> finite zl ->
  bpow radix2 (-905) <= B zh -> B zh <= bpow radix2 (-7) ->
  B zh = rndF (B zh + B zl) -> Rabs (B zl) <= B zh / 2 ->
  exists h l, atan2_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    Rabs (B h + B l - atan (B zh + B zl)) <= bpow radix2 (-64) * atan (B zh + B zl).
Proof.
  intros Fh Fl L U Dw Hl.
  pose proof (low_part_small_a zh zl L Dw Hl) as Hd.
  pose proof U as U7.
  pose proof (bpow_gt_0 radix2 (-905)) as P900.
  set (z := B zh) in *. set (d := B zl) in *.
  assert (Hz0 : 0 < z) by lra.
  bpow_num_in U.
  assert (Hd2 : Rabs d <= / 4503599627370496 * z) by exact Hd.
  apply Rabs_le_inv in Hd2 as [Hd1 Hd2].
  assert (Hdz : Rabs d <= z / 2) by exact Hl.
  assert (HAm : 0.99 * z <= atan (z + d)).
  { assert (Hy : 0 < z + d <= 0.0078126) by (split; lra).
    pose proof (atan_ge_cube (z + d) ltac:(lra)) as G.
    assert (Hy2 : (z + d) * (z + d) * (z + d) <= 0.0000611 * (z + d)) by nra.
    lra. }
  assert (HApos : 0 < atan (z + d)) by (apply atan_pos; lra).
  assert (Hd0 : Rabs d <= / 4503599627370496 * z) by (apply Rabs_le; split; lra).
  destruct (Rle_dec (bpow radix2 (-100)) z) as [Big | Small].
  - (* [2^-100, 2^-7] *)
    destruct (atan2_series_eval zh zl Fh Fl Big U7 Dw Hl) as [h [l [Hs [Fh' [Fl' [Nrm [ec [ea [Hec [Hea Eq]]]]]]]]]].
    exists h, l. split; [exact Hs | split; [exact Fh' | split; [exact Fl' | split; [exact Nrm | ]]]].
    set (Tx := z * z * z * aQ (z * z)) in *.
    assert (X1 : bpow radix2 (-100) <= z <= 0.0078126) by (split; lra).
    pose proof (approx_series_a z X1) as HA.
    assert (Zq : 0 <= z <= bpow radix2 (-7)) by (split; [lra | exact U7]).
    destruct (aQ_pos z Zq) as [Q0 Q1].
    assert (Z3 : 0 <= z * z * z) by (apply Rmult_le_pos; [apply Rmult_le_pos | ]; lra).
    assert (Zz : z * z <= 0.00006104) by nra.
    assert (HT : 0 <= Tx <= 0.3334 * (z * z * z)) by (unfold Tx; split; nra).
    pose proof (atan_shift z d Hz0 Hdz) as SH.
    assert (Hsh : (z + Rabs d) * (z + Rabs d) * Rabs d <= 4.0002 / 18014398509481984 * (z * z * z)).
    { pose proof (Rabs_pos d) as Ra0.
      assert (Ha : Rabs d <= z * / 4503599627370496) by lra.
      assert (Hsq : (z + Rabs d) * (z + Rabs d) <= 1.0000001 * (z * z)) by nra.
      assert (Hnn : 0 <= (z + Rabs d) * (z + Rabs d)) by nra.
      pose proof (Rmult_le_compat _ _ _ _ Hnn Ra0 Hsq Ha) as M.
      nra. }
    assert (HE : Rabs (atan (z + d) - (z + d - Tx)) <= 4.35 / 18014398509481984 * (z * z * z)).
    { replace (atan (z + d) - (z + d - Tx)) with ((atan (z + d) - atan z - d) + (atan z - (z - Tx))) by ring.
      apply Rle_trans with (Rabs (atan (z + d) - atan z - d) + Rabs (atan z - (z - Tx))); [apply Rabs_triang | ].
      unfold Tx. nra. }
    assert (Hb : Rabs (- (Tx * ec)) <= 2.668 / 18014398509481984 * (z * z * z)).
    { rewrite Rabs_Ropp, Rabs_mult, (Rabs_pos_eq Tx) by lra. pose proof (Rabs_pos ec).
      assert (Hec8 : Rabs ec <= 8 / 18014398509481984) by (apply Rle_trans with (/ 2 ^ 51); [exact Hec | interval with (i_prec 100)]).
      pose proof (Rmult_le_compat Tx (0.3334 * (z * z * z)) (Rabs ec) (8 / 18014398509481984) (proj1 HT) (Rabs_pos ec) (proj2 HT) Hec8) as M.
      lra. }
    assert (HE104 : / 2 ^ 104 <= / 1000000000000000000000000000000) by (interval with (i_prec 120)).
    assert (Hnum : (4.35 / 18014398509481984 * (z * z * z) + 2.668 / 18014398509481984 * (z * z * z)) * (1 + / 2 ^ 104)
                   + / 2 ^ 104 * (0.99 * z) <= bpow radix2 (-64) * (0.99 * z)).
    { bpow_num.
      assert (H1 : (4.35 / 18014398509481984 * (z * z * z) + 2.668 / 18014398509481984 * (z * z * z))
                   <= 7.02 / 18014398509481984 * 0.00006104 * z) by nra.
      nra. }
    pose proof (fast_compose (atan (z + d)) (z + d - Tx) (- (Tx * ec)) ea
      (4.35 / 18014398509481984 * (z * z * z)) (2.668 / 18014398509481984 * (z * z * z)) (/ 2 ^ 104)
      (0.99 * z) (bpow radix2 (-64)) HE Hb Hea HAm ltac:(lra) ltac:(apply Rlt_le; apply Rinv_0_lt_compat; apply pow_lt; lra) Hnum) as FC.
    assert (Eq' : B h + B l = (z + d - Tx + - (Tx * ec)) * (1 + ea)).
    { cbv zeta in Eq. rewrite Eq. unfold Tx, z, d. ring. }
    rewrite Eq'. exact FC.
  - (* [2^-900, 2^-100) *)
    assert (Sm : z <= bpow radix2 (-100)) by lra.
    destruct (atan2_series_tiny zh zl Fh Fl L Sm Dw Hl) as [h [l [Hs [Fh' [Fl' [Nrm [tau [ea [Htau [Hea Eq]]]]]]]]]].
    exists h, l. split; [exact Hs | split; [exact Fh' | split; [exact Fl' | split; [exact Nrm | ]]]].
    assert (B100 : bpow radix2 (-100) <= / 1000000000000000000000000000000) by (bpow_num; interval with (i_prec 100)).
    assert (B170 : bpow radix2 (-165) <= / 1000000000000000000000000000000000000000000000000) by (bpow_num; interval with (i_prec 120)).
    assert (B199 : bpow radix2 (-199) <= / 1000000000000000000000000000000000000000000000000) by (bpow_num; interval with (i_prec 120)).
    assert (Hzz : z * z <= bpow radix2 (-199)).
    { replace (-199)%Z with (-100 + -99)%Z by reflexivity. rewrite bpow_plus.
      assert (bpow radix2 (-99) = 2 * bpow radix2 (-100)).
      { replace (-99)%Z with (-100 + 1)%Z by reflexivity. rewrite bpow_plus. change (bpow radix2 1) with 2. ring. }
      pose proof (bpow_ge_0 radix2 (-100)). nra. }
    assert (HE : Rabs (atan (z + d) - (z + d)) <= z * bpow radix2 (-198)).
    { pose proof (atan_ge_cube (z + d) ltac:(lra)) as G1. pose proof (atan_le_id (z + d) ltac:(lra)) as G2.
      apply Rabs_le. split.
      - assert ((z + d) * (z + d) * (z + d) <= z * bpow radix2 (-198)).
        { replace (-198)%Z with (-199 + 1)%Z by reflexivity. rewrite bpow_plus. change (bpow radix2 1) with 2.
          pose proof (bpow_ge_0 radix2 (-199)). assert ((z + d) * (z + d) <= 1.0001 * (z * z)) by nra. nra. }
        nra.
      - pose proof (bpow_ge_0 radix2 (-198)). nra. }
    assert (Hb : Rabs tau <= z * bpow radix2 (-165)) by exact Htau.
    assert (HE104 : / 2 ^ 104 <= / 1000000000000000000000000000000) by (interval with (i_prec 120)).
    assert (Hnum : (z * bpow radix2 (-198) + z * bpow radix2 (-165)) * (1 + / 2 ^ 104) + / 2 ^ 104 * (0.99 * z)
                   <= bpow radix2 (-64) * (0.99 * z)).
    { bpow_num. assert (bpow radix2 (-198) <= bpow radix2 (-165)) by (apply bpow_le; lia). 
      assert (bpow radix2 (-64) >= / 100000000000000000000) by (bpow_num; interval with (i_prec 100)).
      bpow_num_in H. nra. }
    pose proof (fast_compose (atan (z + d)) (z + d) tau ea (z * bpow radix2 (-198)) (z * bpow radix2 (-165)) (/ 2 ^ 104)
      (0.99 * z) (bpow radix2 (-64)) HE Hb Hea HAm ltac:(lra) ltac:(apply Rlt_le; apply Rinv_0_lt_compat; apply pow_lt; lra) Hnum) as FC.
    rewrite Eq. exact FC.
Qed.

(** A double-word whose high word is [zh] in [[2^-900, 1]]: the series below
    [2^-7], the table above, within [2^-63] of [atan]. *)
Theorem fast_dw_a zh zl : finite zh -> finite zl ->
  bpow radix2 (-905) <= B zh -> B zh <= 1 -> B zh = rndF (B zh + B zl) ->
  Rabs (B zl) <= bpow radix2 (-53) * B zh -> on_grid (-211) (B zl) ->
  exists h l, atan2_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    Rabs (B h + B l - atan (B zh + B zl)) <= bpow radix2 (-63) * atan (B zh + B zl).
Proof.
  intros Fh Fl L U Dw Hl Hg.
  pose proof (bpow_gt_0 radix2 (-905)) as P900.
  assert (P53 : bpow radix2 (-53) <= / 2) by (bpow_num; interval with (i_prec 60)).
  assert (Hlh : Rabs (B zl) <= B zh / 2).
  { apply Rle_trans with (1 := Hl). nra. }
  assert (Hlabs : Rabs (B zl) <= bpow radix2 (-53)).
  { apply Rle_trans with (1 := Hl). pose proof (bpow_ge_0 radix2 (-53)). nra. }
  assert (Hsum : 0 < B zh + B zl).
  { apply Rabs_le_inv in Hlh as [A1 A2]. lra. }
  destruct (Rle_dec (B zh) (bpow radix2 (-7))) as [Hs | Ht].
  - destruct (fast_series_a zh zl Fh Fl L Hs Dw Hlh) as [h [l [Hr [Fh' [Fl' [Nrm Err]]]]]].
    exists h, l. repeat split; try assumption.
    assert (An : 0 < atan (B zh + B zl)) by (apply atan_pos; exact Hsum).
    apply Rle_trans with (1 := Err). apply Rmult_le_compat_r; [lra | apply bpow_le; lia].
  - assert (Hbig : / 128 < B zh).
    { assert (bpow radix2 (-7) = / 128) by (bpow_num; reflexivity). lra. }
    set (k := Znearest ne (B zh * 64)).
    pose proof (Znearest_half ne (B zh * 64)) as Hh. fold k in Hh. apply Rabs_le_inv in Hh as [Hh1 Hh2].
    assert (Hk1 : (1 <= k)%Z).
    { assert (0 < IZR k) by lra. apply lt_0_IZR in H. lia. }
    assert (Hk2 : (k <= 64)%Z).
    { assert (IZR k < 65) by lra. assert (IZR k < IZR 65) by (change (IZR 65) with 65; lra). apply lt_IZR in H0. lia. }
    destruct (fast_table k zh zl ltac:(lia) Fh Fl ltac:(lra) U eq_refl Hlabs Hg) as [h [l [Hr [Fh' [Fl' [Nrm Err]]]]]].
    exists h, l. repeat split; try assumption.
    replace (B zh + B zl) with (IZR k / 64 + (B zh - IZR k / 64 + B zl)) by ring. exact Err.
Qed.
