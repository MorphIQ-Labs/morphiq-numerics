(** asin's fast path against [asin]: for a double-word [(zh, zl)] the series
    branch and the table branch return a double-word within [2^-62] of [asin]
    of the value, relatively, composing the transcription's evaluation theorems
    ([series_small_eval], [series_segment]) with the approximation theorems
    ([approx_series], [AsinApprox.approx_<kk>]). *)
From Coq Require Import Reals ZArith Lia Lra Psatz List.
From Flocq Require Import Core.
From Binary64 Require Import Binary64Add IEEE64 RoundingCore.
From Interval Require Import Tactic.
Require Import Ln1pLemmas AsinTables AsinKernel AsinSqrtStep AsinSeriesSmall AsinSegment AsinApprox AsinWithin.
Open Scope R_scope.

(** [|zl| <= 2^-52 zh] for a double-word whose high part is the rounded sum. *)
Lemma low_part_small zh zl : bpow radix2 (-28) <= B zh -> B zh = rndF (B zh + B zl) ->
  Rabs (B zl) <= B zh / 2 -> Rabs (B zl) <= / 4503599627370496 * B zh.
Proof.
  intros L Dw Hl.
  set (z := B zh) in *. set (d := B zl) in *.
  assert (Q1 : bpow radix2 (-1022) <= bpow radix2 (-29)) by (apply bpow_le; lia).
  assert (Q2 : bpow radix2 (-29) = bpow radix2 (-28) / 2).
  { replace (-29)%Z with (-28 + -1)%Z by reflexivity. rewrite bpow_plus. change (bpow radix2 (-1)) with (/ 2). field. }
  assert (Hn : bpow radix2 (-1022) <= Rabs (z + d)).
  { apply Rle_trans with (bpow radix2 (-29)); [exact Q1 | ].
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

(** The series branch: [z = zh + zl] with [zh] in [[2^-28, 2^-7]]. *)
Theorem fast_series zh zl : finite zh -> finite zl ->
  bpow radix2 (-28) <= B zh -> B zh <= bpow radix2 (-7) ->
  B zh = rndF (B zh + B zl) -> Rabs (B zl) <= B zh / 2 ->
  exists h l, asin_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    Rabs (B h + B l - asin (B zh + B zl)) <= bpow radix2 (-66) * asin (B zh + B zl).
Proof.
  intros Fh Fl L U Dw Hl.
  pose proof (low_part_small zh zl L Dw Hl) as Hd.
  destruct (series_small_eval zh zl Fh Fl L U Dw Hl) as [h [l [Hs [Fh' [Fl' [Nrm [ec [ea [Hec [Hea Eq]]]]]]]]]].
  exists h, l. split; [exact Hs | split; [exact Fh' | split; [exact Fl' | split; [exact Nrm | ]]]].
  set (z := B zh) in *. set (d := B zl) in *.
  bpow_num_in L. bpow_num_in U.
  assert (Hz : / 268435456 <= z <= 0.0078126) by (split; lra).
  assert (Hz0 : 0 < z) by lra.
  destruct qr_facts as [[Q00 Q01] [[Q10 Q11] [[Q20 Q21] [Q30 Q31]]]]. bpow_num_in Q31.
  assert (HA2 := approx_series z Hz).
  set (P := q0r + z * z * (q1r + z * z * (q2r + z * z * q3r))) in *.
  set (Tx := z * z * z * P) in *.
  assert (Hzz : z * z <= 0.0000610377) by nra.
  assert (Hu3 : 0 <= q2r + z * z * q3r <= 0.0501) by (split; nra).
  assert (Hu2 : 0 <= q1r + z * z * (q2r + z * z * q3r) <= 0.0801) by (split; nra).
  assert (HP : 0 <= P <= 0.1701) by (subst P; split; nra).
  assert (Hz3 : 0 <= z * z * z) by (apply Rmult_le_pos; [apply Rmult_le_pos | ]; lra).
  assert (HT : 0 <= Tx <= 0.1701 * (z * z * z)) by (subst Tx; split; nra).
  assert (Hec' : Rabs ec <= 8 / 18014398509481984).
  { apply Rle_trans with (/ 2 ^ 51); [exact Hec | interval with (i_prec 100)]. }
  assert (HE104 : / 2 ^ 104 <= / 1000000000000000000000000000000) by (interval with (i_prec 120)).
  assert (HA1 : Rabs (asin (z + d) - asin z - d) <= 0.51 * (z * z) * Rabs d).
  { apply asin_shift; [exact Hz | exact Hd]. }
  assert (HE : Rabs (asin (z + d) - (z + d + Tx)) <= 2.3 / 18014398509481984 * (z * z * z)).
  { replace (asin (z + d) - (z + d + Tx)) with ((asin (z + d) - asin z - d) + (asin z - (z + Tx))) by ring.
    apply Rle_trans with (Rabs (asin (z + d) - asin z - d) + Rabs (asin z - (z + Tx))); [apply Rabs_triang | ].
    assert (Hs1 : 0.51 * (z * z) * Rabs d <= 2.04 / 18014398509481984 * (z * z * z)).
    { pose proof (Rabs_pos d). assert (0 <= z * z) by nra. nra. }
    nra. }
  assert (Hb : Rabs (Tx * ec) <= 1.4 / 18014398509481984 * (z * z * z)).
  { rewrite Rabs_mult, (Rabs_pos_eq Tx) by lra. pose proof (Rabs_pos ec). nra. }
  assert (HAm : 0.999 * z <= asin (z + d)).
  { pose proof (Rabs_le_inv _ _ Hd) as [Hd1 Hd2].
    apply Rle_trans with (z + d); [nra | apply asin_ge; split; lra]. }
  assert (Hz3z : z * z * z <= 0.000061038 * z) by nra.
  assert (Hnum : (2.3 / 18014398509481984 * (z * z * z) + 1.4 / 18014398509481984 * (z * z * z)) * (1 + / 2 ^ 104)
                 + / 2 ^ 104 * (0.999 * z) <= bpow radix2 (-66) * (0.999 * z)).
  { bpow_num.
    assert (H1 : (2.3 / 18014398509481984 * (z * z * z) + 1.4 / 18014398509481984 * (z * z * z)) * (1 + / 2 ^ 104)
                 <= (3.7 / 18014398509481984 * 0.000061038 * z) * (1 + 1 / 1000000000000000000000000000000)) by nra.
    nra. }
  pose proof (fast_compose (asin (z + d)) (z + d + Tx) (Tx * ec) ea
    (2.3 / 18014398509481984 * (z * z * z)) (1.4 / 18014398509481984 * (z * z * z)) (/ 2 ^ 104)
    (0.999 * z) (bpow radix2 (-66)) HE Hb Hea HAm ltac:(lra) ltac:(apply Rlt_le; apply Rinv_0_lt_compat; apply pow_lt; lra) Hnum) as FC.
  rewrite Eq. replace ((z + d + Tx * (1 + ec)) * (1 + ea)) with ((z + d + Tx + Tx * ec) * (1 + ea)) by ring.
  exact FC.
Qed.
