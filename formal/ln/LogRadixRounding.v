(** Final binary64 conversion of the accurate radix-logarithm paths.
    The log2 theorem keeps [LM] Property 4 as an explicit midpoint-distance
    hypothesis. The log10 result is a rounded bounded approximation, without
    an unsupported whole-domain correct-rounding hypothesis. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Binary64 Require Import Binary64Add IEEE64 RoundingCore RoundingGaps.
From Q Require Q128 QSpec.
From Interval Require Import Tactic.
Require Import ExpAccurate LnAccurate LnReduction LnFastDecision LnEntryLemmas
  Ln1pLemmas LogRadixAccurate.
Open Scope R_scope.

Definition log2_accurate_result x := Q128.to_f64 (log2_acc x).
Definition log10_accurate_result x := Q128.to_f64 (log10_acc x).

(** Uniform size bounds for either radix, including subnormal inputs. *)
Lemma radix_log_range x b : finite x -> 0 < B x -> B x <> 1 ->
  0.5 <= ln b <= 3 ->
  bpow radix2 (-57) <= Rabs (ln (B x) / ln b) <= 1600.
Proof.
  intros Fx Px Nx Lb.
  pose proof (lf_ln_away x Fx Px Nx) as Away.
  pose proof (reduce_ok x Fx Px) as R.
  destruct (reduce x) as [[[e i] y] r].
  destruct R as [Hi [Er [Fy [Iy [Gy [Ex He]]]]]].
  destruct (ln_range i Hi) as [L1 [L2 _]].
  assert (Small : Rabs (ln (B x)) <= 800).
  { rewrite Ex, ln_pow2 by lra. apply lx_small; [lia | lra]. }
  unfold Rdiv. rewrite Rabs_mult, Rabs_Rinv by lra.
  rewrite (Rabs_pos_eq (ln b)) by lra.
  split.
  - apply Rmult_le_reg_r with (ln b); [lra | ].
    rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra.
    apply Rle_trans with (2 := Away).
    assert (P : 0 < bpow radix2 (-57)) by apply bpow_gt_0.
    apply Rle_trans with (bpow radix2 (-57) * 3); [nra | interval].
  - apply Rmult_le_reg_r with (ln b); [lra | ].
    rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra. lra.
Qed.

(** No underflow or overflow occurs when converting either nonzero accurate
    result. The Q128 value is normalized and binary64 conversion rounds once. *)
Lemma radix_accurate_round q v : NZ q ->
  bpow radix2 (-57) <= Rabs v <= 1600 ->
  Rabs (Q128.qval q - v) <= / 2 ^ 122 * Rabs v ->
  finite (Q128.to_f64 q) /\
  B (Q128.to_f64 q) = rndF (Q128.qval q).
Proof.
  intros N V E.
  assert (Vp : 0 < Rabs v).
  { pose proof (bpow_gt_0 radix2 (-57)); lra. }
  assert (SmallE : 0 <= / 2 ^ 122 <= / 2) by (split; interval).
  assert (Qlo : bpow radix2 (-58) <= Rabs (Q128.qval q)).
  { pose proof (Rabs_triang_inv v (Q128.qval q)) as T.
    rewrite Rabs_minus_sym in T.
    assert (bpow radix2 (-58) = bpow radix2 (-57) / 2) by (bpow_num; field).
    nra. }
  assert (Qhi : Rabs (Q128.qval q) <= bpow radix2 12).
  { pose proof (Rabs_triang_inv (Q128.qval q) v).
    change (bpow radix2 12) with 4096. nra. }
  assert (Nq : QSpec.normalized 128 (Q128.m q)).
  { destruct N as [Z | N]; [ | exact N].
    rewrite (qval_zero q Z), Rabs_R0 in Qlo.
    pose proof (bpow_gt_0 radix2 (-58)); lra. }
  assert (Round : B (Q128.to_f64 q) = rndF (Q128.qval q)).
  { apply ExpAccurate.to_f64_val; [exact Nq | ].
    apply Rle_lt_trans with (bpow radix2 12); [ | apply bpow_lt; lia].
    apply abs_round_le_generic; [exact _ | exact _ | apply fmt_pow; lia | exact Qhi]. }
  split; [ | exact Round].
  apply lf_nonzero_finite. intros Z.
  assert (Low : bpow radix2 (-58) <= Rabs (B (Q128.to_f64 q))).
  { rewrite Round. apply abs_round_ge_generic;
      [exact _ | exact _ | apply fmt_pow; lia | exact Qlo]. }
  rewrite Z, Rabs_R0 in Low. pose proof (bpow_gt_0 radix2 (-58)); lra.
Qed.

Theorem log2_accurate_round x : finite x -> 0 < B x -> B x <> 1 ->
  finite (log2_accurate_result x) /\
  B (log2_accurate_result x) = rndF (Q128.qval (log2_acc x)).
Proof.
  intros Fx Px Nx. destruct (log2_acc_bound x Fx Px) as [N E].
  exact (radix_accurate_round _ _ N
    (radix_log_range x 2 Fx Px Nx ltac:(split; interval)) E).
Qed.

Theorem log10_accurate_round x : finite x -> 0 < B x -> B x <> 1 ->
  finite (log10_accurate_result x) /\
  B (log10_accurate_result x) = rndF (Q128.qval (log10_acc x)).
Proof.
  intros Fx Px Nx. destruct (log10_acc_bound x Fx Px Nx) as [N E].
  exact (radix_accurate_round _ _ N
    (radix_log_range x 10 Fx Px Nx ltac:(split; interval)) E).
Qed.

Theorem log2_accurate_correct x : finite x -> 0 < B x -> B x <> 1 ->
  midpoint_far (Rabs (ln (B x) / ln 2)) (/ 2 ^ 109) ->
  finite (log2_accurate_result x) /\
  B (log2_accurate_result x) = rndF (ln (B x) / ln 2).
Proof.
  intros Fx Px Nx Far.
  destruct (log2_accurate_round x Fx Px Nx) as [F R].
  split; [exact F | rewrite R].
  destruct (log2_acc_bound x Fx Px) as [_ E].
  pose proof (radix_log_range x 2 Fx Px Nx ltac:(split; interval)) as V.
  assert (Vp : 0 < Rabs (ln (B x) / ln 2)).
  { pose proof (bpow_gt_0 radix2 (-57)); lra. }
  apply rounds_as with (/ 2 ^ 109).
  - intros Z; rewrite Z, Rabs_R0 in Vp; lra.
  - split; interval.
  - exact Far.
  - apply Rle_lt_trans with (1 := E).
    apply Rmult_lt_compat_r; [exact Vp | interval].
Qed.

Theorem log10_accurate_bounded x : finite x -> 0 < B x -> B x <> 1 ->
  finite (log10_accurate_result x) /\
  exists v, B (log10_accurate_result x) = rndF v /\
    Rabs (v - ln (B x) / ln 10) <= / 2 ^ 122 * Rabs (ln (B x) / ln 10).
Proof.
  intros Fx Px Nx. destruct (log10_accurate_round x Fx Px Nx) as [F R].
  split; [exact F | exists (Q128.qval (log10_acc x)); split; [exact R | ]].
  exact (proj2 (log10_acc_bound x Fx Px Nx)).
Qed.

(** Exact representable logarithms, notably powers of either radix, need no
    hard-case hypothesis: the reconstruction error fits inside their cell. *)
Lemma radix_accurate_representable q v : NZ q -> fmtF v ->
  bpow radix2 (-57) <= Rabs v <= 1600 ->
  Rabs (Q128.qval q - v) <= / 2 ^ 122 * Rabs v ->
  finite (Q128.to_f64 q) /\ B (Q128.to_f64 q) = v.
Proof.
  intros N F V E. destruct (radix_accurate_round q v N V E) as [Fin R].
  split; [exact Fin | rewrite R].
  assert (Vp : 0 < Rabs v) by (pose proof (bpow_gt_0 radix2 (-57)); lra).
  apply round_relative_close; [exact F | intros Z; rewrite Z, Rabs_R0 in Vp; lra | ].
  apply Rle_lt_trans with (1 := E).
  replace (Rabs v / 2 ^ 54) with ((/ 2 ^ 54) * Rabs v) by field.
  apply Rmult_lt_compat_r; [exact Vp | interval].
Qed.

Theorem log2_accurate_representable x : finite x -> 0 < B x -> B x <> 1 ->
  fmtF (ln (B x) / ln 2) ->
  finite (log2_accurate_result x) /\
  B (log2_accurate_result x) = ln (B x) / ln 2.
Proof.
  intros Fx Px Nx F. destruct (log2_acc_bound x Fx Px) as [N E].
  exact (radix_accurate_representable _ _ N F
    (radix_log_range x 2 Fx Px Nx ltac:(split; interval)) E).
Qed.

Theorem log10_accurate_representable x : finite x -> 0 < B x -> B x <> 1 ->
  fmtF (ln (B x) / ln 10) ->
  finite (log10_accurate_result x) /\
  B (log10_accurate_result x) = ln (B x) / ln 10.
Proof.
  intros Fx Px Nx F. destruct (log10_acc_bound x Fx Px Nx) as [N E].
  exact (radix_accurate_representable _ _ N F
    (radix_log_range x 10 Fx Px Nx ltac:(split; interval)) E).
Qed.
