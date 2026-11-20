(** The final log10 ULP contract, measured at the exact real result.
    Crossing a binade boundary cannot double the rounding allowance: an
    approximation just across it still rounds to that boundary exactly. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Binary64 Require Import Binary64Add IEEE64 RoundingGaps.
From Q Require Q128.
From Interval Require Import Tactic.
Require Import Ln1pLemmas LogRadixAccurate LogRadixRounding.
Open Scope R_scope.

Lemma radix_round_error_positive v w : bpow radix2 (-57) <= v ->
  Rabs (w - v) <= / 2 ^ 122 * v ->
  Rabs (rndF w - v) <= (/ 2 + / 2 ^ 69) * ulp radix2 (FLT_exp emin prec) v.
Proof.
  intros V E.
  assert (Pv : 0 < v) by (pose proof (bpow_gt_0 radix2 (-57)); lra).
  assert (Pe : 0 <= / 2 ^ 122 < / 2 ^ 54) by (split; interval).
  assert (We : - (/ 2 ^ 122 * v) <= w - v <= / 2 ^ 122 * v) by (apply Rabs_le_inv; exact E).
  assert (Pw : 0 < w) by (assert (/ 2 ^ 122 < 1) by interval; nra).
  set (e := mag radix2 v).
  assert (Ge : (-56 <= e)%Z).
  { unfold e. apply mag_ge_bpow. rewrite Rabs_pos_eq by lra. exact V. }
  assert (Top : v < bpow radix2 e).
  { unfold e. pose proof (bpow_mag_gt radix2 v); rewrite Rabs_pos_eq in H by lra; exact H. }
  assert (U : ulp radix2 (FLT_exp emin prec) v = bpow radix2 (e - 53)).
  { rewrite ulp_neq_0 by lra. unfold cexp, FLT_exp, emin, prec. fold e.
    rewrite Z.max_l by lia. reflexivity. }
  assert (Budget : / 2 ^ 122 * v <= / 2 ^ 69 * bpow radix2 (e - 53)).
  { apply Rle_trans with ((/ 2 ^ 122) * bpow radix2 e).
    - apply Rmult_le_compat_l; lra.
    - right. replace (/ 2 ^ 122) with (bpow radix2 (-122)) by (bpow_num; field).
      replace (/ 2 ^ 69) with (bpow radix2 (-69)) by (bpow_num; field).
      rewrite <- !bpow_plus. f_equal. lia. }
  rewrite U.
  destruct (Rlt_le_dec w (bpow radix2 e)) as [Inside | Across].
  - assert (Mw : (mag radix2 w <= e)%Z).
    { apply mag_le_bpow; [lra | rewrite Rabs_pos_eq by lra; exact Inside]. }
    assert (Uw : ulp radix2 (FLT_exp emin prec) w <= bpow radix2 (e - 53)).
    { rewrite ulp_neq_0 by lra. apply bpow_le. unfold cexp, FLT_exp, emin, prec. lia. }
    pose proof (@error_le_half_ulp radix2 (FLT_exp emin prec) ltac:(exact _) ne w) as Round.
    change (Rabs (rndF w - w) <= / 2 * ulp radix2 (FLT_exp emin prec) w) in Round.
    replace (rndF w - v) with ((rndF w - w) + (w - v)) by ring.
    eapply Rle_trans; [apply Rabs_triang | nra].
  - assert (Rounded : rndF w = bpow radix2 e).
    { apply round_relative_close; [apply fmt_pow; lia | apply Rgt_not_eq, bpow_gt_0 | ].
      rewrite Rabs_pos_eq by lra.
      rewrite (Rabs_pos_eq (bpow radix2 e)) by apply bpow_ge_0.
      apply Rle_lt_trans with ((/ 2 ^ 122) * v); [lra | ].
      assert (0 < bpow radix2 e) by apply bpow_gt_0.
      unfold Rdiv; nra. }
    rewrite Rounded, Rabs_pos_eq by lra.
    pose proof (bpow_gt_0 radix2 (e - 53)). nra.
Qed.

Lemma radix_round_error v w : bpow radix2 (-57) <= Rabs v ->
  Rabs (w - v) <= / 2 ^ 122 * Rabs v ->
  Rabs (rndF w - v) <= (/ 2 + / 2 ^ 69) * ulp radix2 (FLT_exp emin prec) v.
Proof.
  intros V E. destruct (Rle_lt_dec 0 v) as [Pos | Neg].
  - rewrite (Rabs_pos_eq v) in V, E by exact Pos. apply radix_round_error_positive; assumption.
  - rewrite (Rabs_left v) in V, E by exact Neg.
    assert (Opp : Rabs (-w - -v) <= / 2 ^ 122 * -v).
    { replace (-w - -v) with (-(w-v)) by ring. rewrite Rabs_Ropp. exact E. }
    pose proof (radix_round_error_positive (-v) (-w) V Opp) as Bound.
    unfold ne in Bound. rewrite round_NE_opp in Bound.
    replace (- round radix2 (FLT_exp emin prec) ZnearestE w - -v)
      with (- (round radix2 (FLT_exp emin prec) ZnearestE w - v)) in Bound by ring.
    rewrite Rabs_Ropp, ulp_opp in Bound. exact Bound.
Qed.

Theorem log10_accurate_ulp x : finite x -> 0 < B x -> B x <> 1 ->
  finite (log10_accurate_result x) /\
  Rabs (B (log10_accurate_result x) - ln (B x) / ln 10)
    <= (/ 2 + / 2 ^ 69) * ulp radix2 (FLT_exp emin prec) (ln (B x) / ln 10).
Proof.
  intros Fx Px Nx. destruct (log10_accurate_round x Fx Px Nx) as [F R].
  split; [exact F | rewrite R]. apply radix_round_error.
  - exact (proj1 (radix_log_range x 10 Fx Px Nx ltac:(split; interval))).
  - exact (proj2 (log10_acc_bound x Fx Px Nx)).
Qed.
