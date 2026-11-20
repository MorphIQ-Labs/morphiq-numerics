(** The final log10 ULP contract, measured at the exact real result.
    Crossing a binade boundary cannot double the rounding allowance: an
    approximation just across it still rounds to that boundary exactly. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Binary64 Require Import Binary64Add IEEE64 RoundingGaps RelativeUlp.
From Q Require Q128.
From Interval Require Import Tactic.
Require Import Ln1pLemmas LogRadixAccurate LogRadixRounding.
Open Scope R_scope.

Lemma radix_round_error_positive v w : bpow radix2 (-57) <= v ->
  Rabs (w - v) <= / 2 ^ 122 * v ->
  Rabs (rndF w - v) <= (/ 2 + / 2 ^ 69) * ulp radix2 (FLT_exp emin prec) v.
Proof.
  intros V E.
  assert (Pv:0<=v) by (pose proof (bpow_gt_0 radix2 (-57)); lra).
  pose proof (relative_ulp_error (/2^122) v w ltac:(split; interval)
    ltac:(rewrite (Rabs_pos_eq v Pv); exact E)) as Bound.
  assert (Scale:(/2^122)*bpow radix2 53=/2^69).
  { replace (/2^122) with (bpow radix2 (-122)) by (rewrite pow_IZR; reflexivity).
    rewrite <-bpow_plus. rewrite pow_IZR; reflexivity. }
  rewrite Scale in Bound. exact Bound.
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
