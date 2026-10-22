(** asinh's fast path over [(ASINH_IS_X, inf)]: the double-word is [arcsinh x] to
    a relative [2^-63], and the rounding decision accepts only [RN (arcsinh x)]. *)
From Coq Require Import Reals ZArith Lia Lra Psatz List.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 RoundingCore RoundingTest.
From Interval Require Import Tactic.
Require Import Ln1pLemmas AsinTables AsinKernel AsinSqrtStep AsinRecip AsinhKernel AsinhConst AsinhWithin AsinhSeries AsinhLog AsinhLarge AsinhLargeFast.
Open Scope R_scope.

Definition FastOk (x : f64) (y : f64 * f64) : Prop :=
  finite (fst y) /\ finite (snd y) /\ B (fst y) = rndF (B (fst y) + B (snd y)) /\
  bpow radix2 (-30) <= B (fst y) /\ B (fst y) <= bpow radix2 10 /\
  Rabs (B (fst y) + B (snd y) - arcsinh (B x)) <= bpow radix2 (-63) * arcsinh (B x).

Theorem asinh_fast_ok x : finite x -> bpow radix2 (-26) <= B x -> FastOk x (asinh_fast x).
Proof.
  intros Fx L.
  destruct two_m7_val as [F7 V7]. destruct two_28_val as [F28 V28].
  unfold asinh_fast.
  destruct (asinh_lt x asinh_two_m7) eqn:H1.
  - apply (lt_correct x asinh_two_m7 Fx F7) in H1. rewrite V7 in H1.
    destruct (asinh_series_fast x Fx L (Rlt_le _ _ H1)) as [h [l [Hs [Fh [Fl [Dw Er]]]]]].
    rewrite Hs. unfold FastOk. cbn [fst snd].
    assert (Hx7 : B x <= / 128) by (assert (bpow radix2 (-7) = / 128) by (bpow_num; reflexivity); lra).
    assert (Hx26 : / 67108864 <= B x) by (assert (bpow radix2 (-26) = / 67108864) by (bpow_num; reflexivity); lra).
    pose proof (arcsinh_ge_cubic (B x) ltac:(split; lra)) as Ag.
    pose proof (arcsinh_le_id (B x) ltac:(lra)) as Al.
    set (A := arcsinh (B x)) in *.
    assert (HAlo : 0.99 * B x <= A).
    { assert (B x * B x * B x <= B x * / 16384) by nra. lra. }
    assert (Hb66 : bpow radix2 (-66) <= bpow radix2 (-63)) by (apply bpow_le; lia).
    assert (Hmid : bpow radix2 (-66) * A <= bpow radix2 (-63) * A).
    { apply Rmult_le_compat_r; [lra | exact Hb66]. }
    pose proof (bpow_gt_0 radix2 (-66)) as Pb66.
    apply Rabs_le_inv in Er. destruct Er as [Er1 Er2].
    assert (Hbb : bpow radix2 (-66) * A <= 1e-10).
    { assert (bpow radix2 (-66) <= 1e-19) by (bpow_num; apply Rle_trans with (/ 10000000000000000000); [apply Rinv_le_contravar; [lra | simpl; lra] | lra]).
      assert (bpow radix2 (-66) * A <= 1e-19 * A) by (apply Rmult_le_compat_r; lra). lra. }
    split; [exact Fh | split; [exact Fl | split; [exact Dw | split; [ | split]]]].
    + rewrite Dw. apply rndF_ge_bpow; [lia | ].
      assert (bpow radix2 (-30) = / 1073741824) by (bpow_num; reflexivity). lra.
    + rewrite Dw. apply rnd_le_pow; [lia | ].
      assert (bpow radix2 10 = 1024) by (bpow_num; reflexivity). lra.
    + apply Rabs_le. split; lra.
  - destruct (asinh_lt x asinh_two_28) eqn:H2.
    + apply (lt_correct x asinh_two_28 Fx F28) in H2. rewrite V28 in H2.
      assert (L7 : bpow radix2 (-7) <= B x).
      { apply Rnot_lt_le; intros H. assert (asinh_lt x asinh_two_m7 = true) by (apply (lt_correct x asinh_two_m7 Fx F7); rewrite V7; exact H). congruence. }
      destruct (asinh_logarithm_fast x Fx L7 H2) as [h [l [Hs [Fh [Fl [Dw [Hl1 [Hl2 Er]]]]]]]].
      rewrite Hs. unfold FastOk. cbn [fst snd].
      split; [exact Fh | split; [exact Fl | split; [exact Dw | split; [ | split; [exact Hl2 | exact Er]]]]].
      apply Rle_trans with (bpow radix2 (-8)); [apply bpow_le; lia | exact Hl1].
    + assert (L28 : bpow radix2 28 <= B x).
      { apply Rnot_lt_le; intros H. assert (asinh_lt x asinh_two_28 = true) by (apply (lt_correct x asinh_two_28 Fx F28); rewrite V28; exact H). congruence. }
      destruct (asinh_large_fast x Fx L28) as [h [l [Hs [Fh [Fl [Dw [Hl1 [Hl2 Er]]]]]]]].
      rewrite Hs. unfold FastOk. cbn [fst snd].
      split; [exact Fh | split; [exact Fl | split; [exact Dw | split; [ | split; [exact Hl2 | exact Er]]]]].
      apply Rle_trans with (bpow radix2 (-8)); [apply bpow_le; lia | exact Hl1].
Qed.

(** The rounding decision accepts only the correctly rounded value. *)
Lemma asinh_decide_some yh yl Z v : finite yh -> finite yl ->
  bpow radix2 (-30) <= B yh -> B yh <= bpow radix2 10 -> B yh = rndF (B yh + B yl) ->
  Rabs (Z - (B yh + B yl)) <= bpow radix2 (-63) * Rabs Z ->
  asinh_decide (yh, yl) = Some v -> v = yh /\ rndF Z = B yh.
Proof.
  intros Fh Fl L U Dw Err D. destruct eps_val as [Fe Ve].
  unfold asinh_decide in D. cbn [fst snd] in D.
  assert (Hpos : 0 < B yh) by (apply Rlt_le_trans with (bpow radix2 (-30)); [apply bpow_gt_0 | exact L]).
  assert (Hrng : bpow radix2 (-80) <= bpow radix2 (-63) <= bpow radix2 (-60)) by (split; apply bpow_le; lia).
  assert (Hbd : bpow radix2 (-900) <= Rabs (B yh) <= bpow radix2 1000).
  { rewrite Rabs_pos_eq by lra. split.
    - apply Rle_trans with (bpow radix2 (-30)); [apply bpow_le; lia | exact L].
    - apply Rle_trans with (bpow radix2 10); [exact U | apply bpow_le; lia]. }
  refine (decide_with_ok yh yl asinh_eps Z (bpow radix2 (-63)) v Fh Fl Fe Hbd Dw Hrng _ Err D).
  rewrite Ve. split; [apply Rle_refl | ].
  bpow_num. interval with (i_prec 100).
Qed.
