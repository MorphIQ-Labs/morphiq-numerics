(** atan2's tiny ratios: [atan2_tiny_phi] returns the correctly rounded value of [atan (n/d)]
    for a quotient below [2^-900], which is [n/d] itself rounded except where [n/d] is exactly the
    midpoint of two subnormal numbers; there the correct value is the lower neighbor. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 Grid RoundingGaps.
From Interval Require Import Tactic.
Require Import Ln1pLemmas AsinTables AsinKernel AsinSqrtStep AsinSegment AsinWithin AsinFacts AsinPath AsinCorrect AsinSmall AsinEntry
  ExpAccurate Atan2Tables Atan2Kernel Atan2Within Atan2Newton Atan2Odd Atan2Decode Atan2TinyMid.
Open Scope R_scope.

Lemma small_bits k : (0 <= k < 2 ^ 52)%Z -> finite (aw k) /\ B (aw k) = IZR k * bpow radix2 (-1074).
Proof.
  intros Hk. unfold aw, b64_of_bits, binary_float_of_bits.
  rewrite is_finite_FF2B, B2R_FF2B. unfold binary_float_of_bits_aux, split_bits. cbn [fst snd].
  assert (Hs : (2 ^ 52 * 2 ^ 11 <=? k)%Z = false) by (apply Z.leb_gt; lia). rewrite Hs.
  assert (Hm : (k mod 2 ^ 52 = k)%Z) by (apply Z.mod_small; lia). rewrite Hm.
  assert (Hd : (k / 2 ^ 52 mod 2 ^ 11 = 0)%Z) by (rewrite Z.div_small by lia; reflexivity). rewrite Hd.
  cbn [Zeq_bool]. destruct k as [ | p | p]; cbn.
  - split; [reflexivity | ring].
  - split; [reflexivity | ]. unfold F2R. cbn [Fnum Fexp]. reflexivity.
  - lia.
Qed.

Lemma cmp_val x y c : finite x -> finite y -> atan2_cmp_is x y c = true <-> Rcompare (B x) (B y) = c.
Proof.
  intros Fx Fy. unfold atan2_cmp_is, asin_cmp. rewrite (Bcompare_correct 53 1024 x y Fx Fy).
  destruct (Rcompare (B x) (B y)), c; simpl; split; intros H; try discriminate; reflexivity.
Qed.

Lemma tiny_val : finite atan2_tiny /\ B atan2_tiny = bpow radix2 (-900).
Proof.
  destruct (word_ok_intro (0x07b0000000000000)%Z false 4503599627370496%positive 952%nat 4503599627370496%Z 0%Z (-952)%Z
    eq_refl eq_refl ltac:(lia) eq_refl) as [F V].
  split; [exact F | ]. unfold atan2_tiny. rewrite V.
  assert (E : IZR 4503599627370496 = bpow radix2 52) by (apply (IZR_Zpower radix2 52 ltac:(lia)) || exact (izr_pow2 52 ltac:(lia))).
  rewrite E, <- bpow_plus. reflexivity.
Qed.

Lemma minpos_val : finite atan2_min_positive /\ B atan2_min_positive = bpow radix2 (-1022).
Proof.
  destruct (word_ok_intro (0x0010000000000000)%Z false 4503599627370496%positive 1074%nat 4503599627370496%Z 0%Z (-1074)%Z
    eq_refl eq_refl ltac:(lia) eq_refl) as [F V].
  split; [exact F | ]. unfold atan2_min_positive. rewrite V.
  assert (E : IZR 4503599627370496 = bpow radix2 52) by exact (izr_pow2 52 ltac:(lia)).
  rewrite E, <- bpow_plus. reflexivity.
Qed.

(** With no midpoint at the quotient, [atan] of a tiny quotient rounds as the quotient does. *)
Lemma phi_rounds nv dv mn en md ed :
  Z.odd mn = true -> (0 < mn < 2 ^ 53)%Z -> nv = IZR mn * bpow radix2 en ->
  (0 < md < 2 ^ 53)%Z -> dv = IZR md * bpow radix2 ed ->
  0 < nv -> 0 < dv -> nv / dv <= bpow radix2 (-900) ->
  (forall u, fmtF u -> 0 <= u -> nv / dv <> (u + succ radix2 fexp64 u) / 2) ->
  rndF (atan (nv / dv)) = rndF (nv / dv).
Proof.
  intros Omn Hmn Hn Hmd Hd Pn Pd Ht Hnm.
  set (t := nv / dv) in *.
  assert (Pt : 0 < t) by (unfold t; apply Rdiv_lt_0_compat; lra).
  assert (Hb108 : 0 < bpow radix2 (-108) <= / 2) by (split; [apply bpow_gt_0 | apply Rle_trans with (bpow radix2 (-1)); [apply bpow_le; lia | change (bpow radix2 (-1)) with (/ 2); lra]]).
  apply same_rounding_abs with (dl := t * bpow radix2 (-108)); [exact Pt | nra | | ].
  - intros u Fu U0.
    destruct (midpoint_form u Fu U0) as [mu [c [Hmu [Hc [Hu [Hmid _]]]]]].
    change (succ radix2 (FLT_exp emin prec) u) with (succ radix2 fexp64 u). rewrite Hmid.
    destruct (gap_rel nv dv mn en md ed mu c Pn Pd Omn Hmn Hn Hmd Hd Hmu) as [E | G].
    + exfalso. apply (Hnm u Fu U0). rewrite Hmid. exact E.
    + exact G.
  - assert (Ht1 : t <= / 16) by (apply Rle_trans with (bpow radix2 (-900)); [exact Ht | apply Rle_trans with (bpow radix2 (-4)); [apply bpow_le; lia | bpow_num; interval with (i_prec 60)]]).
    pose proof (atan_small_pos t ltac:(split; lra)) as [A1 A2].
    assert (Hcube : t * t * t / 3 < t * bpow radix2 (-108)).
    { assert (Htt : t * t < bpow radix2 (-108)).
      { apply Rle_lt_trans with (bpow radix2 (-900) * bpow radix2 (-900)); [nra | ].
        rewrite <- bpow_plus. apply bpow_lt. lia. }
      nra. }
    rewrite Rabs_left1 by lra. nra.
Qed.
