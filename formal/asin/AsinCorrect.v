(** asin's rounding decision and the positive branch end to end: for [x] in
    [[2^-26, 1 - 2^-53]] the Rust's [asin_positive] returns [RN (asin x)], given
    that no binary64 midpoint lies within [2^-124] relatively of [asin x]
    ([Stable]: the published worst-case search, CORE-MATH's [asin.wc], found none
    within [2^-58.6] ulp, [2^-110] relatively). *)
From Coq Require Import Reals ZArith Lia Lra Psatz List.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 RoundingCore RoundingTest.
From Interval Require Import Tactic.
From Q Require Import Q256 Q256Real QSpec.
Require Import Ln1pLemmas AsinTables AsinKernel AsinSqrtStep AsinNormal AsinSegment AsinWithin AsinFacts AsinRecip
  AsinPath AsinAccurate ErfcxAccurateInputs.
Open Scope R_scope.

(** No binary64 midpoint within [2^-124] (relatively) of the true value: rounding anything
    that close gives the correctly rounded value. *)
Definition Stable (z : R) : Prop :=
  forall w, Rabs (w - z) <= bpow radix2 (-124) * Rabs z -> rndF w = rndF z.

Lemma eps_val : finite asin_eps /\ B asin_eps = bpow radix2 (-62) * (1 + bpow radix2 (-50)).
Proof.
  destruct (word_ok_intro (0x3c10000000000004)%Z false 4503599627370500%positive 114%nat (1125899906842625)%Z 2%Z (-112)%Z
    eq_refl eq_refl ltac:(lia) eq_refl) as [F V].
  split; [exact F | ]. unfold asin_eps. rewrite V. bpow_num. lra.
Qed.

(** The rounding decision accepts only the correctly rounded value. *)
Lemma decide_some yh yl Z v : finite yh -> finite yl ->
  bpow radix2 (-900) <= B yh -> B yh <= bpow radix2 1000 -> B yh = rndF (B yh + B yl) ->
  Rabs (Z - (B yh + B yl)) <= bpow radix2 (-62) * Rabs Z ->
  asin_decide (yh, yl) = Some v -> v = yh /\ rndF Z = B yh.
Proof.
  intros Fh Fl L U Dw Err D. destruct eps_val as [Fe Ve].
  unfold asin_decide in D. cbn [fst snd] in D.
  assert (Hpos : 0 < B yh) by (apply Rlt_le_trans with (bpow radix2 (-900)); [apply bpow_gt_0 | exact L]).
  assert (Hrng : bpow radix2 (-80) <= bpow radix2 (-62) <= bpow radix2 (-60)) by (split; apply bpow_le; lia).
  assert (Habs : Rabs (B yh) <= bpow radix2 1000) by (rewrite Rabs_pos_eq by lra; exact U).
  refine (decide_with_ok yh yl asin_eps Z (bpow radix2 (-62)) v Fh Fl Fe
    (conj (Rle_trans _ _ _ L (Rle_abs _)) Habs) Dw
    Hrng _ Err D).
  rewrite Ve. split; [apply Rle_refl | ].
  bpow_num. interval with (i_prec 100).
Qed.

Lemma le_split_exact x : finite x -> asin_le x asin_split = true -> B x <= SPLIT.
Proof.
  intros Fx H. destruct split_val as [V F].
  unfold asin_le, asin_cmp in H. rewrite (Bcompare_correct 53 1024 x asin_split Fx F), V in H.
  unfold SPLIT. unfold SPLIT_R in H.
  destruct (Rcompare_spec (B x) (6369051672525772 / 2 ^ 53)) as [Hlt | Heq | Hgt]; try discriminate H.
  - rewrite p53 in Hlt. lra.
  - rewrite p53 in Heq. lra.
Qed.

Lemma gt_split_exact x : finite x -> B x <= 1 - / 9007199254740992 -> asin_le x asin_split = false ->
  SPLIT_UP <= B x.
Proof.
  intros Fx U H. destruct split_val as [V F].
  unfold asin_le, asin_cmp in H. rewrite (Bcompare_correct 53 1024 x asin_split Fx F), V in H.
  unfold SPLIT_R in H.
  destruct (Rcompare_spec (B x) (6369051672525772 / 2 ^ 53)) as [Hlt | Heq | Hgt]; try discriminate H.
  rewrite p53 in Hgt.
  assert (L : / 2 <= B x) by lra.
  destruct (grid53 x Fx L U) as [k [Hk [K1 K2]]]. rewrite bp53 in Hk.
  assert (Hk1 : (6369051672525773 <= k)%Z).
  { destruct (Z_le_gt_dec 6369051672525773 k) as [Ok | Bad]; [exact Ok | exfalso].
    assert (IZR k <= 6369051672525772) by (apply IZR_le; lia).
    rewrite Hk in Hgt. nra. }
  unfold SPLIT_UP. rewrite Hk. assert (IZR 6369051672525773 <= IZR k) by (apply IZR_le; exact Hk1).
  change (IZR 6369051672525773) with 6369051672525773 in H0.
  assert (Hq : / 9007199254740992 > 0) by (apply Rinv_0_lt_compat; lra).
  nra.
Qed.

(** The accurate value rounds to the correctly rounded result. *)
Lemma accurate_round q Z : Q256Real.valid q -> Rabs (qval q - Z) <= bpow radix2 (-124) * Z -> Stable Z ->
  / 67108864 <= Z <= 1.6 -> finite (Q256.to_f64 q) /\ B (Q256.to_f64 q) = rndF Z.
Proof.
  intros Vq Err0 St [Z0 Z2].
  assert (Err : Rabs (qval q - Z) <= bpow radix2 (-124) * Rabs Z) by (rewrite (Rabs_pos_eq Z); [exact Err0 | lra]).
  assert (Hb : bpow radix2 (-124) <= / 1000000).
  { apply Rle_trans with (bpow radix2 (-20)); [apply bpow_le; lia | bpow_num; interval with (i_prec 100)]. }
  pose proof (bpow_gt_0 radix2 (-124)) as Hb0.
  assert (Hq : 0 <= qval q <= 2).
  { apply Rabs_le_inv in Err as [E1 E2]. rewrite (Rabs_pos_eq Z) in E1, E2 by lra. split; nra. }
  assert (Hr : Rabs (rndF (qval q)) < bpow radix2 1024).
  { assert (Hge : 0 <= rndF (qval q)) by (apply round_ge_generic; [exact _ | exact _ | apply generic_format_0 | lra]).
    assert (Hle : rndF (qval q) <= 2) by (apply rndF_le_two; lra).
    rewrite Rabs_pos_eq by exact Hge.
    apply Rle_lt_trans with 2; [exact Hle | ]. change 2 with (bpow radix2 1). apply bpow_lt; lia. }
  destruct (q_to_float_round q Vq Hr) as [Fq Bq].
  split; [exact Fq | ]. rewrite Bq. apply St. exact Err.
Qed.

Lemma red_fst_true x : asin_le x asin_split = true -> fst (asin_reduced x) = true.
Proof. intros H. unfold asin_reduced. rewrite H. reflexivity. Qed.

Lemma red_fst_false x : asin_le x asin_split = false -> fst (asin_reduced x) = false.
Proof. intros H. unfold asin_reduced. rewrite H. reflexivity. Qed.

(** From a normalized double-word within [2^-62] of [Z]: its leading word is in the decision's range. *)
Lemma dw_range yh yl Z : B yh = rndF (B yh + B yl) -> / 67108864 <= Z <= 1.6 ->
  Rabs (B yh + B yl - Z) <= bpow radix2 (-62) * Z ->
  bpow radix2 (-28) <= B yh <= 2 /\ 0 < B yh /\ bpow radix2 (-28) <= B yh + B yl.
Proof.
  intros Dw [Z0 Z1] Err.
  assert (Hb : bpow radix2 (-62) <= / 1000000).
  { apply Rle_trans with (bpow radix2 (-20)); [apply bpow_le; lia | bpow_num; interval with (i_prec 100)]. }
  pose proof (bpow_gt_0 radix2 (-62)) as Hb0. pose proof (bpow_gt_0 radix2 (-28)) as H28.
  apply Rabs_le_inv in Err as [E1 E2].
  assert (Hlo : bpow radix2 (-28) <= B yh + B yl).
  { assert (bpow radix2 (-28) <= / 67108864 * 0.99) by (bpow_num; interval with (i_prec 100)). nra. }
  assert (Hhi : B yh + B yl <= 2) by nra.
  split; [split | split].
  - rewrite Dw. apply rndF_ge_bpow; [lia | exact Hlo].
  - rewrite Dw. apply rndF_le_two. exact Hhi.
  - rewrite Dw. apply Rlt_le_trans with (bpow radix2 (-28)); [exact H28 | apply rndF_ge_bpow; [lia | exact Hlo]].
  - exact Hlo.
Qed.

Theorem positive_correct x : finite x -> / 67108864 <= B x -> B x <= 1 - / 9007199254740992 -> Stable (asin (B x)) ->
  finite (asin_positive x) /\ B (asin_positive x) = rndF (asin (B x)).
Proof.
  intros Fx L U St.
  pose proof quarter_pi_le as Pq. pose proof half_pi_le as Ph. pose proof PI_RGT_0 as Ppos.
  assert (Hxb : 0 <= B x <= 1) by (split; [ | lra]; assert (0 < / 67108864) by (apply Rinv_0_lt_compat; lra); lra).
  pose proof (asin_nonneg _ Hxb) as Z0. pose proof (asin_ge _ Hxb) as Zge. pose proof (asin_bound (B x)) as [_ Zhalf].
  set (Z := asin (B x)) in *.
  assert (HZr : / 67108864 <= Z <= 1.6) by lra.
  assert (Hzr' : 0 < Z) by (assert (0 < / 67108864) by (apply Rinv_0_lt_compat; lra); lra).
  assert (Hb63 : bpow radix2 (-63) <= bpow radix2 (-62)) by (apply bpow_le; lia).
  unfold asin_positive. cbv zeta.
  destruct (asin_le x asin_split) eqn:Hle.
  - (* direct *)
    assert (L28 : bpow radix2 (-28) <= B x).
    { apply Rle_trans with (/ 67108864); [bpow_num; interval with (i_prec 100) | exact L]. }
    destruct (fast_direct x Fx L28 Hle) as [yh [yl [Hf [Fyh [Fyl [Nrm Err]]]]]].
    rewrite Hf. cbv iota.
    assert (Err62 : Rabs (B yh + B yl - Z) <= bpow radix2 (-62) * Z).
    { apply Rle_trans with (1 := Err). apply Rmult_le_compat_r; [lra | exact Hb63]. }
    destruct (dw_range yh yl Z Nrm HZr Err62) as [[R1 R2] [Hyh Hsum]].
    assert (Hred : fst (asin_reduced x) = true) by (apply red_fst_true; exact Hle).
    rewrite Hred.
    destruct (asin_decide (yh, yl)) as [v | ] eqn:Hd.
    + assert (HL : bpow radix2 (-900) <= B yh) by (apply Rle_trans with (bpow radix2 (-28)); [apply bpow_le; lia | exact R1]).
      assert (HU : B yh <= bpow radix2 1000) by (apply Rle_trans with 2; [exact R2 | change 2 with (bpow radix2 1); apply bpow_le; lia]).
      assert (Err' : Rabs (Z - (B yh + B yl)) <= bpow radix2 (-62) * Rabs Z).
      { rewrite Rabs_minus_sym, (Rabs_pos_eq Z) by lra. exact Err62. }
      destruct (decide_some yh yl Z v Fyh Fyl HL HU Nrm Err' Hd) as [Hv HZ].
      rewrite Hv. split; [exact Fyh | symmetry; exact HZ].
    + unfold asin_accurate.
      assert (Hnorm : bpow radix2 (-1022) <= Rabs (B yh + B yl)).
      { rewrite Rabs_pos_eq by (pose proof (bpow_gt_0 radix2 (-28)); lra).
        apply Rle_trans with (bpow radix2 (-28)); [apply bpow_le; lia | exact Hsum]. }
      pose proof (dw_low yh yl Hnorm Nrm) as Hlow. rewrite (Rabs_pos_eq (B yh)) in Hlow by lra.
      destruct (accurate_direct x yh yl Fx Fyh Fyl L (le_split_exact x Fx Hle) Hyh Hlow Err62) as [Vq Eq].
      change (asin (B x)) with Z in Eq.
      exact (accurate_round _ Z Vq Eq St HZr).
  - (* complement *)
    assert (HSU : SPLIT_UP <= B x) by (apply gt_split_exact; [exact Fx | exact U | exact Hle]).
    destruct (fast_complement x Fx ltac:(unfold SPLIT_UP_R; unfold SPLIT_UP in HSU; rewrite p53; lra) U)
      as [yh [yl [dh [dl [Hf [Fyh [Fyl [Fdh [Fdl [Nrm [Hdh [Hdl [Err Errd]]]]]]]]]]]]].
    rewrite Hf. cbv iota.
    destruct (dw_range yh yl Z Nrm HZr Err) as [[R1 R2] [Hyh Hsum]].
    assert (Hred : fst (asin_reduced x) = false) by (apply red_fst_false; exact Hle).
    rewrite Hred.
    destruct (asin_decide (yh, yl)) as [v | ] eqn:Hd.
    + assert (HL : bpow radix2 (-900) <= B yh) by (apply Rle_trans with (bpow radix2 (-28)); [apply bpow_le; lia | exact R1]).
      assert (HU : B yh <= bpow radix2 1000) by (apply Rle_trans with 2; [exact R2 | change 2 with (bpow radix2 1); apply bpow_le; lia]).
      assert (Err' : Rabs (Z - (B yh + B yl)) <= bpow radix2 (-62) * Rabs Z).
      { rewrite Rabs_minus_sym, (Rabs_pos_eq Z) by lra. exact Err. }
      destruct (decide_some yh yl Z v Fyh Fyl HL HU Nrm Err' Hd) as [Hv HZ].
      rewrite Hv. split; [exact Fyh | symmetry; exact HZ].
    + unfold asin_accurate.
      destruct (accurate_complement x dh dl Fx Fdh Fdl HSU U Hdh Hdl Errd) as [Vq Eq].
      change (asin (B x)) with Z in Eq.
      exact (accurate_round _ Z Vq Eq St HZr).
Qed.
