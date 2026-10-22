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

(** [phi_rounds] and the exact-midpoint characterization for the pair [n, d] of finite positive operands. *)
Lemma no_exact_mid_or_cond n d mn en md ed :
  finite n -> finite d -> 0 < B n -> 0 < B d ->
  Z.odd mn = true -> (0 < mn < 2 ^ 53)%Z -> B n = IZR mn * bpow radix2 en ->
  Z.odd md = true -> (0 < md < 2 ^ 53)%Z -> B d = IZR md * bpow radix2 ed ->
  forall u, fmtF u -> 0 <= u -> B n / B d = (u + succ radix2 fexp64 u) / 2 ->
  exists k, (0 <= k < 2 ^ 52)%Z /\ mn = ((2 * k + 1) * md)%Z /\ en = (ed - 1075)%Z /\
    B n / B d = IZR (2 * k + 1) * bpow radix2 (-1075).
Proof.
  intros Fn Fd Pn Pd Omn Hmn Hn Omd Hmd Hd u Fu U0 E.
  destruct (exact_mid (B n) (B d) mn en md ed u Fu U0 Omn Hmn Hn Omd Hmd Hd Pd E) as [k [Hk [Emn Een]]].
  exists k. refine (conj Hk (conj Emn (conj Een _))).
  rewrite Hn, Hd, Emn, Een. rewrite mult_IZR.
  assert (Hp : bpow radix2 (ed - 1075) = bpow radix2 ed * bpow radix2 (-1075)) by (rewrite <- bpow_plus; f_equal).
  rewrite Hp. assert (0 < IZR md) by (apply IZR_lt; lia). pose proof (bpow_gt_0 radix2 ed).
  field. split; lra.
Qed.

Lemma atan_lt_id x : 0 < x -> atan x < x.
Proof.
  intros H. destruct (atan_id_diff 0 x ltac:(lra) H) as [c [[Hc1 Hc2] E]]. rewrite atan_0 in E.
  assert (Hq : 0 < c * c / (1 + c * c)) by (apply Rdiv_lt_0_compat; nra).
  nra.
Qed.

Lemma rndF_mono_bpow e v : (-1074 <= e)%Z -> bpow radix2 e <= v -> bpow radix2 e <= rndF v.
Proof. intros He H. apply round_ge_generic; [exact _ | exact _ | apply fmt_bpow; exact He | exact H]. Qed.

Lemma rndF_le_bpow e v : (-1074 <= e)%Z -> v <= bpow radix2 e -> rndF v <= bpow radix2 e.
Proof.
  intros He H. apply Rle_trans with (rndF (bpow radix2 e)); [apply round_le; [exact _ | exact _ | exact H] | ].
  rewrite round_generic; [lra | exact _ | apply fmt_bpow; exact He].
Qed.

Theorem tiny_phi_ok n d : finite n -> finite d -> 0 < B n -> B n <= B d -> B (fdiv n d) < bpow radix2 (-900) ->
  finite (atan2_tiny_phi n d (fdiv n d)) /\ B (atan2_tiny_phi n d (fdiv n d)) = rndF (atan (B n / B d)).
Proof.
  intros Fn Fd Pn Hnd Hq. set (q := fdiv n d) in *.
  assert (Pd : 0 < B d) by lra.
  assert (Ht1 : B n / B d <= 1).
  { apply Rmult_le_reg_r with (B d); [exact Pd | ]. unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra. lra. }
  assert (Pt : 0 < B n / B d) by (apply Rdiv_lt_0_compat; lra).
  destruct (fdiv_ok 1 0 n d Fn ltac:(lra) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(unfold bnd; rewrite Rabs_pos_eq by lra; simpl; lra)) as [Fq Bq].
  fold q in Fq, Bq.
  set (t := B n / B d) in *.
  assert (Ht9 : t <= bpow radix2 (-900)).
  { destruct (Rle_dec t (bpow radix2 (-900))) as [L | G]; [exact L | exfalso].
    pose proof (rndF_mono_bpow (-900) t ltac:(lia) ltac:(lra)) as H. rewrite <- Bq in H. lra. }
  destruct (odd_part_ok n Fn Pn) as [mn [en [Hon [Hno [Hmn [Hen Hbn]]]]]].
  destruct (odd_part_ok d Fd Pd) as [md [ed [Hod [Hdo [Hmd [Hed Hbd]]]]]].
  unfold atan2_tiny_phi. fold q. rewrite Hon, Hod. cbv zeta iota.
  destruct tiny_val as [_ _]. destruct minpos_val as [Fm Vm].
  destruct (atan2_cmp_is q atan2_min_positive Gt) eqn:Hc.
  - (* the quotient is a normal number *)
    apply (proj1 (cmp_val q atan2_min_positive Gt Fq Fm)) in Hc. rewrite Vm in Hc.
    apply Rcompare_Gt_inv in Hc.
    assert (Hnm : forall u, fmtF u -> 0 <= u -> t <> (u + succ radix2 fexp64 u) / 2).
    { intros u Fu U0 E. destruct (no_exact_mid_or_cond n d mn en md ed Fn Fd Pn Pd Hno Hmn Hbn Hdo Hmd Hbd u Fu U0 E)
        as [k [Hk [Emn [Een Et]]]].
      assert (Hlt : t <= bpow radix2 (-1022)).
      { assert (Et' : t = IZR (2 * k + 1) * bpow radix2 (-1075)) by exact Et. rewrite Et'. assert (E53 : IZR (2 * k + 1) <= bpow radix2 53) by (rewrite <- izr_pow2 by lia; apply IZR_le; lia).
        assert (Hp : bpow radix2 53 * bpow radix2 (-1075) = bpow radix2 (-1022)) by (rewrite <- bpow_plus; reflexivity).
        pose proof (bpow_gt_0 radix2 (-1075)). nra. }
      pose proof (rndF_le_bpow (-1022) t ltac:(lia) Hlt) as H. rewrite <- Bq in H. lra. }
    pose proof (phi_rounds (B n) (B d) mn en md ed Hno Hmn Hbn Hmd Hbd Pn Pd Ht9 Hnm) as R.
    split; [exact Fq | ]. rewrite Bq. symmetry. exact R.
  - assert (Hq1 : B q <= bpow radix2 (-1022)).
    { destruct (Rle_dec (B q) (bpow radix2 (-1022))) as [L | G]; [exact L | exfalso].
      assert (Hcc : atan2_cmp_is q atan2_min_positive Gt = true) by (apply (proj2 (cmp_val q atan2_min_positive Gt Fq Fm)); rewrite Vm; apply Rcompare_Gt; lra).
      rewrite Hc in Hcc. discriminate Hcc. }
    destruct ((mn mod md =? 0)%Z && (en - ed =? -1075)%Z)%bool eqn:Hcond.
    + (* the quotient is the midpoint of two subnormal numbers *)
      apply Bool.andb_true_iff in Hcond as [Hc1 Hc2]. apply Z.eqb_eq in Hc1. apply Z.eqb_eq in Hc2.
      assert (Hmd0 : (md <> 0)%Z) by lia.
      assert (Hdiv : mn = (md * (mn / md))%Z) by (apply Z.div_exact; [exact Hmd0 | exact Hc1]).
      set (sv := (mn / md)%Z) in *.
      assert (Hsodd : Z.odd sv = true).
      { rewrite Hdiv in Hno. rewrite Z.odd_mul in Hno. apply Bool.andb_true_iff in Hno as [_ H]. exact H. }
      assert (Hspos : (0 < sv)%Z) by nia.
      destruct (proj1 (Z.odd_spec sv) Hsodd) as [k0 Hk0].
      assert (Hk0r : ((sv - 1) / 2 = k0)%Z) by (rewrite Hk0; replace (2 * k0 + 1 - 1)%Z with (k0 * 2)%Z by ring; apply Z.div_mul; lia).
      rewrite Hk0r.
      assert (Hkr : (0 <= k0 < 2 ^ 52)%Z).
      { assert (Hs : (sv <= mn)%Z) by nia. assert (H52 : (2 ^ 53 = 2 * 2 ^ 52)%Z) by reflexivity. lia. }
      destruct (small_bits k0 Hkr) as [Fk Vk].
      split; [exact Fk | ]. rewrite Vk.
      set (uk := IZR k0 * bpow radix2 (-1074)).
      assert (Ht : t = uk + bpow radix2 (-1075)).
      { assert (Et : t = IZR sv * bpow radix2 (-1075)).
        { unfold t. rewrite Hbn, Hbd. rewrite Hdiv at 1. rewrite mult_IZR.
          replace en with (ed - 1075)%Z by lia. 
          assert (Hp : bpow radix2 (ed - 1075) = bpow radix2 ed * bpow radix2 (-1075)) by (rewrite <- bpow_plus; f_equal).
          rewrite Hp. assert (0 < IZR md) by (apply IZR_lt; lia). pose proof (bpow_gt_0 radix2 ed).
          field. split; lra. }
        rewrite Et, Hk0. unfold uk. rewrite plus_IZR, mult_IZR. simpl IZR.
        assert (E : bpow radix2 (-1074) = 2 * bpow radix2 (-1075)) by (replace (-1074)%Z with (-1075 + 1)%Z by reflexivity; rewrite bpow_plus; change (bpow radix2 1) with 2; ring).
        rewrite E. ring. }
      assert (Fuk : fmtF uk) by (unfold uk; rewrite <- Vk; exact (B_fmt (aw k0))).
      assert (Huk0 : 0 <= uk) by (unfold uk; apply Rmult_le_pos; [apply IZR_le; lia | apply bpow_ge_0]).
      assert (Huk1 : uk < bpow radix2 (-1021)).
      { unfold uk. assert (E : bpow radix2 (-1021) = bpow radix2 53 * bpow radix2 (-1074)) by (rewrite <- bpow_plus; reflexivity).
        rewrite E. apply Rmult_lt_compat_r; [apply bpow_gt_0 | ]. rewrite <- izr_pow2 by lia.
        apply IZR_lt. assert (H52 : (2 ^ 53 = 2 * 2 ^ 52)%Z) by reflexivity. lia. }
      assert (Hulp : ulp radix2 fexp64 uk = bpow radix2 (-1074)).
      { apply ulp_FLT_small; [exact _ | ]. rewrite Rabs_pos_eq by exact Huk0. replace (-1074 + 53)%Z with (-1021)%Z by reflexivity. exact Huk1. }
      assert (Hsucc : succ radix2 fexp64 uk = uk + bpow radix2 (-1074)) by (rewrite succ_eq_pos by exact Huk0; rewrite Hulp; reflexivity).
      assert (HE : bpow radix2 (-1074) = 2 * bpow radix2 (-1075)) by (replace (-1074)%Z with (-1075 + 1)%Z by reflexivity; rewrite bpow_plus; change (bpow radix2 1) with 2; ring).
      pose proof (bpow_gt_0 radix2 (-1075)) as P1075.
      assert (Hpl : t <= bpow radix2 (-1022)).
      { rewrite Ht. unfold uk. assert (E : bpow radix2 (-1022) = bpow radix2 52 * bpow radix2 (-1074)) by (rewrite <- bpow_plus; reflexivity).
        assert (H1 : IZR k0 + 1 <= bpow radix2 52) by (rewrite <- izr_pow2 by lia; replace (IZR k0 + 1) with (IZR (k0 + 1)) by (rewrite plus_IZR; reflexivity); apply IZR_le; lia).
        rewrite E. pose proof (bpow_gt_0 radix2 (-1074)). rewrite HE in *. nra. }
      pose proof (atan_lt_id t Pt) as Hlt.
      assert (Ht16 : t <= / 16) by (apply Rle_trans with (bpow radix2 (-900)); [exact Ht9 | apply Rle_trans with (bpow radix2 (-4)); [apply bpow_le; lia | bpow_num; interval with (i_prec 60)]]).
      pose proof (atan_small_pos t ltac:(split; lra)) as [A1 A2].
      assert (Hcube : t * t * t / 3 < bpow radix2 (-1075)).
      { assert (Htt : t * t <= bpow radix2 (-1022) * bpow radix2 (-1022)) by nra.
        assert (Hb : bpow radix2 (-1022) * bpow radix2 (-1022) * bpow radix2 (-1022) <= bpow radix2 (-3066)) by (rewrite <- !bpow_plus; apply bpow_le; lia).
        assert (Hb2 : bpow radix2 (-3066) < bpow radix2 (-1075)) by (apply bpow_lt; lia).
        pose proof (bpow_gt_0 radix2 (-1022)).
        assert (t * t * t <= bpow radix2 (-1022) * bpow radix2 (-1022) * bpow radix2 (-1022)) by (apply Rmult_le_compat; [nra | nra | exact Htt | exact Hpl]).
        lra. }
      assert (Hzu : uk <= atan t) by lra.
      symmetry. apply Rle_antisym.
      * apply (round_N_le_midp radix2 fexp64 ne uk (atan t) Fuk). rewrite Hsucc. lra.
      * apply round_ge_generic; [exact _ | exact _ | exact Fuk | exact Hzu].
    + assert (Hnm : forall u, fmtF u -> 0 <= u -> t <> (u + succ radix2 fexp64 u) / 2).
      { intros u Fu U0 E. destruct (no_exact_mid_or_cond n d mn en md ed Fn Fd Pn Pd Hno Hmn Hbn Hdo Hmd Hbd u Fu U0 E)
          as [k [Hk [Emn [Een Et]]]].
        assert (Hmod : (mn mod md = 0)%Z) by (rewrite Emn; apply Z.mod_mul; lia).
        assert (Hex : (en - ed = -1075)%Z) by lia.
        rewrite (proj2 (Z.eqb_eq _ _) Hmod), (proj2 (Z.eqb_eq _ _) Hex) in Hcond. discriminate Hcond. }
      pose proof (phi_rounds (B n) (B d) mn en md ed Hno Hmn Hbn Hmd Hbd Pn Pd Ht9 Hnm) as R.
      split; [exact Fq | ]. rewrite Bq. symmetry. exact R.
Qed.
