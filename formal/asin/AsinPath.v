(** asin's fast path end to end: the direct and complement branches return a
    double-word within [2^-62] of [asin x], relatively, and a normalized one;
    the complement's [delta] is within [2^-62] of [pi/2 - asin x]. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Mul IEEE64Eft Grid RoundingCore RoundingTest Encodings.
From Interval Require Import Tactic.
Require Import Ln1pLemmas AsinTables AsinKernel AsinSqrtStep AsinNormal AsinSeriesSmall AsinSegment
  AsinWithin AsinLip AsinApprox AsinSegments AsinFast AsinDouble.
Open Scope R_scope.

Lemma zero_val : B asin_zero = 0 /\ finite asin_zero.
Proof.
  assert (E : asin_zero = B754_zero 53 1024 false) by (vm_compute; reflexivity).
  rewrite E. split; reflexivity.
Qed.

(** A double-word whose high word is [zh], on the table path: the series
    below [2^-7], the table above. *)
Theorem fast_dw zh zl : finite zh -> finite zl ->
  bpow radix2 (-28) <= B zh -> B zh <= 0.7072 -> B zh = rndF (B zh + B zl) ->
  Rabs (B zl) <= bpow radix2 (-53) -> on_grid (-211) (B zl) ->
  exists h l, asin_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    Rabs (B h + B l - asin (B zh + B zl)) <= bpow radix2 (-63) * asin (B zh + B zl).
Proof.
  intros Fh Fl L U Dw Hl Hg.
  assert (Hz0 : 0 < B zh) by (apply Rlt_le_trans with (bpow radix2 (-28)); [apply bpow_gt_0 | exact L]).
  assert (P29 : bpow radix2 (-53) <= bpow radix2 (-28) / 2).
  { assert (bpow radix2 (-53) <= bpow radix2 (-29)) by (apply bpow_le; lia).
    assert (bpow radix2 (-29) = bpow radix2 (-28) / 2).
    { replace (-29)%Z with (-28 + -1)%Z by reflexivity. rewrite bpow_plus. change (bpow radix2 (-1)) with (/ 2). field. }
    lra. }
  assert (Hlh : Rabs (B zl) <= B zh / 2) by lra.
  pose proof (Rabs_le_inv _ _ Hl) as [Hla Hlb].
  assert (P53n : bpow radix2 (-53) <= / 9007199254740992) by (rewrite bp53; lra).
  assert (Hsum : 0 <= B zh + B zl <= 1).
  { assert (bpow radix2 (-53) <= bpow radix2 (-28) / 2) by exact P29. pose proof (bpow_gt_0 radix2 (-28)). lra. }
  pose proof (asin_nonneg _ Hsum) as An.
  destruct (Rle_dec (B zh) (bpow radix2 (-7))) as [Hs | Ht].
  - destruct (fast_series zh zl Fh Fl L Hs Dw Hlh) as [h [l [Hr [Fh' [Fl' [Nrm Err]]]]]].
    exists h, l. repeat split; try assumption.
    apply Rle_trans with (1 := Err). apply Rmult_le_compat_r; [exact An | apply bpow_le; lia].
  - assert (Hbig : / 128 < B zh).
    { assert (bpow radix2 (-7) = / 128) by (bpow_num; reflexivity). lra. }
    set (k := Znearest ne (B zh * 64)).
    pose proof (Znearest_half ne (B zh * 64)) as Hh. fold k in Hh. apply Rabs_le_inv in Hh as [Hh1 Hh2].
    assert (Hk1 : (1 <= k)%Z).
    { assert (0 < IZR k) by lra. apply lt_0_IZR in H. lia. }
    assert (Hk2 : (k <= 45)%Z).
    { assert (IZR k < 46) by lra. assert (IZR k < IZR 46) by (change (IZR 46) with 46; lra). apply lt_IZR in H0. lia. }
    destruct (fast_table k zh zl ltac:(lia) Fh Fl ltac:(lra) U eq_refl Hl Hg) as [h [l [Hr [Fh' [Fl' [Nrm Err]]]]]].
    exists h, l. repeat split; try assumption.
    replace (B zh + B zl) with (IZR k / 64 + (B zh - IZR k / 64 + B zl)) by ring. exact Err.
Qed.

(** An argument not above [SPLIT] is at most [0.7072]. *)
Lemma le_split x : finite x -> asin_le x asin_split = true -> B x <= 0.7072.
Proof.
  intros Fx H. destruct split_val as [V F].
  unfold asin_le, asin_cmp in H. rewrite (Bcompare_correct 53 1024 x asin_split Fx F), V in H.
  destruct (Rcompare_spec (B x) SPLIT_R) as [Hlt | Heq | Hgt]; try discriminate H.
  - unfold SPLIT_R in Hlt. rewrite p53 in Hlt. lra.
  - unfold SPLIT_R in Heq. rewrite p53 in Heq. lra.
Qed.

(** The direct branch: [asin x] for [x <= SPLIT]. *)
Theorem fast_direct x : finite x -> bpow radix2 (-28) <= B x -> asin_le x asin_split = true ->
  exists yh yl, asin_fast (asin_reduced x) = ((yh, yl), (yh, yl)) /\ finite yh /\ finite yl /\
    B yh = rndF (B yh + B yl) /\ Rabs (B yh + B yl - asin (B x)) <= bpow radix2 (-63) * asin (B x).
Proof.
  intros Fx L Hle. pose proof (le_split x Fx Hle) as U. destruct zero_val as [Z0 Fz].
  assert (Hred : asin_reduced x = (true, (x, asin_zero))) by (unfold asin_reduced; rewrite Hle; reflexivity).
  destruct (fast_dw x asin_zero Fx Fz L U ltac:(rewrite Z0, Rplus_0_r; symmetry; apply round_generic; [exact _ | apply B_fmt])
    ltac:(rewrite Z0, Rabs_R0; apply bpow_ge_0) ltac:(rewrite Z0; apply grid_0)) as [h [l [Hs [Fh [Fl [Nrm Err]]]]]].
  rewrite Z0, Rplus_0_r in Err.
  exists h, l. split; [ | repeat split; try assumption].
  unfold asin_fast. rewrite Hred. cbv iota. rewrite Hs. reflexivity.
Qed.

(** [|sl| <= 2^-52 |sh|] for a double-word number whose sum is in the normal range. *)
Lemma dw_low sh sl : bpow radix2 (-1022) <= Rabs (B sh + B sl) -> B sh = rndF (B sh + B sl) ->
  Rabs (B sl) <= bpow radix2 (-52) * Rabs (B sh).
Proof.
  intros Hn Dw. pose proof (rnd_rel_f _ Hn) as R. rewrite <- Dw in R.
  replace (B sh - (B sh + B sl)) with (- B sl) in R by ring. rewrite Rabs_Ropp in R.
  pose proof (Rabs_triang (B sh) (B sl)) as Tr.
  assert (P53 : bpow radix2 (-53) = / 9007199254740992) by exact bp53.
  assert (P52 : bpow radix2 (-52) = / 4503599627370496) by (bpow_num; reflexivity).
  rewrite P53 in R. rewrite P52. pose proof (Rabs_pos (B sl)). pose proof (Rabs_pos (B sh)). lra.
Qed.

Lemma fneg_val x : finite x -> finite (fneg x) /\ B (fneg x) = - B x.
Proof.
  intros Fx. split.
  - unfold fneg, b64_opp. now rewrite is_finite_Bopp.
  - apply B2R_Bopp.
Qed.

(** The double-word [pi/2] of the table. *)
Lemma half_pi_words :
  finite (aw (fst asin_half_pi)) /\ finite (aw (snd asin_half_pi)) /\
  B (aw (fst asin_half_pi)) = IZR 884279719003555 * bpow radix2 (-49) /\
  B (aw (snd asin_half_pi)) = IZR 4967757600021511 * bpow radix2 (-106).
Proof.
  unfold asin_half_pi. cbn [fst snd].
  destruct (word_ok_intro (0x3ff921fb54442d18)%Z false 7074237752028440%positive 52%nat (884279719003555)%Z 3%Z (-49)%Z
    eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c91a62633145c07)%Z false 4967757600021511%positive 106%nat (4967757600021511)%Z 0%Z (-106)%Z
    eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  repeat split; assumption.
Qed.

Lemma half_pi_close : Rabs (IZR 884279719003555 * bpow radix2 (-49) + IZR 4967757600021511 * bpow radix2 (-106) - PI / 2) <= / 500000000000000000000000000000000.
Proof. bpow_num. interval with (i_prec 300). Qed.

Lemma pi_bounds : 3.1415 < PI < 3.1416.
Proof. split; interval with (i_prec 60). Qed.

Lemma e103 : / 2 ^ 103 <= / 1000000000000000000000000000000.
Proof. interval with (i_prec 120). Qed.

(** The complement branch: [asin x = pi/2 - delta], [delta = 2 asin (sqrt ((1 - x)/2))]. *)
Theorem fast_complement x : finite x -> SPLIT_UP_R <= B x -> B x <= 1 - / 9007199254740992 ->
  exists yh yl dh dl, asin_fast (asin_reduced x) = ((yh, yl), (dh, dl)) /\
    finite yh /\ finite yl /\ finite dh /\ finite dl /\ B yh = rndF (B yh + B yl) /\
    0 < B dh /\ Rabs (B dl) <= bpow radix2 (-52) * B dh /\
    Rabs (B yh + B yl - asin (B x)) <= bpow radix2 (-62) * asin (B x) /\
    Rabs (B dh + B dl - (PI / 2 - asin (B x))) <= bpow radix2 (-62) * (PI / 2 - asin (B x)).
Proof.
  intros Fx L U.
  assert (Lh : / 2 <= B x) by (unfold SPLIT_UP_R in L; rewrite p53 in L; lra).
  destruct (reduced_complement x Fx L U) as [zh [zl [Hred [Fzh [Fzl [Hzr [Hzg Hzb]]]]]]].
  destruct (w_facts x L U) as [[W1 W2] [Ww W0]]. set (w := sqrt ((1 - B x) / 2)) in *.
  pose proof (Rle_trans _ _ _ Hzb (Rmult_le_compat_r w _ _ (Rlt_le _ _ W0) e103)) as Hzb'.
  set (z := B zh + B zl) in *.
  apply Rabs_le_inv in Hzb' as [Hz1 Hz2].
  assert (Hzlo : bpow radix2 (-28) <= z).
  { assert (bpow radix2 (-28) = / 268435456) by (bpow_num; reflexivity). lra. }
  assert (Hzhi : z <= 0.3828) by lra.
  assert (Hn : bpow radix2 (-1022) <= Rabs z).
  { rewrite Rabs_pos_eq by (pose proof (bpow_gt_0 radix2 (-28)); lra).
    apply Rle_trans with (bpow radix2 (-28)); [apply bpow_le; lia | exact Hzlo]. }
  pose proof (rnd_rel_f _ Hn) as R. rewrite <- Hzr in R.
  replace (B zh - z) with (- B zl) in R by (unfold z; ring). rewrite Rabs_Ropp in R.
  rewrite (Rabs_pos_eq z) in R by (pose proof (bpow_gt_0 radix2 (-28)); lra).
  assert (P53 : bpow radix2 (-53) = / 9007199254740992) by exact bp53.
  rewrite P53 in R. 
  assert (Hzl53 : Rabs (B zl) <= bpow radix2 (-53)) by (rewrite P53; lra).
  assert (Hz28 : bpow radix2 (-28) <= B zh).
  { rewrite Hzr. apply round_ge_generic; [exact _ | exact _ | apply fmt_bpow; lia | exact Hzlo]. }
  apply Rabs_le_inv in Hzl53 as [Hzl1 Hzl2].
  assert (Hzdef : z = B zh + B zl) by reflexivity.
  assert (Hzh07 : B zh <= 0.7072) by (rewrite P53 in Hzl2; lra).
  destruct (fast_dw zh zl Fzh Fzl Hz28 Hzh07 Hzr (Rabs_le _ _ (conj Hzl1 Hzl2)) Hzg) as [sh [sl [Hs [Fsh [Fsl [Nrm Err]]]]]].
  change (B zh + B zl) with z in Err.
  (* asin z against asin w *)
  assert (Hw0 : 0 < w) by exact W0.
  assert (Hzpos : 0 < z) by (pose proof (bpow_gt_0 radix2 (-28)); lra).
  assert (Hzw : Rabs (z - w) <= / 1000000000000000000000000000000 * w) by (apply Rabs_le; split; lra).
  pose proof (asin_close z w ltac:(lra) ltac:(lra) ltac:(lra) ltac:(lra)) as Cl.
  pose proof (asin_ge w ltac:(lra)) as Awl.
  pose proof (asin_lip 0 w ltac:(lra) ltac:(lra) ltac:(lra)) as Awu. rewrite asin_0 in Awu.
  pose proof (asin_ge z ltac:(lra)) as Azl.
  pose proof (asin_nonneg z ltac:(lra)) as Azn.
  set (A := asin w) in *. set (Az := asin z) in *.
  assert (HAz : Rabs (Az - A) <= 1.1 / 1000000000000000000000000000000 * A) by nra.
  assert (P63 : bpow radix2 (-63) = / 9223372036854775808) by (bpow_num; reflexivity).
  rewrite P63 in Err. pose proof Err as Err'. apply Rabs_le_inv in Err' as [Er1 Er2].
  apply Rabs_le_inv in HAz as [Hza Hzb2].
  set (sv := B sh + B sl) in *.
  assert (Hsv : Az * (1 - / 9223372036854775808) <= sv <= Az * (1 + / 9223372036854775808)) by (split; lra).
  assert (Hsvlo : bpow radix2 (-28) <= sv).
  { assert (bpow radix2 (-28) = / 268435456) by (bpow_num; reflexivity). nra. }
  assert (Hsvn : bpow radix2 (-1022) <= Rabs sv).
  { rewrite Rabs_pos_eq by (pose proof (bpow_gt_0 radix2 (-28)); lra).
    apply Rle_trans with (bpow radix2 (-28)); [apply bpow_le; lia | exact Hsvlo]. }
  pose proof (dw_low sh sl Hsvn Nrm) as Hsl.
  assert (Hshlo : bpow radix2 (-28) <= B sh).
  { rewrite Nrm. apply round_ge_generic; [exact _ | exact _ | apply fmt_bpow; lia | exact Hsvlo]. }
  rewrite (Rabs_pos_eq (B sh)) in Hsl by (pose proof (bpow_gt_0 radix2 (-28)); lra).
  assert (P52 : bpow radix2 (-52) = / 4503599627370496) by (bpow_num; reflexivity).
  rewrite P52 in Hsl. apply Rabs_le_inv in Hsl as [Hsl1 Hsl2].
  assert (Hsvdef : sv = B sh + B sl) by reflexivity.
  assert (Hshhi : B sh <= 0.5) by lra.
  assert (Hb900 : bpow radix2 (-900) <= B sh) by (apply Rle_trans with (bpow radix2 (-28)); [apply bpow_le; lia | exact Hshlo]).
  assert (Hb900' : B sh <= bpow radix2 900).
  { apply Rle_trans with 1; [lra | change 1 with (bpow radix2 0); apply bpow_le; lia]. }
  assert (Hslh : Rabs (B sl) <= B sh / 2) by (apply Rabs_le; split; lra).
  pose proof (mul_f64_two_exact sh sl Fsh Fsl Nrm Hb900 Hb900' Hslh) as M2.
  destruct (mul_f64_64 sh sl asin_two) as [dh dl] eqn:Emul. destruct M2 as [Fdh [Fdl [Bdh Bdl]]].
  (* the half-pi double-word *)
  destruct half_pi_words as [Fhi [Flo [Vhi Vlo]]].
  set (hi := aw (fst asin_half_pi)) in *. set (lo := aw (snd asin_half_pi)) in *.
  assert (Hhi2 : Rabs (B hi) <= 2) by (rewrite Vhi; bpow_num; rewrite Rabs_pos_eq by (interval with (i_prec 60)); interval with (i_prec 60)).
  assert (Hlo2 : Rabs (B lo) <= 2) by (rewrite Vlo; bpow_num; rewrite Rabs_pos_eq by (interval with (i_prec 60)); interval with (i_prec 60)).
  assert (H2big : forall v, Rabs v <= 2 -> Rabs v <= bpow radix2 1020).
  { intros v Hv. apply Rle_trans with 2; [exact Hv | apply Rle_trans with (bpow radix2 1); [change (bpow radix2 1) with 2; lra | apply bpow_le; lia]]. }
  pose proof (two_sum_ieee hi lo Fhi Flo (H2big _ Hhi2) (H2big _ Hlo2)) as TSH.
  destruct (two_sum64 hi lo) as [hh hl] eqn:Eth. destruct TSH as [Fhh [Fhl [Ehh Esh]]].
  assert (Hpi : Rabs (B hh + B hl - PI / 2) <= / 500000000000000000000000000000000).
  { rewrite Esh, Vhi, Vlo. exact half_pi_close. }
  pose proof pi_bounds as [Pi1 Pi2].
  apply Rabs_le_inv in Hpi as [Hp1 Hp2].
  assert (Hhhdw : B hh = rndF (B hh + B hl)) by (rewrite Esh; exact Ehh).
  assert (Hhhge : 1 <= B hh).
  { rewrite Ehh. apply round_ge_generic with (x := bpow radix2 0); [exact _ | exact _ | apply fmt_bpow; lia | ].
    change (bpow radix2 0) with 1. rewrite Vhi, Vlo. bpow_num. interval with (i_prec 60). }
  assert (Hhhn : bpow radix2 (-1022) <= Rabs (B hh + B hl)).
  { rewrite Rabs_pos_eq by lra. apply Rle_trans with 1; [change 1 with (bpow radix2 0); apply bpow_le; lia | lra]. }
  pose proof (dw_low hh hl Hhhn Hhhdw) as Hhl.
  rewrite (Rabs_pos_eq (B hh)) in Hhl by lra. rewrite P52 in Hhl. apply Rabs_le_inv in Hhl as [Hhl1 Hhl2].
  assert (Hhh2 : B hh <= 2) by lra.
  (* delta is a double-word number *)
  assert (Hddw : B dh = rndF (B dh + B dl)).
  { rewrite Bdh, Bdl. apply dw_double_norm; [exact Nrm | ].
    apply Rle_trans with (bpow radix2 (-28)); [apply bpow_le; lia | rewrite <- Hsvdef; exact Hsvlo]. }
  assert (Hdsum : B dh + B dl = 2 * sv) by (rewrite Bdh, Bdl; unfold sv; ring).
  assert (Hsv2 : 0 < sv) by (pose proof (bpow_gt_0 radix2 (-28)); lra).
  assert (Hsvhi : sv <= 0.42).
  { assert (Hzaa : Az <= A * (1 + 1.1 / 1000000000000000000000000000000)) by lra. nra. }
  assert (Hbig : forall v, Rabs v <= 2 -> Rabs v <= bpow radix2 1016).
  { intros v Hv. apply Rle_trans with 2; [exact Hv | apply Rle_trans with (bpow radix2 1); [change (bpow radix2 1) with 2; lra | apply bpow_le; lia]]. }
  assert (Hne : B hh + B hl - (B dh + B dl) <> 0) by (rewrite Hdsum; lra).
  assert (Rhh : Rabs (B hh) <= bpow radix2 1016) by (apply Hbig; rewrite Rabs_pos_eq by lra; lra).
  assert (Rhl : Rabs (B hl) <= bpow radix2 1016) by (apply Hbig; apply Rabs_le; split; lra).
  assert (Rdh : Rabs (B dh) <= bpow radix2 1016) by (apply Hbig; rewrite Bdh, Rabs_pos_eq by lra; lra).
  assert (Rdl : Rabs (B dl) <= bpow radix2 1016) by (apply Hbig; rewrite Bdl; apply Rabs_le; split; lra).
  pose proof (sub_ieee hh hl dh dl Fhh Fhl Hhhdw Fdh Fdl Hddw Rhh Rhl Rdh Rdl Hne) as SUB.
  destruct (sub64 hh hl dh dl) as [yh yl] eqn:Esub. destruct SUB as [Fyh [Fyl Serr]].
  (* the result is a double-word number *)
  destruct (fneg_val dh Fdh) as [Fndh Vndh]. destruct (fneg_val dl Fdl) as [Fndl Vndl].
  assert (Hlhh : bpow radix2 (-900) <= B hh) by (apply Rle_trans with 1; [change 1 with (bpow radix2 0); apply bpow_le; lia | exact Hhhge]).
  assert (Hlhh' : B hh <= bpow radix2 900) by (apply Rle_trans with 2; [exact Hhh2 | apply Rle_trans with (bpow radix2 1); [change (bpow radix2 1) with 2; lra | apply bpow_le; lia]]).
  pose proof (add64_normalized hh hl (fneg dh) (fneg dl) Fhh Fhl Fndh Fndl Hlhh Hlhh'
    ltac:(rewrite P52; apply Rabs_le; split; lra)
    ltac:(rewrite Vndl, Bdl, P52; apply Rabs_le; split; lra)
    ltac:(rewrite Vndh, Bdh, Rabs_Ropp, Rabs_pos_eq by lra; lra)) as NORM.
  pose proof Esub as Esub0. unfold sub64 in Esub. rewrite Esub in NORM. try cbv iota in NORM. destruct NORM as [_ [_ Nrmy]].
  (* the accuracy *)
  set (X := B hh + B hl - (B dh + B dl)) in *.
  assert (HXpos : 0 < X) by (unfold X; rewrite Hdsum; lra).
  assert (EA : 3 * bpow radix2 (- prec) ^ 2 / (1 - 4 * bpow radix2 (- prec)) <= / 1000000000000000000000000000000).
  { replace (- prec)%Z with (-53)%Z by reflexivity. bpow_num. interval with (i_prec 200). }
  assert (Habs : Rabs (B yh + B yl - X) <= / 1000000000000000000000000000000 * Rabs X).
  { apply Rle_trans with (3 * bpow radix2 (- prec) ^ 2 / (1 - 4 * bpow radix2 (- prec)) * Rabs X); [ | apply Rmult_le_compat_r; [apply Rabs_pos | exact EA]].
    replace (B yh + B yl - X) with (((B yh + B yl - X) / X) * X) by (field; lra).
    rewrite Rabs_mult. apply Rmult_le_compat_r; [apply Rabs_pos | exact Serr]. }
  rewrite (Rabs_pos_eq X) in Habs by lra. apply Rabs_le_inv in Habs as [Ha1 Ha2].
  assert (HAx : asin (B x) = PI / 2 - 2 * A).
  { pose proof (complement_identity (B x) ltac:(split; lra)) as CI. change (sqrt ((1 - B x) / 2)) with w in CI. exact CI. }
  assert (HsvA : Rabs (sv - A) <= 1.0001 / 9223372036854775808 * A) by (apply Rabs_le; split; lra).
  apply Rabs_le_inv in HsvA as [Hsa1 Hsa2].
  assert (HA418 : A <= 0.418) by lra.
  exists yh, yl, dh, dl. repeat split; try assumption.
  - unfold asin_fast. rewrite Hred. cbv iota. rewrite Hs. cbv iota. rewrite Emul. cbv iota. unfold hi, lo in Eth. rewrite Eth. cbv iota. rewrite Esub0. reflexivity.
  - pose proof (bpow_gt_0 radix2 (-28)). rewrite Bdh. lra.
  - rewrite Bdl, Bdh, P52. apply Rabs_le. split; lra.
  - assert (Hxdef : X = B hh + B hl - (B dh + B dl)) by reflexivity.
    assert (P62 : bpow radix2 (-62) = / 4611686018427387904) by (bpow_num; reflexivity).
    rewrite P62, HAx. apply Rabs_le. split; lra.
  - assert (Hxdef : X = B hh + B hl - (B dh + B dl)) by reflexivity.
    assert (P62 : bpow radix2 (-62) = / 4611686018427387904) by (bpow_num; reflexivity).
    rewrite P62, HAx. replace (PI / 2 - (PI / 2 - 2 * A)) with (2 * A) by ring. apply Rabs_le. split; lra.
Qed.