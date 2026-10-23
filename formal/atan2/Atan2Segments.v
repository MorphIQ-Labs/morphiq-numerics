(** Segment-by-segment facts of atan2's tables, written by
    generators/atan2_proofs.py; do not edit. For each segment k, the
    certificate formal/atan2/eval_<kk>.g applied over the table words of
    src/atan2/tables.rs, the numeric facts [SegOkRowA] states, and the
    segment's fast value against [atan]. *)
From Coq Require Import Reals ZArith Lia Lra Psatz List.
From Flocq Require Import Core.
From Gappa Require Import Gappa_library.
From Binary64 Require Import Binary64Add IEEE64 Grid.
From Interval Require Import Tactic.
Require Import Ln1pLemmas StageGappa AsinTables AsinKernel AsinSegment AsinWithin Atan2Tables Atan2Kernel Atan2Segment Atan2Approx.
Require atan2_eval_01.
Require atan2_eval_02.
Require atan2_eval_03.
Require atan2_eval_04.
Require atan2_eval_05.
Require atan2_eval_06.
Require atan2_eval_07.
Require atan2_eval_08.
Require atan2_eval_09.
Require atan2_eval_10.
Require atan2_eval_11.
Require atan2_eval_12.
Require atan2_eval_13.
Require atan2_eval_14.
Require atan2_eval_15.
Require atan2_eval_16.
Require atan2_eval_17.
Require atan2_eval_18.
Require atan2_eval_19.
Require atan2_eval_20.
Require atan2_eval_21.
Require atan2_eval_22.
Require atan2_eval_23.
Require atan2_eval_24.
Require atan2_eval_25.
Require atan2_eval_26.
Require atan2_eval_27.
Require atan2_eval_28.
Require atan2_eval_29.
Require atan2_eval_30.
Require atan2_eval_31.
Require atan2_eval_32.
Require atan2_eval_33.
Require atan2_eval_34.
Require atan2_eval_35.
Require atan2_eval_36.
Require atan2_eval_37.
Require atan2_eval_38.
Require atan2_eval_39.
Require atan2_eval_40.
Require atan2_eval_41.
Require atan2_eval_42.
Require atan2_eval_43.
Require atan2_eval_44.
Require atan2_eval_45.
Require atan2_eval_46.
Require atan2_eval_47.
Require atan2_eval_48.
Require atan2_eval_49.
Require atan2_eval_50.
Require atan2_eval_51.
Require atan2_eval_52.
Require atan2_eval_53.
Require atan2_eval_54.
Require atan2_eval_55.
Require atan2_eval_56.
Require atan2_eval_57.
Require atan2_eval_58.
Require atan2_eval_59.
Require atan2_eval_60.
Require atan2_eval_61.
Require atan2_eval_62.
Require atan2_eval_63.
Require atan2_eval_64.
Import ListNotations.
Open Scope R_scope.

(** The double-word addition's rounding is far below every budget here. *)
Lemma ea_dw_small : 0 <= 3 * bpow radix2 (- prec) ^ 2 / (1 - 4 * bpow radix2 (- prec)) <= / 1000000000000000000000000000000.
Proof.
  replace (- prec)%Z with (-53)%Z by reflexivity. bpow_num.
  split; [interval with (i_prec 120) | interval with (i_prec 160)].
Qed.

Lemma zero_word : finite (aw 0) /\ B (aw 0) = 0.
Proof. split; vm_compute; reflexivity. Qed.

Lemma evalcert_01 : EvalCert (IZR (281406274007041) * bpow radix2 (-48)) (IZR (-281406274007041) * bpow radix2 (-108)) (IZR (-281337588072453) * bpow radix2 (-54)) (IZR (-93687637131279) * bpow radix2 (-48)) (IZR (2249052912683959) * bpow radix2 (-57)) (IZR (3589700583778591) * bpow radix2 (-54)) (IZR (-2246674543185411) * bpow radix2 (-57)) (IZR (-638981608443631) * bpow radix2 (-52)) (IZR (4493728000047647) * bpow radix2 (-58)) (IZR (993762747007023) * bpow radix2 (-53)) (IZR (-3281081413173985) * bpow radix2 (-54)) (IZR 980 * bpow radix2 (-80)) (IZR 692 * bpow radix2 (-71)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 245 (-245) (-78)); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_01.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_01.l1 th_ tl_ dg).
Qed.

Lemma segok_01 : SegOkRowA [(0x3f8fff555bbb729b)%Z; (0xbc2220c39d4dff50)%Z; (0x3feffe001ffe0020)%Z; (0xbc2ffe001ffe0020)%Z; (0xbf8ffc005ff800a0)%Z; (0xbfd54d56953003c0)%Z; (0x3f8ff601bfc42edc)%Z; (0x3fc981a0984ad23e)%Z; (0xbf8fed5ab84a380c)%Z; (0xbfc22933fe507778)%Z; (0x3f8fee0b2a51f43e)%Z; (0x3fbc3e935c360178)%Z; (0xbfc75040983905c2)%Z] (IZR 980 * bpow radix2 (-80)).
Proof.
  unfold SegOkRowA. cbn [nth].
  destruct (word_ok_intro (0x3f8fff555bbb729b)%Z false 9006466354344603%positive 59%nat (9006466354344603)%Z 0%Z (-59)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc2220c39d4dff50)%Z true 5102574110637904%positive 113%nat (-318910881914869)%Z 4%Z (-109)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3feffe001ffe0020)%Z false 9005000768225312%positive 53%nat (281406274007041)%Z 5%Z (-48)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc2ffe001ffe0020)%Z true 9005000768225312%positive 113%nat (-281406274007041)%Z 5%Z (-108)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbf8ffc005ff800a0)%Z true 9002802818318496%positive 59%nat (-281337588072453)%Z 5%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbfd54d56953003c0)%Z true 5996008776401856%positive 54%nat (-93687637131279)%Z 6%Z (-48)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3f8ff601bfc42edc)%Z false 8996211650735836%positive 59%nat (2249052912683959)%Z 2%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3fc981a0984ad23e)%Z false 7179401167557182%positive 55%nat (3589700583778591)%Z 1%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbf8fed5ab84a380c)%Z true 8986698172741644%positive 59%nat (-2246674543185411)%Z 2%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0xbfc22933fe507778)%Z true 5111852867549048%positive 55%nat (-638981608443631)%Z 3%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3f8fee0b2a51f43e)%Z false 8987456000095294%positive 59%nat (4493728000047647)%Z 1%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3fbc3e935c360178)%Z false 7950101976056184%positive 56%nat (993762747007023)%Z 3%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xbfc75040983905c2)%Z true 6562162826347970%positive 55%nat (-3281081413173985)%Z 1%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_01 _ _).
  all: seg_numeric.
Qed.

Lemma row_01 : nth (Z.to_nat (1%Z - 1)) atan2_segments [] = [(0x3f8fff555bbb729b)%Z; (0xbc2220c39d4dff50)%Z; (0x3feffe001ffe0020)%Z; (0xbc2ffe001ffe0020)%Z; (0xbf8ffc005ff800a0)%Z; (0xbfd54d56953003c0)%Z; (0x3f8ff601bfc42edc)%Z; (0x3fc981a0984ad23e)%Z; (0xbf8fed5ab84a380c)%Z; (0xbfc22933fe507778)%Z; (0x3f8fee0b2a51f43e)%Z; (0x3fbc3e935c360178)%Z; (0xbfc75040983905c2)%Z].
Proof. reflexivity. Qed.

Lemma fast_01 zh zl : finite zh -> finite zl -> / 128 <= B zh -> B zh <= 1 ->
  Znearest ne (B zh * 64) = 1%Z -> Rabs (B zl) <= bpow radix2 (-53) -> on_grid (-211) (B zl) ->
  exists h l, atan2_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    Rabs (B h + B l - atan (IZR 1 / 64 + ((B zh - IZR 1 / 64) + B zl))) <= bpow radix2 (-63) * atan (IZR 1 / 64 + ((B zh - IZR 1 / 64) + B zl)).
Proof.
  intros Fz Fl L U Hn Hl Hg.
  pose proof (series_segment_a zh zl 1%Z (IZR 980 * bpow radix2 (-80)) ltac:(lia) Fz Fl L U Hn Hl Hg segok_01) as SS.
  cbv zeta in SS. rewrite row_01 in SS. cbn [nth] in SS.
  destruct SS as [h [l [Hs [Fh [Fl' [Nrm [Ht [e1 [ea [E1 [Eea Eq]]]]]]]]]]].
  exists h, l. split; [exact Hs | split; [exact Fh | split; [exact Fl' | split; [exact Nrm | ]]]].
  destruct (word_ok_intro (0x3f8fff555bbb729b)%Z false 9006466354344603%positive 59%nat (9006466354344603)%Z 0%Z (-59)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc2220c39d4dff50)%Z true 5102574110637904%positive 113%nat (-318910881914869)%Z 4%Z (-109)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3feffe001ffe0020)%Z false 9005000768225312%positive 53%nat (281406274007041)%Z 5%Z (-48)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc2ffe001ffe0020)%Z true 9005000768225312%positive 113%nat (-281406274007041)%Z 5%Z (-108)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbf8ffc005ff800a0)%Z true 9002802818318496%positive 59%nat (-281337588072453)%Z 5%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbfd54d56953003c0)%Z true 5996008776401856%positive 54%nat (-93687637131279)%Z 6%Z (-48)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3f8ff601bfc42edc)%Z false 8996211650735836%positive 59%nat (2249052912683959)%Z 2%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3fc981a0984ad23e)%Z false 7179401167557182%positive 55%nat (3589700583778591)%Z 1%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbf8fed5ab84a380c)%Z true 8986698172741644%positive 59%nat (-2246674543185411)%Z 2%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0xbfc22933fe507778)%Z true 5111852867549048%positive 55%nat (-638981608443631)%Z 3%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3f8fee0b2a51f43e)%Z false 8987456000095294%positive 59%nat (4493728000047647)%Z 1%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3fbc3e935c360178)%Z false 7950101976056184%positive 56%nat (993762747007023)%Z 3%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xbfc75040983905c2)%Z true 6562162826347970%positive 55%nat (-3281081413173985)%Z 1%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  unfold seg_poly in Eq.
  pose proof (approx_01 _ _ _ _ _ _ _ _ _ _ _ _ _ ((B zh - IZR 1 / 64) + B zl) V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 Ht) as AP.
  pose proof (amin_01 ((B zh - IZR 1 / 64) + B zl) Ht) as HAm.
  destruct ea_dw_small as [Ea0 Ea1].
  rewrite Eq.
  refine (fast_compose _ _ e1 ea (IZR 13343168 * bpow radix2 (-101)) (IZR 980 * bpow radix2 (-80)) _ (IZR 1048540 * bpow radix2 (-27)) _ AP E1 Eea HAm _ Ea0 _).
  - apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0].
  - bpow_num. replace (- prec)%Z with (-53)%Z by reflexivity. bpow_num. clear - Fz. interval with (i_prec 200).
Qed.

Lemma evalcert_02 : EvalCert (IZR (1124801467909119) * bpow radix2 (-50)) (IZR (1124801467909119) * bpow radix2 (-110)) (IZR (-561852050311677) * bpow radix2 (-54)) (IZR (-186553152314869) * bpow radix2 (-49)) (IZR (2240834699373475) * bpow radix2 (-56)) (IZR (7100685917721701) * bpow radix2 (-55)) (IZR (-2231365338848543) * bpow radix2 (-56)) (IZR (-1251814315611373) * bpow radix2 (-53)) (IZR (8860729811190767) * bpow radix2 (-58)) (IZR (237910379149741) * bpow radix2 (-51)) (IZR (6446163112088107) * bpow radix2 (-54)) (IZR 909 * bpow radix2 (-79)) (IZR 689 * bpow radix2 (-71)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 909 (-909) (-79)); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_02.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_02.l1 th_ tl_ dg).
Qed.

Lemma segok_02 : SegOkRowA [(0x3f9ffd55bba97625)%Z; (0xbc35ec431444912c)%Z; (0x3feff801ff801ff8)%Z; (0x3c2ff801ff801ff8)%Z; (0xbf9ff005fe009fd0)%Z; (0xbfd535694c03bea0)%Z; (0x3f9fd81bf106ae8c)%Z; (0x3fc93a0945c99465)%Z; (0xbf9fb5a8e98b747c)%Z; (0xbfc1ca12ee6d53b4)%Z; (0x3f9f7ac96cd8c3ef)%Z; (0x3fbb0c1a746735a0)%Z; (0x3fd6e6c04e75d22b)%Z] (IZR 909 * bpow radix2 (-79)).
Proof.
  unfold SegOkRowA. cbn [nth].
  destruct (word_ok_intro (0x3f9ffd55bba97625)%Z false 9004268940523045%positive 58%nat (9004268940523045)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc35ec431444912c)%Z true 6170747357925676%positive 112%nat (-1542686839481419)%Z 2%Z (-110)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3feff801ff801ff8)%Z false 8998411743272952%positive 53%nat (1124801467909119)%Z 3%Z (-50)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c2ff801ff801ff8)%Z false 8998411743272952%positive 113%nat (1124801467909119)%Z 3%Z (-110)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbf9ff005fe009fd0)%Z true 8989632804986832%positive 58%nat (-561852050311677)%Z 4%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbfd535694c03bea0)%Z true 5969700874075808%positive 54%nat (-186553152314869)%Z 5%Z (-49)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3f9fd81bf106ae8c)%Z false 8963338797493900%positive 58%nat (2240834699373475)%Z 2%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3fc93a0945c99465)%Z false 7100685917721701%positive 55%nat (7100685917721701)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbf9fb5a8e98b747c)%Z true 8925461355394172%positive 58%nat (-2231365338848543)%Z 2%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0xbfc1ca12ee6d53b4)%Z true 5007257262445492%positive 55%nat (-1251814315611373)%Z 2%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3f9f7ac96cd8c3ef)%Z false 8860729811190767%positive 58%nat (8860729811190767)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3fbb0c1a746735a0)%Z false 7613132132791712%positive 56%nat (237910379149741)%Z 5%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x3fd6e6c04e75d22b)%Z false 6446163112088107%positive 54%nat (6446163112088107)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_02 _ _).
  all: seg_numeric.
Qed.

Lemma row_02 : nth (Z.to_nat (2%Z - 1)) atan2_segments [] = [(0x3f9ffd55bba97625)%Z; (0xbc35ec431444912c)%Z; (0x3feff801ff801ff8)%Z; (0x3c2ff801ff801ff8)%Z; (0xbf9ff005fe009fd0)%Z; (0xbfd535694c03bea0)%Z; (0x3f9fd81bf106ae8c)%Z; (0x3fc93a0945c99465)%Z; (0xbf9fb5a8e98b747c)%Z; (0xbfc1ca12ee6d53b4)%Z; (0x3f9f7ac96cd8c3ef)%Z; (0x3fbb0c1a746735a0)%Z; (0x3fd6e6c04e75d22b)%Z].
Proof. reflexivity. Qed.

Lemma fast_02 zh zl : finite zh -> finite zl -> / 128 <= B zh -> B zh <= 1 ->
  Znearest ne (B zh * 64) = 2%Z -> Rabs (B zl) <= bpow radix2 (-53) -> on_grid (-211) (B zl) ->
  exists h l, atan2_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    Rabs (B h + B l - atan (IZR 2 / 64 + ((B zh - IZR 2 / 64) + B zl))) <= bpow radix2 (-63) * atan (IZR 2 / 64 + ((B zh - IZR 2 / 64) + B zl)).
Proof.
  intros Fz Fl L U Hn Hl Hg.
  pose proof (series_segment_a zh zl 2%Z (IZR 909 * bpow radix2 (-79)) ltac:(lia) Fz Fl L U Hn Hl Hg segok_02) as SS.
  cbv zeta in SS. rewrite row_02 in SS. cbn [nth] in SS.
  destruct SS as [h [l [Hs [Fh [Fl' [Nrm [Ht [e1 [ea [E1 [Eea Eq]]]]]]]]]]].
  exists h, l. split; [exact Hs | split; [exact Fh | split; [exact Fl' | split; [exact Nrm | ]]]].
  destruct (word_ok_intro (0x3f9ffd55bba97625)%Z false 9004268940523045%positive 58%nat (9004268940523045)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc35ec431444912c)%Z true 6170747357925676%positive 112%nat (-1542686839481419)%Z 2%Z (-110)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3feff801ff801ff8)%Z false 8998411743272952%positive 53%nat (1124801467909119)%Z 3%Z (-50)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c2ff801ff801ff8)%Z false 8998411743272952%positive 113%nat (1124801467909119)%Z 3%Z (-110)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbf9ff005fe009fd0)%Z true 8989632804986832%positive 58%nat (-561852050311677)%Z 4%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbfd535694c03bea0)%Z true 5969700874075808%positive 54%nat (-186553152314869)%Z 5%Z (-49)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3f9fd81bf106ae8c)%Z false 8963338797493900%positive 58%nat (2240834699373475)%Z 2%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3fc93a0945c99465)%Z false 7100685917721701%positive 55%nat (7100685917721701)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbf9fb5a8e98b747c)%Z true 8925461355394172%positive 58%nat (-2231365338848543)%Z 2%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0xbfc1ca12ee6d53b4)%Z true 5007257262445492%positive 55%nat (-1251814315611373)%Z 2%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3f9f7ac96cd8c3ef)%Z false 8860729811190767%positive 58%nat (8860729811190767)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3fbb0c1a746735a0)%Z false 7613132132791712%positive 56%nat (237910379149741)%Z 5%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x3fd6e6c04e75d22b)%Z false 6446163112088107%positive 54%nat (6446163112088107)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  unfold seg_poly in Eq.
  pose proof (approx_02 _ _ _ _ _ _ _ _ _ _ _ _ _ ((B zh - IZR 2 / 64) + B zl) V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 Ht) as AP.
  pose proof (amin_02 ((B zh - IZR 2 / 64) + B zl) Ht) as HAm.
  destruct ea_dw_small as [Ea0 Ea1].
  rewrite Eq.
  refine (fast_compose _ _ e1 ea (IZR 14982287 * bpow radix2 (-100)) (IZR 909 * bpow radix2 (-79)) _ (IZR 786283 * bpow radix2 (-25)) _ AP E1 Eea HAm _ Ea0 _).
  - apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0].
  - bpow_num. replace (- prec)%Z with (-53)%Z by reflexivity. bpow_num. clear - Fz. interval with (i_prec 200).
Qed.

Lemma evalcert_03 : EvalCert (IZR (2246862859160725) * bpow radix2 (-51)) (IZR (-5564496299640233) * bpow radix2 (-107)) (IZR (-6725810185960289) * bpow radix2 (-57)) (IZR (-5926067754050057) * bpow radix2 (-54)) (IZR (6681636873532033) * bpow radix2 (-57)) (IZR (3485342084430069) * bpow radix2 (-54)) (IZR (-827277083440457) * bpow radix2 (-54)) (IZR (-2417741191248767) * bpow radix2 (-54)) (IZR (6432679964552911) * bpow radix2 (-57)) (IZR (7274553898129947) * bpow radix2 (-56)) (IZR (1456085792123487) * bpow radix2 (-48)) (IZR 663 * bpow radix2 (-78)) (IZR 685 * bpow radix2 (-71)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 663 (-663) (-78)); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_03.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_03.l1 th_ tl_ dg).
Qed.

Lemma segok_03 : SegOkRowA [(0x3fa7fb818430da2a)%Z; (0xbc086ef8f794f105)%Z; (0x3fefee0a1a513254)%Z; (0xbc83c4e1414b45a9)%Z; (0xbfa7e516b6f5fb61)%Z; (0xbfd50dba2b652209)%Z; (0x3fa7bce9d05d7281)%Z; (0x3fc8c3cce1b9f1ea)%Z; (0xbfa7833ba583aa48)%Z; (0xbfc12dd879b9f6fe)%Z; (0x3fa6da7d043daecf)%Z; (0x3fb9d82b10ff5a1b)%Z; (0x4014b135919ba97c)%Z] (IZR 663 * bpow radix2 (-78)).
Proof.
  unfold SegOkRowA. cbn [nth].
  destruct (word_ok_intro (0x3fa7fb818430da2a)%Z false 6750458151492138%positive 57%nat (3375229075746069)%Z 1%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc086ef8f794f105)%Z true 6877415025733893%positive 115%nat (-6877415025733893)%Z 0%Z (-115)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fefee0a1a513254)%Z false 8987451436642900%positive 53%nat (2246862859160725)%Z 2%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc83c4e1414b45a9)%Z true 5564496299640233%positive 107%nat (-5564496299640233)%Z 0%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfa7e516b6f5fb61)%Z true 6725810185960289%positive 57%nat (-6725810185960289)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbfd50dba2b652209)%Z true 5926067754050057%positive 54%nat (-5926067754050057)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fa7bce9d05d7281)%Z false 6681636873532033%positive 57%nat (6681636873532033)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3fc8c3cce1b9f1ea)%Z false 6970684168860138%positive 55%nat (3485342084430069)%Z 1%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbfa7833ba583aa48)%Z true 6618216667523656%positive 57%nat (-827277083440457)%Z 3%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0xbfc12dd879b9f6fe)%Z true 4835482382497534%positive 55%nat (-2417741191248767)%Z 1%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3fa6da7d043daecf)%Z false 6432679964552911%positive 57%nat (6432679964552911)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3fb9d82b10ff5a1b)%Z false 7274553898129947%positive 56%nat (7274553898129947)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x4014b135919ba97c)%Z false 5824343168493948%positive 50%nat (1456085792123487)%Z 2%Z (-48)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_03 _ _).
  all: seg_numeric.
Qed.

Lemma row_03 : nth (Z.to_nat (3%Z - 1)) atan2_segments [] = [(0x3fa7fb818430da2a)%Z; (0xbc086ef8f794f105)%Z; (0x3fefee0a1a513254)%Z; (0xbc83c4e1414b45a9)%Z; (0xbfa7e516b6f5fb61)%Z; (0xbfd50dba2b652209)%Z; (0x3fa7bce9d05d7281)%Z; (0x3fc8c3cce1b9f1ea)%Z; (0xbfa7833ba583aa48)%Z; (0xbfc12dd879b9f6fe)%Z; (0x3fa6da7d043daecf)%Z; (0x3fb9d82b10ff5a1b)%Z; (0x4014b135919ba97c)%Z].
Proof. reflexivity. Qed.

Lemma fast_03 zh zl : finite zh -> finite zl -> / 128 <= B zh -> B zh <= 1 ->
  Znearest ne (B zh * 64) = 3%Z -> Rabs (B zl) <= bpow radix2 (-53) -> on_grid (-211) (B zl) ->
  exists h l, atan2_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    Rabs (B h + B l - atan (IZR 3 / 64 + ((B zh - IZR 3 / 64) + B zl))) <= bpow radix2 (-63) * atan (IZR 3 / 64 + ((B zh - IZR 3 / 64) + B zl)).
Proof.
  intros Fz Fl L U Hn Hl Hg.
  pose proof (series_segment_a zh zl 3%Z (IZR 663 * bpow radix2 (-78)) ltac:(lia) Fz Fl L U Hn Hl Hg segok_03) as SS.
  cbv zeta in SS. rewrite row_03 in SS. cbn [nth] in SS.
  destruct SS as [h [l [Hs [Fh [Fl' [Nrm [Ht [e1 [ea [E1 [Eea Eq]]]]]]]]]]].
  exists h, l. split; [exact Hs | split; [exact Fh | split; [exact Fl' | split; [exact Nrm | ]]]].
  destruct (word_ok_intro (0x3fa7fb818430da2a)%Z false 6750458151492138%positive 57%nat (3375229075746069)%Z 1%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc086ef8f794f105)%Z true 6877415025733893%positive 115%nat (-6877415025733893)%Z 0%Z (-115)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fefee0a1a513254)%Z false 8987451436642900%positive 53%nat (2246862859160725)%Z 2%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc83c4e1414b45a9)%Z true 5564496299640233%positive 107%nat (-5564496299640233)%Z 0%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfa7e516b6f5fb61)%Z true 6725810185960289%positive 57%nat (-6725810185960289)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbfd50dba2b652209)%Z true 5926067754050057%positive 54%nat (-5926067754050057)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fa7bce9d05d7281)%Z false 6681636873532033%positive 57%nat (6681636873532033)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3fc8c3cce1b9f1ea)%Z false 6970684168860138%positive 55%nat (3485342084430069)%Z 1%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbfa7833ba583aa48)%Z true 6618216667523656%positive 57%nat (-827277083440457)%Z 3%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0xbfc12dd879b9f6fe)%Z true 4835482382497534%positive 55%nat (-2417741191248767)%Z 1%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3fa6da7d043daecf)%Z false 6432679964552911%positive 57%nat (6432679964552911)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3fb9d82b10ff5a1b)%Z false 7274553898129947%positive 56%nat (7274553898129947)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x4014b135919ba97c)%Z false 5824343168493948%positive 50%nat (1456085792123487)%Z 2%Z (-48)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  unfold seg_poly in Eq.
  pose proof (approx_03 _ _ _ _ _ _ _ _ _ _ _ _ _ ((B zh - IZR 3 / 64) + B zl) V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 Ht) as AP.
  pose proof (amin_03 ((B zh - IZR 3 / 64) + B zl) Ht) as HAm.
  destruct ea_dw_small as [Ea0 Ea1].
  rewrite Eq.
  refine (fast_compose _ _ e1 ea (IZR 12312434 * bpow radix2 (-96)) (IZR 663 * bpow radix2 (-78)) _ (IZR 655024 * bpow radix2 (-24)) _ AP E1 Eea HAm _ Ea0 _).
  - apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0].
  - bpow_num. replace (- prec)%Z with (-53)%Z by reflexivity. bpow_num. clear - Fz. interval with (i_prec 200).
Qed.

Lemma evalcert_04 : EvalCert (IZR (280379743338241) * bpow radix2 (-48)) (IZR (-280379743338241) * bpow radix2 (-104)) (IZR (-8937240690376927) * bpow radix2 (-57)) (IZR (-5865426445305739) * bpow radix2 (-54)) (IZR (8833185548119467) * bpow radix2 (-57)) (IZR (424447134355683) * bpow radix2 (-51)) (IZR (-4342256994236001) * bpow radix2 (-56)) (IZR (-71878620170311) * bpow radix2 (-49)) (IZR (8491581784845575) * bpow radix2 (-57)) (IZR (3310770793864807) * bpow radix2 (-55)) (IZR (5496213676697) * bpow radix2 (-50)) (IZR 869 * bpow radix2 (-78)) (IZR 678 * bpow radix2 (-71)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 869 (-869) (-78)); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_04.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_04.l1 th_ tl_ dg).
Qed.

Lemma segok_04 : SegOkRowA [(0x3faff55bb72cfdea)%Z; (0xbc3c934d86d23f1d)%Z; (0x3fefe01fe01fe020)%Z; (0xbc6fe01fe01fe020)%Z; (0xbfafc05f809f40df)%Z; (0xbfd4d69303ba878b)%Z; (0x3faf61bc46d4adab)%Z; (0x3fc82084cab50e30)%Z; (0xbfaeda84fb546cc2)%Z; (0xbfc057e2e7d211c0)%Z; (0x3fae2b0c73dded07)%Z; (0x3fb78641ca33bcce)%Z; (0x3f73febf748a6400)%Z] (IZR 869 * bpow radix2 (-78)).
Proof.
  unfold SegOkRowA. cbn [nth].
  destruct (word_ok_intro (0x3faff55bb72cfdea)%Z false 8995498542038506%positive 57%nat (4497749271019253)%Z 1%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc3c934d86d23f1d)%Z true 8043260531588893%positive 112%nat (-8043260531588893)%Z 0%Z (-112)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fefe01fe01fe020)%Z false 8972151786823712%positive 53%nat (280379743338241)%Z 5%Z (-48)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc6fe01fe01fe020)%Z true 8972151786823712%positive 109%nat (-280379743338241)%Z 5%Z (-104)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfafc05f809f40df)%Z true 8937240690376927%positive 57%nat (-8937240690376927)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbfd4d69303ba878b)%Z true 5865426445305739%positive 54%nat (-5865426445305739)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3faf61bc46d4adab)%Z false 8833185548119467%positive 57%nat (8833185548119467)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3fc82084cab50e30)%Z false 6791154149690928%positive 55%nat (424447134355683)%Z 4%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbfaeda84fb546cc2)%Z true 8684513988472002%positive 57%nat (-4342256994236001)%Z 1%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0xbfc057e2e7d211c0)%Z true 4600231690899904%positive 55%nat (-71878620170311)%Z 6%Z (-49)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3fae2b0c73dded07)%Z false 8491581784845575%positive 57%nat (8491581784845575)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3fb78641ca33bcce)%Z false 6621541587729614%positive 56%nat (3310770793864807)%Z 1%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x3f73febf748a6400)%Z false 5628122804937728%positive 60%nat (5496213676697)%Z 10%Z (-50)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_04 _ _).
  all: seg_numeric.
Qed.

Lemma row_04 : nth (Z.to_nat (4%Z - 1)) atan2_segments [] = [(0x3faff55bb72cfdea)%Z; (0xbc3c934d86d23f1d)%Z; (0x3fefe01fe01fe020)%Z; (0xbc6fe01fe01fe020)%Z; (0xbfafc05f809f40df)%Z; (0xbfd4d69303ba878b)%Z; (0x3faf61bc46d4adab)%Z; (0x3fc82084cab50e30)%Z; (0xbfaeda84fb546cc2)%Z; (0xbfc057e2e7d211c0)%Z; (0x3fae2b0c73dded07)%Z; (0x3fb78641ca33bcce)%Z; (0x3f73febf748a6400)%Z].
Proof. reflexivity. Qed.

Lemma fast_04 zh zl : finite zh -> finite zl -> / 128 <= B zh -> B zh <= 1 ->
  Znearest ne (B zh * 64) = 4%Z -> Rabs (B zl) <= bpow radix2 (-53) -> on_grid (-211) (B zl) ->
  exists h l, atan2_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    Rabs (B h + B l - atan (IZR 4 / 64 + ((B zh - IZR 4 / 64) + B zl))) <= bpow radix2 (-63) * atan (IZR 4 / 64 + ((B zh - IZR 4 / 64) + B zl)).
Proof.
  intros Fz Fl L U Hn Hl Hg.
  pose proof (series_segment_a zh zl 4%Z (IZR 869 * bpow radix2 (-78)) ltac:(lia) Fz Fl L U Hn Hl Hg segok_04) as SS.
  cbv zeta in SS. rewrite row_04 in SS. cbn [nth] in SS.
  destruct SS as [h [l [Hs [Fh [Fl' [Nrm [Ht [e1 [ea [E1 [Eea Eq]]]]]]]]]]].
  exists h, l. split; [exact Hs | split; [exact Fh | split; [exact Fl' | split; [exact Nrm | ]]]].
  destruct (word_ok_intro (0x3faff55bb72cfdea)%Z false 8995498542038506%positive 57%nat (4497749271019253)%Z 1%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc3c934d86d23f1d)%Z true 8043260531588893%positive 112%nat (-8043260531588893)%Z 0%Z (-112)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fefe01fe01fe020)%Z false 8972151786823712%positive 53%nat (280379743338241)%Z 5%Z (-48)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc6fe01fe01fe020)%Z true 8972151786823712%positive 109%nat (-280379743338241)%Z 5%Z (-104)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfafc05f809f40df)%Z true 8937240690376927%positive 57%nat (-8937240690376927)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbfd4d69303ba878b)%Z true 5865426445305739%positive 54%nat (-5865426445305739)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3faf61bc46d4adab)%Z false 8833185548119467%positive 57%nat (8833185548119467)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3fc82084cab50e30)%Z false 6791154149690928%positive 55%nat (424447134355683)%Z 4%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbfaeda84fb546cc2)%Z true 8684513988472002%positive 57%nat (-4342256994236001)%Z 1%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0xbfc057e2e7d211c0)%Z true 4600231690899904%positive 55%nat (-71878620170311)%Z 6%Z (-49)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3fae2b0c73dded07)%Z false 8491581784845575%positive 57%nat (8491581784845575)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3fb78641ca33bcce)%Z false 6621541587729614%positive 56%nat (3310770793864807)%Z 1%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x3f73febf748a6400)%Z false 5628122804937728%positive 60%nat (5496213676697)%Z 10%Z (-50)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  unfold seg_poly in Eq.
  pose proof (approx_04 _ _ _ _ _ _ _ _ _ _ _ _ _ ((B zh - IZR 4 / 64) + B zl) V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 Ht) as AP.
  pose proof (amin_04 ((B zh - IZR 4 / 64) + B zl) Ht) as HAm.
  destruct ea_dw_small as [Ea0 Ea1].
  rewrite Eq.
  refine (fast_compose _ _ e1 ea (IZR 13505914 * bpow radix2 (-102)) (IZR 869 * bpow radix2 (-78)) _ (IZR 916588 * bpow radix2 (-24)) _ AP E1 Eea HAm _ Ea0 _).
  - apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0].
  - bpow_num. replace (- prec)%Z with (-53)%Z by reflexivity. bpow_num. clear - Fz. interval with (i_prec 200).
Qed.

Lemma evalcert_05 : EvalCert (IZR (8952557182096361) * bpow radix2 (-53)) (IZR (-3925486498790299) * bpow radix2 (-108)) (IZR (-5561404121855541) * bpow radix2 (-56)) (IZR (-5788214763143219) * bpow radix2 (-54)) (IZR (5460598880592529) * bpow radix2 (-56)) (IZR (102570370853755) * bpow radix2 (-49)) (IZR (-5317452106799999) * bpow radix2 (-56)) (IZR (-2153283642573957) * bpow radix2 (-54)) (IZR (5173935332094699) * bpow radix2 (-56)) (IZR (744739081449859) * bpow radix2 (-53)) (IZR (-4583221480556721) * bpow radix2 (-50)) (IZR 536 * bpow radix2 (-77)) (IZR 670 * bpow radix2 (-71)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 67 (-67) (-74)); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_05.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_05.l1 th_ tl_ dg).
Qed.

Lemma segok_05 : SegOkRowA [(0x3fb3f59f0e7c559d)%Z; (0x3c5ac4ce285df847)%Z; (0x3fefce4da6ab93e9)%Z; (0xbc6be46b18a97736)%Z; (0xbfb3c2114d22b635)%Z; (0xbfd49059c4d74033)%Z; (0x3fb36662c089e291)%Z; (0x3fc75261a13adec0)%Z; (0xbfb2e431cbef9b7f)%Z; (0xbfbe9999aa771214)%Z; (0x3fb261aab18f72eb)%Z; (0x3fb52ab0a3338c18)%Z; (0xc010486a684688b1)%Z] (IZR 536 * bpow radix2 (-77)).
Proof.
  unfold SegOkRowA. cbn [nth].
  destruct (word_ok_intro (0x3fb3f59f0e7c559d)%Z false 5618088049137053%positive 56%nat (5618088049137053)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c5ac4ce285df847)%Z false 7534739114031175%positive 110%nat (7534739114031175)%Z 0%Z (-110)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fefce4da6ab93e9)%Z false 8952557182096361%positive 53%nat (8952557182096361)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc6be46b18a97736)%Z true 7850972997580598%positive 109%nat (-3925486498790299)%Z 1%Z (-108)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfb3c2114d22b635)%Z true 5561404121855541%positive 56%nat (-5561404121855541)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbfd49059c4d74033)%Z true 5788214763143219%positive 54%nat (-5788214763143219)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fb36662c089e291)%Z false 5460598880592529%positive 56%nat (5460598880592529)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3fc75261a13adec0)%Z false 6564503734640320%positive 55%nat (102570370853755)%Z 6%Z (-49)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbfb2e431cbef9b7f)%Z true 5317452106799999%positive 56%nat (-5317452106799999)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0xbfbe9999aa771214)%Z true 8613134570295828%positive 56%nat (-2153283642573957)%Z 2%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3fb261aab18f72eb)%Z false 5173935332094699%positive 56%nat (5173935332094699)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3fb52ab0a3338c18)%Z false 5957912651598872%positive 56%nat (744739081449859)%Z 3%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc010486a684688b1)%Z true 4583221480556721%positive 50%nat (-4583221480556721)%Z 0%Z (-50)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_05 _ _).
  all: seg_numeric.
Qed.

Lemma row_05 : nth (Z.to_nat (5%Z - 1)) atan2_segments [] = [(0x3fb3f59f0e7c559d)%Z; (0x3c5ac4ce285df847)%Z; (0x3fefce4da6ab93e9)%Z; (0xbc6be46b18a97736)%Z; (0xbfb3c2114d22b635)%Z; (0xbfd49059c4d74033)%Z; (0x3fb36662c089e291)%Z; (0x3fc75261a13adec0)%Z; (0xbfb2e431cbef9b7f)%Z; (0xbfbe9999aa771214)%Z; (0x3fb261aab18f72eb)%Z; (0x3fb52ab0a3338c18)%Z; (0xc010486a684688b1)%Z].
Proof. reflexivity. Qed.

Lemma fast_05 zh zl : finite zh -> finite zl -> / 128 <= B zh -> B zh <= 1 ->
  Znearest ne (B zh * 64) = 5%Z -> Rabs (B zl) <= bpow radix2 (-53) -> on_grid (-211) (B zl) ->
  exists h l, atan2_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    Rabs (B h + B l - atan (IZR 5 / 64 + ((B zh - IZR 5 / 64) + B zl))) <= bpow radix2 (-63) * atan (IZR 5 / 64 + ((B zh - IZR 5 / 64) + B zl)).
Proof.
  intros Fz Fl L U Hn Hl Hg.
  pose proof (series_segment_a zh zl 5%Z (IZR 536 * bpow radix2 (-77)) ltac:(lia) Fz Fl L U Hn Hl Hg segok_05) as SS.
  cbv zeta in SS. rewrite row_05 in SS. cbn [nth] in SS.
  destruct SS as [h [l [Hs [Fh [Fl' [Nrm [Ht [e1 [ea [E1 [Eea Eq]]]]]]]]]]].
  exists h, l. split; [exact Hs | split; [exact Fh | split; [exact Fl' | split; [exact Nrm | ]]]].
  destruct (word_ok_intro (0x3fb3f59f0e7c559d)%Z false 5618088049137053%positive 56%nat (5618088049137053)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c5ac4ce285df847)%Z false 7534739114031175%positive 110%nat (7534739114031175)%Z 0%Z (-110)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fefce4da6ab93e9)%Z false 8952557182096361%positive 53%nat (8952557182096361)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc6be46b18a97736)%Z true 7850972997580598%positive 109%nat (-3925486498790299)%Z 1%Z (-108)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfb3c2114d22b635)%Z true 5561404121855541%positive 56%nat (-5561404121855541)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbfd49059c4d74033)%Z true 5788214763143219%positive 54%nat (-5788214763143219)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fb36662c089e291)%Z false 5460598880592529%positive 56%nat (5460598880592529)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3fc75261a13adec0)%Z false 6564503734640320%positive 55%nat (102570370853755)%Z 6%Z (-49)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbfb2e431cbef9b7f)%Z true 5317452106799999%positive 56%nat (-5317452106799999)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0xbfbe9999aa771214)%Z true 8613134570295828%positive 56%nat (-2153283642573957)%Z 2%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3fb261aab18f72eb)%Z false 5173935332094699%positive 56%nat (5173935332094699)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3fb52ab0a3338c18)%Z false 5957912651598872%positive 56%nat (744739081449859)%Z 3%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc010486a684688b1)%Z true 4583221480556721%positive 50%nat (-4583221480556721)%Z 0%Z (-50)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  unfold seg_poly in Eq.
  pose proof (approx_05 _ _ _ _ _ _ _ _ _ _ _ _ _ ((B zh - IZR 5 / 64) + B zl) V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 Ht) as AP.
  pose proof (amin_05 ((B zh - IZR 5 / 64) + B zl) Ht) as HAm.
  destruct ea_dw_small as [Ea0 Ea1].
  rewrite Eq.
  refine (fast_compose _ _ e1 ea (IZR 9444130 * bpow radix2 (-96)) (IZR 536 * bpow radix2 (-77)) _ (IZR 588853 * bpow radix2 (-23)) _ AP E1 Eea HAm _ Ea0 _).
  - apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0].
  - bpow_num. replace (- prec)%Z with (-53)%Z by reflexivity. bpow_num. clear - Fz. interval with (i_prec 200).
Qed.

Lemma evalcert_06 : EvalCert (IZR (2232181035056819) * bpow radix2 (-51)) (IZR (-5231674300914419) * bpow radix2 (-107)) (IZR (-6638199554399369) * bpow radix2 (-56)) (IZR (-5694985441098135) * bpow radix2 (-54)) (IZR (6465701632158165) * bpow radix2 (-56)) (IZR (6293738842806671) * bpow radix2 (-55)) (IZR (-1555643992597111) * bpow radix2 (-54)) (IZR (-7921374778086837) * bpow radix2 (-56)) (IZR (1508067532765085) * bpow radix2 (-54)) (IZR (5102437881521477) * bpow radix2 (-56)) (IZR (-1685120352180915) * bpow radix2 (-47)) (IZR 636 * bpow radix2 (-77)) (IZR 659 * bpow radix2 (-71)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 159 (-159) (-75)); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_06.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_06.l1 th_ tl_ dg).
Qed.

Lemma segok_06 : SegOkRowA [(0x3fb7ee182602f10f)%Z; (0xbc5cfb654c0c3d98)%Z; (0x3fefb8a096acfacc)%Z; (0xbc82962e18495af3)%Z; (0xbfb7956846635c89)%Z; (0xbfd43b8f2037b997)%Z; (0x3fb6f885790229d5)%Z; (0x3fc65c1f4408d98f)%Z; (0xbfb61b665e4d89dc)%Z; (0xbfbc2472c9c7d5b5)%Z; (0x3fb56e515659de74)%Z; (0x3fb220a3e56aa545)%Z; (0xc027f26e9ffb6acc)%Z] (IZR 636 * bpow radix2 (-77)).
Proof.
  unfold SegOkRowA. cbn [nth].
  destruct (word_ok_intro (0x3fb7ee182602f10f)%Z false 6735711948697871%positive 56%nat (6735711948697871)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc5cfb654c0c3d98)%Z true 8157711834037656%positive 110%nat (-1019713979254707)%Z 3%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fefb8a096acfacc)%Z false 8928724140227276%positive 53%nat (2232181035056819)%Z 2%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc82962e18495af3)%Z true 5231674300914419%positive 107%nat (-5231674300914419)%Z 0%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfb7956846635c89)%Z true 6638199554399369%positive 56%nat (-6638199554399369)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbfd43b8f2037b997)%Z true 5694985441098135%positive 54%nat (-5694985441098135)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fb6f885790229d5)%Z false 6465701632158165%positive 56%nat (6465701632158165)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3fc65c1f4408d98f)%Z false 6293738842806671%positive 55%nat (6293738842806671)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbfb61b665e4d89dc)%Z true 6222575970388444%positive 56%nat (-1555643992597111)%Z 2%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0xbfbc2472c9c7d5b5)%Z true 7921374778086837%positive 56%nat (-7921374778086837)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3fb56e515659de74)%Z false 6032270131060340%positive 56%nat (1508067532765085)%Z 2%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3fb220a3e56aa545)%Z false 5102437881521477%positive 56%nat (5102437881521477)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc027f26e9ffb6acc)%Z true 6740481408723660%positive 49%nat (-1685120352180915)%Z 2%Z (-47)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_06 _ _).
  all: seg_numeric.
Qed.

Lemma row_06 : nth (Z.to_nat (6%Z - 1)) atan2_segments [] = [(0x3fb7ee182602f10f)%Z; (0xbc5cfb654c0c3d98)%Z; (0x3fefb8a096acfacc)%Z; (0xbc82962e18495af3)%Z; (0xbfb7956846635c89)%Z; (0xbfd43b8f2037b997)%Z; (0x3fb6f885790229d5)%Z; (0x3fc65c1f4408d98f)%Z; (0xbfb61b665e4d89dc)%Z; (0xbfbc2472c9c7d5b5)%Z; (0x3fb56e515659de74)%Z; (0x3fb220a3e56aa545)%Z; (0xc027f26e9ffb6acc)%Z].
Proof. reflexivity. Qed.

Lemma fast_06 zh zl : finite zh -> finite zl -> / 128 <= B zh -> B zh <= 1 ->
  Znearest ne (B zh * 64) = 6%Z -> Rabs (B zl) <= bpow radix2 (-53) -> on_grid (-211) (B zl) ->
  exists h l, atan2_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    Rabs (B h + B l - atan (IZR 6 / 64 + ((B zh - IZR 6 / 64) + B zl))) <= bpow radix2 (-63) * atan (IZR 6 / 64 + ((B zh - IZR 6 / 64) + B zl)).
Proof.
  intros Fz Fl L U Hn Hl Hg.
  pose proof (series_segment_a zh zl 6%Z (IZR 636 * bpow radix2 (-77)) ltac:(lia) Fz Fl L U Hn Hl Hg segok_06) as SS.
  cbv zeta in SS. rewrite row_06 in SS. cbn [nth] in SS.
  destruct SS as [h [l [Hs [Fh [Fl' [Nrm [Ht [e1 [ea [E1 [Eea Eq]]]]]]]]]]].
  exists h, l. split; [exact Hs | split; [exact Fh | split; [exact Fl' | split; [exact Nrm | ]]]].
  destruct (word_ok_intro (0x3fb7ee182602f10f)%Z false 6735711948697871%positive 56%nat (6735711948697871)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc5cfb654c0c3d98)%Z true 8157711834037656%positive 110%nat (-1019713979254707)%Z 3%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fefb8a096acfacc)%Z false 8928724140227276%positive 53%nat (2232181035056819)%Z 2%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc82962e18495af3)%Z true 5231674300914419%positive 107%nat (-5231674300914419)%Z 0%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfb7956846635c89)%Z true 6638199554399369%positive 56%nat (-6638199554399369)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbfd43b8f2037b997)%Z true 5694985441098135%positive 54%nat (-5694985441098135)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fb6f885790229d5)%Z false 6465701632158165%positive 56%nat (6465701632158165)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3fc65c1f4408d98f)%Z false 6293738842806671%positive 55%nat (6293738842806671)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbfb61b665e4d89dc)%Z true 6222575970388444%positive 56%nat (-1555643992597111)%Z 2%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0xbfbc2472c9c7d5b5)%Z true 7921374778086837%positive 56%nat (-7921374778086837)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3fb56e515659de74)%Z false 6032270131060340%positive 56%nat (1508067532765085)%Z 2%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3fb220a3e56aa545)%Z false 5102437881521477%positive 56%nat (5102437881521477)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc027f26e9ffb6acc)%Z true 6740481408723660%positive 49%nat (-1685120352180915)%Z 2%Z (-47)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  unfold seg_poly in Eq.
  pose proof (approx_06 _ _ _ _ _ _ _ _ _ _ _ _ _ ((B zh - IZR 6 / 64) + B zl) V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 Ht) as AP.
  pose proof (amin_06 ((B zh - IZR 6 / 64) + B zl) Ht) as HAm.
  destruct ea_dw_small as [Ea0 Ea1].
  rewrite Eq.
  refine (fast_compose _ _ e1 ea (IZR 14034219 * bpow radix2 (-95)) (IZR 636 * bpow radix2 (-77)) _ (IZR 719127 * bpow radix2 (-23)) _ AP E1 Eea HAm _ Ea0 _).
  - apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0].
  - bpow_num. replace (- prec)%Z with (-53)%Z by reflexivity. bpow_num. clear - Fz. interval with (i_prec 200).
Qed.

Lemma evalcert_07 : EvalCert (IZR (4450360452040905) * bpow radix2 (-52)) (IZR (6797230221671851) * bpow radix2 (-108)) (IZR (-7696063623698241) * bpow radix2 (-56)) (IZR (-5586398805212817) * bpow radix2 (-54)) (IZR (7425278236432933) * bpow radix2 (-56)) (IZR (2991199962317161) * bpow radix2 (-54)) (IZR (-880871315629739) * bpow radix2 (-53)) (IZR (-446223210752155) * bpow radix2 (-52)) (IZR (6656604118331663) * bpow radix2 (-56)) (IZR (2120199273569437) * bpow radix2 (-55)) (IZR (-4794672692954223) * bpow radix2 (-49)) (IZR 735 * bpow radix2 (-77)) (IZR 647 * bpow radix2 (-71)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 735 (-735) (-77)); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_07.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_07.l1 th_ tl_ dg).
Qed.

Lemma segok_07 : SegOkRowA [(0x3fbbe39ebe6f07c3)%Z; (0x3c5f7b8f29a05987)%Z; (0x3fef9f2893bb9192)%Z; (0x3c78260b7cd1bdab)%Z; (0xbfbb578772759741)%Z; (0xbfd3d8ccd45bbe91)%Z; (0x3fba61404fa41a25)%Z; (0x3fc540f6066982d2)%Z; (0xbfb9092eaee33558)%Z; (0xbfb95d66ff7a89b0)%Z; (0x3fb7a6256be2310f)%Z; (0x3fae213d72377274)%Z; (0xc02108babaad846f)%Z] (IZR 735 * bpow radix2 (-77)).
Proof.
  unfold SegOkRowA. cbn [nth].
  destruct (word_ok_intro (0x3fbbe39ebe6f07c3)%Z false 7850095310473155%positive 56%nat (7850095310473155)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c5f7b8f29a05987)%Z false 8861579086944647%positive 110%nat (8861579086944647)%Z 0%Z (-110)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fef9f2893bb9192)%Z false 8900720904081810%positive 53%nat (4450360452040905)%Z 1%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c78260b7cd1bdab)%Z false 6797230221671851%positive 108%nat (6797230221671851)%Z 0%Z (-108)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfbb578772759741)%Z true 7696063623698241%positive 56%nat (-7696063623698241)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbfd3d8ccd45bbe91)%Z true 5586398805212817%positive 54%nat (-5586398805212817)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fba61404fa41a25)%Z false 7425278236432933%positive 56%nat (7425278236432933)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3fc540f6066982d2)%Z false 5982399924634322%positive 55%nat (2991199962317161)%Z 1%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbfb9092eaee33558)%Z true 7046970525037912%positive 56%nat (-880871315629739)%Z 3%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0xbfb95d66ff7a89b0)%Z true 7139571372034480%positive 56%nat (-446223210752155)%Z 4%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3fb7a6256be2310f)%Z false 6656604118331663%positive 56%nat (6656604118331663)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3fae213d72377274)%Z false 8480797094277748%positive 57%nat (2120199273569437)%Z 2%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc02108babaad846f)%Z true 4794672692954223%positive 49%nat (-4794672692954223)%Z 0%Z (-49)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_07 _ _).
  all: seg_numeric.
Qed.

Lemma row_07 : nth (Z.to_nat (7%Z - 1)) atan2_segments [] = [(0x3fbbe39ebe6f07c3)%Z; (0x3c5f7b8f29a05987)%Z; (0x3fef9f2893bb9192)%Z; (0x3c78260b7cd1bdab)%Z; (0xbfbb578772759741)%Z; (0xbfd3d8ccd45bbe91)%Z; (0x3fba61404fa41a25)%Z; (0x3fc540f6066982d2)%Z; (0xbfb9092eaee33558)%Z; (0xbfb95d66ff7a89b0)%Z; (0x3fb7a6256be2310f)%Z; (0x3fae213d72377274)%Z; (0xc02108babaad846f)%Z].
Proof. reflexivity. Qed.

Lemma fast_07 zh zl : finite zh -> finite zl -> / 128 <= B zh -> B zh <= 1 ->
  Znearest ne (B zh * 64) = 7%Z -> Rabs (B zl) <= bpow radix2 (-53) -> on_grid (-211) (B zl) ->
  exists h l, atan2_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    Rabs (B h + B l - atan (IZR 7 / 64 + ((B zh - IZR 7 / 64) + B zl))) <= bpow radix2 (-63) * atan (IZR 7 / 64 + ((B zh - IZR 7 / 64) + B zl)).
Proof.
  intros Fz Fl L U Hn Hl Hg.
  pose proof (series_segment_a zh zl 7%Z (IZR 735 * bpow radix2 (-77)) ltac:(lia) Fz Fl L U Hn Hl Hg segok_07) as SS.
  cbv zeta in SS. rewrite row_07 in SS. cbn [nth] in SS.
  destruct SS as [h [l [Hs [Fh [Fl' [Nrm [Ht [e1 [ea [E1 [Eea Eq]]]]]]]]]]].
  exists h, l. split; [exact Hs | split; [exact Fh | split; [exact Fl' | split; [exact Nrm | ]]]].
  destruct (word_ok_intro (0x3fbbe39ebe6f07c3)%Z false 7850095310473155%positive 56%nat (7850095310473155)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c5f7b8f29a05987)%Z false 8861579086944647%positive 110%nat (8861579086944647)%Z 0%Z (-110)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fef9f2893bb9192)%Z false 8900720904081810%positive 53%nat (4450360452040905)%Z 1%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c78260b7cd1bdab)%Z false 6797230221671851%positive 108%nat (6797230221671851)%Z 0%Z (-108)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfbb578772759741)%Z true 7696063623698241%positive 56%nat (-7696063623698241)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbfd3d8ccd45bbe91)%Z true 5586398805212817%positive 54%nat (-5586398805212817)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fba61404fa41a25)%Z false 7425278236432933%positive 56%nat (7425278236432933)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3fc540f6066982d2)%Z false 5982399924634322%positive 55%nat (2991199962317161)%Z 1%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbfb9092eaee33558)%Z true 7046970525037912%positive 56%nat (-880871315629739)%Z 3%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0xbfb95d66ff7a89b0)%Z true 7139571372034480%positive 56%nat (-446223210752155)%Z 4%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3fb7a6256be2310f)%Z false 6656604118331663%positive 56%nat (6656604118331663)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3fae213d72377274)%Z false 8480797094277748%positive 57%nat (2120199273569437)%Z 2%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc02108babaad846f)%Z true 4794672692954223%positive 49%nat (-4794672692954223)%Z 0%Z (-49)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  unfold seg_poly in Eq.
  pose proof (approx_07 _ _ _ _ _ _ _ _ _ _ _ _ _ ((B zh - IZR 7 / 64) + B zl) V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 Ht) as AP.
  pose proof (amin_07 ((B zh - IZR 7 / 64) + B zl) Ht) as HAm.
  destruct ea_dw_small as [Ea0 Ea1].
  rewrite Eq.
  refine (fast_compose _ _ e1 ea (IZR 9947964 * bpow radix2 (-95)) (IZR 735 * bpow radix2 (-77)) _ (IZR 849054 * bpow radix2 (-23)) _ AP E1 Eea HAm _ Ea0 _).
  - apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0].
  - bpow_num. replace (- prec)%Z with (-53)%Z by reflexivity. bpow_num. clear - Fz. interval with (i_prec 200).
Qed.

Lemma evalcert_08 : EvalCert (IZR (277144592453569) * bpow radix2 (-48)) (IZR (-277144592453569) * bpow radix2 (-102)) (IZR (-8732186543767835) * bpow radix2 (-56)) (IZR (-5463214145331671) * bpow radix2 (-54)) (IZR (8333296128850629) * bpow radix2 (-56)) (IZR (5634488478990681) * bpow radix2 (-55)) (IZR (-3890822488316401) * bpow radix2 (-55)) (IZR (-1570897632920293) * bpow radix2 (-54)) (IZR (3538020854539143) * bpow radix2 (-55)) (IZR (3241447238991003) * bpow radix2 (-56)) (IZR (5217418034259967) * bpow radix2 (-51)) (IZR 831 * bpow radix2 (-77)) (IZR 634 * bpow radix2 (-71)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 831 (-831) (-77)); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_08.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_08.l1 th_ tl_ dg).
Qed.

Lemma segok_08 : SegOkRowA [(0x3fbfd5ba9aac2f6e)%Z; (0xbc4cd37686760c17)%Z; (0x3fef81f81f81f820)%Z; (0xbc8f81f81f81f820)%Z; (0xbfbf05e09d0dc11b)%Z; (0xbfd368c3aa76e1d7)%Z; (0x3fbd9b16b3917ac5)%Z; (0x3fc4048994480159)%Z; (0xbfbba55d6899b3e2)%Z; (0xbfb652e46d8e0b94)%Z; (0x3fb9239f587c470e)%Z; (0x3fa708287e79f936)%Z; (0x40028936cc93a7ff)%Z] (IZR 831 * bpow radix2 (-77)).
Proof.
  unfold SegOkRowA. cbn [nth].
  destruct (word_ok_intro (0x3fbfd5ba9aac2f6e)%Z false 8960721713639278%positive 56%nat (4480360856819639)%Z 1%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc4cd37686760c17)%Z true 8113805363383319%positive 111%nat (-8113805363383319)%Z 0%Z (-111)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fef81f81f81f820)%Z false 8868626958514208%positive 53%nat (277144592453569)%Z 5%Z (-48)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc8f81f81f81f820)%Z true 8868626958514208%positive 107%nat (-277144592453569)%Z 5%Z (-102)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfbf05e09d0dc11b)%Z true 8732186543767835%positive 56%nat (-8732186543767835)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbfd368c3aa76e1d7)%Z true 5463214145331671%positive 54%nat (-5463214145331671)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fbd9b16b3917ac5)%Z false 8333296128850629%positive 56%nat (8333296128850629)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3fc4048994480159)%Z false 5634488478990681%positive 55%nat (5634488478990681)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbfbba55d6899b3e2)%Z true 7781644976632802%positive 56%nat (-3890822488316401)%Z 1%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0xbfb652e46d8e0b94)%Z true 6283590531681172%positive 56%nat (-1570897632920293)%Z 2%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3fb9239f587c470e)%Z false 7076041709078286%positive 56%nat (3538020854539143)%Z 1%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3fa708287e79f936)%Z false 6482894477982006%positive 57%nat (3241447238991003)%Z 1%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x40028936cc93a7ff)%Z false 5217418034259967%positive 51%nat (5217418034259967)%Z 0%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_08 _ _).
  all: seg_numeric.
Qed.

Lemma row_08 : nth (Z.to_nat (8%Z - 1)) atan2_segments [] = [(0x3fbfd5ba9aac2f6e)%Z; (0xbc4cd37686760c17)%Z; (0x3fef81f81f81f820)%Z; (0xbc8f81f81f81f820)%Z; (0xbfbf05e09d0dc11b)%Z; (0xbfd368c3aa76e1d7)%Z; (0x3fbd9b16b3917ac5)%Z; (0x3fc4048994480159)%Z; (0xbfbba55d6899b3e2)%Z; (0xbfb652e46d8e0b94)%Z; (0x3fb9239f587c470e)%Z; (0x3fa708287e79f936)%Z; (0x40028936cc93a7ff)%Z].
Proof. reflexivity. Qed.

Lemma fast_08 zh zl : finite zh -> finite zl -> / 128 <= B zh -> B zh <= 1 ->
  Znearest ne (B zh * 64) = 8%Z -> Rabs (B zl) <= bpow radix2 (-53) -> on_grid (-211) (B zl) ->
  exists h l, atan2_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    Rabs (B h + B l - atan (IZR 8 / 64 + ((B zh - IZR 8 / 64) + B zl))) <= bpow radix2 (-63) * atan (IZR 8 / 64 + ((B zh - IZR 8 / 64) + B zl)).
Proof.
  intros Fz Fl L U Hn Hl Hg.
  pose proof (series_segment_a zh zl 8%Z (IZR 831 * bpow radix2 (-77)) ltac:(lia) Fz Fl L U Hn Hl Hg segok_08) as SS.
  cbv zeta in SS. rewrite row_08 in SS. cbn [nth] in SS.
  destruct SS as [h [l [Hs [Fh [Fl' [Nrm [Ht [e1 [ea [E1 [Eea Eq]]]]]]]]]]].
  exists h, l. split; [exact Hs | split; [exact Fh | split; [exact Fl' | split; [exact Nrm | ]]]].
  destruct (word_ok_intro (0x3fbfd5ba9aac2f6e)%Z false 8960721713639278%positive 56%nat (4480360856819639)%Z 1%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc4cd37686760c17)%Z true 8113805363383319%positive 111%nat (-8113805363383319)%Z 0%Z (-111)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fef81f81f81f820)%Z false 8868626958514208%positive 53%nat (277144592453569)%Z 5%Z (-48)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc8f81f81f81f820)%Z true 8868626958514208%positive 107%nat (-277144592453569)%Z 5%Z (-102)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfbf05e09d0dc11b)%Z true 8732186543767835%positive 56%nat (-8732186543767835)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbfd368c3aa76e1d7)%Z true 5463214145331671%positive 54%nat (-5463214145331671)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fbd9b16b3917ac5)%Z false 8333296128850629%positive 56%nat (8333296128850629)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3fc4048994480159)%Z false 5634488478990681%positive 55%nat (5634488478990681)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbfbba55d6899b3e2)%Z true 7781644976632802%positive 56%nat (-3890822488316401)%Z 1%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0xbfb652e46d8e0b94)%Z true 6283590531681172%positive 56%nat (-1570897632920293)%Z 2%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3fb9239f587c470e)%Z false 7076041709078286%positive 56%nat (3538020854539143)%Z 1%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3fa708287e79f936)%Z false 6482894477982006%positive 57%nat (3241447238991003)%Z 1%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x40028936cc93a7ff)%Z false 5217418034259967%positive 51%nat (5217418034259967)%Z 0%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  unfold seg_poly in Eq.
  pose proof (approx_08 _ _ _ _ _ _ _ _ _ _ _ _ _ ((B zh - IZR 8 / 64) + B zl) V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 Ht) as AP.
  pose proof (amin_08 ((B zh - IZR 8 / 64) + B zl) Ht) as HAm.
  destruct ea_dw_small as [Ea0 Ea1].
  rewrite Eq.
  refine (fast_compose _ _ e1 ea (IZR 11342246 * bpow radix2 (-97)) (IZR 831 * bpow radix2 (-77)) _ (IZR 978574 * bpow radix2 (-23)) _ AP E1 Eea HAm _ Ea0 _).
  - apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0].
  - bpow_num. replace (- prec)%Z with (-53)%Z by reflexivity. bpow_num. clear - Fz. interval with (i_prec 200).
Qed.

Lemma evalcert_09 : EvalCert (IZR (4416266237421487) * bpow radix2 (-52)) (IZR (1798420918949961) * bpow radix2 (-106)) (IZR (-1217988677402335) * bpow radix2 (-53)) (IZR (-1331569990592205) * bpow radix2 (-52)) (IZR (4592189375243179) * bpow radix2 (-55)) (IZR (5254385813433751) * bpow radix2 (-55)) (IZR (-8419419197104381) * bpow radix2 (-56)) (IZR (-5370381666193917) * bpow radix2 (-56)) (IZR (7573791757976131) * bpow radix2 (-56)) (IZR (1121693243182513) * bpow radix2 (-55)) (IZR (-4940539387106739) * bpow radix2 (-49)) (IZR 925 * bpow radix2 (-77)) (IZR 618 * bpow radix2 (-71)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 925 (-925) (-77)); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_09.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_09.l1 th_ tl_ dg).
Qed.

Lemma segok_09 : SegOkRowA [(0x3fc1e1fafb043727)%Z; (0xbc4b485914dacf8c)%Z; (0x3fef612438a14f5e)%Z; (0x3c798e9e001f6124)%Z; (0xbfc14f0459d3fb7c)%Z; (0xbfd2ec3931219b34)%Z; (0x3fc050926873e3ab)%Z; (0x3fc2aad607ec2d97)%Z; (0xbfbde96aca7560fd)%Z; (0xbfb314556b8591fd)%Z; (0x3fbae852cf564243)%Z; (0x3f9fe1647a746d88)%Z; (0xc0218d64f72ad5b3)%Z] (IZR 925 * bpow radix2 (-77)).
Proof.
  unfold SegOkRowA. cbn [nth].
  destruct (word_ok_intro (0x3fc1e1fafb043727)%Z false 5033542673512231%positive 55%nat (5033542673512231)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc4b485914dacf8c)%Z true 7679371810361228%positive 111%nat (-1919842952590307)%Z 2%Z (-109)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fef612438a14f5e)%Z false 8832532474842974%positive 53%nat (4416266237421487)%Z 1%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c798e9e001f6124)%Z false 7193683675799844%positive 108%nat (1798420918949961)%Z 2%Z (-106)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfc14f0459d3fb7c)%Z true 4871954709609340%positive 55%nat (-1217988677402335)%Z 2%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbfd2ec3931219b34)%Z true 5326279962368820%positive 54%nat (-1331569990592205)%Z 2%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fc050926873e3ab)%Z false 4592189375243179%positive 55%nat (4592189375243179)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3fc2aad607ec2d97)%Z false 5254385813433751%positive 55%nat (5254385813433751)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbfbde96aca7560fd)%Z true 8419419197104381%positive 56%nat (-8419419197104381)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0xbfb314556b8591fd)%Z true 5370381666193917%positive 56%nat (-5370381666193917)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3fbae852cf564243)%Z false 7573791757976131%positive 56%nat (7573791757976131)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3f9fe1647a746d88)%Z false 8973545945460104%positive 58%nat (1121693243182513)%Z 3%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc0218d64f72ad5b3)%Z true 4940539387106739%positive 49%nat (-4940539387106739)%Z 0%Z (-49)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_09 _ _).
  all: seg_numeric.
Qed.

Lemma row_09 : nth (Z.to_nat (9%Z - 1)) atan2_segments [] = [(0x3fc1e1fafb043727)%Z; (0xbc4b485914dacf8c)%Z; (0x3fef612438a14f5e)%Z; (0x3c798e9e001f6124)%Z; (0xbfc14f0459d3fb7c)%Z; (0xbfd2ec3931219b34)%Z; (0x3fc050926873e3ab)%Z; (0x3fc2aad607ec2d97)%Z; (0xbfbde96aca7560fd)%Z; (0xbfb314556b8591fd)%Z; (0x3fbae852cf564243)%Z; (0x3f9fe1647a746d88)%Z; (0xc0218d64f72ad5b3)%Z].
Proof. reflexivity. Qed.

Lemma fast_09 zh zl : finite zh -> finite zl -> / 128 <= B zh -> B zh <= 1 ->
  Znearest ne (B zh * 64) = 9%Z -> Rabs (B zl) <= bpow radix2 (-53) -> on_grid (-211) (B zl) ->
  exists h l, atan2_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    Rabs (B h + B l - atan (IZR 9 / 64 + ((B zh - IZR 9 / 64) + B zl))) <= bpow radix2 (-63) * atan (IZR 9 / 64 + ((B zh - IZR 9 / 64) + B zl)).
Proof.
  intros Fz Fl L U Hn Hl Hg.
  pose proof (series_segment_a zh zl 9%Z (IZR 925 * bpow radix2 (-77)) ltac:(lia) Fz Fl L U Hn Hl Hg segok_09) as SS.
  cbv zeta in SS. rewrite row_09 in SS. cbn [nth] in SS.
  destruct SS as [h [l [Hs [Fh [Fl' [Nrm [Ht [e1 [ea [E1 [Eea Eq]]]]]]]]]]].
  exists h, l. split; [exact Hs | split; [exact Fh | split; [exact Fl' | split; [exact Nrm | ]]]].
  destruct (word_ok_intro (0x3fc1e1fafb043727)%Z false 5033542673512231%positive 55%nat (5033542673512231)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc4b485914dacf8c)%Z true 7679371810361228%positive 111%nat (-1919842952590307)%Z 2%Z (-109)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fef612438a14f5e)%Z false 8832532474842974%positive 53%nat (4416266237421487)%Z 1%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c798e9e001f6124)%Z false 7193683675799844%positive 108%nat (1798420918949961)%Z 2%Z (-106)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfc14f0459d3fb7c)%Z true 4871954709609340%positive 55%nat (-1217988677402335)%Z 2%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbfd2ec3931219b34)%Z true 5326279962368820%positive 54%nat (-1331569990592205)%Z 2%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fc050926873e3ab)%Z false 4592189375243179%positive 55%nat (4592189375243179)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3fc2aad607ec2d97)%Z false 5254385813433751%positive 55%nat (5254385813433751)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbfbde96aca7560fd)%Z true 8419419197104381%positive 56%nat (-8419419197104381)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0xbfb314556b8591fd)%Z true 5370381666193917%positive 56%nat (-5370381666193917)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3fbae852cf564243)%Z false 7573791757976131%positive 56%nat (7573791757976131)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3f9fe1647a746d88)%Z false 8973545945460104%positive 58%nat (1121693243182513)%Z 3%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc0218d64f72ad5b3)%Z true 4940539387106739%positive 49%nat (-4940539387106739)%Z 0%Z (-49)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  unfold seg_poly in Eq.
  pose proof (approx_09 _ _ _ _ _ _ _ _ _ _ _ _ _ ((B zh - IZR 9 / 64) + B zl) V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 Ht) as AP.
  pose proof (amin_09 ((B zh - IZR 9 / 64) + B zl) Ht) as HAm.
  destruct ea_dw_small as [Ea0 Ea1].
  rewrite Eq.
  refine (fast_compose _ _ e1 ea (IZR 10025210 * bpow radix2 (-95)) (IZR 925 * bpow radix2 (-77)) _ (IZR 553813 * bpow radix2 (-22)) _ AP E1 Eea HAm _ Ea0 _).
  - apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0].
  - bpow_num. replace (- prec)%Z with (-53)%Z by reflexivity. bpow_num. clear - Fz. interval with (i_prec 200).
Qed.

Lemma evalcert_10 : EvalCert (IZR (2198134422510671) * bpow radix2 (-51)) (IZR (1253623537838117) * bpow radix2 (-105)) (IZR (-335273124501151) * bpow radix2 (-51)) (IZR (-1294130822351567) * bpow radix2 (-52)) (IZR (2493464544769251) * bpow radix2 (-54)) (IZR (2423383208383533) * bpow radix2 (-54)) (IZR (-1119372510211067) * bpow radix2 (-53)) (IZR (-8834910187494991) * bpow radix2 (-57)) (IZR (996852611950679) * bpow radix2 (-53)) (IZR (5143492910506691) * bpow radix2 (-58)) (IZR (-6839955651239147) * bpow radix2 (-48)) (IZR 1017 * bpow radix2 (-77)) (IZR 601 * bpow radix2 (-71)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 1017 (-1017) (-77)); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_10.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_10.l1 th_ tl_ dg).
Qed.

Lemma segok_10 : SegOkRowA [(0x3fc3d6eee8c6626c)%Z; (0x3c661a3b0ce9281b)%Z; (0x3fef3cc435b0713c)%Z; (0x3c81d0a7e69ea094)%Z; (0xbfc30eddb7d169f0)%Z; (0xbfd264053fd62b3c)%Z; (0x3fc1b795e8e6e9c6)%Z; (0x3fc1381bbe94a85a)%Z; (0xbfbfd081c6bd5fd8)%Z; (0xbfaf634dd3591e4f)%Z; (0x3fbc550eaea142b8)%Z; (0x3f9245fac3d5e2c3)%Z; (0xc0384ce746df1ceb)%Z] (IZR 1017 * bpow radix2 (-77)).
Proof.
  unfold SegOkRowA. cbn [nth].
  destruct (word_ok_intro (0x3fc3d6eee8c6626c)%Z false 5584346153378412%positive 55%nat (1396086538344603)%Z 2%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c661a3b0ce9281b)%Z false 6221290409633819%positive 109%nat (6221290409633819)%Z 0%Z (-109)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fef3cc435b0713c)%Z false 8792537690042684%positive 53%nat (2198134422510671)%Z 2%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c81d0a7e69ea094)%Z false 5014494151352468%positive 107%nat (1253623537838117)%Z 2%Z (-105)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfc30eddb7d169f0)%Z true 5364369992018416%positive 55%nat (-335273124501151)%Z 4%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbfd264053fd62b3c)%Z true 5176523289406268%positive 54%nat (-1294130822351567)%Z 2%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fc1b795e8e6e9c6)%Z false 4986929089538502%positive 55%nat (2493464544769251)%Z 1%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3fc1381bbe94a85a)%Z false 4846766416767066%positive 55%nat (2423383208383533)%Z 1%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbfbfd081c6bd5fd8)%Z true 8954980081688536%positive 56%nat (-1119372510211067)%Z 3%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0xbfaf634dd3591e4f)%Z true 8834910187494991%positive 57%nat (-8834910187494991)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3fbc550eaea142b8)%Z false 7974820895605432%positive 56%nat (996852611950679)%Z 3%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3f9245fac3d5e2c3)%Z false 5143492910506691%positive 58%nat (5143492910506691)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc0384ce746df1ceb)%Z true 6839955651239147%positive 48%nat (-6839955651239147)%Z 0%Z (-48)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_10 _ _).
  all: seg_numeric.
Qed.

Lemma row_10 : nth (Z.to_nat (10%Z - 1)) atan2_segments [] = [(0x3fc3d6eee8c6626c)%Z; (0x3c661a3b0ce9281b)%Z; (0x3fef3cc435b0713c)%Z; (0x3c81d0a7e69ea094)%Z; (0xbfc30eddb7d169f0)%Z; (0xbfd264053fd62b3c)%Z; (0x3fc1b795e8e6e9c6)%Z; (0x3fc1381bbe94a85a)%Z; (0xbfbfd081c6bd5fd8)%Z; (0xbfaf634dd3591e4f)%Z; (0x3fbc550eaea142b8)%Z; (0x3f9245fac3d5e2c3)%Z; (0xc0384ce746df1ceb)%Z].
Proof. reflexivity. Qed.

Lemma fast_10 zh zl : finite zh -> finite zl -> / 128 <= B zh -> B zh <= 1 ->
  Znearest ne (B zh * 64) = 10%Z -> Rabs (B zl) <= bpow radix2 (-53) -> on_grid (-211) (B zl) ->
  exists h l, atan2_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    Rabs (B h + B l - atan (IZR 10 / 64 + ((B zh - IZR 10 / 64) + B zl))) <= bpow radix2 (-63) * atan (IZR 10 / 64 + ((B zh - IZR 10 / 64) + B zl)).
Proof.
  intros Fz Fl L U Hn Hl Hg.
  pose proof (series_segment_a zh zl 10%Z (IZR 1017 * bpow radix2 (-77)) ltac:(lia) Fz Fl L U Hn Hl Hg segok_10) as SS.
  cbv zeta in SS. rewrite row_10 in SS. cbn [nth] in SS.
  destruct SS as [h [l [Hs [Fh [Fl' [Nrm [Ht [e1 [ea [E1 [Eea Eq]]]]]]]]]]].
  exists h, l. split; [exact Hs | split; [exact Fh | split; [exact Fl' | split; [exact Nrm | ]]]].
  destruct (word_ok_intro (0x3fc3d6eee8c6626c)%Z false 5584346153378412%positive 55%nat (1396086538344603)%Z 2%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c661a3b0ce9281b)%Z false 6221290409633819%positive 109%nat (6221290409633819)%Z 0%Z (-109)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fef3cc435b0713c)%Z false 8792537690042684%positive 53%nat (2198134422510671)%Z 2%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c81d0a7e69ea094)%Z false 5014494151352468%positive 107%nat (1253623537838117)%Z 2%Z (-105)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfc30eddb7d169f0)%Z true 5364369992018416%positive 55%nat (-335273124501151)%Z 4%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbfd264053fd62b3c)%Z true 5176523289406268%positive 54%nat (-1294130822351567)%Z 2%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fc1b795e8e6e9c6)%Z false 4986929089538502%positive 55%nat (2493464544769251)%Z 1%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3fc1381bbe94a85a)%Z false 4846766416767066%positive 55%nat (2423383208383533)%Z 1%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbfbfd081c6bd5fd8)%Z true 8954980081688536%positive 56%nat (-1119372510211067)%Z 3%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0xbfaf634dd3591e4f)%Z true 8834910187494991%positive 57%nat (-8834910187494991)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3fbc550eaea142b8)%Z false 7974820895605432%positive 56%nat (996852611950679)%Z 3%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3f9245fac3d5e2c3)%Z false 5143492910506691%positive 58%nat (5143492910506691)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc0384ce746df1ceb)%Z true 6839955651239147%positive 48%nat (-6839955651239147)%Z 0%Z (-48)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  unfold seg_poly in Eq.
  pose proof (approx_10 _ _ _ _ _ _ _ _ _ _ _ _ _ ((B zh - IZR 10 / 64) + B zl) V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 Ht) as AP.
  pose proof (amin_10 ((B zh - IZR 10 / 64) + B zl) Ht) as HAm.
  destruct ea_dw_small as [Ea0 Ea1].
  rewrite Eq.
  refine (fast_compose _ _ e1 ea (IZR 14261815 * bpow radix2 (-94)) (IZR 1017 * bpow radix2 (-77)) _ (IZR 618077 * bpow radix2 (-22)) _ AP E1 Eea HAm _ Ea0 _).
  - apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0].
  - bpow_num. replace (- prec)%Z with (-53)%Z by reflexivity. bpow_num. clear - Fz. interval with (i_prec 200).
Qed.

Lemma evalcert_11 : EvalCert (IZR (8748752228460779) * bpow radix2 (-53)) (IZR (-3868161690855095) * bpow radix2 (-106)) (IZR (-5842183133826311) * bpow radix2 (-55)) (IZR (-5014938297614675) * bpow radix2 (-54)) (IZR (2674453490972731) * bpow radix2 (-54)) (IZR (2208254196833407) * bpow radix2 (-54)) (IZR (-4692466639080915) * bpow radix2 (-55)) (IZR (-860601178091087) * bpow radix2 (-54)) (IZR (7980265484940121) * bpow radix2 (-56)) (IZR (2240710524066713) * bpow radix2 (-59)) (IZR (-1972381584112781) * bpow radix2 (-47)) (IZR 553 * bpow radix2 (-76)) (IZR 583 * bpow radix2 (-71)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 553 (-553) (-76)); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_11.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_11.l1 th_ tl_ dg).
Qed.

Lemma segok_11 : SegOkRowA [(0x3fc5c9811e3ec26a)%Z; (0xbc5054ab2c010f3d)%Z; (0x3fef14f19cce28eb)%Z; (0xbc8b7c252708cd6e)%Z; (0xbfc4c16f42678d07)%Z; (0xbfd1d10f4fccc153)%Z; (0x3fc300cd74987076)%Z; (0x3fbf6194fbe771fc)%Z; (0xbfc0abc607248dd3)%Z; (0xbfa875b29c1b7278)%Z; (0x3fbc5a0259717359)%Z; (0x3f6fd7a84b536e64)%Z; (0xc02c077b7ebaf234)%Z] (IZR 553 * bpow radix2 (-76)).
Proof.
  unfold SegOkRowA. cbn [nth].
  destruct (word_ok_intro (0x3fc5c9811e3ec26a)%Z false 6132530906317418%positive 55%nat (3066265453158709)%Z 1%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc5054ab2c010f3d)%Z true 4596693781778237%positive 110%nat (-4596693781778237)%Z 0%Z (-110)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fef14f19cce28eb)%Z false 8748752228460779%positive 53%nat (8748752228460779)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc8b7c252708cd6e)%Z true 7736323381710190%positive 107%nat (-3868161690855095)%Z 1%Z (-106)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfc4c16f42678d07)%Z true 5842183133826311%positive 55%nat (-5842183133826311)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbfd1d10f4fccc153)%Z true 5014938297614675%positive 54%nat (-5014938297614675)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fc300cd74987076)%Z false 5348906981945462%positive 55%nat (2674453490972731)%Z 1%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3fbf6194fbe771fc)%Z false 8833016787333628%positive 56%nat (2208254196833407)%Z 2%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbfc0abc607248dd3)%Z true 4692466639080915%positive 55%nat (-4692466639080915)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0xbfa875b29c1b7278)%Z true 6884809424728696%positive 57%nat (-860601178091087)%Z 3%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3fbc5a0259717359)%Z false 7980265484940121%positive 56%nat (7980265484940121)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3f6fd7a84b536e64)%Z false 8962842096266852%positive 61%nat (2240710524066713)%Z 2%Z (-59)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc02c077b7ebaf234)%Z true 7889526336451124%positive 49%nat (-1972381584112781)%Z 2%Z (-47)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_11 _ _).
  all: seg_numeric.
Qed.

Lemma row_11 : nth (Z.to_nat (11%Z - 1)) atan2_segments [] = [(0x3fc5c9811e3ec26a)%Z; (0xbc5054ab2c010f3d)%Z; (0x3fef14f19cce28eb)%Z; (0xbc8b7c252708cd6e)%Z; (0xbfc4c16f42678d07)%Z; (0xbfd1d10f4fccc153)%Z; (0x3fc300cd74987076)%Z; (0x3fbf6194fbe771fc)%Z; (0xbfc0abc607248dd3)%Z; (0xbfa875b29c1b7278)%Z; (0x3fbc5a0259717359)%Z; (0x3f6fd7a84b536e64)%Z; (0xc02c077b7ebaf234)%Z].
Proof. reflexivity. Qed.

Lemma fast_11 zh zl : finite zh -> finite zl -> / 128 <= B zh -> B zh <= 1 ->
  Znearest ne (B zh * 64) = 11%Z -> Rabs (B zl) <= bpow radix2 (-53) -> on_grid (-211) (B zl) ->
  exists h l, atan2_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    Rabs (B h + B l - atan (IZR 11 / 64 + ((B zh - IZR 11 / 64) + B zl))) <= bpow radix2 (-63) * atan (IZR 11 / 64 + ((B zh - IZR 11 / 64) + B zl)).
Proof.
  intros Fz Fl L U Hn Hl Hg.
  pose proof (series_segment_a zh zl 11%Z (IZR 553 * bpow radix2 (-76)) ltac:(lia) Fz Fl L U Hn Hl Hg segok_11) as SS.
  cbv zeta in SS. rewrite row_11 in SS. cbn [nth] in SS.
  destruct SS as [h [l [Hs [Fh [Fl' [Nrm [Ht [e1 [ea [E1 [Eea Eq]]]]]]]]]]].
  exists h, l. split; [exact Hs | split; [exact Fh | split; [exact Fl' | split; [exact Nrm | ]]]].
  destruct (word_ok_intro (0x3fc5c9811e3ec26a)%Z false 6132530906317418%positive 55%nat (3066265453158709)%Z 1%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc5054ab2c010f3d)%Z true 4596693781778237%positive 110%nat (-4596693781778237)%Z 0%Z (-110)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fef14f19cce28eb)%Z false 8748752228460779%positive 53%nat (8748752228460779)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc8b7c252708cd6e)%Z true 7736323381710190%positive 107%nat (-3868161690855095)%Z 1%Z (-106)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfc4c16f42678d07)%Z true 5842183133826311%positive 55%nat (-5842183133826311)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbfd1d10f4fccc153)%Z true 5014938297614675%positive 54%nat (-5014938297614675)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fc300cd74987076)%Z false 5348906981945462%positive 55%nat (2674453490972731)%Z 1%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3fbf6194fbe771fc)%Z false 8833016787333628%positive 56%nat (2208254196833407)%Z 2%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbfc0abc607248dd3)%Z true 4692466639080915%positive 55%nat (-4692466639080915)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0xbfa875b29c1b7278)%Z true 6884809424728696%positive 57%nat (-860601178091087)%Z 3%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3fbc5a0259717359)%Z false 7980265484940121%positive 56%nat (7980265484940121)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3f6fd7a84b536e64)%Z false 8962842096266852%positive 61%nat (2240710524066713)%Z 2%Z (-59)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc02c077b7ebaf234)%Z true 7889526336451124%positive 49%nat (-1972381584112781)%Z 2%Z (-47)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  unfold seg_poly in Eq.
  pose proof (approx_11 _ _ _ _ _ _ _ _ _ _ _ _ _ ((B zh - IZR 11 / 64) + B zl) V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 Ht) as AP.
  pose proof (amin_11 ((B zh - IZR 11 / 64) + B zl) Ht) as HAm.
  destruct ea_dw_small as [Ea0 Ea1].
  rewrite Eq.
  refine (fast_compose _ _ e1 ea (IZR 16428930 * bpow radix2 (-95)) (IZR 553 * bpow radix2 (-76)) _ (IZR 682050 * bpow radix2 (-22)) _ AP E1 Eea HAm _ Ea0 _).
  - apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0].
  - bpow_num. replace (- prec)%Z with (-53)%Z by reflexivity. bpow_num. clear - Fz. interval with (i_prec 200).
Qed.

Lemma evalcert_12 : EvalCert (IZR (4350647187195649) * bpow radix2 (-52)) (IZR (-4894478085595105) * bpow radix2 (-109)) (IZR (-6304334037294827) * bpow radix2 (-55)) (IZR (-4842574405167347) * bpow radix2 (-54)) (IZR (5676548947574939) * bpow radix2 (-55)) (IZR (992150847238819) * bpow radix2 (-53)) (IZR (-4853906944194515) * bpow radix2 (-55)) (IZR (-4924975024838261) * bpow radix2 (-57)) (IZR (964033442286411) * bpow radix2 (-53)) (IZR (-5577731898527895) * bpow radix2 (-59)) (IZR (1437651861114777) * bpow radix2 (-47)) (IZR 596 * bpow radix2 (-76)) (IZR 563 * bpow radix2 (-71)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 149 (-149) (-74)); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_12.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_12.l1 th_ tl_ dg).
Qed.

Lemma segok_12 : SegOkRowA [(0x3fc7b97b4bce5b02)%Z; (0x3c5347b0b4f881ca)%Z; (0x3feee9c7f8458e02)%Z; (0xbc6163807ba71fe1)%Z; (0xbfc665c226d69eeb)%Z; (0xbfd1344bb737e8f3)%Z; (0x3fc42aca8b92009b)%Z; (0x3fbc32d8f6819518)%Z; (0xbfc13e9a472e77d3)%Z; (0xbfa17f3d1ae21675)%Z; (0x3fbb664437085a58)%Z; (0xbf83d0eae876d097)%Z; (0x40246e25a1f83e64)%Z] (IZR 596 * bpow radix2 (-76)).
Proof.
  unfold SegOkRowA. cbn [nth].
  destruct (word_ok_intro (0x3fc7b97b4bce5b02)%Z false 6677863668275970%positive 55%nat (3338931834137985)%Z 1%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c5347b0b4f881ca)%Z false 5426848833503690%positive 110%nat (2713424416751845)%Z 1%Z (-109)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3feee9c7f8458e02)%Z false 8701294374391298%positive 53%nat (4350647187195649)%Z 1%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc6163807ba71fe1)%Z true 4894478085595105%positive 109%nat (-4894478085595105)%Z 0%Z (-109)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfc665c226d69eeb)%Z true 6304334037294827%positive 55%nat (-6304334037294827)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbfd1344bb737e8f3)%Z true 4842574405167347%positive 54%nat (-4842574405167347)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fc42aca8b92009b)%Z false 5676548947574939%positive 55%nat (5676548947574939)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3fbc32d8f6819518)%Z false 7937206777910552%positive 56%nat (992150847238819)%Z 3%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbfc13e9a472e77d3)%Z true 4853906944194515%positive 55%nat (-4853906944194515)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0xbfa17f3d1ae21675)%Z true 4924975024838261%positive 57%nat (-4924975024838261)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3fbb664437085a58)%Z false 7712267538291288%positive 56%nat (964033442286411)%Z 3%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0xbf83d0eae876d097)%Z true 5577731898527895%positive 59%nat (-5577731898527895)%Z 0%Z (-59)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x40246e25a1f83e64)%Z false 5750607444459108%positive 49%nat (1437651861114777)%Z 2%Z (-47)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_12 _ _).
  all: seg_numeric.
Qed.

Lemma row_12 : nth (Z.to_nat (12%Z - 1)) atan2_segments [] = [(0x3fc7b97b4bce5b02)%Z; (0x3c5347b0b4f881ca)%Z; (0x3feee9c7f8458e02)%Z; (0xbc6163807ba71fe1)%Z; (0xbfc665c226d69eeb)%Z; (0xbfd1344bb737e8f3)%Z; (0x3fc42aca8b92009b)%Z; (0x3fbc32d8f6819518)%Z; (0xbfc13e9a472e77d3)%Z; (0xbfa17f3d1ae21675)%Z; (0x3fbb664437085a58)%Z; (0xbf83d0eae876d097)%Z; (0x40246e25a1f83e64)%Z].
Proof. reflexivity. Qed.

Lemma fast_12 zh zl : finite zh -> finite zl -> / 128 <= B zh -> B zh <= 1 ->
  Znearest ne (B zh * 64) = 12%Z -> Rabs (B zl) <= bpow radix2 (-53) -> on_grid (-211) (B zl) ->
  exists h l, atan2_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    Rabs (B h + B l - atan (IZR 12 / 64 + ((B zh - IZR 12 / 64) + B zl))) <= bpow radix2 (-63) * atan (IZR 12 / 64 + ((B zh - IZR 12 / 64) + B zl)).
Proof.
  intros Fz Fl L U Hn Hl Hg.
  pose proof (series_segment_a zh zl 12%Z (IZR 596 * bpow radix2 (-76)) ltac:(lia) Fz Fl L U Hn Hl Hg segok_12) as SS.
  cbv zeta in SS. rewrite row_12 in SS. cbn [nth] in SS.
  destruct SS as [h [l [Hs [Fh [Fl' [Nrm [Ht [e1 [ea [E1 [Eea Eq]]]]]]]]]]].
  exists h, l. split; [exact Hs | split; [exact Fh | split; [exact Fl' | split; [exact Nrm | ]]]].
  destruct (word_ok_intro (0x3fc7b97b4bce5b02)%Z false 6677863668275970%positive 55%nat (3338931834137985)%Z 1%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c5347b0b4f881ca)%Z false 5426848833503690%positive 110%nat (2713424416751845)%Z 1%Z (-109)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3feee9c7f8458e02)%Z false 8701294374391298%positive 53%nat (4350647187195649)%Z 1%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc6163807ba71fe1)%Z true 4894478085595105%positive 109%nat (-4894478085595105)%Z 0%Z (-109)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfc665c226d69eeb)%Z true 6304334037294827%positive 55%nat (-6304334037294827)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbfd1344bb737e8f3)%Z true 4842574405167347%positive 54%nat (-4842574405167347)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fc42aca8b92009b)%Z false 5676548947574939%positive 55%nat (5676548947574939)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3fbc32d8f6819518)%Z false 7937206777910552%positive 56%nat (992150847238819)%Z 3%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbfc13e9a472e77d3)%Z true 4853906944194515%positive 55%nat (-4853906944194515)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0xbfa17f3d1ae21675)%Z true 4924975024838261%positive 57%nat (-4924975024838261)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3fbb664437085a58)%Z false 7712267538291288%positive 56%nat (964033442286411)%Z 3%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0xbf83d0eae876d097)%Z true 5577731898527895%positive 59%nat (-5577731898527895)%Z 0%Z (-59)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x40246e25a1f83e64)%Z false 5750607444459108%positive 49%nat (1437651861114777)%Z 2%Z (-47)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  unfold seg_poly in Eq.
  pose proof (approx_12 _ _ _ _ _ _ _ _ _ _ _ _ _ ((B zh - IZR 12 / 64) + B zl) V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 Ht) as AP.
  pose proof (amin_12 ((B zh - IZR 12 / 64) + B zl) Ht) as HAm.
  destruct ea_dw_small as [Ea0 Ea1].
  rewrite Eq.
  refine (fast_compose _ _ e1 ea (IZR 12145559 * bpow radix2 (-95)) (IZR 596 * bpow radix2 (-76)) _ (IZR 745704 * bpow radix2 (-22)) _ AP E1 Eea HAm _ Ea0 _).
  - apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0].
  - bpow_num. replace (- prec)%Z with (-53)%Z by reflexivity. bpow_num. clear - Fz. interval with (i_prec 200).
Qed.

Lemma evalcert_13 : EvalCert (IZR (8650290304201431) * bpow radix2 (-53)) (IZR (2297733362053505) * bpow radix2 (-112)) (IZR (-3374931551275775) * bpow radix2 (-54)) (IZR (-4660524108587131) * bpow radix2 (-54)) (IZR (373042025332689) * bpow radix2 (-51)) (IZR (7016136643532211) * bpow radix2 (-56)) (IZR (-620250737668569) * bpow radix2 (-52)) (IZR (-2988377169941793) * bpow radix2 (-57)) (IZR (7442866831435031) * bpow radix2 (-56)) (IZR (-776303799805443) * bpow radix2 (-55)) (IZR (3051740535379715) * bpow radix2 (-47)) (IZR 637 * bpow radix2 (-76)) (IZR 543 * bpow radix2 (-71)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 637 (-637) (-76)); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_13.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_13.l1 th_ tl_ dg).
Qed.

Lemma segok_13 : SegOkRowA [(0x3fc9a6a8e96c8626)%Z; (0x3c4cf601e7b4348e)%Z; (0x3feebb64a8c932d7)%Z; (0x3c20538d79aae302)%Z; (0xbfc7faf6f88295fe)%Z; (0xbfd08eb8d3f5a07b)%Z; (0x3fc53479d67ffd10)%Z; (0x3fb8ed239c5555b3)%Z; (0xbfc1a0eb071f8ec8)%Z; (0xbf953bd38f56aa42)%Z; (0x3fba713f79992517)%Z; (0xbf96105a81cd3018)%Z; (0x4035af156d1dae06)%Z] (IZR 637 * bpow radix2 (-76)).
Proof.
  unfold SegOkRowA. cbn [nth].
  destruct (word_ok_intro (0x3fc9a6a8e96c8626)%Z false 7220118818686502%positive 55%nat (3610059409343251)%Z 1%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c4cf601e7b4348e)%Z false 8151787390645390%positive 111%nat (4075893695322695)%Z 1%Z (-110)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3feebb64a8c932d7)%Z false 8650290304201431%positive 53%nat (8650290304201431)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c20538d79aae302)%Z false 4595466724107010%positive 113%nat (2297733362053505)%Z 1%Z (-112)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfc7faf6f88295fe)%Z true 6749863102551550%positive 55%nat (-3374931551275775)%Z 1%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbfd08eb8d3f5a07b)%Z true 4660524108587131%positive 54%nat (-4660524108587131)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fc53479d67ffd10)%Z false 5968672405323024%positive 55%nat (373042025332689)%Z 4%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3fb8ed239c5555b3)%Z false 7016136643532211%positive 56%nat (7016136643532211)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbfc1a0eb071f8ec8)%Z true 4962005901348552%positive 55%nat (-620250737668569)%Z 3%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0xbf953bd38f56aa42)%Z true 5976754339883586%positive 58%nat (-2988377169941793)%Z 1%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3fba713f79992517)%Z false 7442866831435031%positive 56%nat (7442866831435031)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0xbf96105a81cd3018)%Z true 6210430398443544%positive 58%nat (-776303799805443)%Z 3%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x4035af156d1dae06)%Z false 6103481070759430%positive 48%nat (3051740535379715)%Z 1%Z (-47)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_13 _ _).
  all: seg_numeric.
Qed.

Lemma row_13 : nth (Z.to_nat (13%Z - 1)) atan2_segments [] = [(0x3fc9a6a8e96c8626)%Z; (0x3c4cf601e7b4348e)%Z; (0x3feebb64a8c932d7)%Z; (0x3c20538d79aae302)%Z; (0xbfc7faf6f88295fe)%Z; (0xbfd08eb8d3f5a07b)%Z; (0x3fc53479d67ffd10)%Z; (0x3fb8ed239c5555b3)%Z; (0xbfc1a0eb071f8ec8)%Z; (0xbf953bd38f56aa42)%Z; (0x3fba713f79992517)%Z; (0xbf96105a81cd3018)%Z; (0x4035af156d1dae06)%Z].
Proof. reflexivity. Qed.

Lemma fast_13 zh zl : finite zh -> finite zl -> / 128 <= B zh -> B zh <= 1 ->
  Znearest ne (B zh * 64) = 13%Z -> Rabs (B zl) <= bpow radix2 (-53) -> on_grid (-211) (B zl) ->
  exists h l, atan2_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    Rabs (B h + B l - atan (IZR 13 / 64 + ((B zh - IZR 13 / 64) + B zl))) <= bpow radix2 (-63) * atan (IZR 13 / 64 + ((B zh - IZR 13 / 64) + B zl)).
Proof.
  intros Fz Fl L U Hn Hl Hg.
  pose proof (series_segment_a zh zl 13%Z (IZR 637 * bpow radix2 (-76)) ltac:(lia) Fz Fl L U Hn Hl Hg segok_13) as SS.
  cbv zeta in SS. rewrite row_13 in SS. cbn [nth] in SS.
  destruct SS as [h [l [Hs [Fh [Fl' [Nrm [Ht [e1 [ea [E1 [Eea Eq]]]]]]]]]]].
  exists h, l. split; [exact Hs | split; [exact Fh | split; [exact Fl' | split; [exact Nrm | ]]]].
  destruct (word_ok_intro (0x3fc9a6a8e96c8626)%Z false 7220118818686502%positive 55%nat (3610059409343251)%Z 1%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c4cf601e7b4348e)%Z false 8151787390645390%positive 111%nat (4075893695322695)%Z 1%Z (-110)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3feebb64a8c932d7)%Z false 8650290304201431%positive 53%nat (8650290304201431)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c20538d79aae302)%Z false 4595466724107010%positive 113%nat (2297733362053505)%Z 1%Z (-112)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfc7faf6f88295fe)%Z true 6749863102551550%positive 55%nat (-3374931551275775)%Z 1%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbfd08eb8d3f5a07b)%Z true 4660524108587131%positive 54%nat (-4660524108587131)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fc53479d67ffd10)%Z false 5968672405323024%positive 55%nat (373042025332689)%Z 4%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3fb8ed239c5555b3)%Z false 7016136643532211%positive 56%nat (7016136643532211)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbfc1a0eb071f8ec8)%Z true 4962005901348552%positive 55%nat (-620250737668569)%Z 3%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0xbf953bd38f56aa42)%Z true 5976754339883586%positive 58%nat (-2988377169941793)%Z 1%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3fba713f79992517)%Z false 7442866831435031%positive 56%nat (7442866831435031)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0xbf96105a81cd3018)%Z true 6210430398443544%positive 58%nat (-776303799805443)%Z 3%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x4035af156d1dae06)%Z false 6103481070759430%positive 48%nat (3051740535379715)%Z 1%Z (-47)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  unfold seg_poly in Eq.
  pose proof (approx_13 _ _ _ _ _ _ _ _ _ _ _ _ _ ((B zh - IZR 13 / 64) + B zl) V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 Ht) as AP.
  pose proof (amin_13 ((B zh - IZR 13 / 64) + B zl) Ht) as HAm.
  destruct ea_dw_small as [Ea0 Ea1].
  rewrite Eq.
  refine (fast_compose _ _ e1 ea (IZR 12834142 * bpow radix2 (-94)) (IZR 637 * bpow radix2 (-76)) _ (IZR 809014 * bpow radix2 (-22)) _ AP E1 Eea HAm _ Ea0 _).
  - apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0].
  - bpow_num. replace (- prec)%Z with (-53)%Z by reflexivity. bpow_num. clear - Fz. interval with (i_prec 200).
Qed.

Lemma evalcert_14 : EvalCert (IZR (4297936643455161) * bpow radix2 (-52)) (IZR (2535111067038005) * bpow radix2 (-106)) (IZR (-3588957346258923) * bpow radix2 (-54)) (IZR (-2234955375791293) * bpow radix2 (-53)) (IZR (3112242473267141) * bpow radix2 (-54)) (IZR (189991316790621) * bpow radix2 (-51)) (IZR (-5017828309562461) * bpow radix2 (-55)) (IZR (-2211324384051107) * bpow radix2 (-58)) (IZR (7381747551193545) * bpow radix2 (-56)) (IZR (-4700068710827499) * bpow radix2 (-57)) (IZR (73646732880635) * bpow radix2 (-48)) (IZR 677 * bpow radix2 (-76)) (IZR 521 * bpow radix2 (-71)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 677 (-677) (-76)); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_14.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_14.l1 th_ tl_ dg).
Qed.

Lemma segok_14 : SegOkRowA [(0x3fcb90d7529260a2)%Z; (0x3c217b10d2e0e5ab)%Z; (0x3fee89e6b5ccf172)%Z; (0x3c820357153be26a)%Z; (0xbfc980467f79bfd6)%Z; (0xbfcfc2b8650d32f4)%Z; (0x3fc61d22d625df8a)%Z; (0x3fb599799e53aba0)%Z; (0xbfc1d3b031ef745d)%Z; (0xbf7f6cc05193fe8c)%Z; (0x3fba39a9089c49c9)%Z; (0xbfa0b2b005edc5eb)%Z; (0x3fd0becdd68abec0)%Z] (IZR 677 * bpow radix2 (-76)).
Proof.
  unfold SegOkRowA. cbn [nth].
  destruct (word_ok_intro (0x3fcb90d7529260a2)%Z false 7759078848880802%positive 55%nat (3879539424440401)%Z 1%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c217b10d2e0e5ab)%Z false 4920386791728555%positive 113%nat (4920386791728555)%Z 0%Z (-113)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fee89e6b5ccf172)%Z false 8595873286910322%positive 53%nat (4297936643455161)%Z 1%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c820357153be26a)%Z false 5070222134076010%positive 107%nat (2535111067038005)%Z 1%Z (-106)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfc980467f79bfd6)%Z true 7177914692517846%positive 55%nat (-3588957346258923)%Z 1%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbfcfc2b8650d32f4)%Z true 8939821503165172%positive 55%nat (-2234955375791293)%Z 2%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fc61d22d625df8a)%Z false 6224484946534282%positive 55%nat (3112242473267141)%Z 1%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3fb599799e53aba0)%Z false 6079722137299872%positive 56%nat (189991316790621)%Z 5%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbfc1d3b031ef745d)%Z true 5017828309562461%positive 55%nat (-5017828309562461)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0xbf7f6cc05193fe8c)%Z true 8845297536204428%positive 60%nat (-2211324384051107)%Z 2%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3fba39a9089c49c9)%Z false 7381747551193545%positive 56%nat (7381747551193545)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0xbfa0b2b005edc5eb)%Z true 4700068710827499%positive 57%nat (-4700068710827499)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x3fd0becdd68abec0)%Z false 4713390904360640%positive 54%nat (73646732880635)%Z 6%Z (-48)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_14 _ _).
  all: seg_numeric.
Qed.

Lemma row_14 : nth (Z.to_nat (14%Z - 1)) atan2_segments [] = [(0x3fcb90d7529260a2)%Z; (0x3c217b10d2e0e5ab)%Z; (0x3fee89e6b5ccf172)%Z; (0x3c820357153be26a)%Z; (0xbfc980467f79bfd6)%Z; (0xbfcfc2b8650d32f4)%Z; (0x3fc61d22d625df8a)%Z; (0x3fb599799e53aba0)%Z; (0xbfc1d3b031ef745d)%Z; (0xbf7f6cc05193fe8c)%Z; (0x3fba39a9089c49c9)%Z; (0xbfa0b2b005edc5eb)%Z; (0x3fd0becdd68abec0)%Z].
Proof. reflexivity. Qed.

Lemma fast_14 zh zl : finite zh -> finite zl -> / 128 <= B zh -> B zh <= 1 ->
  Znearest ne (B zh * 64) = 14%Z -> Rabs (B zl) <= bpow radix2 (-53) -> on_grid (-211) (B zl) ->
  exists h l, atan2_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    Rabs (B h + B l - atan (IZR 14 / 64 + ((B zh - IZR 14 / 64) + B zl))) <= bpow radix2 (-63) * atan (IZR 14 / 64 + ((B zh - IZR 14 / 64) + B zl)).
Proof.
  intros Fz Fl L U Hn Hl Hg.
  pose proof (series_segment_a zh zl 14%Z (IZR 677 * bpow radix2 (-76)) ltac:(lia) Fz Fl L U Hn Hl Hg segok_14) as SS.
  cbv zeta in SS. rewrite row_14 in SS. cbn [nth] in SS.
  destruct SS as [h [l [Hs [Fh [Fl' [Nrm [Ht [e1 [ea [E1 [Eea Eq]]]]]]]]]]].
  exists h, l. split; [exact Hs | split; [exact Fh | split; [exact Fl' | split; [exact Nrm | ]]]].
  destruct (word_ok_intro (0x3fcb90d7529260a2)%Z false 7759078848880802%positive 55%nat (3879539424440401)%Z 1%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c217b10d2e0e5ab)%Z false 4920386791728555%positive 113%nat (4920386791728555)%Z 0%Z (-113)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fee89e6b5ccf172)%Z false 8595873286910322%positive 53%nat (4297936643455161)%Z 1%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c820357153be26a)%Z false 5070222134076010%positive 107%nat (2535111067038005)%Z 1%Z (-106)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfc980467f79bfd6)%Z true 7177914692517846%positive 55%nat (-3588957346258923)%Z 1%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbfcfc2b8650d32f4)%Z true 8939821503165172%positive 55%nat (-2234955375791293)%Z 2%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fc61d22d625df8a)%Z false 6224484946534282%positive 55%nat (3112242473267141)%Z 1%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3fb599799e53aba0)%Z false 6079722137299872%positive 56%nat (189991316790621)%Z 5%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbfc1d3b031ef745d)%Z true 5017828309562461%positive 55%nat (-5017828309562461)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0xbf7f6cc05193fe8c)%Z true 8845297536204428%positive 60%nat (-2211324384051107)%Z 2%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3fba39a9089c49c9)%Z false 7381747551193545%positive 56%nat (7381747551193545)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0xbfa0b2b005edc5eb)%Z true 4700068710827499%positive 57%nat (-4700068710827499)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x3fd0becdd68abec0)%Z false 4713390904360640%positive 54%nat (73646732880635)%Z 6%Z (-48)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  unfold seg_poly in Eq.
  pose proof (approx_14 _ _ _ _ _ _ _ _ _ _ _ _ _ ((B zh - IZR 14 / 64) + B zl) V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 Ht) as AP.
  pose proof (amin_14 ((B zh - IZR 14 / 64) + B zl) Ht) as HAm.
  destruct ea_dw_small as [Ea0 Ea1].
  rewrite Eq.
  refine (fast_compose _ _ e1 ea (IZR 12451798 * bpow radix2 (-100)) (IZR 677 * bpow radix2 (-76)) _ (IZR 871952 * bpow radix2 (-22)) _ AP E1 Eea HAm _ Ea0 _).
  - apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0].
  - bpow_num. replace (- prec)%Z with (-53)%Z by reflexivity. bpow_num. clear - Fz. interval with (i_prec 200).
Qed.

Lemma evalcert_15 : EvalCert (IZR (4269091431082979) * bpow radix2 (-52)) (IZR (-5361378496457725) * bpow radix2 (-107)) (IZR (-7587739456310409) * bpow radix2 (-55)) (IZR (-8543752873678553) * bpow radix2 (-55)) (IZR (6443576612950217) * bpow radix2 (-55)) (IZR (1284400993394621) * bpow radix2 (-54)) (IZR (-5023221323153543) * bpow radix2 (-55)) (IZR (5563198311700309) * bpow radix2 (-60)) (IZR (3484880403387809) * bpow radix2 (-55)) (IZR (-376873249359707) * bpow radix2 (-53)) (IZR (2103396006319135) * bpow radix2 (-49)) (IZR 715 * bpow radix2 (-76)) (IZR 996 * bpow radix2 (-72)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 715 (-715) (-76)); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_15.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_15.l1 th_ tl_ dg).
Qed.

Lemma segok_15 : SegOkRowA [(0x3fcd77d5df205736)%Z; (0x3c6c648d1534597e)%Z; (0x3fee556e9c86d7c6)%Z; (0xbc830c2534c9abfd)%Z; (0xbfcaf50242f10c89)%Z; (0xbfce5a7f7b1596d9)%Z; (0x3fc6e466171910c9)%Z; (0x3fb2409fa3d77ef4)%Z; (0xbfc1d897da984087)%Z; (0x3f73c3b30b2f1755)%Z; (0x3fb8c2f5e50eab42)%Z; (0xbfa56c3a427475b0)%Z; (0x400de41c2f1d507c)%Z] (IZR 715 * bpow radix2 (-76)).
Proof.
  unfold SegOkRowA. cbn [nth].
  destruct (word_ok_intro (0x3fcd77d5df205736)%Z false 8294534779787062%positive 55%nat (4147267389893531)%Z 1%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c6c648d1534597e)%Z false 7991856456817022%positive 109%nat (3995928228408511)%Z 1%Z (-108)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fee556e9c86d7c6)%Z false 8538182862165958%positive 53%nat (4269091431082979)%Z 1%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc830c2534c9abfd)%Z true 5361378496457725%positive 107%nat (-5361378496457725)%Z 0%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfcaf50242f10c89)%Z true 7587739456310409%positive 55%nat (-7587739456310409)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbfce5a7f7b1596d9)%Z true 8543752873678553%positive 55%nat (-8543752873678553)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fc6e466171910c9)%Z false 6443576612950217%positive 55%nat (6443576612950217)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3fb2409fa3d77ef4)%Z false 5137603973578484%positive 56%nat (1284400993394621)%Z 2%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbfc1d897da984087)%Z true 5023221323153543%positive 55%nat (-5023221323153543)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3f73c3b30b2f1755)%Z false 5563198311700309%positive 60%nat (5563198311700309)%Z 0%Z (-60)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3fb8c2f5e50eab42)%Z false 6969760806775618%positive 56%nat (3484880403387809)%Z 1%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0xbfa56c3a427475b0)%Z true 6029971989755312%positive 57%nat (-376873249359707)%Z 4%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x400de41c2f1d507c)%Z false 8413584025276540%positive 51%nat (2103396006319135)%Z 2%Z (-49)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_15 _ _).
  all: seg_numeric.
Qed.

Lemma row_15 : nth (Z.to_nat (15%Z - 1)) atan2_segments [] = [(0x3fcd77d5df205736)%Z; (0x3c6c648d1534597e)%Z; (0x3fee556e9c86d7c6)%Z; (0xbc830c2534c9abfd)%Z; (0xbfcaf50242f10c89)%Z; (0xbfce5a7f7b1596d9)%Z; (0x3fc6e466171910c9)%Z; (0x3fb2409fa3d77ef4)%Z; (0xbfc1d897da984087)%Z; (0x3f73c3b30b2f1755)%Z; (0x3fb8c2f5e50eab42)%Z; (0xbfa56c3a427475b0)%Z; (0x400de41c2f1d507c)%Z].
Proof. reflexivity. Qed.

Lemma fast_15 zh zl : finite zh -> finite zl -> / 128 <= B zh -> B zh <= 1 ->
  Znearest ne (B zh * 64) = 15%Z -> Rabs (B zl) <= bpow radix2 (-53) -> on_grid (-211) (B zl) ->
  exists h l, atan2_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    Rabs (B h + B l - atan (IZR 15 / 64 + ((B zh - IZR 15 / 64) + B zl))) <= bpow radix2 (-63) * atan (IZR 15 / 64 + ((B zh - IZR 15 / 64) + B zl)).
Proof.
  intros Fz Fl L U Hn Hl Hg.
  pose proof (series_segment_a zh zl 15%Z (IZR 715 * bpow radix2 (-76)) ltac:(lia) Fz Fl L U Hn Hl Hg segok_15) as SS.
  cbv zeta in SS. rewrite row_15 in SS. cbn [nth] in SS.
  destruct SS as [h [l [Hs [Fh [Fl' [Nrm [Ht [e1 [ea [E1 [Eea Eq]]]]]]]]]]].
  exists h, l. split; [exact Hs | split; [exact Fh | split; [exact Fl' | split; [exact Nrm | ]]]].
  destruct (word_ok_intro (0x3fcd77d5df205736)%Z false 8294534779787062%positive 55%nat (4147267389893531)%Z 1%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c6c648d1534597e)%Z false 7991856456817022%positive 109%nat (3995928228408511)%Z 1%Z (-108)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fee556e9c86d7c6)%Z false 8538182862165958%positive 53%nat (4269091431082979)%Z 1%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc830c2534c9abfd)%Z true 5361378496457725%positive 107%nat (-5361378496457725)%Z 0%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfcaf50242f10c89)%Z true 7587739456310409%positive 55%nat (-7587739456310409)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbfce5a7f7b1596d9)%Z true 8543752873678553%positive 55%nat (-8543752873678553)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fc6e466171910c9)%Z false 6443576612950217%positive 55%nat (6443576612950217)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3fb2409fa3d77ef4)%Z false 5137603973578484%positive 56%nat (1284400993394621)%Z 2%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbfc1d897da984087)%Z true 5023221323153543%positive 55%nat (-5023221323153543)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3f73c3b30b2f1755)%Z false 5563198311700309%positive 60%nat (5563198311700309)%Z 0%Z (-60)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3fb8c2f5e50eab42)%Z false 6969760806775618%positive 56%nat (3484880403387809)%Z 1%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0xbfa56c3a427475b0)%Z true 6029971989755312%positive 57%nat (-376873249359707)%Z 4%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x400de41c2f1d507c)%Z false 8413584025276540%positive 51%nat (2103396006319135)%Z 2%Z (-49)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  unfold seg_poly in Eq.
  pose proof (approx_15 _ _ _ _ _ _ _ _ _ _ _ _ _ ((B zh - IZR 15 / 64) + B zl) V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 Ht) as AP.
  pose proof (amin_15 ((B zh - IZR 15 / 64) + B zl) Ht) as HAm.
  destruct ea_dw_small as [Ea0 Ea1].
  rewrite Eq.
  refine (fast_compose _ _ e1 ea (IZR 8950851 * bpow radix2 (-96)) (IZR 715 * bpow radix2 (-76)) _ (IZR 934494 * bpow radix2 (-22)) _ AP E1 Eea HAm _ Ea0 _).
  - apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0].
  - bpow_num. replace (- prec)%Z with (-53)%Z by reflexivity. bpow_num. clear - Fz. interval with (i_prec 200).
Qed.

Lemma evalcert_16 : EvalCert (IZR (4238682002231055) * bpow radix2 (-52)) (IZR (4238682002231055) * bpow radix2 (-108)) (IZR (-3989347766805699) * bpow radix2 (-54)) (IZR (-4067570272037183) * bpow radix2 (-54)) (IZR (3312953162771673) * bpow radix2 (-54)) (IZR (8398011468095751) * bpow radix2 (-57)) (IZR (-4980768998397751) * bpow radix2 (-55)) (IZR (4780950832887209) * bpow radix2 (-58)) (IZR (3337930558025369) * bpow radix2 (-55)) (IZR (-7251804897516987) * bpow radix2 (-57)) (IZR (-1945753261953285) * bpow radix2 (-47)) (IZR 751 * bpow radix2 (-76)) (IZR 949 * bpow radix2 (-72)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 751 (-751) (-76)); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_16.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_16.l1 th_ tl_ dg).
Qed.

Lemma segok_16 : SegOkRowA [(0x3fcf5b75f92c80dd)%Z; (0x3c68ab6e3cf7afbd)%Z; (0x3fee1e1e1e1e1e1e)%Z; (0x3c6e1e1e1e1e1e1e)%Z; (0xbfcc5894d10d4986)%Z; (0xbfcce6de0253d27e)%Z; (0x3fc78a3a08d959b2)%Z; (0x3fadd5f26a602107)%Z; (0xbfc1b1fba6db9737)%Z; (0x3f90fc3fdc1535a9)%Z; (0x3fb7b7a90a645d32)%Z; (0xbfa9c37a66e59dbb)%Z; (0xc02ba69befff4414)%Z] (IZR 751 * bpow radix2 (-76)).
Proof.
  unfold SegOkRowA. cbn [nth].
  destruct (word_ok_intro (0x3fcf5b75f92c80dd)%Z false 8826286527774941%positive 55%nat (8826286527774941)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c68ab6e3cf7afbd)%Z false 6943889398673341%positive 109%nat (6943889398673341)%Z 0%Z (-109)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fee1e1e1e1e1e1e)%Z false 8477364004462110%positive 53%nat (4238682002231055)%Z 1%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c6e1e1e1e1e1e1e)%Z false 8477364004462110%positive 109%nat (4238682002231055)%Z 1%Z (-108)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfcc5894d10d4986)%Z true 7978695533611398%positive 55%nat (-3989347766805699)%Z 1%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbfcce6de0253d27e)%Z true 8135140544074366%positive 55%nat (-4067570272037183)%Z 1%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fc78a3a08d959b2)%Z false 6625906325543346%positive 55%nat (3312953162771673)%Z 1%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3fadd5f26a602107)%Z false 8398011468095751%positive 57%nat (8398011468095751)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbfc1b1fba6db9737)%Z true 4980768998397751%positive 55%nat (-4980768998397751)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3f90fc3fdc1535a9)%Z false 4780950832887209%positive 58%nat (4780950832887209)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3fb7b7a90a645d32)%Z false 6675861116050738%positive 56%nat (3337930558025369)%Z 1%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0xbfa9c37a66e59dbb)%Z true 7251804897516987%positive 57%nat (-7251804897516987)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc02ba69befff4414)%Z true 7783013047813140%positive 49%nat (-1945753261953285)%Z 2%Z (-47)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_16 _ _).
  all: seg_numeric.
Qed.

Lemma row_16 : nth (Z.to_nat (16%Z - 1)) atan2_segments [] = [(0x3fcf5b75f92c80dd)%Z; (0x3c68ab6e3cf7afbd)%Z; (0x3fee1e1e1e1e1e1e)%Z; (0x3c6e1e1e1e1e1e1e)%Z; (0xbfcc5894d10d4986)%Z; (0xbfcce6de0253d27e)%Z; (0x3fc78a3a08d959b2)%Z; (0x3fadd5f26a602107)%Z; (0xbfc1b1fba6db9737)%Z; (0x3f90fc3fdc1535a9)%Z; (0x3fb7b7a90a645d32)%Z; (0xbfa9c37a66e59dbb)%Z; (0xc02ba69befff4414)%Z].
Proof. reflexivity. Qed.

Lemma fast_16 zh zl : finite zh -> finite zl -> / 128 <= B zh -> B zh <= 1 ->
  Znearest ne (B zh * 64) = 16%Z -> Rabs (B zl) <= bpow radix2 (-53) -> on_grid (-211) (B zl) ->
  exists h l, atan2_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    Rabs (B h + B l - atan (IZR 16 / 64 + ((B zh - IZR 16 / 64) + B zl))) <= bpow radix2 (-63) * atan (IZR 16 / 64 + ((B zh - IZR 16 / 64) + B zl)).
Proof.
  intros Fz Fl L U Hn Hl Hg.
  pose proof (series_segment_a zh zl 16%Z (IZR 751 * bpow radix2 (-76)) ltac:(lia) Fz Fl L U Hn Hl Hg segok_16) as SS.
  cbv zeta in SS. rewrite row_16 in SS. cbn [nth] in SS.
  destruct SS as [h [l [Hs [Fh [Fl' [Nrm [Ht [e1 [ea [E1 [Eea Eq]]]]]]]]]]].
  exists h, l. split; [exact Hs | split; [exact Fh | split; [exact Fl' | split; [exact Nrm | ]]]].
  destruct (word_ok_intro (0x3fcf5b75f92c80dd)%Z false 8826286527774941%positive 55%nat (8826286527774941)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c68ab6e3cf7afbd)%Z false 6943889398673341%positive 109%nat (6943889398673341)%Z 0%Z (-109)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fee1e1e1e1e1e1e)%Z false 8477364004462110%positive 53%nat (4238682002231055)%Z 1%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c6e1e1e1e1e1e1e)%Z false 8477364004462110%positive 109%nat (4238682002231055)%Z 1%Z (-108)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfcc5894d10d4986)%Z true 7978695533611398%positive 55%nat (-3989347766805699)%Z 1%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbfcce6de0253d27e)%Z true 8135140544074366%positive 55%nat (-4067570272037183)%Z 1%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fc78a3a08d959b2)%Z false 6625906325543346%positive 55%nat (3312953162771673)%Z 1%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3fadd5f26a602107)%Z false 8398011468095751%positive 57%nat (8398011468095751)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbfc1b1fba6db9737)%Z true 4980768998397751%positive 55%nat (-4980768998397751)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3f90fc3fdc1535a9)%Z false 4780950832887209%positive 58%nat (4780950832887209)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3fb7b7a90a645d32)%Z false 6675861116050738%positive 56%nat (3337930558025369)%Z 1%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0xbfa9c37a66e59dbb)%Z true 7251804897516987%positive 57%nat (-7251804897516987)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc02ba69befff4414)%Z true 7783013047813140%positive 49%nat (-1945753261953285)%Z 2%Z (-47)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  unfold seg_poly in Eq.
  pose proof (approx_16 _ _ _ _ _ _ _ _ _ _ _ _ _ ((B zh - IZR 16 / 64) + B zl) V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 Ht) as AP.
  pose proof (amin_16 ((B zh - IZR 16 / 64) + B zl) Ht) as HAm.
  destruct ea_dw_small as [Ea0 Ea1].
  rewrite Eq.
  refine (fast_compose _ _ e1 ea (IZR 16255197 * bpow radix2 (-95)) (IZR 751 * bpow radix2 (-76)) _ (IZR 996616 * bpow radix2 (-22)) _ AP E1 Eea HAm _ Ea0 _).
  - apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0].
  - bpow_num. replace (- prec)%Z with (-53)%Z by reflexivity. bpow_num. clear - Fz. interval with (i_prec 200).
Qed.

Lemma evalcert_17 : EvalCert (IZR (4206783141096819) * bpow radix2 (-52)) (IZR (309141046257359) * bpow radix2 (-104)) (IZR (-4175124339806923) * bpow radix2 (-54)) (IZR (-1929068561645403) * bpow radix2 (-53)) (IZR (6771783093866819) * bpow radix2 (-55)) (IZR (6545218315677847) * bpow radix2 (-57)) (IZR (-4893652862460237) * bpow radix2 (-55)) (IZR (7917898724680017) * bpow radix2 (-58)) (IZR (3097217383227697) * bpow radix2 (-55)) (IZR (-4101170408258213) * bpow radix2 (-56)) (IZR (-5620890705437541) * bpow radix2 (-48)) (IZR 785 * bpow radix2 (-76)) (IZR 901 * bpow radix2 (-72)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 785 (-785) (-76)); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_17.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_17.l1 th_ tl_ dg).
Qed.

Lemma segok_17 : SegOkRowA [(0x3fd09dc597d86362)%Z; (0x3c762e47390cb865)%Z; (0x3fede4180d8b5ae6)%Z; (0x3c71929823f66cf0)%Z; (0xbfcdaa81c655a596)%Z; (0xbfcb69e91974fd6c)%Z; (0x3fc80ee69dce5143)%Z; (0x3fa740d764aef097)%Z; (0xbfc162c05885614d)%Z; (0x3f9c214974da2151)%Z; (0x3fb601ce3bd6c262)%Z; (0xbfad23fc4ab1f54a)%Z; (0xc033f82b99d1a365)%Z] (IZR 785 * bpow radix2 (-76)).
Proof.
  unfold SegOkRowA. cbn [nth].
  destruct (word_ok_intro (0x3fd09dc597d86362)%Z false 4677071609029474%positive 54%nat (2338535804514737)%Z 1%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c762e47390cb865)%Z false 6243332922325093%positive 108%nat (6243332922325093)%Z 0%Z (-108)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fede4180d8b5ae6)%Z false 8413566282193638%positive 53%nat (4206783141096819)%Z 1%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c71929823f66cf0)%Z false 4946256740117744%positive 108%nat (309141046257359)%Z 4%Z (-104)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfcdaa81c655a596)%Z true 8350248679613846%positive 55%nat (-4175124339806923)%Z 1%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbfcb69e91974fd6c)%Z true 7716274246581612%positive 55%nat (-1929068561645403)%Z 2%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fc80ee69dce5143)%Z false 6771783093866819%positive 55%nat (6771783093866819)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3fa740d764aef097)%Z false 6545218315677847%positive 57%nat (6545218315677847)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbfc162c05885614d)%Z true 4893652862460237%positive 55%nat (-4893652862460237)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3f9c214974da2151)%Z false 7917898724680017%positive 58%nat (7917898724680017)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3fb601ce3bd6c262)%Z false 6194434766455394%positive 56%nat (3097217383227697)%Z 1%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0xbfad23fc4ab1f54a)%Z true 8202340816516426%positive 57%nat (-4101170408258213)%Z 1%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc033f82b99d1a365)%Z true 5620890705437541%positive 48%nat (-5620890705437541)%Z 0%Z (-48)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_17 _ _).
  all: seg_numeric.
Qed.

Lemma row_17 : nth (Z.to_nat (17%Z - 1)) atan2_segments [] = [(0x3fd09dc597d86362)%Z; (0x3c762e47390cb865)%Z; (0x3fede4180d8b5ae6)%Z; (0x3c71929823f66cf0)%Z; (0xbfcdaa81c655a596)%Z; (0xbfcb69e91974fd6c)%Z; (0x3fc80ee69dce5143)%Z; (0x3fa740d764aef097)%Z; (0xbfc162c05885614d)%Z; (0x3f9c214974da2151)%Z; (0x3fb601ce3bd6c262)%Z; (0xbfad23fc4ab1f54a)%Z; (0xc033f82b99d1a365)%Z].
Proof. reflexivity. Qed.

Lemma fast_17 zh zl : finite zh -> finite zl -> / 128 <= B zh -> B zh <= 1 ->
  Znearest ne (B zh * 64) = 17%Z -> Rabs (B zl) <= bpow radix2 (-53) -> on_grid (-211) (B zl) ->
  exists h l, atan2_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    Rabs (B h + B l - atan (IZR 17 / 64 + ((B zh - IZR 17 / 64) + B zl))) <= bpow radix2 (-63) * atan (IZR 17 / 64 + ((B zh - IZR 17 / 64) + B zl)).
Proof.
  intros Fz Fl L U Hn Hl Hg.
  pose proof (series_segment_a zh zl 17%Z (IZR 785 * bpow radix2 (-76)) ltac:(lia) Fz Fl L U Hn Hl Hg segok_17) as SS.
  cbv zeta in SS. rewrite row_17 in SS. cbn [nth] in SS.
  destruct SS as [h [l [Hs [Fh [Fl' [Nrm [Ht [e1 [ea [E1 [Eea Eq]]]]]]]]]]].
  exists h, l. split; [exact Hs | split; [exact Fh | split; [exact Fl' | split; [exact Nrm | ]]]].
  destruct (word_ok_intro (0x3fd09dc597d86362)%Z false 4677071609029474%positive 54%nat (2338535804514737)%Z 1%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c762e47390cb865)%Z false 6243332922325093%positive 108%nat (6243332922325093)%Z 0%Z (-108)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fede4180d8b5ae6)%Z false 8413566282193638%positive 53%nat (4206783141096819)%Z 1%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c71929823f66cf0)%Z false 4946256740117744%positive 108%nat (309141046257359)%Z 4%Z (-104)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfcdaa81c655a596)%Z true 8350248679613846%positive 55%nat (-4175124339806923)%Z 1%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbfcb69e91974fd6c)%Z true 7716274246581612%positive 55%nat (-1929068561645403)%Z 2%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fc80ee69dce5143)%Z false 6771783093866819%positive 55%nat (6771783093866819)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3fa740d764aef097)%Z false 6545218315677847%positive 57%nat (6545218315677847)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbfc162c05885614d)%Z true 4893652862460237%positive 55%nat (-4893652862460237)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3f9c214974da2151)%Z false 7917898724680017%positive 58%nat (7917898724680017)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3fb601ce3bd6c262)%Z false 6194434766455394%positive 56%nat (3097217383227697)%Z 1%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0xbfad23fc4ab1f54a)%Z true 8202340816516426%positive 57%nat (-4101170408258213)%Z 1%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc033f82b99d1a365)%Z true 5620890705437541%positive 48%nat (-5620890705437541)%Z 0%Z (-48)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  unfold seg_poly in Eq.
  pose proof (approx_17 _ _ _ _ _ _ _ _ _ _ _ _ _ ((B zh - IZR 17 / 64) + B zl) V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 Ht) as AP.
  pose proof (amin_17 ((B zh - IZR 17 / 64) + B zl) Ht) as HAm.
  destruct ea_dw_small as [Ea0 Ea1].
  rewrite Eq.
  refine (fast_compose _ _ e1 ea (IZR 11757993 * bpow radix2 (-94)) (IZR 785 * bpow radix2 (-76)) _ (IZR 529147 * bpow radix2 (-21)) _ AP E1 Eea HAm _ Ea0 _).
  - apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0].
  - bpow_num. replace (- prec)%Z with (-53)%Z by reflexivity. bpow_num. clear - Fz. interval with (i_prec 200).
Qed.

Lemma evalcert_18 : EvalCert (IZR (4173471509889039) * bpow radix2 (-52)) (IZR (-3113801009331275) * bpow radix2 (-106)) (IZR (-8701971365415697) * bpow radix2 (-55)) (IZR (-7289414056124321) * bpow radix2 (-55)) (IZR (6881842725139331) * bpow radix2 (-55)) (IZR (4732897261015489) * bpow radix2 (-57)) (IZR (-74461945570835) * bpow radix2 (-49)) (IZR (2692097012190501) * bpow radix2 (-56)) (IZR (5257517316827139) * bpow radix2 (-56)) (IZR (-8844567937328877) * bpow radix2 (-57)) (IZR (1972358009248669) * bpow radix2 (-47)) (IZR 818 * bpow radix2 (-76)) (IZR 852 * bpow radix2 (-72)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 409 (-409) (-75)); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_18.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_18.l1 th_ tl_ dg).
Qed.

Lemma segok_18 : SegOkRowA [(0x3fd18bf5a30bf178)%Z; (0x3c630ca4748b1bf9)%Z; (0x3feda7801da7801e)%Z; (0xbc861ff8961ff896)%Z; (0xbfceea659814cb11)%Z; (0xbfc9e5aef76f9fa1)%Z; (0x3fc872ffdf083383)%Z; (0x3fa0d08b840051c1)%Z; (0xbfc0ee41742984c0)%Z; (0x3fa320e55c399a4a)%Z; (0x3fb2adaf2411e803)%Z; (0xbfaf6c167218a6ed)%Z; (0x402c07658a0b6e74)%Z] (IZR 818 * bpow radix2 (-76)).
Proof.
  unfold SegOkRowA. cbn [nth].
  destruct (word_ok_intro (0x3fd18bf5a30bf178)%Z false 4938961722798456%positive 54%nat (617370215349807)%Z 3%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c630ca4748b1bf9)%Z false 5361925026946041%positive 109%nat (5361925026946041)%Z 0%Z (-109)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3feda7801da7801e)%Z false 8346943019778078%positive 53%nat (4173471509889039)%Z 1%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc861ff8961ff896)%Z true 6227602018662550%positive 107%nat (-3113801009331275)%Z 1%Z (-106)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfceea659814cb11)%Z true 8701971365415697%positive 55%nat (-8701971365415697)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbfc9e5aef76f9fa1)%Z true 7289414056124321%positive 55%nat (-7289414056124321)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fc872ffdf083383)%Z false 6881842725139331%positive 55%nat (6881842725139331)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3fa0d08b840051c1)%Z false 4732897261015489%positive 57%nat (4732897261015489)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbfc0ee41742984c0)%Z true 4765564516533440%positive 55%nat (-74461945570835)%Z 6%Z (-49)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3fa320e55c399a4a)%Z false 5384194024381002%positive 57%nat (2692097012190501)%Z 1%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3fb2adaf2411e803)%Z false 5257517316827139%positive 56%nat (5257517316827139)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0xbfaf6c167218a6ed)%Z true 8844567937328877%positive 57%nat (-8844567937328877)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x402c07658a0b6e74)%Z false 7889432036994676%positive 49%nat (1972358009248669)%Z 2%Z (-47)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_18 _ _).
  all: seg_numeric.
Qed.

Lemma row_18 : nth (Z.to_nat (18%Z - 1)) atan2_segments [] = [(0x3fd18bf5a30bf178)%Z; (0x3c630ca4748b1bf9)%Z; (0x3feda7801da7801e)%Z; (0xbc861ff8961ff896)%Z; (0xbfceea659814cb11)%Z; (0xbfc9e5aef76f9fa1)%Z; (0x3fc872ffdf083383)%Z; (0x3fa0d08b840051c1)%Z; (0xbfc0ee41742984c0)%Z; (0x3fa320e55c399a4a)%Z; (0x3fb2adaf2411e803)%Z; (0xbfaf6c167218a6ed)%Z; (0x402c07658a0b6e74)%Z].
Proof. reflexivity. Qed.

Lemma fast_18 zh zl : finite zh -> finite zl -> / 128 <= B zh -> B zh <= 1 ->
  Znearest ne (B zh * 64) = 18%Z -> Rabs (B zl) <= bpow radix2 (-53) -> on_grid (-211) (B zl) ->
  exists h l, atan2_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    Rabs (B h + B l - atan (IZR 18 / 64 + ((B zh - IZR 18 / 64) + B zl))) <= bpow radix2 (-63) * atan (IZR 18 / 64 + ((B zh - IZR 18 / 64) + B zl)).
Proof.
  intros Fz Fl L U Hn Hl Hg.
  pose proof (series_segment_a zh zl 18%Z (IZR 818 * bpow radix2 (-76)) ltac:(lia) Fz Fl L U Hn Hl Hg segok_18) as SS.
  cbv zeta in SS. rewrite row_18 in SS. cbn [nth] in SS.
  destruct SS as [h [l [Hs [Fh [Fl' [Nrm [Ht [e1 [ea [E1 [Eea Eq]]]]]]]]]]].
  exists h, l. split; [exact Hs | split; [exact Fh | split; [exact Fl' | split; [exact Nrm | ]]]].
  destruct (word_ok_intro (0x3fd18bf5a30bf178)%Z false 4938961722798456%positive 54%nat (617370215349807)%Z 3%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c630ca4748b1bf9)%Z false 5361925026946041%positive 109%nat (5361925026946041)%Z 0%Z (-109)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3feda7801da7801e)%Z false 8346943019778078%positive 53%nat (4173471509889039)%Z 1%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc861ff8961ff896)%Z true 6227602018662550%positive 107%nat (-3113801009331275)%Z 1%Z (-106)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfceea659814cb11)%Z true 8701971365415697%positive 55%nat (-8701971365415697)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbfc9e5aef76f9fa1)%Z true 7289414056124321%positive 55%nat (-7289414056124321)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fc872ffdf083383)%Z false 6881842725139331%positive 55%nat (6881842725139331)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3fa0d08b840051c1)%Z false 4732897261015489%positive 57%nat (4732897261015489)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbfc0ee41742984c0)%Z true 4765564516533440%positive 55%nat (-74461945570835)%Z 6%Z (-49)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3fa320e55c399a4a)%Z false 5384194024381002%positive 57%nat (2692097012190501)%Z 1%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3fb2adaf2411e803)%Z false 5257517316827139%positive 56%nat (5257517316827139)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0xbfaf6c167218a6ed)%Z true 8844567937328877%positive 57%nat (-8844567937328877)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x402c07658a0b6e74)%Z false 7889432036994676%positive 49%nat (1972358009248669)%Z 2%Z (-47)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  unfold seg_poly in Eq.
  pose proof (approx_18 _ _ _ _ _ _ _ _ _ _ _ _ _ ((B zh - IZR 18 / 64) + B zl) V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 Ht) as AP.
  pose proof (amin_18 ((B zh - IZR 18 / 64) + B zl) Ht) as HAm.
  destruct ea_dw_small as [Ea0 Ea1].
  rewrite Eq.
  refine (fast_compose _ _ e1 ea (IZR 16565249 * bpow radix2 (-95)) (IZR 818 * bpow radix2 (-76)) _ (IZR 559755 * bpow radix2 (-21)) _ AP E1 Eea HAm _ Ea0 _).
  - apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0].
  - bpow_num. replace (- prec)%Z with (-53)%Z by reflexivity. bpow_num. clear - Fz. interval with (i_prec 200).
Qed.

Lemma evalcert_19 : EvalCert (IZR (4138825235294941) * bpow radix2 (-52)) (IZR (-6806427437731133) * bpow radix2 (-108)) (IZR (-4516770460954587) * bpow radix2 (-54)) (IZR (-3428385396229841) * bpow radix2 (-54)) (IZR (1739255201607401) * bpow radix2 (-53)) (IZR (5951303960482239) * bpow radix2 (-58)) (IZR (-4600630950987483) * bpow radix2 (-55)) (IZR (6653662703469329) * bpow radix2 (-57)) (IZR (2590797231680787) * bpow radix2 (-55)) (IZR (-146009608486677) * bpow radix2 (-51)) (IZR (-6089474562234827) * bpow radix2 (-47)) (IZR 848 * bpow radix2 (-76)) (IZR 803 * bpow radix2 (-72)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 53 (-53) (-72)); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_19.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_19.l1 th_ tl_ dg).
Qed.

Lemma segok_19 : SegOkRowA [(0x3fd278372057ef46)%Z; (0xbc7077cdd36dfc81)%Z; (0x3fed687aafdfd5ba)%Z; (0xbc782e68e19d8d3d)%Z; (0xbfd00bfa92db6fdb)%Z; (0xbfc85c325b640da2)%Z; (0x3fc8b75fa1dcbba4)%Z; (0x3f9524adee83d1bf)%Z; (0xbfc0583fdd9386db)%Z; (0x3fa7a37891e54311)%Z; (0x3fb268a1f95bda26)%Z; (0xbfb099705b1fe2a0)%Z; (0xc045a258482699cb)%Z] (IZR 848 * bpow radix2 (-76)).
Proof.
  unfold SegOkRowA. cbn [nth].
  destruct (word_ok_intro (0x3fd278372057ef46)%Z false 5198727741960006%positive 54%nat (2599363870980003)%Z 1%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc7077cdd36dfc81)%Z true 4635325526572161%positive 108%nat (-4635325526572161)%Z 0%Z (-108)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fed687aafdfd5ba)%Z false 8277650470589882%positive 53%nat (4138825235294941)%Z 1%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc782e68e19d8d3d)%Z true 6806427437731133%positive 108%nat (-6806427437731133)%Z 0%Z (-108)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd00bfa92db6fdb)%Z true 4516770460954587%positive 54%nat (-4516770460954587)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbfc85c325b640da2)%Z true 6856770792459682%positive 55%nat (-3428385396229841)%Z 1%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fc8b75fa1dcbba4)%Z false 6957020806429604%positive 55%nat (1739255201607401)%Z 2%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3f9524adee83d1bf)%Z false 5951303960482239%positive 58%nat (5951303960482239)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbfc0583fdd9386db)%Z true 4600630950987483%positive 55%nat (-4600630950987483)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3fa7a37891e54311)%Z false 6653662703469329%positive 57%nat (6653662703469329)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3fb268a1f95bda26)%Z false 5181594463361574%positive 56%nat (2590797231680787)%Z 1%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0xbfb099705b1fe2a0)%Z true 4672307471573664%positive 56%nat (-146009608486677)%Z 5%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc045a258482699cb)%Z true 6089474562234827%positive 47%nat (-6089474562234827)%Z 0%Z (-47)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_19 _ _).
  all: seg_numeric.
Qed.

Lemma row_19 : nth (Z.to_nat (19%Z - 1)) atan2_segments [] = [(0x3fd278372057ef46)%Z; (0xbc7077cdd36dfc81)%Z; (0x3fed687aafdfd5ba)%Z; (0xbc782e68e19d8d3d)%Z; (0xbfd00bfa92db6fdb)%Z; (0xbfc85c325b640da2)%Z; (0x3fc8b75fa1dcbba4)%Z; (0x3f9524adee83d1bf)%Z; (0xbfc0583fdd9386db)%Z; (0x3fa7a37891e54311)%Z; (0x3fb268a1f95bda26)%Z; (0xbfb099705b1fe2a0)%Z; (0xc045a258482699cb)%Z].
Proof. reflexivity. Qed.

Lemma fast_19 zh zl : finite zh -> finite zl -> / 128 <= B zh -> B zh <= 1 ->
  Znearest ne (B zh * 64) = 19%Z -> Rabs (B zl) <= bpow radix2 (-53) -> on_grid (-211) (B zl) ->
  exists h l, atan2_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    Rabs (B h + B l - atan (IZR 19 / 64 + ((B zh - IZR 19 / 64) + B zl))) <= bpow radix2 (-63) * atan (IZR 19 / 64 + ((B zh - IZR 19 / 64) + B zl)).
Proof.
  intros Fz Fl L U Hn Hl Hg.
  pose proof (series_segment_a zh zl 19%Z (IZR 848 * bpow radix2 (-76)) ltac:(lia) Fz Fl L U Hn Hl Hg segok_19) as SS.
  cbv zeta in SS. rewrite row_19 in SS. cbn [nth] in SS.
  destruct SS as [h [l [Hs [Fh [Fl' [Nrm [Ht [e1 [ea [E1 [Eea Eq]]]]]]]]]]].
  exists h, l. split; [exact Hs | split; [exact Fh | split; [exact Fl' | split; [exact Nrm | ]]]].
  destruct (word_ok_intro (0x3fd278372057ef46)%Z false 5198727741960006%positive 54%nat (2599363870980003)%Z 1%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc7077cdd36dfc81)%Z true 4635325526572161%positive 108%nat (-4635325526572161)%Z 0%Z (-108)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fed687aafdfd5ba)%Z false 8277650470589882%positive 53%nat (4138825235294941)%Z 1%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc782e68e19d8d3d)%Z true 6806427437731133%positive 108%nat (-6806427437731133)%Z 0%Z (-108)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd00bfa92db6fdb)%Z true 4516770460954587%positive 54%nat (-4516770460954587)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbfc85c325b640da2)%Z true 6856770792459682%positive 55%nat (-3428385396229841)%Z 1%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fc8b75fa1dcbba4)%Z false 6957020806429604%positive 55%nat (1739255201607401)%Z 2%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3f9524adee83d1bf)%Z false 5951303960482239%positive 58%nat (5951303960482239)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbfc0583fdd9386db)%Z true 4600630950987483%positive 55%nat (-4600630950987483)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3fa7a37891e54311)%Z false 6653662703469329%positive 57%nat (6653662703469329)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3fb268a1f95bda26)%Z false 5181594463361574%positive 56%nat (2590797231680787)%Z 1%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0xbfb099705b1fe2a0)%Z true 4672307471573664%positive 56%nat (-146009608486677)%Z 5%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc045a258482699cb)%Z true 6089474562234827%positive 47%nat (-6089474562234827)%Z 0%Z (-47)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  unfold seg_poly in Eq.
  pose proof (approx_19 _ _ _ _ _ _ _ _ _ _ _ _ _ ((B zh - IZR 19 / 64) + B zl) V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 Ht) as AP.
  pose proof (amin_19 ((B zh - IZR 19 / 64) + B zl) Ht) as HAm.
  destruct ea_dw_small as [Ea0 Ea1].
  rewrite Eq.
  refine (fast_compose _ _ e1 ea (IZR 12756919 * bpow radix2 (-93)) (IZR 848 * bpow radix2 (-76)) _ (IZR 590121 * bpow radix2 (-21)) _ AP E1 Eea HAm _ Ea0 _).
  - apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0].
  - bpow_num. replace (- prec)%Z with (-53)%Z by reflexivity. bpow_num. clear - Fz. interval with (i_prec 200).
Qed.

Lemma evalcert_20 : EvalCert (IZR (4102923503938957) * bpow radix2 (-52)) (IZR (1891191302596863) * bpow radix2 (-105)) (IZR (-2336184201531079) * bpow radix2 (-53)) (IZR (-6420488206532863) * bpow radix2 (-55)) (IZR (3499261380796319) * bpow radix2 (-54)) (IZR (5145968686663909) * bpow radix2 (-59)) (IZR (-2201601359030169) * bpow radix2 (-54)) (IZR (242462426235029) * bpow radix2 (-52)) (IZR (8896434096725391) * bpow radix2 (-57)) (IZR (-1203119726495773) * bpow radix2 (-54)) (IZR (-646930935969893) * bpow radix2 (-44)) (IZR 877 * bpow radix2 (-76)) (IZR 753 * bpow radix2 (-72)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 877 (-877) (-76)); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_20.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_20.l1 th_ tl_ dg).
Qed.

Lemma segok_20 : SegOkRowA [(0x3fd362773707ebcc)%Z; (0xbc6963a544b672d8)%Z; (0x3fed272ca3fc5b1a)%Z; (0x3c8ae01d272ca3fc)%Z; (0xbfd0997e8aec9d8e)%Z; (0xbfc6cf6666d5c0ff)%Z; (0x3fc8dd1e8f283f3e)%Z; (0x3f82483b339808e5)%Z; (0xbfbf49610bc49e64)%Z; (0x3fab9095d93012a0)%Z; (0x3faf9b427a1a5d8f)%Z; (0xbfb118ec8fae2074)%Z; (0xc042630ac50fc328)%Z] (IZR 877 * bpow radix2 (-76)).
Proof.
  unfold SegOkRowA. cbn [nth].
  destruct (word_ok_intro (0x3fd362773707ebcc)%Z false 5456288721398732%positive 54%nat (1364072180349683)%Z 2%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc6963a544b672d8)%Z true 7146435891327704%positive 109%nat (-893304486415963)%Z 3%Z (-106)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fed272ca3fc5b1a)%Z false 8205847007877914%positive 53%nat (4102923503938957)%Z 1%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c8ae01d272ca3fc)%Z false 7564765210387452%positive 107%nat (1891191302596863)%Z 2%Z (-105)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd0997e8aec9d8e)%Z true 4672368403062158%positive 54%nat (-2336184201531079)%Z 1%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbfc6cf6666d5c0ff)%Z true 6420488206532863%positive 55%nat (-6420488206532863)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fc8dd1e8f283f3e)%Z false 6998522761592638%positive 55%nat (3499261380796319)%Z 1%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3f82483b339808e5)%Z false 5145968686663909%positive 59%nat (5145968686663909)%Z 0%Z (-59)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbfbf49610bc49e64)%Z true 8806405436120676%positive 56%nat (-2201601359030169)%Z 2%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3fab9095d93012a0)%Z false 7758797639520928%positive 57%nat (242462426235029)%Z 5%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3faf9b427a1a5d8f)%Z false 8896434096725391%positive 57%nat (8896434096725391)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0xbfb118ec8fae2074)%Z true 4812478905983092%positive 56%nat (-1203119726495773)%Z 2%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc042630ac50fc328)%Z true 5175447487759144%positive 47%nat (-646930935969893)%Z 3%Z (-44)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_20 _ _).
  all: seg_numeric.
Qed.

Lemma row_20 : nth (Z.to_nat (20%Z - 1)) atan2_segments [] = [(0x3fd362773707ebcc)%Z; (0xbc6963a544b672d8)%Z; (0x3fed272ca3fc5b1a)%Z; (0x3c8ae01d272ca3fc)%Z; (0xbfd0997e8aec9d8e)%Z; (0xbfc6cf6666d5c0ff)%Z; (0x3fc8dd1e8f283f3e)%Z; (0x3f82483b339808e5)%Z; (0xbfbf49610bc49e64)%Z; (0x3fab9095d93012a0)%Z; (0x3faf9b427a1a5d8f)%Z; (0xbfb118ec8fae2074)%Z; (0xc042630ac50fc328)%Z].
Proof. reflexivity. Qed.

Lemma fast_20 zh zl : finite zh -> finite zl -> / 128 <= B zh -> B zh <= 1 ->
  Znearest ne (B zh * 64) = 20%Z -> Rabs (B zl) <= bpow radix2 (-53) -> on_grid (-211) (B zl) ->
  exists h l, atan2_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    Rabs (B h + B l - atan (IZR 20 / 64 + ((B zh - IZR 20 / 64) + B zl))) <= bpow radix2 (-63) * atan (IZR 20 / 64 + ((B zh - IZR 20 / 64) + B zl)).
Proof.
  intros Fz Fl L U Hn Hl Hg.
  pose proof (series_segment_a zh zl 20%Z (IZR 877 * bpow radix2 (-76)) ltac:(lia) Fz Fl L U Hn Hl Hg segok_20) as SS.
  cbv zeta in SS. rewrite row_20 in SS. cbn [nth] in SS.
  destruct SS as [h [l [Hs [Fh [Fl' [Nrm [Ht [e1 [ea [E1 [Eea Eq]]]]]]]]]]].
  exists h, l. split; [exact Hs | split; [exact Fh | split; [exact Fl' | split; [exact Nrm | ]]]].
  destruct (word_ok_intro (0x3fd362773707ebcc)%Z false 5456288721398732%positive 54%nat (1364072180349683)%Z 2%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc6963a544b672d8)%Z true 7146435891327704%positive 109%nat (-893304486415963)%Z 3%Z (-106)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fed272ca3fc5b1a)%Z false 8205847007877914%positive 53%nat (4102923503938957)%Z 1%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c8ae01d272ca3fc)%Z false 7564765210387452%positive 107%nat (1891191302596863)%Z 2%Z (-105)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd0997e8aec9d8e)%Z true 4672368403062158%positive 54%nat (-2336184201531079)%Z 1%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbfc6cf6666d5c0ff)%Z true 6420488206532863%positive 55%nat (-6420488206532863)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fc8dd1e8f283f3e)%Z false 6998522761592638%positive 55%nat (3499261380796319)%Z 1%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3f82483b339808e5)%Z false 5145968686663909%positive 59%nat (5145968686663909)%Z 0%Z (-59)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbfbf49610bc49e64)%Z true 8806405436120676%positive 56%nat (-2201601359030169)%Z 2%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3fab9095d93012a0)%Z false 7758797639520928%positive 57%nat (242462426235029)%Z 5%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3faf9b427a1a5d8f)%Z false 8896434096725391%positive 57%nat (8896434096725391)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0xbfb118ec8fae2074)%Z true 4812478905983092%positive 56%nat (-1203119726495773)%Z 2%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc042630ac50fc328)%Z true 5175447487759144%positive 47%nat (-646930935969893)%Z 3%Z (-44)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  unfold seg_poly in Eq.
  pose proof (approx_20 _ _ _ _ _ _ _ _ _ _ _ _ _ ((B zh - IZR 20 / 64) + B zl) V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 Ht) as AP.
  pose proof (amin_20 ((B zh - IZR 20 / 64) + B zl) Ht) as HAm.
  destruct ea_dw_small as [Ea0 Ea1].
  rewrite Eq.
  refine (fast_compose _ _ e1 ea (IZR 10844138 * bpow radix2 (-93)) (IZR 877 * bpow radix2 (-76)) _ (IZR 620235 * bpow radix2 (-21)) _ AP E1 Eea HAm _ Ea0 _).
  - apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0].
  - bpow_num. replace (- prec)%Z with (-53)%Z by reflexivity. bpow_num. clear - Fz. interval with (i_prec 200).
Qed.

Lemma evalcert_21 : EvalCert (IZR (8131692340184947) * bpow radix2 (-53)) (IZR (-5189512640928577) * bpow radix2 (-107)) (IZR (-2408859269386945) * bpow radix2 (-53)) (IZR (-5982627108419169) * bpow radix2 (-55)) (IZR (7007791797738207) * bpow radix2 (-55)) (IZR (-2586033764512605) * bpow radix2 (-60)) (IZR (-2088932883041643) * bpow radix2 (-54)) (IZR (8694916824546489) * bpow radix2 (-57)) (IZR (7883934901389715) * bpow radix2 (-57)) (IZR (-4836331643590271) * bpow radix2 (-56)) (IZR (-7652058164418691) * bpow radix2 (-47)) (IZR 904 * bpow radix2 (-76)) (IZR 702 * bpow radix2 (-72)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 113 (-113) (-73)); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_21.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_21.l1 th_ tl_ dg).
Qed.

Lemma segok_21 : SegOkRowA [(0x3fd44aa436c2af0a)%Z; (0xbc75d5e43c55b3ba)%Z; (0x3fece3bb295c0773)%Z; (0xbc826fd591851b41)%Z; (0xbfd11db08221a582)%Z; (0xbfc5412aeb9ef661)%Z; (0x3fc8e58cacc39adf)%Z; (0xbf625ff7cfd266ba)%Z; (0xbfbdaf7e59d035ac)%Z; (0x3faee3fb14adbcb9)%Z; (0x3fac0265a33ac993)%Z; (0xbfb12e9e35a1d67f)%Z; (0xc04b2f81a0b0d883)%Z] (IZR 904 * bpow radix2 (-76)).
Proof.
  unfold SegOkRowA. cbn [nth].
  destruct (word_ok_intro (0x3fd44aa436c2af0a)%Z false 5711568688033546%positive 54%nat (2855784344016773)%Z 1%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc75d5e43c55b3ba)%Z true 6146150752433082%positive 108%nat (-3073075376216541)%Z 1%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fece3bb295c0773)%Z false 8131692340184947%positive 53%nat (8131692340184947)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc826fd591851b41)%Z true 5189512640928577%positive 107%nat (-5189512640928577)%Z 0%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd11db08221a582)%Z true 4817718538773890%positive 54%nat (-2408859269386945)%Z 1%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbfc5412aeb9ef661)%Z true 5982627108419169%positive 55%nat (-5982627108419169)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fc8e58cacc39adf)%Z false 7007791797738207%positive 55%nat (7007791797738207)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbf625ff7cfd266ba)%Z true 5172067529025210%positive 61%nat (-2586033764512605)%Z 1%Z (-60)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbfbdaf7e59d035ac)%Z true 8355731532166572%positive 56%nat (-2088932883041643)%Z 2%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3faee3fb14adbcb9)%Z false 8694916824546489%positive 57%nat (8694916824546489)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3fac0265a33ac993)%Z false 7883934901389715%positive 57%nat (7883934901389715)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0xbfb12e9e35a1d67f)%Z true 4836331643590271%positive 56%nat (-4836331643590271)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc04b2f81a0b0d883)%Z true 7652058164418691%positive 47%nat (-7652058164418691)%Z 0%Z (-47)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_21 _ _).
  all: seg_numeric.
Qed.

Lemma row_21 : nth (Z.to_nat (21%Z - 1)) atan2_segments [] = [(0x3fd44aa436c2af0a)%Z; (0xbc75d5e43c55b3ba)%Z; (0x3fece3bb295c0773)%Z; (0xbc826fd591851b41)%Z; (0xbfd11db08221a582)%Z; (0xbfc5412aeb9ef661)%Z; (0x3fc8e58cacc39adf)%Z; (0xbf625ff7cfd266ba)%Z; (0xbfbdaf7e59d035ac)%Z; (0x3faee3fb14adbcb9)%Z; (0x3fac0265a33ac993)%Z; (0xbfb12e9e35a1d67f)%Z; (0xc04b2f81a0b0d883)%Z].
Proof. reflexivity. Qed.

Lemma fast_21 zh zl : finite zh -> finite zl -> / 128 <= B zh -> B zh <= 1 ->
  Znearest ne (B zh * 64) = 21%Z -> Rabs (B zl) <= bpow radix2 (-53) -> on_grid (-211) (B zl) ->
  exists h l, atan2_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    Rabs (B h + B l - atan (IZR 21 / 64 + ((B zh - IZR 21 / 64) + B zl))) <= bpow radix2 (-63) * atan (IZR 21 / 64 + ((B zh - IZR 21 / 64) + B zl)).
Proof.
  intros Fz Fl L U Hn Hl Hg.
  pose proof (series_segment_a zh zl 21%Z (IZR 904 * bpow radix2 (-76)) ltac:(lia) Fz Fl L U Hn Hl Hg segok_21) as SS.
  cbv zeta in SS. rewrite row_21 in SS. cbn [nth] in SS.
  destruct SS as [h [l [Hs [Fh [Fl' [Nrm [Ht [e1 [ea [E1 [Eea Eq]]]]]]]]]]].
  exists h, l. split; [exact Hs | split; [exact Fh | split; [exact Fl' | split; [exact Nrm | ]]]].
  destruct (word_ok_intro (0x3fd44aa436c2af0a)%Z false 5711568688033546%positive 54%nat (2855784344016773)%Z 1%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc75d5e43c55b3ba)%Z true 6146150752433082%positive 108%nat (-3073075376216541)%Z 1%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fece3bb295c0773)%Z false 8131692340184947%positive 53%nat (8131692340184947)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc826fd591851b41)%Z true 5189512640928577%positive 107%nat (-5189512640928577)%Z 0%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd11db08221a582)%Z true 4817718538773890%positive 54%nat (-2408859269386945)%Z 1%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbfc5412aeb9ef661)%Z true 5982627108419169%positive 55%nat (-5982627108419169)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fc8e58cacc39adf)%Z false 7007791797738207%positive 55%nat (7007791797738207)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbf625ff7cfd266ba)%Z true 5172067529025210%positive 61%nat (-2586033764512605)%Z 1%Z (-60)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbfbdaf7e59d035ac)%Z true 8355731532166572%positive 56%nat (-2088932883041643)%Z 2%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3faee3fb14adbcb9)%Z false 8694916824546489%positive 57%nat (8694916824546489)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3fac0265a33ac993)%Z false 7883934901389715%positive 57%nat (7883934901389715)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0xbfb12e9e35a1d67f)%Z true 4836331643590271%positive 56%nat (-4836331643590271)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc04b2f81a0b0d883)%Z true 7652058164418691%positive 47%nat (-7652058164418691)%Z 0%Z (-47)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  unfold seg_poly in Eq.
  pose proof (approx_21 _ _ _ _ _ _ _ _ _ _ _ _ _ ((B zh - IZR 21 / 64) + B zl) V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 Ht) as AP.
  pose proof (amin_21 ((B zh - IZR 21 / 64) + B zl) Ht) as HAm.
  destruct ea_dw_small as [Ea0 Ea1].
  rewrite Eq.
  refine (fast_compose _ _ e1 ea (IZR 16036929 * bpow radix2 (-93)) (IZR 904 * bpow radix2 (-76)) _ (IZR 650087 * bpow radix2 (-21)) _ AP E1 Eea HAm _ Ea0 _).
  - apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0].
  - bpow_num. replace (- prec)%Z with (-53)%Z by reflexivity. bpow_num. clear - Fz. interval with (i_prec 200).
Qed.

Lemma evalcert_22 : EvalCert (IZR (8055346757078407) * bpow radix2 (-53)) (IZR (-407093940116023) * bpow radix2 (-104)) (IZR (-619100886133537) * bpow radix2 (-51)) (IZR (-1386287886039071) * bpow radix2 (-53)) (IZR (6986475523796789) * bpow radix2 (-55)) (IZR (-1843989191660965) * bpow radix2 (-57)) (IZR (-3929253790802219) * bpow radix2 (-55)) (IZR (4730484166933267) * bpow radix2 (-56)) (IZR (3236642943021219) * bpow radix2 (-56)) (IZR (-4759898096445231) * bpow radix2 (-56)) (IZR (-7260141835146259) * bpow radix2 (-47)) (IZR 929 * bpow radix2 (-76)) (IZR 652 * bpow radix2 (-72)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 929 (-929) (-76)); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_22.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_22.l1 th_ tl_ dg).
Qed.

Lemma segok_22 : SegOkRowA [(0x3fd530ad9951cd4a)%Z; (0xbc62566480884082)%Z; (0x3fec9e4b91ff8d87)%Z; (0xbc7723ff1b0da370)%Z; (0xbfd1988d432f5908)%Z; (0xbfc3b3493403e07c)%Z; (0x3fc8d22997d3ef35)%Z; (0xbf8a3464c2f45694)%Z; (0xbfbbeb4560ddc256)%Z; (0x3fb0ce59ac62bb13)%Z; (0x3fa6ff6b51c46146)%Z; (0xbfb0e91a2334a72f)%Z; (0xc049cb0f7f1a5413)%Z] (IZR 929 * bpow radix2 (-76)).
Proof.
  unfold SegOkRowA. cbn [nth].
  destruct (word_ok_intro (0x3fd530ad9951cd4a)%Z false 5964496670674250%positive 54%nat (2982248335337125)%Z 1%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc62566480884082)%Z true 5161539233923202%positive 109%nat (-2580769616961601)%Z 1%Z (-108)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fec9e4b91ff8d87)%Z false 8055346757078407%positive 53%nat (8055346757078407)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc7723ff1b0da370)%Z true 6513503041856368%positive 108%nat (-407093940116023)%Z 4%Z (-104)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd1988d432f5908)%Z true 4952807089068296%positive 54%nat (-619100886133537)%Z 3%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbfc3b3493403e07c)%Z true 5545151544156284%positive 55%nat (-1386287886039071)%Z 2%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fc8d22997d3ef35)%Z false 6986475523796789%positive 55%nat (6986475523796789)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbf8a3464c2f45694)%Z true 7375956766643860%positive 59%nat (-1843989191660965)%Z 2%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbfbbeb4560ddc256)%Z true 7858507581604438%positive 56%nat (-3929253790802219)%Z 1%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3fb0ce59ac62bb13)%Z false 4730484166933267%positive 56%nat (4730484166933267)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3fa6ff6b51c46146)%Z false 6473285886042438%positive 57%nat (3236642943021219)%Z 1%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0xbfb0e91a2334a72f)%Z true 4759898096445231%positive 56%nat (-4759898096445231)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc049cb0f7f1a5413)%Z true 7260141835146259%positive 47%nat (-7260141835146259)%Z 0%Z (-47)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_22 _ _).
  all: seg_numeric.
Qed.

Lemma row_22 : nth (Z.to_nat (22%Z - 1)) atan2_segments [] = [(0x3fd530ad9951cd4a)%Z; (0xbc62566480884082)%Z; (0x3fec9e4b91ff8d87)%Z; (0xbc7723ff1b0da370)%Z; (0xbfd1988d432f5908)%Z; (0xbfc3b3493403e07c)%Z; (0x3fc8d22997d3ef35)%Z; (0xbf8a3464c2f45694)%Z; (0xbfbbeb4560ddc256)%Z; (0x3fb0ce59ac62bb13)%Z; (0x3fa6ff6b51c46146)%Z; (0xbfb0e91a2334a72f)%Z; (0xc049cb0f7f1a5413)%Z].
Proof. reflexivity. Qed.

Lemma fast_22 zh zl : finite zh -> finite zl -> / 128 <= B zh -> B zh <= 1 ->
  Znearest ne (B zh * 64) = 22%Z -> Rabs (B zl) <= bpow radix2 (-53) -> on_grid (-211) (B zl) ->
  exists h l, atan2_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    Rabs (B h + B l - atan (IZR 22 / 64 + ((B zh - IZR 22 / 64) + B zl))) <= bpow radix2 (-63) * atan (IZR 22 / 64 + ((B zh - IZR 22 / 64) + B zl)).
Proof.
  intros Fz Fl L U Hn Hl Hg.
  pose proof (series_segment_a zh zl 22%Z (IZR 929 * bpow radix2 (-76)) ltac:(lia) Fz Fl L U Hn Hl Hg segok_22) as SS.
  cbv zeta in SS. rewrite row_22 in SS. cbn [nth] in SS.
  destruct SS as [h [l [Hs [Fh [Fl' [Nrm [Ht [e1 [ea [E1 [Eea Eq]]]]]]]]]]].
  exists h, l. split; [exact Hs | split; [exact Fh | split; [exact Fl' | split; [exact Nrm | ]]]].
  destruct (word_ok_intro (0x3fd530ad9951cd4a)%Z false 5964496670674250%positive 54%nat (2982248335337125)%Z 1%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc62566480884082)%Z true 5161539233923202%positive 109%nat (-2580769616961601)%Z 1%Z (-108)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fec9e4b91ff8d87)%Z false 8055346757078407%positive 53%nat (8055346757078407)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc7723ff1b0da370)%Z true 6513503041856368%positive 108%nat (-407093940116023)%Z 4%Z (-104)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd1988d432f5908)%Z true 4952807089068296%positive 54%nat (-619100886133537)%Z 3%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbfc3b3493403e07c)%Z true 5545151544156284%positive 55%nat (-1386287886039071)%Z 2%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fc8d22997d3ef35)%Z false 6986475523796789%positive 55%nat (6986475523796789)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbf8a3464c2f45694)%Z true 7375956766643860%positive 59%nat (-1843989191660965)%Z 2%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbfbbeb4560ddc256)%Z true 7858507581604438%positive 56%nat (-3929253790802219)%Z 1%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3fb0ce59ac62bb13)%Z false 4730484166933267%positive 56%nat (4730484166933267)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3fa6ff6b51c46146)%Z false 6473285886042438%positive 57%nat (3236642943021219)%Z 1%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0xbfb0e91a2334a72f)%Z true 4759898096445231%positive 56%nat (-4759898096445231)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc049cb0f7f1a5413)%Z true 7260141835146259%positive 47%nat (-7260141835146259)%Z 0%Z (-47)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  unfold seg_poly in Eq.
  pose proof (approx_22 _ _ _ _ _ _ _ _ _ _ _ _ _ ((B zh - IZR 22 / 64) + B zl) V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 Ht) as AP.
  pose proof (amin_22 ((B zh - IZR 22 / 64) + B zl) Ht) as HAm.
  destruct ea_dw_small as [Ea0 Ea1].
  rewrite Eq.
  refine (fast_compose _ _ e1 ea (IZR 15217794 * bpow radix2 (-93)) (IZR 929 * bpow radix2 (-76)) _ (IZR 679669 * bpow radix2 (-21)) _ AP E1 Eea HAm _ Ea0 _).
  - apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0].
  - bpow_num. replace (- prec)%Z with (-53)%Z by reflexivity. bpow_num. clear - Fz. interval with (i_prec 200).
Qed.

Lemma evalcert_23 : EvalCert (IZR (7976970410252779) * bpow radix2 (-53)) (IZR (2781033629355705) * bpow radix2 (-108)) (IZR (-5077665056818201) * bpow radix2 (-54)) (IZR (-638739635067481) * bpow radix2 (-52)) (IZR (1734097999226759) * bpow radix2 (-53)) (IZR (-1633927876525819) * bpow radix2 (-56)) (IZR (-7323951815864959) * bpow radix2 (-56)) (IZR (5029607247199689) * bpow radix2 (-56)) (IZR (6327169748409017) * bpow radix2 (-58)) (IZR (-2318151742174125) * bpow radix2 (-55)) (IZR (6850960756819683) * bpow radix2 (-47)) (IZR 952 * bpow radix2 (-76)) (IZR 602 * bpow radix2 (-72)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 119 (-119) (-73)); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_23.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_23.l1 th_ tl_ dg).
Qed.

Lemma segok_23 : SegOkRowA [(0x3fd614840309cfe2)%Z; (0xbc7a725715711f00)%Z; (0x3fec570327afd9eb)%Z; (0x3c63c2abb32c1d72)%Z; (0xbfd20a1c06000419)%Z; (0xbfc22771486ad2c8)%Z; (0x3fc8a49c9cff9e1c)%Z; (0xbf973831eaacfbec)%Z; (0xbfba05186a56327f)%Z; (0x3fb1de66b1543dc9)%Z; (0x3f967a8701499ab9)%Z; (0xbfb078b18641675a)%Z; (0x404856e99a47c6e3)%Z] (IZR 952 * bpow radix2 (-76)).
Proof.
  unfold SegOkRowA. cbn [nth].
  destruct (word_ok_intro (0x3fd614840309cfe2)%Z false 6215006706847714%positive 54%nat (3107503353423857)%Z 1%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc7a725715711f00)%Z true 7444067741933312%positive 108%nat (-29078389616927)%Z 8%Z (-100)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fec570327afd9eb)%Z false 7976970410252779%positive 53%nat (7976970410252779)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c63c2abb32c1d72)%Z false 5562067258711410%positive 109%nat (2781033629355705)%Z 1%Z (-108)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd20a1c06000419)%Z true 5077665056818201%positive 54%nat (-5077665056818201)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbfc22771486ad2c8)%Z true 5109917080539848%positive 55%nat (-638739635067481)%Z 3%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fc8a49c9cff9e1c)%Z false 6936391996907036%positive 55%nat (1734097999226759)%Z 2%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbf973831eaacfbec)%Z true 6535711506103276%positive 58%nat (-1633927876525819)%Z 2%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbfba05186a56327f)%Z true 7323951815864959%positive 56%nat (-7323951815864959)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3fb1de66b1543dc9)%Z false 5029607247199689%positive 56%nat (5029607247199689)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3f967a8701499ab9)%Z false 6327169748409017%positive 58%nat (6327169748409017)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0xbfb078b18641675a)%Z true 4636303484348250%positive 56%nat (-2318151742174125)%Z 1%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x404856e99a47c6e3)%Z false 6850960756819683%positive 47%nat (6850960756819683)%Z 0%Z (-47)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_23 _ _).
  all: seg_numeric.
Qed.

Lemma row_23 : nth (Z.to_nat (23%Z - 1)) atan2_segments [] = [(0x3fd614840309cfe2)%Z; (0xbc7a725715711f00)%Z; (0x3fec570327afd9eb)%Z; (0x3c63c2abb32c1d72)%Z; (0xbfd20a1c06000419)%Z; (0xbfc22771486ad2c8)%Z; (0x3fc8a49c9cff9e1c)%Z; (0xbf973831eaacfbec)%Z; (0xbfba05186a56327f)%Z; (0x3fb1de66b1543dc9)%Z; (0x3f967a8701499ab9)%Z; (0xbfb078b18641675a)%Z; (0x404856e99a47c6e3)%Z].
Proof. reflexivity. Qed.

Lemma fast_23 zh zl : finite zh -> finite zl -> / 128 <= B zh -> B zh <= 1 ->
  Znearest ne (B zh * 64) = 23%Z -> Rabs (B zl) <= bpow radix2 (-53) -> on_grid (-211) (B zl) ->
  exists h l, atan2_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    Rabs (B h + B l - atan (IZR 23 / 64 + ((B zh - IZR 23 / 64) + B zl))) <= bpow radix2 (-63) * atan (IZR 23 / 64 + ((B zh - IZR 23 / 64) + B zl)).
Proof.
  intros Fz Fl L U Hn Hl Hg.
  pose proof (series_segment_a zh zl 23%Z (IZR 952 * bpow radix2 (-76)) ltac:(lia) Fz Fl L U Hn Hl Hg segok_23) as SS.
  cbv zeta in SS. rewrite row_23 in SS. cbn [nth] in SS.
  destruct SS as [h [l [Hs [Fh [Fl' [Nrm [Ht [e1 [ea [E1 [Eea Eq]]]]]]]]]]].
  exists h, l. split; [exact Hs | split; [exact Fh | split; [exact Fl' | split; [exact Nrm | ]]]].
  destruct (word_ok_intro (0x3fd614840309cfe2)%Z false 6215006706847714%positive 54%nat (3107503353423857)%Z 1%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc7a725715711f00)%Z true 7444067741933312%positive 108%nat (-29078389616927)%Z 8%Z (-100)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fec570327afd9eb)%Z false 7976970410252779%positive 53%nat (7976970410252779)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c63c2abb32c1d72)%Z false 5562067258711410%positive 109%nat (2781033629355705)%Z 1%Z (-108)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd20a1c06000419)%Z true 5077665056818201%positive 54%nat (-5077665056818201)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbfc22771486ad2c8)%Z true 5109917080539848%positive 55%nat (-638739635067481)%Z 3%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fc8a49c9cff9e1c)%Z false 6936391996907036%positive 55%nat (1734097999226759)%Z 2%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbf973831eaacfbec)%Z true 6535711506103276%positive 58%nat (-1633927876525819)%Z 2%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbfba05186a56327f)%Z true 7323951815864959%positive 56%nat (-7323951815864959)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3fb1de66b1543dc9)%Z false 5029607247199689%positive 56%nat (5029607247199689)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3f967a8701499ab9)%Z false 6327169748409017%positive 58%nat (6327169748409017)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0xbfb078b18641675a)%Z true 4636303484348250%positive 56%nat (-2318151742174125)%Z 1%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x404856e99a47c6e3)%Z false 6850960756819683%positive 47%nat (6850960756819683)%Z 0%Z (-47)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  unfold seg_poly in Eq.
  pose proof (approx_23 _ _ _ _ _ _ _ _ _ _ _ _ _ ((B zh - IZR 23 / 64) + B zl) V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 Ht) as AP.
  pose proof (amin_23 ((B zh - IZR 23 / 64) + B zl) Ht) as HAm.
  destruct ea_dw_small as [Ea0 Ea1].
  rewrite Eq.
  refine (fast_compose _ _ e1 ea (IZR 14352560 * bpow radix2 (-93)) (IZR 952 * bpow radix2 (-76)) _ (IZR 708974 * bpow radix2 (-21)) _ AP E1 Eea HAm _ Ea0 _).
  - apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0].
  - bpow_num. replace (- prec)%Z with (-53)%Z by reflexivity. bpow_num. clear - Fz. interval with (i_prec 200).
Qed.

Lemma evalcert_24 : EvalCert (IZR (246772582321671) * bpow radix2 (-48)) (IZR (246772582321671) * bpow radix2 (-102)) (IZR (-1298091391938653) * bpow radix2 (-52)) (IZR (-4678661211736271) * bpow radix2 (-55)) (IZR (6859495889840357) * bpow radix2 (-55)) (IZR (-4588715158483875) * bpow radix2 (-57)) (IZR (-845152898014713) * bpow radix2 (-53)) (IZR (2623706505387263) * bpow radix2 (-55)) (IZR (5642481600487947) * bpow radix2 (-58)) (IZR (-8861351132807291) * bpow radix2 (-57)) (IZR (7408523509139957) * bpow radix2 (-52)) (IZR 973 * bpow radix2 (-76)) (IZR 552 * bpow radix2 (-72)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 973 (-973) (-76)); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_24.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_24.l1 th_ tl_ dg).
Qed.

Lemma segok_24 : SegOkRowA [(0x3fd6f61941e4def1)%Z; (0xbc7c63aae6f6e918)%Z; (0x3fec0e070381c0e0)%Z; (0x3c8c0e070381c0e0)%Z; (0xbfd2726dd135c174)%Z; (0xbfc09f37b38cc8cf)%Z; (0x3fc85eacd7da28e5)%Z; (0xbfa04d6980ff33a3)%Z; (0xbfb8054bf222efc8)%Z; (0x3fb2a47e8c7f39fe)%Z; (0x3f940bce9f72e20b)%Z; (0xbfaf7b5a1680407b)%Z; (0x3ffa52034c1289f5)%Z] (IZR 973 * bpow radix2 (-76)).
Proof.
  unfold SegOkRowA. cbn [nth].
  destruct (word_ok_intro (0x3fd6f61941e4def1)%Z false 6463037827768049%positive 54%nat (6463037827768049)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc7c63aae6f6e918)%Z true 7990885018429720%positive 108%nat (-998860627303715)%Z 3%Z (-105)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fec0e070381c0e0)%Z false 7896722634293472%positive 53%nat (246772582321671)%Z 5%Z (-48)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c8c0e070381c0e0)%Z false 7896722634293472%positive 107%nat (246772582321671)%Z 5%Z (-102)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd2726dd135c174)%Z true 5192365567754612%positive 54%nat (-1298091391938653)%Z 2%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbfc09f37b38cc8cf)%Z true 4678661211736271%positive 55%nat (-4678661211736271)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fc85eacd7da28e5)%Z false 6859495889840357%positive 55%nat (6859495889840357)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfa04d6980ff33a3)%Z true 4588715158483875%positive 57%nat (-4588715158483875)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbfb8054bf222efc8)%Z true 6761223184117704%positive 56%nat (-845152898014713)%Z 3%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3fb2a47e8c7f39fe)%Z false 5247413010774526%positive 56%nat (2623706505387263)%Z 1%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3f940bce9f72e20b)%Z false 5642481600487947%positive 58%nat (5642481600487947)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0xbfaf7b5a1680407b)%Z true 8861351132807291%positive 57%nat (-8861351132807291)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x3ffa52034c1289f5)%Z false 7408523509139957%positive 52%nat (7408523509139957)%Z 0%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_24 _ _).
  all: seg_numeric.
Qed.

Lemma row_24 : nth (Z.to_nat (24%Z - 1)) atan2_segments [] = [(0x3fd6f61941e4def1)%Z; (0xbc7c63aae6f6e918)%Z; (0x3fec0e070381c0e0)%Z; (0x3c8c0e070381c0e0)%Z; (0xbfd2726dd135c174)%Z; (0xbfc09f37b38cc8cf)%Z; (0x3fc85eacd7da28e5)%Z; (0xbfa04d6980ff33a3)%Z; (0xbfb8054bf222efc8)%Z; (0x3fb2a47e8c7f39fe)%Z; (0x3f940bce9f72e20b)%Z; (0xbfaf7b5a1680407b)%Z; (0x3ffa52034c1289f5)%Z].
Proof. reflexivity. Qed.

Lemma fast_24 zh zl : finite zh -> finite zl -> / 128 <= B zh -> B zh <= 1 ->
  Znearest ne (B zh * 64) = 24%Z -> Rabs (B zl) <= bpow radix2 (-53) -> on_grid (-211) (B zl) ->
  exists h l, atan2_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    Rabs (B h + B l - atan (IZR 24 / 64 + ((B zh - IZR 24 / 64) + B zl))) <= bpow radix2 (-63) * atan (IZR 24 / 64 + ((B zh - IZR 24 / 64) + B zl)).
Proof.
  intros Fz Fl L U Hn Hl Hg.
  pose proof (series_segment_a zh zl 24%Z (IZR 973 * bpow radix2 (-76)) ltac:(lia) Fz Fl L U Hn Hl Hg segok_24) as SS.
  cbv zeta in SS. rewrite row_24 in SS. cbn [nth] in SS.
  destruct SS as [h [l [Hs [Fh [Fl' [Nrm [Ht [e1 [ea [E1 [Eea Eq]]]]]]]]]]].
  exists h, l. split; [exact Hs | split; [exact Fh | split; [exact Fl' | split; [exact Nrm | ]]]].
  destruct (word_ok_intro (0x3fd6f61941e4def1)%Z false 6463037827768049%positive 54%nat (6463037827768049)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc7c63aae6f6e918)%Z true 7990885018429720%positive 108%nat (-998860627303715)%Z 3%Z (-105)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fec0e070381c0e0)%Z false 7896722634293472%positive 53%nat (246772582321671)%Z 5%Z (-48)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c8c0e070381c0e0)%Z false 7896722634293472%positive 107%nat (246772582321671)%Z 5%Z (-102)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd2726dd135c174)%Z true 5192365567754612%positive 54%nat (-1298091391938653)%Z 2%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbfc09f37b38cc8cf)%Z true 4678661211736271%positive 55%nat (-4678661211736271)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fc85eacd7da28e5)%Z false 6859495889840357%positive 55%nat (6859495889840357)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfa04d6980ff33a3)%Z true 4588715158483875%positive 57%nat (-4588715158483875)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbfb8054bf222efc8)%Z true 6761223184117704%positive 56%nat (-845152898014713)%Z 3%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3fb2a47e8c7f39fe)%Z false 5247413010774526%positive 56%nat (2623706505387263)%Z 1%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3f940bce9f72e20b)%Z false 5642481600487947%positive 58%nat (5642481600487947)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0xbfaf7b5a1680407b)%Z true 8861351132807291%positive 57%nat (-8861351132807291)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x3ffa52034c1289f5)%Z false 7408523509139957%positive 52%nat (7408523509139957)%Z 0%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  unfold seg_poly in Eq.
  pose proof (approx_24 _ _ _ _ _ _ _ _ _ _ _ _ _ ((B zh - IZR 24 / 64) + B zl) V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 Ht) as AP.
  pose proof (amin_24 ((B zh - IZR 24 / 64) + B zl) Ht) as HAm.
  destruct ea_dw_small as [Ea0 Ea1].
  rewrite Eq.
  refine (fast_compose _ _ e1 ea (IZR 15317172 * bpow radix2 (-98)) (IZR 973 * bpow radix2 (-76)) _ (IZR 737994 * bpow radix2 (-21)) _ AP E1 Eea HAm _ Ea0 _).
  - apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0].
  - bpow_num. replace (- prec)%Z with (-53)%Z by reflexivity. bpow_num. clear - Fz. interval with (i_prec 200).
Qed.

Lemma evalcert_25 : EvalCert (IZR (7814761310616205) * bpow radix2 (-53)) (IZR (-8745816857388839) * bpow radix2 (-109)) (IZR (-2648510505610237) * bpow radix2 (-53)) (IZR (-8505991720611995) * bpow radix2 (-56)) (IZR (6757845398777691) * bpow radix2 (-55)) (IZR (-5802094127488669) * bpow radix2 (-57)) (IZR (-193092242444363) * bpow radix2 (-51)) (IZR (2693872762797419) * bpow radix2 (-55)) (IZR (1336167297970227) * bpow radix2 (-56)) (IZR (-8243868174858839) * bpow radix2 (-57)) (IZR (-907817553530397) * bpow radix2 (-44)) (IZR 992 * bpow radix2 (-76)) (IZR 1005 * bpow radix2 (-73)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 31 (-31) (-71)); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_25.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_25.l1 th_ tl_ dg).
Qed.

Lemma segok_25 : SegOkRowA [(0x3fd7d5604b63b3f7)%Z; (0x3c769c885c2b249a)%Z; (0x3febc37be7ec7a8d)%Z; (0xbc6f12462b0e2727)%Z; (0xbfd2d19ccfbdd7fa)%Z; (0xbfbe382786f8309b)%Z; (0x3fc802397e70ef5b)%Z; (0xbfa49cf94f6c1e9d)%Z; (0xbfb5f3b950a20960)%Z; (0x3fb3242042317ad6)%Z; (0x3f92fcf2c49fc0cc)%Z; (0xbfad49c122233a57)%Z; (0xc049cd3df66470e8)%Z] (IZR 992 * bpow radix2 (-76)).
Proof.
  unfold SegOkRowA. cbn [nth].
  destruct (word_ok_intro (0x3fd7d5604b63b3f7)%Z false 6708534022747127%positive 54%nat (6708534022747127)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c769c885c2b249a)%Z false 6364558963451034%positive 108%nat (3182279481725517)%Z 1%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3febc37be7ec7a8d)%Z false 7814761310616205%positive 53%nat (7814761310616205)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc6f12462b0e2727)%Z true 8745816857388839%positive 109%nat (-8745816857388839)%Z 0%Z (-109)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd2d19ccfbdd7fa)%Z true 5297021011220474%positive 54%nat (-2648510505610237)%Z 1%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbfbe382786f8309b)%Z true 8505991720611995%positive 56%nat (-8505991720611995)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fc802397e70ef5b)%Z false 6757845398777691%positive 55%nat (6757845398777691)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfa49cf94f6c1e9d)%Z true 5802094127488669%positive 57%nat (-5802094127488669)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbfb5f3b950a20960)%Z true 6178951758219616%positive 56%nat (-193092242444363)%Z 5%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3fb3242042317ad6)%Z false 5387745525594838%positive 56%nat (2693872762797419)%Z 1%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3f92fcf2c49fc0cc)%Z false 5344669191880908%positive 58%nat (1336167297970227)%Z 2%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0xbfad49c122233a57)%Z true 8243868174858839%positive 57%nat (-8243868174858839)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc049cd3df66470e8)%Z true 7262540428243176%positive 47%nat (-907817553530397)%Z 3%Z (-44)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_25 _ _).
  all: seg_numeric.
Qed.

Lemma row_25 : nth (Z.to_nat (25%Z - 1)) atan2_segments [] = [(0x3fd7d5604b63b3f7)%Z; (0x3c769c885c2b249a)%Z; (0x3febc37be7ec7a8d)%Z; (0xbc6f12462b0e2727)%Z; (0xbfd2d19ccfbdd7fa)%Z; (0xbfbe382786f8309b)%Z; (0x3fc802397e70ef5b)%Z; (0xbfa49cf94f6c1e9d)%Z; (0xbfb5f3b950a20960)%Z; (0x3fb3242042317ad6)%Z; (0x3f92fcf2c49fc0cc)%Z; (0xbfad49c122233a57)%Z; (0xc049cd3df66470e8)%Z].
Proof. reflexivity. Qed.

Lemma fast_25 zh zl : finite zh -> finite zl -> / 128 <= B zh -> B zh <= 1 ->
  Znearest ne (B zh * 64) = 25%Z -> Rabs (B zl) <= bpow radix2 (-53) -> on_grid (-211) (B zl) ->
  exists h l, atan2_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    Rabs (B h + B l - atan (IZR 25 / 64 + ((B zh - IZR 25 / 64) + B zl))) <= bpow radix2 (-63) * atan (IZR 25 / 64 + ((B zh - IZR 25 / 64) + B zl)).
Proof.
  intros Fz Fl L U Hn Hl Hg.
  pose proof (series_segment_a zh zl 25%Z (IZR 992 * bpow radix2 (-76)) ltac:(lia) Fz Fl L U Hn Hl Hg segok_25) as SS.
  cbv zeta in SS. rewrite row_25 in SS. cbn [nth] in SS.
  destruct SS as [h [l [Hs [Fh [Fl' [Nrm [Ht [e1 [ea [E1 [Eea Eq]]]]]]]]]]].
  exists h, l. split; [exact Hs | split; [exact Fh | split; [exact Fl' | split; [exact Nrm | ]]]].
  destruct (word_ok_intro (0x3fd7d5604b63b3f7)%Z false 6708534022747127%positive 54%nat (6708534022747127)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c769c885c2b249a)%Z false 6364558963451034%positive 108%nat (3182279481725517)%Z 1%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3febc37be7ec7a8d)%Z false 7814761310616205%positive 53%nat (7814761310616205)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc6f12462b0e2727)%Z true 8745816857388839%positive 109%nat (-8745816857388839)%Z 0%Z (-109)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd2d19ccfbdd7fa)%Z true 5297021011220474%positive 54%nat (-2648510505610237)%Z 1%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbfbe382786f8309b)%Z true 8505991720611995%positive 56%nat (-8505991720611995)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fc802397e70ef5b)%Z false 6757845398777691%positive 55%nat (6757845398777691)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfa49cf94f6c1e9d)%Z true 5802094127488669%positive 57%nat (-5802094127488669)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbfb5f3b950a20960)%Z true 6178951758219616%positive 56%nat (-193092242444363)%Z 5%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3fb3242042317ad6)%Z false 5387745525594838%positive 56%nat (2693872762797419)%Z 1%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3f92fcf2c49fc0cc)%Z false 5344669191880908%positive 58%nat (1336167297970227)%Z 2%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0xbfad49c122233a57)%Z true 8243868174858839%positive 57%nat (-8243868174858839)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc049cd3df66470e8)%Z true 7262540428243176%positive 47%nat (-907817553530397)%Z 3%Z (-44)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  unfold seg_poly in Eq.
  pose proof (approx_25 _ _ _ _ _ _ _ _ _ _ _ _ _ ((B zh - IZR 25 / 64) + B zl) V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 Ht) as AP.
  pose proof (amin_25 ((B zh - IZR 25 / 64) + B zl) Ht) as HAm.
  destruct ea_dw_small as [Ea0 Ea1].
  rewrite Eq.
  refine (fast_compose _ _ e1 ea (IZR 15227411 * bpow radix2 (-93)) (IZR 992 * bpow radix2 (-76)) _ (IZR 766722 * bpow radix2 (-21)) _ AP E1 Eea HAm _ Ea0 _).
  - apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0].
  - bpow_num. replace (- prec)%Z with (-53)%Z by reflexivity. bpow_num. clear - Fz. interval with (i_prec 200).
Qed.

Lemma evalcert_26 : EvalCert (IZR (966405284666259) * bpow radix2 (-50)) (IZR (-664403633208053) * bpow radix2 (-106)) (IZR (-5391780029118709) * bpow radix2 (-54)) (IZR (-1917200954322005) * bpow radix2 (-54)) (IZR (3316785222468131) * bpow radix2 (-54)) (IZR (-3452553152482011) * bpow radix2 (-56)) (IZR (-87270331773621) * bpow radix2 (-50)) (IZR (5455500829226657) * bpow radix2 (-56)) (IZR (8357210590262413) * bpow radix2 (-61)) (IZR (-7594624232188771) * bpow radix2 (-57)) (IZR (5112205657473649) * bpow radix2 (-53)) (IZR 1009 * bpow radix2 (-76)) (IZR 908 * bpow radix2 (-73)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 1009 (-1009) (-76)); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_26.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_26.l1 th_ tl_ dg).
Qed.

Lemma segok_26 : SegOkRowA [(0x3fd8b24d394a1b25)%Z; (0x3c7b6d0ba3748fa8)%Z; (0x3feb77861d9cdc98)%Z; (0xbc62e22c345bd7a8)%Z; (0xbfd327cb9d57b8f5)%Z; (0xbfbb3ebc8761b154)%Z; (0x3fc7913279f68446)%Z; (0xbfa88828587195b6)%Z; (0xbfb3d7cd47fcad40)%Z; (0x3fb361bfc4ff76a1)%Z; (0x3f6db0d6b88bb48d)%Z; (0xbfaafb453f8feb63)%Z; (0x3fe22986223b8271)%Z] (IZR 1009 * bpow radix2 (-76)).
Proof.
  unfold SegOkRowA. cbn [nth].
  destruct (word_ok_intro (0x3fd8b24d394a1b25)%Z false 6951444184439589%positive 54%nat (6951444184439589)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c7b6d0ba3748fa8)%Z false 7719721125580712%positive 108%nat (964965140697589)%Z 3%Z (-105)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3feb77861d9cdc98)%Z false 7731242277330072%positive 53%nat (966405284666259)%Z 3%Z (-50)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc62e22c345bd7a8)%Z true 5315229065664424%positive 109%nat (-664403633208053)%Z 3%Z (-106)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd327cb9d57b8f5)%Z true 5391780029118709%positive 54%nat (-5391780029118709)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbfbb3ebc8761b154)%Z true 7668803817288020%positive 56%nat (-1917200954322005)%Z 2%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fc7913279f68446)%Z false 6633570444936262%positive 55%nat (3316785222468131)%Z 1%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfa88828587195b6)%Z true 6905106304964022%positive 57%nat (-3452553152482011)%Z 1%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbfb3d7cd47fcad40)%Z true 5585301233511744%positive 56%nat (-87270331773621)%Z 6%Z (-50)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3fb361bfc4ff76a1)%Z false 5455500829226657%positive 56%nat (5455500829226657)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3f6db0d6b88bb48d)%Z false 8357210590262413%positive 61%nat (8357210590262413)%Z 0%Z (-61)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0xbfaafb453f8feb63)%Z true 7594624232188771%positive 57%nat (-7594624232188771)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x3fe22986223b8271)%Z false 5112205657473649%positive 53%nat (5112205657473649)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_26 _ _).
  all: seg_numeric.
Qed.

Lemma row_26 : nth (Z.to_nat (26%Z - 1)) atan2_segments [] = [(0x3fd8b24d394a1b25)%Z; (0x3c7b6d0ba3748fa8)%Z; (0x3feb77861d9cdc98)%Z; (0xbc62e22c345bd7a8)%Z; (0xbfd327cb9d57b8f5)%Z; (0xbfbb3ebc8761b154)%Z; (0x3fc7913279f68446)%Z; (0xbfa88828587195b6)%Z; (0xbfb3d7cd47fcad40)%Z; (0x3fb361bfc4ff76a1)%Z; (0x3f6db0d6b88bb48d)%Z; (0xbfaafb453f8feb63)%Z; (0x3fe22986223b8271)%Z].
Proof. reflexivity. Qed.

Lemma fast_26 zh zl : finite zh -> finite zl -> / 128 <= B zh -> B zh <= 1 ->
  Znearest ne (B zh * 64) = 26%Z -> Rabs (B zl) <= bpow radix2 (-53) -> on_grid (-211) (B zl) ->
  exists h l, atan2_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    Rabs (B h + B l - atan (IZR 26 / 64 + ((B zh - IZR 26 / 64) + B zl))) <= bpow radix2 (-63) * atan (IZR 26 / 64 + ((B zh - IZR 26 / 64) + B zl)).
Proof.
  intros Fz Fl L U Hn Hl Hg.
  pose proof (series_segment_a zh zl 26%Z (IZR 1009 * bpow radix2 (-76)) ltac:(lia) Fz Fl L U Hn Hl Hg segok_26) as SS.
  cbv zeta in SS. rewrite row_26 in SS. cbn [nth] in SS.
  destruct SS as [h [l [Hs [Fh [Fl' [Nrm [Ht [e1 [ea [E1 [Eea Eq]]]]]]]]]]].
  exists h, l. split; [exact Hs | split; [exact Fh | split; [exact Fl' | split; [exact Nrm | ]]]].
  destruct (word_ok_intro (0x3fd8b24d394a1b25)%Z false 6951444184439589%positive 54%nat (6951444184439589)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c7b6d0ba3748fa8)%Z false 7719721125580712%positive 108%nat (964965140697589)%Z 3%Z (-105)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3feb77861d9cdc98)%Z false 7731242277330072%positive 53%nat (966405284666259)%Z 3%Z (-50)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc62e22c345bd7a8)%Z true 5315229065664424%positive 109%nat (-664403633208053)%Z 3%Z (-106)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd327cb9d57b8f5)%Z true 5391780029118709%positive 54%nat (-5391780029118709)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbfbb3ebc8761b154)%Z true 7668803817288020%positive 56%nat (-1917200954322005)%Z 2%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fc7913279f68446)%Z false 6633570444936262%positive 55%nat (3316785222468131)%Z 1%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfa88828587195b6)%Z true 6905106304964022%positive 57%nat (-3452553152482011)%Z 1%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbfb3d7cd47fcad40)%Z true 5585301233511744%positive 56%nat (-87270331773621)%Z 6%Z (-50)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3fb361bfc4ff76a1)%Z false 5455500829226657%positive 56%nat (5455500829226657)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3f6db0d6b88bb48d)%Z false 8357210590262413%positive 61%nat (8357210590262413)%Z 0%Z (-61)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0xbfaafb453f8feb63)%Z true 7594624232188771%positive 57%nat (-7594624232188771)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x3fe22986223b8271)%Z false 5112205657473649%positive 53%nat (5112205657473649)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  unfold seg_poly in Eq.
  pose proof (approx_26 _ _ _ _ _ _ _ _ _ _ _ _ _ ((B zh - IZR 26 / 64) + B zl) V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 Ht) as AP.
  pose proof (amin_26 ((B zh - IZR 26 / 64) + B zl) Ht) as HAm.
  destruct ea_dw_small as [Ea0 Ea1].
  rewrite Eq.
  refine (fast_compose _ _ e1 ea (IZR 10137939 * bpow radix2 (-99)) (IZR 1009 * bpow radix2 (-76)) _ (IZR 795152 * bpow radix2 (-21)) _ AP E1 Eea HAm _ Ea0 _).
  - apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0].
  - bpow_num. replace (- prec)%Z with (-53)%Z by reflexivity. bpow_num. clear - Fz. interval with (i_prec 200).
Qed.

Lemma evalcert_27 : EvalCert (IZR (3823159393514933) * bpow radix2 (-52)) (IZR (-813914792760015) * bpow radix2 (-107)) (IZR (-1369206099895089) * bpow radix2 (-52)) (IZR (-1712112832708065) * bpow radix2 (-54)) (IZR (6488842625048553) * bpow radix2 (-55)) (IZR (-3948176204883101) * bpow radix2 (-56)) (IZR (-2493993216881061) * bpow radix2 (-55)) (IZR (5456383927407223) * bpow radix2 (-56)) (IZR (-5087492116083681) * bpow radix2 (-64)) (IZR (-3458458616360705) * bpow radix2 (-56)) (IZR (-795541399259437) * bpow radix2 (-45)) (IZR 513 * bpow radix2 (-75)) (IZR 813 * bpow radix2 (-73)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 513 (-513) (-75)); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_27.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_27.l1 th_ tl_ dg).
Qed.

Lemma segok_27 : SegOkRowA [(0x3fd98cd5454d6b18)%Z; (0x3c79e6c988fd0a77)%Z; (0x3feb2a495323eb6a)%Z; (0xbc57220270cc9678)%Z; (0xbfd375248cd58cc4)%Z; (0xbfb854a154d5f784)%Z; (0x3fc70d9167ab5fe9)%Z; (0xbfac0db0d067c93a)%Z; (0xbfb1b88c1787634a)%Z; (0x3fb3628d61c05277)%Z; (0xbf32130c106073e1)%Z; (0xbfa892e64a98de02)%Z; (0xc0369c53540e4968)%Z] (IZR 513 * bpow radix2 (-75)).
Proof.
  unfold SegOkRowA. cbn [nth].
  destruct (word_ok_intro (0x3fd98cd5454d6b18)%Z false 7191722036390680%positive 54%nat (898965254548835)%Z 3%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c79e6c988fd0a77)%Z false 7290627678866039%positive 108%nat (7290627678866039)%Z 0%Z (-108)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3feb2a495323eb6a)%Z false 7646318787029866%positive 53%nat (3823159393514933)%Z 1%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc57220270cc9678)%Z true 6511318342080120%positive 110%nat (-813914792760015)%Z 3%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd375248cd58cc4)%Z true 5476824399580356%positive 54%nat (-1369206099895089)%Z 2%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbfb854a154d5f784)%Z true 6848451330832260%positive 56%nat (-1712112832708065)%Z 2%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fc70d9167ab5fe9)%Z false 6488842625048553%positive 55%nat (6488842625048553)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfac0db0d067c93a)%Z true 7896352409766202%positive 57%nat (-3948176204883101)%Z 1%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbfb1b88c1787634a)%Z true 4987986433762122%positive 56%nat (-2493993216881061)%Z 1%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3fb3628d61c05277)%Z false 5456383927407223%positive 56%nat (5456383927407223)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0xbf32130c106073e1)%Z true 5087492116083681%positive 64%nat (-5087492116083681)%Z 0%Z (-64)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0xbfa892e64a98de02)%Z true 6916917232721410%positive 57%nat (-3458458616360705)%Z 1%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc0369c53540e4968)%Z true 6364331194075496%positive 48%nat (-795541399259437)%Z 3%Z (-45)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_27 _ _).
  all: seg_numeric.
Qed.

Lemma row_27 : nth (Z.to_nat (27%Z - 1)) atan2_segments [] = [(0x3fd98cd5454d6b18)%Z; (0x3c79e6c988fd0a77)%Z; (0x3feb2a495323eb6a)%Z; (0xbc57220270cc9678)%Z; (0xbfd375248cd58cc4)%Z; (0xbfb854a154d5f784)%Z; (0x3fc70d9167ab5fe9)%Z; (0xbfac0db0d067c93a)%Z; (0xbfb1b88c1787634a)%Z; (0x3fb3628d61c05277)%Z; (0xbf32130c106073e1)%Z; (0xbfa892e64a98de02)%Z; (0xc0369c53540e4968)%Z].
Proof. reflexivity. Qed.

Lemma fast_27 zh zl : finite zh -> finite zl -> / 128 <= B zh -> B zh <= 1 ->
  Znearest ne (B zh * 64) = 27%Z -> Rabs (B zl) <= bpow radix2 (-53) -> on_grid (-211) (B zl) ->
  exists h l, atan2_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    Rabs (B h + B l - atan (IZR 27 / 64 + ((B zh - IZR 27 / 64) + B zl))) <= bpow radix2 (-63) * atan (IZR 27 / 64 + ((B zh - IZR 27 / 64) + B zl)).
Proof.
  intros Fz Fl L U Hn Hl Hg.
  pose proof (series_segment_a zh zl 27%Z (IZR 513 * bpow radix2 (-75)) ltac:(lia) Fz Fl L U Hn Hl Hg segok_27) as SS.
  cbv zeta in SS. rewrite row_27 in SS. cbn [nth] in SS.
  destruct SS as [h [l [Hs [Fh [Fl' [Nrm [Ht [e1 [ea [E1 [Eea Eq]]]]]]]]]]].
  exists h, l. split; [exact Hs | split; [exact Fh | split; [exact Fl' | split; [exact Nrm | ]]]].
  destruct (word_ok_intro (0x3fd98cd5454d6b18)%Z false 7191722036390680%positive 54%nat (898965254548835)%Z 3%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c79e6c988fd0a77)%Z false 7290627678866039%positive 108%nat (7290627678866039)%Z 0%Z (-108)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3feb2a495323eb6a)%Z false 7646318787029866%positive 53%nat (3823159393514933)%Z 1%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc57220270cc9678)%Z true 6511318342080120%positive 110%nat (-813914792760015)%Z 3%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd375248cd58cc4)%Z true 5476824399580356%positive 54%nat (-1369206099895089)%Z 2%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbfb854a154d5f784)%Z true 6848451330832260%positive 56%nat (-1712112832708065)%Z 2%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fc70d9167ab5fe9)%Z false 6488842625048553%positive 55%nat (6488842625048553)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfac0db0d067c93a)%Z true 7896352409766202%positive 57%nat (-3948176204883101)%Z 1%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbfb1b88c1787634a)%Z true 4987986433762122%positive 56%nat (-2493993216881061)%Z 1%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3fb3628d61c05277)%Z false 5456383927407223%positive 56%nat (5456383927407223)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0xbf32130c106073e1)%Z true 5087492116083681%positive 64%nat (-5087492116083681)%Z 0%Z (-64)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0xbfa892e64a98de02)%Z true 6916917232721410%positive 57%nat (-3458458616360705)%Z 1%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc0369c53540e4968)%Z true 6364331194075496%positive 48%nat (-795541399259437)%Z 3%Z (-45)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  unfold seg_poly in Eq.
  pose proof (approx_27 _ _ _ _ _ _ _ _ _ _ _ _ _ ((B zh - IZR 27 / 64) + B zl) V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 Ht) as AP.
  pose proof (amin_27 ((B zh - IZR 27 / 64) + B zl) Ht) as HAm.
  destruct ea_dw_small as [Ea0 Ea1].
  rewrite Eq.
  refine (fast_compose _ _ e1 ea (IZR 13354619 * bpow radix2 (-94)) (IZR 513 * bpow radix2 (-75)) _ (IZR 823278 * bpow radix2 (-21)) _ AP E1 Eea HAm _ Ea0 _).
  - apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0].
  - bpow_num. replace (- prec)%Z with (-53)%Z by reflexivity. bpow_num. clear - Fz. interval with (i_prec 200).
Qed.

Lemma evalcert_28 : EvalCert (IZR (3780070506907695) * bpow radix2 (-52)) (IZR (3780070506907695) * bpow radix2 (-112)) (IZR (-5552365859326713) * bpow radix2 (-54)) (IZR (-3023677145563087) * bpow radix2 (-55)) (IZR (790730910035853) * bpow radix2 (-52)) (IZR (-4387901790488431) * bpow radix2 (-56)) (IZR (-8787887707757059) * bpow radix2 (-57)) (IZR (5396699825714501) * bpow radix2 (-56)) (IZR (-639320468011779) * bpow radix2 (-57)) (IZR (-3075987586214209) * bpow radix2 (-56)) (IZR (-5433639501116469) * bpow radix2 (-47)) (IZR 520 * bpow radix2 (-75)) (IZR 720 * bpow radix2 (-73)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 65 (-65) (-72)); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_28.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_28.l1 th_ tl_ dg).
Qed.

Lemma segok_28 : SegOkRowA [(0x3fda64eec3cc23fd)%Z; (0xbc724dec1b50b7ff)%Z; (0x3feadbe87f94905e)%Z; (0x3c2adbe87f94905e)%Z; (0xbfd3b9d8eab54af9)%Z; (0xbfb57c09645a7f9e)%Z; (0x3fc67953180b7c68)%Z; (0xbfaf2d8bff100ede)%Z; (0xbfaf38898d259a03)%Z; (0x3fb32c4518123545)%Z; (0xbf722bab2b25d818)%Z; (0xbfa5db3056d1d282)%Z; (0xc0434dddc84d3435)%Z] (IZR 520 * bpow radix2 (-75)).
Proof.
  unfold SegOkRowA. cbn [nth].
  destruct (word_ok_intro (0x3fda64eec3cc23fd)%Z false 7429326044406781%positive 54%nat (7429326044406781)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc724dec1b50b7ff)%Z true 5152226046687231%positive 108%nat (-5152226046687231)%Z 0%Z (-108)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3feadbe87f94905e)%Z false 7560141013815390%positive 53%nat (3780070506907695)%Z 1%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c2adbe87f94905e)%Z false 7560141013815390%positive 113%nat (3780070506907695)%Z 1%Z (-112)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd3b9d8eab54af9)%Z true 5552365859326713%positive 54%nat (-5552365859326713)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbfb57c09645a7f9e)%Z true 6047354291126174%positive 56%nat (-3023677145563087)%Z 1%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fc67953180b7c68)%Z false 6325847280286824%positive 55%nat (790730910035853)%Z 3%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfaf2d8bff100ede)%Z true 8775803580976862%positive 57%nat (-4387901790488431)%Z 1%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbfaf38898d259a03)%Z true 8787887707757059%positive 57%nat (-8787887707757059)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3fb32c4518123545)%Z false 5396699825714501%positive 56%nat (5396699825714501)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0xbf722bab2b25d818)%Z true 5114563744094232%positive 60%nat (-639320468011779)%Z 3%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0xbfa5db3056d1d282)%Z true 6151975172428418%positive 57%nat (-3075987586214209)%Z 1%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc0434dddc84d3435)%Z true 5433639501116469%positive 47%nat (-5433639501116469)%Z 0%Z (-47)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_28 _ _).
  all: seg_numeric.
Qed.

Lemma row_28 : nth (Z.to_nat (28%Z - 1)) atan2_segments [] = [(0x3fda64eec3cc23fd)%Z; (0xbc724dec1b50b7ff)%Z; (0x3feadbe87f94905e)%Z; (0x3c2adbe87f94905e)%Z; (0xbfd3b9d8eab54af9)%Z; (0xbfb57c09645a7f9e)%Z; (0x3fc67953180b7c68)%Z; (0xbfaf2d8bff100ede)%Z; (0xbfaf38898d259a03)%Z; (0x3fb32c4518123545)%Z; (0xbf722bab2b25d818)%Z; (0xbfa5db3056d1d282)%Z; (0xc0434dddc84d3435)%Z].
Proof. reflexivity. Qed.

Lemma fast_28 zh zl : finite zh -> finite zl -> / 128 <= B zh -> B zh <= 1 ->
  Znearest ne (B zh * 64) = 28%Z -> Rabs (B zl) <= bpow radix2 (-53) -> on_grid (-211) (B zl) ->
  exists h l, atan2_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    Rabs (B h + B l - atan (IZR 28 / 64 + ((B zh - IZR 28 / 64) + B zl))) <= bpow radix2 (-63) * atan (IZR 28 / 64 + ((B zh - IZR 28 / 64) + B zl)).
Proof.
  intros Fz Fl L U Hn Hl Hg.
  pose proof (series_segment_a zh zl 28%Z (IZR 520 * bpow radix2 (-75)) ltac:(lia) Fz Fl L U Hn Hl Hg segok_28) as SS.
  cbv zeta in SS. rewrite row_28 in SS. cbn [nth] in SS.
  destruct SS as [h [l [Hs [Fh [Fl' [Nrm [Ht [e1 [ea [E1 [Eea Eq]]]]]]]]]]].
  exists h, l. split; [exact Hs | split; [exact Fh | split; [exact Fl' | split; [exact Nrm | ]]]].
  destruct (word_ok_intro (0x3fda64eec3cc23fd)%Z false 7429326044406781%positive 54%nat (7429326044406781)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc724dec1b50b7ff)%Z true 5152226046687231%positive 108%nat (-5152226046687231)%Z 0%Z (-108)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3feadbe87f94905e)%Z false 7560141013815390%positive 53%nat (3780070506907695)%Z 1%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c2adbe87f94905e)%Z false 7560141013815390%positive 113%nat (3780070506907695)%Z 1%Z (-112)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd3b9d8eab54af9)%Z true 5552365859326713%positive 54%nat (-5552365859326713)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbfb57c09645a7f9e)%Z true 6047354291126174%positive 56%nat (-3023677145563087)%Z 1%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fc67953180b7c68)%Z false 6325847280286824%positive 55%nat (790730910035853)%Z 3%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfaf2d8bff100ede)%Z true 8775803580976862%positive 57%nat (-4387901790488431)%Z 1%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbfaf38898d259a03)%Z true 8787887707757059%positive 57%nat (-8787887707757059)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3fb32c4518123545)%Z false 5396699825714501%positive 56%nat (5396699825714501)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0xbf722bab2b25d818)%Z true 5114563744094232%positive 60%nat (-639320468011779)%Z 3%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0xbfa5db3056d1d282)%Z true 6151975172428418%positive 57%nat (-3075987586214209)%Z 1%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc0434dddc84d3435)%Z true 5433639501116469%positive 47%nat (-5433639501116469)%Z 0%Z (-47)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  unfold seg_poly in Eq.
  pose proof (approx_28 _ _ _ _ _ _ _ _ _ _ _ _ _ ((B zh - IZR 28 / 64) + B zl) V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 Ht) as AP.
  pose proof (amin_28 ((B zh - IZR 28 / 64) + B zl) Ht) as HAm.
  destruct ea_dw_small as [Ea0 Ea1].
  rewrite Eq.
  refine (fast_compose _ _ e1 ea (IZR 11390225 * bpow radix2 (-93)) (IZR 520 * bpow radix2 (-75)) _ (IZR 851095 * bpow radix2 (-21)) _ AP E1 Eea HAm _ Ea0 _).
  - apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0].
  - bpow_num. replace (- prec)%Z with (-53)%Z by reflexivity. bpow_num. clear - Fz. interval with (i_prec 200).
Qed.

Lemma evalcert_29 : EvalCert (IZR (1868213902542997) * bpow radix2 (-51)) (IZR (-5560855444288139) * bpow radix2 (-107)) (IZR (-175582590800071) * bpow radix2 (-49)) (IZR (-5267660043842457) * bpow radix2 (-56)) (IZR (3073378987415369) * bpow radix2 (-54)) (IZR (-4772336163764373) * bpow radix2 (-56)) (IZR (-7618793713356627) * bpow radix2 (-57)) (IZR (5283154439110605) * bpow radix2 (-56)) (IZR (-5760520606679521) * bpow radix2 (-58)) (IZR (-5268393089322895) * bpow radix2 (-57)) (IZR (4777922186621111) * bpow radix2 (-47)) (IZR 526 * bpow radix2 (-75)) (IZR 629 * bpow radix2 (-73)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 263 (-263) (-74)); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_29.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_29.l1 th_ tl_ dg).
Qed.

Lemma segok_29 : SegOkRowA [(0x3fdb3a911da65c6c)%Z; (0x3c7ae187b1ca5040)%Z; (0x3fea8c85c81a2254)%Z; (0xbc83c1918d67728b)%Z; (0xbfd3f6203e8218e0)%Z; (0xbfb2b6e8adb5f399)%Z; (0x3fc5d6719d9c2e92)%Z; (0xbfb0f46a19ca3895)%Z; (0xbfab1140a4e6cf53)%Z; (0x3fb2c5003fa2ffcd)%Z; (0xbf947729b87b81e1)%Z; (0xbfa2b7935aa04f8f)%Z; (0x4040f97eb2b2b0b7)%Z] (IZR 526 * bpow radix2 (-75)).
Proof.
  unfold SegOkRowA. cbn [nth].
  destruct (word_ok_intro (0x3fdb3a911da65c6c)%Z false 7664219313298540%positive 54%nat (1916054828324635)%Z 2%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c7ae187b1ca5040)%Z false 7566322314137664%positive 108%nat (118223786158401)%Z 6%Z (-102)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fea8c85c81a2254)%Z false 7472855610171988%positive 53%nat (1868213902542997)%Z 2%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc83c1918d67728b)%Z true 5560855444288139%positive 107%nat (-5560855444288139)%Z 0%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd3f6203e8218e0)%Z true 5618642905602272%positive 54%nat (-175582590800071)%Z 5%Z (-49)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbfb2b6e8adb5f399)%Z true 5267660043842457%positive 56%nat (-5267660043842457)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fc5d6719d9c2e92)%Z false 6146757974830738%positive 55%nat (3073378987415369)%Z 1%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfb0f46a19ca3895)%Z true 4772336163764373%positive 56%nat (-4772336163764373)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbfab1140a4e6cf53)%Z true 7618793713356627%positive 57%nat (-7618793713356627)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3fb2c5003fa2ffcd)%Z false 5283154439110605%positive 56%nat (5283154439110605)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0xbf947729b87b81e1)%Z true 5760520606679521%positive 58%nat (-5760520606679521)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0xbfa2b7935aa04f8f)%Z true 5268393089322895%positive 57%nat (-5268393089322895)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x4040f97eb2b2b0b7)%Z false 4777922186621111%positive 47%nat (4777922186621111)%Z 0%Z (-47)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_29 _ _).
  all: seg_numeric.
Qed.

Lemma row_29 : nth (Z.to_nat (29%Z - 1)) atan2_segments [] = [(0x3fdb3a911da65c6c)%Z; (0x3c7ae187b1ca5040)%Z; (0x3fea8c85c81a2254)%Z; (0xbc83c1918d67728b)%Z; (0xbfd3f6203e8218e0)%Z; (0xbfb2b6e8adb5f399)%Z; (0x3fc5d6719d9c2e92)%Z; (0xbfb0f46a19ca3895)%Z; (0xbfab1140a4e6cf53)%Z; (0x3fb2c5003fa2ffcd)%Z; (0xbf947729b87b81e1)%Z; (0xbfa2b7935aa04f8f)%Z; (0x4040f97eb2b2b0b7)%Z].
Proof. reflexivity. Qed.

Lemma fast_29 zh zl : finite zh -> finite zl -> / 128 <= B zh -> B zh <= 1 ->
  Znearest ne (B zh * 64) = 29%Z -> Rabs (B zl) <= bpow radix2 (-53) -> on_grid (-211) (B zl) ->
  exists h l, atan2_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    Rabs (B h + B l - atan (IZR 29 / 64 + ((B zh - IZR 29 / 64) + B zl))) <= bpow radix2 (-63) * atan (IZR 29 / 64 + ((B zh - IZR 29 / 64) + B zl)).
Proof.
  intros Fz Fl L U Hn Hl Hg.
  pose proof (series_segment_a zh zl 29%Z (IZR 526 * bpow radix2 (-75)) ltac:(lia) Fz Fl L U Hn Hl Hg segok_29) as SS.
  cbv zeta in SS. rewrite row_29 in SS. cbn [nth] in SS.
  destruct SS as [h [l [Hs [Fh [Fl' [Nrm [Ht [e1 [ea [E1 [Eea Eq]]]]]]]]]]].
  exists h, l. split; [exact Hs | split; [exact Fh | split; [exact Fl' | split; [exact Nrm | ]]]].
  destruct (word_ok_intro (0x3fdb3a911da65c6c)%Z false 7664219313298540%positive 54%nat (1916054828324635)%Z 2%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c7ae187b1ca5040)%Z false 7566322314137664%positive 108%nat (118223786158401)%Z 6%Z (-102)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fea8c85c81a2254)%Z false 7472855610171988%positive 53%nat (1868213902542997)%Z 2%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc83c1918d67728b)%Z true 5560855444288139%positive 107%nat (-5560855444288139)%Z 0%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd3f6203e8218e0)%Z true 5618642905602272%positive 54%nat (-175582590800071)%Z 5%Z (-49)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbfb2b6e8adb5f399)%Z true 5267660043842457%positive 56%nat (-5267660043842457)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fc5d6719d9c2e92)%Z false 6146757974830738%positive 55%nat (3073378987415369)%Z 1%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfb0f46a19ca3895)%Z true 4772336163764373%positive 56%nat (-4772336163764373)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbfab1140a4e6cf53)%Z true 7618793713356627%positive 57%nat (-7618793713356627)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3fb2c5003fa2ffcd)%Z false 5283154439110605%positive 56%nat (5283154439110605)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0xbf947729b87b81e1)%Z true 5760520606679521%positive 58%nat (-5760520606679521)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0xbfa2b7935aa04f8f)%Z true 5268393089322895%positive 57%nat (-5268393089322895)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x4040f97eb2b2b0b7)%Z false 4777922186621111%positive 47%nat (4777922186621111)%Z 0%Z (-47)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  unfold seg_poly in Eq.
  pose proof (approx_29 _ _ _ _ _ _ _ _ _ _ _ _ _ ((B zh - IZR 29 / 64) + B zl) V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 Ht) as AP.
  pose proof (amin_29 ((B zh - IZR 29 / 64) + B zl) Ht) as HAm.
  destruct ea_dw_small as [Ea0 Ea1].
  rewrite Eq.
  refine (fast_compose _ _ e1 ea (IZR 9829017 * bpow radix2 (-93)) (IZR 526 * bpow radix2 (-75)) _ (IZR 878598 * bpow radix2 (-21)) _ AP E1 Eea HAm _ Ea0 _).
  - apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0].
  - bpow_num. replace (- prec)%Z with (-53)%Z by reflexivity. bpow_num. clear - Fz. interval with (i_prec 200).
Qed.

Lemma evalcert_30 : EvalCert (IZR (923075664216851) * bpow radix2 (-50)) (IZR (8884603268087191) * bpow radix2 (-107)) (IZR (-5675917615040365) * bpow radix2 (-54)) (IZR (-4511246182707645) * bpow radix2 (-56)) (IZR (1488428395408071) * bpow radix2 (-53)) (IZR (-318914852226441) * bpow radix2 (-52)) (IZR (-3239935669922181) * bpow radix2 (-56)) (IZR (5122681172489107) * bpow radix2 (-56)) (IZR (-3390570345496317) * bpow radix2 (-57)) (IZR (-2277296439480859) * bpow radix2 (-56)) (IZR (3451703339069841) * bpow radix2 (-47)) (IZR 531 * bpow radix2 (-75)) (IZR 542 * bpow radix2 (-73)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 531 (-531) (-75)); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_30.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_30.l1 th_ tl_ dg).
Qed.

Lemma segok_30 : SegOkRowA [(0x3fdc0db4c94ec9f0)%Z; (0xbc7cc1ce70934c34)%Z; (0x3fea3c4268881898)%Z; (0x3c8f907fe5c3bd97)%Z; (0xbfd42a378d38076d)%Z; (0xbfb006f45a36f1bd)%Z; (0x3fc526def720ab1c)%Z; (0xbfb220d267b05890)%Z; (0xbfa705689d66d30a)%Z; (0x3fb2330d27957393)%Z; (0xbf9817695a0efdfa)%Z; (0xbfa02e60caa5a436)%Z; (0x4038869c9eca6322)%Z] (IZR 531 * bpow radix2 (-75)).
Proof.
  unfold SegOkRowA. cbn [nth].
  destruct (word_ok_intro (0x3fdc0db4c94ec9f0)%Z false 7896369470556656%positive 54%nat (493523091909791)%Z 4%Z (-50)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc7cc1ce70934c34)%Z true 8094391744023604%positive 108%nat (-2023597936005901)%Z 2%Z (-106)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fea3c4268881898)%Z false 7384605313734808%positive 53%nat (923075664216851)%Z 3%Z (-50)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c8f907fe5c3bd97)%Z false 8884603268087191%positive 107%nat (8884603268087191)%Z 0%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd42a378d38076d)%Z true 5675917615040365%positive 54%nat (-5675917615040365)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbfb006f45a36f1bd)%Z true 4511246182707645%positive 56%nat (-4511246182707645)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fc526def720ab1c)%Z false 5953713581632284%positive 55%nat (1488428395408071)%Z 2%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfb220d267b05890)%Z true 5102637635623056%positive 56%nat (-318914852226441)%Z 4%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbfa705689d66d30a)%Z true 6479871339844362%positive 57%nat (-3239935669922181)%Z 1%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3fb2330d27957393)%Z false 5122681172489107%positive 56%nat (5122681172489107)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0xbf9817695a0efdfa)%Z true 6781140690992634%positive 58%nat (-3390570345496317)%Z 1%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0xbfa02e60caa5a436)%Z true 4554592878961718%positive 57%nat (-2277296439480859)%Z 1%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x4038869c9eca6322)%Z false 6903406678139682%positive 48%nat (3451703339069841)%Z 1%Z (-47)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_30 _ _).
  all: seg_numeric.
Qed.

Lemma row_30 : nth (Z.to_nat (30%Z - 1)) atan2_segments [] = [(0x3fdc0db4c94ec9f0)%Z; (0xbc7cc1ce70934c34)%Z; (0x3fea3c4268881898)%Z; (0x3c8f907fe5c3bd97)%Z; (0xbfd42a378d38076d)%Z; (0xbfb006f45a36f1bd)%Z; (0x3fc526def720ab1c)%Z; (0xbfb220d267b05890)%Z; (0xbfa705689d66d30a)%Z; (0x3fb2330d27957393)%Z; (0xbf9817695a0efdfa)%Z; (0xbfa02e60caa5a436)%Z; (0x4038869c9eca6322)%Z].
Proof. reflexivity. Qed.

Lemma fast_30 zh zl : finite zh -> finite zl -> / 128 <= B zh -> B zh <= 1 ->
  Znearest ne (B zh * 64) = 30%Z -> Rabs (B zl) <= bpow radix2 (-53) -> on_grid (-211) (B zl) ->
  exists h l, atan2_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    Rabs (B h + B l - atan (IZR 30 / 64 + ((B zh - IZR 30 / 64) + B zl))) <= bpow radix2 (-63) * atan (IZR 30 / 64 + ((B zh - IZR 30 / 64) + B zl)).
Proof.
  intros Fz Fl L U Hn Hl Hg.
  pose proof (series_segment_a zh zl 30%Z (IZR 531 * bpow radix2 (-75)) ltac:(lia) Fz Fl L U Hn Hl Hg segok_30) as SS.
  cbv zeta in SS. rewrite row_30 in SS. cbn [nth] in SS.
  destruct SS as [h [l [Hs [Fh [Fl' [Nrm [Ht [e1 [ea [E1 [Eea Eq]]]]]]]]]]].
  exists h, l. split; [exact Hs | split; [exact Fh | split; [exact Fl' | split; [exact Nrm | ]]]].
  destruct (word_ok_intro (0x3fdc0db4c94ec9f0)%Z false 7896369470556656%positive 54%nat (493523091909791)%Z 4%Z (-50)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc7cc1ce70934c34)%Z true 8094391744023604%positive 108%nat (-2023597936005901)%Z 2%Z (-106)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fea3c4268881898)%Z false 7384605313734808%positive 53%nat (923075664216851)%Z 3%Z (-50)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c8f907fe5c3bd97)%Z false 8884603268087191%positive 107%nat (8884603268087191)%Z 0%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd42a378d38076d)%Z true 5675917615040365%positive 54%nat (-5675917615040365)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbfb006f45a36f1bd)%Z true 4511246182707645%positive 56%nat (-4511246182707645)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fc526def720ab1c)%Z false 5953713581632284%positive 55%nat (1488428395408071)%Z 2%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfb220d267b05890)%Z true 5102637635623056%positive 56%nat (-318914852226441)%Z 4%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbfa705689d66d30a)%Z true 6479871339844362%positive 57%nat (-3239935669922181)%Z 1%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3fb2330d27957393)%Z false 5122681172489107%positive 56%nat (5122681172489107)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0xbf9817695a0efdfa)%Z true 6781140690992634%positive 58%nat (-3390570345496317)%Z 1%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0xbfa02e60caa5a436)%Z true 4554592878961718%positive 57%nat (-2277296439480859)%Z 1%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x4038869c9eca6322)%Z false 6903406678139682%positive 48%nat (3451703339069841)%Z 1%Z (-47)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  unfold seg_poly in Eq.
  pose proof (approx_30 _ _ _ _ _ _ _ _ _ _ _ _ _ ((B zh - IZR 30 / 64) + B zl) V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 Ht) as AP.
  pose proof (amin_30 ((B zh - IZR 30 / 64) + B zl) Ht) as HAm.
  destruct ea_dw_small as [Ea0 Ea1].
  rewrite Eq.
  refine (fast_compose _ _ e1 ea (IZR 14425111 * bpow radix2 (-94)) (IZR 531 * bpow radix2 (-75)) _ (IZR 905784 * bpow radix2 (-21)) _ AP E1 Eea HAm _ Ea0 _).
  - apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0].
  - bpow_num. replace (- prec)%Z with (-53)%Z by reflexivity. bpow_num. clear - Fz. interval with (i_prec 200).
Qed.

Lemma evalcert_31 : EvalCert (IZR (1823882150851251) * bpow radix2 (-51)) (IZR (-7110290572459173) * bpow radix2 (-107)) (IZR (-5724472513013853) * bpow radix2 (-54)) (IZR (-7559452352944883) * bpow radix2 (-57)) (IZR (2874399047264529) * bpow radix2 (-54)) (IZR (-5380445776367535) * bpow radix2 (-56)) (IZR (-5380572752810803) * bpow radix2 (-57)) (IZR (4922223630145143) * bpow radix2 (-56)) (IZR (-3350011511939673) * bpow radix2 (-57)) (IZR (-7537874579384055) * bpow radix2 (-58)) (IZR (-1986677716946009) * bpow radix2 (-48)) (IZR 535 * bpow radix2 (-75)) (IZR 913 * bpow radix2 (-74)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 535 (-535) (-75)); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_31.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_31.l1 th_ tl_ dg).
Qed.

Lemma segok_31 : SegOkRowA [(0x3fdcde53432c1351)%Z; (0xbc7a2cfa4418f1ad)%Z; (0x3fe9eb3e9edacacc)%Z; (0xbc8942c587d23ca5)%Z; (0xbfd456609eaa285d)%Z; (0xbfaadb4828319af3)%Z; (0x3fc46c805c4f5222)%Z; (0xbfb31d7ca73bcfaf)%Z; (0xbfa31d9a379e9333)%Z; (0x3fb17cbc7efad677)%Z; (0xbf97cda2ac5344b2)%Z; (0xbf9ac7a830aa66f7)%Z; (0xc01c3b7dce683164)%Z] (IZR 535 * bpow radix2 (-75)).
Proof.
  unfold SegOkRowA. cbn [nth].
  destruct (word_ok_intro (0x3fdcde53432c1351)%Z false 8125748538512209%positive 54%nat (8125748538512209)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc7a2cfa4418f1ad)%Z true 7367802790408621%positive 108%nat (-7367802790408621)%Z 0%Z (-108)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fe9eb3e9edacacc)%Z false 7295528603405004%positive 53%nat (1823882150851251)%Z 2%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc8942c587d23ca5)%Z true 7110290572459173%positive 107%nat (-7110290572459173)%Z 0%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd456609eaa285d)%Z true 5724472513013853%positive 54%nat (-5724472513013853)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbfaadb4828319af3)%Z true 7559452352944883%positive 57%nat (-7559452352944883)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fc46c805c4f5222)%Z false 5748798094529058%positive 55%nat (2874399047264529)%Z 1%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfb31d7ca73bcfaf)%Z true 5380445776367535%positive 56%nat (-5380445776367535)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbfa31d9a379e9333)%Z true 5380572752810803%positive 57%nat (-5380572752810803)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3fb17cbc7efad677)%Z false 4922223630145143%positive 56%nat (4922223630145143)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0xbf97cda2ac5344b2)%Z true 6700023023879346%positive 58%nat (-3350011511939673)%Z 1%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0xbf9ac7a830aa66f7)%Z true 7537874579384055%positive 58%nat (-7537874579384055)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc01c3b7dce683164)%Z true 7946710867784036%positive 50%nat (-1986677716946009)%Z 2%Z (-48)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_31 _ _).
  all: seg_numeric.
Qed.

Lemma row_31 : nth (Z.to_nat (31%Z - 1)) atan2_segments [] = [(0x3fdcde53432c1351)%Z; (0xbc7a2cfa4418f1ad)%Z; (0x3fe9eb3e9edacacc)%Z; (0xbc8942c587d23ca5)%Z; (0xbfd456609eaa285d)%Z; (0xbfaadb4828319af3)%Z; (0x3fc46c805c4f5222)%Z; (0xbfb31d7ca73bcfaf)%Z; (0xbfa31d9a379e9333)%Z; (0x3fb17cbc7efad677)%Z; (0xbf97cda2ac5344b2)%Z; (0xbf9ac7a830aa66f7)%Z; (0xc01c3b7dce683164)%Z].
Proof. reflexivity. Qed.

Lemma fast_31 zh zl : finite zh -> finite zl -> / 128 <= B zh -> B zh <= 1 ->
  Znearest ne (B zh * 64) = 31%Z -> Rabs (B zl) <= bpow radix2 (-53) -> on_grid (-211) (B zl) ->
  exists h l, atan2_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    Rabs (B h + B l - atan (IZR 31 / 64 + ((B zh - IZR 31 / 64) + B zl))) <= bpow radix2 (-63) * atan (IZR 31 / 64 + ((B zh - IZR 31 / 64) + B zl)).
Proof.
  intros Fz Fl L U Hn Hl Hg.
  pose proof (series_segment_a zh zl 31%Z (IZR 535 * bpow radix2 (-75)) ltac:(lia) Fz Fl L U Hn Hl Hg segok_31) as SS.
  cbv zeta in SS. rewrite row_31 in SS. cbn [nth] in SS.
  destruct SS as [h [l [Hs [Fh [Fl' [Nrm [Ht [e1 [ea [E1 [Eea Eq]]]]]]]]]]].
  exists h, l. split; [exact Hs | split; [exact Fh | split; [exact Fl' | split; [exact Nrm | ]]]].
  destruct (word_ok_intro (0x3fdcde53432c1351)%Z false 8125748538512209%positive 54%nat (8125748538512209)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc7a2cfa4418f1ad)%Z true 7367802790408621%positive 108%nat (-7367802790408621)%Z 0%Z (-108)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fe9eb3e9edacacc)%Z false 7295528603405004%positive 53%nat (1823882150851251)%Z 2%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc8942c587d23ca5)%Z true 7110290572459173%positive 107%nat (-7110290572459173)%Z 0%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd456609eaa285d)%Z true 5724472513013853%positive 54%nat (-5724472513013853)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbfaadb4828319af3)%Z true 7559452352944883%positive 57%nat (-7559452352944883)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fc46c805c4f5222)%Z false 5748798094529058%positive 55%nat (2874399047264529)%Z 1%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfb31d7ca73bcfaf)%Z true 5380445776367535%positive 56%nat (-5380445776367535)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbfa31d9a379e9333)%Z true 5380572752810803%positive 57%nat (-5380572752810803)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3fb17cbc7efad677)%Z false 4922223630145143%positive 56%nat (4922223630145143)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0xbf97cda2ac5344b2)%Z true 6700023023879346%positive 58%nat (-3350011511939673)%Z 1%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0xbf9ac7a830aa66f7)%Z true 7537874579384055%positive 58%nat (-7537874579384055)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc01c3b7dce683164)%Z true 7946710867784036%positive 50%nat (-1986677716946009)%Z 2%Z (-48)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  unfold seg_poly in Eq.
  pose proof (approx_31 _ _ _ _ _ _ _ _ _ _ _ _ _ ((B zh - IZR 31 / 64) + B zl) V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 Ht) as AP.
  pose proof (amin_31 ((B zh - IZR 31 / 64) + B zl) Ht) as HAm.
  destruct ea_dw_small as [Ea0 Ea1].
  rewrite Eq.
  refine (fast_compose _ _ e1 ea (IZR 16730336 * bpow radix2 (-96)) (IZR 535 * bpow radix2 (-75)) _ (IZR 932649 * bpow radix2 (-21)) _ AP E1 Eea HAm _ Ea0 _).
  - apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0].
  - bpow_num. replace (- prec)%Z with (-53)%Z by reflexivity. bpow_num. clear - Fz. interval with (i_prec 200).
Qed.

Lemma evalcert_32 : EvalCert (IZR (3602879701896397) * bpow radix2 (-52)) (IZR (-3602879701896397) * bpow radix2 (-106)) (IZR (-5764607523034235) * bpow radix2 (-54)) (IZR (-6148914691236517) * bpow radix2 (-57)) (IZR (5534023222165295) * bpow radix2 (-55)) (IZR (-2803905099208917) * bpow radix2 (-55)) (IZR (-8657696624647703) * bpow radix2 (-58)) (IZR (2344317790266149) * bpow radix2 (-55)) (IZR (-7393138750766963) * bpow radix2 (-58)) (IZR (-3018913302485285) * bpow radix2 (-57)) (IZR (-7667738632846753) * bpow radix2 (-49)) (IZR 539 * bpow radix2 (-75)) (IZR 749 * bpow radix2 (-74)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 539 (-539) (-75)); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_32.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_32.l1 th_ tl_ dg).
Qed.

Lemma segok_32 : SegOkRowA [(0x3fddac670561bb4f)%Z; (0x3c7a2b7f222f65e2)%Z; (0x3fe999999999999a)%Z; (0xbc8999999999999a)%Z; (0xbfd47ae147ae147b)%Z; (0xbfa5d867c3ece2a5)%Z; (0x3fc3a92a3055ff2f)%Z; (0xbfb3ec460ed831aa)%Z; (0xbf9ec22113e29e17)%Z; (0x3fb0a84a0a42464a)%Z; (0xbf9a44054103bf73)%Z; (0xbf95735f0e01324a)%Z; (0xc02b3dc48570fda1)%Z] (IZR 539 * bpow radix2 (-75)).
Proof.
  unfold SegOkRowA. cbn [nth].
  destruct (word_ok_intro (0x3fddac670561bb4f)%Z false 8352332796509007%positive 54%nat (8352332796509007)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c7a2b7f222f65e2)%Z false 7366174428849634%positive 108%nat (3683087214424817)%Z 1%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fe999999999999a)%Z false 7205759403792794%positive 53%nat (3602879701896397)%Z 1%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc8999999999999a)%Z true 7205759403792794%positive 107%nat (-3602879701896397)%Z 1%Z (-106)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd47ae147ae147b)%Z true 5764607523034235%positive 54%nat (-5764607523034235)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbfa5d867c3ece2a5)%Z true 6148914691236517%positive 57%nat (-6148914691236517)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fc3a92a3055ff2f)%Z false 5534023222165295%positive 55%nat (5534023222165295)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfb3ec460ed831aa)%Z true 5607810198417834%positive 56%nat (-2803905099208917)%Z 1%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbf9ec22113e29e17)%Z true 8657696624647703%positive 58%nat (-8657696624647703)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3fb0a84a0a42464a)%Z false 4688635580532298%positive 56%nat (2344317790266149)%Z 1%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0xbf9a44054103bf73)%Z true 7393138750766963%positive 58%nat (-7393138750766963)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0xbf95735f0e01324a)%Z true 6037826604970570%positive 58%nat (-3018913302485285)%Z 1%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc02b3dc48570fda1)%Z true 7667738632846753%positive 49%nat (-7667738632846753)%Z 0%Z (-49)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_32 _ _).
  all: seg_numeric.
Qed.

Lemma row_32 : nth (Z.to_nat (32%Z - 1)) atan2_segments [] = [(0x3fddac670561bb4f)%Z; (0x3c7a2b7f222f65e2)%Z; (0x3fe999999999999a)%Z; (0xbc8999999999999a)%Z; (0xbfd47ae147ae147b)%Z; (0xbfa5d867c3ece2a5)%Z; (0x3fc3a92a3055ff2f)%Z; (0xbfb3ec460ed831aa)%Z; (0xbf9ec22113e29e17)%Z; (0x3fb0a84a0a42464a)%Z; (0xbf9a44054103bf73)%Z; (0xbf95735f0e01324a)%Z; (0xc02b3dc48570fda1)%Z].
Proof. reflexivity. Qed.

Lemma fast_32 zh zl : finite zh -> finite zl -> / 128 <= B zh -> B zh <= 1 ->
  Znearest ne (B zh * 64) = 32%Z -> Rabs (B zl) <= bpow radix2 (-53) -> on_grid (-211) (B zl) ->
  exists h l, atan2_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    Rabs (B h + B l - atan (IZR 32 / 64 + ((B zh - IZR 32 / 64) + B zl))) <= bpow radix2 (-63) * atan (IZR 32 / 64 + ((B zh - IZR 32 / 64) + B zl)).
Proof.
  intros Fz Fl L U Hn Hl Hg.
  pose proof (series_segment_a zh zl 32%Z (IZR 539 * bpow radix2 (-75)) ltac:(lia) Fz Fl L U Hn Hl Hg segok_32) as SS.
  cbv zeta in SS. rewrite row_32 in SS. cbn [nth] in SS.
  destruct SS as [h [l [Hs [Fh [Fl' [Nrm [Ht [e1 [ea [E1 [Eea Eq]]]]]]]]]]].
  exists h, l. split; [exact Hs | split; [exact Fh | split; [exact Fl' | split; [exact Nrm | ]]]].
  destruct (word_ok_intro (0x3fddac670561bb4f)%Z false 8352332796509007%positive 54%nat (8352332796509007)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c7a2b7f222f65e2)%Z false 7366174428849634%positive 108%nat (3683087214424817)%Z 1%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fe999999999999a)%Z false 7205759403792794%positive 53%nat (3602879701896397)%Z 1%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc8999999999999a)%Z true 7205759403792794%positive 107%nat (-3602879701896397)%Z 1%Z (-106)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd47ae147ae147b)%Z true 5764607523034235%positive 54%nat (-5764607523034235)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbfa5d867c3ece2a5)%Z true 6148914691236517%positive 57%nat (-6148914691236517)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fc3a92a3055ff2f)%Z false 5534023222165295%positive 55%nat (5534023222165295)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfb3ec460ed831aa)%Z true 5607810198417834%positive 56%nat (-2803905099208917)%Z 1%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbf9ec22113e29e17)%Z true 8657696624647703%positive 58%nat (-8657696624647703)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3fb0a84a0a42464a)%Z false 4688635580532298%positive 56%nat (2344317790266149)%Z 1%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0xbf9a44054103bf73)%Z true 7393138750766963%positive 58%nat (-7393138750766963)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0xbf95735f0e01324a)%Z true 6037826604970570%positive 58%nat (-3018913302485285)%Z 1%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc02b3dc48570fda1)%Z true 7667738632846753%positive 49%nat (-7667738632846753)%Z 0%Z (-49)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  unfold seg_poly in Eq.
  pose proof (approx_32 _ _ _ _ _ _ _ _ _ _ _ _ _ ((B zh - IZR 32 / 64) + B zl) V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 Ht) as AP.
  pose proof (amin_32 ((B zh - IZR 32 / 64) + B zl) Ht) as HAm.
  destruct ea_dw_small as [Ea0 Ea1].
  rewrite Eq.
  refine (fast_compose _ _ e1 ea (IZR 16106542 * bpow radix2 (-95)) (IZR 539 * bpow radix2 (-75)) _ (IZR 959190 * bpow radix2 (-21)) _ AP E1 Eea HAm _ Ea0 _).
  - apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0].
  - bpow_num. replace (- prec)%Z with (-53)%Z by reflexivity. bpow_num. clear - Fz. interval with (i_prec 200).
Qed.

Lemma evalcert_33 : EvalCert (IZR (1778856709133033) * bpow radix2 (-51)) (IZR (-8255006915820481) * bpow radix2 (-108)) (IZR (-5796637021699465) * bpow radix2 (-54)) (IZR (-4793101683345109) * bpow radix2 (-57)) (IZR (5311313746328417) * bpow radix2 (-55)) (IZR (-5787120438528409) * bpow radix2 (-56)) (IZR (-6662498974432421) * bpow radix2 (-58)) (IZR (4428528435466205) * bpow radix2 (-56)) (IZR (-3721093674278759) * bpow radix2 (-57)) (IZR (-4578702448844611) * bpow radix2 (-58)) (IZR (-2197858101003017) * bpow radix2 (-46)) (IZR 542 * bpow radix2 (-75)) (IZR 591 * bpow radix2 (-74)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 271 (-271) (-74)); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_33.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_33.l1 th_ tl_ dg).
Qed.

Lemma segok_33 : SegOkRowA [(0x3fde77eb7f175a34)%Z; (0x3c70e53dc1bf3435)%Z; (0x3fe9477169044ba4)%Z; (0xbc7d53e292d5fbc1)%Z; (0xbfd49802ba91fd89)%Z; (0xbfa1074cf33546d5)%Z; (0x3fc2de9c9923fb61)%Z; (0xbfb48f5afa02c999)%Z; (0xbf97ab81ecaffca5)%Z; (0x3faf7772408c1fba)%Z; (0xbf9a70a145433ece)%Z; (0xbf90444e3cfedf43)%Z; (0xc03f3bc2dd820c24)%Z] (IZR 542 * bpow radix2 (-75)).
Proof.
  unfold SegOkRowA. cbn [nth].
  destruct (word_ok_intro (0x3fde77eb7f175a34)%Z false 8576102634576436%positive 54%nat (2144025658644109)%Z 2%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c70e53dc1bf3435)%Z false 4755653033669685%positive 108%nat (4755653033669685)%Z 0%Z (-108)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fe9477169044ba4)%Z false 7115426836532132%positive 53%nat (1778856709133033)%Z 2%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc7d53e292d5fbc1)%Z true 8255006915820481%positive 108%nat (-8255006915820481)%Z 0%Z (-108)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd49802ba91fd89)%Z true 5796637021699465%positive 54%nat (-5796637021699465)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbfa1074cf33546d5)%Z true 4793101683345109%positive 57%nat (-4793101683345109)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fc2de9c9923fb61)%Z false 5311313746328417%positive 55%nat (5311313746328417)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfb48f5afa02c999)%Z true 5787120438528409%positive 56%nat (-5787120438528409)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbf97ab81ecaffca5)%Z true 6662498974432421%positive 58%nat (-6662498974432421)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3faf7772408c1fba)%Z false 8857056870932410%positive 57%nat (4428528435466205)%Z 1%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0xbf9a70a145433ece)%Z true 7442187348557518%positive 58%nat (-3721093674278759)%Z 1%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0xbf90444e3cfedf43)%Z true 4578702448844611%positive 58%nat (-4578702448844611)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc03f3bc2dd820c24)%Z true 8791432404012068%positive 48%nat (-2197858101003017)%Z 2%Z (-46)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_33 _ _).
  all: seg_numeric.
Qed.

Lemma row_33 : nth (Z.to_nat (33%Z - 1)) atan2_segments [] = [(0x3fde77eb7f175a34)%Z; (0x3c70e53dc1bf3435)%Z; (0x3fe9477169044ba4)%Z; (0xbc7d53e292d5fbc1)%Z; (0xbfd49802ba91fd89)%Z; (0xbfa1074cf33546d5)%Z; (0x3fc2de9c9923fb61)%Z; (0xbfb48f5afa02c999)%Z; (0xbf97ab81ecaffca5)%Z; (0x3faf7772408c1fba)%Z; (0xbf9a70a145433ece)%Z; (0xbf90444e3cfedf43)%Z; (0xc03f3bc2dd820c24)%Z].
Proof. reflexivity. Qed.

Lemma fast_33 zh zl : finite zh -> finite zl -> / 128 <= B zh -> B zh <= 1 ->
  Znearest ne (B zh * 64) = 33%Z -> Rabs (B zl) <= bpow radix2 (-53) -> on_grid (-211) (B zl) ->
  exists h l, atan2_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    Rabs (B h + B l - atan (IZR 33 / 64 + ((B zh - IZR 33 / 64) + B zl))) <= bpow radix2 (-63) * atan (IZR 33 / 64 + ((B zh - IZR 33 / 64) + B zl)).
Proof.
  intros Fz Fl L U Hn Hl Hg.
  pose proof (series_segment_a zh zl 33%Z (IZR 542 * bpow radix2 (-75)) ltac:(lia) Fz Fl L U Hn Hl Hg segok_33) as SS.
  cbv zeta in SS. rewrite row_33 in SS. cbn [nth] in SS.
  destruct SS as [h [l [Hs [Fh [Fl' [Nrm [Ht [e1 [ea [E1 [Eea Eq]]]]]]]]]]].
  exists h, l. split; [exact Hs | split; [exact Fh | split; [exact Fl' | split; [exact Nrm | ]]]].
  destruct (word_ok_intro (0x3fde77eb7f175a34)%Z false 8576102634576436%positive 54%nat (2144025658644109)%Z 2%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c70e53dc1bf3435)%Z false 4755653033669685%positive 108%nat (4755653033669685)%Z 0%Z (-108)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fe9477169044ba4)%Z false 7115426836532132%positive 53%nat (1778856709133033)%Z 2%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc7d53e292d5fbc1)%Z true 8255006915820481%positive 108%nat (-8255006915820481)%Z 0%Z (-108)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd49802ba91fd89)%Z true 5796637021699465%positive 54%nat (-5796637021699465)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbfa1074cf33546d5)%Z true 4793101683345109%positive 57%nat (-4793101683345109)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fc2de9c9923fb61)%Z false 5311313746328417%positive 55%nat (5311313746328417)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfb48f5afa02c999)%Z true 5787120438528409%positive 56%nat (-5787120438528409)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbf97ab81ecaffca5)%Z true 6662498974432421%positive 58%nat (-6662498974432421)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3faf7772408c1fba)%Z false 8857056870932410%positive 57%nat (4428528435466205)%Z 1%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0xbf9a70a145433ece)%Z true 7442187348557518%positive 58%nat (-3721093674278759)%Z 1%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0xbf90444e3cfedf43)%Z true 4578702448844611%positive 58%nat (-4578702448844611)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc03f3bc2dd820c24)%Z true 8791432404012068%positive 48%nat (-2197858101003017)%Z 2%Z (-46)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  unfold seg_poly in Eq.
  pose proof (approx_33 _ _ _ _ _ _ _ _ _ _ _ _ _ ((B zh - IZR 33 / 64) + B zl) V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 Ht) as AP.
  pose proof (amin_33 ((B zh - IZR 33 / 64) + B zl) Ht) as HAm.
  destruct ea_dw_small as [Ea0 Ea1].
  rewrite Eq.
  refine (fast_compose _ _ e1 ea (IZR 9220836 * bpow radix2 (-93)) (IZR 542 * bpow radix2 (-75)) _ (IZR 985404 * bpow radix2 (-21)) _ AP E1 Eea HAm _ Ea0 _).
  - apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0].
  - bpow_num. replace (- prec)%Z with (-53)%Z by reflexivity. bpow_num. clear - Fz. interval with (i_prec 200).
Qed.

Lemma evalcert_34 : EvalCert (IZR (7024655016644917) * bpow radix2 (-53)) (IZR (-5844732494317841) * bpow radix2 (-108)) (IZR (-5820887020647121) * bpow radix2 (-54)) (IZR (-6987533149167423) * bpow radix2 (-58)) (IZR (5082495575409119) * bpow radix2 (-55)) (IZR (-2960519118719919) * bpow radix2 (-55)) (IZR (-4785714675494981) * bpow radix2 (-58)) (IZR (8296357785766811) * bpow radix2 (-57)) (IZR (-8018989994838369) * bpow radix2 (-58)) (IZR (-6536169415181149) * bpow radix2 (-59)) (IZR (-8613675049484091) * bpow radix2 (-48)) (IZR 544 * bpow radix2 (-75)) (IZR 879 * bpow radix2 (-75)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 17 (-17) (-70)); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_34.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_34.l1 th_ tl_ dg).
Qed.

Lemma segok_34 : SegOkRowA [(0x3fdf40dd0b541418)%Z; (0xbc6a3992dc382a23)%Z; (0x3fe8f4e2f2efd135)%Z; (0xbc74c3c0d4218911)%Z; (0xbfd4ae10df24b2d1)%Z; (0xbf98d31fd7365f3f)%Z; (0x3fc20e80b75841df)%Z; (0xbfb5092724d8175e)%Z; (0xbf910095073ab045)%Z; (0x3fad797e52c00b9b)%Z; (0xbf9c7d3a9a198961)%Z; (0xbf87389c882f035d)%Z; (0xc03e9a178188ff3b)%Z] (IZR 544 * bpow radix2 (-75)).
Proof.
  unfold SegOkRowA. cbn [nth].
  destruct (word_ok_intro (0x3fdf40dd0b541418)%Z false 8797042400039960%positive 54%nat (1099630300004995)%Z 3%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc6a3992dc382a23)%Z true 7381652317153827%positive 109%nat (-7381652317153827)%Z 0%Z (-109)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fe8f4e2f2efd135)%Z false 7024655016644917%positive 53%nat (7024655016644917)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc74c3c0d4218911)%Z true 5844732494317841%positive 108%nat (-5844732494317841)%Z 0%Z (-108)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd4ae10df24b2d1)%Z true 5820887020647121%positive 54%nat (-5820887020647121)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbf98d31fd7365f3f)%Z true 6987533149167423%positive 58%nat (-6987533149167423)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fc20e80b75841df)%Z false 5082495575409119%positive 55%nat (5082495575409119)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfb5092724d8175e)%Z true 5921038237439838%positive 56%nat (-2960519118719919)%Z 1%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbf910095073ab045)%Z true 4785714675494981%positive 58%nat (-4785714675494981)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3fad797e52c00b9b)%Z false 8296357785766811%positive 57%nat (8296357785766811)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0xbf9c7d3a9a198961)%Z true 8018989994838369%positive 58%nat (-8018989994838369)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0xbf87389c882f035d)%Z true 6536169415181149%positive 59%nat (-6536169415181149)%Z 0%Z (-59)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc03e9a178188ff3b)%Z true 8613675049484091%positive 48%nat (-8613675049484091)%Z 0%Z (-48)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_34 _ _).
  all: seg_numeric.
Qed.

Lemma row_34 : nth (Z.to_nat (34%Z - 1)) atan2_segments [] = [(0x3fdf40dd0b541418)%Z; (0xbc6a3992dc382a23)%Z; (0x3fe8f4e2f2efd135)%Z; (0xbc74c3c0d4218911)%Z; (0xbfd4ae10df24b2d1)%Z; (0xbf98d31fd7365f3f)%Z; (0x3fc20e80b75841df)%Z; (0xbfb5092724d8175e)%Z; (0xbf910095073ab045)%Z; (0x3fad797e52c00b9b)%Z; (0xbf9c7d3a9a198961)%Z; (0xbf87389c882f035d)%Z; (0xc03e9a178188ff3b)%Z].
Proof. reflexivity. Qed.

Lemma fast_34 zh zl : finite zh -> finite zl -> / 128 <= B zh -> B zh <= 1 ->
  Znearest ne (B zh * 64) = 34%Z -> Rabs (B zl) <= bpow radix2 (-53) -> on_grid (-211) (B zl) ->
  exists h l, atan2_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    Rabs (B h + B l - atan (IZR 34 / 64 + ((B zh - IZR 34 / 64) + B zl))) <= bpow radix2 (-63) * atan (IZR 34 / 64 + ((B zh - IZR 34 / 64) + B zl)).
Proof.
  intros Fz Fl L U Hn Hl Hg.
  pose proof (series_segment_a zh zl 34%Z (IZR 544 * bpow radix2 (-75)) ltac:(lia) Fz Fl L U Hn Hl Hg segok_34) as SS.
  cbv zeta in SS. rewrite row_34 in SS. cbn [nth] in SS.
  destruct SS as [h [l [Hs [Fh [Fl' [Nrm [Ht [e1 [ea [E1 [Eea Eq]]]]]]]]]]].
  exists h, l. split; [exact Hs | split; [exact Fh | split; [exact Fl' | split; [exact Nrm | ]]]].
  destruct (word_ok_intro (0x3fdf40dd0b541418)%Z false 8797042400039960%positive 54%nat (1099630300004995)%Z 3%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc6a3992dc382a23)%Z true 7381652317153827%positive 109%nat (-7381652317153827)%Z 0%Z (-109)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fe8f4e2f2efd135)%Z false 7024655016644917%positive 53%nat (7024655016644917)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc74c3c0d4218911)%Z true 5844732494317841%positive 108%nat (-5844732494317841)%Z 0%Z (-108)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd4ae10df24b2d1)%Z true 5820887020647121%positive 54%nat (-5820887020647121)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbf98d31fd7365f3f)%Z true 6987533149167423%positive 58%nat (-6987533149167423)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fc20e80b75841df)%Z false 5082495575409119%positive 55%nat (5082495575409119)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfb5092724d8175e)%Z true 5921038237439838%positive 56%nat (-2960519118719919)%Z 1%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbf910095073ab045)%Z true 4785714675494981%positive 58%nat (-4785714675494981)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3fad797e52c00b9b)%Z false 8296357785766811%positive 57%nat (8296357785766811)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0xbf9c7d3a9a198961)%Z true 8018989994838369%positive 58%nat (-8018989994838369)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0xbf87389c882f035d)%Z true 6536169415181149%positive 59%nat (-6536169415181149)%Z 0%Z (-59)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc03e9a178188ff3b)%Z true 8613675049484091%positive 48%nat (-8613675049484091)%Z 0%Z (-48)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  unfold seg_poly in Eq.
  pose proof (approx_34 _ _ _ _ _ _ _ _ _ _ _ _ _ ((B zh - IZR 34 / 64) + B zl) V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 Ht) as AP.
  pose proof (amin_34 ((B zh - IZR 34 / 64) + B zl) Ht) as HAm.
  destruct ea_dw_small as [Ea0 Ea1].
  rewrite Eq.
  refine (fast_compose _ _ e1 ea (IZR 9034108 * bpow radix2 (-93)) (IZR 544 * bpow radix2 (-75)) _ (IZR 1011290 * bpow radix2 (-21)) _ AP E1 Eea HAm _ Ea0 _).
  - apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0].
  - bpow_num. replace (- prec)%Z with (-53)%Z by reflexivity. bpow_num. clear - Fz. interval with (i_prec 200).
Qed.

Lemma evalcert_35 : EvalCert (IZR (6933562891828435) * bpow radix2 (-53)) (IZR (2021160667198035) * bpow radix2 (-107)) (IZR (-729711561628251) * bpow radix2 (-51)) (IZR (-4504438987504111) * bpow radix2 (-58)) (IZR (4849286379602573) * bpow radix2 (-55)) (IZR (-1503108318712293) * bpow radix2 (-54)) (IZR (-3034853543951981) * bpow radix2 (-58)) (IZR (7706877603771653) * bpow radix2 (-57)) (IZR (-5112489470836329) * bpow radix2 (-57)) (IZR (-4073639017193319) * bpow radix2 (-59)) (IZR (4428542440416261) * bpow radix2 (-48)) (IZR 545 * bpow radix2 (-75)) (IZR 590 * bpow radix2 (-75)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 545 (-545) (-75)); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_35.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_35.l1 th_ tl_ dg).
Qed.

Lemma segok_35 : SegOkRowA [(0x3fe0039c73c1a40c)%Z; (0xbc8b32c949c9d593)%Z; (0x3fe8a209e931fcd3)%Z; (0x3c6cb8f08e68c94c)%Z; (0xbfd4bd59b35ad2d8)%Z; (0xbf9000c36dc339ef)%Z; (0x3fc13a667812028d)%Z; (0xbfb55c46b5954794)%Z; (0xbf85905dcedd7cda)%Z; (0x3fab615d45e67505)%Z; (0xbfa229c836d3be69)%Z; (0xbf7cf1e7fd203ece)%Z; (0x402f7778c611480a)%Z] (IZR 545 * bpow radix2 (-75)).
Proof.
  unfold SegOkRowA. cbn [nth].
  destruct (word_ok_intro (0x3fe0039c73c1a40c)%Z false 4507570119222284%positive 53%nat (1126892529805571)%Z 2%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc8b32c949c9d593)%Z true 7655664478967187%positive 107%nat (-7655664478967187)%Z 0%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fe8a209e931fcd3)%Z false 6933562891828435%positive 53%nat (6933562891828435)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c6cb8f08e68c94c)%Z false 8084642668792140%positive 109%nat (2021160667198035)%Z 2%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd4bd59b35ad2d8)%Z true 5837692493026008%positive 54%nat (-729711561628251)%Z 3%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbf9000c36dc339ef)%Z true 4504438987504111%positive 58%nat (-4504438987504111)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fc13a667812028d)%Z false 4849286379602573%positive 55%nat (4849286379602573)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfb55c46b5954794)%Z true 6012433274849172%positive 56%nat (-1503108318712293)%Z 2%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbf85905dcedd7cda)%Z true 6069707087903962%positive 59%nat (-3034853543951981)%Z 1%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3fab615d45e67505)%Z false 7706877603771653%positive 57%nat (7706877603771653)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0xbfa229c836d3be69)%Z true 5112489470836329%positive 57%nat (-5112489470836329)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0xbf7cf1e7fd203ece)%Z true 8147278034386638%positive 60%nat (-4073639017193319)%Z 1%Z (-59)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x402f7778c611480a)%Z false 8857084880832522%positive 49%nat (4428542440416261)%Z 1%Z (-48)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_35 _ _).
  all: seg_numeric.
Qed.

Lemma row_35 : nth (Z.to_nat (35%Z - 1)) atan2_segments [] = [(0x3fe0039c73c1a40c)%Z; (0xbc8b32c949c9d593)%Z; (0x3fe8a209e931fcd3)%Z; (0x3c6cb8f08e68c94c)%Z; (0xbfd4bd59b35ad2d8)%Z; (0xbf9000c36dc339ef)%Z; (0x3fc13a667812028d)%Z; (0xbfb55c46b5954794)%Z; (0xbf85905dcedd7cda)%Z; (0x3fab615d45e67505)%Z; (0xbfa229c836d3be69)%Z; (0xbf7cf1e7fd203ece)%Z; (0x402f7778c611480a)%Z].
Proof. reflexivity. Qed.

Lemma fast_35 zh zl : finite zh -> finite zl -> / 128 <= B zh -> B zh <= 1 ->
  Znearest ne (B zh * 64) = 35%Z -> Rabs (B zl) <= bpow radix2 (-53) -> on_grid (-211) (B zl) ->
  exists h l, atan2_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    Rabs (B h + B l - atan (IZR 35 / 64 + ((B zh - IZR 35 / 64) + B zl))) <= bpow radix2 (-63) * atan (IZR 35 / 64 + ((B zh - IZR 35 / 64) + B zl)).
Proof.
  intros Fz Fl L U Hn Hl Hg.
  pose proof (series_segment_a zh zl 35%Z (IZR 545 * bpow radix2 (-75)) ltac:(lia) Fz Fl L U Hn Hl Hg segok_35) as SS.
  cbv zeta in SS. rewrite row_35 in SS. cbn [nth] in SS.
  destruct SS as [h [l [Hs [Fh [Fl' [Nrm [Ht [e1 [ea [E1 [Eea Eq]]]]]]]]]]].
  exists h, l. split; [exact Hs | split; [exact Fh | split; [exact Fl' | split; [exact Nrm | ]]]].
  destruct (word_ok_intro (0x3fe0039c73c1a40c)%Z false 4507570119222284%positive 53%nat (1126892529805571)%Z 2%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc8b32c949c9d593)%Z true 7655664478967187%positive 107%nat (-7655664478967187)%Z 0%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fe8a209e931fcd3)%Z false 6933562891828435%positive 53%nat (6933562891828435)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c6cb8f08e68c94c)%Z false 8084642668792140%positive 109%nat (2021160667198035)%Z 2%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd4bd59b35ad2d8)%Z true 5837692493026008%positive 54%nat (-729711561628251)%Z 3%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbf9000c36dc339ef)%Z true 4504438987504111%positive 58%nat (-4504438987504111)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fc13a667812028d)%Z false 4849286379602573%positive 55%nat (4849286379602573)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfb55c46b5954794)%Z true 6012433274849172%positive 56%nat (-1503108318712293)%Z 2%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbf85905dcedd7cda)%Z true 6069707087903962%positive 59%nat (-3034853543951981)%Z 1%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3fab615d45e67505)%Z false 7706877603771653%positive 57%nat (7706877603771653)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0xbfa229c836d3be69)%Z true 5112489470836329%positive 57%nat (-5112489470836329)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0xbf7cf1e7fd203ece)%Z true 8147278034386638%positive 60%nat (-4073639017193319)%Z 1%Z (-59)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x402f7778c611480a)%Z false 8857084880832522%positive 49%nat (4428542440416261)%Z 1%Z (-48)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  unfold seg_poly in Eq.
  pose proof (approx_35 _ _ _ _ _ _ _ _ _ _ _ _ _ ((B zh - IZR 35 / 64) + B zl) V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 Ht) as AP.
  pose proof (amin_35 ((B zh - IZR 35 / 64) + B zl) Ht) as HAm.
  destruct ea_dw_small as [Ea0 Ea1].
  rewrite Eq.
  refine (fast_compose _ _ e1 ea (IZR 9265605 * bpow radix2 (-94)) (IZR 545 * bpow radix2 (-75)) _ (IZR 1036845 * bpow radix2 (-21)) _ AP E1 Eea HAm _ Ea0 _).
  - apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0].
  - bpow_num. replace (- prec)%Z with (-53)%Z by reflexivity. bpow_num. clear - Fz. interval with (i_prec 200).
Qed.

Lemma evalcert_36 : EvalCert (IZR (1710566030573957) * bpow radix2 (-51)) (IZR (-4490235830256637) * bpow radix2 (-107)) (IZR (-5847394858223141) * bpow radix2 (-54)) (IZR (-8554843428142263) * bpow radix2 (-60)) (IZR (4613288655488437) * bpow radix2 (-55)) (IZR (-6064323191286957) * bpow radix2 (-56)) (IZR (-5661154166475689) * bpow radix2 (-60)) (IZR (1774842144659339) * bpow radix2 (-55)) (IZR (-8143642725898769) * bpow radix2 (-58)) (IZR (-7478171908968949) * bpow radix2 (-61)) (IZR (-5925552829856813) * bpow radix2 (-47)) (IZR 546 * bpow radix2 (-75)) (IZR 627 * bpow radix2 (-76)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 273 (-273) (-74)); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_36.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_36.l1 th_ tl_ dg).
Qed.

Lemma segok_36 : SegOkRowA [(0x3fe0657e94db30d0)%Z; (0xbc7d5b495f6349e6)%Z; (0x3fe84f00c2780614)%Z; (0xbc7fe7b0ff3d87fa)%Z; (0xbfd4c62cb562c625)%Z; (0xbf7e6495b3a4bcb7)%Z; (0x3fc063c2f78e85b5)%Z; (0xbfb58b78459eacad)%Z; (0xbf741cca2b1c8ba9)%Z; (0x3fa938d68e425e2c)%Z; (0xbf9cee9993dada11)%Z; (0xbf6a915b943411f5)%Z; (0xc0450d4247857c2d)%Z] (IZR 546 * bpow radix2 (-75)).
Proof.
  unfold SegOkRowA. cbn [nth].
  destruct (word_ok_intro (0x3fe0657e94db30d0)%Z false 4615193965048016%positive 53%nat (288449622815501)%Z 4%Z (-49)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc7d5b495f6349e6)%Z true 8263145015691750%positive 108%nat (-4131572507845875)%Z 1%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fe84f00c2780614)%Z false 6842264122295828%positive 53%nat (1710566030573957)%Z 2%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc7fe7b0ff3d87fa)%Z true 8980471660513274%positive 108%nat (-4490235830256637)%Z 1%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd4c62cb562c625)%Z true 5847394858223141%positive 54%nat (-5847394858223141)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbf7e6495b3a4bcb7)%Z true 8554843428142263%positive 60%nat (-8554843428142263)%Z 0%Z (-60)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fc063c2f78e85b5)%Z false 4613288655488437%positive 55%nat (4613288655488437)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfb58b78459eacad)%Z true 6064323191286957%positive 56%nat (-6064323191286957)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbf741cca2b1c8ba9)%Z true 5661154166475689%positive 60%nat (-5661154166475689)%Z 0%Z (-60)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3fa938d68e425e2c)%Z false 7099368578637356%positive 57%nat (1774842144659339)%Z 2%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0xbf9cee9993dada11)%Z true 8143642725898769%positive 58%nat (-8143642725898769)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0xbf6a915b943411f5)%Z true 7478171908968949%positive 61%nat (-7478171908968949)%Z 0%Z (-61)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc0450d4247857c2d)%Z true 5925552829856813%positive 47%nat (-5925552829856813)%Z 0%Z (-47)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_36 _ _).
  all: seg_numeric.
Qed.

Lemma row_36 : nth (Z.to_nat (36%Z - 1)) atan2_segments [] = [(0x3fe0657e94db30d0)%Z; (0xbc7d5b495f6349e6)%Z; (0x3fe84f00c2780614)%Z; (0xbc7fe7b0ff3d87fa)%Z; (0xbfd4c62cb562c625)%Z; (0xbf7e6495b3a4bcb7)%Z; (0x3fc063c2f78e85b5)%Z; (0xbfb58b78459eacad)%Z; (0xbf741cca2b1c8ba9)%Z; (0x3fa938d68e425e2c)%Z; (0xbf9cee9993dada11)%Z; (0xbf6a915b943411f5)%Z; (0xc0450d4247857c2d)%Z].
Proof. reflexivity. Qed.

Lemma fast_36 zh zl : finite zh -> finite zl -> / 128 <= B zh -> B zh <= 1 ->
  Znearest ne (B zh * 64) = 36%Z -> Rabs (B zl) <= bpow radix2 (-53) -> on_grid (-211) (B zl) ->
  exists h l, atan2_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    Rabs (B h + B l - atan (IZR 36 / 64 + ((B zh - IZR 36 / 64) + B zl))) <= bpow radix2 (-63) * atan (IZR 36 / 64 + ((B zh - IZR 36 / 64) + B zl)).
Proof.
  intros Fz Fl L U Hn Hl Hg.
  pose proof (series_segment_a zh zl 36%Z (IZR 546 * bpow radix2 (-75)) ltac:(lia) Fz Fl L U Hn Hl Hg segok_36) as SS.
  cbv zeta in SS. rewrite row_36 in SS. cbn [nth] in SS.
  destruct SS as [h [l [Hs [Fh [Fl' [Nrm [Ht [e1 [ea [E1 [Eea Eq]]]]]]]]]]].
  exists h, l. split; [exact Hs | split; [exact Fh | split; [exact Fl' | split; [exact Nrm | ]]]].
  destruct (word_ok_intro (0x3fe0657e94db30d0)%Z false 4615193965048016%positive 53%nat (288449622815501)%Z 4%Z (-49)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc7d5b495f6349e6)%Z true 8263145015691750%positive 108%nat (-4131572507845875)%Z 1%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fe84f00c2780614)%Z false 6842264122295828%positive 53%nat (1710566030573957)%Z 2%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc7fe7b0ff3d87fa)%Z true 8980471660513274%positive 108%nat (-4490235830256637)%Z 1%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd4c62cb562c625)%Z true 5847394858223141%positive 54%nat (-5847394858223141)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0xbf7e6495b3a4bcb7)%Z true 8554843428142263%positive 60%nat (-8554843428142263)%Z 0%Z (-60)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fc063c2f78e85b5)%Z false 4613288655488437%positive 55%nat (4613288655488437)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfb58b78459eacad)%Z true 6064323191286957%positive 56%nat (-6064323191286957)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0xbf741cca2b1c8ba9)%Z true 5661154166475689%positive 60%nat (-5661154166475689)%Z 0%Z (-60)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3fa938d68e425e2c)%Z false 7099368578637356%positive 57%nat (1774842144659339)%Z 2%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0xbf9cee9993dada11)%Z true 8143642725898769%positive 58%nat (-8143642725898769)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0xbf6a915b943411f5)%Z true 7478171908968949%positive 61%nat (-7478171908968949)%Z 0%Z (-61)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc0450d4247857c2d)%Z true 5925552829856813%positive 47%nat (-5925552829856813)%Z 0%Z (-47)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  unfold seg_poly in Eq.
  pose proof (approx_36 _ _ _ _ _ _ _ _ _ _ _ _ _ ((B zh - IZR 36 / 64) + B zl) V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 Ht) as AP.
  pose proof (amin_36 ((B zh - IZR 36 / 64) + B zl) Ht) as HAm.
  destruct ea_dw_small as [Ea0 Ea1].
  rewrite Eq.
  refine (fast_compose _ _ e1 ea (IZR 12425053 * bpow radix2 (-93)) (IZR 546 * bpow radix2 (-75)) _ (IZR 531034 * bpow radix2 (-20)) _ AP E1 Eea HAm _ Ea0 _).
  - apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0].
  - bpow_num. replace (- prec)%Z with (-53)%Z by reflexivity. bpow_num. clear - Fz. interval with (i_prec 200).
Qed.

Lemma evalcert_37 : EvalCert (IZR (1687716749653207) * bpow radix2 (-51)) (IZR (-5893823336679559) * bpow radix2 (-107)) (IZR (-5850339635028427) * bpow radix2 (-54)) (IZR (6952492835708733) * bpow radix2 (-64)) (IZR (8751970073840769) * bpow radix2 (-56)) (IZR (-6079818507953281) * bpow radix2 (-56)) (IZR (4507130101438497) * bpow radix2 (-64)) (IZR (6483541365042885) * bpow radix2 (-57)) (IZR (-4237171188045039) * bpow radix2 (-57)) (IZR (1437481205722437) * bpow radix2 (-63)) (IZR (-4967534171440961) * bpow radix2 (-47)) (IZR 546 * bpow radix2 (-75)) (IZR 609 * bpow radix2 (-78)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 273 (-273) (-74)); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_37.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_37.l1 th_ tl_ dg).
Qed.

Lemma segok_37 : SegOkRowA [(0x3fe0c6145b5b43da)%Z; (0x3c5974fa13b5404f)%Z; (0x3fe7fbe0b560d35c)%Z; (0xbc84f066ae5a0887)%Z; (0xbfd4c8da57c2e1cb)%Z; (0x3f38b34161c69f3d)%Z; (0x3fbf17ded3560c81)%Z; (0xbfb599900e772481)%Z; (0x3f30033600a71821)%Z; (0x3fa708bf1bf32ec5)%Z; (0xbf9e1b5e970829de)%Z; (0x3f246d86b28db514)%Z; (0xc041a5f22db2c741)%Z] (IZR 546 * bpow radix2 (-75)).
Proof.
  unfold SegOkRowA. cbn [nth].
  destruct (word_ok_intro (0x3fe0c6145b5b43da)%Z false 4721390361723866%positive 53%nat (2360695180861933)%Z 1%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c5974fa13b5404f)%Z false 7165491839057999%positive 110%nat (7165491839057999)%Z 0%Z (-110)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fe7fbe0b560d35c)%Z false 6750866998612828%positive 53%nat (1687716749653207)%Z 2%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc84f066ae5a0887)%Z true 5893823336679559%positive 107%nat (-5893823336679559)%Z 0%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd4c8da57c2e1cb)%Z true 5850339635028427%positive 54%nat (-5850339635028427)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3f38b34161c69f3d)%Z false 6952492835708733%positive 64%nat (6952492835708733)%Z 0%Z (-64)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fbf17ded3560c81)%Z false 8751970073840769%positive 56%nat (8751970073840769)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfb599900e772481)%Z true 6079818507953281%positive 56%nat (-6079818507953281)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3f30033600a71821)%Z false 4507130101438497%positive 64%nat (4507130101438497)%Z 0%Z (-64)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3fa708bf1bf32ec5)%Z false 6483541365042885%positive 57%nat (6483541365042885)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0xbf9e1b5e970829de)%Z true 8474342376090078%positive 58%nat (-4237171188045039)%Z 1%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3f246d86b28db514)%Z false 5749924822889748%positive 65%nat (1437481205722437)%Z 2%Z (-63)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc041a5f22db2c741)%Z true 4967534171440961%positive 47%nat (-4967534171440961)%Z 0%Z (-47)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_37 _ _).
  all: seg_numeric.
Qed.

Lemma row_37 : nth (Z.to_nat (37%Z - 1)) atan2_segments [] = [(0x3fe0c6145b5b43da)%Z; (0x3c5974fa13b5404f)%Z; (0x3fe7fbe0b560d35c)%Z; (0xbc84f066ae5a0887)%Z; (0xbfd4c8da57c2e1cb)%Z; (0x3f38b34161c69f3d)%Z; (0x3fbf17ded3560c81)%Z; (0xbfb599900e772481)%Z; (0x3f30033600a71821)%Z; (0x3fa708bf1bf32ec5)%Z; (0xbf9e1b5e970829de)%Z; (0x3f246d86b28db514)%Z; (0xc041a5f22db2c741)%Z].
Proof. reflexivity. Qed.

Lemma fast_37 zh zl : finite zh -> finite zl -> / 128 <= B zh -> B zh <= 1 ->
  Znearest ne (B zh * 64) = 37%Z -> Rabs (B zl) <= bpow radix2 (-53) -> on_grid (-211) (B zl) ->
  exists h l, atan2_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    Rabs (B h + B l - atan (IZR 37 / 64 + ((B zh - IZR 37 / 64) + B zl))) <= bpow radix2 (-63) * atan (IZR 37 / 64 + ((B zh - IZR 37 / 64) + B zl)).
Proof.
  intros Fz Fl L U Hn Hl Hg.
  pose proof (series_segment_a zh zl 37%Z (IZR 546 * bpow radix2 (-75)) ltac:(lia) Fz Fl L U Hn Hl Hg segok_37) as SS.
  cbv zeta in SS. rewrite row_37 in SS. cbn [nth] in SS.
  destruct SS as [h [l [Hs [Fh [Fl' [Nrm [Ht [e1 [ea [E1 [Eea Eq]]]]]]]]]]].
  exists h, l. split; [exact Hs | split; [exact Fh | split; [exact Fl' | split; [exact Nrm | ]]]].
  destruct (word_ok_intro (0x3fe0c6145b5b43da)%Z false 4721390361723866%positive 53%nat (2360695180861933)%Z 1%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c5974fa13b5404f)%Z false 7165491839057999%positive 110%nat (7165491839057999)%Z 0%Z (-110)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fe7fbe0b560d35c)%Z false 6750866998612828%positive 53%nat (1687716749653207)%Z 2%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc84f066ae5a0887)%Z true 5893823336679559%positive 107%nat (-5893823336679559)%Z 0%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd4c8da57c2e1cb)%Z true 5850339635028427%positive 54%nat (-5850339635028427)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3f38b34161c69f3d)%Z false 6952492835708733%positive 64%nat (6952492835708733)%Z 0%Z (-64)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fbf17ded3560c81)%Z false 8751970073840769%positive 56%nat (8751970073840769)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfb599900e772481)%Z true 6079818507953281%positive 56%nat (-6079818507953281)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3f30033600a71821)%Z false 4507130101438497%positive 64%nat (4507130101438497)%Z 0%Z (-64)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3fa708bf1bf32ec5)%Z false 6483541365042885%positive 57%nat (6483541365042885)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0xbf9e1b5e970829de)%Z true 8474342376090078%positive 58%nat (-4237171188045039)%Z 1%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3f246d86b28db514)%Z false 5749924822889748%positive 65%nat (1437481205722437)%Z 2%Z (-63)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc041a5f22db2c741)%Z true 4967534171440961%positive 47%nat (-4967534171440961)%Z 0%Z (-47)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  unfold seg_poly in Eq.
  pose proof (approx_37 _ _ _ _ _ _ _ _ _ _ _ _ _ ((B zh - IZR 37 / 64) + B zl) V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 Ht) as AP.
  pose proof (amin_37 ((B zh - IZR 37 / 64) + B zl) Ht) as HAm.
  destruct ea_dw_small as [Ea0 Ea1].
  rewrite Eq.
  refine (fast_compose _ _ e1 ea (IZR 10416515 * bpow radix2 (-93)) (IZR 546 * bpow radix2 (-75)) _ (IZR 543480 * bpow radix2 (-20)) _ AP E1 Eea HAm _ Ea0 _).
  - apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0].
  - bpow_num. replace (- prec)%Z with (-53)%Z by reflexivity. bpow_num. clear - Fz. interval with (i_prec 200).
Qed.

Lemma evalcert_38 : EvalCert (IZR (6659474394840993) * bpow radix2 (-53)) (IZR (6542413321494179) * bpow radix2 (-107)) (IZR (-730859283765943) * bpow radix2 (-51)) (IZR (559320976477335) * bpow radix2 (-56)) (IZR (8277471317776061) * bpow radix2 (-56)) (IZR (-3031036428003845) * bpow radix2 (-55)) (IZR (5685145852983205) * bpow radix2 (-60)) (IZR (2934012244146397) * bpow radix2 (-56)) (IZR (-509042573933859) * bpow radix2 (-54)) (IZR (3598239205639151) * bpow radix2 (-60)) (IZR (-5897746217380899) * bpow radix2 (-47)) (IZR 546 * bpow radix2 (-75)) (IZR 636 * bpow radix2 (-76)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 273 (-273) (-74)); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_38.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_38.l1 th_ tl_ dg).
Qed.

Lemma segok_38 : SegOkRowA [(0x3fe1255d9bfbd2a9)%Z; (0xbc52bdaee1c0ee35)%Z; (0x3fe7a8c1b5b1ffa1)%Z; (0x3c873e4a4e005ea3)%Z; (0xbfd4c5b37fead5b8)%Z; (0x3f7fcb3101e4c970)%Z; (0x3fbd6850f988d6bd)%Z; (0xbfb5896c532f540a)%Z; (0x3f74329c2b1037a5)%Z; (0x3fa4d8efeb2871ba)%Z; (0xbf9cef8b5cb7d230)%Z; (0x3f699128b35687de)%Z; (0xc044f3f80c432c23)%Z] (IZR 546 * bpow radix2 (-75)).
Proof.
  unfold SegOkRowA. cbn [nth].
  destruct (word_ok_intro (0x3fe1255d9bfbd2a9)%Z false 4826158583239337%positive 53%nat (4826158583239337)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc52bdaee1c0ee35)%Z true 5275108390268469%positive 110%nat (-5275108390268469)%Z 0%Z (-110)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fe7a8c1b5b1ffa1)%Z false 6659474394840993%positive 53%nat (6659474394840993)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c873e4a4e005ea3)%Z false 6542413321494179%positive 107%nat (6542413321494179)%Z 0%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd4c5b37fead5b8)%Z true 5846874270127544%positive 54%nat (-730859283765943)%Z 3%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3f7fcb3101e4c970)%Z false 8949135623637360%positive 60%nat (559320976477335)%Z 4%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fbd6850f988d6bd)%Z false 8277471317776061%positive 56%nat (8277471317776061)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfb5896c532f540a)%Z true 6062072856007690%positive 56%nat (-3031036428003845)%Z 1%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3f74329c2b1037a5)%Z false 5685145852983205%positive 60%nat (5685145852983205)%Z 0%Z (-60)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3fa4d8efeb2871ba)%Z false 5868024488292794%positive 57%nat (2934012244146397)%Z 1%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0xbf9cef8b5cb7d230)%Z true 8144681182941744%positive 58%nat (-509042573933859)%Z 4%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3f699128b35687de)%Z false 7196478411278302%positive 61%nat (3598239205639151)%Z 1%Z (-60)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc044f3f80c432c23)%Z true 5897746217380899%positive 47%nat (-5897746217380899)%Z 0%Z (-47)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_38 _ _).
  all: seg_numeric.
Qed.

Lemma row_38 : nth (Z.to_nat (38%Z - 1)) atan2_segments [] = [(0x3fe1255d9bfbd2a9)%Z; (0xbc52bdaee1c0ee35)%Z; (0x3fe7a8c1b5b1ffa1)%Z; (0x3c873e4a4e005ea3)%Z; (0xbfd4c5b37fead5b8)%Z; (0x3f7fcb3101e4c970)%Z; (0x3fbd6850f988d6bd)%Z; (0xbfb5896c532f540a)%Z; (0x3f74329c2b1037a5)%Z; (0x3fa4d8efeb2871ba)%Z; (0xbf9cef8b5cb7d230)%Z; (0x3f699128b35687de)%Z; (0xc044f3f80c432c23)%Z].
Proof. reflexivity. Qed.

Lemma fast_38 zh zl : finite zh -> finite zl -> / 128 <= B zh -> B zh <= 1 ->
  Znearest ne (B zh * 64) = 38%Z -> Rabs (B zl) <= bpow radix2 (-53) -> on_grid (-211) (B zl) ->
  exists h l, atan2_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    Rabs (B h + B l - atan (IZR 38 / 64 + ((B zh - IZR 38 / 64) + B zl))) <= bpow radix2 (-63) * atan (IZR 38 / 64 + ((B zh - IZR 38 / 64) + B zl)).
Proof.
  intros Fz Fl L U Hn Hl Hg.
  pose proof (series_segment_a zh zl 38%Z (IZR 546 * bpow radix2 (-75)) ltac:(lia) Fz Fl L U Hn Hl Hg segok_38) as SS.
  cbv zeta in SS. rewrite row_38 in SS. cbn [nth] in SS.
  destruct SS as [h [l [Hs [Fh [Fl' [Nrm [Ht [e1 [ea [E1 [Eea Eq]]]]]]]]]]].
  exists h, l. split; [exact Hs | split; [exact Fh | split; [exact Fl' | split; [exact Nrm | ]]]].
  destruct (word_ok_intro (0x3fe1255d9bfbd2a9)%Z false 4826158583239337%positive 53%nat (4826158583239337)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc52bdaee1c0ee35)%Z true 5275108390268469%positive 110%nat (-5275108390268469)%Z 0%Z (-110)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fe7a8c1b5b1ffa1)%Z false 6659474394840993%positive 53%nat (6659474394840993)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c873e4a4e005ea3)%Z false 6542413321494179%positive 107%nat (6542413321494179)%Z 0%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd4c5b37fead5b8)%Z true 5846874270127544%positive 54%nat (-730859283765943)%Z 3%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3f7fcb3101e4c970)%Z false 8949135623637360%positive 60%nat (559320976477335)%Z 4%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fbd6850f988d6bd)%Z false 8277471317776061%positive 56%nat (8277471317776061)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfb5896c532f540a)%Z true 6062072856007690%positive 56%nat (-3031036428003845)%Z 1%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3f74329c2b1037a5)%Z false 5685145852983205%positive 60%nat (5685145852983205)%Z 0%Z (-60)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3fa4d8efeb2871ba)%Z false 5868024488292794%positive 57%nat (2934012244146397)%Z 1%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0xbf9cef8b5cb7d230)%Z true 8144681182941744%positive 58%nat (-509042573933859)%Z 4%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3f699128b35687de)%Z false 7196478411278302%positive 61%nat (3598239205639151)%Z 1%Z (-60)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc044f3f80c432c23)%Z true 5897746217380899%positive 47%nat (-5897746217380899)%Z 0%Z (-47)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  unfold seg_poly in Eq.
  pose proof (approx_38 _ _ _ _ _ _ _ _ _ _ _ _ _ ((B zh - IZR 38 / 64) + B zl) V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 Ht) as AP.
  pose proof (amin_38 ((B zh - IZR 38 / 64) + B zl) Ht) as HAm.
  destruct ea_dw_small as [Ea0 Ea1].
  rewrite Eq.
  refine (fast_compose _ _ e1 ea (IZR 12365232 * bpow radix2 (-93)) (IZR 546 * bpow radix2 (-75)) _ (IZR 555760 * bpow radix2 (-20)) _ AP E1 Eea HAm _ Ea0 _).
  - apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0].
  - bpow_num. replace (- prec)%Z with (-53)%Z by reflexivity. bpow_num. clear - Fz. interval with (i_prec 200).
Qed.

Lemma evalcert_39 : EvalCert (IZR (3284091877106917) * bpow radix2 (-52)) (IZR (-3761952902193763) * bpow radix2 (-106)) (IZR (-5837346145813683) * bpow radix2 (-54)) (IZR (8495168439207807) * bpow radix2 (-59)) (IZR (487847169275227) * bpow radix2 (-52)) (IZR (-1503559686127293) * bpow radix2 (-54)) (IZR (5276633738839465) * bpow radix2 (-59)) (IZR (5260349862807499) * bpow radix2 (-57)) (IZR (-4744789663640323) * bpow radix2 (-57)) (IZR (6537209214242657) * bpow radix2 (-60)) (IZR (-953343060868799) * bpow radix2 (-48)) (IZR 545 * bpow radix2 (-75)) (IZR 546 * bpow radix2 (-75)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 545 (-545) (-75)); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_39.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_39.l1 th_ tl_ dg).
Qed.

Lemma segok_39 : SegOkRowA [(0x3fe1835a88be7c13)%Z; (0x3c8c621cec00c301)%Z; (0x3fe755ba737d49ca)%Z; (0xbc8abaf3d4cb44c6)%Z; (0xbfd4bd090f73c4b3)%Z; (0x3f8e2e4f8920477f)%Z; (0x3fbbbb1c53ab55b0)%Z; (0xbfb55deb13f5faf4)%Z; (0x3f82bf12079d05a9)%Z; (0x3fa2b042a4f787cb)%Z; (0xbfa0db5c6e6f6b03)%Z; (0x3f77398ea1098f61)%Z; (0xc00b187bd3eff5f8)%Z] (IZR 545 * bpow radix2 (-75)).
Proof.
  unfold SegOkRowA. cbn [nth].
  destruct (word_ok_intro (0x3fe1835a88be7c13)%Z false 4929499468561427%positive 53%nat (4929499468561427)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c8c621cec00c301)%Z false 7989175705977601%positive 107%nat (7989175705977601)%Z 0%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fe755ba737d49ca)%Z false 6568183754213834%positive 53%nat (3284091877106917)%Z 1%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc8abaf3d4cb44c6)%Z true 7523905804387526%positive 107%nat (-3761952902193763)%Z 1%Z (-106)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd4bd090f73c4b3)%Z true 5837346145813683%positive 54%nat (-5837346145813683)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3f8e2e4f8920477f)%Z false 8495168439207807%positive 59%nat (8495168439207807)%Z 0%Z (-59)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fbbbb1c53ab55b0)%Z false 7805554708403632%positive 56%nat (487847169275227)%Z 4%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfb55deb13f5faf4)%Z true 6014238744509172%positive 56%nat (-1503559686127293)%Z 2%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3f82bf12079d05a9)%Z false 5276633738839465%positive 59%nat (5276633738839465)%Z 0%Z (-59)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3fa2b042a4f787cb)%Z false 5260349862807499%positive 57%nat (5260349862807499)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0xbfa0db5c6e6f6b03)%Z true 4744789663640323%positive 57%nat (-4744789663640323)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3f77398ea1098f61)%Z false 6537209214242657%positive 60%nat (6537209214242657)%Z 0%Z (-60)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc00b187bd3eff5f8)%Z true 7626744486950392%positive 51%nat (-953343060868799)%Z 3%Z (-48)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_39 _ _).
  all: seg_numeric.
Qed.

Lemma row_39 : nth (Z.to_nat (39%Z - 1)) atan2_segments [] = [(0x3fe1835a88be7c13)%Z; (0x3c8c621cec00c301)%Z; (0x3fe755ba737d49ca)%Z; (0xbc8abaf3d4cb44c6)%Z; (0xbfd4bd090f73c4b3)%Z; (0x3f8e2e4f8920477f)%Z; (0x3fbbbb1c53ab55b0)%Z; (0xbfb55deb13f5faf4)%Z; (0x3f82bf12079d05a9)%Z; (0x3fa2b042a4f787cb)%Z; (0xbfa0db5c6e6f6b03)%Z; (0x3f77398ea1098f61)%Z; (0xc00b187bd3eff5f8)%Z].
Proof. reflexivity. Qed.

Lemma fast_39 zh zl : finite zh -> finite zl -> / 128 <= B zh -> B zh <= 1 ->
  Znearest ne (B zh * 64) = 39%Z -> Rabs (B zl) <= bpow radix2 (-53) -> on_grid (-211) (B zl) ->
  exists h l, atan2_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    Rabs (B h + B l - atan (IZR 39 / 64 + ((B zh - IZR 39 / 64) + B zl))) <= bpow radix2 (-63) * atan (IZR 39 / 64 + ((B zh - IZR 39 / 64) + B zl)).
Proof.
  intros Fz Fl L U Hn Hl Hg.
  pose proof (series_segment_a zh zl 39%Z (IZR 545 * bpow radix2 (-75)) ltac:(lia) Fz Fl L U Hn Hl Hg segok_39) as SS.
  cbv zeta in SS. rewrite row_39 in SS. cbn [nth] in SS.
  destruct SS as [h [l [Hs [Fh [Fl' [Nrm [Ht [e1 [ea [E1 [Eea Eq]]]]]]]]]]].
  exists h, l. split; [exact Hs | split; [exact Fh | split; [exact Fl' | split; [exact Nrm | ]]]].
  destruct (word_ok_intro (0x3fe1835a88be7c13)%Z false 4929499468561427%positive 53%nat (4929499468561427)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c8c621cec00c301)%Z false 7989175705977601%positive 107%nat (7989175705977601)%Z 0%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fe755ba737d49ca)%Z false 6568183754213834%positive 53%nat (3284091877106917)%Z 1%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc8abaf3d4cb44c6)%Z true 7523905804387526%positive 107%nat (-3761952902193763)%Z 1%Z (-106)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd4bd090f73c4b3)%Z true 5837346145813683%positive 54%nat (-5837346145813683)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3f8e2e4f8920477f)%Z false 8495168439207807%positive 59%nat (8495168439207807)%Z 0%Z (-59)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fbbbb1c53ab55b0)%Z false 7805554708403632%positive 56%nat (487847169275227)%Z 4%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfb55deb13f5faf4)%Z true 6014238744509172%positive 56%nat (-1503559686127293)%Z 2%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3f82bf12079d05a9)%Z false 5276633738839465%positive 59%nat (5276633738839465)%Z 0%Z (-59)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3fa2b042a4f787cb)%Z false 5260349862807499%positive 57%nat (5260349862807499)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0xbfa0db5c6e6f6b03)%Z true 4744789663640323%positive 57%nat (-4744789663640323)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3f77398ea1098f61)%Z false 6537209214242657%positive 60%nat (6537209214242657)%Z 0%Z (-60)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc00b187bd3eff5f8)%Z true 7626744486950392%positive 51%nat (-953343060868799)%Z 3%Z (-48)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  unfold seg_poly in Eq.
  pose proof (approx_39 _ _ _ _ _ _ _ _ _ _ _ _ _ ((B zh - IZR 39 / 64) + B zl) V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 Ht) as AP.
  pose proof (amin_39 ((B zh - IZR 39 / 64) + B zl) Ht) as HAm.
  destruct ea_dw_small as [Ea0 Ea1].
  rewrite Eq.
  refine (fast_compose _ _ e1 ea (IZR 16054169 * bpow radix2 (-97)) (IZR 545 * bpow radix2 (-75)) _ (IZR 567873 * bpow radix2 (-20)) _ AP E1 Eea HAm _ Ea0 _).
  - apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0].
  - bpow_num. replace (- prec)%Z with (-53)%Z by reflexivity. bpow_num. clear - Fz. interval with (i_prec 200).
Qed.

Lemma evalcert_40 : EvalCert (IZR (404817944033303) * bpow radix2 (-49)) (IZR (404817944033303) * bpow radix2 (-104)) (IZR (-2911050384059707) * bpow radix2 (-53)) (IZR (383778927037085) * bpow radix2 (-54)) (IZR (1834612235458035) * bpow radix2 (-54)) (IZR (-2969714468968177) * bpow radix2 (-55)) (IZR (7447658995577753) * bpow radix2 (-59)) (IZR (4666967038120577) * bpow radix2 (-57)) (IZR (-1221720184244365) * bpow radix2 (-55)) (IZR (2239608164166231) * bpow radix2 (-58)) (IZR (3019358535788795) * bpow radix2 (-48)) (IZR 544 * bpow radix2 (-75)) (IZR 761 * bpow radix2 (-75)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 17 (-17) (-70)); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_40.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_40.l1 th_ tl_ dg).
Qed.

Lemma segok_40 : SegOkRowA [(0x3fe1e00babdefeb4)%Z; (0xbc5928df287a668f)%Z; (0x3fe702e05c0b8170)%Z; (0x3c7702e05c0b8170)%Z; (0xbfd4af2b78215a76)%Z; (0x3f95d0b7e9e4a9d0)%Z; (0x3fba1247ca6157cc)%Z; (0xbfb519e11003ade2)%Z; (0x3f8a759b3cd6f399)%Z; (0x3fa09494f07c5281)%Z; (0xbfa15c9796632234)%Z; (0x3f7fd3a5a43ea95c)%Z; (0x4025742e61f351f6)%Z] (IZR 544 * bpow radix2 (-75)).
Proof.
  unfold SegOkRowA. cbn [nth].
  destruct (word_ok_intro (0x3fe1e00babdefeb4)%Z false 5031415336861364%positive 53%nat (1257853834215341)%Z 2%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc5928df287a668f)%Z true 7081813339694735%positive 110%nat (-7081813339694735)%Z 0%Z (-110)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fe702e05c0b8170)%Z false 6477087104532848%positive 53%nat (404817944033303)%Z 4%Z (-49)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c7702e05c0b8170)%Z false 6477087104532848%positive 108%nat (404817944033303)%Z 4%Z (-104)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd4af2b78215a76)%Z true 5822100768119414%positive 54%nat (-2911050384059707)%Z 1%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3f95d0b7e9e4a9d0)%Z false 6140462832593360%positive 58%nat (383778927037085)%Z 4%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fba1247ca6157cc)%Z false 7338448941832140%positive 56%nat (1834612235458035)%Z 2%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfb519e11003ade2)%Z true 5939428937936354%positive 56%nat (-2969714468968177)%Z 1%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3f8a759b3cd6f399)%Z false 7447658995577753%positive 59%nat (7447658995577753)%Z 0%Z (-59)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3fa09494f07c5281)%Z false 4666967038120577%positive 57%nat (4666967038120577)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0xbfa15c9796632234)%Z true 4886880736977460%positive 57%nat (-1221720184244365)%Z 2%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3f7fd3a5a43ea95c)%Z false 8958432656664924%positive 60%nat (2239608164166231)%Z 2%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x4025742e61f351f6)%Z false 6038717071577590%positive 49%nat (3019358535788795)%Z 1%Z (-48)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_40 _ _).
  all: seg_numeric.
Qed.

Lemma row_40 : nth (Z.to_nat (40%Z - 1)) atan2_segments [] = [(0x3fe1e00babdefeb4)%Z; (0xbc5928df287a668f)%Z; (0x3fe702e05c0b8170)%Z; (0x3c7702e05c0b8170)%Z; (0xbfd4af2b78215a76)%Z; (0x3f95d0b7e9e4a9d0)%Z; (0x3fba1247ca6157cc)%Z; (0xbfb519e11003ade2)%Z; (0x3f8a759b3cd6f399)%Z; (0x3fa09494f07c5281)%Z; (0xbfa15c9796632234)%Z; (0x3f7fd3a5a43ea95c)%Z; (0x4025742e61f351f6)%Z].
Proof. reflexivity. Qed.

Lemma fast_40 zh zl : finite zh -> finite zl -> / 128 <= B zh -> B zh <= 1 ->
  Znearest ne (B zh * 64) = 40%Z -> Rabs (B zl) <= bpow radix2 (-53) -> on_grid (-211) (B zl) ->
  exists h l, atan2_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    Rabs (B h + B l - atan (IZR 40 / 64 + ((B zh - IZR 40 / 64) + B zl))) <= bpow radix2 (-63) * atan (IZR 40 / 64 + ((B zh - IZR 40 / 64) + B zl)).
Proof.
  intros Fz Fl L U Hn Hl Hg.
  pose proof (series_segment_a zh zl 40%Z (IZR 544 * bpow radix2 (-75)) ltac:(lia) Fz Fl L U Hn Hl Hg segok_40) as SS.
  cbv zeta in SS. rewrite row_40 in SS. cbn [nth] in SS.
  destruct SS as [h [l [Hs [Fh [Fl' [Nrm [Ht [e1 [ea [E1 [Eea Eq]]]]]]]]]]].
  exists h, l. split; [exact Hs | split; [exact Fh | split; [exact Fl' | split; [exact Nrm | ]]]].
  destruct (word_ok_intro (0x3fe1e00babdefeb4)%Z false 5031415336861364%positive 53%nat (1257853834215341)%Z 2%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc5928df287a668f)%Z true 7081813339694735%positive 110%nat (-7081813339694735)%Z 0%Z (-110)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fe702e05c0b8170)%Z false 6477087104532848%positive 53%nat (404817944033303)%Z 4%Z (-49)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c7702e05c0b8170)%Z false 6477087104532848%positive 108%nat (404817944033303)%Z 4%Z (-104)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd4af2b78215a76)%Z true 5822100768119414%positive 54%nat (-2911050384059707)%Z 1%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3f95d0b7e9e4a9d0)%Z false 6140462832593360%positive 58%nat (383778927037085)%Z 4%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fba1247ca6157cc)%Z false 7338448941832140%positive 56%nat (1834612235458035)%Z 2%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfb519e11003ade2)%Z true 5939428937936354%positive 56%nat (-2969714468968177)%Z 1%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3f8a759b3cd6f399)%Z false 7447658995577753%positive 59%nat (7447658995577753)%Z 0%Z (-59)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3fa09494f07c5281)%Z false 4666967038120577%positive 57%nat (4666967038120577)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0xbfa15c9796632234)%Z true 4886880736977460%positive 57%nat (-1221720184244365)%Z 2%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3f7fd3a5a43ea95c)%Z false 8958432656664924%positive 60%nat (2239608164166231)%Z 2%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x4025742e61f351f6)%Z false 6038717071577590%positive 49%nat (3019358535788795)%Z 1%Z (-48)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  unfold seg_poly in Eq.
  pose proof (approx_40 _ _ _ _ _ _ _ _ _ _ _ _ _ ((B zh - IZR 40 / 64) + B zl) V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 Ht) as AP.
  pose proof (amin_40 ((B zh - IZR 40 / 64) + B zl) Ht) as HAm.
  destruct ea_dw_small as [Ea0 Ea1].
  rewrite Eq.
  refine (fast_compose _ _ e1 ea (IZR 12640955 * bpow radix2 (-95)) (IZR 544 * bpow radix2 (-75)) _ (IZR 579821 * bpow radix2 (-20)) _ AP E1 Eea HAm _ Ea0 _).
  - apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0].
  - bpow_num. replace (- prec)%Z with (-53)%Z by reflexivity. bpow_num. clear - Fz. interval with (i_prec 200).
Qed.

Lemma evalcert_41 : EvalCert (IZR (6386271100470677) * bpow radix2 (-53)) (IZR (3434803524008033) * bpow radix2 (-106)) (IZR (-5801480134199431) * bpow radix2 (-54)) (IZR (7917375923837233) * bpow radix2 (-58)) (IZR (6878142175618719) * bpow radix2 (-56)) (IZR (-2920341689377327) * bpow radix2 (-55)) (IZR (4681630843285057) * bpow radix2 (-58)) (IZR (4093275074875525) * bpow radix2 (-57)) (IZR (-5281914005588973) * bpow radix2 (-57)) (IZR (2738973266020311) * bpow radix2 (-58)) (IZR (2786498339006241) * bpow radix2 (-46)) (IZR 542 * bpow radix2 (-75)) (IZR 962 * bpow radix2 (-75)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 271 (-271) (-74)); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_41.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_41.l1 th_ tl_ dg).
Qed.

Lemma segok_41 : SegOkRowA [(0x3fe23b71e2cc9e6a)%Z; (0x3c6c421c9f38224e)%Z; (0x3fe6b0479c620595)%Z; (0x3c8867df07d7f0c2)%Z; (0xbfd49c6a5a920887)%Z; (0x3f9c20cfbb7e5931)%Z; (0x3fb86fa24517a69f)%Z; (0xbfb4c0121209445e)%Z; (0x3f90a1eb1f622e41)%Z; (0x3f9d159fbd9ca10a)%Z; (0xbfa2c3df70098bed)%Z; (0x3f837629d1240fae)%Z; (0x4043cc9c6753ce42)%Z] (IZR 542 * bpow radix2 (-75)).
Proof.
  unfold SegOkRowA. cbn [nth].
  destruct (word_ok_intro (0x3fe23b71e2cc9e6a)%Z false 5131909903195754%positive 53%nat (2565954951597877)%Z 1%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c6c421c9f38224e)%Z false 7953990045672014%positive 109%nat (3976995022836007)%Z 1%Z (-108)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fe6b0479c620595)%Z false 6386271100470677%positive 53%nat (6386271100470677)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c8867df07d7f0c2)%Z false 6869607048016066%positive 107%nat (3434803524008033)%Z 1%Z (-106)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd49c6a5a920887)%Z true 5801480134199431%positive 54%nat (-5801480134199431)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3f9c20cfbb7e5931)%Z false 7917375923837233%positive 58%nat (7917375923837233)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fb86fa24517a69f)%Z false 6878142175618719%positive 56%nat (6878142175618719)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfb4c0121209445e)%Z true 5840683378754654%positive 56%nat (-2920341689377327)%Z 1%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3f90a1eb1f622e41)%Z false 4681630843285057%positive 58%nat (4681630843285057)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3f9d159fbd9ca10a)%Z false 8186550149751050%positive 58%nat (4093275074875525)%Z 1%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0xbfa2c3df70098bed)%Z true 5281914005588973%positive 57%nat (-5281914005588973)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3f837629d1240fae)%Z false 5477946532040622%positive 59%nat (2738973266020311)%Z 1%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x4043cc9c6753ce42)%Z false 5572996678012482%positive 47%nat (2786498339006241)%Z 1%Z (-46)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_41 _ _).
  all: seg_numeric.
Qed.

Lemma row_41 : nth (Z.to_nat (41%Z - 1)) atan2_segments [] = [(0x3fe23b71e2cc9e6a)%Z; (0x3c6c421c9f38224e)%Z; (0x3fe6b0479c620595)%Z; (0x3c8867df07d7f0c2)%Z; (0xbfd49c6a5a920887)%Z; (0x3f9c20cfbb7e5931)%Z; (0x3fb86fa24517a69f)%Z; (0xbfb4c0121209445e)%Z; (0x3f90a1eb1f622e41)%Z; (0x3f9d159fbd9ca10a)%Z; (0xbfa2c3df70098bed)%Z; (0x3f837629d1240fae)%Z; (0x4043cc9c6753ce42)%Z].
Proof. reflexivity. Qed.

Lemma fast_41 zh zl : finite zh -> finite zl -> / 128 <= B zh -> B zh <= 1 ->
  Znearest ne (B zh * 64) = 41%Z -> Rabs (B zl) <= bpow radix2 (-53) -> on_grid (-211) (B zl) ->
  exists h l, atan2_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    Rabs (B h + B l - atan (IZR 41 / 64 + ((B zh - IZR 41 / 64) + B zl))) <= bpow radix2 (-63) * atan (IZR 41 / 64 + ((B zh - IZR 41 / 64) + B zl)).
Proof.
  intros Fz Fl L U Hn Hl Hg.
  pose proof (series_segment_a zh zl 41%Z (IZR 542 * bpow radix2 (-75)) ltac:(lia) Fz Fl L U Hn Hl Hg segok_41) as SS.
  cbv zeta in SS. rewrite row_41 in SS. cbn [nth] in SS.
  destruct SS as [h [l [Hs [Fh [Fl' [Nrm [Ht [e1 [ea [E1 [Eea Eq]]]]]]]]]]].
  exists h, l. split; [exact Hs | split; [exact Fh | split; [exact Fl' | split; [exact Nrm | ]]]].
  destruct (word_ok_intro (0x3fe23b71e2cc9e6a)%Z false 5131909903195754%positive 53%nat (2565954951597877)%Z 1%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c6c421c9f38224e)%Z false 7953990045672014%positive 109%nat (3976995022836007)%Z 1%Z (-108)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fe6b0479c620595)%Z false 6386271100470677%positive 53%nat (6386271100470677)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c8867df07d7f0c2)%Z false 6869607048016066%positive 107%nat (3434803524008033)%Z 1%Z (-106)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd49c6a5a920887)%Z true 5801480134199431%positive 54%nat (-5801480134199431)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3f9c20cfbb7e5931)%Z false 7917375923837233%positive 58%nat (7917375923837233)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fb86fa24517a69f)%Z false 6878142175618719%positive 56%nat (6878142175618719)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfb4c0121209445e)%Z true 5840683378754654%positive 56%nat (-2920341689377327)%Z 1%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3f90a1eb1f622e41)%Z false 4681630843285057%positive 58%nat (4681630843285057)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3f9d159fbd9ca10a)%Z false 8186550149751050%positive 58%nat (4093275074875525)%Z 1%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0xbfa2c3df70098bed)%Z true 5281914005588973%positive 57%nat (-5281914005588973)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3f837629d1240fae)%Z false 5477946532040622%positive 59%nat (2738973266020311)%Z 1%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x4043cc9c6753ce42)%Z false 5572996678012482%positive 47%nat (2786498339006241)%Z 1%Z (-46)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  unfold seg_poly in Eq.
  pose proof (approx_41 _ _ _ _ _ _ _ _ _ _ _ _ _ ((B zh - IZR 41 / 64) + B zl) V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 Ht) as AP.
  pose proof (amin_41 ((B zh - IZR 41 / 64) + B zl) Ht) as HAm.
  destruct ea_dw_small as [Ea0 Ea1].
  rewrite Eq.
  refine (fast_compose _ _ e1 ea (IZR 11676517 * bpow radix2 (-93)) (IZR 542 * bpow radix2 (-75)) _ (IZR 591602 * bpow radix2 (-20)) _ AP E1 Eea HAm _ Ea0 _).
  - apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0].
  - bpow_num. replace (- prec)%Z with (-53)%Z by reflexivity. bpow_num. clear - Fz. interval with (i_prec 200).
Qed.

Lemma evalcert_42 : EvalCert (IZR (1573954272500815) * bpow radix2 (-51)) (IZR (-4525118533439843) * bpow radix2 (-109)) (IZR (-5775821275743605) * bpow radix2 (-54)) (IZR (4790123665751325) * bpow radix2 (-57)) (IZR (3213194418142491) * bpow radix2 (-55)) (IZR (-5720941479141221) * bpow radix2 (-56)) (IZR (344773820477665) * bpow radix2 (-54)) (IZR (7087356645010595) * bpow radix2 (-58)) (IZR (-8675153754544911) * bpow radix2 (-58)) (IZR (3124767869098841) * bpow radix2 (-58)) (IZR (5367896419992839) * bpow radix2 (-51)) (IZR 540 * bpow radix2 (-75)) (IZR 576 * bpow radix2 (-74)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 135 (-135) (-73)); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_42.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_42.l1 th_ tl_ dg).
Qed.

Lemma segok_42 : SegOkRowA [(0x3fe2958e59308e31)%Z; (0xbc709e73b0c6c087)%Z; (0x3fe65e032538713c)%Z; (0xbc60139242c09163)%Z; (0xbfd485142f6d4575)%Z; (0x3fa104979386fd1d)%Z; (0x3fb6d4c43fc67a36)%Z; (0xbfb4532a7ca51f65)%Z; (0x3f93991e918f0e10)%Z; (0x3f992de9cf38eca3)%Z; (0xbf9ed201a1e95b0f)%Z; (0x3f8633eb6dafb6b2)%Z; (0x40031212c74e0507)%Z] (IZR 540 * bpow radix2 (-75)).
Proof.
  unfold SegOkRowA. cbn [nth].
  destruct (word_ok_intro (0x3fe2958e59308e31)%Z false 5230988195040817%positive 53%nat (5230988195040817)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc709e73b0c6c087)%Z true 4677819351613575%positive 108%nat (-4677819351613575)%Z 0%Z (-108)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fe65e032538713c)%Z false 6295817090003260%positive 53%nat (1573954272500815)%Z 2%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc60139242c09163)%Z true 4525118533439843%positive 109%nat (-4525118533439843)%Z 0%Z (-109)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd485142f6d4575)%Z true 5775821275743605%positive 54%nat (-5775821275743605)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fa104979386fd1d)%Z false 4790123665751325%positive 57%nat (4790123665751325)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fb6d4c43fc67a36)%Z false 6426388836284982%positive 56%nat (3213194418142491)%Z 1%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfb4532a7ca51f65)%Z true 5720941479141221%positive 56%nat (-5720941479141221)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3f93991e918f0e10)%Z false 5516381127642640%positive 58%nat (344773820477665)%Z 4%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3f992de9cf38eca3)%Z false 7087356645010595%positive 58%nat (7087356645010595)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0xbf9ed201a1e95b0f)%Z true 8675153754544911%positive 58%nat (-8675153754544911)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3f8633eb6dafb6b2)%Z false 6249535738197682%positive 59%nat (3124767869098841)%Z 1%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x40031212c74e0507)%Z false 5367896419992839%positive 51%nat (5367896419992839)%Z 0%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_42 _ _).
  all: seg_numeric.
Qed.

Lemma row_42 : nth (Z.to_nat (42%Z - 1)) atan2_segments [] = [(0x3fe2958e59308e31)%Z; (0xbc709e73b0c6c087)%Z; (0x3fe65e032538713c)%Z; (0xbc60139242c09163)%Z; (0xbfd485142f6d4575)%Z; (0x3fa104979386fd1d)%Z; (0x3fb6d4c43fc67a36)%Z; (0xbfb4532a7ca51f65)%Z; (0x3f93991e918f0e10)%Z; (0x3f992de9cf38eca3)%Z; (0xbf9ed201a1e95b0f)%Z; (0x3f8633eb6dafb6b2)%Z; (0x40031212c74e0507)%Z].
Proof. reflexivity. Qed.

Lemma fast_42 zh zl : finite zh -> finite zl -> / 128 <= B zh -> B zh <= 1 ->
  Znearest ne (B zh * 64) = 42%Z -> Rabs (B zl) <= bpow radix2 (-53) -> on_grid (-211) (B zl) ->
  exists h l, atan2_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    Rabs (B h + B l - atan (IZR 42 / 64 + ((B zh - IZR 42 / 64) + B zl))) <= bpow radix2 (-63) * atan (IZR 42 / 64 + ((B zh - IZR 42 / 64) + B zl)).
Proof.
  intros Fz Fl L U Hn Hl Hg.
  pose proof (series_segment_a zh zl 42%Z (IZR 540 * bpow radix2 (-75)) ltac:(lia) Fz Fl L U Hn Hl Hg segok_42) as SS.
  cbv zeta in SS. rewrite row_42 in SS. cbn [nth] in SS.
  destruct SS as [h [l [Hs [Fh [Fl' [Nrm [Ht [e1 [ea [E1 [Eea Eq]]]]]]]]]]].
  exists h, l. split; [exact Hs | split; [exact Fh | split; [exact Fl' | split; [exact Nrm | ]]]].
  destruct (word_ok_intro (0x3fe2958e59308e31)%Z false 5230988195040817%positive 53%nat (5230988195040817)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc709e73b0c6c087)%Z true 4677819351613575%positive 108%nat (-4677819351613575)%Z 0%Z (-108)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fe65e032538713c)%Z false 6295817090003260%positive 53%nat (1573954272500815)%Z 2%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc60139242c09163)%Z true 4525118533439843%positive 109%nat (-4525118533439843)%Z 0%Z (-109)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd485142f6d4575)%Z true 5775821275743605%positive 54%nat (-5775821275743605)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fa104979386fd1d)%Z false 4790123665751325%positive 57%nat (4790123665751325)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fb6d4c43fc67a36)%Z false 6426388836284982%positive 56%nat (3213194418142491)%Z 1%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfb4532a7ca51f65)%Z true 5720941479141221%positive 56%nat (-5720941479141221)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3f93991e918f0e10)%Z false 5516381127642640%positive 58%nat (344773820477665)%Z 4%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3f992de9cf38eca3)%Z false 7087356645010595%positive 58%nat (7087356645010595)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0xbf9ed201a1e95b0f)%Z true 8675153754544911%positive 58%nat (-8675153754544911)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3f8633eb6dafb6b2)%Z false 6249535738197682%positive 59%nat (3124767869098841)%Z 1%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x40031212c74e0507)%Z false 5367896419992839%positive 51%nat (5367896419992839)%Z 0%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  unfold seg_poly in Eq.
  pose proof (approx_42 _ _ _ _ _ _ _ _ _ _ _ _ _ ((B zh - IZR 42 / 64) + B zl) V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 Ht) as AP.
  pose proof (amin_42 ((B zh - IZR 42 / 64) + B zl) Ht) as HAm.
  destruct ea_dw_small as [Ea0 Ea1].
  rewrite Eq.
  refine (fast_compose _ _ e1 ea (IZR 11213689 * bpow radix2 (-97)) (IZR 540 * bpow radix2 (-75)) _ (IZR 603219 * bpow radix2 (-20)) _ AP E1 Eea HAm _ Ea0 _).
  - apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0].
  - bpow_num. replace (- prec)%Z with (-53)%Z by reflexivity. bpow_num. clear - Fz. interval with (i_prec 200).
Qed.

Lemma evalcert_43 : EvalCert (IZR (775725150282151) * bpow radix2 (-50)) (IZR (5066454887780299) * bpow radix2 (-107)) (IZR (-5745454973460669) * bpow radix2 (-54)) (IZR (2782852794833527) * bpow radix2 (-56)) (IZR (2992359193270437) * bpow radix2 (-55)) (IZR (-2791509758311451) * bpow radix2 (-55)) (IZR (3116916035350447) * bpow radix2 (-57)) (IZR (6043292466209347) * bpow radix2 (-58)) (IZR (-5976981787885793) * bpow radix2 (-58)) (IZR (6897504421173529) * bpow radix2 (-59)) (IZR (-237741604862667) * bpow radix2 (-42)) (IZR 537 * bpow radix2 (-75)) (IZR 663 * bpow radix2 (-74)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 537 (-537) (-75)); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_43.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_43.l1 th_ tl_ dg).
Qed.

Lemma segok_43 : SegOkRowA [(0x3fe2ee628406cbca)%Z; (0x3c8c5d5e9ff0cf8d)%Z; (0x3fe60c24b0350d38)%Z; (0x3c81ffe9f3db4fcb)%Z; (0xbfd46975fac420bd)%Z; (0x3fa3c5fad098b4ee)%Z; (0x3fb54311d582b14a)%Z; (0xbfb3d5ba070ff836)%Z; (0x3f9625a32229df5e)%Z; (0x3f957857acb8e243)%Z; (0xbf953c08844bc0e1)%Z; (0x3f88813e64dc5919)%Z; (0xc04b0730fcff5960)%Z] (IZR 537 * bpow radix2 (-75)).
Proof.
  unfold SegOkRowA. cbn [nth].
  destruct (word_ok_intro (0x3fe2ee628406cbca)%Z false 5328656470035402%positive 53%nat (2664328235017701)%Z 1%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c8c5d5e9ff0cf8d)%Z false 7983960339566477%positive 107%nat (7983960339566477)%Z 0%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fe60c24b0350d38)%Z false 6205801202257208%positive 53%nat (775725150282151)%Z 3%Z (-50)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c81ffe9f3db4fcb)%Z false 5066454887780299%positive 107%nat (5066454887780299)%Z 0%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd46975fac420bd)%Z true 5745454973460669%positive 54%nat (-5745454973460669)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fa3c5fad098b4ee)%Z false 5565705589667054%positive 57%nat (2782852794833527)%Z 1%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fb54311d582b14a)%Z false 5984718386540874%positive 56%nat (2992359193270437)%Z 1%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfb3d5ba070ff836)%Z true 5583019516622902%positive 56%nat (-2791509758311451)%Z 1%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3f9625a32229df5e)%Z false 6233832070700894%positive 58%nat (3116916035350447)%Z 1%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3f957857acb8e243)%Z false 6043292466209347%positive 58%nat (6043292466209347)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0xbf953c08844bc0e1)%Z true 5976981787885793%positive 58%nat (-5976981787885793)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3f88813e64dc5919)%Z false 6897504421173529%positive 59%nat (6897504421173529)%Z 0%Z (-59)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc04b0730fcff5960)%Z true 7607731355605344%positive 47%nat (-237741604862667)%Z 5%Z (-42)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_43 _ _).
  all: seg_numeric.
Qed.

Lemma row_43 : nth (Z.to_nat (43%Z - 1)) atan2_segments [] = [(0x3fe2ee628406cbca)%Z; (0x3c8c5d5e9ff0cf8d)%Z; (0x3fe60c24b0350d38)%Z; (0x3c81ffe9f3db4fcb)%Z; (0xbfd46975fac420bd)%Z; (0x3fa3c5fad098b4ee)%Z; (0x3fb54311d582b14a)%Z; (0xbfb3d5ba070ff836)%Z; (0x3f9625a32229df5e)%Z; (0x3f957857acb8e243)%Z; (0xbf953c08844bc0e1)%Z; (0x3f88813e64dc5919)%Z; (0xc04b0730fcff5960)%Z].
Proof. reflexivity. Qed.

Lemma fast_43 zh zl : finite zh -> finite zl -> / 128 <= B zh -> B zh <= 1 ->
  Znearest ne (B zh * 64) = 43%Z -> Rabs (B zl) <= bpow radix2 (-53) -> on_grid (-211) (B zl) ->
  exists h l, atan2_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    Rabs (B h + B l - atan (IZR 43 / 64 + ((B zh - IZR 43 / 64) + B zl))) <= bpow radix2 (-63) * atan (IZR 43 / 64 + ((B zh - IZR 43 / 64) + B zl)).
Proof.
  intros Fz Fl L U Hn Hl Hg.
  pose proof (series_segment_a zh zl 43%Z (IZR 537 * bpow radix2 (-75)) ltac:(lia) Fz Fl L U Hn Hl Hg segok_43) as SS.
  cbv zeta in SS. rewrite row_43 in SS. cbn [nth] in SS.
  destruct SS as [h [l [Hs [Fh [Fl' [Nrm [Ht [e1 [ea [E1 [Eea Eq]]]]]]]]]]].
  exists h, l. split; [exact Hs | split; [exact Fh | split; [exact Fl' | split; [exact Nrm | ]]]].
  destruct (word_ok_intro (0x3fe2ee628406cbca)%Z false 5328656470035402%positive 53%nat (2664328235017701)%Z 1%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c8c5d5e9ff0cf8d)%Z false 7983960339566477%positive 107%nat (7983960339566477)%Z 0%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fe60c24b0350d38)%Z false 6205801202257208%positive 53%nat (775725150282151)%Z 3%Z (-50)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c81ffe9f3db4fcb)%Z false 5066454887780299%positive 107%nat (5066454887780299)%Z 0%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd46975fac420bd)%Z true 5745454973460669%positive 54%nat (-5745454973460669)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fa3c5fad098b4ee)%Z false 5565705589667054%positive 57%nat (2782852794833527)%Z 1%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fb54311d582b14a)%Z false 5984718386540874%positive 56%nat (2992359193270437)%Z 1%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfb3d5ba070ff836)%Z true 5583019516622902%positive 56%nat (-2791509758311451)%Z 1%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3f9625a32229df5e)%Z false 6233832070700894%positive 58%nat (3116916035350447)%Z 1%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3f957857acb8e243)%Z false 6043292466209347%positive 58%nat (6043292466209347)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0xbf953c08844bc0e1)%Z true 5976981787885793%positive 58%nat (-5976981787885793)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3f88813e64dc5919)%Z false 6897504421173529%positive 59%nat (6897504421173529)%Z 0%Z (-59)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc04b0730fcff5960)%Z true 7607731355605344%positive 47%nat (-237741604862667)%Z 5%Z (-42)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  unfold seg_poly in Eq.
  pose proof (approx_43 _ _ _ _ _ _ _ _ _ _ _ _ _ ((B zh - IZR 43 / 64) + B zl) V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 Ht) as AP.
  pose proof (amin_43 ((B zh - IZR 43 / 64) + B zl) Ht) as HAm.
  destruct ea_dw_small as [Ea0 Ea1].
  rewrite Eq.
  refine (fast_compose _ _ e1 ea (IZR 15945278 * bpow radix2 (-93)) (IZR 537 * bpow radix2 (-75)) _ (IZR 614671 * bpow radix2 (-20)) _ AP E1 Eea HAm _ Ea0 _).
  - apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0].
  - bpow_num. replace (- prec)%Z with (-53)%Z by reflexivity. bpow_num. clear - Fz. interval with (i_prec 200).
Qed.

Lemma evalcert_44 : EvalCert (IZR (6116294454147729) * bpow radix2 (-53)) (IZR (5686242500340467) * bpow radix2 (-107)) (IZR (-356919039764589) * bpow radix2 (-50)) (IZR (3143389225056385) * bpow radix2 (-56)) (IZR (5554445672279183) * bpow radix2 (-56)) (IZR (-5429592801591725) * bpow radix2 (-56)) (IZR (6840479409890417) * bpow radix2 (-58)) (IZR (5059596498737373) * bpow radix2 (-58)) (IZR (-6077728306568013) * bpow radix2 (-58)) (IZR (3645068698396973) * bpow radix2 (-58)) (IZR (-2736780305404849) * bpow radix2 (-46)) (IZR 534 * bpow radix2 (-75)) (IZR 745 * bpow radix2 (-74)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 267 (-267) (-74)); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_44.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_44.l1 th_ tl_ dg).
Qed.

Lemma segok_44 : SegOkRowA [(0x3fe345f01cce37bb)%Z; (0x3c81021137c71102)%Z; (0x3fe5babcc647fa91)%Z; (0x3c84339b8056eaf3)%Z; (0xbfd449db094286d0)%Z; (0x3fa655caac4cf102)%Z; (0x3fb3bbbd29386c8f)%Z; (0xbfb34a2f9636c1ad)%Z; (0x3f984d613951e471)%Z; (0x3f91f9ad1c0398dd)%Z; (0xbf9597a964c11b4d)%Z; (0x3f89e65761e6525a)%Z; (0xc043722ca3dd2762)%Z] (IZR 534 * bpow radix2 (-75)).
Proof.
  unfold SegOkRowA. cbn [nth].
  destruct (word_ok_intro (0x3fe345f01cce37bb)%Z false 5424922135246779%positive 53%nat (5424922135246779)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c81021137c71102)%Z false 4787347577573634%positive 107%nat (2393673788786817)%Z 1%Z (-106)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fe5babcc647fa91)%Z false 6116294454147729%positive 53%nat (6116294454147729)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c84339b8056eaf3)%Z false 5686242500340467%positive 107%nat (5686242500340467)%Z 0%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd449db094286d0)%Z true 5710704636233424%positive 54%nat (-356919039764589)%Z 4%Z (-50)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fa655caac4cf102)%Z false 6286778450112770%positive 57%nat (3143389225056385)%Z 1%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fb3bbbd29386c8f)%Z false 5554445672279183%positive 56%nat (5554445672279183)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfb34a2f9636c1ad)%Z true 5429592801591725%positive 56%nat (-5429592801591725)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3f984d613951e471)%Z false 6840479409890417%positive 58%nat (6840479409890417)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3f91f9ad1c0398dd)%Z false 5059596498737373%positive 58%nat (5059596498737373)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0xbf9597a964c11b4d)%Z true 6077728306568013%positive 58%nat (-6077728306568013)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3f89e65761e6525a)%Z false 7290137396793946%positive 59%nat (3645068698396973)%Z 1%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc043722ca3dd2762)%Z true 5473560610809698%positive 47%nat (-2736780305404849)%Z 1%Z (-46)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_44 _ _).
  all: seg_numeric.
Qed.

Lemma row_44 : nth (Z.to_nat (44%Z - 1)) atan2_segments [] = [(0x3fe345f01cce37bb)%Z; (0x3c81021137c71102)%Z; (0x3fe5babcc647fa91)%Z; (0x3c84339b8056eaf3)%Z; (0xbfd449db094286d0)%Z; (0x3fa655caac4cf102)%Z; (0x3fb3bbbd29386c8f)%Z; (0xbfb34a2f9636c1ad)%Z; (0x3f984d613951e471)%Z; (0x3f91f9ad1c0398dd)%Z; (0xbf9597a964c11b4d)%Z; (0x3f89e65761e6525a)%Z; (0xc043722ca3dd2762)%Z].
Proof. reflexivity. Qed.

Lemma fast_44 zh zl : finite zh -> finite zl -> / 128 <= B zh -> B zh <= 1 ->
  Znearest ne (B zh * 64) = 44%Z -> Rabs (B zl) <= bpow radix2 (-53) -> on_grid (-211) (B zl) ->
  exists h l, atan2_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    Rabs (B h + B l - atan (IZR 44 / 64 + ((B zh - IZR 44 / 64) + B zl))) <= bpow radix2 (-63) * atan (IZR 44 / 64 + ((B zh - IZR 44 / 64) + B zl)).
Proof.
  intros Fz Fl L U Hn Hl Hg.
  pose proof (series_segment_a zh zl 44%Z (IZR 534 * bpow radix2 (-75)) ltac:(lia) Fz Fl L U Hn Hl Hg segok_44) as SS.
  cbv zeta in SS. rewrite row_44 in SS. cbn [nth] in SS.
  destruct SS as [h [l [Hs [Fh [Fl' [Nrm [Ht [e1 [ea [E1 [Eea Eq]]]]]]]]]]].
  exists h, l. split; [exact Hs | split; [exact Fh | split; [exact Fl' | split; [exact Nrm | ]]]].
  destruct (word_ok_intro (0x3fe345f01cce37bb)%Z false 5424922135246779%positive 53%nat (5424922135246779)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c81021137c71102)%Z false 4787347577573634%positive 107%nat (2393673788786817)%Z 1%Z (-106)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fe5babcc647fa91)%Z false 6116294454147729%positive 53%nat (6116294454147729)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c84339b8056eaf3)%Z false 5686242500340467%positive 107%nat (5686242500340467)%Z 0%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd449db094286d0)%Z true 5710704636233424%positive 54%nat (-356919039764589)%Z 4%Z (-50)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fa655caac4cf102)%Z false 6286778450112770%positive 57%nat (3143389225056385)%Z 1%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fb3bbbd29386c8f)%Z false 5554445672279183%positive 56%nat (5554445672279183)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfb34a2f9636c1ad)%Z true 5429592801591725%positive 56%nat (-5429592801591725)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3f984d613951e471)%Z false 6840479409890417%positive 58%nat (6840479409890417)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3f91f9ad1c0398dd)%Z false 5059596498737373%positive 58%nat (5059596498737373)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0xbf9597a964c11b4d)%Z true 6077728306568013%positive 58%nat (-6077728306568013)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3f89e65761e6525a)%Z false 7290137396793946%positive 59%nat (3645068698396973)%Z 1%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc043722ca3dd2762)%Z true 5473560610809698%positive 47%nat (-2736780305404849)%Z 1%Z (-46)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  unfold seg_poly in Eq.
  pose proof (approx_44 _ _ _ _ _ _ _ _ _ _ _ _ _ ((B zh - IZR 44 / 64) + B zl) V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 Ht) as AP.
  pose proof (amin_44 ((B zh - IZR 44 / 64) + B zl) Ht) as HAm.
  destruct ea_dw_small as [Ea0 Ea1].
  rewrite Eq.
  refine (fast_compose _ _ e1 ea (IZR 11472105 * bpow radix2 (-93)) (IZR 534 * bpow radix2 (-75)) _ (IZR 625959 * bpow radix2 (-20)) _ AP E1 Eea HAm _ Ea0 _).
  - apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0].
  - bpow_num. replace (- prec)%Z with (-53)%Z by reflexivity. bpow_num. clear - Fz. interval with (i_prec 200).
Qed.

Lemma evalcert_45 : EvalCert (IZR (6027362873291799) * bpow radix2 (-53)) (IZR (285659623480901) * bpow radix2 (-103)) (IZR (-44311604198355) * bpow radix2 (-47)) (IZR (6954838502954825) * bpow radix2 (-57)) (IZR (2568341244587069) * bpow radix2 (-55)) (IZR (-5263182235488377) * bpow radix2 (-56)) (IZR (7343102366755073) * bpow radix2 (-58)) (IZR (8279875258256983) * bpow radix2 (-59)) (IZR (-8169307651020941) * bpow radix2 (-58)) (IZR (7583654290696219) * bpow radix2 (-59)) (IZR (3823066227029299) * bpow radix2 (-47)) (IZR 530 * bpow radix2 (-75)) (IZR 820 * bpow radix2 (-74)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 265 (-265) (-74)); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_45.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_45.l1 th_ tl_ dg).
Qed.

Lemma segok_45 : SegOkRowA [(0x3fe39c391cd4171a)%Z; (0xbc82304331d8bf46)%Z; (0x3fe569dac6feb417)%Z; (0x3c803ce50625e450)%Z; (0xbfd4268cb6bde980)%Z; (0x3fa8b56386705749)%Z; (0x3fb23fc91717587a)%Z; (0xbfb2b2d61b88d079)%Z; (0x3f9a1683401ea901)%Z; (0x3f8d6a80af8d8e57)%Z; (0xbf9d05f12899988d)%Z; (0x3f8af14b1c18a81b)%Z; (0x403b2a1df0d46a66)%Z] (IZR 530 * bpow radix2 (-75)).
Proof.
  unfold SegOkRowA. cbn [nth].
  destruct (word_ok_intro (0x3fe39c391cd4171a)%Z false 5519793668232986%positive 53%nat (2759896834116493)%Z 1%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc82304331d8bf46)%Z true 5119614738022214%positive 107%nat (-2559807369011107)%Z 1%Z (-106)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fe569dac6feb417)%Z false 6027362873291799%positive 53%nat (6027362873291799)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c803ce50625e450)%Z false 4570553975694416%positive 107%nat (285659623480901)%Z 4%Z (-103)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd4268cb6bde980)%Z true 5671885337389440%positive 54%nat (-44311604198355)%Z 7%Z (-47)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fa8b56386705749)%Z false 6954838502954825%positive 57%nat (6954838502954825)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fb23fc91717587a)%Z false 5136682489174138%positive 56%nat (2568341244587069)%Z 1%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfb2b2d61b88d079)%Z true 5263182235488377%positive 56%nat (-5263182235488377)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3f9a1683401ea901)%Z false 7343102366755073%positive 58%nat (7343102366755073)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3f8d6a80af8d8e57)%Z false 8279875258256983%positive 59%nat (8279875258256983)%Z 0%Z (-59)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0xbf9d05f12899988d)%Z true 8169307651020941%positive 58%nat (-8169307651020941)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3f8af14b1c18a81b)%Z false 7583654290696219%positive 59%nat (7583654290696219)%Z 0%Z (-59)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x403b2a1df0d46a66)%Z false 7646132454058598%positive 48%nat (3823066227029299)%Z 1%Z (-47)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_45 _ _).
  all: seg_numeric.
Qed.

Lemma row_45 : nth (Z.to_nat (45%Z - 1)) atan2_segments [] = [(0x3fe39c391cd4171a)%Z; (0xbc82304331d8bf46)%Z; (0x3fe569dac6feb417)%Z; (0x3c803ce50625e450)%Z; (0xbfd4268cb6bde980)%Z; (0x3fa8b56386705749)%Z; (0x3fb23fc91717587a)%Z; (0xbfb2b2d61b88d079)%Z; (0x3f9a1683401ea901)%Z; (0x3f8d6a80af8d8e57)%Z; (0xbf9d05f12899988d)%Z; (0x3f8af14b1c18a81b)%Z; (0x403b2a1df0d46a66)%Z].
Proof. reflexivity. Qed.

Lemma fast_45 zh zl : finite zh -> finite zl -> / 128 <= B zh -> B zh <= 1 ->
  Znearest ne (B zh * 64) = 45%Z -> Rabs (B zl) <= bpow radix2 (-53) -> on_grid (-211) (B zl) ->
  exists h l, atan2_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    Rabs (B h + B l - atan (IZR 45 / 64 + ((B zh - IZR 45 / 64) + B zl))) <= bpow radix2 (-63) * atan (IZR 45 / 64 + ((B zh - IZR 45 / 64) + B zl)).
Proof.
  intros Fz Fl L U Hn Hl Hg.
  pose proof (series_segment_a zh zl 45%Z (IZR 530 * bpow radix2 (-75)) ltac:(lia) Fz Fl L U Hn Hl Hg segok_45) as SS.
  cbv zeta in SS. rewrite row_45 in SS. cbn [nth] in SS.
  destruct SS as [h [l [Hs [Fh [Fl' [Nrm [Ht [e1 [ea [E1 [Eea Eq]]]]]]]]]]].
  exists h, l. split; [exact Hs | split; [exact Fh | split; [exact Fl' | split; [exact Nrm | ]]]].
  destruct (word_ok_intro (0x3fe39c391cd4171a)%Z false 5519793668232986%positive 53%nat (2759896834116493)%Z 1%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc82304331d8bf46)%Z true 5119614738022214%positive 107%nat (-2559807369011107)%Z 1%Z (-106)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fe569dac6feb417)%Z false 6027362873291799%positive 53%nat (6027362873291799)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c803ce50625e450)%Z false 4570553975694416%positive 107%nat (285659623480901)%Z 4%Z (-103)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd4268cb6bde980)%Z true 5671885337389440%positive 54%nat (-44311604198355)%Z 7%Z (-47)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fa8b56386705749)%Z false 6954838502954825%positive 57%nat (6954838502954825)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fb23fc91717587a)%Z false 5136682489174138%positive 56%nat (2568341244587069)%Z 1%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfb2b2d61b88d079)%Z true 5263182235488377%positive 56%nat (-5263182235488377)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3f9a1683401ea901)%Z false 7343102366755073%positive 58%nat (7343102366755073)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3f8d6a80af8d8e57)%Z false 8279875258256983%positive 59%nat (8279875258256983)%Z 0%Z (-59)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0xbf9d05f12899988d)%Z true 8169307651020941%positive 58%nat (-8169307651020941)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3f8af14b1c18a81b)%Z false 7583654290696219%positive 59%nat (7583654290696219)%Z 0%Z (-59)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x403b2a1df0d46a66)%Z false 7646132454058598%positive 48%nat (3823066227029299)%Z 1%Z (-47)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  unfold seg_poly in Eq.
  pose proof (approx_45 _ _ _ _ _ _ _ _ _ _ _ _ _ ((B zh - IZR 45 / 64) + B zl) V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 Ht) as AP.
  pose proof (amin_45 ((B zh - IZR 45 / 64) + B zl) Ht) as HAm.
  destruct ea_dw_small as [Ea0 Ea1].
  rewrite Eq.
  refine (fast_compose _ _ e1 ea (IZR 16022867 * bpow radix2 (-94)) (IZR 530 * bpow radix2 (-75)) _ (IZR 637085 * bpow radix2 (-20)) _ AP E1 Eea HAm _ Ea0 _).
  - apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0].
  - bpow_num. replace (- prec)%Z with (-53)%Z by reflexivity. bpow_num. clear - Fz. interval with (i_prec 200).
Qed.

Lemma evalcert_46 : EvalCert (IZR (5939067634806681) * bpow radix2 (-53)) (IZR (2493944416959837) * bpow radix2 (-107)) (IZR (-1407325749909117) * bpow radix2 (-52)) (IZR (1892877233245623) * bpow radix2 (-55)) (IZR (295771877511113) * bpow radix2 (-52)) (IZR (-1271536212403493) * bpow radix2 (-54)) (IZR (7748559052467941) * bpow radix2 (-58)) (IZR (1643308086575517) * bpow radix2 (-57)) (IZR (-3034947253550369) * bpow radix2 (-57)) (IZR (7633834445944817) * bpow radix2 (-59)) (IZR (-216775008803303) * bpow radix2 (-44)) (IZR 526 * bpow radix2 (-75)) (IZR 890 * bpow radix2 (-74)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 263 (-263) (-74)); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_46.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_46.l1 th_ tl_ dg).
Qed.

Lemma segok_46 : SegOkRowA [(0x3fe3f13fb89e96f4)%Z; (0x3c7ecf8b492644f0)%Z; (0x3fe5198cf0ab6f99)%Z; (0x3c71b8755e1ffaba)%Z; (0xbfd3ffd23da059f4)%Z; (0x3faae63f4c5d36dc)%Z; (0x3fb0d00c1b18fc90)%Z; (0xbfb211d261099494)%Z; (0x3f9b8745fdd7eee5)%Z; (0x3f875a51eb070674)%Z; (0xbf95908971eb7a42)%Z; (0x3f8b1eee966cb7f1)%Z; (0xc028a4fbacab3ce0)%Z] (IZR 526 * bpow radix2 (-75)).
Proof.
  unfold SegOkRowA. cbn [nth].
  destruct (word_ok_intro (0x3fe3f13fb89e96f4)%Z false 5613280540137204%positive 53%nat (1403320135034301)%Z 2%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c7ecf8b492644f0)%Z false 8672446435968240%positive 108%nat (542027902248015)%Z 4%Z (-104)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fe5198cf0ab6f99)%Z false 5939067634806681%positive 53%nat (5939067634806681)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c71b8755e1ffaba)%Z false 4987888833919674%positive 108%nat (2493944416959837)%Z 1%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd3ffd23da059f4)%Z true 5629302999636468%positive 54%nat (-1407325749909117)%Z 2%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3faae63f4c5d36dc)%Z false 7571508932982492%positive 57%nat (1892877233245623)%Z 2%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fb0d00c1b18fc90)%Z false 4732350040177808%positive 56%nat (295771877511113)%Z 4%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfb211d261099494)%Z true 5086144849613972%positive 56%nat (-1271536212403493)%Z 2%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3f9b8745fdd7eee5)%Z false 7748559052467941%positive 58%nat (7748559052467941)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3f875a51eb070674)%Z false 6573232346302068%positive 59%nat (1643308086575517)%Z 2%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0xbf95908971eb7a42)%Z true 6069894507100738%positive 58%nat (-3034947253550369)%Z 1%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3f8b1eee966cb7f1)%Z false 7633834445944817%positive 59%nat (7633834445944817)%Z 0%Z (-59)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc028a4fbacab3ce0)%Z true 6936800281705696%positive 49%nat (-216775008803303)%Z 5%Z (-44)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_46 _ _).
  all: seg_numeric.
Qed.

Lemma row_46 : nth (Z.to_nat (46%Z - 1)) atan2_segments [] = [(0x3fe3f13fb89e96f4)%Z; (0x3c7ecf8b492644f0)%Z; (0x3fe5198cf0ab6f99)%Z; (0x3c71b8755e1ffaba)%Z; (0xbfd3ffd23da059f4)%Z; (0x3faae63f4c5d36dc)%Z; (0x3fb0d00c1b18fc90)%Z; (0xbfb211d261099494)%Z; (0x3f9b8745fdd7eee5)%Z; (0x3f875a51eb070674)%Z; (0xbf95908971eb7a42)%Z; (0x3f8b1eee966cb7f1)%Z; (0xc028a4fbacab3ce0)%Z].
Proof. reflexivity. Qed.

Lemma fast_46 zh zl : finite zh -> finite zl -> / 128 <= B zh -> B zh <= 1 ->
  Znearest ne (B zh * 64) = 46%Z -> Rabs (B zl) <= bpow radix2 (-53) -> on_grid (-211) (B zl) ->
  exists h l, atan2_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    Rabs (B h + B l - atan (IZR 46 / 64 + ((B zh - IZR 46 / 64) + B zl))) <= bpow radix2 (-63) * atan (IZR 46 / 64 + ((B zh - IZR 46 / 64) + B zl)).
Proof.
  intros Fz Fl L U Hn Hl Hg.
  pose proof (series_segment_a zh zl 46%Z (IZR 526 * bpow radix2 (-75)) ltac:(lia) Fz Fl L U Hn Hl Hg segok_46) as SS.
  cbv zeta in SS. rewrite row_46 in SS. cbn [nth] in SS.
  destruct SS as [h [l [Hs [Fh [Fl' [Nrm [Ht [e1 [ea [E1 [Eea Eq]]]]]]]]]]].
  exists h, l. split; [exact Hs | split; [exact Fh | split; [exact Fl' | split; [exact Nrm | ]]]].
  destruct (word_ok_intro (0x3fe3f13fb89e96f4)%Z false 5613280540137204%positive 53%nat (1403320135034301)%Z 2%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c7ecf8b492644f0)%Z false 8672446435968240%positive 108%nat (542027902248015)%Z 4%Z (-104)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fe5198cf0ab6f99)%Z false 5939067634806681%positive 53%nat (5939067634806681)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c71b8755e1ffaba)%Z false 4987888833919674%positive 108%nat (2493944416959837)%Z 1%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd3ffd23da059f4)%Z true 5629302999636468%positive 54%nat (-1407325749909117)%Z 2%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3faae63f4c5d36dc)%Z false 7571508932982492%positive 57%nat (1892877233245623)%Z 2%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fb0d00c1b18fc90)%Z false 4732350040177808%positive 56%nat (295771877511113)%Z 4%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfb211d261099494)%Z true 5086144849613972%positive 56%nat (-1271536212403493)%Z 2%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3f9b8745fdd7eee5)%Z false 7748559052467941%positive 58%nat (7748559052467941)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3f875a51eb070674)%Z false 6573232346302068%positive 59%nat (1643308086575517)%Z 2%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0xbf95908971eb7a42)%Z true 6069894507100738%positive 58%nat (-3034947253550369)%Z 1%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3f8b1eee966cb7f1)%Z false 7633834445944817%positive 59%nat (7633834445944817)%Z 0%Z (-59)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc028a4fbacab3ce0)%Z true 6936800281705696%positive 49%nat (-216775008803303)%Z 5%Z (-44)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  unfold seg_poly in Eq.
  pose proof (approx_46 _ _ _ _ _ _ _ _ _ _ _ _ _ ((B zh - IZR 46 / 64) + B zl) V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 Ht) as AP.
  pose proof (amin_46 ((B zh - IZR 46 / 64) + B zl) Ht) as HAm.
  destruct ea_dw_small as [Ea0 Ea1].
  rewrite Eq.
  refine (fast_compose _ _ e1 ea (IZR 14538222 * bpow radix2 (-95)) (IZR 526 * bpow radix2 (-75)) _ (IZR 648049 * bpow radix2 (-20)) _ AP E1 Eea HAm _ Ea0 _).
  - apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0].
  - bpow_num. replace (- prec)%Z with (-53)%Z by reflexivity. bpow_num. clear - Fz. interval with (i_prec 200).
Qed.

Lemma evalcert_47 : EvalCert (IZR (5851465209741333) * bpow radix2 (-53)) (IZR (-7617190551352731) * bpow radix2 (-108)) (IZR (-697906714944565) * bpow radix2 (-51)) (IZR (4069258420407729) * bpow radix2 (-56)) (IZR (8684383974053163) * bpow radix2 (-57)) (IZR (-4900667896697289) * bpow radix2 (-56)) (IZR (4032220387557805) * bpow radix2 (-57)) (IZR (5001378802156627) * bpow radix2 (-59)) (IZR (-5628594514241257) * bpow radix2 (-58)) (IZR (7714426666903937) * bpow radix2 (-59)) (IZR (-1381315358198893) * bpow radix2 (-47)) (IZR 522 * bpow radix2 (-75)) (IZR 954 * bpow radix2 (-74)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 261 (-261) (-74)); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_47.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_47.l1 th_ tl_ dg).
Qed.

Lemma segok_47 : SegOkRowA [(0x3fe445065b795b56)%Z; (0xbc7f76d0163f79c8)%Z; (0x3fe4c9e0693e0015)%Z; (0xbc7b0fcb60fff59b)%Z; (0xbfd3d5f08ea521a8)%Z; (0x3face9f01d4b9b62)%Z; (0x3faeda66b5ddd52b)%Z; (0xbfb16921a92511c9)%Z; (0x3f9ca690efb6835a)%Z; (0x3f81c4ba3ee3c453)%Z; (0xbf93ff2d489b26e9)%Z; (0x3f8b683aed206981)%Z; (0xc023a1322cfe31b4)%Z] (IZR 522 * bpow radix2 (-75)).
Proof.
  unfold SegOkRowA. cbn [nth].
  destruct (word_ok_intro (0x3fe445065b795b56)%Z false 5705393141013334%positive 53%nat (2852696570506667)%Z 1%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc7f76d0163f79c8)%Z true 8856360376564168%positive 108%nat (-1107045047070521)%Z 3%Z (-105)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fe4c9e0693e0015)%Z false 5851465209741333%positive 53%nat (5851465209741333)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc7b0fcb60fff59b)%Z true 7617190551352731%positive 108%nat (-7617190551352731)%Z 0%Z (-108)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd3d5f08ea521a8)%Z true 5583253719556520%positive 54%nat (-697906714944565)%Z 3%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3face9f01d4b9b62)%Z false 8138516840815458%positive 57%nat (4069258420407729)%Z 1%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3faeda66b5ddd52b)%Z false 8684383974053163%positive 57%nat (8684383974053163)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfb16921a92511c9)%Z true 4900667896697289%positive 56%nat (-4900667896697289)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3f9ca690efb6835a)%Z false 8064440775115610%positive 58%nat (4032220387557805)%Z 1%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3f81c4ba3ee3c453)%Z false 5001378802156627%positive 59%nat (5001378802156627)%Z 0%Z (-59)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0xbf93ff2d489b26e9)%Z true 5628594514241257%positive 58%nat (-5628594514241257)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3f8b683aed206981)%Z false 7714426666903937%positive 59%nat (7714426666903937)%Z 0%Z (-59)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc023a1322cfe31b4)%Z true 5525261432795572%positive 49%nat (-1381315358198893)%Z 2%Z (-47)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_47 _ _).
  all: seg_numeric.
Qed.

Lemma row_47 : nth (Z.to_nat (47%Z - 1)) atan2_segments [] = [(0x3fe445065b795b56)%Z; (0xbc7f76d0163f79c8)%Z; (0x3fe4c9e0693e0015)%Z; (0xbc7b0fcb60fff59b)%Z; (0xbfd3d5f08ea521a8)%Z; (0x3face9f01d4b9b62)%Z; (0x3faeda66b5ddd52b)%Z; (0xbfb16921a92511c9)%Z; (0x3f9ca690efb6835a)%Z; (0x3f81c4ba3ee3c453)%Z; (0xbf93ff2d489b26e9)%Z; (0x3f8b683aed206981)%Z; (0xc023a1322cfe31b4)%Z].
Proof. reflexivity. Qed.

Lemma fast_47 zh zl : finite zh -> finite zl -> / 128 <= B zh -> B zh <= 1 ->
  Znearest ne (B zh * 64) = 47%Z -> Rabs (B zl) <= bpow radix2 (-53) -> on_grid (-211) (B zl) ->
  exists h l, atan2_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    Rabs (B h + B l - atan (IZR 47 / 64 + ((B zh - IZR 47 / 64) + B zl))) <= bpow radix2 (-63) * atan (IZR 47 / 64 + ((B zh - IZR 47 / 64) + B zl)).
Proof.
  intros Fz Fl L U Hn Hl Hg.
  pose proof (series_segment_a zh zl 47%Z (IZR 522 * bpow radix2 (-75)) ltac:(lia) Fz Fl L U Hn Hl Hg segok_47) as SS.
  cbv zeta in SS. rewrite row_47 in SS. cbn [nth] in SS.
  destruct SS as [h [l [Hs [Fh [Fl' [Nrm [Ht [e1 [ea [E1 [Eea Eq]]]]]]]]]]].
  exists h, l. split; [exact Hs | split; [exact Fh | split; [exact Fl' | split; [exact Nrm | ]]]].
  destruct (word_ok_intro (0x3fe445065b795b56)%Z false 5705393141013334%positive 53%nat (2852696570506667)%Z 1%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc7f76d0163f79c8)%Z true 8856360376564168%positive 108%nat (-1107045047070521)%Z 3%Z (-105)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fe4c9e0693e0015)%Z false 5851465209741333%positive 53%nat (5851465209741333)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc7b0fcb60fff59b)%Z true 7617190551352731%positive 108%nat (-7617190551352731)%Z 0%Z (-108)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd3d5f08ea521a8)%Z true 5583253719556520%positive 54%nat (-697906714944565)%Z 3%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3face9f01d4b9b62)%Z false 8138516840815458%positive 57%nat (4069258420407729)%Z 1%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3faeda66b5ddd52b)%Z false 8684383974053163%positive 57%nat (8684383974053163)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfb16921a92511c9)%Z true 4900667896697289%positive 56%nat (-4900667896697289)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3f9ca690efb6835a)%Z false 8064440775115610%positive 58%nat (4032220387557805)%Z 1%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3f81c4ba3ee3c453)%Z false 5001378802156627%positive 59%nat (5001378802156627)%Z 0%Z (-59)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0xbf93ff2d489b26e9)%Z true 5628594514241257%positive 58%nat (-5628594514241257)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3f8b683aed206981)%Z false 7714426666903937%positive 59%nat (7714426666903937)%Z 0%Z (-59)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc023a1322cfe31b4)%Z true 5525261432795572%positive 49%nat (-1381315358198893)%Z 2%Z (-47)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  unfold seg_poly in Eq.
  pose proof (approx_47 _ _ _ _ _ _ _ _ _ _ _ _ _ ((B zh - IZR 47 / 64) + B zl) V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 Ht) as AP.
  pose proof (amin_47 ((B zh - IZR 47 / 64) + B zl) Ht) as HAm.
  destruct ea_dw_small as [Ea0 Ea1].
  rewrite Eq.
  refine (fast_compose _ _ e1 ea (IZR 11578571 * bpow radix2 (-95)) (IZR 522 * bpow radix2 (-75)) _ (IZR 658852 * bpow radix2 (-20)) _ AP E1 Eea HAm _ Ea0 _).
  - apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0].
  - bpow_num. replace (- prec)%Z with (-53)%Z by reflexivity. bpow_num. clear - Fz. interval with (i_prec 200).
Qed.

Lemma evalcert_48 : EvalCert (IZR (5764607523034235) * bpow radix2 (-53)) (IZR (-1080863910568919) * bpow radix2 (-106)) (IZR (-5534023222112865) * bpow radix2 (-54)) (IZR (1082208985657627) * bpow radix2 (-54)) (IZR (7933575690373767) * bpow radix2 (-57)) (IZR (-4708766067387939) * bpow radix2 (-56)) (IZR (2074541692033757) * bpow radix2 (-56)) (IZR (3564380599619171) * bpow radix2 (-59)) (IZR (-1915835285462679) * bpow radix2 (-56)) (IZR (7599180013937521) * bpow radix2 (-59)) (IZR (970273959659403) * bpow radix2 (-44)) (IZR 518 * bpow radix2 (-75)) (IZR 1012 * bpow radix2 (-74)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 259 (-259) (-74)); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_48.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_48.l1 th_ tl_ dg).
Qed.

Lemma segok_48 : SegOkRowA [(0x3fe4978fa3269ee1)%Z; (0x3c72419a87f2a458)%Z; (0x3fe47ae147ae147b)%Z; (0xbc6eb851eb851eb8)%Z; (0xbfd3a92a30553261)%Z; (0x3faec21b514d88d8)%Z; (0x3fac2f8b88d2ca87)%Z; (0xbfb0ba9908c6ee23)%Z; (0x3f9d7b2382806b74)%Z; (0x3f7953920ef81cc6)%Z; (0xbf9b39c4a68d7a5c)%Z; (0x3f8aff69f950a371)%Z; (0x404b93ac159a3c58)%Z] (IZR 518 * bpow radix2 (-75)).
Proof.
  unfold SegOkRowA. cbn [nth].
  destruct (word_ok_intro (0x3fe4978fa3269ee1)%Z false 5796142707547873%positive 53%nat (5796142707547873)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c72419a87f2a458)%Z false 5138681542386776%positive 108%nat (642335192798347)%Z 3%Z (-105)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fe47ae147ae147b)%Z false 5764607523034235%positive 53%nat (5764607523034235)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc6eb851eb851eb8)%Z true 8646911284551352%positive 109%nat (-1080863910568919)%Z 3%Z (-106)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd3a92a30553261)%Z true 5534023222112865%positive 54%nat (-5534023222112865)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3faec21b514d88d8)%Z false 8657671885261016%positive 57%nat (1082208985657627)%Z 3%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fac2f8b88d2ca87)%Z false 7933575690373767%positive 57%nat (7933575690373767)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfb0ba9908c6ee23)%Z true 4708766067387939%positive 56%nat (-4708766067387939)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3f9d7b2382806b74)%Z false 8298166768135028%positive 58%nat (2074541692033757)%Z 2%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3f7953920ef81cc6)%Z false 7128761199238342%positive 60%nat (3564380599619171)%Z 1%Z (-59)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0xbf9b39c4a68d7a5c)%Z true 7663341141850716%positive 58%nat (-1915835285462679)%Z 2%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3f8aff69f950a371)%Z false 7599180013937521%positive 59%nat (7599180013937521)%Z 0%Z (-59)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x404b93ac159a3c58)%Z false 7762191677275224%positive 47%nat (970273959659403)%Z 3%Z (-44)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_48 _ _).
  all: seg_numeric.
Qed.

Lemma row_48 : nth (Z.to_nat (48%Z - 1)) atan2_segments [] = [(0x3fe4978fa3269ee1)%Z; (0x3c72419a87f2a458)%Z; (0x3fe47ae147ae147b)%Z; (0xbc6eb851eb851eb8)%Z; (0xbfd3a92a30553261)%Z; (0x3faec21b514d88d8)%Z; (0x3fac2f8b88d2ca87)%Z; (0xbfb0ba9908c6ee23)%Z; (0x3f9d7b2382806b74)%Z; (0x3f7953920ef81cc6)%Z; (0xbf9b39c4a68d7a5c)%Z; (0x3f8aff69f950a371)%Z; (0x404b93ac159a3c58)%Z].
Proof. reflexivity. Qed.

Lemma fast_48 zh zl : finite zh -> finite zl -> / 128 <= B zh -> B zh <= 1 ->
  Znearest ne (B zh * 64) = 48%Z -> Rabs (B zl) <= bpow radix2 (-53) -> on_grid (-211) (B zl) ->
  exists h l, atan2_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    Rabs (B h + B l - atan (IZR 48 / 64 + ((B zh - IZR 48 / 64) + B zl))) <= bpow radix2 (-63) * atan (IZR 48 / 64 + ((B zh - IZR 48 / 64) + B zl)).
Proof.
  intros Fz Fl L U Hn Hl Hg.
  pose proof (series_segment_a zh zl 48%Z (IZR 518 * bpow radix2 (-75)) ltac:(lia) Fz Fl L U Hn Hl Hg segok_48) as SS.
  cbv zeta in SS. rewrite row_48 in SS. cbn [nth] in SS.
  destruct SS as [h [l [Hs [Fh [Fl' [Nrm [Ht [e1 [ea [E1 [Eea Eq]]]]]]]]]]].
  exists h, l. split; [exact Hs | split; [exact Fh | split; [exact Fl' | split; [exact Nrm | ]]]].
  destruct (word_ok_intro (0x3fe4978fa3269ee1)%Z false 5796142707547873%positive 53%nat (5796142707547873)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c72419a87f2a458)%Z false 5138681542386776%positive 108%nat (642335192798347)%Z 3%Z (-105)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fe47ae147ae147b)%Z false 5764607523034235%positive 53%nat (5764607523034235)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc6eb851eb851eb8)%Z true 8646911284551352%positive 109%nat (-1080863910568919)%Z 3%Z (-106)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd3a92a30553261)%Z true 5534023222112865%positive 54%nat (-5534023222112865)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3faec21b514d88d8)%Z false 8657671885261016%positive 57%nat (1082208985657627)%Z 3%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fac2f8b88d2ca87)%Z false 7933575690373767%positive 57%nat (7933575690373767)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfb0ba9908c6ee23)%Z true 4708766067387939%positive 56%nat (-4708766067387939)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3f9d7b2382806b74)%Z false 8298166768135028%positive 58%nat (2074541692033757)%Z 2%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3f7953920ef81cc6)%Z false 7128761199238342%positive 60%nat (3564380599619171)%Z 1%Z (-59)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0xbf9b39c4a68d7a5c)%Z true 7663341141850716%positive 58%nat (-1915835285462679)%Z 2%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3f8aff69f950a371)%Z false 7599180013937521%positive 59%nat (7599180013937521)%Z 0%Z (-59)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x404b93ac159a3c58)%Z false 7762191677275224%positive 47%nat (970273959659403)%Z 3%Z (-44)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  unfold seg_poly in Eq.
  pose proof (approx_48 _ _ _ _ _ _ _ _ _ _ _ _ _ ((B zh - IZR 48 / 64) + B zl) V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 Ht) as AP.
  pose proof (amin_48 ((B zh - IZR 48 / 64) + B zl) Ht) as HAm.
  destruct ea_dw_small as [Ea0 Ea1].
  rewrite Eq.
  refine (fast_compose _ _ e1 ea (IZR 16267606 * bpow radix2 (-93)) (IZR 518 * bpow radix2 (-75)) _ (IZR 669496 * bpow radix2 (-20)) _ AP E1 Eea HAm _ Ea0 _).
  - apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0].
  - bpow_num. replace (- prec)%Z with (-53)%Z by reflexivity. bpow_num. clear - Fz. interval with (i_prec 200).
Qed.

Lemma evalcert_49 : EvalCert (IZR (5678542119042497) * bpow radix2 (-53)) (IZR (4946542549009675) * bpow radix2 (-110)) (IZR (-5481886435375487) * bpow radix2 (-54)) (IZR (4565423304325889) * bpow radix2 (-56)) (IZR (1803283242495351) * bpow radix2 (-55)) (IZR (-4512281408205493) * bpow radix2 (-56)) (IZR (4228407446179617) * bpow radix2 (-57)) (IZR (1130232226538717) * bpow radix2 (-58)) (IZR (-3294681340475809) * bpow radix2 (-57)) (IZR (7475232200825229) * bpow radix2 (-59)) (IZR (2908251418782171) * bpow radix2 (-46)) (IZR 513 * bpow radix2 (-75)) (IZR 533 * bpow radix2 (-73)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 513 (-513) (-75)); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_49.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_49.l1 th_ tl_ dg).
Qed.

Lemma segok_49 : SegOkRowA [(0x3fe4e8de5bb6ec04)%Z; (0x3c84a33dbeb3796c)%Z; (0x3fe42c9a9dd8fdc1)%Z; (0x3c5192daaf80050b)%Z; (0xbfd379bf25adf97f)%Z; (0x3fb0383a724dbb01)%Z; (0x3fa9a04e6464b5dc)%Z; (0xbfb007e5627672b5)%Z; (0x3f9e0b6da7971e42)%Z; (0x3f700fc2c9819374)%Z; (0xbf9768fd8de4f342)%Z; (0x3f8a8eaf1ff1998d)%Z; (0x4044aa141977d3b6)%Z] (IZR 513 * bpow radix2 (-75)).
Proof.
  unfold SegOkRowA. cbn [nth].
  destruct (word_ok_intro (0x3fe4e8de5bb6ec04)%Z false 5885541253311492%positive 53%nat (1471385313327873)%Z 2%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c84a33dbeb3796c)%Z false 5808985121978732%positive 107%nat (1452246280494683)%Z 2%Z (-105)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fe42c9a9dd8fdc1)%Z false 5678542119042497%positive 53%nat (5678542119042497)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c5192daaf80050b)%Z false 4946542549009675%positive 110%nat (4946542549009675)%Z 0%Z (-110)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd379bf25adf97f)%Z true 5481886435375487%positive 54%nat (-5481886435375487)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fb0383a724dbb01)%Z false 4565423304325889%positive 56%nat (4565423304325889)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fa9a04e6464b5dc)%Z false 7213132969981404%positive 57%nat (1803283242495351)%Z 2%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfb007e5627672b5)%Z true 4512281408205493%positive 56%nat (-4512281408205493)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3f9e0b6da7971e42)%Z false 8456814892359234%positive 58%nat (4228407446179617)%Z 1%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3f700fc2c9819374)%Z false 4520928906154868%positive 60%nat (1130232226538717)%Z 2%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0xbf9768fd8de4f342)%Z true 6589362680951618%positive 58%nat (-3294681340475809)%Z 1%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3f8a8eaf1ff1998d)%Z false 7475232200825229%positive 59%nat (7475232200825229)%Z 0%Z (-59)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x4044aa141977d3b6)%Z false 5816502837564342%positive 47%nat (2908251418782171)%Z 1%Z (-46)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_49 _ _).
  all: seg_numeric.
Qed.

Lemma row_49 : nth (Z.to_nat (49%Z - 1)) atan2_segments [] = [(0x3fe4e8de5bb6ec04)%Z; (0x3c84a33dbeb3796c)%Z; (0x3fe42c9a9dd8fdc1)%Z; (0x3c5192daaf80050b)%Z; (0xbfd379bf25adf97f)%Z; (0x3fb0383a724dbb01)%Z; (0x3fa9a04e6464b5dc)%Z; (0xbfb007e5627672b5)%Z; (0x3f9e0b6da7971e42)%Z; (0x3f700fc2c9819374)%Z; (0xbf9768fd8de4f342)%Z; (0x3f8a8eaf1ff1998d)%Z; (0x4044aa141977d3b6)%Z].
Proof. reflexivity. Qed.

Lemma fast_49 zh zl : finite zh -> finite zl -> / 128 <= B zh -> B zh <= 1 ->
  Znearest ne (B zh * 64) = 49%Z -> Rabs (B zl) <= bpow radix2 (-53) -> on_grid (-211) (B zl) ->
  exists h l, atan2_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    Rabs (B h + B l - atan (IZR 49 / 64 + ((B zh - IZR 49 / 64) + B zl))) <= bpow radix2 (-63) * atan (IZR 49 / 64 + ((B zh - IZR 49 / 64) + B zl)).
Proof.
  intros Fz Fl L U Hn Hl Hg.
  pose proof (series_segment_a zh zl 49%Z (IZR 513 * bpow radix2 (-75)) ltac:(lia) Fz Fl L U Hn Hl Hg segok_49) as SS.
  cbv zeta in SS. rewrite row_49 in SS. cbn [nth] in SS.
  destruct SS as [h [l [Hs [Fh [Fl' [Nrm [Ht [e1 [ea [E1 [Eea Eq]]]]]]]]]]].
  exists h, l. split; [exact Hs | split; [exact Fh | split; [exact Fl' | split; [exact Nrm | ]]]].
  destruct (word_ok_intro (0x3fe4e8de5bb6ec04)%Z false 5885541253311492%positive 53%nat (1471385313327873)%Z 2%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c84a33dbeb3796c)%Z false 5808985121978732%positive 107%nat (1452246280494683)%Z 2%Z (-105)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fe42c9a9dd8fdc1)%Z false 5678542119042497%positive 53%nat (5678542119042497)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c5192daaf80050b)%Z false 4946542549009675%positive 110%nat (4946542549009675)%Z 0%Z (-110)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd379bf25adf97f)%Z true 5481886435375487%positive 54%nat (-5481886435375487)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fb0383a724dbb01)%Z false 4565423304325889%positive 56%nat (4565423304325889)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fa9a04e6464b5dc)%Z false 7213132969981404%positive 57%nat (1803283242495351)%Z 2%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfb007e5627672b5)%Z true 4512281408205493%positive 56%nat (-4512281408205493)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3f9e0b6da7971e42)%Z false 8456814892359234%positive 58%nat (4228407446179617)%Z 1%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3f700fc2c9819374)%Z false 4520928906154868%positive 60%nat (1130232226538717)%Z 2%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0xbf9768fd8de4f342)%Z true 6589362680951618%positive 58%nat (-3294681340475809)%Z 1%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3f8a8eaf1ff1998d)%Z false 7475232200825229%positive 59%nat (7475232200825229)%Z 0%Z (-59)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x4044aa141977d3b6)%Z false 5816502837564342%positive 47%nat (2908251418782171)%Z 1%Z (-46)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  unfold seg_poly in Eq.
  pose proof (approx_49 _ _ _ _ _ _ _ _ _ _ _ _ _ ((B zh - IZR 49 / 64) + B zl) V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 Ht) as AP.
  pose proof (amin_49 ((B zh - IZR 49 / 64) + B zl) Ht) as HAm.
  destruct ea_dw_small as [Ea0 Ea1].
  rewrite Eq.
  refine (fast_compose _ _ e1 ea (IZR 12190212 * bpow radix2 (-93)) (IZR 513 * bpow radix2 (-75)) _ (IZR 679982 * bpow radix2 (-20)) _ AP E1 Eea HAm _ Ea0 _).
  - apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0].
  - bpow_num. replace (- prec)%Z with (-53)%Z by reflexivity. bpow_num. clear - Fz. interval with (i_prec 200).
Qed.

Lemma evalcert_50 : EvalCert (IZR (1398328083210245) * bpow radix2 (-51)) (IZR (-289497610977121) * bpow radix2 (-104)) (IZR (-1356776793897145) * bpow radix2 (-52)) (IZR (1194994805786361) * bpow radix2 (-54)) (IZR (3261819544195039) * bpow radix2 (-56)) (IZR (-539110692148819) * bpow radix2 (-53)) (IZR (8547595698387151) * bpow radix2 (-58)) (IZR (8691274806480263) * bpow radix2 (-62)) (IZR (-341669665657215) * bpow radix2 (-55)) (IZR (3579529746466387) * bpow radix2 (-58)) (IZR (-3038013475173807) * bpow radix2 (-46)) (IZR 1015 * bpow radix2 (-76)) (IZR 557 * bpow radix2 (-73)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 1015 (-1015) (-76)); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_50.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_50.l1 th_ tl_ dg).
Qed.

Lemma segok_50 : SegOkRowA [(0x3fe538f57b89061f)%Z; (0xbc81bb74abda520c)%Z; (0x3fe3df1682b78014)%Z; (0xbc7074bea43ff610)%Z; (0xbfd347ecdb5be2e4)%Z; (0x3fb0fb5da3a11be4)%Z; (0x3fa72d3716819fbe)%Z; (0xbfaea517d4cd6530)%Z; (0x3f9e5dfe354938cf)%Z; (0x3f5ee0ab1b7c4d87)%Z; (0xbf836bf2b0d517f0)%Z; (0x3f896f206e008ca6)%Z; (0xc045961d44056b5e)%Z] (IZR 1015 * bpow radix2 (-76)).
Proof.
  unfold SegOkRowA. cbn [nth].
  destruct (word_ok_intro (0x3fe538f57b89061f)%Z false 5973601501644319%positive 53%nat (5973601501644319)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc81bb74abda520c)%Z true 4991184377893388%positive 107%nat (-1247796094473347)%Z 2%Z (-105)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fe3df1682b78014)%Z false 5593312332840980%positive 53%nat (1398328083210245)%Z 2%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc7074bea43ff610)%Z true 4631961775633936%positive 108%nat (-289497610977121)%Z 4%Z (-104)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd347ecdb5be2e4)%Z true 5427107175588580%positive 54%nat (-1356776793897145)%Z 2%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fb0fb5da3a11be4)%Z false 4779979223145444%positive 56%nat (1194994805786361)%Z 2%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fa72d3716819fbe)%Z false 6523639088390078%positive 57%nat (3261819544195039)%Z 1%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfaea517d4cd6530)%Z true 8625771074381104%positive 57%nat (-539110692148819)%Z 4%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3f9e5dfe354938cf)%Z false 8547595698387151%positive 58%nat (8547595698387151)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3f5ee0ab1b7c4d87)%Z false 8691274806480263%positive 62%nat (8691274806480263)%Z 0%Z (-62)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0xbf836bf2b0d517f0)%Z true 5466714650515440%positive 59%nat (-341669665657215)%Z 4%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3f896f206e008ca6)%Z false 7159059492932774%positive 59%nat (3579529746466387)%Z 1%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc045961d44056b5e)%Z true 6076026950347614%positive 47%nat (-3038013475173807)%Z 1%Z (-46)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_50 _ _).
  all: seg_numeric.
Qed.

Lemma row_50 : nth (Z.to_nat (50%Z - 1)) atan2_segments [] = [(0x3fe538f57b89061f)%Z; (0xbc81bb74abda520c)%Z; (0x3fe3df1682b78014)%Z; (0xbc7074bea43ff610)%Z; (0xbfd347ecdb5be2e4)%Z; (0x3fb0fb5da3a11be4)%Z; (0x3fa72d3716819fbe)%Z; (0xbfaea517d4cd6530)%Z; (0x3f9e5dfe354938cf)%Z; (0x3f5ee0ab1b7c4d87)%Z; (0xbf836bf2b0d517f0)%Z; (0x3f896f206e008ca6)%Z; (0xc045961d44056b5e)%Z].
Proof. reflexivity. Qed.

Lemma fast_50 zh zl : finite zh -> finite zl -> / 128 <= B zh -> B zh <= 1 ->
  Znearest ne (B zh * 64) = 50%Z -> Rabs (B zl) <= bpow radix2 (-53) -> on_grid (-211) (B zl) ->
  exists h l, atan2_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    Rabs (B h + B l - atan (IZR 50 / 64 + ((B zh - IZR 50 / 64) + B zl))) <= bpow radix2 (-63) * atan (IZR 50 / 64 + ((B zh - IZR 50 / 64) + B zl)).
Proof.
  intros Fz Fl L U Hn Hl Hg.
  pose proof (series_segment_a zh zl 50%Z (IZR 1015 * bpow radix2 (-76)) ltac:(lia) Fz Fl L U Hn Hl Hg segok_50) as SS.
  cbv zeta in SS. rewrite row_50 in SS. cbn [nth] in SS.
  destruct SS as [h [l [Hs [Fh [Fl' [Nrm [Ht [e1 [ea [E1 [Eea Eq]]]]]]]]]]].
  exists h, l. split; [exact Hs | split; [exact Fh | split; [exact Fl' | split; [exact Nrm | ]]]].
  destruct (word_ok_intro (0x3fe538f57b89061f)%Z false 5973601501644319%positive 53%nat (5973601501644319)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc81bb74abda520c)%Z true 4991184377893388%positive 107%nat (-1247796094473347)%Z 2%Z (-105)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fe3df1682b78014)%Z false 5593312332840980%positive 53%nat (1398328083210245)%Z 2%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc7074bea43ff610)%Z true 4631961775633936%positive 108%nat (-289497610977121)%Z 4%Z (-104)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd347ecdb5be2e4)%Z true 5427107175588580%positive 54%nat (-1356776793897145)%Z 2%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fb0fb5da3a11be4)%Z false 4779979223145444%positive 56%nat (1194994805786361)%Z 2%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fa72d3716819fbe)%Z false 6523639088390078%positive 57%nat (3261819544195039)%Z 1%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfaea517d4cd6530)%Z true 8625771074381104%positive 57%nat (-539110692148819)%Z 4%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3f9e5dfe354938cf)%Z false 8547595698387151%positive 58%nat (8547595698387151)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3f5ee0ab1b7c4d87)%Z false 8691274806480263%positive 62%nat (8691274806480263)%Z 0%Z (-62)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0xbf836bf2b0d517f0)%Z true 5466714650515440%positive 59%nat (-341669665657215)%Z 4%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3f896f206e008ca6)%Z false 7159059492932774%positive 59%nat (3579529746466387)%Z 1%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc045961d44056b5e)%Z true 6076026950347614%positive 47%nat (-3038013475173807)%Z 1%Z (-46)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  unfold seg_poly in Eq.
  pose proof (approx_50 _ _ _ _ _ _ _ _ _ _ _ _ _ ((B zh - IZR 50 / 64) + B zl) V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 Ht) as AP.
  pose proof (amin_50 ((B zh - IZR 50 / 64) + B zl) Ht) as HAm.
  destruct ea_dw_small as [Ea0 Ea1].
  rewrite Eq.
  refine (fast_compose _ _ e1 ea (IZR 12732299 * bpow radix2 (-93)) (IZR 1015 * bpow radix2 (-76)) _ (IZR 690311 * bpow radix2 (-20)) _ AP E1 Eea HAm _ Ea0 _).
  - apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0].
  - bpow_num. replace (- prec)%Z with (-53)%Z by reflexivity. bpow_num. clear - Fz. interval with (i_prec 200).
Qed.

Lemma evalcert_51 : EvalCert (IZR (688619683205523) * bpow radix2 (-50)) (IZR (4013361591182189) * bpow radix2 (-106)) (IZR (-2684968966382353) * bpow radix2 (-53)) (IZR (4973476699341763) * bpow radix2 (-56)) (IZR (5865429184784175) * bpow radix2 (-57)) (IZR (-8224167544656023) * bpow radix2 (-57)) (IZR (1072231494973869) * bpow radix2 (-55)) (IZR (2414586273186287) * bpow radix2 (-65)) (IZR (-7873084848312895) * bpow radix2 (-59)) (IZR (6918327659366737) * bpow radix2 (-59)) (IZR (-3292311223734987) * bpow radix2 (-53)) (IZR 1004 * bpow radix2 (-76)) (IZR 579 * bpow radix2 (-73)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 251 (-251) (-74)); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_51.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_51.l1 th_ tl_ dg).
Qed.

Lemma segok_51 : SegOkRowA [(0x3fe587d81f732fbb)%Z; (0xbc75e5c9d8c5a950)%Z; (0x3fe3925e1cd28c98)%Z; (0x3c8c84431ffec6da)%Z; (0xbfd313ee1af2c622)%Z; (0x3fb1ab59c7f683c3)%Z; (0x3fa4d693a703a72f)%Z; (0xbfad37d639129097)%Z; (0x3f9e7982caffcd68)%Z; (0x3f11281b5a2f83de)%Z; (0xbf8bf88769ab923f)%Z; (0x3f88942eae938951)%Z; (0xbfd764ade1f62596)%Z] (IZR 1004 * bpow radix2 (-76)).
Proof.
  unfold SegOkRowA. cbn [nth].
  destruct (word_ok_intro (0x3fe587d81f732fbb)%Z false 6060336821252027%positive 53%nat (6060336821252027)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc75e5c9d8c5a950)%Z true 6163629598943568%positive 108%nat (-385226849933973)%Z 4%Z (-104)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fe3925e1cd28c98)%Z false 5508957465644184%positive 53%nat (688619683205523)%Z 3%Z (-50)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c8c84431ffec6da)%Z false 8026723182364378%positive 107%nat (4013361591182189)%Z 1%Z (-106)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd313ee1af2c622)%Z true 5369937932764706%positive 54%nat (-2684968966382353)%Z 1%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fb1ab59c7f683c3)%Z false 4973476699341763%positive 56%nat (4973476699341763)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fa4d693a703a72f)%Z false 5865429184784175%positive 57%nat (5865429184784175)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfad37d639129097)%Z true 8224167544656023%positive 57%nat (-8224167544656023)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3f9e7982caffcd68)%Z false 8577851959790952%positive 58%nat (1072231494973869)%Z 3%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3f11281b5a2f83de)%Z false 4829172546372574%positive 66%nat (2414586273186287)%Z 1%Z (-65)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0xbf8bf88769ab923f)%Z true 7873084848312895%positive 59%nat (-7873084848312895)%Z 0%Z (-59)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3f88942eae938951)%Z false 6918327659366737%positive 59%nat (6918327659366737)%Z 0%Z (-59)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xbfd764ade1f62596)%Z true 6584622447469974%positive 54%nat (-3292311223734987)%Z 1%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_51 _ _).
  all: seg_numeric.
Qed.

Lemma row_51 : nth (Z.to_nat (51%Z - 1)) atan2_segments [] = [(0x3fe587d81f732fbb)%Z; (0xbc75e5c9d8c5a950)%Z; (0x3fe3925e1cd28c98)%Z; (0x3c8c84431ffec6da)%Z; (0xbfd313ee1af2c622)%Z; (0x3fb1ab59c7f683c3)%Z; (0x3fa4d693a703a72f)%Z; (0xbfad37d639129097)%Z; (0x3f9e7982caffcd68)%Z; (0x3f11281b5a2f83de)%Z; (0xbf8bf88769ab923f)%Z; (0x3f88942eae938951)%Z; (0xbfd764ade1f62596)%Z].
Proof. reflexivity. Qed.

Lemma fast_51 zh zl : finite zh -> finite zl -> / 128 <= B zh -> B zh <= 1 ->
  Znearest ne (B zh * 64) = 51%Z -> Rabs (B zl) <= bpow radix2 (-53) -> on_grid (-211) (B zl) ->
  exists h l, atan2_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    Rabs (B h + B l - atan (IZR 51 / 64 + ((B zh - IZR 51 / 64) + B zl))) <= bpow radix2 (-63) * atan (IZR 51 / 64 + ((B zh - IZR 51 / 64) + B zl)).
Proof.
  intros Fz Fl L U Hn Hl Hg.
  pose proof (series_segment_a zh zl 51%Z (IZR 1004 * bpow radix2 (-76)) ltac:(lia) Fz Fl L U Hn Hl Hg segok_51) as SS.
  cbv zeta in SS. rewrite row_51 in SS. cbn [nth] in SS.
  destruct SS as [h [l [Hs [Fh [Fl' [Nrm [Ht [e1 [ea [E1 [Eea Eq]]]]]]]]]]].
  exists h, l. split; [exact Hs | split; [exact Fh | split; [exact Fl' | split; [exact Nrm | ]]]].
  destruct (word_ok_intro (0x3fe587d81f732fbb)%Z false 6060336821252027%positive 53%nat (6060336821252027)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc75e5c9d8c5a950)%Z true 6163629598943568%positive 108%nat (-385226849933973)%Z 4%Z (-104)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fe3925e1cd28c98)%Z false 5508957465644184%positive 53%nat (688619683205523)%Z 3%Z (-50)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c8c84431ffec6da)%Z false 8026723182364378%positive 107%nat (4013361591182189)%Z 1%Z (-106)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd313ee1af2c622)%Z true 5369937932764706%positive 54%nat (-2684968966382353)%Z 1%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fb1ab59c7f683c3)%Z false 4973476699341763%positive 56%nat (4973476699341763)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fa4d693a703a72f)%Z false 5865429184784175%positive 57%nat (5865429184784175)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfad37d639129097)%Z true 8224167544656023%positive 57%nat (-8224167544656023)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3f9e7982caffcd68)%Z false 8577851959790952%positive 58%nat (1072231494973869)%Z 3%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3f11281b5a2f83de)%Z false 4829172546372574%positive 66%nat (2414586273186287)%Z 1%Z (-65)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0xbf8bf88769ab923f)%Z true 7873084848312895%positive 59%nat (-7873084848312895)%Z 0%Z (-59)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3f88942eae938951)%Z false 6918327659366737%positive 59%nat (6918327659366737)%Z 0%Z (-59)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xbfd764ade1f62596)%Z true 6584622447469974%positive 54%nat (-3292311223734987)%Z 1%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  unfold seg_poly in Eq.
  pose proof (approx_51 _ _ _ _ _ _ _ _ _ _ _ _ _ ((B zh - IZR 51 / 64) + B zl) V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 Ht) as AP.
  pose proof (amin_51 ((B zh - IZR 51 / 64) + B zl) Ht) as HAm.
  destruct ea_dw_small as [Ea0 Ea1].
  rewrite Eq.
  refine (fast_compose _ _ e1 ea (IZR 13683936 * bpow radix2 (-100)) (IZR 1004 * bpow radix2 (-76)) _ (IZR 700485 * bpow radix2 (-20)) _ AP E1 Eea HAm _ Ea0 _).
  - apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0].
  - bpow_num. replace (- prec)%Z with (-53)%Z by reflexivity. bpow_num. clear - Fz. interval with (i_prec 200).
Qed.

Lemma evalcert_52 : EvalCert (IZR (2712756481427875) * bpow radix2 (-52)) (IZR (8562137644506731) * bpow radix2 (-107)) (IZR (-2655309873585873) * bpow radix2 (-53)) (IZR (5146895663261957) * bpow radix2 (-56)) (IZR (5238615828165271) * bpow radix2 (-57)) (IZR (-7822441636681259) * bpow radix2 (-57)) (IZR (1069257584260849) * bpow radix2 (-55)) (IZR (-7127654002238925) * bpow radix2 (-62)) (IZR (-5048230466988991) * bpow radix2 (-58)) (IZR (6433231581616853) * bpow radix2 (-59)) (IZR (5565162350788601) * bpow radix2 (-47)) (IZR 993 * bpow radix2 (-76)) (IZR 598 * bpow radix2 (-73)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 993 (-993) (-76)); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_52.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_52.l1 th_ tl_ dg).
Qed.

Lemma segok_52 : SegOkRowA [(0x3fe5d58987169b18)%Z; (0x3c60028e4bc5e7ca)%Z; (0x3fe34679ace01346)%Z; (0x3c8e6b3804d19e6b)%Z; (0xbfd2ddfb03913da2)%Z; (0x3fb2491307b46905)%Z; (0x3fa29c7e4b8d7297)%Z; (0xbfabca781f07d62b)%Z; (0x3f9e63df73ddb788)%Z; (0xbf59529044e2a5cd)%Z; (0xbf91ef56bfbaabbf)%Z; (0x3f86dafd732e1ad5)%Z; (0x4043c57c55093ff9)%Z] (IZR 993 * bpow radix2 (-76)).
Proof.
  unfold SegOkRowA. cbn [nth].
  destruct (word_ok_intro (0x3fe5d58987169b18)%Z false 6145761164565272%positive 53%nat (768220145570659)%Z 3%Z (-50)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c60028e4bc5e7ca)%Z false 4506409807243210%positive 109%nat (2253204903621605)%Z 1%Z (-108)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fe34679ace01346)%Z false 5425512962855750%positive 53%nat (2712756481427875)%Z 1%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c8e6b3804d19e6b)%Z false 8562137644506731%positive 107%nat (8562137644506731)%Z 0%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd2ddfb03913da2)%Z true 5310619747171746%positive 54%nat (-2655309873585873)%Z 1%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fb2491307b46905)%Z false 5146895663261957%positive 56%nat (5146895663261957)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fa29c7e4b8d7297)%Z false 5238615828165271%positive 57%nat (5238615828165271)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfabca781f07d62b)%Z true 7822441636681259%positive 57%nat (-7822441636681259)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3f9e63df73ddb788)%Z false 8554060674086792%positive 58%nat (1069257584260849)%Z 3%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0xbf59529044e2a5cd)%Z true 7127654002238925%positive 62%nat (-7127654002238925)%Z 0%Z (-62)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0xbf91ef56bfbaabbf)%Z true 5048230466988991%positive 58%nat (-5048230466988991)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3f86dafd732e1ad5)%Z false 6433231581616853%positive 59%nat (6433231581616853)%Z 0%Z (-59)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x4043c57c55093ff9)%Z false 5565162350788601%positive 47%nat (5565162350788601)%Z 0%Z (-47)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_52 _ _).
  all: seg_numeric.
Qed.

Lemma row_52 : nth (Z.to_nat (52%Z - 1)) atan2_segments [] = [(0x3fe5d58987169b18)%Z; (0x3c60028e4bc5e7ca)%Z; (0x3fe34679ace01346)%Z; (0x3c8e6b3804d19e6b)%Z; (0xbfd2ddfb03913da2)%Z; (0x3fb2491307b46905)%Z; (0x3fa29c7e4b8d7297)%Z; (0xbfabca781f07d62b)%Z; (0x3f9e63df73ddb788)%Z; (0xbf59529044e2a5cd)%Z; (0xbf91ef56bfbaabbf)%Z; (0x3f86dafd732e1ad5)%Z; (0x4043c57c55093ff9)%Z].
Proof. reflexivity. Qed.

Lemma fast_52 zh zl : finite zh -> finite zl -> / 128 <= B zh -> B zh <= 1 ->
  Znearest ne (B zh * 64) = 52%Z -> Rabs (B zl) <= bpow radix2 (-53) -> on_grid (-211) (B zl) ->
  exists h l, atan2_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    Rabs (B h + B l - atan (IZR 52 / 64 + ((B zh - IZR 52 / 64) + B zl))) <= bpow radix2 (-63) * atan (IZR 52 / 64 + ((B zh - IZR 52 / 64) + B zl)).
Proof.
  intros Fz Fl L U Hn Hl Hg.
  pose proof (series_segment_a zh zl 52%Z (IZR 993 * bpow radix2 (-76)) ltac:(lia) Fz Fl L U Hn Hl Hg segok_52) as SS.
  cbv zeta in SS. rewrite row_52 in SS. cbn [nth] in SS.
  destruct SS as [h [l [Hs [Fh [Fl' [Nrm [Ht [e1 [ea [E1 [Eea Eq]]]]]]]]]]].
  exists h, l. split; [exact Hs | split; [exact Fh | split; [exact Fl' | split; [exact Nrm | ]]]].
  destruct (word_ok_intro (0x3fe5d58987169b18)%Z false 6145761164565272%positive 53%nat (768220145570659)%Z 3%Z (-50)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c60028e4bc5e7ca)%Z false 4506409807243210%positive 109%nat (2253204903621605)%Z 1%Z (-108)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fe34679ace01346)%Z false 5425512962855750%positive 53%nat (2712756481427875)%Z 1%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c8e6b3804d19e6b)%Z false 8562137644506731%positive 107%nat (8562137644506731)%Z 0%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd2ddfb03913da2)%Z true 5310619747171746%positive 54%nat (-2655309873585873)%Z 1%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fb2491307b46905)%Z false 5146895663261957%positive 56%nat (5146895663261957)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fa29c7e4b8d7297)%Z false 5238615828165271%positive 57%nat (5238615828165271)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfabca781f07d62b)%Z true 7822441636681259%positive 57%nat (-7822441636681259)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3f9e63df73ddb788)%Z false 8554060674086792%positive 58%nat (1069257584260849)%Z 3%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0xbf59529044e2a5cd)%Z true 7127654002238925%positive 62%nat (-7127654002238925)%Z 0%Z (-62)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0xbf91ef56bfbaabbf)%Z true 5048230466988991%positive 58%nat (-5048230466988991)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3f86dafd732e1ad5)%Z false 6433231581616853%positive 59%nat (6433231581616853)%Z 0%Z (-59)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x4043c57c55093ff9)%Z false 5565162350788601%positive 47%nat (5565162350788601)%Z 0%Z (-47)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  unfold seg_poly in Eq.
  pose proof (approx_52 _ _ _ _ _ _ _ _ _ _ _ _ _ ((B zh - IZR 52 / 64) + B zl) V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 Ht) as AP.
  pose proof (amin_52 ((B zh - IZR 52 / 64) + B zl) Ht) as HAm.
  destruct ea_dw_small as [Ea0 Ea1].
  rewrite Eq.
  refine (fast_compose _ _ e1 ea (IZR 11663217 * bpow radix2 (-93)) (IZR 993 * bpow radix2 (-76)) _ (IZR 710506 * bpow radix2 (-20)) _ AP E1 Eea HAm _ Ea0 _).
  - apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0].
  - bpow_num. replace (- prec)%Z with (-53)%Z by reflexivity. bpow_num. clear - Fz. interval with (i_prec 200).
Qed.

Lemma evalcert_53 : EvalCert (IZR (667876324174857) * bpow radix2 (-50)) (IZR (3328946053309053) * bpow radix2 (-106)) (IZR (-1312345541839893) * bpow radix2 (-52)) (IZR (2650608203293385) * bpow radix2 (-55)) (IZR (4643113581740843) * bpow radix2 (-57)) (IZR (-7422975366863135) * bpow radix2 (-57)) (IZR (4241193961993313) * bpow radix2 (-57)) (IZR (-6823344078719893) * bpow radix2 (-61)) (IZR (-8415898924360067) * bpow radix2 (-61)) (IZR (6111656105948003) * bpow radix2 (-59)) (IZR (-110487388830921) * bpow radix2 (-41)) (IZR 982 * bpow radix2 (-76)) (IZR 615 * bpow radix2 (-73)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 491 (-491) (-75)); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_53.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_53.l1 th_ tl_ dg).
Qed.

Lemma segok_53 : SegOkRowA [(0x3fe6220d115d7b8e)%Z; (0xbc62b785350ee8c1)%Z; (0x3fe2fb7098736048)%Z; (0x3c87a7514df7c4fa)%Z; (0xbfd2a64907603054)%Z; (0x3fb2d56da0cac592)%Z; (0x3fa07ee31fb1032b)%Z; (0xbfaa5f2821eb191f)%Z; (0x3f9e22afd70e68c2)%Z; (0xbf683dcb97fe0b95)%Z; (0xbf6de63729da2183)%Z; (0x3f85b684d32f3363)%Z; (0xc0491f36640f3240)%Z] (IZR 982 * bpow radix2 (-76)).
Proof.
  unfold SegOkRowA. cbn [nth].
  destruct (word_ok_intro (0x3fe6220d115d7b8e)%Z false 6229889008892814%positive 53%nat (3114944504446407)%Z 1%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc62b785350ee8c1)%Z true 5268332329494721%positive 109%nat (-5268332329494721)%Z 0%Z (-109)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fe2fb7098736048)%Z false 5343010593398856%positive 53%nat (667876324174857)%Z 3%Z (-50)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c87a7514df7c4fa)%Z false 6657892106618106%positive 107%nat (3328946053309053)%Z 1%Z (-106)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd2a64907603054)%Z true 5249382167359572%positive 54%nat (-1312345541839893)%Z 2%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fb2d56da0cac592)%Z false 5301216406586770%positive 56%nat (2650608203293385)%Z 1%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fa07ee31fb1032b)%Z false 4643113581740843%positive 57%nat (4643113581740843)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfaa5f2821eb191f)%Z true 7422975366863135%positive 57%nat (-7422975366863135)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3f9e22afd70e68c2)%Z false 8482387923986626%positive 58%nat (4241193961993313)%Z 1%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0xbf683dcb97fe0b95)%Z true 6823344078719893%positive 61%nat (-6823344078719893)%Z 0%Z (-61)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0xbf6de63729da2183)%Z true 8415898924360067%positive 61%nat (-8415898924360067)%Z 0%Z (-61)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3f85b684d32f3363)%Z false 6111656105948003%positive 59%nat (6111656105948003)%Z 0%Z (-59)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc0491f36640f3240)%Z true 7071192885178944%positive 47%nat (-110487388830921)%Z 6%Z (-41)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_53 _ _).
  all: seg_numeric.
Qed.

Lemma row_53 : nth (Z.to_nat (53%Z - 1)) atan2_segments [] = [(0x3fe6220d115d7b8e)%Z; (0xbc62b785350ee8c1)%Z; (0x3fe2fb7098736048)%Z; (0x3c87a7514df7c4fa)%Z; (0xbfd2a64907603054)%Z; (0x3fb2d56da0cac592)%Z; (0x3fa07ee31fb1032b)%Z; (0xbfaa5f2821eb191f)%Z; (0x3f9e22afd70e68c2)%Z; (0xbf683dcb97fe0b95)%Z; (0xbf6de63729da2183)%Z; (0x3f85b684d32f3363)%Z; (0xc0491f36640f3240)%Z].
Proof. reflexivity. Qed.

Lemma fast_53 zh zl : finite zh -> finite zl -> / 128 <= B zh -> B zh <= 1 ->
  Znearest ne (B zh * 64) = 53%Z -> Rabs (B zl) <= bpow radix2 (-53) -> on_grid (-211) (B zl) ->
  exists h l, atan2_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    Rabs (B h + B l - atan (IZR 53 / 64 + ((B zh - IZR 53 / 64) + B zl))) <= bpow radix2 (-63) * atan (IZR 53 / 64 + ((B zh - IZR 53 / 64) + B zl)).
Proof.
  intros Fz Fl L U Hn Hl Hg.
  pose proof (series_segment_a zh zl 53%Z (IZR 982 * bpow radix2 (-76)) ltac:(lia) Fz Fl L U Hn Hl Hg segok_53) as SS.
  cbv zeta in SS. rewrite row_53 in SS. cbn [nth] in SS.
  destruct SS as [h [l [Hs [Fh [Fl' [Nrm [Ht [e1 [ea [E1 [Eea Eq]]]]]]]]]]].
  exists h, l. split; [exact Hs | split; [exact Fh | split; [exact Fl' | split; [exact Nrm | ]]]].
  destruct (word_ok_intro (0x3fe6220d115d7b8e)%Z false 6229889008892814%positive 53%nat (3114944504446407)%Z 1%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc62b785350ee8c1)%Z true 5268332329494721%positive 109%nat (-5268332329494721)%Z 0%Z (-109)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fe2fb7098736048)%Z false 5343010593398856%positive 53%nat (667876324174857)%Z 3%Z (-50)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c87a7514df7c4fa)%Z false 6657892106618106%positive 107%nat (3328946053309053)%Z 1%Z (-106)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd2a64907603054)%Z true 5249382167359572%positive 54%nat (-1312345541839893)%Z 2%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fb2d56da0cac592)%Z false 5301216406586770%positive 56%nat (2650608203293385)%Z 1%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fa07ee31fb1032b)%Z false 4643113581740843%positive 57%nat (4643113581740843)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfaa5f2821eb191f)%Z true 7422975366863135%positive 57%nat (-7422975366863135)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3f9e22afd70e68c2)%Z false 8482387923986626%positive 58%nat (4241193961993313)%Z 1%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0xbf683dcb97fe0b95)%Z true 6823344078719893%positive 61%nat (-6823344078719893)%Z 0%Z (-61)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0xbf6de63729da2183)%Z true 8415898924360067%positive 61%nat (-8415898924360067)%Z 0%Z (-61)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3f85b684d32f3363)%Z false 6111656105948003%positive 59%nat (6111656105948003)%Z 0%Z (-59)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc0491f36640f3240)%Z true 7071192885178944%positive 47%nat (-110487388830921)%Z 6%Z (-41)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  unfold seg_poly in Eq.
  pose proof (approx_53 _ _ _ _ _ _ _ _ _ _ _ _ _ ((B zh - IZR 53 / 64) + B zl) V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 Ht) as AP.
  pose proof (amin_53 ((B zh - IZR 53 / 64) + B zl) Ht) as HAm.
  destruct ea_dw_small as [Ea0 Ea1].
  rewrite Eq.
  refine (fast_compose _ _ e1 ea (IZR 14815452 * bpow radix2 (-93)) (IZR 982 * bpow radix2 (-76)) _ (IZR 720375 * bpow radix2 (-20)) _ AP E1 Eea HAm _ Ea0 _).
  - apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0].
  - bpow_num. replace (- prec)%Z with (-53)%Z by reflexivity. bpow_num. clear - Fz. interval with (i_prec 200).
Qed.

Lemma evalcert_54 : EvalCert (IZR (2630739314562115) * bpow radix2 (-52)) (IZR (3175384563280053) * bpow radix2 (-106)) (IZR (-2593221640366991) * bpow radix2 (-53)) (IZR (5437413763658655) * bpow radix2 (-56)) (IZR (8157324818227897) * bpow radix2 (-58)) (IZR (-1756964767034003) * bpow radix2 (-55)) (IZR (8369320334277773) * bpow radix2 (-58)) (IZR (-2413557268014829) * bpow radix2 (-59)) (IZR (-3212029812708333) * bpow radix2 (-59)) (IZR (2890722755552297) * bpow radix2 (-58)) (IZR (-3626703077478287) * bpow radix2 (-47)) (IZR 970 * bpow radix2 (-76)) (IZR 630 * bpow radix2 (-73)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 485 (-485) (-75)); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_54.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_54.l1 th_ tl_ dg).
Qed.

Lemma segok_54 : SegOkRowA [(0x3fe66d663923e087)%Z; (0xbc76ea6febe8bbba)%Z; (0x3fe2b14974aea886)%Z; (0x3c868ffda9d6d16a)%Z; (0xbfd26d0aed65571e)%Z; (0x3fb3514c8be1339f)%Z; (0x3f9cfb0b301ba2b9)%Z; (0xbfa8f7ccf349aa4c)%Z; (0x3f9dbbda3d893c8d)%Z; (0xbf71263c2f35cdda)%Z; (0xbf76d2a5effd27da)%Z; (0x3f848a31adfa4852)%Z; (0xc039c4ef39471f1e)%Z] (IZR 970 * bpow radix2 (-76)).
Proof.
  unfold SegOkRowA. cbn [nth].
  destruct (word_ok_intro (0x3fe66d663923e087)%Z false 6312735300378759%positive 53%nat (6312735300378759)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc76ea6febe8bbba)%Z true 6450215907802042%positive 108%nat (-3225107953901021)%Z 1%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fe2b14974aea886)%Z false 5261478629124230%positive 53%nat (2630739314562115)%Z 1%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c868ffda9d6d16a)%Z false 6350769126560106%positive 107%nat (3175384563280053)%Z 1%Z (-106)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd26d0aed65571e)%Z true 5186443280733982%positive 54%nat (-2593221640366991)%Z 1%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fb3514c8be1339f)%Z false 5437413763658655%positive 56%nat (5437413763658655)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3f9cfb0b301ba2b9)%Z false 8157324818227897%positive 58%nat (8157324818227897)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfa8f7ccf349aa4c)%Z true 7027859068136012%positive 57%nat (-1756964767034003)%Z 2%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3f9dbbda3d893c8d)%Z false 8369320334277773%positive 58%nat (8369320334277773)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0xbf71263c2f35cdda)%Z true 4827114536029658%positive 60%nat (-2413557268014829)%Z 1%Z (-59)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0xbf76d2a5effd27da)%Z true 6424059625416666%positive 60%nat (-3212029812708333)%Z 1%Z (-59)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3f848a31adfa4852)%Z false 5781445511104594%positive 59%nat (2890722755552297)%Z 1%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc039c4ef39471f1e)%Z true 7253406154956574%positive 48%nat (-3626703077478287)%Z 1%Z (-47)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_54 _ _).
  all: seg_numeric.
Qed.

Lemma row_54 : nth (Z.to_nat (54%Z - 1)) atan2_segments [] = [(0x3fe66d663923e087)%Z; (0xbc76ea6febe8bbba)%Z; (0x3fe2b14974aea886)%Z; (0x3c868ffda9d6d16a)%Z; (0xbfd26d0aed65571e)%Z; (0x3fb3514c8be1339f)%Z; (0x3f9cfb0b301ba2b9)%Z; (0xbfa8f7ccf349aa4c)%Z; (0x3f9dbbda3d893c8d)%Z; (0xbf71263c2f35cdda)%Z; (0xbf76d2a5effd27da)%Z; (0x3f848a31adfa4852)%Z; (0xc039c4ef39471f1e)%Z].
Proof. reflexivity. Qed.

Lemma fast_54 zh zl : finite zh -> finite zl -> / 128 <= B zh -> B zh <= 1 ->
  Znearest ne (B zh * 64) = 54%Z -> Rabs (B zl) <= bpow radix2 (-53) -> on_grid (-211) (B zl) ->
  exists h l, atan2_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    Rabs (B h + B l - atan (IZR 54 / 64 + ((B zh - IZR 54 / 64) + B zl))) <= bpow radix2 (-63) * atan (IZR 54 / 64 + ((B zh - IZR 54 / 64) + B zl)).
Proof.
  intros Fz Fl L U Hn Hl Hg.
  pose proof (series_segment_a zh zl 54%Z (IZR 970 * bpow radix2 (-76)) ltac:(lia) Fz Fl L U Hn Hl Hg segok_54) as SS.
  cbv zeta in SS. rewrite row_54 in SS. cbn [nth] in SS.
  destruct SS as [h [l [Hs [Fh [Fl' [Nrm [Ht [e1 [ea [E1 [Eea Eq]]]]]]]]]]].
  exists h, l. split; [exact Hs | split; [exact Fh | split; [exact Fl' | split; [exact Nrm | ]]]].
  destruct (word_ok_intro (0x3fe66d663923e087)%Z false 6312735300378759%positive 53%nat (6312735300378759)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc76ea6febe8bbba)%Z true 6450215907802042%positive 108%nat (-3225107953901021)%Z 1%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fe2b14974aea886)%Z false 5261478629124230%positive 53%nat (2630739314562115)%Z 1%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c868ffda9d6d16a)%Z false 6350769126560106%positive 107%nat (3175384563280053)%Z 1%Z (-106)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd26d0aed65571e)%Z true 5186443280733982%positive 54%nat (-2593221640366991)%Z 1%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fb3514c8be1339f)%Z false 5437413763658655%positive 56%nat (5437413763658655)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3f9cfb0b301ba2b9)%Z false 8157324818227897%positive 58%nat (8157324818227897)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfa8f7ccf349aa4c)%Z true 7027859068136012%positive 57%nat (-1756964767034003)%Z 2%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3f9dbbda3d893c8d)%Z false 8369320334277773%positive 58%nat (8369320334277773)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0xbf71263c2f35cdda)%Z true 4827114536029658%positive 60%nat (-2413557268014829)%Z 1%Z (-59)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0xbf76d2a5effd27da)%Z true 6424059625416666%positive 60%nat (-3212029812708333)%Z 1%Z (-59)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3f848a31adfa4852)%Z false 5781445511104594%positive 59%nat (2890722755552297)%Z 1%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc039c4ef39471f1e)%Z true 7253406154956574%positive 48%nat (-3626703077478287)%Z 1%Z (-47)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  unfold seg_poly in Eq.
  pose proof (approx_54 _ _ _ _ _ _ _ _ _ _ _ _ _ ((B zh - IZR 54 / 64) + B zl) V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 Ht) as AP.
  pose proof (amin_54 ((B zh - IZR 54 / 64) + B zl) Ht) as HAm.
  destruct ea_dw_small as [Ea0 Ea1].
  rewrite Eq.
  refine (fast_compose _ _ e1 ea (IZR 15191324 * bpow radix2 (-94)) (IZR 970 * bpow radix2 (-76)) _ (IZR 730094 * bpow radix2 (-20)) _ AP E1 Eea HAm _ Ea0 _).
  - apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0].
  - bpow_num. replace (- prec)%Z with (-53)%Z by reflexivity. bpow_num. clear - Fz. interval with (i_prec 200).
Qed.

Lemma evalcert_55 : EvalCert (IZR (2590471011614879) * bpow radix2 (-52)) (IZR (-2204683092404655) * bpow radix2 (-105)) (IZR (-1280502452027015) * bpow radix2 (-52)) (IZR (1389113001163849) * bpow radix2 (-54)) (IZR (3544849814781553) * bpow radix2 (-57)) (IZR (-3319454223197253) * bpow radix2 (-56)) (IZR (2055063399683967) * bpow radix2 (-56)) (IZR (-6042229856357037) * bpow radix2 (-60)) (IZR (-2898052765663245) * bpow radix2 (-60)) (IZR (5287884802235469) * bpow radix2 (-59)) (IZR (-336925577819375) * bpow radix2 (-43)) (IZR 958 * bpow radix2 (-76)) (IZR 644 * bpow radix2 (-73)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 479 (-479) (-75)); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_55.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_55.l1 th_ tl_ dg).
Qed.

Lemma segok_55 : SegOkRowA [(0x3fe6b798920b3d99)%Z; (0xbc8a80386188c50e)%Z; (0x3fe2680a10e5813e)%Z; (0xbc8f54972242a6bc)%Z; (0xbfd23270d725fa1c)%Z; (0x3fb3bd904bf2f124)%Z; (0x3f99300b53fbfce2)%Z; (0xbfa7960d53a4c88a)%Z; (0x3f9d3446efb75dfc)%Z; (0xbf757760443d4aad)%Z; (0xbf649786fb46801a)%Z; (0x3f82c94d9f401c4d)%Z; (0xc04326e9961b4ef0)%Z] (IZR 958 * bpow radix2 (-76)).
Proof.
  unfold SegOkRowA. cbn [nth].
  destruct (word_ok_intro (0x3fe6b798920b3d99)%Z false 6394315400756633%positive 53%nat (6394315400756633)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc8a80386188c50e)%Z true 7459329037354254%positive 107%nat (-3729664518677127)%Z 1%Z (-106)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fe2680a10e5813e)%Z false 5180942023229758%positive 53%nat (2590471011614879)%Z 1%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc8f54972242a6bc)%Z true 8818732369618620%positive 107%nat (-2204683092404655)%Z 2%Z (-105)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd23270d725fa1c)%Z true 5122009808108060%positive 54%nat (-1280502452027015)%Z 2%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fb3bd904bf2f124)%Z false 5556452004655396%positive 56%nat (1389113001163849)%Z 2%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3f99300b53fbfce2)%Z false 7089699629563106%positive 58%nat (3544849814781553)%Z 1%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfa7960d53a4c88a)%Z true 6638908446394506%positive 57%nat (-3319454223197253)%Z 1%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3f9d3446efb75dfc)%Z false 8220253598735868%positive 58%nat (2055063399683967)%Z 2%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0xbf757760443d4aad)%Z true 6042229856357037%positive 60%nat (-6042229856357037)%Z 0%Z (-60)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0xbf649786fb46801a)%Z true 5796105531326490%positive 61%nat (-2898052765663245)%Z 1%Z (-60)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3f82c94d9f401c4d)%Z false 5287884802235469%positive 59%nat (5287884802235469)%Z 0%Z (-59)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc04326e9961b4ef0)%Z true 5390809245110000%positive 47%nat (-336925577819375)%Z 4%Z (-43)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_55 _ _).
  all: seg_numeric.
Qed.

Lemma row_55 : nth (Z.to_nat (55%Z - 1)) atan2_segments [] = [(0x3fe6b798920b3d99)%Z; (0xbc8a80386188c50e)%Z; (0x3fe2680a10e5813e)%Z; (0xbc8f54972242a6bc)%Z; (0xbfd23270d725fa1c)%Z; (0x3fb3bd904bf2f124)%Z; (0x3f99300b53fbfce2)%Z; (0xbfa7960d53a4c88a)%Z; (0x3f9d3446efb75dfc)%Z; (0xbf757760443d4aad)%Z; (0xbf649786fb46801a)%Z; (0x3f82c94d9f401c4d)%Z; (0xc04326e9961b4ef0)%Z].
Proof. reflexivity. Qed.

Lemma fast_55 zh zl : finite zh -> finite zl -> / 128 <= B zh -> B zh <= 1 ->
  Znearest ne (B zh * 64) = 55%Z -> Rabs (B zl) <= bpow radix2 (-53) -> on_grid (-211) (B zl) ->
  exists h l, atan2_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    Rabs (B h + B l - atan (IZR 55 / 64 + ((B zh - IZR 55 / 64) + B zl))) <= bpow radix2 (-63) * atan (IZR 55 / 64 + ((B zh - IZR 55 / 64) + B zl)).
Proof.
  intros Fz Fl L U Hn Hl Hg.
  pose proof (series_segment_a zh zl 55%Z (IZR 958 * bpow radix2 (-76)) ltac:(lia) Fz Fl L U Hn Hl Hg segok_55) as SS.
  cbv zeta in SS. rewrite row_55 in SS. cbn [nth] in SS.
  destruct SS as [h [l [Hs [Fh [Fl' [Nrm [Ht [e1 [ea [E1 [Eea Eq]]]]]]]]]]].
  exists h, l. split; [exact Hs | split; [exact Fh | split; [exact Fl' | split; [exact Nrm | ]]]].
  destruct (word_ok_intro (0x3fe6b798920b3d99)%Z false 6394315400756633%positive 53%nat (6394315400756633)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc8a80386188c50e)%Z true 7459329037354254%positive 107%nat (-3729664518677127)%Z 1%Z (-106)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fe2680a10e5813e)%Z false 5180942023229758%positive 53%nat (2590471011614879)%Z 1%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc8f54972242a6bc)%Z true 8818732369618620%positive 107%nat (-2204683092404655)%Z 2%Z (-105)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd23270d725fa1c)%Z true 5122009808108060%positive 54%nat (-1280502452027015)%Z 2%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fb3bd904bf2f124)%Z false 5556452004655396%positive 56%nat (1389113001163849)%Z 2%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3f99300b53fbfce2)%Z false 7089699629563106%positive 58%nat (3544849814781553)%Z 1%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfa7960d53a4c88a)%Z true 6638908446394506%positive 57%nat (-3319454223197253)%Z 1%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3f9d3446efb75dfc)%Z false 8220253598735868%positive 58%nat (2055063399683967)%Z 2%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0xbf757760443d4aad)%Z true 6042229856357037%positive 60%nat (-6042229856357037)%Z 0%Z (-60)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0xbf649786fb46801a)%Z true 5796105531326490%positive 61%nat (-2898052765663245)%Z 1%Z (-60)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3f82c94d9f401c4d)%Z false 5287884802235469%positive 59%nat (5287884802235469)%Z 0%Z (-59)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc04326e9961b4ef0)%Z true 5390809245110000%positive 47%nat (-336925577819375)%Z 4%Z (-43)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  unfold seg_poly in Eq.
  pose proof (approx_55 _ _ _ _ _ _ _ _ _ _ _ _ _ ((B zh - IZR 55 / 64) + B zl) V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 Ht) as AP.
  pose proof (amin_55 ((B zh - IZR 55 / 64) + B zl) Ht) as HAm.
  destruct ea_dw_small as [Ea0 Ea1].
  rewrite Eq.
  refine (fast_compose _ _ e1 ea (IZR 11244851 * bpow radix2 (-93)) (IZR 958 * bpow radix2 (-76)) _ (IZR 739664 * bpow radix2 (-20)) _ AP E1 Eea HAm _ Ea0 _).
  - apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0].
  - bpow_num. replace (- prec)%Z with (-53)%Z by reflexivity. bpow_num. clear - Fz. interval with (i_prec 200).
Qed.

Lemma evalcert_56 : EvalCert (IZR (637677823344495) * bpow radix2 (-50)) (IZR (637677823344495) * bpow radix2 (-106)) (IZR (-5056277254129801) * bpow radix2 (-54)) (IZR (5659280399059735) * bpow radix2 (-56)) (IZR (6082263185647287) * bpow radix2 (-58)) (IZR (-6257682525482809) * bpow radix2 (-57)) (IZR (251270444150211) * bpow radix2 (-53)) (IZR (-883936010651981) * bpow radix2 (-57)) (IZR (-154925292062993) * bpow radix2 (-54)) (IZR (615355225880723) * bpow radix2 (-56)) (IZR (4242324216567599) * bpow radix2 (-48)) (IZR 946 * bpow radix2 (-76)) (IZR 655 * bpow radix2 (-73)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 473 (-473) (-75)); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_56.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_56.l1 th_ tl_ dg).
Qed.

Lemma segok_56 : SegOkRowA [(0x3fe700a7c5784634)%Z; (0xbc78c34d25aadef6)%Z; (0x3fe21fb78121fb78)%Z; (0x3c621fb78121fb78)%Z; (0xbfd1f6a8499e4889)%Z; (0x3fb41b15e5decb17)%Z; (0x3f959bc9409c66b7)%Z; (0xbfa63b54400c6f39)%Z; (0x3f9c90eeb21db860)%Z; (0xbf791f7b1f5a4a68)%Z; (0xbf819ceb60012220)%Z; (0x3f817d4c6d31c498)%Z; (0x402e24be27e6ae5e)%Z] (IZR 946 * bpow radix2 (-76)).
Proof.
  unfold SegOkRowA. cbn [nth].
  destruct (word_ok_intro (0x3fe700a7c5784634)%Z false 6474645036877364%positive 53%nat (1618661259219341)%Z 2%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc78c34d25aadef6)%Z true 6970135552909046%positive 108%nat (-3485067776454523)%Z 1%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fe21fb78121fb78)%Z false 5101422586755960%positive 53%nat (637677823344495)%Z 3%Z (-50)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c621fb78121fb78)%Z false 5101422586755960%positive 109%nat (637677823344495)%Z 3%Z (-106)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd1f6a8499e4889)%Z true 5056277254129801%positive 54%nat (-5056277254129801)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fb41b15e5decb17)%Z false 5659280399059735%positive 56%nat (5659280399059735)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3f959bc9409c66b7)%Z false 6082263185647287%positive 58%nat (6082263185647287)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfa63b54400c6f39)%Z true 6257682525482809%positive 57%nat (-6257682525482809)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3f9c90eeb21db860)%Z false 8040654212806752%positive 58%nat (251270444150211)%Z 5%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0xbf791f7b1f5a4a68)%Z true 7071488085215848%positive 60%nat (-883936010651981)%Z 3%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0xbf819ceb60012220)%Z true 4957609346015776%positive 59%nat (-154925292062993)%Z 5%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3f817d4c6d31c498)%Z false 4922841807045784%positive 59%nat (615355225880723)%Z 3%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x402e24be27e6ae5e)%Z false 8484648433135198%positive 49%nat (4242324216567599)%Z 1%Z (-48)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_56 _ _).
  all: seg_numeric.
Qed.

Lemma row_56 : nth (Z.to_nat (56%Z - 1)) atan2_segments [] = [(0x3fe700a7c5784634)%Z; (0xbc78c34d25aadef6)%Z; (0x3fe21fb78121fb78)%Z; (0x3c621fb78121fb78)%Z; (0xbfd1f6a8499e4889)%Z; (0x3fb41b15e5decb17)%Z; (0x3f959bc9409c66b7)%Z; (0xbfa63b54400c6f39)%Z; (0x3f9c90eeb21db860)%Z; (0xbf791f7b1f5a4a68)%Z; (0xbf819ceb60012220)%Z; (0x3f817d4c6d31c498)%Z; (0x402e24be27e6ae5e)%Z].
Proof. reflexivity. Qed.

Lemma fast_56 zh zl : finite zh -> finite zl -> / 128 <= B zh -> B zh <= 1 ->
  Znearest ne (B zh * 64) = 56%Z -> Rabs (B zl) <= bpow radix2 (-53) -> on_grid (-211) (B zl) ->
  exists h l, atan2_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    Rabs (B h + B l - atan (IZR 56 / 64 + ((B zh - IZR 56 / 64) + B zl))) <= bpow radix2 (-63) * atan (IZR 56 / 64 + ((B zh - IZR 56 / 64) + B zl)).
Proof.
  intros Fz Fl L U Hn Hl Hg.
  pose proof (series_segment_a zh zl 56%Z (IZR 946 * bpow radix2 (-76)) ltac:(lia) Fz Fl L U Hn Hl Hg segok_56) as SS.
  cbv zeta in SS. rewrite row_56 in SS. cbn [nth] in SS.
  destruct SS as [h [l [Hs [Fh [Fl' [Nrm [Ht [e1 [ea [E1 [Eea Eq]]]]]]]]]]].
  exists h, l. split; [exact Hs | split; [exact Fh | split; [exact Fl' | split; [exact Nrm | ]]]].
  destruct (word_ok_intro (0x3fe700a7c5784634)%Z false 6474645036877364%positive 53%nat (1618661259219341)%Z 2%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc78c34d25aadef6)%Z true 6970135552909046%positive 108%nat (-3485067776454523)%Z 1%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fe21fb78121fb78)%Z false 5101422586755960%positive 53%nat (637677823344495)%Z 3%Z (-50)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c621fb78121fb78)%Z false 5101422586755960%positive 109%nat (637677823344495)%Z 3%Z (-106)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd1f6a8499e4889)%Z true 5056277254129801%positive 54%nat (-5056277254129801)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fb41b15e5decb17)%Z false 5659280399059735%positive 56%nat (5659280399059735)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3f959bc9409c66b7)%Z false 6082263185647287%positive 58%nat (6082263185647287)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfa63b54400c6f39)%Z true 6257682525482809%positive 57%nat (-6257682525482809)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3f9c90eeb21db860)%Z false 8040654212806752%positive 58%nat (251270444150211)%Z 5%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0xbf791f7b1f5a4a68)%Z true 7071488085215848%positive 60%nat (-883936010651981)%Z 3%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0xbf819ceb60012220)%Z true 4957609346015776%positive 59%nat (-154925292062993)%Z 5%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3f817d4c6d31c498)%Z false 4922841807045784%positive 59%nat (615355225880723)%Z 3%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x402e24be27e6ae5e)%Z false 8484648433135198%positive 49%nat (4242324216567599)%Z 1%Z (-48)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  unfold seg_poly in Eq.
  pose proof (approx_56 _ _ _ _ _ _ _ _ _ _ _ _ _ ((B zh - IZR 56 / 64) + B zl) V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 Ht) as AP.
  pose proof (amin_56 ((B zh - IZR 56 / 64) + B zl) Ht) as HAm.
  destruct ea_dw_small as [Ea0 Ea1].
  rewrite Eq.
  refine (fast_compose _ _ e1 ea (IZR 8866442 * bpow radix2 (-94)) (IZR 946 * bpow radix2 (-76)) _ (IZR 749089 * bpow radix2 (-20)) _ AP E1 Eea HAm _ Ea0 _).
  - apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0].
  - bpow_num. replace (- prec)%Z with (-53)%Z by reflexivity. bpow_num. clear - Fz. interval with (i_prec 200).
Qed.

Lemma evalcert_57 : EvalCert (IZR (2511469581172165) * bpow radix2 (-52)) (IZR (-6062844535798429) * bpow radix2 (-109)) (IZR (-77959845406025) * bpow radix2 (-48)) (IZR (2873414702847027) * bpow radix2 (-55)) (IZR (1283425584900245) * bpow radix2 (-56)) (IZR (-2942751041576119) * bpow radix2 (-56)) (IZR (3917568612317011) * bpow radix2 (-57)) (IZR (-3964688447590669) * bpow radix2 (-59)) (IZR (-7850325956591667) * bpow radix2 (-61)) (IZR (4556088360790335) * bpow radix2 (-59)) (IZR (-8148421172663551) * bpow radix2 (-49)) (IZR 934 * bpow radix2 (-76)) (IZR 665 * bpow radix2 (-73)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 467 (-467) (-75)); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_57.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_57.l1 th_ tl_ dg).
Qed.

Lemma segok_57 : SegOkRowA [(0x3fe748978fba8e0f)%Z; (0x3c47b2a6165884a1)%Z; (0x3fe1d856287ffb8a)%Z; (0xbc658a1ffee27a9d)%Z; (0xbfd1b9dc39195240)%Z; (0x3fb46ab5fd4fa866)%Z; (0x3f923d133855a254)%Z; (0xbfa4e8d53cfdb96e)%Z; (0x3f9bd6040b0a6ea6)%Z; (0xbf7c2bb9ed20a21a)%Z; (0xbf6be3d472038033)%Z; (0x3f802fbcfc4f693f)%Z; (0xc02cf2f2257a14ff)%Z] (IZR 934 * bpow radix2 (-76)).
Proof.
  unfold SegOkRowA. cbn [nth].
  destruct (word_ok_intro (0x3fe748978fba8e0f)%Z false 6553740252974607%positive 53%nat (6553740252974607)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c47b2a6165884a1)%Z false 6670350873560225%positive 111%nat (6670350873560225)%Z 0%Z (-111)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fe1d856287ffb8a)%Z false 5022939162344330%positive 53%nat (2511469581172165)%Z 1%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc658a1ffee27a9d)%Z true 6062844535798429%positive 109%nat (-6062844535798429)%Z 0%Z (-109)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd1b9dc39195240)%Z true 4989430105985600%positive 54%nat (-77959845406025)%Z 6%Z (-48)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fb46ab5fd4fa866)%Z false 5746829405694054%positive 56%nat (2873414702847027)%Z 1%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3f923d133855a254)%Z false 5133702339600980%positive 58%nat (1283425584900245)%Z 2%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfa4e8d53cfdb96e)%Z true 5885502083152238%positive 57%nat (-2942751041576119)%Z 1%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3f9bd6040b0a6ea6)%Z false 7835137224634022%positive 58%nat (3917568612317011)%Z 1%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0xbf7c2bb9ed20a21a)%Z true 7929376895181338%positive 60%nat (-3964688447590669)%Z 1%Z (-59)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0xbf6be3d472038033)%Z true 7850325956591667%positive 61%nat (-7850325956591667)%Z 0%Z (-61)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3f802fbcfc4f693f)%Z false 4556088360790335%positive 59%nat (4556088360790335)%Z 0%Z (-59)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc02cf2f2257a14ff)%Z true 8148421172663551%positive 49%nat (-8148421172663551)%Z 0%Z (-49)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_57 _ _).
  all: seg_numeric.
Qed.

Lemma row_57 : nth (Z.to_nat (57%Z - 1)) atan2_segments [] = [(0x3fe748978fba8e0f)%Z; (0x3c47b2a6165884a1)%Z; (0x3fe1d856287ffb8a)%Z; (0xbc658a1ffee27a9d)%Z; (0xbfd1b9dc39195240)%Z; (0x3fb46ab5fd4fa866)%Z; (0x3f923d133855a254)%Z; (0xbfa4e8d53cfdb96e)%Z; (0x3f9bd6040b0a6ea6)%Z; (0xbf7c2bb9ed20a21a)%Z; (0xbf6be3d472038033)%Z; (0x3f802fbcfc4f693f)%Z; (0xc02cf2f2257a14ff)%Z].
Proof. reflexivity. Qed.

Lemma fast_57 zh zl : finite zh -> finite zl -> / 128 <= B zh -> B zh <= 1 ->
  Znearest ne (B zh * 64) = 57%Z -> Rabs (B zl) <= bpow radix2 (-53) -> on_grid (-211) (B zl) ->
  exists h l, atan2_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    Rabs (B h + B l - atan (IZR 57 / 64 + ((B zh - IZR 57 / 64) + B zl))) <= bpow radix2 (-63) * atan (IZR 57 / 64 + ((B zh - IZR 57 / 64) + B zl)).
Proof.
  intros Fz Fl L U Hn Hl Hg.
  pose proof (series_segment_a zh zl 57%Z (IZR 934 * bpow radix2 (-76)) ltac:(lia) Fz Fl L U Hn Hl Hg segok_57) as SS.
  cbv zeta in SS. rewrite row_57 in SS. cbn [nth] in SS.
  destruct SS as [h [l [Hs [Fh [Fl' [Nrm [Ht [e1 [ea [E1 [Eea Eq]]]]]]]]]]].
  exists h, l. split; [exact Hs | split; [exact Fh | split; [exact Fl' | split; [exact Nrm | ]]]].
  destruct (word_ok_intro (0x3fe748978fba8e0f)%Z false 6553740252974607%positive 53%nat (6553740252974607)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c47b2a6165884a1)%Z false 6670350873560225%positive 111%nat (6670350873560225)%Z 0%Z (-111)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fe1d856287ffb8a)%Z false 5022939162344330%positive 53%nat (2511469581172165)%Z 1%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc658a1ffee27a9d)%Z true 6062844535798429%positive 109%nat (-6062844535798429)%Z 0%Z (-109)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd1b9dc39195240)%Z true 4989430105985600%positive 54%nat (-77959845406025)%Z 6%Z (-48)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fb46ab5fd4fa866)%Z false 5746829405694054%positive 56%nat (2873414702847027)%Z 1%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3f923d133855a254)%Z false 5133702339600980%positive 58%nat (1283425584900245)%Z 2%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfa4e8d53cfdb96e)%Z true 5885502083152238%positive 57%nat (-2942751041576119)%Z 1%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3f9bd6040b0a6ea6)%Z false 7835137224634022%positive 58%nat (3917568612317011)%Z 1%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0xbf7c2bb9ed20a21a)%Z true 7929376895181338%positive 60%nat (-3964688447590669)%Z 1%Z (-59)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0xbf6be3d472038033)%Z true 7850325956591667%positive 61%nat (-7850325956591667)%Z 0%Z (-61)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3f802fbcfc4f693f)%Z false 4556088360790335%positive 59%nat (4556088360790335)%Z 0%Z (-59)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc02cf2f2257a14ff)%Z true 8148421172663551%positive 49%nat (-8148421172663551)%Z 0%Z (-49)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  unfold seg_poly in Eq.
  pose proof (approx_57 _ _ _ _ _ _ _ _ _ _ _ _ _ ((B zh - IZR 57 / 64) + B zl) V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 Ht) as AP.
  pose proof (amin_57 ((B zh - IZR 57 / 64) + B zl) Ht) as HAm.
  destruct ea_dw_small as [Ea0 Ea1].
  rewrite Eq.
  refine (fast_compose _ _ e1 ea (IZR 8532759 * bpow radix2 (-94)) (IZR 934 * bpow radix2 (-76)) _ (IZR 758368 * bpow radix2 (-20)) _ AP E1 Eea HAm _ Ea0 _).
  - apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0].
  - bpow_num. replace (- prec)%Z with (-53)%Z by reflexivity. bpow_num. clear - Fz. interval with (i_prec 200).
Qed.

Lemma evalcert_58 : EvalCert (IZR (2472753897280101) * bpow radix2 (-52)) (IZR (-8905777708172863) * bpow radix2 (-107)) (IZR (-4921642073299589) * bpow radix2 (-54)) (IZR (2910003722190807) * bpow radix2 (-55)) (IZR (1060628741604921) * bpow radix2 (-56)) (IZR (-5523468235605677) * bpow radix2 (-57)) (IZR (237764910998749) * bpow radix2 (-53)) (IZR (-2157569637752401) * bpow radix2 (-58)) (IZR (-4969222514043155) * bpow radix2 (-59)) (IZR (2038766272625775) * bpow radix2 (-58)) (IZR (2186792260710917) * bpow radix2 (-46)) (IZR 921 * bpow radix2 (-76)) (IZR 673 * bpow radix2 (-73)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 921 (-921) (-76)); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_58.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_58.l1 th_ tl_ dg).
Qed.

Lemma segok_58 : SegOkRowA [(0x3fe78f6bbd5d315e)%Z; (0x3c8406a089803740)%Z; (0x3fe191e9c35424ca)%Z; (0xbc8fa3c1f4be863f)%Z; (0xbfd17c35177d9a85)%Z; (0x3fb4ad44144fffae)%Z; (0x3f8e2516fb0e31c8)%Z; (0xbfa39f90aa1c86ad)%Z; (0x3f9b07dea1ec9ba0)%Z; (0xbf7ea9314f587944)%Z; (0xbf81a77b46c26913)%Z; (0x3f7cf8fd0dd6f1bc)%Z; (0x403f1380ff96c814)%Z] (IZR 921 * bpow radix2 (-76)).
Proof.
  unfold SegOkRowA. cbn [nth].
  destruct (word_ok_intro (0x3fe78f6bbd5d315e)%Z false 6631617365619038%positive 53%nat (3315808682809519)%Z 1%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c8406a089803740)%Z false 5636786105628480%positive 107%nat (88074782900445)%Z 6%Z (-101)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fe191e9c35424ca)%Z false 4945507794560202%positive 53%nat (2472753897280101)%Z 1%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc8fa3c1f4be863f)%Z true 8905777708172863%positive 107%nat (-8905777708172863)%Z 0%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd17c35177d9a85)%Z true 4921642073299589%positive 54%nat (-4921642073299589)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fb4ad44144fffae)%Z false 5820007444381614%positive 56%nat (2910003722190807)%Z 1%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3f8e2516fb0e31c8)%Z false 8485029932839368%positive 59%nat (1060628741604921)%Z 3%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfa39f90aa1c86ad)%Z true 5523468235605677%positive 57%nat (-5523468235605677)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3f9b07dea1ec9ba0)%Z false 7608477151959968%positive 58%nat (237764910998749)%Z 5%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0xbf7ea9314f587944)%Z true 8630278551009604%positive 60%nat (-2157569637752401)%Z 2%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0xbf81a77b46c26913)%Z true 4969222514043155%positive 59%nat (-4969222514043155)%Z 0%Z (-59)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3f7cf8fd0dd6f1bc)%Z false 8155065090503100%positive 60%nat (2038766272625775)%Z 2%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x403f1380ff96c814)%Z false 8747169042843668%positive 48%nat (2186792260710917)%Z 2%Z (-46)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_58 _ _).
  all: seg_numeric.
Qed.

Lemma row_58 : nth (Z.to_nat (58%Z - 1)) atan2_segments [] = [(0x3fe78f6bbd5d315e)%Z; (0x3c8406a089803740)%Z; (0x3fe191e9c35424ca)%Z; (0xbc8fa3c1f4be863f)%Z; (0xbfd17c35177d9a85)%Z; (0x3fb4ad44144fffae)%Z; (0x3f8e2516fb0e31c8)%Z; (0xbfa39f90aa1c86ad)%Z; (0x3f9b07dea1ec9ba0)%Z; (0xbf7ea9314f587944)%Z; (0xbf81a77b46c26913)%Z; (0x3f7cf8fd0dd6f1bc)%Z; (0x403f1380ff96c814)%Z].
Proof. reflexivity. Qed.

Lemma fast_58 zh zl : finite zh -> finite zl -> / 128 <= B zh -> B zh <= 1 ->
  Znearest ne (B zh * 64) = 58%Z -> Rabs (B zl) <= bpow radix2 (-53) -> on_grid (-211) (B zl) ->
  exists h l, atan2_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    Rabs (B h + B l - atan (IZR 58 / 64 + ((B zh - IZR 58 / 64) + B zl))) <= bpow radix2 (-63) * atan (IZR 58 / 64 + ((B zh - IZR 58 / 64) + B zl)).
Proof.
  intros Fz Fl L U Hn Hl Hg.
  pose proof (series_segment_a zh zl 58%Z (IZR 921 * bpow radix2 (-76)) ltac:(lia) Fz Fl L U Hn Hl Hg segok_58) as SS.
  cbv zeta in SS. rewrite row_58 in SS. cbn [nth] in SS.
  destruct SS as [h [l [Hs [Fh [Fl' [Nrm [Ht [e1 [ea [E1 [Eea Eq]]]]]]]]]]].
  exists h, l. split; [exact Hs | split; [exact Fh | split; [exact Fl' | split; [exact Nrm | ]]]].
  destruct (word_ok_intro (0x3fe78f6bbd5d315e)%Z false 6631617365619038%positive 53%nat (3315808682809519)%Z 1%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c8406a089803740)%Z false 5636786105628480%positive 107%nat (88074782900445)%Z 6%Z (-101)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fe191e9c35424ca)%Z false 4945507794560202%positive 53%nat (2472753897280101)%Z 1%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc8fa3c1f4be863f)%Z true 8905777708172863%positive 107%nat (-8905777708172863)%Z 0%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd17c35177d9a85)%Z true 4921642073299589%positive 54%nat (-4921642073299589)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fb4ad44144fffae)%Z false 5820007444381614%positive 56%nat (2910003722190807)%Z 1%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3f8e2516fb0e31c8)%Z false 8485029932839368%positive 59%nat (1060628741604921)%Z 3%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfa39f90aa1c86ad)%Z true 5523468235605677%positive 57%nat (-5523468235605677)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3f9b07dea1ec9ba0)%Z false 7608477151959968%positive 58%nat (237764910998749)%Z 5%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0xbf7ea9314f587944)%Z true 8630278551009604%positive 60%nat (-2157569637752401)%Z 2%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0xbf81a77b46c26913)%Z true 4969222514043155%positive 59%nat (-4969222514043155)%Z 0%Z (-59)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3f7cf8fd0dd6f1bc)%Z false 8155065090503100%positive 60%nat (2038766272625775)%Z 2%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x403f1380ff96c814)%Z false 8747169042843668%positive 48%nat (2186792260710917)%Z 2%Z (-46)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  unfold seg_poly in Eq.
  pose proof (approx_58 _ _ _ _ _ _ _ _ _ _ _ _ _ ((B zh - IZR 58 / 64) + B zl) V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 Ht) as AP.
  pose proof (amin_58 ((B zh - IZR 58 / 64) + B zl) Ht) as HAm.
  destruct ea_dw_small as [Ea0 Ea1].
  rewrite Eq.
  refine (fast_compose _ _ e1 ea (IZR 9166071 * bpow radix2 (-93)) (IZR 921 * bpow radix2 (-76)) _ (IZR 767505 * bpow radix2 (-20)) _ AP E1 Eea HAm _ Ea0 _).
  - apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0].
  - bpow_num. replace (- prec)%Z with (-53)%Z by reflexivity. bpow_num. clear - Fz. interval with (i_prec 200).
Qed.

Lemma evalcert_59 : EvalCert (IZR (4869141896188347) * bpow radix2 (-53)) (IZR (-1181028436001739) * bpow radix2 (-105)) (IZR (-4853076362678421) * bpow radix2 (-54)) (IZR (5879698203918865) * bpow radix2 (-56)) (IZR (3407042859837839) * bpow radix2 (-58)) (IZR (-161640027717981) * bpow radix2 (-52)) (IZR (7364460258173261) * bpow radix2 (-58)) (IZR (-2297091435814071) * bpow radix2 (-58)) (IZR (-5698730589349745) * bpow radix2 (-63)) (IZR (465405117343777) * bpow radix2 (-56)) (IZR (-5721541022356329) * bpow radix2 (-48)) (IZR 908 * bpow radix2 (-76)) (IZR 679 * bpow radix2 (-73)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 227 (-227) (-74)); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_59.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_59.l1 th_ tl_ dg).
Qed.

Lemma segok_59 : SegOkRowA [(0x3fe7d528289fa093)%Z; (0x3c8560821e2f3aa9)%Z; (0x3fe14c75711551bb)%Z; (0xbc80c88e71970f2c)%Z; (0xbfd13dd8e4aa5095)%Z; (0x3fb4e38dead4c211)%Z; (0x3f88355ff6ca531e)%Z; (0xbfa260580de02ba0)%Z; (0x3f9a29f005a6a14d)%Z; (0xbf8052628e18b96e)%Z; (0xbf443ef71c72e771)%Z; (0x3f7a74892b228210)%Z; (0xc03453b614349369)%Z] (IZR 908 * bpow radix2 (-76)).
Proof.
  unfold SegOkRowA. cbn [nth].
  destruct (word_ok_intro (0x3fe7d528289fa093)%Z false 6708292921303187%positive 53%nat (6708292921303187)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c8560821e2f3aa9)%Z false 6017086479350441%positive 107%nat (6017086479350441)%Z 0%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fe14c75711551bb)%Z false 4869141896188347%positive 53%nat (4869141896188347)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc80c88e71970f2c)%Z true 4724113744006956%positive 107%nat (-1181028436001739)%Z 2%Z (-105)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd13dd8e4aa5095)%Z true 4853076362678421%positive 54%nat (-4853076362678421)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fb4e38dead4c211)%Z false 5879698203918865%positive 56%nat (5879698203918865)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3f88355ff6ca531e)%Z false 6814085719675678%positive 59%nat (3407042859837839)%Z 1%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfa260580de02ba0)%Z true 5172480886975392%positive 57%nat (-161640027717981)%Z 5%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3f9a29f005a6a14d)%Z false 7364460258173261%positive 58%nat (7364460258173261)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0xbf8052628e18b96e)%Z true 4594182871628142%positive 59%nat (-2297091435814071)%Z 1%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0xbf443ef71c72e771)%Z true 5698730589349745%positive 63%nat (-5698730589349745)%Z 0%Z (-63)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3f7a74892b228210)%Z false 7446481877500432%positive 60%nat (465405117343777)%Z 4%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc03453b614349369)%Z true 5721541022356329%positive 48%nat (-5721541022356329)%Z 0%Z (-48)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_59 _ _).
  all: seg_numeric.
Qed.

Lemma row_59 : nth (Z.to_nat (59%Z - 1)) atan2_segments [] = [(0x3fe7d528289fa093)%Z; (0x3c8560821e2f3aa9)%Z; (0x3fe14c75711551bb)%Z; (0xbc80c88e71970f2c)%Z; (0xbfd13dd8e4aa5095)%Z; (0x3fb4e38dead4c211)%Z; (0x3f88355ff6ca531e)%Z; (0xbfa260580de02ba0)%Z; (0x3f9a29f005a6a14d)%Z; (0xbf8052628e18b96e)%Z; (0xbf443ef71c72e771)%Z; (0x3f7a74892b228210)%Z; (0xc03453b614349369)%Z].
Proof. reflexivity. Qed.

Lemma fast_59 zh zl : finite zh -> finite zl -> / 128 <= B zh -> B zh <= 1 ->
  Znearest ne (B zh * 64) = 59%Z -> Rabs (B zl) <= bpow radix2 (-53) -> on_grid (-211) (B zl) ->
  exists h l, atan2_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    Rabs (B h + B l - atan (IZR 59 / 64 + ((B zh - IZR 59 / 64) + B zl))) <= bpow radix2 (-63) * atan (IZR 59 / 64 + ((B zh - IZR 59 / 64) + B zl)).
Proof.
  intros Fz Fl L U Hn Hl Hg.
  pose proof (series_segment_a zh zl 59%Z (IZR 908 * bpow radix2 (-76)) ltac:(lia) Fz Fl L U Hn Hl Hg segok_59) as SS.
  cbv zeta in SS. rewrite row_59 in SS. cbn [nth] in SS.
  destruct SS as [h [l [Hs [Fh [Fl' [Nrm [Ht [e1 [ea [E1 [Eea Eq]]]]]]]]]]].
  exists h, l. split; [exact Hs | split; [exact Fh | split; [exact Fl' | split; [exact Nrm | ]]]].
  destruct (word_ok_intro (0x3fe7d528289fa093)%Z false 6708292921303187%positive 53%nat (6708292921303187)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c8560821e2f3aa9)%Z false 6017086479350441%positive 107%nat (6017086479350441)%Z 0%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fe14c75711551bb)%Z false 4869141896188347%positive 53%nat (4869141896188347)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc80c88e71970f2c)%Z true 4724113744006956%positive 107%nat (-1181028436001739)%Z 2%Z (-105)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd13dd8e4aa5095)%Z true 4853076362678421%positive 54%nat (-4853076362678421)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fb4e38dead4c211)%Z false 5879698203918865%positive 56%nat (5879698203918865)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3f88355ff6ca531e)%Z false 6814085719675678%positive 59%nat (3407042859837839)%Z 1%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfa260580de02ba0)%Z true 5172480886975392%positive 57%nat (-161640027717981)%Z 5%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3f9a29f005a6a14d)%Z false 7364460258173261%positive 58%nat (7364460258173261)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0xbf8052628e18b96e)%Z true 4594182871628142%positive 59%nat (-2297091435814071)%Z 1%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0xbf443ef71c72e771)%Z true 5698730589349745%positive 63%nat (-5698730589349745)%Z 0%Z (-63)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3f7a74892b228210)%Z false 7446481877500432%positive 60%nat (465405117343777)%Z 4%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc03453b614349369)%Z true 5721541022356329%positive 48%nat (-5721541022356329)%Z 0%Z (-48)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  unfold seg_poly in Eq.
  pose proof (approx_59 _ _ _ _ _ _ _ _ _ _ _ _ _ ((B zh - IZR 59 / 64) + B zl) V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 Ht) as AP.
  pose proof (amin_59 ((B zh - IZR 59 / 64) + B zl) Ht) as HAm.
  destruct ea_dw_small as [Ea0 Ea1].
  rewrite Eq.
  refine (fast_compose _ _ e1 ea (IZR 11987651 * bpow radix2 (-94)) (IZR 908 * bpow radix2 (-76)) _ (IZR 776501 * bpow radix2 (-20)) _ AP E1 Eea HAm _ Ea0 _).
  - apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0].
  - bpow_num. replace (- prec)%Z with (-53)%Z by reflexivity. bpow_num. clear - Fz. interval with (i_prec 200).
Qed.

Lemma evalcert_60 : EvalCert (IZR (37451971953185) * bpow radix2 (-46)) (IZR (-37451971953185) * bpow radix2 (-100)) (IZR (-4783885980880845) * bpow radix2 (-54)) (IZR (5926758441362935) * bpow radix2 (-56)) (IZR (1312750866824413) * bpow radix2 (-57)) (IZR (-2416628405195775) * bpow radix2 (-56)) (IZR (7107035779100169) * bpow radix2 (-58)) (IZR (-1202159481498727) * bpow radix2 (-57)) (IZR (7037624326953111) * bpow radix2 (-61)) (IZR (207176116309279) * bpow radix2 (-55)) (IZR (-44926650711967) * bpow radix2 (-40)) (IZR 895 * bpow radix2 (-76)) (IZR 684 * bpow radix2 (-73)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 895 (-895) (-76)); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_60.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_60.l1 th_ tl_ dg).
Qed.

Lemma segok_60 : SegOkRowA [(0x3fe819d0b7158a4d)%Z; (0xbc7bf76229d3b917)%Z; (0x3fe107fbbe011080)%Z; (0xbc8107fbbe011080)%Z; (0xbfd0feeb40894fcd)%Z; (0x3fb50e5afb9125f7)%Z; (0x3f82a7c28461f374)%Z; (0xbfa12bd24b4aa7fe)%Z; (0x3f993fcfb704ee09)%Z; (0xbf81156e436eb19c)%Z; (0x3f6900ae9a121897)%Z; (0x3f778d9e5a31a3e0)%Z; (0xc0446e26873fcf80)%Z] (IZR 895 * bpow radix2 (-76)).
Proof.
  unfold SegOkRowA. cbn [nth].
  destruct (word_ok_intro (0x3fe819d0b7158a4d)%Z false 6783783656589901%positive 53%nat (6783783656589901)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc7bf76229d3b917)%Z true 7871825351784727%positive 108%nat (-7871825351784727)%Z 0%Z (-108)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fe107fbbe011080)%Z false 4793852410007680%positive 53%nat (37451971953185)%Z 7%Z (-46)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc8107fbbe011080)%Z true 4793852410007680%positive 107%nat (-37451971953185)%Z 7%Z (-100)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd0feeb40894fcd)%Z true 4783885980880845%positive 54%nat (-4783885980880845)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fb50e5afb9125f7)%Z false 5926758441362935%positive 56%nat (5926758441362935)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3f82a7c28461f374)%Z false 5251003467297652%positive 59%nat (1312750866824413)%Z 2%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfa12bd24b4aa7fe)%Z true 4833256810391550%positive 57%nat (-2416628405195775)%Z 1%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3f993fcfb704ee09)%Z false 7107035779100169%positive 58%nat (7107035779100169)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0xbf81156e436eb19c)%Z true 4808637925994908%positive 59%nat (-1202159481498727)%Z 2%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3f6900ae9a121897)%Z false 7037624326953111%positive 61%nat (7037624326953111)%Z 0%Z (-61)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3f778d9e5a31a3e0)%Z false 6629635721896928%positive 60%nat (207176116309279)%Z 5%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc0446e26873fcf80)%Z true 5750611291131776%positive 47%nat (-44926650711967)%Z 7%Z (-40)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_60 _ _).
  all: seg_numeric.
Qed.

Lemma row_60 : nth (Z.to_nat (60%Z - 1)) atan2_segments [] = [(0x3fe819d0b7158a4d)%Z; (0xbc7bf76229d3b917)%Z; (0x3fe107fbbe011080)%Z; (0xbc8107fbbe011080)%Z; (0xbfd0feeb40894fcd)%Z; (0x3fb50e5afb9125f7)%Z; (0x3f82a7c28461f374)%Z; (0xbfa12bd24b4aa7fe)%Z; (0x3f993fcfb704ee09)%Z; (0xbf81156e436eb19c)%Z; (0x3f6900ae9a121897)%Z; (0x3f778d9e5a31a3e0)%Z; (0xc0446e26873fcf80)%Z].
Proof. reflexivity. Qed.

Lemma fast_60 zh zl : finite zh -> finite zl -> / 128 <= B zh -> B zh <= 1 ->
  Znearest ne (B zh * 64) = 60%Z -> Rabs (B zl) <= bpow radix2 (-53) -> on_grid (-211) (B zl) ->
  exists h l, atan2_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    Rabs (B h + B l - atan (IZR 60 / 64 + ((B zh - IZR 60 / 64) + B zl))) <= bpow radix2 (-63) * atan (IZR 60 / 64 + ((B zh - IZR 60 / 64) + B zl)).
Proof.
  intros Fz Fl L U Hn Hl Hg.
  pose proof (series_segment_a zh zl 60%Z (IZR 895 * bpow radix2 (-76)) ltac:(lia) Fz Fl L U Hn Hl Hg segok_60) as SS.
  cbv zeta in SS. rewrite row_60 in SS. cbn [nth] in SS.
  destruct SS as [h [l [Hs [Fh [Fl' [Nrm [Ht [e1 [ea [E1 [Eea Eq]]]]]]]]]]].
  exists h, l. split; [exact Hs | split; [exact Fh | split; [exact Fl' | split; [exact Nrm | ]]]].
  destruct (word_ok_intro (0x3fe819d0b7158a4d)%Z false 6783783656589901%positive 53%nat (6783783656589901)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc7bf76229d3b917)%Z true 7871825351784727%positive 108%nat (-7871825351784727)%Z 0%Z (-108)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fe107fbbe011080)%Z false 4793852410007680%positive 53%nat (37451971953185)%Z 7%Z (-46)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc8107fbbe011080)%Z true 4793852410007680%positive 107%nat (-37451971953185)%Z 7%Z (-100)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd0feeb40894fcd)%Z true 4783885980880845%positive 54%nat (-4783885980880845)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fb50e5afb9125f7)%Z false 5926758441362935%positive 56%nat (5926758441362935)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3f82a7c28461f374)%Z false 5251003467297652%positive 59%nat (1312750866824413)%Z 2%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfa12bd24b4aa7fe)%Z true 4833256810391550%positive 57%nat (-2416628405195775)%Z 1%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3f993fcfb704ee09)%Z false 7107035779100169%positive 58%nat (7107035779100169)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0xbf81156e436eb19c)%Z true 4808637925994908%positive 59%nat (-1202159481498727)%Z 2%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3f6900ae9a121897)%Z false 7037624326953111%positive 61%nat (7037624326953111)%Z 0%Z (-61)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3f778d9e5a31a3e0)%Z false 6629635721896928%positive 60%nat (207176116309279)%Z 5%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc0446e26873fcf80)%Z true 5750611291131776%positive 47%nat (-44926650711967)%Z 7%Z (-40)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  unfold seg_poly in Eq.
  pose proof (approx_60 _ _ _ _ _ _ _ _ _ _ _ _ _ ((B zh - IZR 60 / 64) + B zl) V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 Ht) as AP.
  pose proof (amin_60 ((B zh - IZR 60 / 64) + B zl) Ht) as HAm.
  destruct ea_dw_small as [Ea0 Ea1].
  rewrite Eq.
  refine (fast_compose _ _ e1 ea (IZR 12050180 * bpow radix2 (-93)) (IZR 895 * bpow radix2 (-76)) _ (IZR 785358 * bpow radix2 (-20)) _ AP E1 Eea HAm _ Ea0 _).
  - apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0].
  - bpow_num. replace (- prec)%Z with (-53)%Z by reflexivity. bpow_num. clear - Fz. interval with (i_prec 200).
Qed.

Lemma evalcert_61 : EvalCert (IZR (1179911991410359) * bpow radix2 (-51)) (IZR (-4562940904282247) * bpow radix2 (-107)) (IZR (-4714214061114025) * bpow radix2 (-54)) (IZR (5962016228531315) * bpow radix2 (-56)) (IZR (7584033889396647) * bpow radix2 (-60)) (IZR (-2253173584693165) * bpow radix2 (-56)) (IZR (6839527772339453) * bpow radix2 (-58)) (IZR (-4965076712447507) * bpow radix2 (-59)) (IZR (1276203680615483) * bpow radix2 (-58)) (IZR (5857031551486921) * bpow radix2 (-60)) (IZR (-6380410888668435) * bpow radix2 (-47)) (IZR 882 * bpow radix2 (-76)) (IZR 688 * bpow radix2 (-73)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 441 (-441) (-75)); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_61.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_61.l1 th_ tl_ dg).
Qed.

Lemma segok_61 : SegOkRowA [(0x3fe85d69576cc2c5)%Z; (0x3c66b66e7fc8b8c3)%Z; (0x3fe0c47eac74fadc)%Z; (0xbc8035f877bb1887)%Z; (0xbfd0bf8d7e8202a9)%Z; (0x3fb52e6c13725c73)%Z; (0x3f7af1a37df127a7)%Z; (0xbfa0027fb6440f5a)%Z; (0x3f984c83a74d3cfd)%Z; (0xbf81a3b601ba5e13)%Z; (0x3f7222cd4c2d30ec)%Z; (0x3f74cef06d108bc9)%Z; (0xc046aaf32c8a4513)%Z] (IZR 882 * bpow radix2 (-76)).
Proof.
  unfold SegOkRowA. cbn [nth].
  destruct (word_ok_intro (0x3fe85d69576cc2c5)%Z false 6858106460750533%positive 53%nat (6858106460750533)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c66b66e7fc8b8c3)%Z false 6393035194153155%positive 109%nat (6393035194153155)%Z 0%Z (-109)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fe0c47eac74fadc)%Z false 4719647965641436%positive 53%nat (1179911991410359)%Z 2%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc8035f877bb1887)%Z true 4562940904282247%positive 107%nat (-4562940904282247)%Z 0%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd0bf8d7e8202a9)%Z true 4714214061114025%positive 54%nat (-4714214061114025)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fb52e6c13725c73)%Z false 5962016228531315%positive 56%nat (5962016228531315)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3f7af1a37df127a7)%Z false 7584033889396647%positive 60%nat (7584033889396647)%Z 0%Z (-60)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfa0027fb6440f5a)%Z true 4506347169386330%positive 57%nat (-2253173584693165)%Z 1%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3f984c83a74d3cfd)%Z false 6839527772339453%positive 58%nat (6839527772339453)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0xbf81a3b601ba5e13)%Z true 4965076712447507%positive 59%nat (-4965076712447507)%Z 0%Z (-59)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3f7222cd4c2d30ec)%Z false 5104814722461932%positive 60%nat (1276203680615483)%Z 2%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3f74cef06d108bc9)%Z false 5857031551486921%positive 60%nat (5857031551486921)%Z 0%Z (-60)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc046aaf32c8a4513)%Z true 6380410888668435%positive 47%nat (-6380410888668435)%Z 0%Z (-47)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_61 _ _).
  all: seg_numeric.
Qed.

Lemma row_61 : nth (Z.to_nat (61%Z - 1)) atan2_segments [] = [(0x3fe85d69576cc2c5)%Z; (0x3c66b66e7fc8b8c3)%Z; (0x3fe0c47eac74fadc)%Z; (0xbc8035f877bb1887)%Z; (0xbfd0bf8d7e8202a9)%Z; (0x3fb52e6c13725c73)%Z; (0x3f7af1a37df127a7)%Z; (0xbfa0027fb6440f5a)%Z; (0x3f984c83a74d3cfd)%Z; (0xbf81a3b601ba5e13)%Z; (0x3f7222cd4c2d30ec)%Z; (0x3f74cef06d108bc9)%Z; (0xc046aaf32c8a4513)%Z].
Proof. reflexivity. Qed.

Lemma fast_61 zh zl : finite zh -> finite zl -> / 128 <= B zh -> B zh <= 1 ->
  Znearest ne (B zh * 64) = 61%Z -> Rabs (B zl) <= bpow radix2 (-53) -> on_grid (-211) (B zl) ->
  exists h l, atan2_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    Rabs (B h + B l - atan (IZR 61 / 64 + ((B zh - IZR 61 / 64) + B zl))) <= bpow radix2 (-63) * atan (IZR 61 / 64 + ((B zh - IZR 61 / 64) + B zl)).
Proof.
  intros Fz Fl L U Hn Hl Hg.
  pose proof (series_segment_a zh zl 61%Z (IZR 882 * bpow radix2 (-76)) ltac:(lia) Fz Fl L U Hn Hl Hg segok_61) as SS.
  cbv zeta in SS. rewrite row_61 in SS. cbn [nth] in SS.
  destruct SS as [h [l [Hs [Fh [Fl' [Nrm [Ht [e1 [ea [E1 [Eea Eq]]]]]]]]]]].
  exists h, l. split; [exact Hs | split; [exact Fh | split; [exact Fl' | split; [exact Nrm | ]]]].
  destruct (word_ok_intro (0x3fe85d69576cc2c5)%Z false 6858106460750533%positive 53%nat (6858106460750533)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c66b66e7fc8b8c3)%Z false 6393035194153155%positive 109%nat (6393035194153155)%Z 0%Z (-109)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fe0c47eac74fadc)%Z false 4719647965641436%positive 53%nat (1179911991410359)%Z 2%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc8035f877bb1887)%Z true 4562940904282247%positive 107%nat (-4562940904282247)%Z 0%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd0bf8d7e8202a9)%Z true 4714214061114025%positive 54%nat (-4714214061114025)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fb52e6c13725c73)%Z false 5962016228531315%positive 56%nat (5962016228531315)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3f7af1a37df127a7)%Z false 7584033889396647%positive 60%nat (7584033889396647)%Z 0%Z (-60)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbfa0027fb6440f5a)%Z true 4506347169386330%positive 57%nat (-2253173584693165)%Z 1%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3f984c83a74d3cfd)%Z false 6839527772339453%positive 58%nat (6839527772339453)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0xbf81a3b601ba5e13)%Z true 4965076712447507%positive 59%nat (-4965076712447507)%Z 0%Z (-59)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3f7222cd4c2d30ec)%Z false 5104814722461932%positive 60%nat (1276203680615483)%Z 2%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3f74cef06d108bc9)%Z false 5857031551486921%positive 60%nat (5857031551486921)%Z 0%Z (-60)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc046aaf32c8a4513)%Z true 6380410888668435%positive 47%nat (-6380410888668435)%Z 0%Z (-47)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  unfold seg_poly in Eq.
  pose proof (approx_61 _ _ _ _ _ _ _ _ _ _ _ _ _ ((B zh - IZR 61 / 64) + B zl) V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 Ht) as AP.
  pose proof (amin_61 ((B zh - IZR 61 / 64) + B zl) Ht) as HAm.
  destruct ea_dw_small as [Ea0 Ea1].
  rewrite Eq.
  refine (fast_compose _ _ e1 ea (IZR 13370265 * bpow radix2 (-93)) (IZR 882 * bpow radix2 (-76)) _ (IZR 794078 * bpow radix2 (-20)) _ AP E1 Eea HAm _ Ea0 _).
  - apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0].
  - bpow_num. replace (- prec)%Z with (-53)%Z by reflexivity. bpow_num. clear - Fz. interval with (i_prec 200).
Qed.

Lemma evalcert_62 : EvalCert (IZR (580816878895137) * bpow radix2 (-50)) (IZR (17583323482177) * bpow radix2 (-100)) (IZR (-580524275933477) * bpow radix2 (-51)) (IZR (5986269602965151) * bpow radix2 (-56)) (IZR (4866422712132945) * bpow radix2 (-60)) (IZR (-8384308669062711) * bpow radix2 (-58)) (IZR (6564992914809907) * bpow radix2 (-58)) (IZR (-2534876834896963) * bpow radix2 (-58)) (IZR (-3422911588050723) * bpow radix2 (-62)) (IZR (5311698167737637) * bpow radix2 (-60)) (IZR (-3109551456668981) * bpow radix2 (-50)) (IZR 869 * bpow radix2 (-76)) (IZR 691 * bpow radix2 (-73)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 869 (-869) (-76)); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_62.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_62.l1 th_ tl_ dg).
Qed.

Lemma segok_62 : SegOkRowA [(0x3fe89ff5ff57f1f8)%Z; (0xbc855b9a5e177a1b)%Z; (0x3fe081ffbdf80108)%Z; (0x3c6ffbdf80108200)%Z; (0xbfd07fdeba010928)%Z; (0x3fb5447b0136e69f)%Z; (0x3f7149fc55156551)%Z; (0xbf9dc97bfbe81e37)%Z; (0x3f9752d386a3e433)%Z; (0xbf8202ea02963886)%Z; (0xbf48523d6a9b4e46)%Z; (0x3f72def61a712d25)%Z; (0xc006183dbbf89a6a)%Z] (IZR 869 * bpow radix2 (-76)).
Proof.
  unfold SegOkRowA. cbn [nth].
  destruct (word_ok_intro (0x3fe89ff5ff57f1f8)%Z false 6931278340813304%positive 53%nat (866409792601663)%Z 3%Z (-50)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc855b9a5e177a1b)%Z true 6011693072611867%positive 107%nat (-6011693072611867)%Z 0%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fe081ffbdf80108)%Z false 4646535031161096%positive 53%nat (580816878895137)%Z 3%Z (-50)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c6ffbdf80108200)%Z false 9002661622874624%positive 109%nat (17583323482177)%Z 9%Z (-100)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd07fdeba010928)%Z true 4644194207467816%positive 54%nat (-580524275933477)%Z 3%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fb5447b0136e69f)%Z false 5986269602965151%positive 56%nat (5986269602965151)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3f7149fc55156551)%Z false 4866422712132945%positive 60%nat (4866422712132945)%Z 0%Z (-60)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbf9dc97bfbe81e37)%Z true 8384308669062711%positive 58%nat (-8384308669062711)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3f9752d386a3e433)%Z false 6564992914809907%positive 58%nat (6564992914809907)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0xbf8202ea02963886)%Z true 5069753669793926%positive 59%nat (-2534876834896963)%Z 1%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0xbf48523d6a9b4e46)%Z true 6845823176101446%positive 63%nat (-3422911588050723)%Z 1%Z (-62)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3f72def61a712d25)%Z false 5311698167737637%positive 60%nat (5311698167737637)%Z 0%Z (-60)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc006183dbbf89a6a)%Z true 6219102913337962%positive 51%nat (-3109551456668981)%Z 1%Z (-50)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_62 _ _).
  all: seg_numeric.
Qed.

Lemma row_62 : nth (Z.to_nat (62%Z - 1)) atan2_segments [] = [(0x3fe89ff5ff57f1f8)%Z; (0xbc855b9a5e177a1b)%Z; (0x3fe081ffbdf80108)%Z; (0x3c6ffbdf80108200)%Z; (0xbfd07fdeba010928)%Z; (0x3fb5447b0136e69f)%Z; (0x3f7149fc55156551)%Z; (0xbf9dc97bfbe81e37)%Z; (0x3f9752d386a3e433)%Z; (0xbf8202ea02963886)%Z; (0xbf48523d6a9b4e46)%Z; (0x3f72def61a712d25)%Z; (0xc006183dbbf89a6a)%Z].
Proof. reflexivity. Qed.

Lemma fast_62 zh zl : finite zh -> finite zl -> / 128 <= B zh -> B zh <= 1 ->
  Znearest ne (B zh * 64) = 62%Z -> Rabs (B zl) <= bpow radix2 (-53) -> on_grid (-211) (B zl) ->
  exists h l, atan2_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    Rabs (B h + B l - atan (IZR 62 / 64 + ((B zh - IZR 62 / 64) + B zl))) <= bpow radix2 (-63) * atan (IZR 62 / 64 + ((B zh - IZR 62 / 64) + B zl)).
Proof.
  intros Fz Fl L U Hn Hl Hg.
  pose proof (series_segment_a zh zl 62%Z (IZR 869 * bpow radix2 (-76)) ltac:(lia) Fz Fl L U Hn Hl Hg segok_62) as SS.
  cbv zeta in SS. rewrite row_62 in SS. cbn [nth] in SS.
  destruct SS as [h [l [Hs [Fh [Fl' [Nrm [Ht [e1 [ea [E1 [Eea Eq]]]]]]]]]]].
  exists h, l. split; [exact Hs | split; [exact Fh | split; [exact Fl' | split; [exact Nrm | ]]]].
  destruct (word_ok_intro (0x3fe89ff5ff57f1f8)%Z false 6931278340813304%positive 53%nat (866409792601663)%Z 3%Z (-50)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc855b9a5e177a1b)%Z true 6011693072611867%positive 107%nat (-6011693072611867)%Z 0%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fe081ffbdf80108)%Z false 4646535031161096%positive 53%nat (580816878895137)%Z 3%Z (-50)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c6ffbdf80108200)%Z false 9002661622874624%positive 109%nat (17583323482177)%Z 9%Z (-100)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd07fdeba010928)%Z true 4644194207467816%positive 54%nat (-580524275933477)%Z 3%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fb5447b0136e69f)%Z false 5986269602965151%positive 56%nat (5986269602965151)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3f7149fc55156551)%Z false 4866422712132945%positive 60%nat (4866422712132945)%Z 0%Z (-60)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbf9dc97bfbe81e37)%Z true 8384308669062711%positive 58%nat (-8384308669062711)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3f9752d386a3e433)%Z false 6564992914809907%positive 58%nat (6564992914809907)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0xbf8202ea02963886)%Z true 5069753669793926%positive 59%nat (-2534876834896963)%Z 1%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0xbf48523d6a9b4e46)%Z true 6845823176101446%positive 63%nat (-3422911588050723)%Z 1%Z (-62)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3f72def61a712d25)%Z false 5311698167737637%positive 60%nat (5311698167737637)%Z 0%Z (-60)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc006183dbbf89a6a)%Z true 6219102913337962%positive 51%nat (-3109551456668981)%Z 1%Z (-50)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  unfold seg_poly in Eq.
  pose proof (approx_62 _ _ _ _ _ _ _ _ _ _ _ _ _ ((B zh - IZR 62 / 64) + B zl) V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 Ht) as AP.
  pose proof (amin_62 ((B zh - IZR 62 / 64) + B zl) Ht) as HAm.
  destruct ea_dw_small as [Ea0 Ea1].
  rewrite Eq.
  refine (fast_compose _ _ e1 ea (IZR 13016496 * bpow radix2 (-97)) (IZR 869 * bpow radix2 (-76)) _ (IZR 802663 * bpow radix2 (-20)) _ AP E1 Eea HAm _ Ea0 _).
  - apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0].
  - bpow_num. replace (- prec)%Z with (-53)%Z by reflexivity. bpow_num. clear - Fz. interval with (i_prec 200).
Qed.

Lemma evalcert_63 : EvalCert (IZR (4574518059196417) * bpow radix2 (-53)) (IZR (4538779636858945) * bpow radix2 (-111)) (IZR (-4573950852989449) * bpow radix2 (-54)) (IZR (6000285582323089) * bpow radix2 (-56)) (IZR (4682269302910037) * bpow radix2 (-61)) (IZR (-7781895766283237) * bpow radix2 (-58)) (IZR (3142979220819661) * bpow radix2 (-57)) (IZR (-2564272605199071) * bpow radix2 (-58)) (IZR (-8042539094998977) * bpow radix2 (-62)) (IZR (4709295987195781) * bpow radix2 (-60)) (IZR (5000908992608685) * bpow radix2 (-49)) (IZR 856 * bpow radix2 (-76)) (IZR 692 * bpow radix2 (-73)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 107 (-107) (-73)); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_63.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_63.l1 th_ tl_ dg).
Qed.

Lemma segok_63 : SegOkRowA [(0x3fe8e17aa99cc05e)%Z; (0xbc7ec182ab042f61)%Z; (0x3fe0407ffbefe001)%Z; (0x3c401ffefbf80041)%Z; (0xbfd03ffbebd00209)%Z; (0x3fb5513a5aaf6d91)%Z; (0x3f60a27fc68aec55)%Z; (0xbf9ba597ccd413e5)%Z; (0x3f96550bbffc9d9a)%Z; (0xbf8238627b7af5be)%Z; (0xbf5c92a58dd97fc1)%Z; (0x3f70bb146a757f85)%Z; (0x4021c44cdc0ef9ad)%Z] (IZR 856 * bpow radix2 (-76)).
Proof.
  unfold SegOkRowA. cbn [nth].
  destruct (word_ok_intro (0x3fe8e17aa99cc05e)%Z false 7003316388937822%positive 53%nat (3501658194468911)%Z 1%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc7ec182ab042f61)%Z true 8657016260407137%positive 108%nat (-8657016260407137)%Z 0%Z (-108)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fe0407ffbefe001)%Z false 4574518059196417%positive 53%nat (4574518059196417)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c401ffefbf80041)%Z false 4538779636858945%positive 111%nat (4538779636858945)%Z 0%Z (-111)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd03ffbebd00209)%Z true 4573950852989449%positive 54%nat (-4573950852989449)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fb5513a5aaf6d91)%Z false 6000285582323089%positive 56%nat (6000285582323089)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3f60a27fc68aec55)%Z false 4682269302910037%positive 61%nat (4682269302910037)%Z 0%Z (-61)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbf9ba597ccd413e5)%Z true 7781895766283237%positive 58%nat (-7781895766283237)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3f96550bbffc9d9a)%Z false 6285958441639322%positive 58%nat (3142979220819661)%Z 1%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0xbf8238627b7af5be)%Z true 5128545210398142%positive 59%nat (-2564272605199071)%Z 1%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0xbf5c92a58dd97fc1)%Z true 8042539094998977%positive 62%nat (-8042539094998977)%Z 0%Z (-62)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3f70bb146a757f85)%Z false 4709295987195781%positive 60%nat (4709295987195781)%Z 0%Z (-60)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x4021c44cdc0ef9ad)%Z false 5000908992608685%positive 49%nat (5000908992608685)%Z 0%Z (-49)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_63 _ _).
  all: seg_numeric.
Qed.

Lemma row_63 : nth (Z.to_nat (63%Z - 1)) atan2_segments [] = [(0x3fe8e17aa99cc05e)%Z; (0xbc7ec182ab042f61)%Z; (0x3fe0407ffbefe001)%Z; (0x3c401ffefbf80041)%Z; (0xbfd03ffbebd00209)%Z; (0x3fb5513a5aaf6d91)%Z; (0x3f60a27fc68aec55)%Z; (0xbf9ba597ccd413e5)%Z; (0x3f96550bbffc9d9a)%Z; (0xbf8238627b7af5be)%Z; (0xbf5c92a58dd97fc1)%Z; (0x3f70bb146a757f85)%Z; (0x4021c44cdc0ef9ad)%Z].
Proof. reflexivity. Qed.

Lemma fast_63 zh zl : finite zh -> finite zl -> / 128 <= B zh -> B zh <= 1 ->
  Znearest ne (B zh * 64) = 63%Z -> Rabs (B zl) <= bpow radix2 (-53) -> on_grid (-211) (B zl) ->
  exists h l, atan2_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    Rabs (B h + B l - atan (IZR 63 / 64 + ((B zh - IZR 63 / 64) + B zl))) <= bpow radix2 (-63) * atan (IZR 63 / 64 + ((B zh - IZR 63 / 64) + B zl)).
Proof.
  intros Fz Fl L U Hn Hl Hg.
  pose proof (series_segment_a zh zl 63%Z (IZR 856 * bpow radix2 (-76)) ltac:(lia) Fz Fl L U Hn Hl Hg segok_63) as SS.
  cbv zeta in SS. rewrite row_63 in SS. cbn [nth] in SS.
  destruct SS as [h [l [Hs [Fh [Fl' [Nrm [Ht [e1 [ea [E1 [Eea Eq]]]]]]]]]]].
  exists h, l. split; [exact Hs | split; [exact Fh | split; [exact Fl' | split; [exact Nrm | ]]]].
  destruct (word_ok_intro (0x3fe8e17aa99cc05e)%Z false 7003316388937822%positive 53%nat (3501658194468911)%Z 1%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc7ec182ab042f61)%Z true 8657016260407137%positive 108%nat (-8657016260407137)%Z 0%Z (-108)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fe0407ffbefe001)%Z false 4574518059196417%positive 53%nat (4574518059196417)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c401ffefbf80041)%Z false 4538779636858945%positive 111%nat (4538779636858945)%Z 0%Z (-111)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0xbfd03ffbebd00209)%Z true 4573950852989449%positive 54%nat (-4573950852989449)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fb5513a5aaf6d91)%Z false 6000285582323089%positive 56%nat (6000285582323089)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3f60a27fc68aec55)%Z false 4682269302910037%positive 61%nat (4682269302910037)%Z 0%Z (-61)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbf9ba597ccd413e5)%Z true 7781895766283237%positive 58%nat (-7781895766283237)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3f96550bbffc9d9a)%Z false 6285958441639322%positive 58%nat (3142979220819661)%Z 1%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0xbf8238627b7af5be)%Z true 5128545210398142%positive 59%nat (-2564272605199071)%Z 1%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0xbf5c92a58dd97fc1)%Z true 8042539094998977%positive 62%nat (-8042539094998977)%Z 0%Z (-62)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3f70bb146a757f85)%Z false 4709295987195781%positive 60%nat (4709295987195781)%Z 0%Z (-60)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x4021c44cdc0ef9ad)%Z false 5000908992608685%positive 49%nat (5000908992608685)%Z 0%Z (-49)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  unfold seg_poly in Eq.
  pose proof (approx_63 _ _ _ _ _ _ _ _ _ _ _ _ _ ((B zh - IZR 63 / 64) + B zl) V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 Ht) as AP.
  pose proof (amin_63 ((B zh - IZR 63 / 64) + B zl) Ht) as HAm.
  destruct ea_dw_small as [Ea0 Ea1].
  rewrite Eq.
  refine (fast_compose _ _ e1 ea (IZR 10484480 * bpow radix2 (-95)) (IZR 856 * bpow radix2 (-76)) _ (IZR 811115 * bpow radix2 (-20)) _ AP E1 Eea HAm _ Ea0 _).
  - apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0].
  - bpow_num. replace (- prec)%Z with (-53)%Z by reflexivity. bpow_num. clear - Fz. interval with (i_prec 200).
Qed.

Lemma evalcert_64 : EvalCert (IZR (1) * bpow radix2 (-1)) 0 (IZR (-1) * bpow radix2 (-2)) (IZR (6004799503160661) * bpow radix2 (-56)) (IZR (1669622273244265) * bpow radix2 (-124)) (IZR (-7205759403661701) * bpow radix2 (-58)) (IZR (6004799503160659) * bpow radix2 (-58)) (IZR (-643372296146765) * bpow radix2 (-56)) (IZR (2311434041383767) * bpow radix2 (-93)) (IZR (8256992271041247) * bpow radix2 (-61)) (IZR (-7205764053143631) * bpow radix2 (-61)) (IZR 843 * bpow radix2 (-76)) (IZR 692 * bpow radix2 (-73)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 843 (-843) (-76)); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_64.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (atan2_eval_64.l1 th_ tl_ dg).
Qed.

Lemma segok_64 : SegOkRowA [(0x3fe921fb54442d18)%Z; (0x3c81a62633145c07)%Z; (0x3fe0000000000000)%Z; (0x0000000000000000)%Z; (0xbfd0000000000000)%Z; (0x3fb5555555555555)%Z; (0x3b57ba0cea05f1a4)%Z; (0xbf99999999979985)%Z; (0x3f95555555555553)%Z; (0xbf824926495c7a68)%Z; (0x3d506c7959eab6ae)%Z; (0x3f6d55b0d33a82df)%Z; (0xbf69999aaeb9104f)%Z] (IZR 843 * bpow radix2 (-76)).
Proof.
  unfold SegOkRowA. cbn [nth].
  destruct (word_ok_intro (0x3fe921fb54442d18)%Z false 7074237752028440%positive 53%nat (884279719003555)%Z 3%Z (-50)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c81a62633145c07)%Z false 4967757600021511%positive 107%nat (4967757600021511)%Z 0%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fe0000000000000)%Z false 4503599627370496%positive 53%nat (1)%Z 52%Z (-1)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct zero_word as [F3 V3].
  destruct (word_ok_intro (0xbfd0000000000000)%Z true 4503599627370496%positive 54%nat (-1)%Z 52%Z (-2)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fb5555555555555)%Z false 6004799503160661%positive 56%nat (6004799503160661)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3b57ba0cea05f1a4)%Z false 6678489092977060%positive 126%nat (1669622273244265)%Z 2%Z (-124)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbf99999999979985)%Z true 7205759403661701%positive 58%nat (-7205759403661701)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3f95555555555553)%Z false 6004799503160659%positive 58%nat (6004799503160659)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0xbf824926495c7a68)%Z true 5146978369174120%positive 59%nat (-643372296146765)%Z 3%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3d506c7959eab6ae)%Z false 4622868082767534%positive 94%nat (2311434041383767)%Z 1%Z (-93)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3f6d55b0d33a82df)%Z false 8256992271041247%positive 61%nat (8256992271041247)%Z 0%Z (-61)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xbf69999aaeb9104f)%Z true 7205764053143631%positive 61%nat (-7205764053143631)%Z 0%Z (-61)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values_a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_64 _ _).
  all: seg_numeric.
Qed.

Lemma row_64 : nth (Z.to_nat (64%Z - 1)) atan2_segments [] = [(0x3fe921fb54442d18)%Z; (0x3c81a62633145c07)%Z; (0x3fe0000000000000)%Z; (0x0000000000000000)%Z; (0xbfd0000000000000)%Z; (0x3fb5555555555555)%Z; (0x3b57ba0cea05f1a4)%Z; (0xbf99999999979985)%Z; (0x3f95555555555553)%Z; (0xbf824926495c7a68)%Z; (0x3d506c7959eab6ae)%Z; (0x3f6d55b0d33a82df)%Z; (0xbf69999aaeb9104f)%Z].
Proof. reflexivity. Qed.

Lemma fast_64 zh zl : finite zh -> finite zl -> / 128 <= B zh -> B zh <= 1 ->
  Znearest ne (B zh * 64) = 64%Z -> Rabs (B zl) <= bpow radix2 (-53) -> on_grid (-211) (B zl) ->
  exists h l, atan2_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    Rabs (B h + B l - atan (IZR 64 / 64 + ((B zh - IZR 64 / 64) + B zl))) <= bpow radix2 (-63) * atan (IZR 64 / 64 + ((B zh - IZR 64 / 64) + B zl)).
Proof.
  intros Fz Fl L U Hn Hl Hg.
  pose proof (series_segment_a zh zl 64%Z (IZR 843 * bpow radix2 (-76)) ltac:(lia) Fz Fl L U Hn Hl Hg segok_64) as SS.
  cbv zeta in SS. rewrite row_64 in SS. cbn [nth] in SS.
  destruct SS as [h [l [Hs [Fh [Fl' [Nrm [Ht [e1 [ea [E1 [Eea Eq]]]]]]]]]]].
  exists h, l. split; [exact Hs | split; [exact Fh | split; [exact Fl' | split; [exact Nrm | ]]]].
  destruct (word_ok_intro (0x3fe921fb54442d18)%Z false 7074237752028440%positive 53%nat (884279719003555)%Z 3%Z (-50)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c81a62633145c07)%Z false 4967757600021511%positive 107%nat (4967757600021511)%Z 0%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3fe0000000000000)%Z false 4503599627370496%positive 53%nat (1)%Z 52%Z (-1)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct zero_word as [F3 V3].
  destruct (word_ok_intro (0xbfd0000000000000)%Z true 4503599627370496%positive 54%nat (-1)%Z 52%Z (-2)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fb5555555555555)%Z false 6004799503160661%positive 56%nat (6004799503160661)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3b57ba0cea05f1a4)%Z false 6678489092977060%positive 126%nat (1669622273244265)%Z 2%Z (-124)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0xbf99999999979985)%Z true 7205759403661701%positive 58%nat (-7205759403661701)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3f95555555555553)%Z false 6004799503160659%positive 58%nat (6004799503160659)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0xbf824926495c7a68)%Z true 5146978369174120%positive 59%nat (-643372296146765)%Z 3%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3d506c7959eab6ae)%Z false 4622868082767534%positive 94%nat (2311434041383767)%Z 1%Z (-93)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3f6d55b0d33a82df)%Z false 8256992271041247%positive 61%nat (8256992271041247)%Z 0%Z (-61)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xbf69999aaeb9104f)%Z true 7205764053143631%positive 61%nat (-7205764053143631)%Z 0%Z (-61)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  unfold seg_poly in Eq.
  pose proof (approx_64 _ _ _ _ _ _ _ _ _ _ _ _ _ ((B zh - IZR 64 / 64) + B zl) V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 Ht) as AP.
  pose proof (amin_64 ((B zh - IZR 64 / 64) + B zl) Ht) as HAm.
  destruct ea_dw_small as [Ea0 Ea1].
  rewrite Eq.
  refine (fast_compose _ _ e1 ea (IZR 14883246 * bpow radix2 (-105)) (IZR 843 * bpow radix2 (-76)) _ (IZR 819436 * bpow radix2 (-20)) _ AP E1 Eea HAm _ Ea0 _).
  - apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0].
  - bpow_num. replace (- prec)%Z with (-53)%Z by reflexivity. bpow_num. clear - Fz. interval with (i_prec 200).
Qed.

(** The table branch: [k = round (64 zh)] in [1..64], the tail [zl] a double-word low part
    on the [2^-211] grid. *)
Theorem fast_table (k : Z) zh zl : (1 <= k <= 64)%Z -> finite zh -> finite zl -> / 128 <= B zh -> B zh <= 1 ->
  Znearest ne (B zh * 64) = k -> Rabs (B zl) <= bpow radix2 (-53) -> on_grid (-211) (B zl) ->
  exists h l, atan2_series zh zl = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    Rabs (B h + B l - atan (IZR k / 64 + ((B zh - IZR k / 64) + B zl)))
      <= bpow radix2 (-63) * atan (IZR k / 64 + ((B zh - IZR k / 64) + B zl)).
Proof.
  intros Hk Fz Fl L U Hn Hl Hg.
  assert (Hc : k = 1%Z \/ k = 2%Z \/ k = 3%Z \/ k = 4%Z \/ k = 5%Z \/ k = 6%Z \/ k = 7%Z \/ k = 8%Z \/ k = 9%Z \/ k = 10%Z \/ k = 11%Z \/ k = 12%Z \/ k = 13%Z \/ k = 14%Z \/ k = 15%Z \/ k = 16%Z \/ k = 17%Z \/ k = 18%Z \/ k = 19%Z \/ k = 20%Z \/ k = 21%Z \/ k = 22%Z \/ k = 23%Z \/ k = 24%Z \/ k = 25%Z \/ k = 26%Z \/ k = 27%Z \/ k = 28%Z \/ k = 29%Z \/ k = 30%Z \/ k = 31%Z \/ k = 32%Z \/ k = 33%Z \/ k = 34%Z \/ k = 35%Z \/ k = 36%Z \/ k = 37%Z \/ k = 38%Z \/ k = 39%Z \/ k = 40%Z \/ k = 41%Z \/ k = 42%Z \/ k = 43%Z \/ k = 44%Z \/ k = 45%Z \/ k = 46%Z \/ k = 47%Z \/ k = 48%Z \/ k = 49%Z \/ k = 50%Z \/ k = 51%Z \/ k = 52%Z \/ k = 53%Z \/ k = 54%Z \/ k = 55%Z \/ k = 56%Z \/ k = 57%Z \/ k = 58%Z \/ k = 59%Z \/ k = 60%Z \/ k = 61%Z \/ k = 62%Z \/ k = 63%Z \/ k = 64%Z) by lia.
  repeat (destruct Hc as [E | Hc]; [rewrite E in Hn; rewrite E; first [exact (fast_01 zh zl Fz Fl L U Hn Hl Hg) | exact (fast_02 zh zl Fz Fl L U Hn Hl Hg) | exact (fast_03 zh zl Fz Fl L U Hn Hl Hg) | exact (fast_04 zh zl Fz Fl L U Hn Hl Hg) | exact (fast_05 zh zl Fz Fl L U Hn Hl Hg) | exact (fast_06 zh zl Fz Fl L U Hn Hl Hg) | exact (fast_07 zh zl Fz Fl L U Hn Hl Hg) | exact (fast_08 zh zl Fz Fl L U Hn Hl Hg) | exact (fast_09 zh zl Fz Fl L U Hn Hl Hg) | exact (fast_10 zh zl Fz Fl L U Hn Hl Hg) | exact (fast_11 zh zl Fz Fl L U Hn Hl Hg) | exact (fast_12 zh zl Fz Fl L U Hn Hl Hg) | exact (fast_13 zh zl Fz Fl L U Hn Hl Hg) | exact (fast_14 zh zl Fz Fl L U Hn Hl Hg) | exact (fast_15 zh zl Fz Fl L U Hn Hl Hg) | exact (fast_16 zh zl Fz Fl L U Hn Hl Hg) | exact (fast_17 zh zl Fz Fl L U Hn Hl Hg) | exact (fast_18 zh zl Fz Fl L U Hn Hl Hg) | exact (fast_19 zh zl Fz Fl L U Hn Hl Hg) | exact (fast_20 zh zl Fz Fl L U Hn Hl Hg) | exact (fast_21 zh zl Fz Fl L U Hn Hl Hg) | exact (fast_22 zh zl Fz Fl L U Hn Hl Hg) | exact (fast_23 zh zl Fz Fl L U Hn Hl Hg) | exact (fast_24 zh zl Fz Fl L U Hn Hl Hg) | exact (fast_25 zh zl Fz Fl L U Hn Hl Hg) | exact (fast_26 zh zl Fz Fl L U Hn Hl Hg) | exact (fast_27 zh zl Fz Fl L U Hn Hl Hg) | exact (fast_28 zh zl Fz Fl L U Hn Hl Hg) | exact (fast_29 zh zl Fz Fl L U Hn Hl Hg) | exact (fast_30 zh zl Fz Fl L U Hn Hl Hg) | exact (fast_31 zh zl Fz Fl L U Hn Hl Hg) | exact (fast_32 zh zl Fz Fl L U Hn Hl Hg) | exact (fast_33 zh zl Fz Fl L U Hn Hl Hg) | exact (fast_34 zh zl Fz Fl L U Hn Hl Hg) | exact (fast_35 zh zl Fz Fl L U Hn Hl Hg) | exact (fast_36 zh zl Fz Fl L U Hn Hl Hg) | exact (fast_37 zh zl Fz Fl L U Hn Hl Hg) | exact (fast_38 zh zl Fz Fl L U Hn Hl Hg) | exact (fast_39 zh zl Fz Fl L U Hn Hl Hg) | exact (fast_40 zh zl Fz Fl L U Hn Hl Hg) | exact (fast_41 zh zl Fz Fl L U Hn Hl Hg) | exact (fast_42 zh zl Fz Fl L U Hn Hl Hg) | exact (fast_43 zh zl Fz Fl L U Hn Hl Hg) | exact (fast_44 zh zl Fz Fl L U Hn Hl Hg) | exact (fast_45 zh zl Fz Fl L U Hn Hl Hg) | exact (fast_46 zh zl Fz Fl L U Hn Hl Hg) | exact (fast_47 zh zl Fz Fl L U Hn Hl Hg) | exact (fast_48 zh zl Fz Fl L U Hn Hl Hg) | exact (fast_49 zh zl Fz Fl L U Hn Hl Hg) | exact (fast_50 zh zl Fz Fl L U Hn Hl Hg) | exact (fast_51 zh zl Fz Fl L U Hn Hl Hg) | exact (fast_52 zh zl Fz Fl L U Hn Hl Hg) | exact (fast_53 zh zl Fz Fl L U Hn Hl Hg) | exact (fast_54 zh zl Fz Fl L U Hn Hl Hg) | exact (fast_55 zh zl Fz Fl L U Hn Hl Hg) | exact (fast_56 zh zl Fz Fl L U Hn Hl Hg) | exact (fast_57 zh zl Fz Fl L U Hn Hl Hg) | exact (fast_58 zh zl Fz Fl L U Hn Hl Hg) | exact (fast_59 zh zl Fz Fl L U Hn Hl Hg) | exact (fast_60 zh zl Fz Fl L U Hn Hl Hg) | exact (fast_61 zh zl Fz Fl L U Hn Hl Hg) | exact (fast_62 zh zl Fz Fl L U Hn Hl Hg) | exact (fast_63 zh zl Fz Fl L U Hn Hl Hg) | exact (fast_64 zh zl Fz Fl L U Hn Hl Hg)] | ]).
  rewrite Hc in Hn. rewrite Hc. exact (fast_64 zh zl Fz Fl L U Hn Hl Hg).
Qed.
