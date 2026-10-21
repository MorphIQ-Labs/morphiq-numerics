(** Segment-by-segment facts of asin's tables, written by
    generators/asin_certificates.py; do not edit. For each segment k, the
    certificate formal/asin/eval_<kk>.g applied over the table words of
    src/asin/tables.rs, and the numeric facts [SegOkRow] states. *)
From Coq Require Import Reals ZArith Lia Lra Psatz List.
From Flocq Require Import Core.
From Gappa Require Import Gappa_library.
From Interval Require Import Tactic.
Require Import StageGappa AsinTables AsinKernel AsinSegment.
Require asin_eval_01.
Require asin_eval_02.
Require asin_eval_03.
Require asin_eval_04.
Require asin_eval_05.
Require asin_eval_06.
Require asin_eval_07.
Require asin_eval_08.
Require asin_eval_09.
Require asin_eval_10.
Require asin_eval_11.
Require asin_eval_12.
Require asin_eval_13.
Require asin_eval_14.
Require asin_eval_15.
Require asin_eval_16.
Require asin_eval_17.
Require asin_eval_18.
Require asin_eval_19.
Require asin_eval_20.
Require asin_eval_21.
Require asin_eval_22.
Require asin_eval_23.
Require asin_eval_24.
Require asin_eval_25.
Require asin_eval_26.
Require asin_eval_27.
Require asin_eval_28.
Require asin_eval_29.
Require asin_eval_30.
Require asin_eval_31.
Require asin_eval_32.
Require asin_eval_33.
Require asin_eval_34.
Require asin_eval_35.
Require asin_eval_36.
Require asin_eval_37.
Require asin_eval_38.
Require asin_eval_39.
Require asin_eval_40.
Require asin_eval_41.
Require asin_eval_42.
Require asin_eval_43.
Require asin_eval_44.
Require asin_eval_45.
Import ListNotations.
Open Scope R_scope.

Lemma evalcert_01 : EvalCert (IZR (1126037370967041) * bpow radix2 (-50)) (IZR (6772720625608905) * bpow radix2 (-106)) (IZR (4505249398272039) * bpow radix2 (-59)) (IZR (6011399929709017) * bpow radix2 (-55)) (IZR (3381137750625937) * bpow radix2 (-59)) (IZR (2710414339854473) * bpow radix2 (-55)) (IZR (705090610717565) * bpow radix2 (-57)) (IZR (6472263933108925) * bpow radix2 (-57)) (IZR (5159111431375361) * bpow radix2 (-60)) (IZR (4389957216634859) * bpow radix2 (-57)) (IZR (-769501581422205) * bpow radix2 (-49)) (IZR 604 * bpow radix2 (-80)) (IZR 693 * bpow radix2 (-72)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 151 (-151) (-78)); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_01.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_01.l1 th_ tl_ dg).
Qed.

Lemma segok_01 : SegOkRow [(0x3f90002aabdde94c)%Z; (0x3c1130cd26cdfa37)%Z; (0x3ff0008006005004)%Z; (0x3c980fc0e70d68c9)%Z; (0x3f8001801e023027)%Z; (0x3fc55b561d69c1d9)%Z; (0x3f780640f5201d22)%Z; (0x3fb3423707d7a112)%Z; (0x3f740a359b171be8)%Z; (0x3fa6fe7d60a022bd)%Z; (0x3f72542f3c394a01)%Z; (0x3f9f314920f40fd6)%Z; (0xbff5dedc635173e8)%Z] (IZR 604 * bpow radix2 (-80)).
Proof.
  unfold SegOkRow. cbn [nth].
  destruct (word_ok_intro (0x3f90002aabdde94c)%Z false 4503782899444044%positive 58%nat (1125945724861011)%Z 2%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c1130cd26cdfa37)%Z false 4838732281543223%positive 114%nat (4838732281543223)%Z 0%Z (-114)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3ff0008006005004)%Z false 4504149483868164%positive 52%nat (1126037370967041)%Z 2%Z (-50)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c980fc0e70d68c9)%Z false 6772720625608905%positive 106%nat (6772720625608905)%Z 0%Z (-106)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0x3f8001801e023027)%Z false 4505249398272039%positive 59%nat (4505249398272039)%Z 0%Z (-59)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fc55b561d69c1d9)%Z false 6011399929709017%positive 55%nat (6011399929709017)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3f780640f5201d22)%Z false 6762275501251874%positive 60%nat (3381137750625937)%Z 1%Z (-59)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3fb3423707d7a112)%Z false 5420828679708946%positive 56%nat (2710414339854473)%Z 1%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3f740a359b171be8)%Z false 5640724885740520%positive 60%nat (705090610717565)%Z 3%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3fa6fe7d60a022bd)%Z false 6472263933108925%positive 57%nat (6472263933108925)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3f72542f3c394a01)%Z false 5159111431375361%positive 60%nat (5159111431375361)%Z 0%Z (-60)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3f9f314920f40fd6)%Z false 8779914433269718%positive 58%nat (4389957216634859)%Z 1%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xbff5dedc635173e8)%Z true 6156012651377640%positive 52%nat (-769501581422205)%Z 3%Z (-49)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_01 _ _).
  all: seg_numeric.
Qed.

Lemma evalcert_02 : EvalCert (IZR (4505800262550625) * bpow radix2 (-52)) (IZR (-8498763825352503) * bpow radix2 (-111)) (IZR (4510204759385963) * bpow radix2 (-58)) (IZR (6031241555073311) * bpow radix2 (-55)) (IZR (6782953122433409) * bpow radix2 (-59)) (IZR (2735277006179843) * bpow radix2 (-55)) (IZR (5674578463174089) * bpow radix2 (-59)) (IZR (6588663934042381) * bpow radix2 (-57)) (IZR (2450422438503577) * bpow radix2 (-58)) (IZR (4554878066920787) * bpow radix2 (-57)) (IZR (5171806696599027) * bpow radix2 (-52)) (IZR 562 * bpow radix2 (-79)) (IZR 696 * bpow radix2 (-72)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 281 (-281) (-78)); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_02.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_02.l1 th_ tl_ dg).
Qed.

Lemma segok_02 : SegOkRow [(0x3fa000aabde0b9c8)%Z; (0x3c2d6d94551be3e9)%Z; (0x3ff0020060140461)%Z; (0xbc4e3194a6d70f37)%Z; (0x3f900601e08c276b)%Z; (0x3fc56d61da71d91f)%Z; (0x3f88190f57640981)%Z; (0x3fb36f709ca19c06)%Z; (0x3f8428ffc18c2dc9)%Z; (0x3fa7685add55410d)%Z; (0x3f81694addfe4932)%Z; (0x3fa02ea3312c8d53)%Z; (0x3ff25fbb14ff6df3)%Z] (IZR 562 * bpow radix2 (-79)).
Proof.
  unfold SegOkRow. cbn [nth].
  destruct (word_ok_intro (0x3fa000aabde0b9c8)%Z false 4504332957432264%positive 57%nat (563041619679033)%Z 3%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c2d6d94551be3e9)%Z false 8283258175087593%positive 113%nat (8283258175087593)%Z 0%Z (-113)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3ff0020060140461)%Z false 4505800262550625%positive 52%nat (4505800262550625)%Z 0%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc4e3194a6d70f37)%Z true 8498763825352503%positive 111%nat (-8498763825352503)%Z 0%Z (-111)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0x3f900601e08c276b)%Z false 4510204759385963%positive 58%nat (4510204759385963)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fc56d61da71d91f)%Z false 6031241555073311%positive 55%nat (6031241555073311)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3f88190f57640981)%Z false 6782953122433409%positive 59%nat (6782953122433409)%Z 0%Z (-59)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3fb36f709ca19c06)%Z false 5470554012359686%positive 56%nat (2735277006179843)%Z 1%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3f8428ffc18c2dc9)%Z false 5674578463174089%positive 59%nat (5674578463174089)%Z 0%Z (-59)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3fa7685add55410d)%Z false 6588663934042381%positive 57%nat (6588663934042381)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3f81694addfe4932)%Z false 4900844877007154%positive 59%nat (2450422438503577)%Z 1%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3fa02ea3312c8d53)%Z false 4554878066920787%positive 57%nat (4554878066920787)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x3ff25fbb14ff6df3)%Z false 5171806696599027%positive 52%nat (5171806696599027)%Z 0%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_02 _ _).
  all: seg_numeric.
Qed.

Lemma evalcert_03 : EvalCert (IZR (4508555598381145) * bpow radix2 (-52)) (IZR (4568242766441471) * bpow radix2 (-106)) (IZR (211803933175723) * bpow radix2 (-53)) (IZR (3032222950245231) * bpow radix2 (-54)) (IZR (5113185997534887) * bpow radix2 (-58)) (IZR (1388523334125217) * bpow radix2 (-54)) (IZR (4298567617008109) * bpow radix2 (-58)) (IZR (848155880411463) * bpow radix2 (-54)) (IZR (59035705554335) * bpow radix2 (-52)) (IZR (2369686360596989) * bpow radix2 (-56)) (IZR (1570493318319017) * bpow radix2 (-51)) (IZR 822 * bpow radix2 (-79)) (IZR 700 * bpow radix2 (-72)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 411 (-411) (-78)); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_03.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_03.l1 th_ tl_ dg).
Qed.

Lemma segok_03 : SegOkRow [(0x3fa8024091fdb0a9)%Z; (0x3c380650020adbca)%Z; (0x3ff00481e6e44059)%Z; (0x3c903acae7576bff)%Z; (0x3f98144e465df560)%Z; (0x3fc58b94d7a886de)%Z; (0x3f922a6a630db6a7)%Z; (0x3fb3bb6b205f1a84)%Z; (0x3f8e8b0c87b5a3da)%Z; (0x3fa81b256fba8a38)%Z; (0x3f8ad8a9211acf80)%Z; (0x3fa0d66f338143fa)%Z; (0x3fe6516be1712ea4)%Z] (IZR 822 * bpow radix2 (-79)).
Proof.
  unfold SegOkRow. cbn [nth].
  destruct (word_ok_intro (0x3fa8024091fdb0a9)%Z false 6757875791540393%positive 57%nat (6757875791540393)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c380650020adbca)%Z false 6762340142472138%positive 112%nat (3381170071236069)%Z 1%Z (-111)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3ff00481e6e44059)%Z false 4508555598381145%positive 52%nat (4508555598381145)%Z 0%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c903acae7576bff)%Z false 4568242766441471%positive 106%nat (4568242766441471)%Z 0%Z (-106)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0x3f98144e465df560)%Z false 6777725861623136%positive 58%nat (211803933175723)%Z 5%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fc58b94d7a886de)%Z false 6064445900490462%positive 55%nat (3032222950245231)%Z 1%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3f922a6a630db6a7)%Z false 5113185997534887%positive 58%nat (5113185997534887)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3fb3bb6b205f1a84)%Z false 5554093336500868%positive 56%nat (1388523334125217)%Z 2%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3f8e8b0c87b5a3da)%Z false 8597135234016218%positive 59%nat (4298567617008109)%Z 1%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3fa81b256fba8a38)%Z false 6785247043291704%positive 57%nat (848155880411463)%Z 3%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3f8ad8a9211acf80)%Z false 7556570310954880%positive 59%nat (59035705554335)%Z 7%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3fa0d66f338143fa)%Z false 4739372721193978%positive 57%nat (2369686360596989)%Z 1%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x3fe6516be1712ea4)%Z false 6281973273276068%positive 53%nat (1570493318319017)%Z 2%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_03 _ _).
  all: seg_numeric.
Qed.

Lemma evalcert_04 : EvalCert (IZR (1128105393592573) * bpow radix2 (-50)) (IZR (-6800162284299809) * bpow radix2 (-106)) (IZR (4530117345250175) * bpow radix2 (-57)) (IZR (6111217124572785) * bpow radix2 (-55)) (IZR (858301356307651) * bpow radix2 (-55)) (IZR (709057022684735) * bpow radix2 (-53)) (IZR (5811956754621423) * bpow radix2 (-58)) (IZR (7065931195228945) * bpow radix2 (-57)) (IZR (2629417887522087) * bpow radix2 (-57)) (IZR (1280965164106671) * bpow radix2 (-55)) (IZR (-7551129699268327) * bpow radix2 (-52)) (IZR 543 * bpow radix2 (-78)) (IZR 706 * bpow radix2 (-72)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 543 (-543) (-78)); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_04.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_04.l1 th_ tl_ dg).
Qed.

Lemma segok_04 : SegOkRow [(0x3fb002abde953619)%Z; (0x3c5182e2dc6ddeed)%Z; (0x3ff00806050463f4)%Z; (0xbc9828b6295ee621)%Z; (0x3fa0181e23278b7f)%Z; (0x3fc5b61e9ddafe71)%Z; (0x3f9864f6db9fa618)%Z; (0x3fb427119fb371f8)%Z; (0x3f94a5f1a1cf23ef)%Z; (0x3fa91a6d4ee62311)%Z; (0x3f92aee21e4dba4e)%Z; (0x3fa2341fc64e0ebc)%Z; (0xbffad3b66360b6e7)%Z] (IZR 543 * bpow radix2 (-78)).
Proof.
  unfold SegOkRow. cbn [nth].
  destruct (word_ok_intro (0x3fb002abde953619)%Z false 4506536824354329%positive 56%nat (4506536824354329)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c5182e2dc6ddeed)%Z false 4928985476488941%positive 110%nat (4928985476488941)%Z 0%Z (-110)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3ff00806050463f4)%Z false 4512421574370292%positive 52%nat (1128105393592573)%Z 2%Z (-50)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc9828b6295ee621)%Z true 6800162284299809%positive 106%nat (-6800162284299809)%Z 0%Z (-106)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0x3fa0181e23278b7f)%Z false 4530117345250175%positive 57%nat (4530117345250175)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fc5b61e9ddafe71)%Z false 6111217124572785%positive 55%nat (6111217124572785)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3f9864f6db9fa618)%Z false 6866410850461208%positive 58%nat (858301356307651)%Z 3%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3fb427119fb371f8)%Z false 5672456181477880%positive 56%nat (709057022684735)%Z 3%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3f94a5f1a1cf23ef)%Z false 5811956754621423%positive 58%nat (5811956754621423)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3fa91a6d4ee62311)%Z false 7065931195228945%positive 57%nat (7065931195228945)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3f92aee21e4dba4e)%Z false 5258835775044174%positive 58%nat (2629417887522087)%Z 1%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3fa2341fc64e0ebc)%Z false 5123860656426684%positive 57%nat (1280965164106671)%Z 2%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xbffad3b66360b6e7)%Z true 7551129699268327%positive 52%nat (-7551129699268327)%Z 0%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_04 _ _).
  all: seg_numeric.
Qed.

Lemma evalcert_05 : EvalCert (IZR (4517406758996121) * bpow radix2 (-52)) (IZR (-5097144788332017) * bpow radix2 (-108)) (IZR (5681435177121135) * bpow radix2 (-57)) (IZR (771480561511315) * bpow radix2 (-52)) (IZR (8662247121360415) * bpow radix2 (-58)) (IZR (5827084061175837) * bpow radix2 (-56)) (IZR (3698232099254743) * bpow radix2 (-57)) (IZR (14524256662937) * bpow radix2 (-48)) (IZR (6486473084075553) * bpow radix2 (-58)) (IZR (5506244840117563) * bpow radix2 (-57)) (IZR (5637488977063009) * bpow radix2 (-50)) (IZR 675 * bpow radix2 (-78)) (IZR 713 * bpow radix2 (-72)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 675 (-675) (-78)); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_05.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_05.l1 th_ tl_ dg).
Qed.

Lemma segok_05 : SegOkRow [(0x3fb405390240e6fd)%Z; (0x3c51ed0159037972)%Z; (0x3ff00c8eb92d0899)%Z; (0xbc721bd3807a2df1)%Z; (0x3fa42f3c358bf56f)%Z; (0x3fc5ed42868f5c98)%Z; (0x3f9ec64492a0161f)%Z; (0x3fb4b3b3bb8af01d)%Z; (0x3f9a470b852563ae)%Z; (0x3faa6b62516b3200)%Z; (0x3f970b69b4057e21)%Z; (0x3fa38fe687bdd53b)%Z; (0x401407442fe72c61)%Z] (IZR 675 * bpow radix2 (-78)).
Proof.
  unfold SegOkRow. cbn [nth].
  destruct (word_ok_intro (0x3fb405390240e6fd)%Z false 5635241943295741%positive 56%nat (5635241943295741)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c51ed0159037972)%Z false 5045664648231282%positive 110%nat (2522832324115641)%Z 1%Z (-109)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3ff00c8eb92d0899)%Z false 4517406758996121%positive 52%nat (4517406758996121)%Z 0%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc721bd3807a2df1)%Z true 5097144788332017%positive 108%nat (-5097144788332017)%Z 0%Z (-108)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0x3fa42f3c358bf56f)%Z false 5681435177121135%positive 57%nat (5681435177121135)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fc5ed42868f5c98)%Z false 6171844492090520%positive 55%nat (771480561511315)%Z 3%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3f9ec64492a0161f)%Z false 8662247121360415%positive 58%nat (8662247121360415)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3fb4b3b3bb8af01d)%Z false 5827084061175837%positive 56%nat (5827084061175837)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3f9a470b852563ae)%Z false 7396464198509486%positive 58%nat (3698232099254743)%Z 1%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3faa6b62516b3200)%Z false 7436419411423744%positive 57%nat (14524256662937)%Z 9%Z (-48)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3f970b69b4057e21)%Z false 6486473084075553%positive 58%nat (6486473084075553)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3fa38fe687bdd53b)%Z false 5506244840117563%positive 57%nat (5506244840117563)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x401407442fe72c61)%Z false 5637488977063009%positive 50%nat (5637488977063009)%Z 0%Z (-50)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_05 _ _).
  all: seg_numeric.
Qed.

Lemma evalcert_06 : EvalCert (IZR (4523522259223879) * bpow radix2 (-52)) (IZR (-4357064405925269) * bpow radix2 (-105)) (IZR (53480066118903) * bpow radix2 (-50)) (IZR (780838237402825) * bpow radix2 (-52)) (IZR (5256156230207593) * bpow radix2 (-57)) (IZR (3009939830227179) * bpow radix2 (-55)) (IZR (4536248364932311) * bpow radix2 (-57)) (IZR (7904282598378947) * bpow radix2 (-57)) (IZR (8114613892451433) * bpow radix2 (-58)) (IZR (6065208514334213) * bpow radix2 (-57)) (IZR (2847113355957759) * bpow radix2 (-49)) (IZR 809 * bpow radix2 (-78)) (IZR 722 * bpow radix2 (-72)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 809 (-809) (-78)); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_06.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_06.l1 th_ tl_ dg).
Qed.

Lemma segok_06 : SegOkRow [(0x3fb809092913e52e)%Z; (0x3c3cf6b1f9befb16)%Z; (0x3ff0121e99650547)%Z; (0xbc9ef574385b7b2a)%Z; (0x3fa851e62bfa7b80)%Z; (0x3fc631588e23b648)%Z; (0x3fa2ac723cfc4869)%Z; (0x3fb5630c74c081d6)%Z; (0x3fa01db1a0679cd7)%Z; (0x3fac14e7347b0dc3)%Z; (0x3f9cd432c68c8c69)%Z; (0x3fa58c4666fc4e05)%Z; (0x40143ade786f2bfe)%Z] (IZR 809 * bpow radix2 (-78)).
Proof.
  unfold SegOkRow. cbn [nth].
  destruct (word_ok_intro (0x3fb809092913e52e)%Z false 6765334389581102%positive 56%nat (3382667194790551)%Z 1%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c3cf6b1f9befb16)%Z false 8152543607585558%positive 112%nat (4076271803792779)%Z 1%Z (-111)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3ff0121e99650547)%Z false 4523522259223879%positive 52%nat (4523522259223879)%Z 0%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc9ef574385b7b2a)%Z true 8714128811850538%positive 106%nat (-4357064405925269)%Z 1%Z (-105)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0x3fa851e62bfa7b80)%Z false 6845448463219584%positive 57%nat (53480066118903)%Z 7%Z (-50)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fc631588e23b648)%Z false 6246705899222600%positive 55%nat (780838237402825)%Z 3%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fa2ac723cfc4869)%Z false 5256156230207593%positive 57%nat (5256156230207593)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3fb5630c74c081d6)%Z false 6019879660454358%positive 56%nat (3009939830227179)%Z 1%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3fa01db1a0679cd7)%Z false 4536248364932311%positive 57%nat (4536248364932311)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3fac14e7347b0dc3)%Z false 7904282598378947%positive 57%nat (7904282598378947)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3f9cd432c68c8c69)%Z false 8114613892451433%positive 58%nat (8114613892451433)%Z 0%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3fa58c4666fc4e05)%Z false 6065208514334213%positive 57%nat (6065208514334213)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x40143ade786f2bfe)%Z false 5694226711915518%positive 50%nat (2847113355957759)%Z 1%Z (-49)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_06 _ _).
  all: seg_numeric.
Qed.

Lemma evalcert_07 : EvalCert (IZR (566347723721473) * bpow radix2 (-49)) (IZR (6185128859481527) * bpow radix2 (-108)) (IZR (4012434379674345) * bpow radix2 (-56)) (IZR (1584068131677005) * bpow radix2 (-53)) (IZR (6214448053513121) * bpow radix2 (-57)) (IZR (6253245849272579) * bpow radix2 (-56)) (IZR (2715595832258703) * bpow radix2 (-56)) (IZR (8479263250366673) * bpow radix2 (-57)) (IZR (5051912482551943) * bpow radix2 (-57)) (IZR (1692639193815033) * bpow radix2 (-55)) (IZR (7118056182831249) * bpow radix2 (-54)) (IZR 945 * bpow radix2 (-78)) (IZR 733 * bpow radix2 (-72)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 945 (-945) (-78)); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_07.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_07.l1 th_ tl_ dg).
Qed.

Lemma segok_07 : SegOkRow [(0x3fbc0e5e80f7172d)%Z; (0x3c5d8eeba8bc0030)%Z; (0x3ff018b8d7225808)%Z; (0x3c75f957888f35b7)%Z; (0x3fac82935bc525d2)%Z; (0x3fc682ce69278d34)%Z; (0x3fa61401f0b46ba1)%Z; (0x3fb6374b418a0103)%Z; (0x3fa34ba3d9dee11e)%Z; (0x3fae1fd851fec0d1)%Z; (0x3fa1f2b008f57887)%Z; (0x3fa80dc917855fe4)%Z; (0x3fd949d59a44d891)%Z] (IZR 945 * bpow radix2 (-78)).
Proof.
  unfold SegOkRow. cbn [nth].
  destruct (word_ok_intro (0x3fbc0e5e80f7172d)%Z false 7897098401290029%positive 56%nat (7897098401290029)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c5d8eeba8bc0030)%Z false 8319917123960880%positive 110%nat (519994820247555)%Z 4%Z (-106)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3ff018b8d7225808)%Z false 4530781789771784%positive 52%nat (566347723721473)%Z 3%Z (-49)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c75f957888f35b7)%Z false 6185128859481527%positive 108%nat (6185128859481527)%Z 0%Z (-108)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0x3fac82935bc525d2)%Z false 8024868759348690%positive 57%nat (4012434379674345)%Z 1%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fc682ce69278d34)%Z false 6336272526708020%positive 55%nat (1584068131677005)%Z 2%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fa61401f0b46ba1)%Z false 6214448053513121%positive 57%nat (6214448053513121)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3fb6374b418a0103)%Z false 6253245849272579%positive 56%nat (6253245849272579)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3fa34ba3d9dee11e)%Z false 5431191664517406%positive 57%nat (2715595832258703)%Z 1%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3fae1fd851fec0d1)%Z false 8479263250366673%positive 57%nat (8479263250366673)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3fa1f2b008f57887)%Z false 5051912482551943%positive 57%nat (5051912482551943)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3fa80dc917855fe4)%Z false 6770556775260132%positive 57%nat (1692639193815033)%Z 2%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x3fd949d59a44d891)%Z false 7118056182831249%positive 54%nat (7118056182831249)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_07 _ _).
  all: seg_numeric.
Qed.

Lemma evalcert_08 : EvalCert (IZR (2269600879738189) * bpow radix2 (-51)) (IZR (-5599664444214413) * bpow radix2 (-106)) (IZR (576406572631921) * bpow radix2 (-53)) (IZR (6441114716394799) * bpow radix2 (-55)) (IZR (7212561356226845) * bpow radix2 (-57)) (IZR (3265067867187775) * bpow radix2 (-55)) (IZR (6395433731352679) * bpow radix2 (-57)) (IZR (2293386867470157) * bpow radix2 (-55)) (IZR (745411088331103) * bpow radix2 (-54)) (IZR (959113422211695) * bpow radix2 (-54)) (IZR (1523183162926223) * bpow radix2 (-48)) (IZR 542 * bpow radix2 (-77)) (IZR 746 * bpow radix2 (-72)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 271 (-271) (-76)); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_08.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_08.l1 th_ tl_ dg).
Qed.

Lemma segok_08 : SegOkRow [(0x3fc00abe0c129e1e)%Z; (0x3c37ceb0ee49d42a)%Z; (0x3ff02061446ffa9a)%Z; (0xbc93e4dd7a0f0c8d)%Z; (0x3fb061e8e8103b88)%Z; (0x3fc6e228e2a0d52f)%Z; (0x3fa99fc94d8f011d)%Z; (0x3fb7331fb4c8547e)%Z; (0x3fa6b89cf3bde867)%Z; (0x3fb04ba57b22de9a)%Z; (0x3fa52f94590d8af8)%Z; (0x3fab4277f6a45378)%Z; (0x4015a54edd6a923c)%Z] (IZR 542 * bpow radix2 (-77)).
Proof.
  unfold SegOkRow. cbn [nth].
  destruct (word_ok_intro (0x3fc00abe0c129e1e)%Z false 4515410989981214%positive 55%nat (2257705494990607)%Z 1%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c37ceb0ee49d42a)%Z false 6701183771726890%positive 112%nat (3350591885863445)%Z 1%Z (-111)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3ff02061446ffa9a)%Z false 4539201759476378%positive 52%nat (2269600879738189)%Z 1%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc93e4dd7a0f0c8d)%Z true 5599664444214413%positive 106%nat (-5599664444214413)%Z 0%Z (-106)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0x3fb061e8e8103b88)%Z false 4611252581055368%positive 56%nat (576406572631921)%Z 3%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fc6e228e2a0d52f)%Z false 6441114716394799%positive 55%nat (6441114716394799)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fa99fc94d8f011d)%Z false 7212561356226845%positive 57%nat (7212561356226845)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3fb7331fb4c8547e)%Z false 6530135734375550%positive 56%nat (3265067867187775)%Z 1%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3fa6b89cf3bde867)%Z false 6395433731352679%positive 57%nat (6395433731352679)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3fb04ba57b22de9a)%Z false 4586773734940314%positive 56%nat (2293386867470157)%Z 1%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3fa52f94590d8af8)%Z false 5963288706648824%positive 57%nat (745411088331103)%Z 3%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3fab4277f6a45378)%Z false 7672907377693560%positive 57%nat (959113422211695)%Z 3%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x4015a54edd6a923c)%Z false 6092732651704892%positive 50%nat (1523183162926223)%Z 2%Z (-48)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_08 _ _).
  all: seg_numeric.
Qed.

Lemma evalcert_09 : EvalCert (IZR (4548801375835321) * bpow radix2 (-52)) (IZR (-7196522371567301) * bpow radix2 (-106)) (IZR (652580222286711) * bpow radix2 (-53)) (IZR (6561909193701257) * bpow radix2 (-55)) (IZR (2064391716093195) * bpow radix2 (-55)) (IZR (6854115320369491) * bpow radix2 (-56)) (IZR (465174986871869) * bpow radix2 (-53)) (IZR (5001092651520301) * bpow radix2 (-56)) (IZR (7213954632421331) * bpow radix2 (-57)) (IZR (8659056216241305) * bpow radix2 (-57)) (IZR (1359517317361463) * bpow radix2 (-62)) (IZR 612 * bpow radix2 (-77)) (IZR 760 * bpow radix2 (-72)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 153 (-153) (-75)); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_09.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_09.l1 th_ tl_ dg).
Qed.

Lemma segok_09 : SegOkRow [(0x3fc20f530308cc20)%Z; (0xbc6ed63934b583b4)%Z; (0x3ff0291c5a2914b9)%Z; (0xbc999132ef934ec5)%Z; (0x3fb28c2562b1dbb8)%Z; (0x3fc750058a89f789)%Z; (0x3fad56369ba8f42c)%Z; (0x3fb859c814eb9153)%Z; (0x3faa712fdd9d43d0)%Z; (0x3fb1c4779efb912d)%Z; (0x3fa9a10db34a8fd3)%Z; (0x3faec35da1dbf499)%Z; (0x3f3351e52b11bcdc)%Z] (IZR 612 * bpow radix2 (-77)).
Proof.
  unfold SegOkRow. cbn [nth].
  destruct (word_ok_intro (0x3fc20f530308cc20)%Z false 5083398788402208%positive 55%nat (158856212137569)%Z 5%Z (-50)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc6ed63934b583b4)%Z true 8679790487110580%positive 109%nat (-2169947621777645)%Z 2%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3ff0291c5a2914b9)%Z false 4548801375835321%positive 52%nat (4548801375835321)%Z 0%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc999132ef934ec5)%Z true 7196522371567301%positive 106%nat (-7196522371567301)%Z 0%Z (-106)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0x3fb28c2562b1dbb8)%Z false 5220641778293688%positive 56%nat (652580222286711)%Z 3%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fc750058a89f789)%Z false 6561909193701257%positive 55%nat (6561909193701257)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fad56369ba8f42c)%Z false 8257566864372780%positive 57%nat (2064391716093195)%Z 2%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3fb859c814eb9153)%Z false 6854115320369491%positive 56%nat (6854115320369491)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3faa712fdd9d43d0)%Z false 7442799789949904%positive 57%nat (465174986871869)%Z 4%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3fb1c4779efb912d)%Z false 5001092651520301%positive 56%nat (5001092651520301)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3fa9a10db34a8fd3)%Z false 7213954632421331%positive 57%nat (7213954632421331)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3faec35da1dbf499)%Z false 8659056216241305%positive 57%nat (8659056216241305)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x3f3351e52b11bcdc)%Z false 5438069269445852%positive 64%nat (1359517317361463)%Z 2%Z (-62)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_09 _ _).
  all: seg_numeric.
Qed.

Lemma evalcert_10 : EvalCert (IZR (1139900692263115) * bpow radix2 (-50)) (IZR (3887429065679749) * bpow radix2 (-108)) (IZR (2921066839032607) * bpow radix2 (-55)) (IZR (3349723894690445) * bpow radix2 (-54)) (IZR (584821581316745) * bpow radix2 (-53)) (IZR (3614720398617367) * bpow radix2 (-55)) (IZR (4294483681742503) * bpow radix2 (-56)) (IZR (2745881703779187) * bpow radix2 (-55)) (IZR (8565032463280933) * bpow radix2 (-57)) (IZR (4975253597752989) * bpow radix2 (-56)) (IZR (-2592746993424111) * bpow radix2 (-50)) (IZR 683 * bpow radix2 (-77)) (IZR 776 * bpow radix2 (-72)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 683 (-683) (-77)); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_10.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_10.l1 th_ tl_ dg).
Qed.

Lemma segok_10 : SegOkRow [(0x3fc41510cb011423)%Z; (0xbc515d675180eda8)%Z; (0x3ff032ef3f5dc32c)%Z; (0x3c6b9f313919470a)%Z; (0x3fb4c163be9c863e)%Z; (0x3fc7cd1cbdad651a)%Z; (0x3fb09f2314e41448)%Z; (0x3fb9af235aa4d62e)%Z; (0x3fae839eccb01d4e)%Z; (0x3fb382bacf1916e6)%Z; (0x3fae6dda0576ab25)%Z; (0x3fb1acf77f5c8e9d)%Z; (0xc0026c2de7122dde)%Z] (IZR 683 * bpow radix2 (-77)).
Proof.
  unfold SegOkRow. cbn [nth].
  destruct (word_ok_intro (0x3fc41510cb011423)%Z false 5652661403718691%positive 55%nat (5652661403718691)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc515d675180eda8)%Z true 4887772934499752%positive 110%nat (-610971616812469)%Z 3%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3ff032ef3f5dc32c)%Z false 4559602769052460%positive 52%nat (1139900692263115)%Z 2%Z (-50)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c6b9f313919470a)%Z false 7774858131359498%positive 109%nat (3887429065679749)%Z 1%Z (-108)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0x3fb4c163be9c863e)%Z false 5842133678065214%positive 56%nat (2921066839032607)%Z 1%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fc7cd1cbdad651a)%Z false 6699447789380890%positive 55%nat (3349723894690445)%Z 1%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fb09f2314e41448)%Z false 4678572650533960%positive 56%nat (584821581316745)%Z 3%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3fb9af235aa4d62e)%Z false 7229440797234734%positive 56%nat (3614720398617367)%Z 1%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3fae839eccb01d4e)%Z false 8588967363485006%positive 57%nat (4294483681742503)%Z 1%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3fb382bacf1916e6)%Z false 5491763407558374%positive 56%nat (2745881703779187)%Z 1%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3fae6dda0576ab25)%Z false 8565032463280933%positive 57%nat (8565032463280933)%Z 0%Z (-57)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3fb1acf77f5c8e9d)%Z false 4975253597752989%positive 56%nat (4975253597752989)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc0026c2de7122dde)%Z true 5185493986848222%positive 51%nat (-2592746993424111)%Z 1%Z (-50)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_10 _ _).
  all: seg_numeric.
Qed.

Lemma evalcert_11 : EvalCert (IZR (4571631137185043) * bpow radix2 (-52)) (IZR (-8045827140788093) * bpow radix2 (-111)) (IZR (3238670008129077) * bpow radix2 (-55)) (IZR (3427323924897625) * bpow radix2 (-54)) (IZR (1314962795670395) * bpow radix2 (-54)) (IZR (7661152995987803) * bpow radix2 (-56)) (IZR (4925911566934313) * bpow radix2 (-56)) (IZR (6069959352126049) * bpow radix2 (-56)) (IZR (2503126283513649) * bpow radix2 (-55)) (IZR (2865473322349421) * bpow radix2 (-55)) (IZR (8130831088764329) * bpow radix2 (-54)) (IZR 757 * bpow radix2 (-77)) (IZR 795 * bpow radix2 (-72)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 757 (-757) (-77)); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_11.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_11.l1 th_ tl_ dg).
Qed.

Lemma segok_11 : SegOkRow [(0x3fc61c1ab9d55d30)%Z; (0xbc695a37debb0f64)%Z; (0x3ff03ddfd1f9dd13)%Z; (0xbc4c95a31ca69f7d)%Z; (0x3fb7031b3ec22c6a)%Z; (0x3fc85a441225beb2)%Z; (0x3fb2afce8950adec)%Z; (0x3fbb37c72ee5515b)%Z; (0x3fb1801729246129)%Z; (0x3fb590988afc0a61)%Z; (0x3fb1c92901e9de62)%Z; (0x3fb45c43fefbe6da)%Z; (0x3fdce2f2a2c645a9)%Z] (IZR 757 * bpow radix2 (-77)).
Proof.
  unfold SegOkRow. cbn [nth].
  destruct (word_ok_intro (0x3fc61c1ab9d55d30)%Z false 6223350600129840%positive 55%nat (388959412508115)%Z 4%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc695a37debb0f64)%Z true 7136070424268644%positive 109%nat (-1784017606067161)%Z 2%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3ff03ddfd1f9dd13)%Z false 4571631137185043%positive 52%nat (4571631137185043)%Z 0%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc4c95a31ca69f7d)%Z true 8045827140788093%positive 111%nat (-8045827140788093)%Z 0%Z (-111)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0x3fb7031b3ec22c6a)%Z false 6477340016258154%positive 56%nat (3238670008129077)%Z 1%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fc85a441225beb2)%Z false 6854647849795250%positive 55%nat (3427323924897625)%Z 1%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fb2afce8950adec)%Z false 5259851182681580%positive 56%nat (1314962795670395)%Z 2%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3fbb37c72ee5515b)%Z false 7661152995987803%positive 56%nat (7661152995987803)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3fb1801729246129)%Z false 4925911566934313%positive 56%nat (4925911566934313)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3fb590988afc0a61)%Z false 6069959352126049%positive 56%nat (6069959352126049)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3fb1c92901e9de62)%Z false 5006252567027298%positive 56%nat (2503126283513649)%Z 1%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3fb45c43fefbe6da)%Z false 5730946644698842%positive 56%nat (2865473322349421)%Z 1%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x3fdce2f2a2c645a9)%Z false 8130831088764329%positive 54%nat (8130831088764329)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_11 _ _).
  all: seg_numeric.
Qed.

Lemma evalcert_12 : EvalCert (IZR (4584914914302779) * bpow radix2 (-52)) (IZR (1950688671142495) * bpow radix2 (-104)) (IZR (1781991221753307) * bpow radix2 (-54)) (IZR (7028564566951415) * bpow radix2 (-55)) (IZR (1469312501743905) * bpow radix2 (-54)) (IZR (8155192213350935) * bpow radix2 (-56)) (IZR (5625969837372671) * bpow radix2 (-56)) (IZR (6749209287842715) * bpow radix2 (-56)) (IZR (5864224426708327) * bpow radix2 (-56)) (IZR (6668196914247527) * bpow radix2 (-56)) (IZR (3749877629424639) * bpow radix2 (-51)) (IZR 832 * bpow radix2 (-77)) (IZR 815 * bpow radix2 (-72)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 13 (-13) (-71)); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_12.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_12.l1 th_ tl_ dg).
Qed.

Lemma segok_12 : SegOkRow [(0x3fc82494ed0e78fc)%Z; (0xbc6443c2697a7d2f)%Z; (0x3ff049f4b0cadb3b)%Z; (0x3c9bb890653e497c)%Z; (0x3fb952d8a70fd76c)%Z; (0x3fc8f871364b45f7)%Z; (0x3fb4e153e6ec0484)%Z; (0x3fbcf91aa6f3aa17)%Z; (0x3fb3fcca2dac74ff)%Z; (0x3fb7fa5ebe1ddb9b)%Z; (0x3fb4d57b25d64d67)%Z; (0x3fb7b0b0945db767)%Z; (0x3ffaa4fcd81b27fe)%Z] (IZR 832 * bpow radix2 (-77)).
Proof.
  unfold SegOkRow. cbn [nth].
  destruct (word_ok_intro (0x3fc82494ed0e78fc)%Z false 6795621491964156%positive 55%nat (1698905372991039)%Z 2%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc6443c2697a7d2f)%Z true 5704001806564655%positive 109%nat (-5704001806564655)%Z 0%Z (-109)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3ff049f4b0cadb3b)%Z false 4584914914302779%positive 52%nat (4584914914302779)%Z 0%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c9bb890653e497c)%Z false 7802754684569980%positive 106%nat (1950688671142495)%Z 2%Z (-104)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0x3fb952d8a70fd76c)%Z false 7127964887013228%positive 56%nat (1781991221753307)%Z 2%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fc8f871364b45f7)%Z false 7028564566951415%positive 55%nat (7028564566951415)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fb4e153e6ec0484)%Z false 5877250006975620%positive 56%nat (1469312501743905)%Z 2%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3fbcf91aa6f3aa17)%Z false 8155192213350935%positive 56%nat (8155192213350935)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3fb3fcca2dac74ff)%Z false 5625969837372671%positive 56%nat (5625969837372671)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3fb7fa5ebe1ddb9b)%Z false 6749209287842715%positive 56%nat (6749209287842715)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3fb4d57b25d64d67)%Z false 5864224426708327%positive 56%nat (5864224426708327)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3fb7b0b0945db767)%Z false 6668196914247527%positive 56%nat (6668196914247527)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x3ffaa4fcd81b27fe)%Z false 7499755258849278%positive 52%nat (3749877629424639)%Z 1%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_12 _ _).
  all: seg_numeric.
Qed.

Lemma evalcert_13 : EvalCert (IZR (4599485963920735) * bpow radix2 (-52)) (IZR (6066579618235403) * bpow radix2 (-106)) (IZR (7795818328458471) * bpow radix2 (-56)) (IZR (451400344340429) * bpow radix2 (-51)) (IZR (6535903764664947) * bpow radix2 (-56)) (IZR (8718537401278367) * bpow radix2 (-56)) (IZR (3203291313420643) * bpow radix2 (-55)) (IZR (7545907466955763) * bpow radix2 (-56)) (IZR (1701641438989519) * bpow radix2 (-54)) (IZR (3884724380411283) * bpow radix2 (-55)) (IZR (5017868095468731) * bpow radix2 (-49)) (IZR 909 * bpow radix2 (-77)) (IZR 838 * bpow radix2 (-72)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 909 (-909) (-77)); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_13.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_13.l1 th_ tl_ dg).
Qed.

Lemma segok_13 : SegOkRow [(0x3fca2ea462b4998e)%Z; (0xbc651d494caa9d70)%Z; (0x3ff057354707655f)%Z; (0x3c958d85a325840b)%Z; (0x3fbbb241663384e7)%Z; (0x3fc9a8bd52d07cd0)%Z; (0x3fb7385eae2dd273)%Z; (0x3fbef976acc39f9f)%Z; (0x3fb6c2c0c1b272c6)%Z; (0x3fbacef67e136bf3)%Z; (0x3fb82e891606333c)%Z; (0x3fbb9a45c17d4b26)%Z; (0x4021d3b9755c34bb)%Z] (IZR 909 * bpow radix2 (-77)).
Proof.
  unfold SegOkRow. cbn [nth].
  destruct (word_ok_intro (0x3fca2ea462b4998e)%Z false 7369632959994254%positive 55%nat (3684816479997127)%Z 1%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc651d494caa9d70)%Z true 5943175166991728%positive 109%nat (-371448447936983)%Z 4%Z (-105)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3ff057354707655f)%Z false 4599485963920735%positive 52%nat (4599485963920735)%Z 0%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c958d85a325840b)%Z false 6066579618235403%positive 106%nat (6066579618235403)%Z 0%Z (-106)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0x3fbbb241663384e7)%Z false 7795818328458471%positive 56%nat (7795818328458471)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fc9a8bd52d07cd0)%Z false 7222405509446864%positive 55%nat (451400344340429)%Z 4%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fb7385eae2dd273)%Z false 6535903764664947%positive 56%nat (6535903764664947)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3fbef976acc39f9f)%Z false 8718537401278367%positive 56%nat (8718537401278367)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3fb6c2c0c1b272c6)%Z false 6406582626841286%positive 56%nat (3203291313420643)%Z 1%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3fbacef67e136bf3)%Z false 7545907466955763%positive 56%nat (7545907466955763)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3fb82e891606333c)%Z false 6806565755958076%positive 56%nat (1701641438989519)%Z 2%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3fbb9a45c17d4b26)%Z false 7769448760822566%positive 56%nat (3884724380411283)%Z 1%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x4021d3b9755c34bb)%Z false 5017868095468731%positive 49%nat (5017868095468731)%Z 0%Z (-49)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_13 _ _).
  all: seg_numeric.
Qed.

Lemma evalcert_14 : EvalCert (IZR (2307689900185971) * bpow radix2 (-51)) (IZR (-5991750353204499) * bpow radix2 (-106)) (IZR (2120707846735005) * bpow radix2 (-54)) (IZR (3718773847578687) * bpow radix2 (-54)) (IZR (7241538279682043) * bpow radix2 (-56)) (IZR (4679687364319231) * bpow radix2 (-55)) (IZR (7281636677624775) * bpow radix2 (-56)) (IZR (8479893459712933) * bpow radix2 (-56)) (IZR (8072885025702265) * bpow radix2 (-56)) (IZR (1146303575732757) * bpow radix2 (-53)) (IZR (2404599983395017) * bpow radix2 (-51)) (IZR 988 * bpow radix2 (-77)) (IZR 864 * bpow radix2 (-72)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 247 (-247) (-75)); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_14.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_14.l1 th_ tl_ dg).
Qed.

Lemma segok_14 : SegOkRow [(0x3fcc3a6f13aae84b)%Z; (0xbc67739d10fe8bc1)%Z; (0x3ff065a9d98132e6)%Z; (0xbc9549771762b513)%Z; (0x3fbe231717821274)%Z; (0x3fca6c69045eb07e)%Z; (0x3fb9ba2404c9affb)%Z; (0x3fc0a0269f0297ff)%Z; (0x3fb9de9c278da3c7)%Z; (0x3fbe206b0d663ba5)%Z; (0x3fbcae3f04450179)%Z; (0x3fc04a3a65bec854)%Z; (0x3ff115f11faca192)%Z] (IZR 988 * bpow radix2 (-77)).
Proof.
  unfold SegOkRow. cbn [nth].
  destruct (word_ok_intro (0x3fcc3a6f13aae84b)%Z false 7945548093646923%positive 55%nat (7945548093646923)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc67739d10fe8bc1)%Z true 6601042896522177%positive 109%nat (-6601042896522177)%Z 0%Z (-109)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3ff065a9d98132e6)%Z false 4615379800371942%positive 52%nat (2307689900185971)%Z 1%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc9549771762b513)%Z true 5991750353204499%positive 106%nat (-5991750353204499)%Z 0%Z (-106)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0x3fbe231717821274)%Z false 8482831386940020%positive 56%nat (2120707846735005)%Z 2%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fca6c69045eb07e)%Z false 7437547695157374%positive 55%nat (3718773847578687)%Z 1%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fb9ba2404c9affb)%Z false 7241538279682043%positive 56%nat (7241538279682043)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3fc0a0269f0297ff)%Z false 4679687364319231%positive 55%nat (4679687364319231)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3fb9de9c278da3c7)%Z false 7281636677624775%positive 56%nat (7281636677624775)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3fbe206b0d663ba5)%Z false 8479893459712933%positive 56%nat (8479893459712933)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3fbcae3f04450179)%Z false 8072885025702265%positive 56%nat (8072885025702265)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3fc04a3a65bec854)%Z false 4585214302931028%positive 55%nat (1146303575732757)%Z 2%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x3ff115f11faca192)%Z false 4809199966790034%positive 52%nat (2404599983395017)%Z 1%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_14 _ _).
  all: seg_numeric.
Qed.

Lemma evalcert_15 : EvalCert (IZR (2316317920626055) * bpow radix2 (-51)) (IZR (-8763360667876271) * bpow radix2 (-106)) (IZR (4595536458384939) * bpow radix2 (-55)) (IZR (7675557618464065) * bpow radix2 (-55)) (IZR (8000572592974283) * bpow radix2 (-56)) (IZR (5043650887300247) * bpow radix2 (-55)) (IZR (4133710826304487) * bpow radix2 (-55)) (IZR (299226727192479) * bpow radix2 (-51)) (IZR (303885005635245) * bpow radix2 (-51)) (IZR (2705079352906485) * bpow radix2 (-54)) (IZR (-6832789283283419) * bpow radix2 (-48)) (IZR 535 * bpow radix2 (-76)) (IZR 892 * bpow radix2 (-72)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 535 (-535) (-76)); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_15.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_15.l1 th_ tl_ dg).
Qed.

Lemma segok_15 : SegOkRow [(0x3fce481c0fce7134)%Z; (0x3c1c9bcb7ab7132b)%Z; (0x3ff0755b95b10b0e)%Z; (0xbc9f223ae7a5bbaf)%Z; (0x3fc0539db627862b)%Z; (0x3fcb44e1054d3541)%Z; (0x3fbc6c7a776769cb)%Z; (0x3fc1eb2c7b823497)%Z; (0x3fbd5f2d1acfe7ce)%Z; (0x3fc102526c8179f0)%Z; (0x3fc1461bdd03ead0)%Z; (0x3fc33882bbd6a5ea)%Z; (0xc0384662ba0e21db)%Z] (IZR 535 * bpow radix2 (-76)).
Proof.
  unfold SegOkRow. cbn [nth].
  destruct (word_ok_intro (0x3fce481c0fce7134)%Z false 8523534662791476%positive 55%nat (2130883665697869)%Z 2%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c1c9bcb7ab7132b)%Z false 8052597587383083%positive 114%nat (8052597587383083)%Z 0%Z (-114)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3ff0755b95b10b0e)%Z false 4632635841252110%positive 52%nat (2316317920626055)%Z 1%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc9f223ae7a5bbaf)%Z true 8763360667876271%positive 106%nat (-8763360667876271)%Z 0%Z (-106)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0x3fc0539db627862b)%Z false 4595536458384939%positive 55%nat (4595536458384939)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fcb44e1054d3541)%Z false 7675557618464065%positive 55%nat (7675557618464065)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fbc6c7a776769cb)%Z false 8000572592974283%positive 56%nat (8000572592974283)%Z 0%Z (-56)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3fc1eb2c7b823497)%Z false 5043650887300247%positive 55%nat (5043650887300247)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3fbd5f2d1acfe7ce)%Z false 8267421652608974%positive 56%nat (4133710826304487)%Z 1%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3fc102526c8179f0)%Z false 4787627635079664%positive 55%nat (299226727192479)%Z 4%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3fc1461bdd03ead0)%Z false 4862160090163920%positive 55%nat (303885005635245)%Z 4%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3fc33882bbd6a5ea)%Z false 5410158705812970%positive 55%nat (2705079352906485)%Z 1%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc0384662ba0e21db)%Z true 6832789283283419%positive 48%nat (-6832789283283419)%Z 0%Z (-48)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_15 _ _).
  all: seg_numeric.
Qed.

Lemma evalcert_16 : EvalCert (IZR (4651297694611163) * bpow radix2 (-52)) (IZR (-1118956374265591) * bpow radix2 (-103)) (IZR (620173025948155) * bpow radix2 (-52)) (IZR (124034605189631) * bpow radix2 (-49)) (IZR (4410119295632043) * bpow radix2 (-55)) (IZR (1364196902115541) * bpow radix2 (-53)) (IZR (2345791433481071) * bpow radix2 (-54)) (IZR (5430623645062917) * bpow radix2 (-55)) (IZR (2785640742475551) * bpow radix2 (-54)) (IZR (1604778968818183) * bpow radix2 (-53)) (IZR (3154147363098467) * bpow radix2 (-58)) (IZR 577 * bpow radix2 (-76)) (IZR 923 * bpow radix2 (-72)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 577 (-577) (-76)); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_16.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_16.l1 th_ tl_ dg).
Qed.

Lemma segok_16 : SegOkRow [(0x3fd02be9ce0b87cd)%Z; (0x3c5e5d09da2e0f04)%Z; (0x3ff08654a2d4f6db)%Z; (0xbc9fcd7aa9a877b8)%Z; (0x3fc1a05a47498fd8)%Z; (0x3fcc33c3a5427fc0)%Z; (0x3fbf55f5d4110556)%Z; (0x3fc362eb5f046354)%Z; (0x3fc0aaf8423836de)%Z; (0x3fc34b1f9945d705)%Z; (0x3fc3cb0d0ddaae3e)%Z; (0x3fc6ce26e184881c)%Z; (0x3f86695c524b1ec6)%Z] (IZR 577 * bpow radix2 (-76)).
Proof.
  unfold SegOkRow. cbn [nth].
  destruct (word_ok_intro (0x3fd02be9ce0b87cd)%Z false 4551882811606989%positive 54%nat (4551882811606989)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c5e5d09da2e0f04)%Z false 8546546197860100%positive 110%nat (2136636549465025)%Z 2%Z (-108)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3ff08654a2d4f6db)%Z false 4651297694611163%positive 52%nat (4651297694611163)%Z 0%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc9fcd7aa9a877b8)%Z true 8951650994124728%positive 106%nat (-1118956374265591)%Z 3%Z (-103)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0x3fc1a05a47498fd8)%Z false 4961384207585240%positive 55%nat (620173025948155)%Z 3%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fcc33c3a5427fc0)%Z false 7938214732136384%positive 55%nat (124034605189631)%Z 6%Z (-49)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fbf55f5d4110556)%Z false 8820238591264086%positive 56%nat (4410119295632043)%Z 1%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3fc362eb5f046354)%Z false 5456787608462164%positive 55%nat (1364196902115541)%Z 2%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3fc0aaf8423836de)%Z false 4691582866962142%positive 55%nat (2345791433481071)%Z 1%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3fc34b1f9945d705)%Z false 5430623645062917%positive 55%nat (5430623645062917)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3fc3cb0d0ddaae3e)%Z false 5571281484951102%positive 55%nat (2785640742475551)%Z 1%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3fc6ce26e184881c)%Z false 6419115875272732%positive 55%nat (1604778968818183)%Z 2%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x3f86695c524b1ec6)%Z false 6308294726196934%positive 59%nat (3154147363098467)%Z 1%Z (-58)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_16 _ _).
  all: seg_numeric.
Qed.

Lemma evalcert_17 : EvalCert (IZR (4671413485200487) * bpow radix2 (-52)) (IZR (4637348302410697) * bpow radix2 (-109)) (IZR (667520077738131) * bpow radix2 (-52)) (IZR (1028442373822595) * bpow radix2 (-52)) (IZR (4854361000795953) * bpow radix2 (-55)) (IZR (5925705947891195) * bpow radix2 (-55)) (IZR (2662889673219899) * bpow radix2 (-54)) (IZR (6186763561595531) * bpow radix2 (-55)) (IZR (6691953071521055) * bpow radix2 (-55)) (IZR (3824993744824487) * bpow radix2 (-54)) (IZR (-7620072313664745) * bpow radix2 (-48)) (IZR 621 * bpow radix2 (-76)) (IZR 957 * bpow radix2 (-72)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 621 (-621) (-76)); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_17.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_17.l1 th_ tl_ dg).
Qed.

Lemma segok_17 : SegOkRow [(0x3fd134dfa9805147)%Z; (0xbc7bbe27a4ac52e2)%Z; (0x3ff098a035626467)%Z; (0x3c6079a4ca43d3c9)%Z; (0x3fc2f8d908e98498)%Z; (0x3fcd3ae732e8c418)%Z; (0x3fc13f03ff105f31)%Z; (0x3fc50d65ee1145fb)%Z; (0x3fc2ebc4a218be76)%Z; (0x3fc5fad42465f28b)%Z; (0x3fc7c64bbdae7d1f)%Z; (0x3fcb2d9f82db514e)%Z; (0xc03b126a576b34e9)%Z] (IZR 621 * bpow radix2 (-76)).
Proof.
  unfold SegOkRow. cbn [nth].
  destruct (word_ok_intro (0x3fd134dfa9805147)%Z false 4843209830191431%positive 54%nat (4843209830191431)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc7bbe27a4ac52e2)%Z true 7808901846946530%positive 108%nat (-3904450923473265)%Z 1%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3ff098a035626467)%Z false 4671413485200487%positive 52%nat (4671413485200487)%Z 0%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c6079a4ca43d3c9)%Z false 4637348302410697%positive 109%nat (4637348302410697)%Z 0%Z (-109)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0x3fc2f8d908e98498)%Z false 5340160621905048%positive 55%nat (667520077738131)%Z 3%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fcd3ae732e8c418)%Z false 8227538990580760%positive 55%nat (1028442373822595)%Z 3%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fc13f03ff105f31)%Z false 4854361000795953%positive 55%nat (4854361000795953)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3fc50d65ee1145fb)%Z false 5925705947891195%positive 55%nat (5925705947891195)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3fc2ebc4a218be76)%Z false 5325779346439798%positive 55%nat (2662889673219899)%Z 1%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3fc5fad42465f28b)%Z false 6186763561595531%positive 55%nat (6186763561595531)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3fc7c64bbdae7d1f)%Z false 6691953071521055%positive 55%nat (6691953071521055)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3fcb2d9f82db514e)%Z false 7649987489648974%positive 55%nat (3824993744824487)%Z 1%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc03b126a576b34e9)%Z true 7620072313664745%positive 48%nat (-7620072313664745)%Z 0%Z (-48)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_17 _ _).
  all: seg_numeric.
Qed.

Lemma evalcert_18 : EvalCert (IZR (4693036224830451) * bpow radix2 (-52)) (IZR (-2423744871033107) * bpow radix2 (-105)) (IZR (179161510173803) * bpow radix2 (-50)) (IZR (4272911596004035) * bpow radix2 (-54)) (IZR (5337664691653425) * bpow radix2 (-55)) (IZR (6458177869149051) * bpow radix2 (-55)) (IZR (6049852129006355) * bpow radix2 (-55)) (IZR (442364892008963) * bpow radix2 (-51)) (IZR (3855120409237537) * bpow radix2 (-54)) (IZR (4590889623075055) * bpow radix2 (-54)) (IZR (3087798930790951) * bpow radix2 (-49)) (IZR 667 * bpow radix2 (-76)) (IZR 994 * bpow radix2 (-72)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 667 (-667) (-76)); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_18.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_18.l1 th_ tl_ dg).
Qed.

Lemma segok_18 : SegOkRow [(0x3fd23f0523c5dc2b)%Z; (0x3c44fc2674a3d6b2)%Z; (0x3ff0ac4aa5195bf3)%Z; (0xbc9138c42820d226)%Z; (0x3fc45e49457b8d60)%Z; (0x3fce5c6183ac4586)%Z; (0x3fc2f693e7e04b31)%Z; (0x3fc6f1adb5c9737b)%Z; (0x3fc57e4ef717d313)%Z; (0x3fc92541a3fd2030)%Z; (0x3fcb646c551e3042)%Z; (0x3fd04f63c92fb8ef)%Z; (0x4015f0ac6cd0b44e)%Z] (IZR 667 * bpow radix2 (-76)).
Proof.
  unfold SegOkRow. cbn [nth].
  destruct (word_ok_intro (0x3fd23f0523c5dc2b)%Z false 5135840888347691%positive 54%nat (5135840888347691)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c44fc2674a3d6b2)%Z false 5906741630064306%positive 111%nat (2953370815032153)%Z 1%Z (-110)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3ff0ac4aa5195bf3)%Z false 4693036224830451%positive 52%nat (4693036224830451)%Z 0%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc9138c42820d226)%Z true 4847489742066214%positive 106%nat (-2423744871033107)%Z 1%Z (-105)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0x3fc45e49457b8d60)%Z false 5733168325561696%positive 55%nat (179161510173803)%Z 5%Z (-50)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fce5c6183ac4586)%Z false 8545823192008070%positive 55%nat (4272911596004035)%Z 1%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fc2f693e7e04b31)%Z false 5337664691653425%positive 55%nat (5337664691653425)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3fc6f1adb5c9737b)%Z false 6458177869149051%positive 55%nat (6458177869149051)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3fc57e4ef717d313)%Z false 6049852129006355%positive 55%nat (6049852129006355)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3fc92541a3fd2030)%Z false 7077838272143408%positive 55%nat (442364892008963)%Z 4%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3fcb646c551e3042)%Z false 7710240818475074%positive 55%nat (3855120409237537)%Z 1%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3fd04f63c92fb8ef)%Z false 4590889623075055%positive 54%nat (4590889623075055)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x4015f0ac6cd0b44e)%Z false 6175597861581902%positive 50%nat (3087798930790951)%Z 1%Z (-49)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_18 _ _).
  all: seg_numeric.
Qed.

Lemma evalcert_19 : EvalCert (IZR (4716224232773905) * bpow radix2 (-52)) (IZR (8176254165422927) * bpow radix2 (-106)) (IZR (3070912271514361) * bpow radix2 (-54)) (IZR (2223917754634905) * bpow radix2 (-53)) (IZR (733167929188207) * bpow radix2 (-52)) (IZR (3531681590723073) * bpow radix2 (-54)) (IZR (107499245619945) * bpow radix2 (-49)) (IZR (2032647331868163) * bpow radix2 (-53)) (IZR (1138864890473465) * bpow radix2 (-52)) (IZR (2760164288095821) * bpow radix2 (-53)) (IZR (4857085858731957) * bpow radix2 (-49)) (IZR 714 * bpow radix2 (-76)) (IZR 518 * bpow radix2 (-71)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 357 (-357) (-75)); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_19.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_19.l1 th_ tl_ dg).
Qed.

Lemma segok_19 : SegOkRow [(0x3fd34a709597aab1)%Z; (0xbc770f1371722985)%Z; (0x3ff0c16186135911)%Z; (0x3c9d0c42851f934f)%Z; (0x3fc5d1f4f628f5f2)%Z; (0x3fcf9a90cf194a64)%Z; (0x3fc4d67fafd6fb78)%Z; (0x3fc9181765598402)%Z; (0x3fc871479652ba40)%Z; (0x3fcce2ba58adb80c)%Z; (0x3fd02f2a94f9afe4)%Z; (0x3fd39cb5a7d3cc9a)%Z; (0x4021417e6d40d7b5)%Z] (IZR 714 * bpow radix2 (-76)).
Proof.
  unfold SegOkRow. cbn [nth].
  destruct (word_ok_intro (0x3fd34a709597aab1)%Z false 5429871964039857%positive 54%nat (5429871964039857)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc770f1371722985)%Z true 6490500646447493%positive 108%nat (-6490500646447493)%Z 0%Z (-108)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3ff0c16186135911)%Z false 4716224232773905%positive 52%nat (4716224232773905)%Z 0%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c9d0c42851f934f)%Z false 8176254165422927%positive 106%nat (8176254165422927)%Z 0%Z (-106)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0x3fc5d1f4f628f5f2)%Z false 6141824543028722%positive 55%nat (3070912271514361)%Z 1%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fcf9a90cf194a64)%Z false 8895671018539620%positive 55%nat (2223917754634905)%Z 2%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fc4d67fafd6fb78)%Z false 5865343433505656%positive 55%nat (733167929188207)%Z 3%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3fc9181765598402)%Z false 7063363181446146%positive 55%nat (3531681590723073)%Z 1%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3fc871479652ba40)%Z false 6879951719676480%positive 55%nat (107499245619945)%Z 6%Z (-49)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3fcce2ba58adb80c)%Z false 8130589327472652%positive 55%nat (2032647331868163)%Z 2%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3fd02f2a94f9afe4)%Z false 4555459561893860%positive 54%nat (1138864890473465)%Z 2%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3fd39cb5a7d3cc9a)%Z false 5520328576191642%positive 54%nat (2760164288095821)%Z 1%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x4021417e6d40d7b5)%Z false 4857085858731957%positive 49%nat (4857085858731957)%Z 0%Z (-49)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_19 _ _).
  all: seg_numeric.
Qed.

Lemma evalcert_20 : EvalCert (IZR (4741041613197763) * bpow radix2 (-52)) (IZR (-891457182481707) * bpow radix2 (-108)) (IZR (6567676693607291) * bpow radix2 (-55)) (IZR (2320010468391147) * bpow radix2 (-53)) (IZR (6443488882525645) * bpow radix2 (-55)) (IZR (3876042378076121) * bpow radix2 (-54)) (IZR (1958876648417047) * bpow radix2 (-53)) (IZR (1172243004827131) * bpow radix2 (-52)) (IZR (2695183152357737) * bpow radix2 (-53)) (IZR (416559781958455) * bpow radix2 (-50)) (IZR (4630788634616861) * bpow radix2 (-48)) (IZR 763 * bpow radix2 (-76)) (IZR 541 * bpow radix2 (-71)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 763 (-763) (-76)); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_20.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_20.l1 th_ tl_ dg).
Qed.

Lemma segok_20 : SegOkRow [(0x3fd457393b90e2aa)%Z; (0x3c7b1f64d329fe98)%Z; (0x3ff0d7f3c53851c3)%Z; (0xbc495634658de958)%Z; (0x3fc755446452737b)%Z; (0x3fd07c130faff1d6)%Z; (0x3fc6e451a9f505cd)%Z; (0x3fcb8a7ae228bfb2)%Z; (0x3fcbd65a0b269c5c)%Z; (0x3fd0a8985f9297ec)%Z; (0x3fd3268274cd42d2)%Z; (0x3fd7adbe1d4d3370)%Z; (0x403073ad7f98a41d)%Z] (IZR 763 * bpow radix2 (-76)).
Proof.
  unfold SegOkRow. cbn [nth].
  destruct (word_ok_intro (0x3fd457393b90e2aa)%Z false 5725402858316458%positive 54%nat (2862701429158229)%Z 1%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c7b1f64d329fe98)%Z false 7634342271123096%positive 108%nat (954292783890387)%Z 3%Z (-105)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3ff0d7f3c53851c3)%Z false 4741041613197763%positive 52%nat (4741041613197763)%Z 0%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc495634658de958)%Z true 7131657459853656%positive 111%nat (-891457182481707)%Z 3%Z (-108)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0x3fc755446452737b)%Z false 6567676693607291%positive 55%nat (6567676693607291)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fd07c130faff1d6)%Z false 4640020936782294%positive 54%nat (2320010468391147)%Z 1%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fc6e451a9f505cd)%Z false 6443488882525645%positive 55%nat (6443488882525645)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3fcb8a7ae228bfb2)%Z false 7752084756152242%positive 55%nat (3876042378076121)%Z 1%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3fcbd65a0b269c5c)%Z false 7835506593668188%positive 55%nat (1958876648417047)%Z 2%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3fd0a8985f9297ec)%Z false 4688972019308524%positive 54%nat (1172243004827131)%Z 2%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3fd3268274cd42d2)%Z false 5390366304715474%positive 54%nat (2695183152357737)%Z 1%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3fd7adbe1d4d3370)%Z false 6664956511335280%positive 54%nat (416559781958455)%Z 4%Z (-50)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x403073ad7f98a41d)%Z false 4630788634616861%positive 48%nat (4630788634616861)%Z 0%Z (-48)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_20 _ _).
  all: seg_numeric.
Qed.

Lemma evalcert_21 : EvalCert (IZR (2383779398926573) * bpow radix2 (-51)) (IZR (-1051748032238729) * bpow radix2 (-105)) (IZR (3506210136423873) * bpow radix2 (-54)) (IZR (2425575966350845) * bpow radix2 (-53)) (IZR (884889248969855) * bpow radix2 (-52)) (IZR (4268583771725079) * bpow radix2 (-54)) (IZR (8939940363767059) * bpow radix2 (-55)) (IZR (5430313580872895) * bpow radix2 (-54)) (IZR (3244828538216955) * bpow radix2 (-53)) (IZR (8097917668160167) * bpow radix2 (-54)) (IZR (-2636307948376459) * bpow radix2 (-48)) (IZR 814 * bpow radix2 (-76)) (IZR 566 * bpow radix2 (-71)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 407 (-407) (-75)); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_21.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_21.l1 th_ tl_ dg).
Qed.

Lemma segok_21 : SegOkRow [(0x3fd565774cb66f02)%Z; (0xbc7c537759c5cce1)%Z; (0x3ff0f011c89781da)%Z; (0xbc7de4795ed6a448)%Z; (0x3fc8e9c25360fb82)%Z; (0x3fd13c18d3b33bfa)%Z; (0x3fc9266aaacda3f8)%Z; (0x3fce548236d0ba2e)%Z; (0x3fcfc2d411b20d13)%Z; (0x3fd34ad76801c4bf)%Z; (0x3fd70e4f08c143f6)%Z; (0x3fdcc5036207f2a7)%Z; (0xc022bb6a8d902316)%Z] (IZR 814 * bpow radix2 (-76)).
Proof.
  unfold SegOkRow. cbn [nth].
  destruct (word_ok_intro (0x3fd565774cb66f02)%Z false 6022537573461762%positive 54%nat (3011268786730881)%Z 1%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc7c537759c5cce1)%Z true 7973071420247265%positive 108%nat (-7973071420247265)%Z 0%Z (-108)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3ff0f011c89781da)%Z false 4767558797853146%positive 52%nat (2383779398926573)%Z 1%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc7de4795ed6a448)%Z true 8413984257909832%positive 108%nat (-1051748032238729)%Z 3%Z (-105)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0x3fc8e9c25360fb82)%Z false 7012420272847746%positive 55%nat (3506210136423873)%Z 1%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fd13c18d3b33bfa)%Z false 4851151932701690%positive 54%nat (2425575966350845)%Z 1%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fc9266aaacda3f8)%Z false 7079113991758840%positive 55%nat (884889248969855)%Z 3%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3fce548236d0ba2e)%Z false 8537167543450158%positive 55%nat (4268583771725079)%Z 1%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3fcfc2d411b20d13)%Z false 8939940363767059%positive 55%nat (8939940363767059)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3fd34ad76801c4bf)%Z false 5430313580872895%positive 54%nat (5430313580872895)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3fd70e4f08c143f6)%Z false 6489657076433910%positive 54%nat (3244828538216955)%Z 1%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3fdcc5036207f2a7)%Z false 8097917668160167%positive 54%nat (8097917668160167)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc022bb6a8d902316)%Z true 5272615896752918%positive 49%nat (-2636307948376459)%Z 1%Z (-48)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_21 _ _).
  all: seg_numeric.
Qed.

Lemma evalcert_22 : EvalCert (IZR (1198963290937753) * bpow radix2 (-50)) (IZR (-1699263973706287) * bpow radix2 (-104)) (IZR (3738959720133679) * bpow radix2 (-54)) (IZR (79424192182443) * bpow radix2 (-48)) (IZR (3890162609457145) * bpow radix2 (-54)) (IZR (4716928981621589) * bpow radix2 (-54)) (IZR (638854566837545) * bpow radix2 (-51)) (IZR (6314622548223211) * bpow radix2 (-54)) (IZR (7739894549740871) * bpow radix2 (-54)) (IZR (4944392643048417) * bpow radix2 (-53)) (IZR (-5636631413204235) * bpow radix2 (-50)) (IZR 868 * bpow radix2 (-76)) (IZR 593 * bpow radix2 (-71)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 217 (-217) (-74)); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_22.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_22.l1 th_ tl_ dg).
Qed.

Lemma segok_22 : SegOkRow [(0x3fd675441329986e)%Z; (0x3c7d027ed2bb2eda)%Z; (0x3ff109cd94386664)%Z; (0xbc9825e2e62128bc)%Z; (0x3fca9120cbe5685e)%Z; (0x3fd20f18b0be2ac0)%Z; (0x3fcba42a20e90ff2)%Z; (0x3fd0c2059c615b55)%Z; (0x3fd228475c27e948)%Z; (0x3fd66f1da1e0a4eb)%Z; (0x3fdb7f64a13c7d47)%Z; (0x3fe190e61f1e73e1)%Z; (0xc014067c851d250b)%Z] (IZR 868 * bpow radix2 (-76)).
Proof.
  unfold SegOkRow. cbn [nth].
  destruct (word_ok_intro (0x3fd675441329986e)%Z false 6321384727353454%positive 54%nat (3160692363676727)%Z 1%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c7d027ed2bb2eda)%Z false 8165518049226458%positive 108%nat (4082759024613229)%Z 1%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3ff109cd94386664)%Z false 4795853163751012%positive 52%nat (1198963290937753)%Z 2%Z (-50)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc9825e2e62128bc)%Z true 6797055894825148%positive 106%nat (-1699263973706287)%Z 2%Z (-104)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0x3fca9120cbe5685e)%Z false 7477919440267358%positive 55%nat (3738959720133679)%Z 1%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fd20f18b0be2ac0)%Z false 5083148299676352%positive 54%nat (79424192182443)%Z 6%Z (-48)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fcba42a20e90ff2)%Z false 7780325218914290%positive 55%nat (3890162609457145)%Z 1%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3fd0c2059c615b55)%Z false 4716928981621589%positive 54%nat (4716928981621589)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3fd228475c27e948)%Z false 5110836534700360%positive 54%nat (638854566837545)%Z 3%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3fd66f1da1e0a4eb)%Z false 6314622548223211%positive 54%nat (6314622548223211)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3fdb7f64a13c7d47)%Z false 7739894549740871%positive 54%nat (7739894549740871)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3fe190e61f1e73e1)%Z false 4944392643048417%positive 53%nat (4944392643048417)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc014067c851d250b)%Z true 5636631413204235%positive 50%nat (-5636631413204235)%Z 0%Z (-50)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_22 _ _).
  all: seg_numeric.
Qed.

Lemma evalcert_23 : EvalCert (IZR (4826009737352117) * bpow radix2 (-52)) (IZR (6141958890159565) * bpow radix2 (-111)) (IZR (995778852450563) * bpow radix2 (-52)) (IZR (1334550729326121) * bpow radix2 (-52)) (IZR (4278265659452911) * bpow radix2 (-54)) (IZR (2615086275350393) * bpow radix2 (-53)) (IZR (5857650728160687) * bpow radix2 (-54)) (IZR (3686744414966185) * bpow radix2 (-53)) (IZR (1154595129160855) * bpow radix2 (-51)) (IZR (759235480627909) * bpow radix2 (-50)) (IZR (7767999520138843) * bpow radix2 (-49)) (IZR 925 * bpow radix2 (-76)) (IZR 623 * bpow radix2 (-71)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 925 (-925) (-76)); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_23.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_23.l1 th_ tl_ dg).
Qed.

Lemma segok_23 : SegOkRow [(0x3fd786ba074fef93)%Z; (0xbc773b1910f90a93)%Z; (0x3ff1253af413d3b5)%Z; (0x3c45d2143ddf7dcd)%Z; (0x3fcc4d3ea6338818)%Z; (0x3fd2f711389ff8a4)%Z; (0x3fce661eb1c5dbde)%Z; (0x3fd294d070ff9ef2)%Z; (0x3fd4cf8096decdaf)%Z; (0x3fda32262676a352)%Z; (0x3fe068648221d25c)%Z; (0x3fe5942a48fd5628)%Z; (0x402b98f45403665b)%Z] (IZR 925 * bpow radix2 (-76)).
Proof.
  unfold SegOkRow. cbn [nth].
  destruct (word_ok_intro (0x3fd786ba074fef93)%Z false 6622058009063315%positive 54%nat (6622058009063315)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc773b1910f90a93)%Z true 6538903309322899%positive 108%nat (-6538903309322899)%Z 0%Z (-108)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3ff1253af413d3b5)%Z false 4826009737352117%positive 52%nat (4826009737352117)%Z 0%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c45d2143ddf7dcd)%Z false 6141958890159565%positive 111%nat (6141958890159565)%Z 0%Z (-111)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0x3fcc4d3ea6338818)%Z false 7966230819604504%positive 55%nat (995778852450563)%Z 3%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fd2f711389ff8a4)%Z false 5338202917304484%positive 54%nat (1334550729326121)%Z 2%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fce661eb1c5dbde)%Z false 8556531318905822%positive 55%nat (4278265659452911)%Z 1%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3fd294d070ff9ef2)%Z false 5230172550700786%positive 54%nat (2615086275350393)%Z 1%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3fd4cf8096decdaf)%Z false 5857650728160687%positive 54%nat (5857650728160687)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3fda32262676a352)%Z false 7373488829932370%positive 54%nat (3686744414966185)%Z 1%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3fe068648221d25c)%Z false 4618380516643420%positive 53%nat (1154595129160855)%Z 2%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3fe5942a48fd5628)%Z false 6073883845023272%positive 53%nat (759235480627909)%Z 3%Z (-50)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x402b98f45403665b)%Z false 7767999520138843%positive 49%nat (7767999520138843)%Z 0%Z (-49)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_23 _ _).
  all: seg_numeric.
Qed.

Lemma evalcert_24 : EvalCert (IZR (4858121998980315) * bpow radix2 (-52)) (IZR (-72925177116655) * bpow radix2 (-100)) (IZR (8479631125492913) * bpow radix2 (-55)) (IZR (2809413140567349) * bpow radix2 (-53)) (IZR (4709348856472351) * bpow radix2 (-54)) (IZR (5819205790431609) * bpow radix2 (-54)) (IZR (3365792563037537) * bpow radix2 (-53)) (IZR (1080820367399499) * bpow radix2 (-51)) (IZR (2791775213866963) * bpow radix2 (-52)) (IZR (7485035877023839) * bpow radix2 (-53)) (IZR (8986060013205109) * bpow radix2 (-53)) (IZR 984 * bpow radix2 (-76)) (IZR 656 * bpow radix2 (-71)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 123 (-123) (-73)); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_24.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_24.l1 th_ tl_ dg).
Qed.

Lemma segok_24 : SegOkRow [(0x3fd899f4edc962d3)%Z; (0x3c33e919701b7c6d)%Z; (0x3ff1426fac0654db)%Z; (0xbc9094cdd1bdfbc0)%Z; (0x3fce202df90fb4b1)%Z; (0x3fd3f64af08aaa6a)%Z; (0x3fd0bb20b9b6a31f)%Z; (0x3fd4ac896e037979)%Z; (0x3fd7ea574c370ac2)%Z; (0x3fdeb800d084d258)%Z; (0x3fe3d635a3d49fa6)%Z; (0x3fea9799b894c05f)%Z; (0x3fefecc623047675)%Z] (IZR 984 * bpow radix2 (-76)).
Proof.
  unfold SegOkRow. cbn [nth].
  destruct (word_ok_intro (0x3fd899f4edc962d3)%Z false 6924676681523923%positive 54%nat (6924676681523923)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c33e919701b7c6d)%Z false 5604320021806189%positive 112%nat (5604320021806189)%Z 0%Z (-112)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3ff1426fac0654db)%Z false 4858121998980315%positive 52%nat (4858121998980315)%Z 0%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc9094cdd1bdfbc0)%Z true 4667211335465920%positive 106%nat (-72925177116655)%Z 6%Z (-100)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0x3fce202df90fb4b1)%Z false 8479631125492913%positive 55%nat (8479631125492913)%Z 0%Z (-55)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fd3f64af08aaa6a)%Z false 5618826281134698%positive 54%nat (2809413140567349)%Z 1%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fd0bb20b9b6a31f)%Z false 4709348856472351%positive 54%nat (4709348856472351)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3fd4ac896e037979)%Z false 5819205790431609%positive 54%nat (5819205790431609)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3fd7ea574c370ac2)%Z false 6731585126075074%positive 54%nat (3365792563037537)%Z 1%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3fdeb800d084d258)%Z false 8646562939195992%positive 54%nat (1080820367399499)%Z 3%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3fe3d635a3d49fa6)%Z false 5583550427733926%positive 53%nat (2791775213866963)%Z 1%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3fea9799b894c05f)%Z false 7485035877023839%positive 53%nat (7485035877023839)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x3fefecc623047675)%Z false 8986060013205109%positive 53%nat (8986060013205109)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_24 _ _).
  all: seg_numeric.
Qed.

Lemma evalcert_25 : EvalCert (IZR (4892292803818435) * bpow radix2 (-52)) (IZR (6960967058538587) * bpow radix2 (-108)) (IZR (4510324682287235) * bpow radix2 (-54)) (IZR (2963949924318609) * bpow radix2 (-53)) (IZR (5189828962856573) * bpow radix2 (-54)) (IZR (3248562644448439) * bpow radix2 (-53)) (IZR (7758703514837457) * bpow radix2 (-54)) (IZR (2545967047172755) * bpow radix2 (-52)) (IZR (6741866046690717) * bpow radix2 (-53)) (IZR (2319817733600743) * bpow radix2 (-51)) (IZR (7744582827795301) * bpow radix2 (-49)) (IZR 524 * bpow radix2 (-75)) (IZR 693 * bpow radix2 (-71)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 131 (-131) (-73)); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_25.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_25.l1 th_ tl_ dg).
Qed.

Lemma segok_25 : SegOkRow [(0x3fd9af11f89ba61c)%Z; (0x3c7a884c2416dce8)%Z; (0x3ff16183aeb573c3)%Z; (0x3c78baf670d1405b)%Z; (0x3fd0061dcc826883)%Z; (0x3fd50f64bcbdfb22)%Z; (0x3fd2701f37c6ae7d)%Z; (0x3fd71519dce7e96e)%Z; (0x3fdb907feeeb61d1)%Z; (0x3fe217164ae9c526)%Z; (0x3fe7f3b102d6159d)%Z; (0x3ff07bb94fe8ebce)%Z; (0x402b83a834626365)%Z] (IZR 524 * bpow radix2 (-75)).
Proof.
  unfold SegOkRow. cbn [nth].
  destruct (word_ok_intro (0x3fd9af11f89ba61c)%Z false 7229366138021404%positive 54%nat (1807341534505351)%Z 2%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c7a884c2416dce8)%Z false 7468209998847208%positive 108%nat (933526249855901)%Z 3%Z (-105)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3ff16183aeb573c3)%Z false 4892292803818435%positive 52%nat (4892292803818435)%Z 0%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c78baf670d1405b)%Z false 6960967058538587%positive 108%nat (6960967058538587)%Z 0%Z (-108)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0x3fd0061dcc826883)%Z false 4510324682287235%positive 54%nat (4510324682287235)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fd50f64bcbdfb22)%Z false 5927899848637218%positive 54%nat (2963949924318609)%Z 1%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fd2701f37c6ae7d)%Z false 5189828962856573%positive 54%nat (5189828962856573)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3fd71519dce7e96e)%Z false 6497125288896878%positive 54%nat (3248562644448439)%Z 1%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3fdb907feeeb61d1)%Z false 7758703514837457%positive 54%nat (7758703514837457)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3fe217164ae9c526)%Z false 5091934094345510%positive 53%nat (2545967047172755)%Z 1%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3fe7f3b102d6159d)%Z false 6741866046690717%positive 53%nat (6741866046690717)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3ff07bb94fe8ebce)%Z false 4639635467201486%positive 52%nat (2319817733600743)%Z 1%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x402b83a834626365)%Z false 7744582827795301%positive 49%nat (7744582827795301)%Z 0%Z (-49)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_25 _ _).
  all: seg_numeric.
Qed.

Lemma evalcert_26 : EvalCert (IZR (2464317719541811) * bpow radix2 (-51)) (IZR (-7142706471951485) * bpow radix2 (-108)) (IZR (2398026131764663) * bpow radix2 (-53)) (IZR (3134370098270537) * bpow radix2 (-53)) (IZR (2863624215254571) * bpow radix2 (-53)) (IZR (909968562658425) * bpow radix2 (-51)) (IZR (8971237795862965) * bpow radix2 (-54)) (IZR (6024445591820709) * bpow radix2 (-53)) (IZR (510375146503167) * bpow radix2 (-49)) (IZR (5791100654842779) * bpow radix2 (-52)) (IZR (3017847515141841) * bpow radix2 (-46)) (IZR 557 * bpow radix2 (-75)) (IZR 733 * bpow radix2 (-71)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 557 (-557) (-75)); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_26.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_26.l1 th_ tl_ dg).
Qed.

Lemma segok_26 : SegOkRow [(0x3fdac62fec0b2a92)%Z; (0x3c7cb9f9a052f11f)%Z; (0x3ff182915c92f066)%Z; (0xbc796040f1fedc7d)%Z; (0x3fd109fbef7deb6e)%Z; (0x3fd64562d09aa292)%Z; (0x3fd458e6f03dac56)%Z; (0x3fd9dce48778e3c8)%Z; (0x3fdfdf4b120499b5)%Z; (0x3fe567338b7819a5)%Z; (0x3fed02ef94f3bff0)%Z; (0x3ff492f9b163f39b)%Z; (0x4045716ec240ada2)%Z] (IZR 557 * bpow radix2 (-75)).
Proof.
  unfold SegOkRow. cbn [nth].
  destruct (word_ok_intro (0x3fdac62fec0b2a92)%Z false 7536258520394386%positive 54%nat (3768129260197193)%Z 1%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c7cb9f9a052f11f)%Z false 8085781135683871%positive 108%nat (8085781135683871)%Z 0%Z (-108)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3ff182915c92f066)%Z false 4928635439083622%positive 52%nat (2464317719541811)%Z 1%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc796040f1fedc7d)%Z true 7142706471951485%positive 108%nat (-7142706471951485)%Z 0%Z (-108)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0x3fd109fbef7deb6e)%Z false 4796052263529326%positive 54%nat (2398026131764663)%Z 1%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fd64562d09aa292)%Z false 6268740196541074%positive 54%nat (3134370098270537)%Z 1%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fd458e6f03dac56)%Z false 5727248430509142%positive 54%nat (2863624215254571)%Z 1%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3fd9dce48778e3c8)%Z false 7279748501267400%positive 54%nat (909968562658425)%Z 3%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3fdfdf4b120499b5)%Z false 8971237795862965%positive 54%nat (8971237795862965)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3fe567338b7819a5)%Z false 6024445591820709%positive 53%nat (6024445591820709)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3fed02ef94f3bff0)%Z false 8166002344050672%positive 53%nat (510375146503167)%Z 4%Z (-49)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3ff492f9b163f39b)%Z false 5791100654842779%positive 52%nat (5791100654842779)%Z 0%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x4045716ec240ada2)%Z false 6035695030283682%positive 47%nat (3017847515141841)%Z 1%Z (-46)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_26 _ _).
  all: seg_numeric.
Qed.

Lemma evalcert_27 : EvalCert (IZR (1241818710238557) * bpow radix2 (-50)) (IZR (-4175444700197533) * bpow radix2 (-105)) (IZR (2549287474062639) * bpow radix2 (-53)) (IZR (6645176519966189) * bpow radix2 (-54)) (IZR (6330512507322983) * bpow radix2 (-54)) (IZR (4093134128205551) * bpow radix2 (-53)) (IZR (2602318934884591) * bpow radix2 (-52)) (IZR (447584470790489) * bpow radix2 (-49)) (IZR (625941694968661) * bpow radix2 (-49)) (IZR (3629895130933553) * bpow radix2 (-51)) (IZR (868197057756901) * bpow radix2 (-45)) (IZR 592 * bpow radix2 (-75)) (IZR 777 * bpow radix2 (-71)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 37 (-37) (-71)); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_27.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_27.l1 th_ tl_ dg).
Qed.

Lemma segok_27 : SegOkRow [(0x3fdbdf6f47ae6904)%Z; (0x3c7e7bfe76547424)%Z; (0x3ff1a5b5cc659574)%Z; (0xbc9dab16f444e53a)%Z; (0x3fd21d207ca4ca5e)%Z; (0x3fd79bc0b9f13ded)%Z; (0x3fd67d914d3ec267)%Z; (0x3fdd155e1b759dde)%Z; (0x3fe27d972f6981de)%Z; (0x3fe9713616371590)%Z; (0x3ff1ca5343079aa8)%Z; (0x3ff9cabda3b3d262)%Z; (0x4038acf709c7f728)%Z] (IZR 592 * bpow radix2 (-75)).
Proof.
  unfold SegOkRow. cbn [nth].
  destruct (word_ok_intro (0x3fdbdf6f47ae6904)%Z false 7845493408164100%positive 54%nat (1961373352041025)%Z 2%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c7e7bfe76547424)%Z false 8580582138475556%positive 108%nat (2145145534618889)%Z 2%Z (-106)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3ff1a5b5cc659574)%Z false 4967274840954228%positive 52%nat (1241818710238557)%Z 2%Z (-50)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc9dab16f444e53a)%Z true 8350889400395066%positive 106%nat (-4175444700197533)%Z 1%Z (-105)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0x3fd21d207ca4ca5e)%Z false 5098574948125278%positive 54%nat (2549287474062639)%Z 1%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fd79bc0b9f13ded)%Z false 6645176519966189%positive 54%nat (6645176519966189)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fd67d914d3ec267)%Z false 6330512507322983%positive 54%nat (6330512507322983)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3fdd155e1b759dde)%Z false 8186268256411102%positive 54%nat (4093134128205551)%Z 1%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3fe27d972f6981de)%Z false 5204637869769182%positive 53%nat (2602318934884591)%Z 1%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3fe9713616371590)%Z false 7161351532647824%positive 53%nat (447584470790489)%Z 4%Z (-49)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3ff1ca5343079aa8)%Z false 5007533559749288%positive 52%nat (625941694968661)%Z 3%Z (-49)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x3ff9cabda3b3d262)%Z false 7259790261867106%positive 52%nat (3629895130933553)%Z 1%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x4038acf709c7f728)%Z false 6945576462055208%positive 48%nat (868197057756901)%Z 3%Z (-45)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_27 _ _).
  all: seg_numeric.
Qed.

Lemma evalcert_28 : EvalCert (IZR (1252087249931759) * bpow radix2 (-50)) (IZR (-3433888551477617) * bpow radix2 (-106)) (IZR (5419662685694957) * bpow radix2 (-54)) (IZR (3530822343199475) * bpow radix2 (-53)) (IZR (7010184244403459) * bpow radix2 (-54)) (IZR (4620044341553855) * bpow radix2 (-53)) (IZR (3030748456584179) * bpow radix2 (-52)) (IZR (4277366743175477) * bpow radix2 (-52)) (IZR (3071951335132633) * bpow radix2 (-51)) (IZR (4582581211862877) * bpow radix2 (-51)) (IZR (3221573680827911) * bpow radix2 (-46)) (IZR 629 * bpow radix2 (-75)) (IZR 827 * bpow radix2 (-71)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 629 (-629) (-75)); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_28.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_28.l1 th_ tl_ dg).
Qed.

Lemma segok_28 : SegOkRow [(0x3fdcfaf27460fe9f)%Z; (0xbc68bf75f355f723)%Z; (0x3ff1cb111f0a37bc)%Z; (0xbc886634f69e42e2)%Z; (0x3fd341278d2eebed)%Z; (0x3fd91687471015e6)%Z; (0x3fd8e7b9b5b29d03)%Z; (0x3fe069e7e5d32abf)%Z; (0x3fe588e63a5107e6)%Z; (0x3fee647c1a9a226a)%Z; (0x3ff5d3d8d0321bb2)%Z; (0x400047d55549975d)%Z; (0x4046e40225ba1c0e)%Z] (IZR 629 * bpow radix2 (-75)).
Proof.
  unfold SegOkRow. cbn [nth].
  destruct (word_ok_intro (0x3fdcfaf27460fe9f)%Z false 8157218589441695%positive 54%nat (8157218589441695)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc68bf75f355f723)%Z true 6965912755631907%positive 109%nat (-6965912755631907)%Z 0%Z (-109)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3ff1cb111f0a37bc)%Z false 5008348999727036%positive 52%nat (1252087249931759)%Z 2%Z (-50)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc886634f69e42e2)%Z true 6867777102955234%positive 107%nat (-3433888551477617)%Z 1%Z (-106)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0x3fd341278d2eebed)%Z false 5419662685694957%positive 54%nat (5419662685694957)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fd91687471015e6)%Z false 7061644686398950%positive 54%nat (3530822343199475)%Z 1%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fd8e7b9b5b29d03)%Z false 7010184244403459%positive 54%nat (7010184244403459)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3fe069e7e5d32abf)%Z false 4620044341553855%positive 53%nat (4620044341553855)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3fe588e63a5107e6)%Z false 6061496913168358%positive 53%nat (3030748456584179)%Z 1%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3fee647c1a9a226a)%Z false 8554733486350954%positive 53%nat (4277366743175477)%Z 1%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3ff5d3d8d0321bb2)%Z false 6143902670265266%positive 52%nat (3071951335132633)%Z 1%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x400047d55549975d)%Z false 4582581211862877%positive 51%nat (4582581211862877)%Z 0%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x4046e40225ba1c0e)%Z false 6443147361655822%positive 47%nat (3221573680827911)%Z 1%Z (-46)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_28 _ _).
  all: seg_numeric.
Qed.

Lemma evalcert_29 : EvalCert (IZR (1263002646943313) * bpow radix2 (-50)) (IZR (-6628627455915475) * bpow radix2 (-111)) (IZR (2880654885071323) * bpow radix2 (-53)) (IZR (7523301949328493) * bpow radix2 (-54)) (IZR (3889426850227687) * bpow radix2 (-53)) (IZR (5234949863044023) * bpow radix2 (-53)) (IZR (7087770110373689) * bpow radix2 (-53)) (IZR (5135988772845193) * bpow radix2 (-52)) (IZR (7596557121840873) * bpow radix2 (-52)) (IZR (5823523265258095) * bpow radix2 (-51)) (IZR (3600221697932263) * bpow radix2 (-46)) (IZR 669 * bpow radix2 (-75)) (IZR 881 * bpow radix2 (-71)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 669 (-669) (-75)); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_29.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_29.l1 th_ tl_ dg).
Qed.

Lemma segok_29 : SegOkRow [(0x3fde18ddf7da106b)%Z; (0xbc558029cecb4d7b)%Z; (0x3ff1f2c6e07c5944)%Z; (0xbc478cb398dbb5d3)%Z; (0x3fd477e1764a53b6)%Z; (0x3fdaba673c3a4c6d)%Z; (0x3fdba2d383934bce)%Z; (0x3fe29928bf00f3b7)%Z; (0x3fe92e4a13adaf39)%Z; (0x3ff23f2792603689)%Z; (0x3ffafd0748c366e9)%Z; (0x4004b076ab91226f)%Z; (0x404994c3ded5f7ce)%Z] (IZR 669 * bpow radix2 (-75)).
Proof.
  unfold SegOkRow. cbn [nth].
  destruct (word_ok_intro (0x3fde18ddf7da106b)%Z false 8471590926422123%positive 54%nat (8471590926422123)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc558029cecb4d7b)%Z true 6051891562368379%positive 110%nat (-6051891562368379)%Z 0%Z (-110)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3ff1f2c6e07c5944)%Z false 5052010587773252%positive 52%nat (1263002646943313)%Z 2%Z (-50)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc478cb398dbb5d3)%Z true 6628627455915475%positive 111%nat (-6628627455915475)%Z 0%Z (-111)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0x3fd477e1764a53b6)%Z false 5761309770142646%positive 54%nat (2880654885071323)%Z 1%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fdaba673c3a4c6d)%Z false 7523301949328493%positive 54%nat (7523301949328493)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fdba2d383934bce)%Z false 7778853700455374%positive 54%nat (3889426850227687)%Z 1%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3fe29928bf00f3b7)%Z false 5234949863044023%positive 53%nat (5234949863044023)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3fe92e4a13adaf39)%Z false 7087770110373689%positive 53%nat (7087770110373689)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3ff23f2792603689)%Z false 5135988772845193%positive 52%nat (5135988772845193)%Z 0%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x3ffafd0748c366e9)%Z false 7596557121840873%positive 52%nat (7596557121840873)%Z 0%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x4004b076ab91226f)%Z false 5823523265258095%positive 51%nat (5823523265258095)%Z 0%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x404994c3ded5f7ce)%Z false 7200443395864526%positive 47%nat (3600221697932263)%Z 1%Z (-46)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_29 _ _).
  all: seg_numeric.
Qed.

Lemma evalcert_30 : EvalCert (IZR (2549214426231573) * bpow radix2 (-51)) (IZR (7853668715149175) * bpow radix2 (-107)) (IZR (6125771837752967) * bpow radix2 (-54)) (IZR (8036167599586481) * bpow radix2 (-54)) (IZR (8651602853959893) * bpow radix2 (-54)) (IZR (5955533884745109) * bpow radix2 (-53)) (IZR (4161733697591853) * bpow radix2 (-52)) (IZR (1550111093413251) * bpow radix2 (-50)) (IZR (4729285214242525) * bpow radix2 (-51)) (IZR (465869293925453) * bpow radix2 (-47)) (IZR (1507774243268843) * bpow radix2 (-45)) (IZR 711 * bpow radix2 (-75)) (IZR 942 * bpow radix2 (-71)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 711 (-711) (-75)); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_30.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_30.l1 th_ tl_ dg).
Qed.

Lemma segok_30 : SegOkRow [(0x3fdf3958aecddef4)%Z; (0xbc5fc135930a7786)%Z; (0x3ff21cfe78a9e62a)%Z; (0x3c8be6debdf33777)%Z; (0x3fd5c35b665d4687)%Z; (0x3fdc8cda1320fcb1)%Z; (0x3fdebc9642d918d5)%Z; (0x3fe52886c9a5e595)%Z; (0x3fed92264563b45a)%Z; (0x3ff607457457560c)%Z; (0x4000cd42853c86dd)%Z; (0x400a7b4a5c6b44d0)%Z; (0x40456d4030afa3ac)%Z] (IZR 711 * bpow radix2 (-75)).
Proof.
  unfold SegOkRow. cbn [nth].
  destruct (word_ok_intro (0x3fdf3958aecddef4)%Z false 8788777330663156%positive 54%nat (2197194332665789)%Z 2%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc5fc135930a7786)%Z true 8938160122394502%positive 110%nat (-4469080061197251)%Z 1%Z (-109)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3ff21cfe78a9e62a)%Z false 5098428852463146%positive 52%nat (2549214426231573)%Z 1%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c8be6debdf33777)%Z false 7853668715149175%positive 107%nat (7853668715149175)%Z 0%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0x3fd5c35b665d4687)%Z false 6125771837752967%positive 54%nat (6125771837752967)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fdc8cda1320fcb1)%Z false 8036167599586481%positive 54%nat (8036167599586481)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fdebc9642d918d5)%Z false 8651602853959893%positive 54%nat (8651602853959893)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3fe52886c9a5e595)%Z false 5955533884745109%positive 53%nat (5955533884745109)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3fed92264563b45a)%Z false 8323467395183706%positive 53%nat (4161733697591853)%Z 1%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3ff607457457560c)%Z false 6200444373653004%positive 52%nat (1550111093413251)%Z 2%Z (-50)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x4000cd42853c86dd)%Z false 4729285214242525%positive 51%nat (4729285214242525)%Z 0%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x400a7b4a5c6b44d0)%Z false 7453908702807248%positive 51%nat (465869293925453)%Z 4%Z (-47)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x40456d4030afa3ac)%Z false 6031096973075372%positive 47%nat (1507774243268843)%Z 2%Z (-45)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_30 _ _).
  all: seg_numeric.
Qed.

Lemma evalcert_31 : EvalCert (IZR (5147791825775151) * bpow radix2 (-52)) (IZR (-3522066238407225) * bpow radix2 (-107)) (IZR (6515610196068835) * bpow radix2 (-54)) (IZR (4303648193713543) * bpow radix2 (-53)) (IZR (2411648710426553) * bpow radix2 (-52)) (IZR (212616380250563) * bpow radix2 (-48)) (IZR (613726681006329) * bpow radix2 (-49)) (IZR (1882094239733087) * bpow radix2 (-50)) (IZR (2972405951395771) * bpow radix2 (-50)) (IZR (2402073976672927) * bpow radix2 (-49)) (IZR (-8795911621375995) * bpow radix2 (-48)) (IZR 756 * bpow radix2 (-75)) (IZR 1009 * bpow radix2 (-71)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 189 (-189) (-73)); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_31.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_31.l1 th_ tl_ dg).
Qed.

Lemma segok_31 : SegOkRow [(0x3fe02e46075785a1)%Z; (0x3c7d1c9139aa7a36)%Z; (0x3ff249e3af272a2f)%Z; (0xbc790699e6080472)%Z; (0x3fd725e9b73b49e3)%Z; (0x3fde944a5ba62b0e)%Z; (0x3fe122c3716a7f72)%Z; (0x3fe82bf37a2f3860)%Z; (0x3ff17173067c07c8)%Z; (0x3ffabf04da5f557c)%Z; (0x40051ec661b8ef76)%Z; (0x40111158dc35253e)%Z; (0xc03f3fd5c3aaf7fb)%Z] (IZR 756 * bpow radix2 (-75)).
Proof.
  unfold SegOkRow. cbn [nth].
  destruct (word_ok_intro (0x3fe02e46075785a1)%Z false 4554477933135265%positive 53%nat (4554477933135265)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c7d1c9139aa7a36)%Z false 8194184387918390%positive 108%nat (4097092193959195)%Z 1%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3ff249e3af272a2f)%Z false 5147791825775151%positive 52%nat (5147791825775151)%Z 0%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc790699e6080472)%Z true 7044132476814450%positive 108%nat (-3522066238407225)%Z 1%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0x3fd725e9b73b49e3)%Z false 6515610196068835%positive 54%nat (6515610196068835)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fde944a5ba62b0e)%Z false 8607296387427086%positive 54%nat (4303648193713543)%Z 1%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fe122c3716a7f72)%Z false 4823297420853106%positive 53%nat (2411648710426553)%Z 1%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3fe82bf37a2f3860)%Z false 6803724168018016%positive 53%nat (212616380250563)%Z 5%Z (-48)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3ff17173067c07c8)%Z false 4909813448050632%positive 52%nat (613726681006329)%Z 3%Z (-49)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x3ffabf04da5f557c)%Z false 7528376958932348%positive 52%nat (1882094239733087)%Z 2%Z (-50)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x40051ec661b8ef76)%Z false 5944811902791542%positive 51%nat (2972405951395771)%Z 1%Z (-50)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x40111158dc35253e)%Z false 4804147953345854%positive 50%nat (2402073976672927)%Z 1%Z (-49)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc03f3fd5c3aaf7fb)%Z true 8795911621375995%positive 48%nat (-8795911621375995)%Z 0%Z (-48)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_31 _ _).
  all: seg_numeric.
Qed.

Lemma evalcert_32 : EvalCert (IZR (1300077228592327) * bpow radix2 (-50)) (IZR (5427618362502125) * bpow radix2 (-106)) (IZR (3466872609579539) * bpow radix2 (-53)) (IZR (2311248406386359) * bpow radix2 (-52)) (IZR (1348228237051475) * bpow radix2 (-51)) (IZR (243965109564779) * bpow radix2 (-48)) (IZR (2910461382898369) * bpow radix2 (-51)) (IZR (4598038638091141) * bpow radix2 (-51)) (IZR (3733284131994545) * bpow radix2 (-50)) (IZR (6243166936059511) * bpow radix2 (-50)) (IZR (5569593202407149) * bpow radix2 (-47)) (IZR 805 * bpow radix2 (-75)) (IZR 543 * bpow radix2 (-70)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 805 (-805) (-75)); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_32.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_32.l1 th_ tl_ dg).
Qed.

Lemma segok_32 : SegOkRow [(0x3fe0c152382d7366)%Z; (0xbc8ee6913347c2a6)%Z; (0x3ff279a74590331c)%Z; (0x3c934863e0792bed)%Z; (0x3fd8a2345cc04426)%Z; (0x3fe06c22e8802d6e)%Z; (0x3fe328d36495194c)%Z; (0x3febbc51b62ead60)%Z; (0x3ff4ae1931b86582)%Z; (0x400055e44bafdb85)%Z; (0x400a86cde510f762)%Z; (0x40162e20937f4e77)%Z; (0x4043c983f85f76ed)%Z] (IZR 805 * bpow radix2 (-75)).
Proof.
  unfold SegOkRow. cbn [nth].
  destruct (word_ok_intro (0x3fe0c152382d7366)%Z false 4716158501352294%positive 53%nat (2358079250676147)%Z 1%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc8ee6913347c2a6)%Z true 8697760606306982%positive 107%nat (-4348880303153491)%Z 1%Z (-106)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3ff279a74590331c)%Z false 5200308914369308%positive 52%nat (1300077228592327)%Z 2%Z (-50)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c934863e0792bed)%Z false 5427618362502125%positive 106%nat (5427618362502125)%Z 0%Z (-106)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0x3fd8a2345cc04426)%Z false 6933745219159078%positive 54%nat (3466872609579539)%Z 1%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fe06c22e8802d6e)%Z false 4622496812772718%positive 53%nat (2311248406386359)%Z 1%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fe328d36495194c)%Z false 5392912948205900%positive 53%nat (1348228237051475)%Z 2%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3febbc51b62ead60)%Z false 7806883506072928%positive 53%nat (243965109564779)%Z 5%Z (-48)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3ff4ae1931b86582)%Z false 5820922765796738%positive 52%nat (2910461382898369)%Z 1%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x400055e44bafdb85)%Z false 4598038638091141%positive 51%nat (4598038638091141)%Z 0%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x400a86cde510f762)%Z false 7466568263989090%positive 51%nat (3733284131994545)%Z 1%Z (-50)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x40162e20937f4e77)%Z false 6243166936059511%positive 50%nat (6243166936059511)%Z 0%Z (-50)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x4043c983f85f76ed)%Z false 5569593202407149%positive 47%nat (5569593202407149)%Z 0%Z (-47)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_32 _ _).
  all: seg_numeric.
Qed.

Lemma evalcert_33 : EvalCert (IZR (2628106974626967) * bpow radix2 (-51)) (IZR (1167323935010109) * bpow radix2 (-104)) (IZR (1845880256206237) * bpow radix2 (-52)) (IZR (1244885460114997) * bpow radix2 (-51)) (IZR (6048045941157083) * bpow radix2 (-53)) (IZR (4499693009503049) * bpow radix2 (-52)) (IZR (3468757479485465) * bpow radix2 (-51)) (IZR (2826346812666525) * bpow radix2 (-50)) (IZR (296416027059505) * bpow radix2 (-46)) (IZR (8176618898136695) * bpow radix2 (-50)) (IZR (7053658890318003) * bpow radix2 (-48)) (IZR 857 * bpow radix2 (-75)) (IZR 585 * bpow radix2 (-70)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 857 (-857) (-75)); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_33.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_33.l1 th_ tl_ dg).
Qed.

Lemma segok_33 : SegOkRow [(0x3fe155e8b2a00052)%Z; (0x3c6bb9429fa5e8f6)%Z; (0x3ff2ac7fad4f092e)%Z; (0x3c9096b321efb4f4)%Z; (0x3fda3b45f3e05674)%Z; (0x3fe1b0ddee8b78d4)%Z; (0x3fe57caa6de86cdb)%Z; (0x3feff8e4d6dc0692)%Z; (0x3ff8a5a212c0e032)%Z; (0x400415184b8fe53a)%Z; (0x4010d96bbffa5310)%Z; (0x401d0c9770e31e77)%Z; (0x40390f43f08630b3)%Z] (IZR 857 * bpow radix2 (-75)).
Proof.
  unfold SegOkRow. cbn [nth].
  destruct (word_ok_intro (0x3fe155e8b2a00052)%Z false 4879532521685074%positive 53%nat (2439766260842537)%Z 1%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c6bb9429fa5e8f6)%Z false 7803520168618230%positive 109%nat (3901760084309115)%Z 1%Z (-108)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3ff2ac7fad4f092e)%Z false 5256213949253934%positive 52%nat (2628106974626967)%Z 1%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c9096b321efb4f4)%Z false 4669295740040436%positive 106%nat (1167323935010109)%Z 2%Z (-104)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0x3fda3b45f3e05674)%Z false 7383521024824948%positive 54%nat (1845880256206237)%Z 2%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fe1b0ddee8b78d4)%Z false 4979541840459988%positive 53%nat (1244885460114997)%Z 2%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fe57caa6de86cdb)%Z false 6048045941157083%positive 53%nat (6048045941157083)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3feff8e4d6dc0692)%Z false 8999386019006098%positive 53%nat (4499693009503049)%Z 1%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3ff8a5a212c0e032)%Z false 6937514958970930%positive 52%nat (3468757479485465)%Z 1%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x400415184b8fe53a)%Z false 5652693625333050%positive 51%nat (2826346812666525)%Z 1%Z (-50)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x4010d96bbffa5310)%Z false 4742656432952080%positive 50%nat (296416027059505)%Z 4%Z (-46)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x401d0c9770e31e77)%Z false 8176618898136695%positive 50%nat (8176618898136695)%Z 0%Z (-50)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x40390f43f08630b3)%Z false 7053658890318003%positive 48%nat (7053658890318003)%Z 0%Z (-48)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_33 _ _).
  all: seg_numeric.
Qed.

Lemma evalcert_34 : EvalCert (IZR (5315768793841329) * bpow radix2 (-52)) (IZR (-119640199650705) * bpow radix2 (-100)) (IZR (7868784282584171) * bpow radix2 (-54)) (IZR (2690311841152427) * bpow radix2 (-52)) (IZR (3402560059982075) * bpow radix2 (-52)) (IZR (2606180570145789) * bpow radix2 (-51)) (IZR (4157509379265079) * bpow radix2 (-51)) (IZR (6996741369689371) * bpow radix2 (-51)) (IZR (6064674193936963) * bpow radix2 (-50)) (IZR (5404690659381237) * bpow radix2 (-49)) (IZR (13105765839257) * bpow radix2 (-38)) (IZR 914 * bpow radix2 (-75)) (IZR 633 * bpow radix2 (-70)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 457 (-457) (-74)); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_34.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_34.l1 th_ tl_ dg).
Qed.

Lemma segok_34 : SegOkRow [(0x3fe1ec230c714a96)%Z; (0x3c841dc77911b08c)%Z; (0x3ff2e2a9deaa3eb1)%Z; (0xbc9b33f9e6776440)%Z; (0x3fdbf49e1bfa446b)%Z; (0x3fe31da61340fb56)%Z; (0x3fe82d387f6781f6)%Z; (0x3ff2849d663547fa)%Z; (0x3ffd8a772b67246e)%Z; (0x4008db7fcbecf51b)%Z; (0x40158bc9ff021243)%Z; (0x402333899adf8ff5)%Z; (0x4047d6d908e33200)%Z] (IZR 914 * bpow radix2 (-75)).
Proof.
  unfold SegOkRow. cbn [nth].
  destruct (word_ok_intro (0x3fe1ec230c714a96)%Z false 5044709880842902%positive 53%nat (2522354940421451)%Z 1%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c841dc77911b08c)%Z false 5662242101112972%positive 107%nat (1415560525278243)%Z 2%Z (-105)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3ff2e2a9deaa3eb1)%Z false 5315768793841329%positive 52%nat (5315768793841329)%Z 0%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc9b33f9e6776440)%Z true 7656972777645120%positive 106%nat (-119640199650705)%Z 6%Z (-100)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0x3fdbf49e1bfa446b)%Z false 7868784282584171%positive 54%nat (7868784282584171)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fe31da61340fb56)%Z false 5380623682304854%positive 53%nat (2690311841152427)%Z 1%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fe82d387f6781f6)%Z false 6805120119964150%positive 53%nat (3402560059982075)%Z 1%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3ff2849d663547fa)%Z false 5212361140291578%positive 52%nat (2606180570145789)%Z 1%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x3ffd8a772b67246e)%Z false 8315018758530158%positive 52%nat (4157509379265079)%Z 1%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x4008db7fcbecf51b)%Z false 6996741369689371%positive 51%nat (6996741369689371)%Z 0%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x40158bc9ff021243)%Z false 6064674193936963%positive 50%nat (6064674193936963)%Z 0%Z (-50)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x402333899adf8ff5)%Z false 5404690659381237%positive 49%nat (5404690659381237)%Z 0%Z (-49)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x4047d6d908e33200)%Z false 6710152109699584%positive 47%nat (13105765839257)%Z 9%Z (-38)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_34 _ _).
  all: seg_numeric.
Qed.

Lemma evalcert_35 : EvalCert (IZR (2689633817288871) * bpow radix2 (-51)) (IZR (1393391792459019) * bpow radix2 (-104)) (IZR (65577975343163) * bpow radix2 (-47)) (IZR (1458181117694705) * bpow radix2 (-51)) (IZR (7684402452482127) * bpow radix2 (-53)) (IZR (6069168205411905) * bpow radix2 (-52)) (IZR (5013204213616159) * bpow radix2 (-51)) (IZR (4361735350807281) * bpow radix2 (-50)) (IZR (1958776140481007) * bpow radix2 (-48)) (IZR (7210977038642177) * bpow radix2 (-49)) (IZR (-8815200010715801) * bpow radix2 (-49)) (IZR 975 * bpow radix2 (-75)) (IZR 686 * bpow radix2 (-70)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 975 (-975) (-75)); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_35.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_35.l1 th_ tl_ dg).
Qed.

Lemma segok_35 : SegOkRow [(0x3fe2841ce0862975)%Z; (0xbc87ed81c0e02251)%Z; (0x3ff31c6a5882c14e)%Z; (0x3c93cd213b4a342c)%Z; (0x3fddd247f6741d80)%Z; (0x3fe4b8d4fe274bc4)%Z; (0x3feb4cec5e7dc84f)%Z; (0x3ff58fe056f73641)%Z; (0x4001cf7b9056ce1f)%Z; (0x400efdf34c60d5e2)%Z; (0x401bd5fc703107bc)%Z; (0x40299e586cdf2c01)%Z; (0xc02f5160b1434299)%Z] (IZR 975 * bpow radix2 (-75)).
Proof.
  unfold SegOkRow. cbn [nth].
  destruct (word_ok_intro (0x3fe2841ce0862975)%Z false 5211809141631349%positive 53%nat (5211809141631349)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc87ed81c0e02251)%Z true 6735066006823505%positive 107%nat (-6735066006823505)%Z 0%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3ff31c6a5882c14e)%Z false 5379267634577742%positive 52%nat (2689633817288871)%Z 1%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c93cd213b4a342c)%Z false 5573567169836076%positive 106%nat (1393391792459019)%Z 2%Z (-104)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0x3fddd247f6741d80)%Z false 8393980843924864%positive 54%nat (65577975343163)%Z 7%Z (-47)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fe4b8d4fe274bc4)%Z false 5832724470778820%positive 53%nat (1458181117694705)%Z 2%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3feb4cec5e7dc84f)%Z false 7684402452482127%positive 53%nat (7684402452482127)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3ff58fe056f73641)%Z false 6069168205411905%positive 52%nat (6069168205411905)%Z 0%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x4001cf7b9056ce1f)%Z false 5013204213616159%positive 51%nat (5013204213616159)%Z 0%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x400efdf34c60d5e2)%Z false 8723470701614562%positive 51%nat (4361735350807281)%Z 1%Z (-50)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x401bd5fc703107bc)%Z false 7835104561924028%positive 50%nat (1958776140481007)%Z 2%Z (-48)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x40299e586cdf2c01)%Z false 7210977038642177%positive 49%nat (7210977038642177)%Z 0%Z (-49)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc02f5160b1434299)%Z true 8815200010715801%positive 49%nat (-8815200010715801)%Z 0%Z (-49)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_35 _ _).
  all: seg_numeric.
Qed.

Lemma evalcert_36 : EvalCert (IZR (5447042111371653) * bpow radix2 (-52)) (IZR (4089041772631895) * bpow radix2 (-106)) (IZR (8964275017571635) * bpow radix2 (-54)) (IZR (6344240351060221) * bpow radix2 (-53)) (IZR (272221249513281) * bpow radix2 (-48)) (IZR (3552871733314005) * bpow radix2 (-51)) (IZR (1521083548800615) * bpow radix2 (-49)) (IZR (685067029789715) * bpow radix2 (-47)) (IZR (5094788835348309) * bpow radix2 (-49)) (IZR (1215081273387691) * bpow radix2 (-46)) (IZR (8650594972180409) * bpow radix2 (-48)) (IZR 521 * bpow radix2 (-74)) (IZR 747 * bpow radix2 (-70)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 521 (-521) (-74)); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_36.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_36.l1 th_ tl_ dg).
Qed.

Lemma segok_36 : SegOkRow [(0x3fe31df40fbd31cd)%Z; (0x3c310ebcfd1cc29d)%Z; (0x3ff35a0e521ff985)%Z; (0x3c8d0dec74a8aeae)%Z; (0x3fdfd8f5ec175d33)%Z; (0x3fe68a0d907ea0fd)%Z; (0x3feef2ae5c14e820)%Z; (0x3ff93ea2d33183aa)%Z; (0x40059dab7266599c)%Z; (0x40137884c7a9e098)%Z; (0x402219aef6bc8f55)%Z; (0x403144709eb1aaac)%Z; (0x403ebbab98699fb9)%Z] (IZR 521 * bpow radix2 (-74)).
Proof.
  unfold SegOkRow. cbn [nth].
  destruct (word_ok_intro (0x3fe31df40fbd31cd)%Z false 5380958630785485%positive 53%nat (5380958630785485)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c310ebcfd1cc29d)%Z false 4801279467242141%positive 112%nat (4801279467242141)%Z 0%Z (-112)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3ff35a0e521ff985)%Z false 5447042111371653%positive 52%nat (5447042111371653)%Z 0%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c8d0dec74a8aeae)%Z false 8178083545263790%positive 107%nat (4089041772631895)%Z 1%Z (-106)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0x3fdfd8f5ec175d33)%Z false 8964275017571635%positive 54%nat (8964275017571635)%Z 0%Z (-54)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fe68a0d907ea0fd)%Z false 6344240351060221%positive 53%nat (6344240351060221)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3feef2ae5c14e820)%Z false 8711079984424992%positive 53%nat (272221249513281)%Z 5%Z (-48)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3ff93ea2d33183aa)%Z false 7105743466628010%positive 52%nat (3552871733314005)%Z 1%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x40059dab7266599c)%Z false 6084334195202460%positive 51%nat (1521083548800615)%Z 2%Z (-49)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x40137884c7a9e098)%Z false 5480536238317720%positive 50%nat (685067029789715)%Z 3%Z (-47)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x402219aef6bc8f55)%Z false 5094788835348309%positive 49%nat (5094788835348309)%Z 0%Z (-49)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x403144709eb1aaac)%Z false 4860325093550764%positive 48%nat (1215081273387691)%Z 2%Z (-46)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x403ebbab98699fb9)%Z false 8650594972180409%positive 48%nat (8650594972180409)%Z 0%Z (-48)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_36 _ _).
  all: seg_numeric.
Qed.

Lemma evalcert_37 : EvalCert (IZR (5519467488403195) * bpow radix2 (-52)) (IZR (4150199042690085) * bpow radix2 (-106)) (IZR (4792848922823163) * bpow radix2 (-53)) (IZR (6925331570741381) * bpow radix2 (-53)) (IZR (4958345772924727) * bpow radix2 (-52)) (IZR (4184138885586199) * bpow radix2 (-51)) (IZR (3717985797536125) * bpow radix2 (-50)) (IZR (3471914362413973) * bpow radix2 (-49)) (IZR (3349664926694743) * bpow radix2 (-48)) (IZR (6622172630820801) * bpow radix2 (-48)) (IZR (-692675871695181) * bpow radix2 (-45)) (IZR 557 * bpow radix2 (-74)) (IZR 816 * bpow radix2 (-70)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 557 (-557) (-74)); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_37.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_37.l1 th_ tl_ dg).
Qed.

Lemma segok_37 : SegOkRow [(0x3fe3b9c90c43296d)%Z; (0xbc776eebb78fe641)%Z; (0x3ff39bed2afedefb)%Z; (0x3c8d7d2b075f984a)%Z; (0x3fe107121981c9fb)%Z; (0x3fe89a8d6839d085)%Z; (0x3ff19d96d677ff37)%Z; (0x3ffdbae77feeba2e)%Z; (0x400a6afa0d7bf2fa)%Z; (0x4018ab601c86472a)%Z; (0x4027cd014824faae)%Z; (0x403786d4b74d27c1)%Z; (0xc033afe15a370a68)%Z] (IZR 557 * bpow radix2 (-74)).
Proof.
  unfold SegOkRow. cbn [nth].
  destruct (word_ok_intro (0x3fe3b9c90c43296d)%Z false 5552297702795629%positive 53%nat (5552297702795629)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc776eebb78fe641)%Z true 6595883140376129%positive 108%nat (-6595883140376129)%Z 0%Z (-108)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3ff39bed2afedefb)%Z false 5519467488403195%positive 52%nat (5519467488403195)%Z 0%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c8d7d2b075f984a)%Z false 8300398085380170%positive 107%nat (4150199042690085)%Z 1%Z (-106)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0x3fe107121981c9fb)%Z false 4792848922823163%positive 53%nat (4792848922823163)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3fe89a8d6839d085)%Z false 6925331570741381%positive 53%nat (6925331570741381)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3ff19d96d677ff37)%Z false 4958345772924727%positive 52%nat (4958345772924727)%Z 0%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x3ffdbae77feeba2e)%Z false 8368277771172398%positive 52%nat (4184138885586199)%Z 1%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x400a6afa0d7bf2fa)%Z false 7435971595072250%positive 51%nat (3717985797536125)%Z 1%Z (-50)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x4018ab601c86472a)%Z false 6943828724827946%positive 50%nat (3471914362413973)%Z 1%Z (-49)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x4027cd014824faae)%Z false 6699329853389486%positive 49%nat (3349664926694743)%Z 1%Z (-48)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x403786d4b74d27c1)%Z false 6622172630820801%positive 48%nat (6622172630820801)%Z 0%Z (-48)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xc033afe15a370a68)%Z true 5541406973561448%positive 48%nat (-692675871695181)%Z 3%Z (-45)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_37 _ _).
  all: seg_numeric.
Qed.

Lemma evalcert_38 : EvalCert (IZR (5596970123316373) * bpow radix2 (-52)) (IZR (-8347570507691329) * bpow radix2 (-108)) (IZR (320791651110139) * bpow radix2 (-49)) (IZR (1897094136786609) * bpow radix2 (-51)) (IZR (5670525123030287) * bpow radix2 (-52)) (IZR (154956470145451) * bpow radix2 (-46)) (IZR (2289095161802765) * bpow radix2 (-49)) (IZR (1109601829024885) * bpow radix2 (-47)) (IZR (4446131623821647) * bpow radix2 (-48)) (IZR (2282453322514225) * bpow radix2 (-46)) (IZR (-5647811859201235) * bpow radix2 (-52)) (IZR 597 * bpow radix2 (-74)) (IZR 895 * bpow radix2 (-70)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 597 (-597) (-74)); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_38.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_38.l1 th_ tl_ dg).
Qed.

Lemma segok_38 : SegOkRow [(0x3fe457bf318fe517)%Z; (0xbc86189642d67942)%Z; (0x3ff3e26a2804cc95)%Z; (0xbc7da81236d93541)%Z; (0x3fe23c220694cfb0)%Z; (0x3feaf5969883bac4)%Z; (0x3ff4255003a5ed0f)%Z; (0x40019dd3ab7a3560)%Z; (0x401043d6fff3e01a)%Z; (0x401f896a76e3a3a8)%Z; (0x402f97776020029e)%Z; (0x404037c227027e62)%Z; (0xbff410a7aba03cd3)%Z] (IZR 597 * bpow radix2 (-74)).
Proof.
  unfold SegOkRow. cbn [nth].
  destruct (word_ok_intro (0x3fe457bf318fe517)%Z false 5725978216097047%positive 53%nat (5725978216097047)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc86189642d67942)%Z true 6219483133147458%positive 107%nat (-3109741566573729)%Z 1%Z (-106)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3ff3e26a2804cc95)%Z false 5596970123316373%positive 52%nat (5596970123316373)%Z 0%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc7da81236d93541)%Z true 8347570507691329%positive 108%nat (-8347570507691329)%Z 0%Z (-108)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0x3fe23c220694cfb0)%Z false 5132666417762224%positive 53%nat (320791651110139)%Z 4%Z (-49)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3feaf5969883bac4)%Z false 7588376547146436%positive 53%nat (1897094136786609)%Z 2%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3ff4255003a5ed0f)%Z false 5670525123030287%positive 52%nat (5670525123030287)%Z 0%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x40019dd3ab7a3560)%Z false 4958607044654432%positive 51%nat (154956470145451)%Z 5%Z (-46)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x401043d6fff3e01a)%Z false 4578190323605530%positive 50%nat (2289095161802765)%Z 1%Z (-49)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x401f896a76e3a3a8)%Z false 8876814632199080%positive 50%nat (1109601829024885)%Z 3%Z (-47)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x402f97776020029e)%Z false 8892263247643294%positive 49%nat (4446131623821647)%Z 1%Z (-48)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x404037c227027e62)%Z false 4564906645028450%positive 47%nat (2282453322514225)%Z 1%Z (-46)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0xbff410a7aba03cd3)%Z true 5647811859201235%positive 52%nat (-5647811859201235)%Z 0%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_38 _ _).
  all: seg_numeric.
Qed.

Lemma evalcert_39 : EvalCert (IZR (5680036569571777) * bpow radix2 (-52)) (IZR (-978854697390233) * bpow radix2 (-103)) (IZR (5505775253456759) * bpow radix2 (-53)) (IZR (260892697762339) * bpow radix2 (-48)) (IZR (6517426295913093) * bpow radix2 (-52)) (IZR (5916220034362889) * bpow radix2 (-51)) (IZR (5683319550412733) * bpow radix2 (-50)) (IZR (5728884039449369) * bpow radix2 (-49)) (IZR (5964421482402675) * bpow radix2 (-48)) (IZR (1593208313829191) * bpow radix2 (-45)) (IZR (7673297956373999) * bpow radix2 (-46)) (IZR 640 * bpow radix2 (-74)) (IZR 986 * bpow radix2 (-70)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 5 (-5) (-67)); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_39.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_39.l1 th_ tl_ dg).
Qed.

Lemma segok_39 : SegOkRow [(0x3fe4f7fd2bc2fb34)%Z; (0xbc8d7c3a91e5f88b)%Z; (0x3ff42df6920a61c1)%Z; (0xbc9bd21af43284c8)%Z; (0x3fe38f7932320777)%Z; (0x3feda8fa12634460)%Z; (0x3ff727908f37ba85)%Z; (0x400504c5518fae09)%Z; (0x401430f2f2f287bd)%Z; (0x40245a63c2217b19)%Z; (0x4035309c17bfd373)%Z; (0x4046a40ede655d1c)%Z; (0x405b42d2e6f205ef)%Z] (IZR 640 * bpow radix2 (-74)).
Proof.
  unfold SegOkRow. cbn [nth].
  destruct (word_ok_intro (0x3fe4f7fd2bc2fb34)%Z false 5902166267198260%positive 53%nat (1475541566799565)%Z 2%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc8d7c3a91e5f88b)%Z true 8299365322324107%positive 107%nat (-8299365322324107)%Z 0%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3ff42df6920a61c1)%Z false 5680036569571777%positive 52%nat (5680036569571777)%Z 0%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc9bd21af43284c8)%Z true 7830837579121864%positive 106%nat (-978854697390233)%Z 3%Z (-103)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0x3fe38f7932320777)%Z false 5505775253456759%positive 53%nat (5505775253456759)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3feda8fa12634460)%Z false 8348566328394848%positive 53%nat (260892697762339)%Z 5%Z (-48)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3ff727908f37ba85)%Z false 6517426295913093%positive 52%nat (6517426295913093)%Z 0%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x400504c5518fae09)%Z false 5916220034362889%positive 51%nat (5916220034362889)%Z 0%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x401430f2f2f287bd)%Z false 5683319550412733%positive 50%nat (5683319550412733)%Z 0%Z (-50)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x40245a63c2217b19)%Z false 5728884039449369%positive 49%nat (5728884039449369)%Z 0%Z (-49)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x4035309c17bfd373)%Z false 5964421482402675%positive 48%nat (5964421482402675)%Z 0%Z (-48)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x4046a40ede655d1c)%Z false 6372833255316764%positive 47%nat (1593208313829191)%Z 2%Z (-45)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x405b42d2e6f205ef)%Z false 7673297956373999%positive 46%nat (7673297956373999)%Z 0%Z (-46)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_39 _ _).
  all: seg_numeric.
Qed.

Lemma evalcert_40 : EvalCert (IZR (5769224750464927) * bpow radix2 (-52)) (IZR (189688914154421) * bpow radix2 (-103)) (IZR (2958576795110219) * bpow radix2 (-52)) (IZR (2306172681316683) * bpow radix2 (-51)) (IZR (7531630079337669) * bpow radix2 (-52)) (IZR (7110343985822305) * bpow radix2 (-51)) (IZR (7117441727771049) * bpow radix2 (-50)) (IZR (934001725518031) * bpow radix2 (-46)) (IZR (4052056845230451) * bpow radix2 (-47)) (IZR (1127407690999829) * bpow radix2 (-44)) (IZR (2416936059242791) * bpow radix2 (-44)) (IZR 688 * bpow radix2 (-74)) (IZR 546 * bpow radix2 (-69)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 43 (-43) (-70)); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_40.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_40.l1 th_ tl_ dg).
Qed.

Lemma segok_40 : SegOkRow [(0x3fe59aad71ced00f)%Z; (0xbc5b5b31565e9408)%Z; (0x3ff47f144fe17f9f)%Z; (0x3c7590ac8b1276a0)%Z; (0x3fe5059eadd39696)%Z; (0x3ff062e756ebd296)%Z; (0x3ffac1fa477564c5)%Z; (0x400942d1f7817a61)%Z; (0x4019494689e4b1a9)%Z; (0x402a8bc1c88d8678)%Z; (0x403ccaa601bd42e6)%Z; (0x4050057c3bc1a054)%Z; (0x40612c618e83124e)%Z] (IZR 688 * bpow radix2 (-74)).
Proof.
  unfold SegOkRow. cbn [nth].
  destruct (word_ok_intro (0x3fe59aad71ced00f)%Z false 6081044240322575%positive 53%nat (6081044240322575)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc5b5b31565e9408)%Z true 7700091831751688%positive 110%nat (-962511478968961)%Z 3%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3ff47f144fe17f9f)%Z false 5769224750464927%positive 52%nat (5769224750464927)%Z 0%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c7590ac8b1276a0)%Z false 6070045252941472%positive 108%nat (189688914154421)%Z 5%Z (-103)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0x3fe5059eadd39696)%Z false 5917153590220438%positive 53%nat (2958576795110219)%Z 1%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3ff062e756ebd296)%Z false 4612345362633366%positive 52%nat (2306172681316683)%Z 1%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3ffac1fa477564c5)%Z false 7531630079337669%positive 52%nat (7531630079337669)%Z 0%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x400942d1f7817a61)%Z false 7110343985822305%positive 51%nat (7110343985822305)%Z 0%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x4019494689e4b1a9)%Z false 7117441727771049%positive 50%nat (7117441727771049)%Z 0%Z (-50)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x402a8bc1c88d8678)%Z false 7472013804144248%positive 49%nat (934001725518031)%Z 3%Z (-46)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x403ccaa601bd42e6)%Z false 8104113690460902%positive 48%nat (4052056845230451)%Z 1%Z (-47)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x4050057c3bc1a054)%Z false 4509630763999316%positive 46%nat (1127407690999829)%Z 2%Z (-44)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x40612c618e83124e)%Z false 4833872118485582%positive 45%nat (2416936059242791)%Z 1%Z (-44)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_40 _ _).
  all: seg_numeric.
Qed.

Lemma evalcert_41 : EvalCert (IZR (5865177785022393) * bpow radix2 (-52)) (IZR (-6333963736564785) * bpow radix2 (-108)) (IZR (99574446867875) * bpow radix2 (-47)) (IZR (5120094626298279) * bpow radix2 (-52)) (IZR (4377719325211449) * bpow radix2 (-51)) (IZR (4306556712450301) * bpow radix2 (-50)) (IZR (8998859513042027) * bpow radix2 (-50)) (IZR (4928150865958043) * bpow radix2 (-48)) (IZR (1393823401754525) * bpow radix2 (-45)) (IZR (101205329381547) * bpow radix2 (-40)) (IZR (2744161264153755) * bpow radix2 (-43)) (IZR 742 * bpow radix2 (-74)) (IZR 606 * bpow radix2 (-69)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 371 (-371) (-73)); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_41.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_41.l1 th_ tl_ dg).
Qed.

Lemma segok_41 : SegOkRow [(0x3fe63ffed6d198f6)%Z; (0x3c8b5625ef0627b6)%Z; (0x3ff4d6591e6bb7b9)%Z; (0xbc7680b4da89c431)%Z; (0x3fe6a3fee23168c0)%Z; (0x3ff230b2ed6ab9a7)%Z; (0x3fff1b066a9c7672)%Z; (0x400e9994be19f1fa)%Z; (0x401ff86a40a8946b)%Z; (0x4031822089c3d49b)%Z; (0x4043ceb332f6fe74)%Z; (0x405702eced422ac0)%Z; (0x40737f99aab66936)%Z] (IZR 742 * bpow radix2 (-74)).
Proof.
  unfold SegOkRow. cbn [nth].
  destruct (word_ok_intro (0x3fe63ffed6d198f6)%Z false 6262813245937910%positive 53%nat (3131406622968955)%Z 1%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c8b5625ef0627b6)%Z false 7694545295124406%positive 107%nat (3847272647562203)%Z 1%Z (-106)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3ff4d6591e6bb7b9)%Z false 5865177785022393%positive 52%nat (5865177785022393)%Z 0%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc7680b4da89c431)%Z true 6333963736564785%positive 108%nat (-6333963736564785)%Z 0%Z (-108)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0x3fe6a3fee23168c0)%Z false 6372764599544000%positive 53%nat (99574446867875)%Z 6%Z (-47)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3ff230b2ed6ab9a7)%Z false 5120094626298279%positive 52%nat (5120094626298279)%Z 0%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x3fff1b066a9c7672)%Z false 8755438650422898%positive 52%nat (4377719325211449)%Z 1%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x400e9994be19f1fa)%Z false 8613113424900602%positive 51%nat (4306556712450301)%Z 1%Z (-50)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x401ff86a40a8946b)%Z false 8998859513042027%positive 50%nat (8998859513042027)%Z 0%Z (-50)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x4031822089c3d49b)%Z false 4928150865958043%positive 48%nat (4928150865958043)%Z 0%Z (-48)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x4043ceb332f6fe74)%Z false 5575293607018100%positive 47%nat (1393823401754525)%Z 2%Z (-45)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x405702eced422ac0)%Z false 6477141080419008%positive 46%nat (101205329381547)%Z 6%Z (-40)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x40737f99aab66936)%Z false 5488322528307510%positive 44%nat (2744161264153755)%Z 1%Z (-43)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_41 _ _).
  all: seg_numeric.
Qed.

Lemma evalcert_42 : EvalCert (IZR (2984320620957201) * bpow radix2 (-51)) (IZR (-2859391599151177) * bpow radix2 (-106)) (IZR (3439903014207957) * bpow radix2 (-52)) (IZR (5712286330762385) * bpow radix2 (-52)) (IZR (1280547615789565) * bpow radix2 (-49)) (IZR (5261635984958169) * bpow radix2 (-50)) (IZR (2874111606524593) * bpow radix2 (-48)) (IZR (411324418929619) * bpow radix2 (-44)) (IZR (3802474628415) * bpow radix2 (-36)) (IZR (2363479769120063) * bpow radix2 (-44)) (IZR (4644975817658749) * bpow radix2 (-44)) (IZR 801 * bpow radix2 (-74)) (IZR 677 * bpow radix2 (-69)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 801 (-801) (-74)); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_42.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_42.l1 th_ tl_ dg).
Qed.

Lemma segok_42 : SegOkRow [(0x3fe6e825383cc40b)%Z; (0x3c71a9ec7321e76a)%Z; (0x3ff5347295041c22)%Z; (0xbc845133f9151092)%Z; (0x3fe87125aa7283aa)%Z; (0x3ff44b4b4d99b491)%Z; (0x4002329ae70747f4)%Z; (0x4012b16e17d222d9)%Z; (0x40246bfa82b41562)%Z; (0x4037618ede0b3d30)%Z; (0x404baaa93229f800)%Z; (0x4060cb250824fa7e)%Z; (0x40708094b59a117d)%Z] (IZR 801 * bpow radix2 (-74)).
Proof.
  unfold SegOkRow. cbn [nth].
  destruct (word_ok_intro (0x3fe6e825383cc40b)%Z false 6447696042574859%positive 53%nat (6447696042574859)%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c71a9ec7321e76a)%Z false 4971907613058922%positive 108%nat (2485953806529461)%Z 1%Z (-107)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3ff5347295041c22)%Z false 5968641241914402%positive 52%nat (2984320620957201)%Z 1%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc845133f9151092)%Z true 5718783198302354%positive 107%nat (-2859391599151177)%Z 1%Z (-106)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0x3fe87125aa7283aa)%Z false 6879806028415914%positive 53%nat (3439903014207957)%Z 1%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3ff44b4b4d99b491)%Z false 5712286330762385%positive 52%nat (5712286330762385)%Z 0%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x4002329ae70747f4)%Z false 5122190463158260%positive 51%nat (1280547615789565)%Z 2%Z (-49)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x4012b16e17d222d9)%Z false 5261635984958169%positive 50%nat (5261635984958169)%Z 0%Z (-50)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x40246bfa82b41562)%Z false 5748223213049186%positive 49%nat (2874111606524593)%Z 1%Z (-48)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x4037618ede0b3d30)%Z false 6581190702873904%positive 48%nat (411324418929619)%Z 4%Z (-44)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x404baaa93229f800)%Z false 7787468038993920%positive 47%nat (3802474628415)%Z 11%Z (-36)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x4060cb250824fa7e)%Z false 4726959538240126%positive 45%nat (2363479769120063)%Z 1%Z (-44)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x40708094b59a117d)%Z false 4644975817658749%positive 44%nat (4644975817658749)%Z 0%Z (-44)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_42 _ _).
  all: seg_numeric.
Qed.

Lemma evalcert_43 : EvalCert (IZR (6080484871944967) * bpow radix2 (-52)) (IZR (-580507558600809) * bpow radix2 (-103)) (IZR (1861759497951997) * bpow radix2 (-51)) (IZR (1601921296837511) * bpow radix2 (-50)) (IZR (3018055367916151) * bpow radix2 (-50)) (IZR (6488929709043133) * bpow radix2 (-50)) (IZR (3713767834617703) * bpow radix2 (-48)) (IZR (4453850836196419) * bpow radix2 (-47)) (IZR (5519489761216533) * bpow radix2 (-46)) (IZR (7021732080075739) * bpow radix2 (-45)) (IZR (1262807764190069) * bpow radix2 (-41)) (IZR 867 * bpow radix2 (-74)) (IZR 761 * bpow radix2 (-69)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 867 (-867) (-74)); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_43.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_43.l1 th_ tl_ dg).
Qed.

Lemma segok_43 : SegOkRow [(0x3fe7935a501afa78)%Z; (0xbc8a585b7d2a71f2)%Z; (0x3ff59a2b34dabb07)%Z; (0xbc907fbf968f0348)%Z; (0x3fea750aa6216bf4)%Z; (0x3ff6c3c1776cae1c)%Z; (0x400571cf8c3bf4ee)%Z; (0x40170da5ae47adbd)%Z; (0x402a634de91f0ece)%Z; (0x403fa581e9f2b886)%Z; (0x40539bf25a8f0815)%Z; (0x4068f23a665743db)%Z; (0x4081f21160d10dd4)%Z] (IZR 867 * bpow radix2 (-74)).
Proof.
  unfold SegOkRow. cbn [nth].
  destruct (word_ok_intro (0x3fe7935a501afa78)%Z false 6635940564630136%positive 53%nat (829492570578767)%Z 3%Z (-50)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc8a585b7d2a71f2)%Z true 7415499359678962%positive 107%nat (-3707749679839481)%Z 1%Z (-106)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3ff59a2b34dabb07)%Z false 6080484871944967%positive 52%nat (6080484871944967)%Z 0%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0xbc907fbf968f0348)%Z true 4644060468806472%positive 106%nat (-580507558600809)%Z 3%Z (-103)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0x3fea750aa6216bf4)%Z false 7447037991807988%positive 53%nat (1861759497951997)%Z 2%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3ff6c3c1776cae1c)%Z false 6407685187350044%positive 52%nat (1601921296837511)%Z 2%Z (-50)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x400571cf8c3bf4ee)%Z false 6036110735832302%positive 51%nat (3018055367916151)%Z 1%Z (-50)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x40170da5ae47adbd)%Z false 6488929709043133%positive 50%nat (6488929709043133)%Z 0%Z (-50)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x402a634de91f0ece)%Z false 7427535669235406%positive 49%nat (3713767834617703)%Z 1%Z (-48)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x403fa581e9f2b886)%Z false 8907701672392838%positive 48%nat (4453850836196419)%Z 1%Z (-47)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x40539bf25a8f0815)%Z false 5519489761216533%positive 46%nat (5519489761216533)%Z 0%Z (-46)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x4068f23a665743db)%Z false 7021732080075739%positive 45%nat (7021732080075739)%Z 0%Z (-45)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x4081f21160d10dd4)%Z false 5051231056760276%positive 43%nat (1262807764190069)%Z 2%Z (-41)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_43 _ _).
  all: seg_numeric.
Qed.

Lemma evalcert_44 : EvalCert (IZR (3100865129740775) * bpow radix2 (-51)) (IZR (4740118239254557) * bpow radix2 (-112)) (IZR (2021304677164357) * bpow radix2 (-51)) (IZR (3615208904073083) * bpow radix2 (-51)) (IZR (7169115738384441) * bpow radix2 (-51)) (IZR (1010621381371163) * bpow radix2 (-47)) (IZR (4858970293721621) * bpow radix2 (-48)) (IZR (3058982807610893) * bpow radix2 (-46)) (IZR (7961676447557205) * bpow radix2 (-46)) (IZR (5317145150283821) * bpow radix2 (-44)) (IZR (6929787242983981) * bpow radix2 (-43)) (IZR 942 * bpow radix2 (-74)) (IZR 860 * bpow radix2 (-69)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 471 (-471) (-73)); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_44.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_44.l1 th_ tl_ dg).
Qed.

Lemma segok_44 : SegOkRow [(0x3fe841deb5114bb4)%Z; (0xbc849d1c4e2eba5e)%Z; (0x3ff60870d91bf3ce)%Z; (0x3c30d71cc7d8181d)%Z; (0x3fecb976ad0f9514)%Z; (0x3ff9b006d5083ef6)%Z; (0x40097845d4f0a839)%Z; (0x401cb93d038328d8)%Z; (0x403143352e54da15)%Z; (0x4045bc41df3e4c1a)%Z; (0x405c491a40792655)%Z; (0x4072e3ea53e6e02d)%Z; (0x40889e9ad2fcb22d)%Z] (IZR 942 * bpow radix2 (-74)).
Proof.
  unfold SegOkRow. cbn [nth].
  destruct (word_ok_intro (0x3fe841deb5114bb4)%Z false 6827824217410484%positive 53%nat (1706956054352621)%Z 2%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0xbc849d1c4e2eba5e)%Z true 5802244430543454%positive 107%nat (-2901122215271727)%Z 1%Z (-106)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3ff60870d91bf3ce)%Z false 6201730259481550%positive 52%nat (3100865129740775)%Z 1%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c30d71cc7d8181d)%Z false 4740118239254557%positive 112%nat (4740118239254557)%Z 0%Z (-112)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0x3fecb976ad0f9514)%Z false 8085218708657428%positive 53%nat (2021304677164357)%Z 2%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3ff9b006d5083ef6)%Z false 7230417808146166%positive 52%nat (3615208904073083)%Z 1%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x40097845d4f0a839)%Z false 7169115738384441%positive 51%nat (7169115738384441)%Z 0%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x401cb93d038328d8)%Z false 8084971050969304%positive 50%nat (1010621381371163)%Z 3%Z (-47)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x403143352e54da15)%Z false 4858970293721621%positive 48%nat (4858970293721621)%Z 0%Z (-48)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x4045bc41df3e4c1a)%Z false 6117965615221786%positive 47%nat (3058982807610893)%Z 1%Z (-46)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x405c491a40792655)%Z false 7961676447557205%positive 46%nat (7961676447557205)%Z 0%Z (-46)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x4072e3ea53e6e02d)%Z false 5317145150283821%positive 44%nat (5317145150283821)%Z 0%Z (-44)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x40889e9ad2fcb22d)%Z false 6929787242983981%positive 43%nat (6929787242983981)%Z 0%Z (-43)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_44 _ _).
  all: seg_numeric.
Qed.

Lemma evalcert_45 : EvalCert (IZR (3166793197699573) * bpow radix2 (-51)) (IZR (5058499357955529) * bpow radix2 (-108)) (IZR (68810088795983) * bpow radix2 (-46)) (IZR (8211880192886553) * bpow radix2 (-52)) (IZR (2147240825692887) * bpow radix2 (-49)) (IZR (5094008790994567) * bpow radix2 (-49)) (IZR (3222698913457889) * bpow radix2 (-47)) (IZR (8541731814890713) * bpow radix2 (-47)) (IZR (2924764773140051) * bpow radix2 (-44)) (IZR (4112943213466937) * bpow radix2 (-43)) (IZR (1572447563680239) * bpow radix2 (-40)) (IZR 514 * bpow radix2 (-73)) (IZR 978 * bpow radix2 (-69)).
Proof.
  unfold EvalCert. intros th_ tl_ dg Th Tl Dg. split.
  - apply (rabs_bnd _ 257 (-257) (-72)); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_45.l1 th_ tl_ dg).
  - apply (rabs_bnd _ 1 (-1) 1); [reflexivity | bpow_num; lra | ].
    gappa_goal (asin_eval_45.l1 th_ tl_ dg).
Qed.

Lemma segok_45 : SegOkRow [(0x3fe8f3fb14e496b4)%Z; (0x3c873d01b84833b2)%Z; (0x3ff6805cff4083ea)%Z; (0x3c71f8ada953d5c9)%Z; (0x3fef4a8c7327a780)%Z; (0x3ffd2ca959d5c719)%Z; (0x400e839ddaa68b5c)%Z; (0x402218f958784e87)%Z; (0x4036e60e1fe8cdc2)%Z; (0x404e58a8ea97dcd9)%Z; (0x4064c81dbab58ca6)%Z; (0x407d39666e70aa72)%Z; (0x40965887e9d827bc)%Z] (IZR 514 * bpow radix2 (-73)).
Proof.
  unfold SegOkRow. cbn [nth].
  destruct (word_ok_intro (0x3fe8f3fb14e496b4)%Z false 7023659153921716%positive 53%nat (1755914788480429)%Z 2%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c873d01b84833b2)%Z false 6541002060346290%positive 107%nat (3270501030173145)%Z 1%Z (-106)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  destruct (word_ok_intro (0x3ff6805cff4083ea)%Z false 6333586395399146%positive 52%nat (3166793197699573)%Z 1%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F2 V2].
  destruct (word_ok_intro (0x3c71f8ada953d5c9)%Z false 5058499357955529%positive 108%nat (5058499357955529)%Z 0%Z (-108)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F3 V3].
  destruct (word_ok_intro (0x3fef4a8c7327a780)%Z false 8807691365885824%positive 53%nat (68810088795983)%Z 7%Z (-46)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F4 V4].
  destruct (word_ok_intro (0x3ffd2ca959d5c719)%Z false 8211880192886553%positive 52%nat (8211880192886553)%Z 0%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F5 V5].
  destruct (word_ok_intro (0x400e839ddaa68b5c)%Z false 8588963302771548%positive 51%nat (2147240825692887)%Z 2%Z (-49)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F6 V6].
  destruct (word_ok_intro (0x402218f958784e87)%Z false 5094008790994567%positive 49%nat (5094008790994567)%Z 0%Z (-49)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F7 V7].
  destruct (word_ok_intro (0x4036e60e1fe8cdc2)%Z false 6445397826915778%positive 48%nat (3222698913457889)%Z 1%Z (-47)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F8 V8].
  destruct (word_ok_intro (0x404e58a8ea97dcd9)%Z false 8541731814890713%positive 47%nat (8541731814890713)%Z 0%Z (-47)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F9 V9].
  destruct (word_ok_intro (0x4064c81dbab58ca6)%Z false 5849529546280102%positive 45%nat (2924764773140051)%Z 1%Z (-44)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F10 V10].
  destruct (word_ok_intro (0x407d39666e70aa72)%Z false 8225886426933874%positive 44%nat (4112943213466937)%Z 1%Z (-43)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F11 V11].
  destruct (word_ok_intro (0x40965887e9d827bc)%Z false 6289790254720956%positive 42%nat (1572447563680239)%Z 2%Z (-40)%Z eq_refl eq_refl ltac:(lia) eq_refl) as [F12 V12].
  refine (segok_from_values _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    F0 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12
    _ _ _ _ _ _ _ _ _ _ _ _ _ evalcert_45 _ _).
  all: seg_numeric.
Qed.

Lemma segok_all (k : Z) : (1 <= k <= 45)%Z ->
  exists bound, SegOkRow (nth (Z.to_nat (k - 1)) asin_segments []) bound /\ bound <= bpow radix2 (-63).
Proof.
  intros Hk.
  assert (Hc : k = 1%Z \/ k = 2%Z \/ k = 3%Z \/ k = 4%Z \/ k = 5%Z \/ k = 6%Z \/ k = 7%Z \/ k = 8%Z \/ k = 9%Z \/ k = 10%Z \/ k = 11%Z \/ k = 12%Z \/ k = 13%Z \/ k = 14%Z \/ k = 15%Z \/ k = 16%Z \/ k = 17%Z \/ k = 18%Z \/ k = 19%Z \/ k = 20%Z \/ k = 21%Z \/ k = 22%Z \/ k = 23%Z \/ k = 24%Z \/ k = 25%Z \/ k = 26%Z \/ k = 27%Z \/ k = 28%Z \/ k = 29%Z \/ k = 30%Z \/ k = 31%Z \/ k = 32%Z \/ k = 33%Z \/ k = 34%Z \/ k = 35%Z \/ k = 36%Z \/ k = 37%Z \/ k = 38%Z \/ k = 39%Z \/ k = 40%Z \/ k = 41%Z \/ k = 42%Z \/ k = 43%Z \/ k = 44%Z \/ k = 45%Z) by lia.
  repeat (destruct Hc as [E | Hc]; [subst k; first [(exists (IZR 604 * bpow radix2 (-80)); split; [exact segok_01 | bpow_num; interval with (i_prec 60)]) | (exists (IZR 562 * bpow radix2 (-79)); split; [exact segok_02 | bpow_num; interval with (i_prec 60)]) | (exists (IZR 822 * bpow radix2 (-79)); split; [exact segok_03 | bpow_num; interval with (i_prec 60)]) | (exists (IZR 543 * bpow radix2 (-78)); split; [exact segok_04 | bpow_num; interval with (i_prec 60)]) | (exists (IZR 675 * bpow radix2 (-78)); split; [exact segok_05 | bpow_num; interval with (i_prec 60)]) | (exists (IZR 809 * bpow radix2 (-78)); split; [exact segok_06 | bpow_num; interval with (i_prec 60)]) | (exists (IZR 945 * bpow radix2 (-78)); split; [exact segok_07 | bpow_num; interval with (i_prec 60)]) | (exists (IZR 542 * bpow radix2 (-77)); split; [exact segok_08 | bpow_num; interval with (i_prec 60)]) | (exists (IZR 612 * bpow radix2 (-77)); split; [exact segok_09 | bpow_num; interval with (i_prec 60)]) | (exists (IZR 683 * bpow radix2 (-77)); split; [exact segok_10 | bpow_num; interval with (i_prec 60)]) | (exists (IZR 757 * bpow radix2 (-77)); split; [exact segok_11 | bpow_num; interval with (i_prec 60)]) | (exists (IZR 832 * bpow radix2 (-77)); split; [exact segok_12 | bpow_num; interval with (i_prec 60)]) | (exists (IZR 909 * bpow radix2 (-77)); split; [exact segok_13 | bpow_num; interval with (i_prec 60)]) | (exists (IZR 988 * bpow radix2 (-77)); split; [exact segok_14 | bpow_num; interval with (i_prec 60)]) | (exists (IZR 535 * bpow radix2 (-76)); split; [exact segok_15 | bpow_num; interval with (i_prec 60)]) | (exists (IZR 577 * bpow radix2 (-76)); split; [exact segok_16 | bpow_num; interval with (i_prec 60)]) | (exists (IZR 621 * bpow radix2 (-76)); split; [exact segok_17 | bpow_num; interval with (i_prec 60)]) | (exists (IZR 667 * bpow radix2 (-76)); split; [exact segok_18 | bpow_num; interval with (i_prec 60)]) | (exists (IZR 714 * bpow radix2 (-76)); split; [exact segok_19 | bpow_num; interval with (i_prec 60)]) | (exists (IZR 763 * bpow radix2 (-76)); split; [exact segok_20 | bpow_num; interval with (i_prec 60)]) | (exists (IZR 814 * bpow radix2 (-76)); split; [exact segok_21 | bpow_num; interval with (i_prec 60)]) | (exists (IZR 868 * bpow radix2 (-76)); split; [exact segok_22 | bpow_num; interval with (i_prec 60)]) | (exists (IZR 925 * bpow radix2 (-76)); split; [exact segok_23 | bpow_num; interval with (i_prec 60)]) | (exists (IZR 984 * bpow radix2 (-76)); split; [exact segok_24 | bpow_num; interval with (i_prec 60)]) | (exists (IZR 524 * bpow radix2 (-75)); split; [exact segok_25 | bpow_num; interval with (i_prec 60)]) | (exists (IZR 557 * bpow radix2 (-75)); split; [exact segok_26 | bpow_num; interval with (i_prec 60)]) | (exists (IZR 592 * bpow radix2 (-75)); split; [exact segok_27 | bpow_num; interval with (i_prec 60)]) | (exists (IZR 629 * bpow radix2 (-75)); split; [exact segok_28 | bpow_num; interval with (i_prec 60)]) | (exists (IZR 669 * bpow radix2 (-75)); split; [exact segok_29 | bpow_num; interval with (i_prec 60)]) | (exists (IZR 711 * bpow radix2 (-75)); split; [exact segok_30 | bpow_num; interval with (i_prec 60)]) | (exists (IZR 756 * bpow radix2 (-75)); split; [exact segok_31 | bpow_num; interval with (i_prec 60)]) | (exists (IZR 805 * bpow radix2 (-75)); split; [exact segok_32 | bpow_num; interval with (i_prec 60)]) | (exists (IZR 857 * bpow radix2 (-75)); split; [exact segok_33 | bpow_num; interval with (i_prec 60)]) | (exists (IZR 914 * bpow radix2 (-75)); split; [exact segok_34 | bpow_num; interval with (i_prec 60)]) | (exists (IZR 975 * bpow radix2 (-75)); split; [exact segok_35 | bpow_num; interval with (i_prec 60)]) | (exists (IZR 521 * bpow radix2 (-74)); split; [exact segok_36 | bpow_num; interval with (i_prec 60)]) | (exists (IZR 557 * bpow radix2 (-74)); split; [exact segok_37 | bpow_num; interval with (i_prec 60)]) | (exists (IZR 597 * bpow radix2 (-74)); split; [exact segok_38 | bpow_num; interval with (i_prec 60)]) | (exists (IZR 640 * bpow radix2 (-74)); split; [exact segok_39 | bpow_num; interval with (i_prec 60)]) | (exists (IZR 688 * bpow radix2 (-74)); split; [exact segok_40 | bpow_num; interval with (i_prec 60)]) | (exists (IZR 742 * bpow radix2 (-74)); split; [exact segok_41 | bpow_num; interval with (i_prec 60)]) | (exists (IZR 801 * bpow radix2 (-74)); split; [exact segok_42 | bpow_num; interval with (i_prec 60)]) | (exists (IZR 867 * bpow radix2 (-74)); split; [exact segok_43 | bpow_num; interval with (i_prec 60)]) | (exists (IZR 942 * bpow radix2 (-74)); split; [exact segok_44 | bpow_num; interval with (i_prec 60)]) | (exists (IZR 514 * bpow radix2 (-73)); split; [exact segok_45 | bpow_num; interval with (i_prec 60)])] | ]).
  subst k. exists (IZR 514 * bpow radix2 (-73)); split; [exact segok_45 | bpow_num; interval with (i_prec 60)].
Qed.
