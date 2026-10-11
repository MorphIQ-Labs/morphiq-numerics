(** Constants of [ln]'s reduction, written by generators/ln_constants.py; do
    not edit. Each is given by its binary64 encoding, as in
    crates/morphiq-numerics/src/ln/tables.rs, with what the proofs take about
    it (docs/ln.md, section 3). *)

From Coq Require Import Reals ZArith List Lia Lra.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import IEEE64 Grid Encodings.
Import ListNotations.

Open Scope R_scope.

(** Table interval [i]: the significand [m] in [[1 + i/128, 1 + (i+1)/128)],
    and [y = m] for [i < 53], [y = m/2] otherwise. *)
Definition ln_lo (i : nat) : R := if (i <? 53)%nat then 1 + INR i / 128 else (1 + INR i / 128) / 2.
Definition ln_hi (i : nat) : R := if (i <? 53)%nat then 1 + INR (S i) / 128 else (1 + INR (S i) / 128) / 2.

(** [R[i]], the reduction's reciprocals, by their encodings. *)
Definition ln_r_bits : list Z := [
  4607182418800017408%Z;
  4607076865683750912%Z;
  4607006496939573248%Z;
  4606944924288417792%Z;
  4606874555544240128%Z;
  4606812982893084672%Z;
  4606751410241929216%Z;
  4606681041497751552%Z;
  4606619468846596096%Z;
  4606557896195440640%Z;
  4606496323544285184%Z;
  4606443546986151936%Z;
  4606381974334996480%Z;
  4606320401683841024%Z;
  4606267625125707776%Z;
  4606206052474552320%Z;
  4606153275916419072%Z;
  4606100499358285824%Z;
  4606047722800152576%Z;
  4605994946242019328%Z;
  4605942169683886080%Z;
  4605889393125752832%Z;
  4605836616567619584%Z;
  4605783840009486336%Z;
  4605731063451353088%Z;
  4605687082986242048%Z;
  4605634306428108800%Z;
  4605590325962997760%Z;
  4605546345497886720%Z;
  4605493568939753472%Z;
  4605449588474642432%Z;
  4605405608009531392%Z;
  4605361627544420352%Z;
  4605317647079309312%Z;
  4605273666614198272%Z;
  4605229686149087232%Z;
  4605185705683976192%Z;
  4605141725218865152%Z;
  4605097744753754112%Z;
  4605062560381665280%Z;
  4605018579916554240%Z;
  4604974599451443200%Z;
  4604939415079354368%Z;
  4604895434614243328%Z;
  4604860250242154496%Z;
  4604816269777043456%Z;
  4604781085404954624%Z;
  4604745901032865792%Z;
  4604710716660776960%Z;
  4604666736195665920%Z;
  4604631551823577088%Z;
  4604596367451488256%Z;
  4604561183079399424%Z;
  4609029598334681088%Z;
  4608994413962592256%Z;
  4608959229590503424%Z;
  4608924045218414592%Z;
  4608897656939347968%Z;
  4608862472567259136%Z;
  4608827288195170304%Z;
  4608792103823081472%Z;
  4608765715544014848%Z;
  4608730531171926016%Z;
  4608695346799837184%Z;
  4608668958520770560%Z;
  4608633774148681728%Z;
  4608607385869615104%Z;
  4608572201497526272%Z;
  4608545813218459648%Z;
  4608519424939393024%Z;
  4608484240567304192%Z;
  4608457852288237568%Z;
  4608431464009170944%Z;
  4608396279637082112%Z;
  4608369891358015488%Z;
  4608343503078948864%Z;
  4608317114799882240%Z;
  4608290726520815616%Z;
  4608264338241748992%Z;
  4608237949962682368%Z;
  4608211561683615744%Z;
  4608185173404549120%Z;
  4608158785125482496%Z;
  4608132396846415872%Z;
  4608106008567349248%Z;
  4608079620288282624%Z;
  4608053232009216000%Z;
  4608026843730149376%Z;
  4608000455451082752%Z;
  4607982863265038336%Z;
  4607956474985971712%Z;
  4607930086706905088%Z;
  4607903698427838464%Z;
  4607886106241794048%Z;
  4607859717962727424%Z;
  4607833329683660800%Z;
  4607815737497616384%Z;
  4607789349218549760%Z;
  4607771757032505344%Z;
  4607745368753438720%Z;
  4607727776567394304%Z;
  4607701388288327680%Z;
  4607683796102283264%Z;
  4607657407823216640%Z;
  4607639815637172224%Z;
  4607613427358105600%Z;
  4607595835172061184%Z;
  4607578242986016768%Z;
  4607551854706950144%Z;
  4607534262520905728%Z;
  4607516670334861312%Z;
  4607490282055794688%Z;
  4607472689869750272%Z;
  4607455097683705856%Z;
  4607437505497661440%Z;
  4607411117218594816%Z;
  4607393525032550400%Z;
  4607375932846505984%Z;
  4607358340660461568%Z;
  4607340748474417152%Z;
  4607314360195350528%Z;
  4607296768009306112%Z;
  4607279175823261696%Z;
  4607261583637217280%Z;
  4607243991451172864%Z;
  4607226399265128448%Z;
  4607208807079084032%Z;
  4607182418800017408%Z
].
Definition ln_r (i : nat) : f64 := b64_of_bits (nth i ln_r_bits 0%Z).

(** Each [R[i]] is a binary64 number on [2^-10]'s grid between [1/2] and [2],
    and [|y·R[i] - 1| <= 2^-7] over its interval: [y·R[i]] is increasing in
    [y], so the endpoints decide it. *)
Definition ln_r_ok (i : nat) : Prop :=
  finite (ln_r i) /\ on_grid (-10) (B (ln_r i)) /\ / 2 <= B (ln_r i) <= 2 /\
  1 - / 128 <= ln_lo i * B (ln_r i) /\ ln_hi i * B (ln_r i) <= 1 + / 128.

Lemma ln_r_ok_0 : ln_r_ok 0.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 0) with (b64_of_bits 4607182418800017408).
  split; [exact (bits_finite 4607182418800017408 _ _ _ eq_refl) | ].
  rewrite (bits_val 4607182418800017408 false 4503599627370496 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 0) with 0 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 0)) with 1 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1024%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_1 : ln_r_ok 1.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 1) with (b64_of_bits 4607076865683750912).
  split; [exact (bits_finite 4607076865683750912 _ _ _ eq_refl) | ].
  rewrite (bits_val 4607076865683750912 false 8901646138474496 53 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 53) with 9007199254740992 by ring.
  replace (INR 1) with 1 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 1)) with 2 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1012%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_2 : ln_r_ok 2.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 2) with (b64_of_bits 4607006496939573248).
  split; [exact (bits_finite 4607006496939573248 _ _ _ eq_refl) | ].
  rewrite (bits_val 4607006496939573248 false 8831277394296832 53 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 53) with 9007199254740992 by ring.
  replace (INR 2) with 2 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 2)) with 3 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1004%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_3 : ln_r_ok 3.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 3) with (b64_of_bits 4606944924288417792).
  split; [exact (bits_finite 4606944924288417792 _ _ _ eq_refl) | ].
  rewrite (bits_val 4606944924288417792 false 8769704743141376 53 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 53) with 9007199254740992 by ring.
  replace (INR 3) with 3 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 3)) with 4 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 997%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_4 : ln_r_ok 4.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 4) with (b64_of_bits 4606874555544240128).
  split; [exact (bits_finite 4606874555544240128 _ _ _ eq_refl) | ].
  rewrite (bits_val 4606874555544240128 false 8699335998963712 53 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 53) with 9007199254740992 by ring.
  replace (INR 4) with 4 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 4)) with 5 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 989%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_5 : ln_r_ok 5.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 5) with (b64_of_bits 4606812982893084672).
  split; [exact (bits_finite 4606812982893084672 _ _ _ eq_refl) | ].
  rewrite (bits_val 4606812982893084672 false 8637763347808256 53 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 53) with 9007199254740992 by ring.
  replace (INR 5) with 5 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 5)) with 6 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 982%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_6 : ln_r_ok 6.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 6) with (b64_of_bits 4606751410241929216).
  split; [exact (bits_finite 4606751410241929216 _ _ _ eq_refl) | ].
  rewrite (bits_val 4606751410241929216 false 8576190696652800 53 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 53) with 9007199254740992 by ring.
  replace (INR 6) with 6 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 6)) with 7 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 975%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_7 : ln_r_ok 7.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 7) with (b64_of_bits 4606681041497751552).
  split; [exact (bits_finite 4606681041497751552 _ _ _ eq_refl) | ].
  rewrite (bits_val 4606681041497751552 false 8505821952475136 53 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 53) with 9007199254740992 by ring.
  replace (INR 7) with 7 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 7)) with 8 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 967%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_8 : ln_r_ok 8.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 8) with (b64_of_bits 4606619468846596096).
  split; [exact (bits_finite 4606619468846596096 _ _ _ eq_refl) | ].
  rewrite (bits_val 4606619468846596096 false 8444249301319680 53 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 53) with 9007199254740992 by ring.
  replace (INR 8) with 8 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 8)) with 9 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 960%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_9 : ln_r_ok 9.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 9) with (b64_of_bits 4606557896195440640).
  split; [exact (bits_finite 4606557896195440640 _ _ _ eq_refl) | ].
  rewrite (bits_val 4606557896195440640 false 8382676650164224 53 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 53) with 9007199254740992 by ring.
  replace (INR 9) with 9 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 9)) with 10 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 953%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_10 : ln_r_ok 10.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 10) with (b64_of_bits 4606496323544285184).
  split; [exact (bits_finite 4606496323544285184 _ _ _ eq_refl) | ].
  rewrite (bits_val 4606496323544285184 false 8321103999008768 53 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 53) with 9007199254740992 by ring.
  replace (INR 10) with 10 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 10)) with 11 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 946%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_11 : ln_r_ok 11.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 11) with (b64_of_bits 4606443546986151936).
  split; [exact (bits_finite 4606443546986151936 _ _ _ eq_refl) | ].
  rewrite (bits_val 4606443546986151936 false 8268327440875520 53 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 53) with 9007199254740992 by ring.
  replace (INR 11) with 11 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 11)) with 12 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 940%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_12 : ln_r_ok 12.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 12) with (b64_of_bits 4606381974334996480).
  split; [exact (bits_finite 4606381974334996480 _ _ _ eq_refl) | ].
  rewrite (bits_val 4606381974334996480 false 8206754789720064 53 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 53) with 9007199254740992 by ring.
  replace (INR 12) with 12 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 12)) with 13 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 933%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_13 : ln_r_ok 13.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 13) with (b64_of_bits 4606320401683841024).
  split; [exact (bits_finite 4606320401683841024 _ _ _ eq_refl) | ].
  rewrite (bits_val 4606320401683841024 false 8145182138564608 53 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 53) with 9007199254740992 by ring.
  replace (INR 13) with 13 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 13)) with 14 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 926%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_14 : ln_r_ok 14.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 14) with (b64_of_bits 4606267625125707776).
  split; [exact (bits_finite 4606267625125707776 _ _ _ eq_refl) | ].
  rewrite (bits_val 4606267625125707776 false 8092405580431360 53 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 53) with 9007199254740992 by ring.
  replace (INR 14) with 14 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 14)) with 15 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 920%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_15 : ln_r_ok 15.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 15) with (b64_of_bits 4606206052474552320).
  split; [exact (bits_finite 4606206052474552320 _ _ _ eq_refl) | ].
  rewrite (bits_val 4606206052474552320 false 8030832929275904 53 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 53) with 9007199254740992 by ring.
  replace (INR 15) with 15 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 15)) with 16 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 913%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_16 : ln_r_ok 16.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 16) with (b64_of_bits 4606153275916419072).
  split; [exact (bits_finite 4606153275916419072 _ _ _ eq_refl) | ].
  rewrite (bits_val 4606153275916419072 false 7978056371142656 53 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 53) with 9007199254740992 by ring.
  replace (INR 16) with 16 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 16)) with 17 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 907%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_17 : ln_r_ok 17.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 17) with (b64_of_bits 4606100499358285824).
  split; [exact (bits_finite 4606100499358285824 _ _ _ eq_refl) | ].
  rewrite (bits_val 4606100499358285824 false 7925279813009408 53 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 53) with 9007199254740992 by ring.
  replace (INR 17) with 17 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 17)) with 18 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 901%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_18 : ln_r_ok 18.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 18) with (b64_of_bits 4606047722800152576).
  split; [exact (bits_finite 4606047722800152576 _ _ _ eq_refl) | ].
  rewrite (bits_val 4606047722800152576 false 7872503254876160 53 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 53) with 9007199254740992 by ring.
  replace (INR 18) with 18 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 18)) with 19 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 895%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_19 : ln_r_ok 19.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 19) with (b64_of_bits 4605994946242019328).
  split; [exact (bits_finite 4605994946242019328 _ _ _ eq_refl) | ].
  rewrite (bits_val 4605994946242019328 false 7819726696742912 53 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 53) with 9007199254740992 by ring.
  replace (INR 19) with 19 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 19)) with 20 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 889%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_20 : ln_r_ok 20.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 20) with (b64_of_bits 4605942169683886080).
  split; [exact (bits_finite 4605942169683886080 _ _ _ eq_refl) | ].
  rewrite (bits_val 4605942169683886080 false 7766950138609664 53 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 53) with 9007199254740992 by ring.
  replace (INR 20) with 20 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 20)) with 21 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 883%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_21 : ln_r_ok 21.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 21) with (b64_of_bits 4605889393125752832).
  split; [exact (bits_finite 4605889393125752832 _ _ _ eq_refl) | ].
  rewrite (bits_val 4605889393125752832 false 7714173580476416 53 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 53) with 9007199254740992 by ring.
  replace (INR 21) with 21 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 21)) with 22 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 877%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_22 : ln_r_ok 22.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 22) with (b64_of_bits 4605836616567619584).
  split; [exact (bits_finite 4605836616567619584 _ _ _ eq_refl) | ].
  rewrite (bits_val 4605836616567619584 false 7661397022343168 53 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 53) with 9007199254740992 by ring.
  replace (INR 22) with 22 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 22)) with 23 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 871%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_23 : ln_r_ok 23.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 23) with (b64_of_bits 4605783840009486336).
  split; [exact (bits_finite 4605783840009486336 _ _ _ eq_refl) | ].
  rewrite (bits_val 4605783840009486336 false 7608620464209920 53 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 53) with 9007199254740992 by ring.
  replace (INR 23) with 23 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 23)) with 24 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 865%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_24 : ln_r_ok 24.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 24) with (b64_of_bits 4605731063451353088).
  split; [exact (bits_finite 4605731063451353088 _ _ _ eq_refl) | ].
  rewrite (bits_val 4605731063451353088 false 7555843906076672 53 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 53) with 9007199254740992 by ring.
  replace (INR 24) with 24 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 24)) with 25 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 859%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_25 : ln_r_ok 25.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 25) with (b64_of_bits 4605687082986242048).
  split; [exact (bits_finite 4605687082986242048 _ _ _ eq_refl) | ].
  rewrite (bits_val 4605687082986242048 false 7511863440965632 53 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 53) with 9007199254740992 by ring.
  replace (INR 25) with 25 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 25)) with 26 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 854%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_26 : ln_r_ok 26.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 26) with (b64_of_bits 4605634306428108800).
  split; [exact (bits_finite 4605634306428108800 _ _ _ eq_refl) | ].
  rewrite (bits_val 4605634306428108800 false 7459086882832384 53 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 53) with 9007199254740992 by ring.
  replace (INR 26) with 26 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 26)) with 27 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 848%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_27 : ln_r_ok 27.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 27) with (b64_of_bits 4605590325962997760).
  split; [exact (bits_finite 4605590325962997760 _ _ _ eq_refl) | ].
  rewrite (bits_val 4605590325962997760 false 7415106417721344 53 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 53) with 9007199254740992 by ring.
  replace (INR 27) with 27 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 27)) with 28 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 843%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_28 : ln_r_ok 28.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 28) with (b64_of_bits 4605546345497886720).
  split; [exact (bits_finite 4605546345497886720 _ _ _ eq_refl) | ].
  rewrite (bits_val 4605546345497886720 false 7371125952610304 53 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 53) with 9007199254740992 by ring.
  replace (INR 28) with 28 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 28)) with 29 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 838%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_29 : ln_r_ok 29.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 29) with (b64_of_bits 4605493568939753472).
  split; [exact (bits_finite 4605493568939753472 _ _ _ eq_refl) | ].
  rewrite (bits_val 4605493568939753472 false 7318349394477056 53 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 53) with 9007199254740992 by ring.
  replace (INR 29) with 29 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 29)) with 30 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 832%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_30 : ln_r_ok 30.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 30) with (b64_of_bits 4605449588474642432).
  split; [exact (bits_finite 4605449588474642432 _ _ _ eq_refl) | ].
  rewrite (bits_val 4605449588474642432 false 7274368929366016 53 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 53) with 9007199254740992 by ring.
  replace (INR 30) with 30 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 30)) with 31 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 827%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_31 : ln_r_ok 31.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 31) with (b64_of_bits 4605405608009531392).
  split; [exact (bits_finite 4605405608009531392 _ _ _ eq_refl) | ].
  rewrite (bits_val 4605405608009531392 false 7230388464254976 53 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 53) with 9007199254740992 by ring.
  replace (INR 31) with 31 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 31)) with 32 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 822%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_32 : ln_r_ok 32.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 32) with (b64_of_bits 4605361627544420352).
  split; [exact (bits_finite 4605361627544420352 _ _ _ eq_refl) | ].
  rewrite (bits_val 4605361627544420352 false 7186407999143936 53 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 53) with 9007199254740992 by ring.
  replace (INR 32) with 32 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 32)) with 33 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 817%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_33 : ln_r_ok 33.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 33) with (b64_of_bits 4605317647079309312).
  split; [exact (bits_finite 4605317647079309312 _ _ _ eq_refl) | ].
  rewrite (bits_val 4605317647079309312 false 7142427534032896 53 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 53) with 9007199254740992 by ring.
  replace (INR 33) with 33 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 33)) with 34 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 812%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_34 : ln_r_ok 34.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 34) with (b64_of_bits 4605273666614198272).
  split; [exact (bits_finite 4605273666614198272 _ _ _ eq_refl) | ].
  rewrite (bits_val 4605273666614198272 false 7098447068921856 53 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 53) with 9007199254740992 by ring.
  replace (INR 34) with 34 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 34)) with 35 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 807%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_35 : ln_r_ok 35.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 35) with (b64_of_bits 4605229686149087232).
  split; [exact (bits_finite 4605229686149087232 _ _ _ eq_refl) | ].
  rewrite (bits_val 4605229686149087232 false 7054466603810816 53 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 53) with 9007199254740992 by ring.
  replace (INR 35) with 35 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 35)) with 36 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 802%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_36 : ln_r_ok 36.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 36) with (b64_of_bits 4605185705683976192).
  split; [exact (bits_finite 4605185705683976192 _ _ _ eq_refl) | ].
  rewrite (bits_val 4605185705683976192 false 7010486138699776 53 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 53) with 9007199254740992 by ring.
  replace (INR 36) with 36 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 36)) with 37 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 797%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_37 : ln_r_ok 37.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 37) with (b64_of_bits 4605141725218865152).
  split; [exact (bits_finite 4605141725218865152 _ _ _ eq_refl) | ].
  rewrite (bits_val 4605141725218865152 false 6966505673588736 53 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 53) with 9007199254740992 by ring.
  replace (INR 37) with 37 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 37)) with 38 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 792%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_38 : ln_r_ok 38.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 38) with (b64_of_bits 4605097744753754112).
  split; [exact (bits_finite 4605097744753754112 _ _ _ eq_refl) | ].
  rewrite (bits_val 4605097744753754112 false 6922525208477696 53 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 53) with 9007199254740992 by ring.
  replace (INR 38) with 38 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 38)) with 39 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 787%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_39 : ln_r_ok 39.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 39) with (b64_of_bits 4605062560381665280).
  split; [exact (bits_finite 4605062560381665280 _ _ _ eq_refl) | ].
  rewrite (bits_val 4605062560381665280 false 6887340836388864 53 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 53) with 9007199254740992 by ring.
  replace (INR 39) with 39 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 39)) with 40 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 783%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_40 : ln_r_ok 40.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 40) with (b64_of_bits 4605018579916554240).
  split; [exact (bits_finite 4605018579916554240 _ _ _ eq_refl) | ].
  rewrite (bits_val 4605018579916554240 false 6843360371277824 53 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 53) with 9007199254740992 by ring.
  replace (INR 40) with 40 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 40)) with 41 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 778%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_41 : ln_r_ok 41.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 41) with (b64_of_bits 4604974599451443200).
  split; [exact (bits_finite 4604974599451443200 _ _ _ eq_refl) | ].
  rewrite (bits_val 4604974599451443200 false 6799379906166784 53 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 53) with 9007199254740992 by ring.
  replace (INR 41) with 41 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 41)) with 42 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 773%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_42 : ln_r_ok 42.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 42) with (b64_of_bits 4604939415079354368).
  split; [exact (bits_finite 4604939415079354368 _ _ _ eq_refl) | ].
  rewrite (bits_val 4604939415079354368 false 6764195534077952 53 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 53) with 9007199254740992 by ring.
  replace (INR 42) with 42 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 42)) with 43 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 769%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_43 : ln_r_ok 43.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 43) with (b64_of_bits 4604895434614243328).
  split; [exact (bits_finite 4604895434614243328 _ _ _ eq_refl) | ].
  rewrite (bits_val 4604895434614243328 false 6720215068966912 53 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 53) with 9007199254740992 by ring.
  replace (INR 43) with 43 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 43)) with 44 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 764%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_44 : ln_r_ok 44.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 44) with (b64_of_bits 4604860250242154496).
  split; [exact (bits_finite 4604860250242154496 _ _ _ eq_refl) | ].
  rewrite (bits_val 4604860250242154496 false 6685030696878080 53 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 53) with 9007199254740992 by ring.
  replace (INR 44) with 44 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 44)) with 45 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 760%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_45 : ln_r_ok 45.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 45) with (b64_of_bits 4604816269777043456).
  split; [exact (bits_finite 4604816269777043456 _ _ _ eq_refl) | ].
  rewrite (bits_val 4604816269777043456 false 6641050231767040 53 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 53) with 9007199254740992 by ring.
  replace (INR 45) with 45 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 45)) with 46 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 755%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_46 : ln_r_ok 46.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 46) with (b64_of_bits 4604781085404954624).
  split; [exact (bits_finite 4604781085404954624 _ _ _ eq_refl) | ].
  rewrite (bits_val 4604781085404954624 false 6605865859678208 53 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 53) with 9007199254740992 by ring.
  replace (INR 46) with 46 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 46)) with 47 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 751%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_47 : ln_r_ok 47.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 47) with (b64_of_bits 4604745901032865792).
  split; [exact (bits_finite 4604745901032865792 _ _ _ eq_refl) | ].
  rewrite (bits_val 4604745901032865792 false 6570681487589376 53 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 53) with 9007199254740992 by ring.
  replace (INR 47) with 47 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 47)) with 48 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 747%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_48 : ln_r_ok 48.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 48) with (b64_of_bits 4604710716660776960).
  split; [exact (bits_finite 4604710716660776960 _ _ _ eq_refl) | ].
  rewrite (bits_val 4604710716660776960 false 6535497115500544 53 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 53) with 9007199254740992 by ring.
  replace (INR 48) with 48 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 48)) with 49 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 743%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_49 : ln_r_ok 49.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 49) with (b64_of_bits 4604666736195665920).
  split; [exact (bits_finite 4604666736195665920 _ _ _ eq_refl) | ].
  rewrite (bits_val 4604666736195665920 false 6491516650389504 53 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 53) with 9007199254740992 by ring.
  replace (INR 49) with 49 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 49)) with 50 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 738%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_50 : ln_r_ok 50.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 50) with (b64_of_bits 4604631551823577088).
  split; [exact (bits_finite 4604631551823577088 _ _ _ eq_refl) | ].
  rewrite (bits_val 4604631551823577088 false 6456332278300672 53 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 53) with 9007199254740992 by ring.
  replace (INR 50) with 50 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 50)) with 51 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 734%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_51 : ln_r_ok 51.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 51) with (b64_of_bits 4604596367451488256).
  split; [exact (bits_finite 4604596367451488256 _ _ _ eq_refl) | ].
  rewrite (bits_val 4604596367451488256 false 6421147906211840 53 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 53) with 9007199254740992 by ring.
  replace (INR 51) with 51 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 51)) with 52 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 730%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_52 : ln_r_ok 52.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 52) with (b64_of_bits 4604561183079399424).
  split; [exact (bits_finite 4604561183079399424 _ _ _ eq_refl) | ].
  rewrite (bits_val 4604561183079399424 false 6385963534123008 53 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 53) with 9007199254740992 by ring.
  replace (INR 52) with 52 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 52)) with 53 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 726%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_53 : ln_r_ok 53.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 53) with (b64_of_bits 4609029598334681088).
  split; [exact (bits_finite 4609029598334681088 _ _ _ eq_refl) | ].
  rewrite (bits_val 4609029598334681088 false 6350779162034176 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 53) with 53 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 53)) with 54 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1444%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_54 : ln_r_ok 54.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 54) with (b64_of_bits 4608994413962592256).
  split; [exact (bits_finite 4608994413962592256 _ _ _ eq_refl) | ].
  rewrite (bits_val 4608994413962592256 false 6315594789945344 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 54) with 54 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 54)) with 55 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1436%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_55 : ln_r_ok 55.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 55) with (b64_of_bits 4608959229590503424).
  split; [exact (bits_finite 4608959229590503424 _ _ _ eq_refl) | ].
  rewrite (bits_val 4608959229590503424 false 6280410417856512 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 55) with 55 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 55)) with 56 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1428%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_56 : ln_r_ok 56.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 56) with (b64_of_bits 4608924045218414592).
  split; [exact (bits_finite 4608924045218414592 _ _ _ eq_refl) | ].
  rewrite (bits_val 4608924045218414592 false 6245226045767680 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 56) with 56 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 56)) with 57 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1420%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_57 : ln_r_ok 57.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 57) with (b64_of_bits 4608897656939347968).
  split; [exact (bits_finite 4608897656939347968 _ _ _ eq_refl) | ].
  rewrite (bits_val 4608897656939347968 false 6218837766701056 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 57) with 57 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 57)) with 58 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1414%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_58 : ln_r_ok 58.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 58) with (b64_of_bits 4608862472567259136).
  split; [exact (bits_finite 4608862472567259136 _ _ _ eq_refl) | ].
  rewrite (bits_val 4608862472567259136 false 6183653394612224 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 58) with 58 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 58)) with 59 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1406%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_59 : ln_r_ok 59.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 59) with (b64_of_bits 4608827288195170304).
  split; [exact (bits_finite 4608827288195170304 _ _ _ eq_refl) | ].
  rewrite (bits_val 4608827288195170304 false 6148469022523392 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 59) with 59 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 59)) with 60 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1398%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_60 : ln_r_ok 60.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 60) with (b64_of_bits 4608792103823081472).
  split; [exact (bits_finite 4608792103823081472 _ _ _ eq_refl) | ].
  rewrite (bits_val 4608792103823081472 false 6113284650434560 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 60) with 60 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 60)) with 61 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1390%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_61 : ln_r_ok 61.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 61) with (b64_of_bits 4608765715544014848).
  split; [exact (bits_finite 4608765715544014848 _ _ _ eq_refl) | ].
  rewrite (bits_val 4608765715544014848 false 6086896371367936 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 61) with 61 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 61)) with 62 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1384%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_62 : ln_r_ok 62.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 62) with (b64_of_bits 4608730531171926016).
  split; [exact (bits_finite 4608730531171926016 _ _ _ eq_refl) | ].
  rewrite (bits_val 4608730531171926016 false 6051711999279104 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 62) with 62 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 62)) with 63 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1376%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_63 : ln_r_ok 63.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 63) with (b64_of_bits 4608695346799837184).
  split; [exact (bits_finite 4608695346799837184 _ _ _ eq_refl) | ].
  rewrite (bits_val 4608695346799837184 false 6016527627190272 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 63) with 63 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 63)) with 64 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1368%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_64 : ln_r_ok 64.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 64) with (b64_of_bits 4608668958520770560).
  split; [exact (bits_finite 4608668958520770560 _ _ _ eq_refl) | ].
  rewrite (bits_val 4608668958520770560 false 5990139348123648 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 64) with 64 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 64)) with 65 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1362%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_65 : ln_r_ok 65.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 65) with (b64_of_bits 4608633774148681728).
  split; [exact (bits_finite 4608633774148681728 _ _ _ eq_refl) | ].
  rewrite (bits_val 4608633774148681728 false 5954954976034816 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 65) with 65 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 65)) with 66 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1354%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_66 : ln_r_ok 66.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 66) with (b64_of_bits 4608607385869615104).
  split; [exact (bits_finite 4608607385869615104 _ _ _ eq_refl) | ].
  rewrite (bits_val 4608607385869615104 false 5928566696968192 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 66) with 66 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 66)) with 67 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1348%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_67 : ln_r_ok 67.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 67) with (b64_of_bits 4608572201497526272).
  split; [exact (bits_finite 4608572201497526272 _ _ _ eq_refl) | ].
  rewrite (bits_val 4608572201497526272 false 5893382324879360 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 67) with 67 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 67)) with 68 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1340%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_68 : ln_r_ok 68.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 68) with (b64_of_bits 4608545813218459648).
  split; [exact (bits_finite 4608545813218459648 _ _ _ eq_refl) | ].
  rewrite (bits_val 4608545813218459648 false 5866994045812736 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 68) with 68 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 68)) with 69 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1334%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_69 : ln_r_ok 69.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 69) with (b64_of_bits 4608519424939393024).
  split; [exact (bits_finite 4608519424939393024 _ _ _ eq_refl) | ].
  rewrite (bits_val 4608519424939393024 false 5840605766746112 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 69) with 69 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 69)) with 70 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1328%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_70 : ln_r_ok 70.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 70) with (b64_of_bits 4608484240567304192).
  split; [exact (bits_finite 4608484240567304192 _ _ _ eq_refl) | ].
  rewrite (bits_val 4608484240567304192 false 5805421394657280 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 70) with 70 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 70)) with 71 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1320%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_71 : ln_r_ok 71.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 71) with (b64_of_bits 4608457852288237568).
  split; [exact (bits_finite 4608457852288237568 _ _ _ eq_refl) | ].
  rewrite (bits_val 4608457852288237568 false 5779033115590656 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 71) with 71 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 71)) with 72 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1314%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_72 : ln_r_ok 72.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 72) with (b64_of_bits 4608431464009170944).
  split; [exact (bits_finite 4608431464009170944 _ _ _ eq_refl) | ].
  rewrite (bits_val 4608431464009170944 false 5752644836524032 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 72) with 72 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 72)) with 73 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1308%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_73 : ln_r_ok 73.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 73) with (b64_of_bits 4608396279637082112).
  split; [exact (bits_finite 4608396279637082112 _ _ _ eq_refl) | ].
  rewrite (bits_val 4608396279637082112 false 5717460464435200 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 73) with 73 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 73)) with 74 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1300%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_74 : ln_r_ok 74.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 74) with (b64_of_bits 4608369891358015488).
  split; [exact (bits_finite 4608369891358015488 _ _ _ eq_refl) | ].
  rewrite (bits_val 4608369891358015488 false 5691072185368576 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 74) with 74 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 74)) with 75 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1294%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_75 : ln_r_ok 75.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 75) with (b64_of_bits 4608343503078948864).
  split; [exact (bits_finite 4608343503078948864 _ _ _ eq_refl) | ].
  rewrite (bits_val 4608343503078948864 false 5664683906301952 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 75) with 75 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 75)) with 76 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1288%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_76 : ln_r_ok 76.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 76) with (b64_of_bits 4608317114799882240).
  split; [exact (bits_finite 4608317114799882240 _ _ _ eq_refl) | ].
  rewrite (bits_val 4608317114799882240 false 5638295627235328 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 76) with 76 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 76)) with 77 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1282%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_77 : ln_r_ok 77.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 77) with (b64_of_bits 4608290726520815616).
  split; [exact (bits_finite 4608290726520815616 _ _ _ eq_refl) | ].
  rewrite (bits_val 4608290726520815616 false 5611907348168704 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 77) with 77 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 77)) with 78 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1276%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_78 : ln_r_ok 78.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 78) with (b64_of_bits 4608264338241748992).
  split; [exact (bits_finite 4608264338241748992 _ _ _ eq_refl) | ].
  rewrite (bits_val 4608264338241748992 false 5585519069102080 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 78) with 78 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 78)) with 79 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1270%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_79 : ln_r_ok 79.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 79) with (b64_of_bits 4608237949962682368).
  split; [exact (bits_finite 4608237949962682368 _ _ _ eq_refl) | ].
  rewrite (bits_val 4608237949962682368 false 5559130790035456 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 79) with 79 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 79)) with 80 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1264%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_80 : ln_r_ok 80.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 80) with (b64_of_bits 4608211561683615744).
  split; [exact (bits_finite 4608211561683615744 _ _ _ eq_refl) | ].
  rewrite (bits_val 4608211561683615744 false 5532742510968832 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 80) with 80 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 80)) with 81 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1258%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_81 : ln_r_ok 81.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 81) with (b64_of_bits 4608185173404549120).
  split; [exact (bits_finite 4608185173404549120 _ _ _ eq_refl) | ].
  rewrite (bits_val 4608185173404549120 false 5506354231902208 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 81) with 81 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 81)) with 82 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1252%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_82 : ln_r_ok 82.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 82) with (b64_of_bits 4608158785125482496).
  split; [exact (bits_finite 4608158785125482496 _ _ _ eq_refl) | ].
  rewrite (bits_val 4608158785125482496 false 5479965952835584 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 82) with 82 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 82)) with 83 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1246%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_83 : ln_r_ok 83.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 83) with (b64_of_bits 4608132396846415872).
  split; [exact (bits_finite 4608132396846415872 _ _ _ eq_refl) | ].
  rewrite (bits_val 4608132396846415872 false 5453577673768960 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 83) with 83 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 83)) with 84 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1240%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_84 : ln_r_ok 84.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 84) with (b64_of_bits 4608106008567349248).
  split; [exact (bits_finite 4608106008567349248 _ _ _ eq_refl) | ].
  rewrite (bits_val 4608106008567349248 false 5427189394702336 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 84) with 84 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 84)) with 85 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1234%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_85 : ln_r_ok 85.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 85) with (b64_of_bits 4608079620288282624).
  split; [exact (bits_finite 4608079620288282624 _ _ _ eq_refl) | ].
  rewrite (bits_val 4608079620288282624 false 5400801115635712 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 85) with 85 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 85)) with 86 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1228%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_86 : ln_r_ok 86.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 86) with (b64_of_bits 4608053232009216000).
  split; [exact (bits_finite 4608053232009216000 _ _ _ eq_refl) | ].
  rewrite (bits_val 4608053232009216000 false 5374412836569088 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 86) with 86 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 86)) with 87 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1222%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_87 : ln_r_ok 87.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 87) with (b64_of_bits 4608026843730149376).
  split; [exact (bits_finite 4608026843730149376 _ _ _ eq_refl) | ].
  rewrite (bits_val 4608026843730149376 false 5348024557502464 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 87) with 87 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 87)) with 88 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1216%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_88 : ln_r_ok 88.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 88) with (b64_of_bits 4608000455451082752).
  split; [exact (bits_finite 4608000455451082752 _ _ _ eq_refl) | ].
  rewrite (bits_val 4608000455451082752 false 5321636278435840 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 88) with 88 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 88)) with 89 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1210%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_89 : ln_r_ok 89.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 89) with (b64_of_bits 4607982863265038336).
  split; [exact (bits_finite 4607982863265038336 _ _ _ eq_refl) | ].
  rewrite (bits_val 4607982863265038336 false 5304044092391424 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 89) with 89 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 89)) with 90 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1206%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_90 : ln_r_ok 90.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 90) with (b64_of_bits 4607956474985971712).
  split; [exact (bits_finite 4607956474985971712 _ _ _ eq_refl) | ].
  rewrite (bits_val 4607956474985971712 false 5277655813324800 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 90) with 90 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 90)) with 91 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1200%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_91 : ln_r_ok 91.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 91) with (b64_of_bits 4607930086706905088).
  split; [exact (bits_finite 4607930086706905088 _ _ _ eq_refl) | ].
  rewrite (bits_val 4607930086706905088 false 5251267534258176 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 91) with 91 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 91)) with 92 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1194%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_92 : ln_r_ok 92.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 92) with (b64_of_bits 4607903698427838464).
  split; [exact (bits_finite 4607903698427838464 _ _ _ eq_refl) | ].
  rewrite (bits_val 4607903698427838464 false 5224879255191552 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 92) with 92 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 92)) with 93 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1188%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_93 : ln_r_ok 93.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 93) with (b64_of_bits 4607886106241794048).
  split; [exact (bits_finite 4607886106241794048 _ _ _ eq_refl) | ].
  rewrite (bits_val 4607886106241794048 false 5207287069147136 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 93) with 93 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 93)) with 94 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1184%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_94 : ln_r_ok 94.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 94) with (b64_of_bits 4607859717962727424).
  split; [exact (bits_finite 4607859717962727424 _ _ _ eq_refl) | ].
  rewrite (bits_val 4607859717962727424 false 5180898790080512 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 94) with 94 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 94)) with 95 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1178%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_95 : ln_r_ok 95.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 95) with (b64_of_bits 4607833329683660800).
  split; [exact (bits_finite 4607833329683660800 _ _ _ eq_refl) | ].
  rewrite (bits_val 4607833329683660800 false 5154510511013888 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 95) with 95 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 95)) with 96 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1172%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_96 : ln_r_ok 96.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 96) with (b64_of_bits 4607815737497616384).
  split; [exact (bits_finite 4607815737497616384 _ _ _ eq_refl) | ].
  rewrite (bits_val 4607815737497616384 false 5136918324969472 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 96) with 96 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 96)) with 97 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1168%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_97 : ln_r_ok 97.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 97) with (b64_of_bits 4607789349218549760).
  split; [exact (bits_finite 4607789349218549760 _ _ _ eq_refl) | ].
  rewrite (bits_val 4607789349218549760 false 5110530045902848 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 97) with 97 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 97)) with 98 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1162%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_98 : ln_r_ok 98.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 98) with (b64_of_bits 4607771757032505344).
  split; [exact (bits_finite 4607771757032505344 _ _ _ eq_refl) | ].
  rewrite (bits_val 4607771757032505344 false 5092937859858432 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 98) with 98 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 98)) with 99 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1158%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_99 : ln_r_ok 99.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 99) with (b64_of_bits 4607745368753438720).
  split; [exact (bits_finite 4607745368753438720 _ _ _ eq_refl) | ].
  rewrite (bits_val 4607745368753438720 false 5066549580791808 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 99) with 99 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 99)) with 100 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1152%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_100 : ln_r_ok 100.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 100) with (b64_of_bits 4607727776567394304).
  split; [exact (bits_finite 4607727776567394304 _ _ _ eq_refl) | ].
  rewrite (bits_val 4607727776567394304 false 5048957394747392 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 100) with 100 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 100)) with 101 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1148%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_101 : ln_r_ok 101.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 101) with (b64_of_bits 4607701388288327680).
  split; [exact (bits_finite 4607701388288327680 _ _ _ eq_refl) | ].
  rewrite (bits_val 4607701388288327680 false 5022569115680768 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 101) with 101 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 101)) with 102 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1142%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_102 : ln_r_ok 102.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 102) with (b64_of_bits 4607683796102283264).
  split; [exact (bits_finite 4607683796102283264 _ _ _ eq_refl) | ].
  rewrite (bits_val 4607683796102283264 false 5004976929636352 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 102) with 102 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 102)) with 103 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1138%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_103 : ln_r_ok 103.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 103) with (b64_of_bits 4607657407823216640).
  split; [exact (bits_finite 4607657407823216640 _ _ _ eq_refl) | ].
  rewrite (bits_val 4607657407823216640 false 4978588650569728 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 103) with 103 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 103)) with 104 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1132%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_104 : ln_r_ok 104.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 104) with (b64_of_bits 4607639815637172224).
  split; [exact (bits_finite 4607639815637172224 _ _ _ eq_refl) | ].
  rewrite (bits_val 4607639815637172224 false 4960996464525312 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 104) with 104 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 104)) with 105 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1128%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_105 : ln_r_ok 105.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 105) with (b64_of_bits 4607613427358105600).
  split; [exact (bits_finite 4607613427358105600 _ _ _ eq_refl) | ].
  rewrite (bits_val 4607613427358105600 false 4934608185458688 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 105) with 105 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 105)) with 106 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1122%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_106 : ln_r_ok 106.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 106) with (b64_of_bits 4607595835172061184).
  split; [exact (bits_finite 4607595835172061184 _ _ _ eq_refl) | ].
  rewrite (bits_val 4607595835172061184 false 4917015999414272 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 106) with 106 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 106)) with 107 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1118%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_107 : ln_r_ok 107.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 107) with (b64_of_bits 4607578242986016768).
  split; [exact (bits_finite 4607578242986016768 _ _ _ eq_refl) | ].
  rewrite (bits_val 4607578242986016768 false 4899423813369856 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 107) with 107 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 107)) with 108 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1114%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_108 : ln_r_ok 108.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 108) with (b64_of_bits 4607551854706950144).
  split; [exact (bits_finite 4607551854706950144 _ _ _ eq_refl) | ].
  rewrite (bits_val 4607551854706950144 false 4873035534303232 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 108) with 108 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 108)) with 109 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1108%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_109 : ln_r_ok 109.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 109) with (b64_of_bits 4607534262520905728).
  split; [exact (bits_finite 4607534262520905728 _ _ _ eq_refl) | ].
  rewrite (bits_val 4607534262520905728 false 4855443348258816 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 109) with 109 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 109)) with 110 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1104%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_110 : ln_r_ok 110.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 110) with (b64_of_bits 4607516670334861312).
  split; [exact (bits_finite 4607516670334861312 _ _ _ eq_refl) | ].
  rewrite (bits_val 4607516670334861312 false 4837851162214400 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 110) with 110 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 110)) with 111 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1100%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_111 : ln_r_ok 111.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 111) with (b64_of_bits 4607490282055794688).
  split; [exact (bits_finite 4607490282055794688 _ _ _ eq_refl) | ].
  rewrite (bits_val 4607490282055794688 false 4811462883147776 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 111) with 111 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 111)) with 112 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1094%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_112 : ln_r_ok 112.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 112) with (b64_of_bits 4607472689869750272).
  split; [exact (bits_finite 4607472689869750272 _ _ _ eq_refl) | ].
  rewrite (bits_val 4607472689869750272 false 4793870697103360 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 112) with 112 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 112)) with 113 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1090%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_113 : ln_r_ok 113.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 113) with (b64_of_bits 4607455097683705856).
  split; [exact (bits_finite 4607455097683705856 _ _ _ eq_refl) | ].
  rewrite (bits_val 4607455097683705856 false 4776278511058944 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 113) with 113 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 113)) with 114 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1086%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_114 : ln_r_ok 114.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 114) with (b64_of_bits 4607437505497661440).
  split; [exact (bits_finite 4607437505497661440 _ _ _ eq_refl) | ].
  rewrite (bits_val 4607437505497661440 false 4758686325014528 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 114) with 114 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 114)) with 115 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1082%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_115 : ln_r_ok 115.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 115) with (b64_of_bits 4607411117218594816).
  split; [exact (bits_finite 4607411117218594816 _ _ _ eq_refl) | ].
  rewrite (bits_val 4607411117218594816 false 4732298045947904 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 115) with 115 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 115)) with 116 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1076%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_116 : ln_r_ok 116.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 116) with (b64_of_bits 4607393525032550400).
  split; [exact (bits_finite 4607393525032550400 _ _ _ eq_refl) | ].
  rewrite (bits_val 4607393525032550400 false 4714705859903488 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 116) with 116 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 116)) with 117 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1072%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_117 : ln_r_ok 117.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 117) with (b64_of_bits 4607375932846505984).
  split; [exact (bits_finite 4607375932846505984 _ _ _ eq_refl) | ].
  rewrite (bits_val 4607375932846505984 false 4697113673859072 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 117) with 117 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 117)) with 118 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1068%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_118 : ln_r_ok 118.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 118) with (b64_of_bits 4607358340660461568).
  split; [exact (bits_finite 4607358340660461568 _ _ _ eq_refl) | ].
  rewrite (bits_val 4607358340660461568 false 4679521487814656 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 118) with 118 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 118)) with 119 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1064%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_119 : ln_r_ok 119.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 119) with (b64_of_bits 4607340748474417152).
  split; [exact (bits_finite 4607340748474417152 _ _ _ eq_refl) | ].
  rewrite (bits_val 4607340748474417152 false 4661929301770240 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 119) with 119 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 119)) with 120 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1060%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_120 : ln_r_ok 120.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 120) with (b64_of_bits 4607314360195350528).
  split; [exact (bits_finite 4607314360195350528 _ _ _ eq_refl) | ].
  rewrite (bits_val 4607314360195350528 false 4635541022703616 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 120) with 120 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 120)) with 121 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1054%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_121 : ln_r_ok 121.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 121) with (b64_of_bits 4607296768009306112).
  split; [exact (bits_finite 4607296768009306112 _ _ _ eq_refl) | ].
  rewrite (bits_val 4607296768009306112 false 4617948836659200 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 121) with 121 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 121)) with 122 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1050%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_122 : ln_r_ok 122.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 122) with (b64_of_bits 4607279175823261696).
  split; [exact (bits_finite 4607279175823261696 _ _ _ eq_refl) | ].
  rewrite (bits_val 4607279175823261696 false 4600356650614784 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 122) with 122 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 122)) with 123 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1046%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_123 : ln_r_ok 123.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 123) with (b64_of_bits 4607261583637217280).
  split; [exact (bits_finite 4607261583637217280 _ _ _ eq_refl) | ].
  rewrite (bits_val 4607261583637217280 false 4582764464570368 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 123) with 123 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 123)) with 124 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1042%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_124 : ln_r_ok 124.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 124) with (b64_of_bits 4607243991451172864).
  split; [exact (bits_finite 4607243991451172864 _ _ _ eq_refl) | ].
  rewrite (bits_val 4607243991451172864 false 4565172278525952 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 124) with 124 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 124)) with 125 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1038%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_125 : ln_r_ok 125.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 125) with (b64_of_bits 4607226399265128448).
  split; [exact (bits_finite 4607226399265128448 _ _ _ eq_refl) | ].
  rewrite (bits_val 4607226399265128448 false 4547580092481536 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 125) with 125 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 125)) with 126 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1034%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_126 : ln_r_ok 126.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 126) with (b64_of_bits 4607208807079084032).
  split; [exact (bits_finite 4607208807079084032 _ _ _ eq_refl) | ].
  rewrite (bits_val 4607208807079084032 false 4529987906437120 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 126) with 126 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 126)) with 127 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1030%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.
Lemma ln_r_ok_127 : ln_r_ok 127.
Proof.
  unfold ln_r_ok, ln_lo, ln_hi. change (ln_r 127) with (b64_of_bits 4607182418800017408).
  split; [exact (bits_finite 4607182418800017408 _ _ _ eq_refl) | ].
  rewrite (bits_val 4607182418800017408 false 4503599627370496 52 eq_refl). cbn [SpecFloat.cond_Zopp].
  replace (2 ^ 52) with 4503599627370496 by ring.
  replace (INR 127) with 127 by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR (S 127)) with 128 by (rewrite INR_IZR_INZ; reflexivity).
  cbv [Nat.ltb Nat.leb].
  split; [exists 1024%Z; change (bpow radix2 (-10)) with (/ 1024); lra | ].
  repeat split; lra.
Qed.

Theorem ln_r_table_ok i : (i < 128)%nat -> ln_r_ok i.
Proof.
  intros H.
  destruct i as [|i]; [exact ln_r_ok_0 | ].
  destruct i as [|i]; [exact ln_r_ok_1 | ].
  destruct i as [|i]; [exact ln_r_ok_2 | ].
  destruct i as [|i]; [exact ln_r_ok_3 | ].
  destruct i as [|i]; [exact ln_r_ok_4 | ].
  destruct i as [|i]; [exact ln_r_ok_5 | ].
  destruct i as [|i]; [exact ln_r_ok_6 | ].
  destruct i as [|i]; [exact ln_r_ok_7 | ].
  destruct i as [|i]; [exact ln_r_ok_8 | ].
  destruct i as [|i]; [exact ln_r_ok_9 | ].
  destruct i as [|i]; [exact ln_r_ok_10 | ].
  destruct i as [|i]; [exact ln_r_ok_11 | ].
  destruct i as [|i]; [exact ln_r_ok_12 | ].
  destruct i as [|i]; [exact ln_r_ok_13 | ].
  destruct i as [|i]; [exact ln_r_ok_14 | ].
  destruct i as [|i]; [exact ln_r_ok_15 | ].
  destruct i as [|i]; [exact ln_r_ok_16 | ].
  destruct i as [|i]; [exact ln_r_ok_17 | ].
  destruct i as [|i]; [exact ln_r_ok_18 | ].
  destruct i as [|i]; [exact ln_r_ok_19 | ].
  destruct i as [|i]; [exact ln_r_ok_20 | ].
  destruct i as [|i]; [exact ln_r_ok_21 | ].
  destruct i as [|i]; [exact ln_r_ok_22 | ].
  destruct i as [|i]; [exact ln_r_ok_23 | ].
  destruct i as [|i]; [exact ln_r_ok_24 | ].
  destruct i as [|i]; [exact ln_r_ok_25 | ].
  destruct i as [|i]; [exact ln_r_ok_26 | ].
  destruct i as [|i]; [exact ln_r_ok_27 | ].
  destruct i as [|i]; [exact ln_r_ok_28 | ].
  destruct i as [|i]; [exact ln_r_ok_29 | ].
  destruct i as [|i]; [exact ln_r_ok_30 | ].
  destruct i as [|i]; [exact ln_r_ok_31 | ].
  destruct i as [|i]; [exact ln_r_ok_32 | ].
  destruct i as [|i]; [exact ln_r_ok_33 | ].
  destruct i as [|i]; [exact ln_r_ok_34 | ].
  destruct i as [|i]; [exact ln_r_ok_35 | ].
  destruct i as [|i]; [exact ln_r_ok_36 | ].
  destruct i as [|i]; [exact ln_r_ok_37 | ].
  destruct i as [|i]; [exact ln_r_ok_38 | ].
  destruct i as [|i]; [exact ln_r_ok_39 | ].
  destruct i as [|i]; [exact ln_r_ok_40 | ].
  destruct i as [|i]; [exact ln_r_ok_41 | ].
  destruct i as [|i]; [exact ln_r_ok_42 | ].
  destruct i as [|i]; [exact ln_r_ok_43 | ].
  destruct i as [|i]; [exact ln_r_ok_44 | ].
  destruct i as [|i]; [exact ln_r_ok_45 | ].
  destruct i as [|i]; [exact ln_r_ok_46 | ].
  destruct i as [|i]; [exact ln_r_ok_47 | ].
  destruct i as [|i]; [exact ln_r_ok_48 | ].
  destruct i as [|i]; [exact ln_r_ok_49 | ].
  destruct i as [|i]; [exact ln_r_ok_50 | ].
  destruct i as [|i]; [exact ln_r_ok_51 | ].
  destruct i as [|i]; [exact ln_r_ok_52 | ].
  destruct i as [|i]; [exact ln_r_ok_53 | ].
  destruct i as [|i]; [exact ln_r_ok_54 | ].
  destruct i as [|i]; [exact ln_r_ok_55 | ].
  destruct i as [|i]; [exact ln_r_ok_56 | ].
  destruct i as [|i]; [exact ln_r_ok_57 | ].
  destruct i as [|i]; [exact ln_r_ok_58 | ].
  destruct i as [|i]; [exact ln_r_ok_59 | ].
  destruct i as [|i]; [exact ln_r_ok_60 | ].
  destruct i as [|i]; [exact ln_r_ok_61 | ].
  destruct i as [|i]; [exact ln_r_ok_62 | ].
  destruct i as [|i]; [exact ln_r_ok_63 | ].
  destruct i as [|i]; [exact ln_r_ok_64 | ].
  destruct i as [|i]; [exact ln_r_ok_65 | ].
  destruct i as [|i]; [exact ln_r_ok_66 | ].
  destruct i as [|i]; [exact ln_r_ok_67 | ].
  destruct i as [|i]; [exact ln_r_ok_68 | ].
  destruct i as [|i]; [exact ln_r_ok_69 | ].
  destruct i as [|i]; [exact ln_r_ok_70 | ].
  destruct i as [|i]; [exact ln_r_ok_71 | ].
  destruct i as [|i]; [exact ln_r_ok_72 | ].
  destruct i as [|i]; [exact ln_r_ok_73 | ].
  destruct i as [|i]; [exact ln_r_ok_74 | ].
  destruct i as [|i]; [exact ln_r_ok_75 | ].
  destruct i as [|i]; [exact ln_r_ok_76 | ].
  destruct i as [|i]; [exact ln_r_ok_77 | ].
  destruct i as [|i]; [exact ln_r_ok_78 | ].
  destruct i as [|i]; [exact ln_r_ok_79 | ].
  destruct i as [|i]; [exact ln_r_ok_80 | ].
  destruct i as [|i]; [exact ln_r_ok_81 | ].
  destruct i as [|i]; [exact ln_r_ok_82 | ].
  destruct i as [|i]; [exact ln_r_ok_83 | ].
  destruct i as [|i]; [exact ln_r_ok_84 | ].
  destruct i as [|i]; [exact ln_r_ok_85 | ].
  destruct i as [|i]; [exact ln_r_ok_86 | ].
  destruct i as [|i]; [exact ln_r_ok_87 | ].
  destruct i as [|i]; [exact ln_r_ok_88 | ].
  destruct i as [|i]; [exact ln_r_ok_89 | ].
  destruct i as [|i]; [exact ln_r_ok_90 | ].
  destruct i as [|i]; [exact ln_r_ok_91 | ].
  destruct i as [|i]; [exact ln_r_ok_92 | ].
  destruct i as [|i]; [exact ln_r_ok_93 | ].
  destruct i as [|i]; [exact ln_r_ok_94 | ].
  destruct i as [|i]; [exact ln_r_ok_95 | ].
  destruct i as [|i]; [exact ln_r_ok_96 | ].
  destruct i as [|i]; [exact ln_r_ok_97 | ].
  destruct i as [|i]; [exact ln_r_ok_98 | ].
  destruct i as [|i]; [exact ln_r_ok_99 | ].
  destruct i as [|i]; [exact ln_r_ok_100 | ].
  destruct i as [|i]; [exact ln_r_ok_101 | ].
  destruct i as [|i]; [exact ln_r_ok_102 | ].
  destruct i as [|i]; [exact ln_r_ok_103 | ].
  destruct i as [|i]; [exact ln_r_ok_104 | ].
  destruct i as [|i]; [exact ln_r_ok_105 | ].
  destruct i as [|i]; [exact ln_r_ok_106 | ].
  destruct i as [|i]; [exact ln_r_ok_107 | ].
  destruct i as [|i]; [exact ln_r_ok_108 | ].
  destruct i as [|i]; [exact ln_r_ok_109 | ].
  destruct i as [|i]; [exact ln_r_ok_110 | ].
  destruct i as [|i]; [exact ln_r_ok_111 | ].
  destruct i as [|i]; [exact ln_r_ok_112 | ].
  destruct i as [|i]; [exact ln_r_ok_113 | ].
  destruct i as [|i]; [exact ln_r_ok_114 | ].
  destruct i as [|i]; [exact ln_r_ok_115 | ].
  destruct i as [|i]; [exact ln_r_ok_116 | ].
  destruct i as [|i]; [exact ln_r_ok_117 | ].
  destruct i as [|i]; [exact ln_r_ok_118 | ].
  destruct i as [|i]; [exact ln_r_ok_119 | ].
  destruct i as [|i]; [exact ln_r_ok_120 | ].
  destruct i as [|i]; [exact ln_r_ok_121 | ].
  destruct i as [|i]; [exact ln_r_ok_122 | ].
  destruct i as [|i]; [exact ln_r_ok_123 | ].
  destruct i as [|i]; [exact ln_r_ok_124 | ].
  destruct i as [|i]; [exact ln_r_ok_125 | ].
  destruct i as [|i]; [exact ln_r_ok_126 | ].
  destruct i as [|i]; [exact ln_r_ok_127 | ].
  lia.
Qed.

(** [R[0] = R[127] = 1]: arguments near 1 reduce with no table term. *)
Lemma ln_r_ends : B (ln_r 0) = 1 /\ B (ln_r 127) = 1.
Proof.
  split.
  - change (ln_r 0) with (b64_of_bits 4607182418800017408).
    rewrite (bits_val 4607182418800017408 false 4503599627370496 52 eq_refl). cbn [SpecFloat.cond_Zopp].
    replace (2 ^ 52) with 4503599627370496 by ring. lra.
  - change (ln_r 127) with (b64_of_bits 4607182418800017408).
    rewrite (bits_val 4607182418800017408 false 4503599627370496 52 eq_refl). cbn [SpecFloat.cond_Zopp].
    replace (2 ^ 52) with 4503599627370496 by ring. lra.
Qed.

(** The accurate path's Q128 constants (docs/ln.md, section 6), as
    crates/morphiq-numerics/src/ln/tables.rs gives them: [-ln R[i]] as
    [(negative, m, e)] with value [(-1)^negative·m·2^e] ([m = 0] where
    [R[i] = 1]); [ln 2] as [m·2^-128]; [1/k] as [(m, e)], [k = 1 ..]. Their
    errors are proved in formal/ln/LnTableCheck.v. *)
Definition ln_neg_ln_r_q : list (bool * Z * Z) := [
  (false, 0%Z, (0)%Z);
  (false, 256718943005710385692603868903618128700%Z, (-134)%Z);
  (false, 214780843714777817510591060339871493724%Z, (-133)%Z);
  (false, 290966312107081599021777797313972502424%Z, (-133)%Z);
  (false, 189346578565388208869320306568858818703%Z, (-132)%Z);
  (false, 228019115685601422182423827135060741453%Z, (-132)%Z);
  (false, 266968311018043740463403664321820496753%Z, (-132)%Z);
  (false, 311825560606910492368743818633158812437%Z, (-132)%Z);
  (false, 175690565842157890247104371654833823896%Z, (-131)%Z);
  (false, 195613093388286331574342310911940015350%Z, (-131)%Z);
  (false, 215682497133981453865936348995369015011%Z, (-131)%Z);
  (false, 233003397150905456704409038487859228878%Z, (-131)%Z);
  (false, 253351396370745611067681702126711473060%Z, (-131)%Z);
  (false, 273852636403816209088211770146969515615%Z, (-131)%Z);
  (false, 291548856479520925809877779719752934261%Z, (-131)%Z);
  (false, 312340897051114526717050292800655466063%Z, (-131)%Z);
  (false, 330289922089561293947617637889416410600%Z, (-131)%Z);
  (false, 174179039348474145740524081036426815137%Z, (-130)%Z);
  (false, 183273479424765303854554597004573066371%Z, (-130)%Z);
  (false, 192429093324562203145175961123881752258%Z, (-130)%Z);
  (false, 201646709596670846365205373255404903337%Z, (-130)%Z);
  (false, 210927173737746426695091751878214639393%Z, (-130)%Z);
  (false, 220271348657689506677232977147659685365%Z, (-130)%Z);
  (false, 229680115161127696356075443908386969054%Z, (-130)%Z);
  (false, 239154372445654633414773302600750252208%Z, (-130)%Z);
  (false, 247100276317130489828518662047820882977%Z, (-130)%Z);
  (false, 256696998570006993667891611938598357252%Z, (-130)%Z);
  (false, 264746279672427742180866684538148044364%Z, (-130)%Z);
  (false, 272843444941642067057812948600822575220%Z, (-130)%Z);
  (false, 282624058050804727558322947896973879015%Z, (-130)%Z);
  (false, 290828600479512404603594936212751851702%Z, (-130)%Z);
  (false, 299082897866165800038943903873267544300%Z, (-130)%Z);
  (false, 307387557354367027444413062895592158428%Z, (-130)%Z);
  (false, 315743197269139185601572540810766332283%Z, (-130)%Z);
  (false, 324150447393185693234087242561534885569%Z, (-130)%Z);
  (false, 332609949251734601660347612670418593531%Z, (-130)%Z);
  (false, 170561178203145015290721073765702662784%Z, (-129)%Z);
  (false, 174844167378813532006988720622684578292%Z, (-129)%Z);
  (false, 179154281429190677105556582005567241636%Z, (-129)%Z);
  (false, 182622134710177121814229332312394483653%Z, (-129)%Z);
  (false, 186981949324636288026295774640212341098%Z, (-129)%Z);
  (false, 191369873834156539663126088935979261926%Z, (-129)%Z);
  (false, 194900697493597384682106490962234864668%Z, (-129)%Z);
  (false, 199340143984895522258236928236989068051%Z, (-129)%Z);
  (false, 202912670476390219066010938056626960441%Z, (-129)%Z);
  (false, 207404863247361660632389132472471308484%Z, (-129)%Z);
  (false, 211020089458307899516007367874011043599%Z, (-129)%Z);
  (false, 214654622709841876775538373991875476871%Z, (-129)%Z);
  (false, 218308670327375585394770949475287383039%Z, (-129)%Z);
  (false, 222903993214338554142578046532975499903%Z, (-129)%Z);
  (false, 226602723698006223117928237778144252042%Z, (-129)%Z);
  (false, 230321665923976917580200940812745649058%Z, (-129)%Z);
  (false, 234061042000976128255501121566649257298%Z, (-129)%Z);
  (true, 233910448731900000853730477299428349939%Z, (-129)%Z);
  (true, 230129523819268451198264355617327774895%Z, (-129)%Z);
  (true, 226327476311523764149750591472009868720%Z, (-129)%Z);
  (true, 222504068874274334169580955775357950049%Z, (-129)%Z);
  (true, 219622350805054283289278088461211245446%Z, (-129)%Z);
  (true, 215760980254399467702541742440527203854%Z, (-129)%Z);
  (true, 211877576086365445754282873687208881370%Z, (-129)%Z);
  (true, 207971885402269091512496525121853929923%Z, (-129)%Z);
  (true, 205027837261776371314838454752147650884%Z, (-129)%Z);
  (true, 201082523407893074126816515430798714615%Z, (-129)%Z);
  (true, 197114204678524906013177120706670565045%Z, (-129)%Z);
  (true, 194122706526304434158419319414229643069%Z, (-129)%Z);
  (true, 190113477059150330672573615828098200511%Z, (-129)%Z);
  (true, 187090978824693478613843451349405239910%Z, (-129)%Z);
  (true, 183039986305243979223557094196624930213%Z, (-129)%Z);
  (true, 179985838768933801984653719142728317479%Z, (-129)%Z);
  (true, 176917923428609805914038029479477101852%Z, (-129)%Z);
  (true, 172805737299098678120811589934959544457%Z, (-129)%Z);
  (true, 339410418461876414997974235901103752856%Z, (-130)%Z);
  (true, 333180982107089589002373896484451911267%Z, (-130)%Z);
  (true, 324830468383940747573725487390897454535%Z, (-130)%Z);
  (true, 318533790380448949962365132905630999596%Z, (-130)%Z);
  (true, 312207848082833162590746948009388640142%Z, (-130)%Z);
  (true, 305852368204373782373515418194235342752%Z, (-130)%Z);
  (true, 299467073612223929253669340429986832129%Z, (-130)%Z);
  (true, 293051683254897347910914772063471078067%Z, (-130)%Z);
  (true, 286605912088039350466723927286413680030%Z, (-130)%Z);
  (true, 280129470998431782478720538483797599883%Z, (-130)%Z);
  (true, 273622066726181354059189080287579775461%Z, (-130)%Z);
  (true, 267083401785038974449595787159957438346%Z, (-130)%Z);
  (true, 260513174380795959096076032834084263573%Z, (-130)%Z);
  (true, 253911078327701140328094387076869616672%Z, (-130)%Z);
  (true, 247276802962841003132152984867005255771%Z, (-130)%Z);
  (true, 240610033058422983075224886271778777368%Z, (-130)%Z);
  (true, 233910448731900000853730477299428349939%Z, (-130)%Z);
  (true, 227177725353872163744598377981989730902%Z, (-130)%Z);
  (true, 222670670018265032053713734863226973801%Z, (-130)%Z);
  (true, 215881980296293792442472031816518754827%Z, (-130)%Z);
  (true, 209059261912270410984807934338658102321%Z, (-130)%Z);
  (true, 202202172005974429848222726339896202290%Z, (-130)%Z);
  (true, 197611511776898934551353007581626057768%Z, (-130)%Z);
  (true, 190696359895323222383782292489576946738%Z, (-130)%Z);
  (true, 183745896446814715591308858105665091149%Z, (-130)%Z);
  (true, 179092457836726603825350471787190972705%Z, (-130)%Z);
  (true, 172082333495132798338009543415537040154%Z, (-130)%Z);
  (true, 334777557911593929282003848241171533399%Z, (-131)%Z);
  (true, 320635921250299622345247528227825560302%Z, (-131)%Z);
  (true, 311167184972278887207860396666673988182%Z, (-131)%Z);
  (true, 296902040004419369377265490604427407359%Z, (-131)%Z);
  (true, 287350244466551046791589262921399207485%Z, (-131)%Z);
  (true, 272959414819228489526732775691032347821%Z, (-131)%Z);
  (true, 263323089941552055887942861394800155320%Z, (-131)%Z);
  (true, 248804341204714933205932986256309928508%Z, (-131)%Z);
  (true, 239081977529962841390620165929247100429%Z, (-131)%Z);
  (true, 229324766599101959152754244359208215537%Z, (-131)%Z);
  (true, 214623062448918972113468474263996655820%Z, (-131)%Z);
  (true, 204777630612936586782474120162906449937%Z, (-131)%Z);
  (true, 194896462103937199890894459857178793630%Z, (-131)%Z);
  (true, 180007132723264327238024291772054699317%Z, (-131)%Z);
  (true, 340070954243443330824791786172488876671%Z, (-132)%Z);
  (true, 320054321878416779727719798190152913405%Z, (-132)%Z);
  (true, 299963827234027460565492857661312372489%Z, (-132)%Z);
  (true, 269688394981063957821956643639270772616%Z, (-132)%Z);
  (true, 249410837572460883524359882997256774602%Z, (-132)%Z);
  (true, 229057476034696421000343596928088092690%Z, (-132)%Z);
  (true, 208627741479252749454655847024044745558%Z, (-132)%Z);
  (true, 188121058589462975592530422821349238093%Z, (-132)%Z);
  (true, 314430963079648555659354768738561111308%Z, (-133)%Z);
  (true, 273027735473655831619244130184812730219%Z, (-133)%Z);
  (true, 231466479898420175793039495846577930995%Z, (-133)%Z);
  (true, 189745985407221356006643803913892997840%Z, (-133)%Z);
  (true, 295730054161616959041608096527083568724%Z, (-134)%Z);
  (true, 211644731623213367151146060951531514366%Z, (-134)%Z);
  (true, 254466992334967015760930892334780970388%Z, (-135)%Z);
  (false, 0%Z, (0)%Z)
].
Definition ln_ln2_q : Z := 235865763225513294137944142764154484399%Z.
Definition ln_recips : list (Z * Z) := [
  (170141183460469231731687303715884105728%Z, (-127)%Z);
  (170141183460469231731687303715884105728%Z, (-128)%Z);
  (226854911280625642308916404954512140971%Z, (-129)%Z);
  (170141183460469231731687303715884105728%Z, (-129)%Z);
  (272225893536750770770699685945414569165%Z, (-130)%Z);
  (226854911280625642308916404954512140971%Z, (-130)%Z);
  (194447066811964836264785489961010406546%Z, (-130)%Z);
  (170141183460469231731687303715884105728%Z, (-130)%Z);
  (302473215040834189745221873272682854628%Z, (-131)%Z);
  (272225893536750770770699685945414569165%Z, (-131)%Z);
  (247478085033409791609726987223104153786%Z, (-131)%Z);
  (226854911280625642308916404954512140971%Z, (-131)%Z);
  (209404533489808285208230527650318899358%Z, (-131)%Z);
  (194447066811964836264785489961010406546%Z, (-131)%Z);
  (181483929024500513847133123963609712777%Z, (-131)%Z);
  (170141183460469231731687303715884105728%Z, (-131)%Z);
  (320265757102059730318470218759311257841%Z, (-132)%Z);
  (302473215040834189745221873272682854628%Z, (-132)%Z)
].
