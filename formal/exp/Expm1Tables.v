(** Written by generators/expm1_constants.py; do not edit. *)
From Coq Require Import Reals ZArith List Lia.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import IEEE64 Grid Encodings.
From Interval Require Import Tactic.
Import ListNotations.
Open Scope R_scope.
Definition em_overflow : f64 := b64_of_bits 4649454530587146736.
Lemma em_overflow_val : B em_overflow = 6243314768165360 / 2 ^ 43.
Proof. exact (bits_val 4649454530587146736 false 6243314768165360 43 eq_refl). Qed.
Lemma em_overflow_finite : finite em_overflow.
Proof. exact (bits_finite 4649454530587146736 _ _ _ eq_refl). Qed.
Definition em_minus_one_screen : f64 := b64_of_bits 13853836650999914722.
Lemma em_minus_one_screen_val : B em_minus_one_screen = (- 5267796835639522) / 2 ^ 47.
Proof. exact (bits_val 13853836650999914722 true 5267796835639522 47 eq_refl). Qed.
Lemma em_minus_one_screen_finite : finite em_minus_one_screen.
Proof. exact (bits_finite 13853836650999914722 _ _ _ eq_refl). Qed.
Definition em_minus_one : f64 := b64_of_bits 13830554455654793216.
Lemma em_minus_one_val : B em_minus_one = (- 4503599627370496) / 2 ^ 52.
Proof. exact (bits_val 13830554455654793216 true 4503599627370496 52 eq_refl). Qed.
Lemma em_minus_one_finite : finite em_minus_one.
Proof. exact (bits_finite 13830554455654793216 _ _ _ eq_refl). Qed.
Definition em_tiny : f64 := b64_of_bits 4363988038922010624.
Lemma em_tiny_val : B em_tiny = 4503599627370496 / 2 ^ 106.
Proof. exact (bits_val 4363988038922010624 false 4503599627370496 106 eq_refl). Qed.
Lemma em_tiny_finite : finite em_tiny.
Proof. exact (bits_finite 4363988038922010624 _ _ _ eq_refl). Qed.
Definition em_small : f64 := b64_of_bits 4584664420663164928.
Lemma em_small_val : B em_small = 4503599627370496 / 2 ^ 57.
Proof. exact (bits_val 4584664420663164928 false 4503599627370496 57 eq_refl). Qed.
Lemma em_small_finite : finite em_small.
Proof. exact (bits_finite 4584664420663164928 _ _ _ eq_refl). Qed.
Definition em_c3 : f64 := b64_of_bits 4595172819793696085.
Lemma em_c3_val : B em_c3 = 6004799503160661 / 2 ^ 55.
Proof. exact (bits_val 4595172819793696085 false 6004799503160661 55 eq_refl). Qed.
Lemma em_c3_finite : finite em_c3.
Proof. exact (bits_finite 4595172819793696085 _ _ _ eq_refl). Qed.
Definition em_a3 : R := IZR 6004799503160661 * bpow radix2 (-55).
Lemma em_c3_real : B em_c3 = em_a3.
Proof. rewrite em_c3_val. unfold em_a3. apply Rle_antisym; interval with (i_prec 120). Qed.
Definition em_c4 : f64 := b64_of_bits 4586165620538955097.
Lemma em_c4_val : B em_c4 = 6004799503160665 / 2 ^ 57.
Proof. exact (bits_val 4586165620538955097 false 6004799503160665 57 eq_refl). Qed.
Lemma em_c4_finite : finite em_c4.
Proof. exact (bits_finite 4586165620538955097 _ _ _ eq_refl). Qed.
Definition em_a4 : R := IZR 6004799503160665 * bpow radix2 (-57).
Lemma em_c4_real : B em_c4 = em_a4.
Proof. rewrite em_c4_val. unfold em_a4. apply Rle_antisym; interval with (i_prec 120). Qed.
Definition em_c5 : f64 := b64_of_bits 4575957461383625656.
Lemma em_c5_val : B em_c5 = 4803839602572216 / 2 ^ 59.
Proof. exact (bits_val 4575957461383625656 false 4803839602572216 59 eq_refl). Qed.
Lemma em_c5_finite : finite em_c5.
Proof. exact (bits_finite 4575957461383625656 _ _ _ eq_refl). Qed.
Definition em_a5 : R := IZR 600479950321527 * bpow radix2 (-56).
Lemma em_c5_real : B em_c5 = em_a5.
Proof. rewrite em_c5_val. unfold em_a5. apply Rle_antisym; interval with (i_prec 120). Qed.
Definition em_c6 : f64 := b64_of_bits 4564047942367959211.
Lemma em_c6_val : B em_c6 = 6405119469017259 / 2 ^ 62.
Proof. exact (bits_val 4564047942367959211 false 6405119469017259 62 eq_refl). Qed.
Lemma em_c6_finite : finite em_c6.
Proof. exact (bits_finite 4564047942367959211 _ _ _ eq_refl). Qed.
Definition em_a6 : R := IZR 6405119469017259 * bpow radix2 (-62).
Lemma em_c6_real : B em_c6 = em_a6.
Proof. rewrite em_c6_val. unfold em_a6. apply Rle_antisym; interval with (i_prec 120). Qed.
Definition em_c7 : f64 := b64_of_bits 4551452154827725632.
Lemma em_c7_val : B em_c7 = 7320130810895168 / 2 ^ 65.
Proof. exact (bits_val 4551452154827725632 false 7320130810895168 65 eq_refl). Qed.
Lemma em_c7_finite : finite em_c7.
Proof. exact (bits_finite 4551452154827725632 _ _ _ eq_refl). Qed.
Definition em_a7 : R := IZR 114377043920237 * bpow radix2 (-59).
Lemma em_c7_real : B em_c7 = em_a7.
Proof. rewrite em_c7_val. unfold em_a7. apply Rle_antisym; interval with (i_prec 120). Qed.
Definition em_c8 : f64 := b64_of_bits 4537941498814083276.
Lemma em_c8_val : B em_c8 = 7320273679364300 / 2 ^ 68.
Proof. exact (bits_val 4537941498814083276 false 7320273679364300 68 eq_refl). Qed.
Lemma em_c8_finite : finite em_c8.
Proof. exact (bits_finite 4537941498814083276 _ _ _ eq_refl). Qed.
Definition em_a8 : R := IZR 1830068419841075 * bpow radix2 (-66).
Lemma em_c8_real : B em_c8 = em_a8.
Proof. rewrite em_c8_val. unfold em_a8. apply Rle_antisym; interval with (i_prec 120). Qed.
Definition em_c9 : f64 := b64_of_bits 4523831720251825955.
Lemma em_c9_val : B em_c9 = 6721293999218467 / 2 ^ 71.
Proof. exact (bits_val 4523831720251825955 false 6721293999218467 71 eq_refl). Qed.
Lemma em_c9_finite : finite em_c9.
Proof. exact (bits_finite 4523831720251825955 _ _ _ eq_refl). Qed.
Definition em_a9 : R := IZR 6721293999218467 * bpow radix2 (-71).
Lemma em_c9_real : B em_c9 = em_a9.
Proof. rewrite em_c9_val. unfold em_a9. apply Rle_antisym; interval with (i_prec 120). Qed.
Definition em_w (x : R) : R := (B em_c3 + x * (B em_c4 + x * (B em_c5 + x * (B em_c6 + x * (B em_c7 + x * (B em_c8 + x * B em_c9)))))).
Definition em_poly_difference (x : R) : R := ((1/108086391056891904) + x * ((-11/432345564227567616) + x * ((-81913/1080863910568919040) + x * ((45935089/207525870829232455680) + x * ((28184089313/181585136975578398720) + x * ((-10799946515137/23242897532874035036160) + x * ((-608124414074802329/6693954489467722090414080) + x * ((1/3628800) + x * ((1/39916800) + x * ((1/479001600) + x * ((1/6227020800) + x * ((1/87178291200) + x * ((1/1307674368000) + x * (1/20922789888000)))))))))))))).
Definition em_recip_bits : list (Z * nat) := [
  (170141183460469231731687303715884105728%Z, 128%nat);
  (226854911280625642308916404954512140971%Z, 129%nat);
  (170141183460469231731687303715884105728%Z, 129%nat);
  (272225893536750770770699685945414569165%Z, 130%nat);
  (226854911280625642308916404954512140971%Z, 130%nat);
  (194447066811964836264785489961010406546%Z, 130%nat);
  (170141183460469231731687303715884105728%Z, 130%nat);
  (302473215040834189745221873272682854628%Z, 131%nat);
  (272225893536750770770699685945414569165%Z, 131%nat);
  (247478085033409791609726987223104153786%Z, 131%nat);
  (226854911280625642308916404954512140971%Z, 131%nat);
  (209404533489808285208230527650318899358%Z, 131%nat);
  (194447066811964836264785489961010406546%Z, 131%nat);
  (181483929024500513847133123963609712777%Z, 131%nat);
  (170141183460469231731687303715884105728%Z, 131%nat)
].
Definition em_recip k := nth (k - 2) em_recip_bits (0%Z, 0%nat).
Definition em_recip_ok k : Prop :=
 (2^127 <= fst (em_recip k) < 2^128)%Z /\
 Rabs (IZR (fst (em_recip k)) / 2^snd (em_recip k) * INR k - 1) <= /2^127.
Lemma em_recip_ok_2 : em_recip_ok 2.
Proof.
 unfold em_recip_ok; change (em_recip 2) with (170141183460469231731687303715884105728%Z, 128%nat); cbn [fst snd].
 split; [lia | ]. rewrite INR_IZR_INZ.
 change (Z.of_nat 2) with 2%Z. interval with (i_prec 140).
Qed.
Lemma em_recip_ok_3 : em_recip_ok 3.
Proof.
 unfold em_recip_ok; change (em_recip 3) with (226854911280625642308916404954512140971%Z, 129%nat); cbn [fst snd].
 split; [lia | ]. rewrite INR_IZR_INZ.
 change (Z.of_nat 3) with 3%Z. interval with (i_prec 140).
Qed.
Lemma em_recip_ok_4 : em_recip_ok 4.
Proof.
 unfold em_recip_ok; change (em_recip 4) with (170141183460469231731687303715884105728%Z, 129%nat); cbn [fst snd].
 split; [lia | ]. rewrite INR_IZR_INZ.
 change (Z.of_nat 4) with 4%Z. interval with (i_prec 140).
Qed.
Lemma em_recip_ok_5 : em_recip_ok 5.
Proof.
 unfold em_recip_ok; change (em_recip 5) with (272225893536750770770699685945414569165%Z, 130%nat); cbn [fst snd].
 split; [lia | ]. rewrite INR_IZR_INZ.
 change (Z.of_nat 5) with 5%Z. interval with (i_prec 140).
Qed.
Lemma em_recip_ok_6 : em_recip_ok 6.
Proof.
 unfold em_recip_ok; change (em_recip 6) with (226854911280625642308916404954512140971%Z, 130%nat); cbn [fst snd].
 split; [lia | ]. rewrite INR_IZR_INZ.
 change (Z.of_nat 6) with 6%Z. interval with (i_prec 140).
Qed.
Lemma em_recip_ok_7 : em_recip_ok 7.
Proof.
 unfold em_recip_ok; change (em_recip 7) with (194447066811964836264785489961010406546%Z, 130%nat); cbn [fst snd].
 split; [lia | ]. rewrite INR_IZR_INZ.
 change (Z.of_nat 7) with 7%Z. interval with (i_prec 140).
Qed.
Lemma em_recip_ok_8 : em_recip_ok 8.
Proof.
 unfold em_recip_ok; change (em_recip 8) with (170141183460469231731687303715884105728%Z, 130%nat); cbn [fst snd].
 split; [lia | ]. rewrite INR_IZR_INZ.
 change (Z.of_nat 8) with 8%Z. interval with (i_prec 140).
Qed.
Lemma em_recip_ok_9 : em_recip_ok 9.
Proof.
 unfold em_recip_ok; change (em_recip 9) with (302473215040834189745221873272682854628%Z, 131%nat); cbn [fst snd].
 split; [lia | ]. rewrite INR_IZR_INZ.
 change (Z.of_nat 9) with 9%Z. interval with (i_prec 140).
Qed.
Lemma em_recip_ok_10 : em_recip_ok 10.
Proof.
 unfold em_recip_ok; change (em_recip 10) with (272225893536750770770699685945414569165%Z, 131%nat); cbn [fst snd].
 split; [lia | ]. rewrite INR_IZR_INZ.
 change (Z.of_nat 10) with 10%Z. interval with (i_prec 140).
Qed.
Lemma em_recip_ok_11 : em_recip_ok 11.
Proof.
 unfold em_recip_ok; change (em_recip 11) with (247478085033409791609726987223104153786%Z, 131%nat); cbn [fst snd].
 split; [lia | ]. rewrite INR_IZR_INZ.
 change (Z.of_nat 11) with 11%Z. interval with (i_prec 140).
Qed.
Lemma em_recip_ok_12 : em_recip_ok 12.
Proof.
 unfold em_recip_ok; change (em_recip 12) with (226854911280625642308916404954512140971%Z, 131%nat); cbn [fst snd].
 split; [lia | ]. rewrite INR_IZR_INZ.
 change (Z.of_nat 12) with 12%Z. interval with (i_prec 140).
Qed.
Lemma em_recip_ok_13 : em_recip_ok 13.
Proof.
 unfold em_recip_ok; change (em_recip 13) with (209404533489808285208230527650318899358%Z, 131%nat); cbn [fst snd].
 split; [lia | ]. rewrite INR_IZR_INZ.
 change (Z.of_nat 13) with 13%Z. interval with (i_prec 140).
Qed.
Lemma em_recip_ok_14 : em_recip_ok 14.
Proof.
 unfold em_recip_ok; change (em_recip 14) with (194447066811964836264785489961010406546%Z, 131%nat); cbn [fst snd].
 split; [lia | ]. rewrite INR_IZR_INZ.
 change (Z.of_nat 14) with 14%Z. interval with (i_prec 140).
Qed.
Lemma em_recip_ok_15 : em_recip_ok 15.
Proof.
 unfold em_recip_ok; change (em_recip 15) with (181483929024500513847133123963609712777%Z, 131%nat); cbn [fst snd].
 split; [lia | ]. rewrite INR_IZR_INZ.
 change (Z.of_nat 15) with 15%Z. interval with (i_prec 140).
Qed.
Lemma em_recip_ok_16 : em_recip_ok 16.
Proof.
 unfold em_recip_ok; change (em_recip 16) with (170141183460469231731687303715884105728%Z, 131%nat); cbn [fst snd].
 split; [lia | ]. rewrite INR_IZR_INZ.
 change (Z.of_nat 16) with 16%Z. interval with (i_prec 140).
Qed.
Theorem em_recip_table_ok k : (2 <= k <= 16)%nat -> em_recip_ok k.
Proof.
 intros H. destruct k as [|[|k]]; try lia.
 destruct k as [|k]; [exact em_recip_ok_2 | ].
 destruct k as [|k]; [exact em_recip_ok_3 | ].
 destruct k as [|k]; [exact em_recip_ok_4 | ].
 destruct k as [|k]; [exact em_recip_ok_5 | ].
 destruct k as [|k]; [exact em_recip_ok_6 | ].
 destruct k as [|k]; [exact em_recip_ok_7 | ].
 destruct k as [|k]; [exact em_recip_ok_8 | ].
 destruct k as [|k]; [exact em_recip_ok_9 | ].
 destruct k as [|k]; [exact em_recip_ok_10 | ].
 destruct k as [|k]; [exact em_recip_ok_11 | ].
 destruct k as [|k]; [exact em_recip_ok_12 | ].
 destruct k as [|k]; [exact em_recip_ok_13 | ].
 destruct k as [|k]; [exact em_recip_ok_14 | ].
 destruct k as [|k]; [exact em_recip_ok_15 | ].
 destruct k as [|k]; [exact em_recip_ok_16 | ].
 lia.
Qed.
