(** asinh's large form, [x >= 2^28]: the transcription's fast value against
    [arcsinh], relatively within [2^-63]. *)
From Coq Require Import Reals ZArith Lia Lra Psatz List.
From Flocq Require Import Core Mult_error IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add Binary64Mul IEEE64 IEEE64Add IEEE64Mul IEEE64Eft IEEE64Sqrt Grid Encodings RoundingCore RoundingTest.
From Interval Require Import Tactic.
Require Import Ln1pLemmas AsinTables AsinKernel AsinSqrtStep AsinSegment AsinNormal AsinRecip AsinPath
  LnFastValue AsinhTables AsinhKernel AsinhConst AsinhWithin AsinhOps AsinhRoot AsinhLog AsinhLarge.
Open Scope R_scope.

Lemma ln2_words : finite (aw (fst asinh_ln2)) /\ finite (aw (snd asinh_ln2)) /\
  B (aw (fst asinh_ln2)) = IZR 6243314768165359 * bpow radix2 (-53) /\
  B (aw (snd asinh_ln2)) = IZR 7525737178955839 * bpow radix2 (-108).
Proof.
  unfold asinh_ln2. cbn [fst snd].
  destruct (word_ok_intro (0x3fe62e42fefa39ef)%Z false 6243314768165359%positive 53%nat (6243314768165359)%Z 0%Z (-53)%Z
    eq_refl eq_refl ltac:(lia) eq_refl) as [F0 V0].
  destruct (word_ok_intro (0x3c7abc9e3b39803f)%Z false 7525737178955839%positive 108%nat (7525737178955839)%Z 0%Z (-108)%Z
    eq_refl eq_refl ltac:(lia) eq_refl) as [F1 V1].
  repeat split; assumption.
Qed.

Lemma ln2_sum_close : Rabs (IZR 6243314768165359 * bpow radix2 (-53) + IZR 7525737178955839 * bpow radix2 (-108) - ln 2) <= 1e-30.
Proof. bpow_num. apply Rabs_le. split; interval with (i_prec 300). Qed.

Lemma ln2_bounds : 0.6931 <= ln 2 <= 0.6932.
Proof. split; interval with (i_prec 60). Qed.

Lemma ln2_vals : 0.69 <= IZR 6243314768165359 * bpow radix2 (-53) <= 0.7 /\ 0 <= IZR 7525737178955839 * bpow radix2 (-108) <= 1e-16.
Proof. bpow_num. split; split; interval with (i_prec 100). Qed.

Lemma bp_m53' : bpow radix2 (-53) = / 9007199254740992. Proof. bpow_num. reflexivity. Qed.
Lemma bp_m52' : bpow radix2 (-52) = / 4503599627370496. Proof. bpow_num. reflexivity. Qed.

Lemma eta_tiny : bpow radix2 (-1075) <= 1e-100.
Proof.
  apply Rle_trans with (bpow radix2 (-340)); [apply bpow_le; lia | ].
  bpow_num. apply Rle_trans with (/ 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000);
    [apply Rinv_le_contravar; [lra | ] | lra].
  simpl. lra.
Qed.

Theorem asinh_large_fast x : finite x -> bpow radix2 28 <= B x ->
  exists h l, asinh_large x = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    bpow radix2 (-8) <= B h /\ B h <= bpow radix2 10 /\
    Rabs (B h + B l - arcsinh (B x)) <= bpow radix2 (-63) * arcsinh (B x).
Proof.
  intros Fx L.
  assert (HXlo : 268435456 <= B x) by (rewrite bp28 in L; exact L).
  assert (HXhi : B x < bpow radix2 1024).
  { pose proof (abs_B2R_lt_emax 53 1024 x) as H. rewrite Rabs_pos_eq in H by lra. exact H. }
  assert (HX0 : 0 < B x) by lra.
  pose proof (lf_ln_fast_value_ok x Fx HX0) as LF.
  unfold asinh_large.
  destruct (lf_ln_fast_value x) as [lh ll] eqn:E1.
  destruct LF as [Flh [Fll [Dwl [Hlh [Hll Hlnerr]]]]].
  destruct ln2_words as [Fhi [Flo [Vhi Vlo]]].
  set (hi := aw (fst asinh_ln2)) in *. set (lo := aw (snd asinh_ln2)) in *.
  pose proof ln2_bounds as [Hl2a Hl2b].
  destruct ln2_vals as [[Hv1 Hv2] [Hv3 Hv4]].
  assert (Hp0 : 1 <= bpow radix2 1020) by (apply Rle_trans with (bpow radix2 0); [simpl; lra | apply bpow_le; lia]).
  assert (Hhi_b : Rabs (B hi) <= bpow radix2 1020) by (rewrite Rabs_pos_eq by (rewrite Vhi; lra); rewrite Vhi; lra).
  assert (Hlo_b : Rabs (B lo) <= bpow radix2 1020) by (rewrite Rabs_pos_eq by (rewrite Vlo; lra); rewrite Vlo; lra).
  pose proof (two_sum_ieee hi lo Fhi Flo Hhi_b Hlo_b) as TS.
  destruct (two_sum64 hi lo) as [ch cl] eqn:E2. cbv beta iota in TS.
  destruct TS as [Fch [Fcl [Ech Escl]]].
  assert (Hhl : 0.69 <= B hi + B lo <= 0.7001) by (rewrite Vhi, Vlo; split; lra).
  destruct Hhl as [Hhl1 Hhl2].
  assert (Hch_lo : 1 / 2 <= B ch).
  { rewrite Ech. apply Rle_trans with (bpow radix2 (-1)); [rewrite bp1; lra | apply rndF_ge_bpow; [lia | rewrite bp1; lra]]. }
  assert (Hch_hi : B ch <= 1).
  { pose proof (rnd_le_pow 0 (B hi + B lo) ltac:(lia) ltac:(change (bpow radix2 0) with 1; lra)) as H. change (bpow radix2 0) with 1 in H. rewrite Ech. exact H. }
  assert (Dwc : B ch = rndF (B ch + B cl)) by (rewrite Escl; exact Ech).
  assert (Hcl : Rabs (B cl) <= bpow radix2 (-52) * Rabs (B ch)).
  { apply lo_bound; [ | exact Dwc]. rewrite Rabs_pos_eq by lra. apply Rle_trans with (1 / 2); [apply Rle_trans with (bpow radix2 (-1)); [apply bpow_le; lia | rewrite bp1; lra] | exact Hch_lo]. }
  rewrite bp_m52', (Rabs_pos_eq (B ch)) in Hcl by lra.
  (* ln x *)
  assert (HlnXlo : 19.4 <= ln (B x)).
  { apply Rle_trans with (ln (bpow radix2 28)); [rewrite ln_bpow; change (IZR 28) with 28; lra | apply ln_mono; [apply bpow_gt_0 | exact L]]. }
  assert (HlnXhi : ln (B x) <= 710).
  { apply Rle_trans with (ln (bpow radix2 1024)); [apply ln_mono; lra | rewrite ln_bpow; change (IZR 1024) with 1024; lra]. }
  assert (HLN : Rabs (B lh + B ll - ln (B x)) <= / 18446744073709551616 * Rabs (ln (B x))).
  { assert (H264 : 2 ^ 64 = 18446744073709551616) by (simpl; ring). rewrite H264 in Hlnerr. exact Hlnerr. }
  rewrite (Rabs_pos_eq (ln (B x))) in HLN by lra.
  assert (HLNb : 19.39 <= B lh + B ll <= 710.01).
  { apply Rabs_le_inv in HLN. destruct HLN as [H1 H2].
    assert (/ 18446744073709551616 * ln (B x) <= / 18446744073709551616 * 710) by (apply Rmult_le_compat_l; lra).
    assert (0 <= / 18446744073709551616 * ln (B x)) by (apply Rmult_le_pos; lra).
    split; lra. }
  destruct HLNb as [HLNb1 HLNb2].
  assert (Hlh_lo : 16 <= B lh).
  { rewrite Dwl. apply Rle_trans with (bpow radix2 4); [change (bpow radix2 4) with 16; lra | apply rndF_ge_bpow; [lia | change (bpow radix2 4) with 16; lra]]. }
  assert (Hlh_hi : B lh <= 1024) by (apply Rabs_le_inv in Hlh; lra).
  assert (Hll_lh : Rabs (B ll) <= bpow radix2 (-52) * Rabs (B lh)).
  { apply lo_bound; [ | exact Dwl]. rewrite Rabs_pos_eq by lra. apply Rle_trans with 16; [apply Rle_trans with (bpow radix2 0); [apply bpow_le; lia | simpl; lra] | exact Hlh_lo]. }
  rewrite bp_m52', (Rabs_pos_eq (B lh)) in Hll_lh by lra.
  assert (Hb1016 : forall v, Rabs v <= 2048 -> Rabs v <= bpow radix2 1016).
  { intros v Hv. apply Rle_trans with 2048; [exact Hv | change 2048 with (bpow radix2 11); apply bpow_le; lia]. }
  assert (Hcl1 : Rabs (B cl) <= 1).
  { assert (/ 4503599627370496 * B ch <= / 4503599627370496 * 1) by (apply Rmult_le_compat_l; lra). lra. }
  assert (Hlh2048 : Rabs (B lh) <= 2048) by lra.
  assert (Hch2048 : Rabs (B ch) <= 2048) by (rewrite Rabs_pos_eq by lra; lra).
  assert (Hcl2048 : Rabs (B cl) <= 2048) by lra.
  assert (Hsum0 : B lh + B ll + (B ch + B cl) <> 0) by (rewrite Escl; lra).
  pose proof (add_ieee lh ll ch cl Flh Fll Dwl Fch Fcl Dwc (Hb1016 _ Hlh2048) (Hb1016 _ Hll) (Hb1016 _ Hch2048) (Hb1016 _ Hcl2048) Hsum0) as AD.
  pose proof (add64_normalized lh ll ch cl Flh Fll Fch Fcl ltac:(apply Rle_trans with 16; [apply Rle_trans with (bpow radix2 0); [apply bpow_le; lia | simpl; lra] | exact Hlh_lo]) ltac:(apply Rle_trans with 1024; [exact Hlh_hi | apply Rle_trans with (bpow radix2 10); [change (bpow radix2 10) with 1024; lra | apply bpow_le; lia]]) ltac:(rewrite bp_m52'; lra) ltac:(rewrite bp_m52'; lra) ltac:(rewrite Rabs_pos_eq by lra; lra)) as AN.
  destruct (add64 lh ll ch cl) as [sh sl] eqn:E3. cbv beta iota in AD, AN.
  destruct AD as [Fsh [Fsl Bd1]]. destruct AN as [_ [_ Dws]].
  (* the quotient 1/(4 x^2) *)
  destruct quarter_val as [Fq Vq].
  assert (HXinv : / (B x) <= bpow radix2 (-28)).
  { assert (bpow radix2 (-28) = / 268435456) by (bpow_num; reflexivity). rewrite H. apply Rinv_le_contravar; lra. }
  assert (Hq0 : B asinh_quarter <> 0) by (rewrite Vq; apply Rgt_not_eq, bpow_gt_0).
  assert (Hd1b : Rabs (B asinh_quarter / B x) <= bpow radix2 (-30)).
  { rewrite Vq, Rabs_pos_eq by (apply Rmult_le_pos; [apply bpow_ge_0 | apply Rlt_le, Rinv_0_lt_compat; lra]).
    assert (bpow radix2 (-30) = bpow radix2 (-2) * bpow radix2 (-28)) by (rewrite <- bpow_plus; reflexivity).
    rewrite H. unfold Rdiv. apply Rmult_le_compat_l; [apply bpow_ge_0 | exact HXinv]. }
  destruct (div_abs2 asinh_quarter x (-30) Fq ltac:(lra) Hd1b ltac:(lia)) as [Fd1 [Ed1 Bd1b]].
  set (d1 := fdiv asinh_quarter x) in *.
  assert (Hx0 : B x <> 0) by lra.
  assert (Hd2b : Rabs (B d1 / B x) <= bpow radix2 (-58)).
  { assert (Hd1p : 0 <= B d1).
    { rewrite Ed1, Vq. apply round_ge_generic; [exact _ | exact _ | apply generic_format_0 | ].
      apply Rmult_le_pos; [apply bpow_ge_0 | apply Rlt_le, Rinv_0_lt_compat; lra]. }
    rewrite Rabs_pos_eq by (apply Rmult_le_pos; [exact Hd1p | apply Rlt_le, Rinv_0_lt_compat; lra]).
    apply Rabs_le_inv in Bd1b. destruct Bd1b as [_ Bd1b'].
    assert (bpow radix2 (-58) = bpow radix2 (-30) * bpow radix2 (-28)) by (rewrite <- bpow_plus; reflexivity).
    rewrite H. unfold Rdiv. apply Rmult_le_compat; [exact Hd1p | apply Rlt_le, Rinv_0_lt_compat; lra | exact Bd1b' | exact HXinv]. }
  destruct (div_abs2 d1 x (-58) Fd1 Hx0 Hd2b ltac:(lia)) as [Fc [Ec Bc]].
  set (c := fdiv d1 x) in *.
  set (t4 := / (B x * B x) / 4).
  pose proof eta_tiny as Heta.
  assert (Ht4 : 0 <= t4 <= 4e-18).
  { assert (Hxx : 72057594037927936 <= B x * B x) by (assert (268435456 * 268435456 <= B x * B x) by (apply Rmult_le_compat; lra); lra).
    unfold t4. split.
    - apply Rmult_le_pos; [apply Rlt_le, Rinv_0_lt_compat; nra | lra].
    - assert (/ (B x * B x) <= / 72057594037927936) by (apply Rinv_le_contravar; lra). lra. }
  assert (Hc1 : Rabs (B d1 - B asinh_quarter / B x) <= / 9007199254740992 * Rabs (B asinh_quarter / B x) + bpow radix2 (-1075)).
  { rewrite Ed1. pose proof (rnd_err (B asinh_quarter / B x)) as R. rewrite bp_m53' in R. exact R. }
  assert (Hc2 : Rabs (B c - B d1 / B x) <= / 9007199254740992 * Rabs (B d1 / B x) + bpow radix2 (-1075)).
  { rewrite Ec. pose proof (rnd_err (B d1 / B x)) as R. rewrite bp_m53' in R. exact R. }
  assert (Hq30 : Rabs (B asinh_quarter / B x) <= 9.32e-10).
  { apply Rle_trans with (bpow radix2 (-30)); [exact Hd1b | assert (bpow radix2 (-30) = / 1073741824) by (bpow_num; reflexivity); rewrite H; lra]. }
  assert (Hq58 : Rabs (B d1 / B x) <= 3.47e-18).
  { apply Rle_trans with (bpow radix2 (-58)); [exact Hd2b | assert (bpow radix2 (-58) = / 288230376151711744) by (bpow_num; reflexivity); rewrite H; lra]. }
  assert (Hxe : B asinh_quarter / B x / B x = t4).
  { unfold t4. rewrite Vq. assert (bpow radix2 (-2) = / 4) by (bpow_num; reflexivity). rewrite H. field. lra. }
  assert (Hinv28 : / B x <= 3.7253e-9).
  { apply Rle_trans with (bpow radix2 (-28)); [exact HXinv | assert (bpow radix2 (-28) = / 268435456) by (bpow_num; reflexivity); rewrite H; lra]. }
  assert (Hct : Rabs (B c - t4) <= 1e-33).
  { assert (E : B c - t4 = (B c - B d1 / B x) + (B d1 - B asinh_quarter / B x) / B x) by (rewrite <- Hxe; field; lra).
    rewrite E.
    apply Rle_trans with (Rabs (B c - B d1 / B x) + Rabs ((B d1 - B asinh_quarter / B x) / B x)); [apply Rabs_triang | ].
    assert (Ha : Rabs (B d1 - B asinh_quarter / B x) <= 1.04e-25).
    { assert (/ 9007199254740992 * Rabs (B asinh_quarter / B x) <= / 9007199254740992 * 9.32e-10) by (apply Rmult_le_compat_l; lra). lra. }
    assert (Hz : Rabs ((B d1 - B asinh_quarter / B x) / B x) <= 3.9e-34).
    { unfold Rdiv. rewrite Rabs_mult, Rabs_Rinv by exact Hx0. rewrite (Rabs_pos_eq (B x)) by lra.
      assert (Rabs (B d1 - B asinh_quarter * / B x) * / B x <= 1.04e-25 * 3.7253e-9).
      { apply Rmult_le_compat; [apply Rabs_pos | apply Rlt_le, Rinv_0_lt_compat; lra | exact Ha | exact Hinv28]. }
      lra. }
    assert (/ 9007199254740992 * Rabs (B d1 / B x) <= / 9007199254740992 * 3.47e-18) by (apply Rmult_le_compat_l; lra).
    lra. }
  (* the sum sh + sl and the final addition *)
  set (LN := B lh + B ll) in *. set (LN2 := B ch + B cl) in *.
  assert (HLN2 : LN2 = B hi + B lo) by exact Escl.
  assert (Hsum0' : LN + LN2 <> 0) by lra.
  set (ea1 := (B sh + B sl - (LN + LN2)) / (LN + LN2)).
  assert (HS1 : B sh + B sl = (LN + LN2) * (1 + ea1)) by (unfold ea1; field; exact Hsum0').
  assert (Hea1 : Rabs ea1 <= 1e-31).
  { unfold ea1. apply Rle_trans with (3 * bpow radix2 (- prec) ^ 2 / (1 - 4 * bpow radix2 (- prec))); [exact Bd1 | ].
    replace (- prec)%Z with (-53)%Z by reflexivity. rewrite bp_m53'. simpl. lra. }
  assert (HSbd : Rabs (B sh + B sl) <= 1024).
  { rewrite HS1. apply Rabs_le_inv in Hea1. destruct Hea1 as [He1 He2].
    assert (Hp : (LN + LN2) * ea1 <= (LN + LN2) * 1e-31) by (apply Rmult_le_compat_l; lra).
    assert (Hp' : (LN + LN2) * (-1e-31) <= (LN + LN2) * ea1) by (apply Rmult_le_compat_l; lra).
    apply Rabs_le. split; lra. }
  assert (Hsh1024 : Rabs (B sh) <= 1024).
  { rewrite Dws. apply rnd_bound; [change 1024 with (bpow radix2 10); apply fmt_pow; lia | exact HSbd]. }
  assert (Hsl1024 : Rabs (B sl) <= 2048) by (apply Rabs_le_inv in HSbd; apply Rabs_le_inv in Hsh1024; apply Rabs_le; lra).
  assert (Hsh_pos : 16 <= B sh).
  { rewrite Dws. apply Rle_trans with (bpow radix2 4); [change (bpow radix2 4) with 16; lra | apply rndF_ge_bpow; [lia | ]].
    change (bpow radix2 4) with 16. apply Rabs_le_inv in Hea1. destruct Hea1 as [He1 He2].
    assert (Hp' : (LN + LN2) * (-1e-31) <= (LN + LN2) * ea1) by (apply Rmult_le_compat_l; lra). lra. }
  assert (Hb1018 : forall v, Rabs v <= 2048 -> Rabs v <= bpow radix2 1018).
  { intros v Hv. apply Rle_trans with 2048; [exact Hv | change 2048 with (bpow radix2 11); apply bpow_le; lia]. }
  assert (Hc2048 : Rabs (B c) <= 2048).
  { apply Rle_trans with (bpow radix2 (-58)); [exact Bc | ]. assert (bpow radix2 (-58) = / 288230376151711744) by (bpow_num; reflexivity). rewrite H. lra. }
  pose proof (add_f64_ieee sh sl c Fsh Fsl Fc Dws (Hb1018 (B sh) ltac:(lra)) (Hb1018 _ Hsl1024) (Hb1018 _ Hc2048)) as AF.
  pose proof (add_f64_normalized_ieee sh sl c Fsh Fsl Fc Dws (Hb1018 (B sh) ltac:(lra)) (Hb1018 _ Hsl1024) (Hb1018 _ Hc2048)) as AFN.
  destruct (add_f64_64 sh sl c) as [yh yl] eqn:E4. cbv beta iota in AF, AFN.
  destruct AF as [Fyh [Fyl Bd2]]. destruct AFN as [_ [_ Dwy]].
  exists yh, yl. split; [reflexivity | ]. split; [exact Fyh | ]. split; [exact Fyl | ]. split; [exact Dwy | ].
  set (S := B sh + B sl + B c).
  assert (HSVlo : 19 <= B sh + B sl).
  { apply Rabs_le_inv in Hea1. destruct Hea1 as [He1 He2].
    assert (Hp' : (LN + LN2) * (-1e-31) <= (LN + LN2) * ea1) by (apply Rmult_le_compat_l; lra). lra. }
  assert (Hcn : -1e-33 <= B c) by (apply Rabs_le_inv in Hct; destruct Hct as [Hct1 Hct2]; destruct Ht4 as [Ht41 Ht42]; lra).
  assert (HS : 0 < S) by (unfold S; lra).
  set (ea2 := (B yh + B yl - S) / S).
  assert (HY : B yh + B yl = S * (1 + ea2)) by (unfold ea2; field; lra).
  assert (Hea2 : Rabs ea2 <= 2.5e-32).
  { unfold ea2. apply Rle_trans with (2 * bpow radix2 (- prec) ^ 2); [exact Bd2 | ].
    replace (- prec)%Z with (-53)%Z by reflexivity. rewrite bp_m53'. simpl. lra. }
  pose proof (large_expansion (B x) HXlo) as EXP.
  set (A := arcsinh (B x)) in *.
  set (r := A - (ln (B x) + ln 2 + t4)).
  assert (HAr : A = ln (B x) + ln 2 + t4 + r) by (unfold r; ring).
  assert (Hr : Rabs r <= E114).
  { unfold r. replace (A - (ln (B x) + ln 2 + t4)) with (A - (ln 2 + ln (B x) + t4)) by ring. exact EXP. }
  pose proof (ln2_sum_close) as L2C.
  assert (Hl2c : Rabs (LN2 - ln 2) <= 1e-30) by (rewrite HLN2, Vhi, Vlo; exact L2C).
  assert (HLNr : Rabs (LN - ln (B x)) <= / 18446744073709551616 * Rabs (ln (B x))) by (rewrite (Rabs_pos_eq (ln (B x))) by lra; exact HLN).
  assert (Hl2 : 0.69 <= ln 2 <= 0.6932) by (split; lra).
  pose proof (large_final A (ln (B x)) (ln 2) LN LN2 (B sh + B sl) ea1 (B c) t4 ea2 r (B yh + B yl) HAr Hr HlnXlo HlnXhi
    Hl2 HLNr Hl2c HS1 Hea1 Ht4 Hct HY Hea2) as FIN.
  assert (Hb63 : bpow radix2 (-63) = / 9223372036854775808) by (bpow_num; reflexivity).
  assert (HAbd : 19 <= A <= 711).
  { apply Rabs_le_inv in Hr. destruct Hr as [Hr1 Hr2]. destruct Ht4 as [Ht41 Ht42].
    assert (E114 <= 1e-34) by (unfold E114; apply Rle_trans with (/ 10000000000000000000000000000000000); [apply Rinv_le_contravar; lra | lra]).
    split; lra. }
  destruct HAbd as [HAlo HAhi].
  apply Rabs_le_inv in FIN. destruct FIN as [FIN1 FIN2].
  assert (HAs : / 9223372036854775808 * A <= / 9223372036854775808 * 711) by (apply Rmult_le_compat_l; lra).
  assert (HAs0 : 0 <= / 9223372036854775808 * A) by (apply Rmult_le_pos; lra).
  split; [ | split; [ | rewrite Hb63; apply Rabs_le; split; lra]].
  - rewrite Dwy. apply rndF_ge_bpow; [lia | ]. assert (bpow radix2 (-8) = / 256) by (bpow_num; reflexivity). lra.
  - rewrite Dwy. apply rnd_le_pow; [lia | ]. assert (bpow radix2 10 = 1024) by (bpow_num; reflexivity). lra.
Qed.
