(** exp/mod.rs's stage B ([Stages::b_value] and [Stages::b], docs/exp.md,
    sections 6 and 7), transcribed on binary64 and proved:
    - the exactness facts: [A], [T_j]'s leading word with its low 32 bits
      cleared, has 21 significant bits, so [d = th − A] and [A·r_h] are exact
      ([mask_ok], [stage_b_value_ok]), and Fast2Sum is exact for
      [th >= 1 > |A·r_h|];
    - [stage_b_value_ok]: [y + l] is within [209·2^-78 < 2^-70.29] of
      [T_j·e^R], and [|l| <= 2^-20]: formal/exp/stage_b.g's theorem, with its
      hypotheses proved here (the reduction of ExpStageReduction.v,
      formal/exp/stage_b_poly.g, formal/exp/stage_mvt.g, the approximation
      and table bounds of ExpStageTables.v);
    - [exp_stage_b_ok]: for every finite [|x| < 704], when stage B's test
      passes, the returned value is [RN(e^x)] ([E_B = 2^-70 >= 209·2^-78 + 2^-73]). *)

From Coq Require Import ZArith Reals Lia Lra Psatz Classical Bool.
From Flocq Require Import Core Relative IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Mul IEEE64Eft Grid Encodings RoundingConstant.
From Gappa Require Gappa_definitions Gappa_round_def.
From Interval Require Import Tactic.
Require Import TableCheck.
Require ExpReduction ExpStageTables StageGappa ExpStageReduction ExpStageA.
Require exp_stage_b exp_stage_b_poly.
Import ExpStageTables StageGappa ExpStageReduction ExpStageA.

Open Scope R_scope.

(** * The leading 21 bits of [T_j]'s leading word *)

(** [0xffff_ffff_0000_0000]: exp/mod.rs's [HIGH_21]. *)
Definition high21 : Z := 18446744069414584320.

Lemma land_high x : (0 <= x < 2 ^ 64)%Z -> Z.land x high21 = (x / 2 ^ 32 * 2 ^ 32)%Z.
Proof.
  intros H. unfold high21. change 18446744069414584320%Z with (Z.shiftl (Z.ones 32) 32).
  rewrite <- (Z.shiftr_div_pow2 x 32), <- Z.shiftl_mul_pow2 by lia.
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, !Z.shiftl_spec by lia.
  destruct (Z.lt_ge_cases i 32) as [L | G].
  - rewrite (Z.testbit_neg_r (Z.ones 32) (i - 32)) by lia.
    rewrite (Z.testbit_neg_r (Z.shiftr x 32) (i - 32)) by lia. apply andb_false_r.
  - rewrite Z.shiftr_spec by lia. replace (i - 32 + 32)%Z with i by ring.
    destruct (Z.lt_ge_cases i 64) as [L2 | G2].
    + rewrite Z.ones_spec_low by lia. apply andb_true_r.
    + rewrite Z.ones_spec_high by lia. rewrite andb_false_r.
      symmetry. destruct (Z.eq_dec x 0) as [Z0 | N0]; [subst; apply Z.bits_0 | ].
      apply Z.bits_above_log2; [lia | ].
      assert (P : (2 ^ 64 <= 2 ^ i)%Z) by (apply Z.pow_le_mono_r; lia).
      apply Z.log2_lt_pow2; lia.
Qed.

Lemma bits_round_trip hb : (0 <= hb < 2 ^ 64)%Z -> bits_of_b64 (b64_of_bits hb) = hb.
Proof. intros H. apply bits_of_binary_float_of_bits. exact H. Qed.

(** [A = b64_of_bits(th.to_bits() & HIGH_21)] for [th = b64_of_bits hb] in
    [[1, 2)]: a multiple of [2^-20], [th − A] in [[0, 2^-20)], and on
    [2^-52]'s grid. *)
Lemma mask_ok hb f : hb = (1023 * 2 ^ 52 + f)%Z -> (0 <= f < 2 ^ 52)%Z ->
  let a := b64_of_bits (Z.land (bits_of_b64 (b64_of_bits hb)) high21) in
  finite a /\ exists A : Z, B a = IZR A * bpow radix2 (-20) /\ (2 ^ 20 <= A < 2 ^ 21)%Z /\
    B (b64_of_bits hb) - B a = IZR (f mod 2 ^ 32) * bpow radix2 (-52).
Proof.
  intros Hb Hf a.
  assert (R : (0 <= hb < 2 ^ 64)%Z) by (subst; lia).
  unfold a. rewrite bits_round_trip by exact R. rewrite land_high by exact R.
  assert (E : (hb / 2 ^ 32 * 2 ^ 32 = 1023 * 2 ^ 52 + (f - f mod 2 ^ 32))%Z).
  { rewrite Hb. pose proof (Z.div_mod (1023 * 2 ^ 52 + f) (2 ^ 32) ltac:(lia)) as D.
    replace ((1023 * 2 ^ 52 + f) mod 2 ^ 32)%Z with (f mod 2 ^ 32)%Z in D.
    - lia.
    - replace (1023 * 2 ^ 52 + f)%Z with (f + (1023 * 2 ^ 20) * 2 ^ 32)%Z by ring.
      rewrite Z.mod_add by lia. reflexivity. }
  pose proof (Z.mod_pos_bound f (2 ^ 32) ltac:(lia)) as M.
  rewrite E. rewrite <- join_eq.
  destruct (join_val (f - f mod 2 ^ 32) 1023 ltac:(lia) ltac:(lia)) as [Fa Ba].
  rewrite <- join_eq in Hb. rewrite Hb.
  destruct (join_val f 1023 ltac:(lia) ltac:(lia)) as [Fh Bh].
  split; [exact Fa | ].
  pose proof (Z.div_mod f (2 ^ 32) ltac:(lia)) as Df.
  exists ((f / 2 ^ 32) + 2 ^ 20)%Z. split; [ | split].
  - rewrite Ba. replace (f - f mod 2 ^ 32 + 2 ^ 52)%Z with (((f / 2 ^ 32) + 2 ^ 20) * 2 ^ 32)%Z by lia.
    rewrite mult_IZR, (IZR_pow2 32) by lia. change (1023 - 1075)%Z with (-52)%Z.
    rewrite Rmult_assoc, <- bpow_plus. reflexivity.
  - pose proof (Z.div_lt_upper_bound f (2 ^ 32) (2 ^ 20) ltac:(lia) ltac:(lia)).
    pose proof (Z.div_pos f (2 ^ 32) ltac:(lia) ltac:(lia)). lia.
  - rewrite Bh, Ba. change (1023 - 1075)%Z with (-52)%Z. rewrite <- Rmult_minus_distr_r, <- minus_IZR.
    f_equal. f_equal. ring.
Qed.

(** * The certificates *)

(** formal/exp/stage_b_poly.g's theorem. *)
Theorem stage_b_poly_bound (r_ : R) :
  -0.00068 <= rn r_ <= 0.00068 ->
  let r := rn r_ in
  let t4 := rn (d4_g + rn (r * d5_g)) in
  let t3 := rn (d3_g + rn (r * t4)) in
  let h := rn (half_g + rn (r * t3)) in
  let r2 := rn (r * r) in
  let q := rn (r2 * h) in
  Rabs (q - Qs r) <= bpow radix2 (-73) /\ 0 <= q <= bpow radix2 (-22) /\
  Rabs t4 <= 1 /\ Rabs t3 <= 1 /\ Rabs h <= 1 /\ Rabs r2 <= 1.
Proof.
  intros Hr. cbv zeta. unfold Qs, half_g, d3_g, d4_g, d5_g.
  repeat split; try apply Rabs_le; gappa_goal (exp_stage_b_poly.l1 r_).
Qed.

(** formal/exp/stage_b.g's theorem. *)
Theorem stage_b_bound (Th d rh Tl rt q_ Dt dr eq m a : R) :
  Rabs rh <= 0.000678 -> Rabs rt <= bpow radix2 (-40) -> Rabs dr <= bpow radix2 (-93) ->
  0 <= rn q_ <= bpow radix2 (-22) -> Rabs eq <= bpow radix2 (-73) ->
  Rabs a <= IZR 5174524961095286666344419 * bpow radix2 (-158) -> Rabs m <= bpow radix2 (-74) ->
  1 <= Th <= 2 -> Rabs Tl <= bpow radix2 (-53) -> Rabs Dt <= bpow radix2 (-104) ->
  0 <= d <= bpow radix2 (-20) ->
  let ph := (Th - d) * rh in
  let y := rn (Th + ph) in
  let e := Th + ph - y in
  let rhi := rn (rh + rt) in
  let s5 := rn (Tl * rhi) in
  let s3 := rn (d * rh) in
  let q := rn q_ in
  let s1 := rn (rt + q) in
  let s2 := rn (Th * s1) in
  let s4 := rn (s3 + s2) in
  let s6 := rn (s5 + s4) in
  let rest := rn (Tl + s6) in
  let l := rn (e + rest) in
  let expR := one_g + (rh + rt - dr) + (q - eq + m) + a in
  Rabs (y + l - (Th + Tl - Dt) * expR) <= IZR 209 * bpow radix2 (-78) /\
  Rabs l <= bpow radix2 (-20) /\ 1 / 2 <= y <= 4 /\
  Rabs rhi <= 1 /\ Rabs s1 <= 1 /\ Rabs s2 <= 1 /\ Rabs s3 <= 1 /\ Rabs s4 <= 1 /\
  Rabs s5 <= 1 /\ Rabs s6 <= 1 /\ Rabs rest <= 1.
Proof.
  intros Hrh Hrt Hdr Hq Heq Ha Hm HTh HTl HDt Hd. cbv zeta. unfold one_g.
  apply Rabs_le_inv in Hrh. apply Rabs_le_inv in Hrt. apply Rabs_le_inv in Hdr.
  apply Rabs_le_inv in Heq. apply Rabs_le_inv in Ha. apply Rabs_le_inv in Hm.
  apply Rabs_le_inv in HTl. apply Rabs_le_inv in HDt.
  repeat split; try apply Rabs_le; gappa_goal (exp_stage_b.l1 Th d rh Tl rt q_ Dt dr eq m a).
Qed.

(** * The transcription *)

(** [Stages::b_value]. *)
Definition stage_b_at (rh rt : f64) (j : nat) : f64 * f64 :=
  let rhi := fadd rh rt in
  let q := fmul (fmul rhi rhi)
                (fadd c_half (fmul rhi (fadd st_d3 (fmul rhi (fadd st_d4 (fmul rhi st_d5)))))) in
  let th := st_t_hi j in
  let tl := st_t_lo j in
  let a := b64_of_bits (Z.land (bits_of_b64 th) high21) in
  let rest := fadd tl (fadd (fmul tl rhi) (fadd (fmul (fsub th a) rh) (fmul th (fadd rt q)))) in
  let '(y, e) := fast_two_sum64 th (fmul a rh) in
  (y, fadd e rest).

Definition stage_b_value (n r1 : f64) (j : nat) : f64 * f64 :=
  let p2 := fmul n st_l2 in
  let rh := fsub (fadd (fsub r1 p2) c_split) c_split in
  let rt := fsub (fsub (fsub r1 rh) p2) (fmul n st_l3) in
  stage_b_at rh rt j.

Lemma mul1 u v U V : Rabs u <= U -> Rabs v <= V -> Rabs (u * v) <= U * V.
Proof. intros Hu Hv. rewrite Rabs_mult. apply Rmult_le_compat; try apply Rabs_pos; assumption. Qed.

Lemma add1 u v U V : Rabs u <= U -> Rabs v <= V -> Rabs (u + v) <= U + V.
Proof. intros Hu Hv. apply Rle_trans with (1 := Rabs_triang u v). lra. Qed.

Theorem stage_b_at_ok rh rt j R : finite rh -> finite rt -> on_grid (-40) (B rh) ->
  Rabs (B rh) <= 0.000678 -> Rabs (B rt) <= bpow radix2 (-40) ->
  Rabs (B rh + B rt - R) <= bpow radix2 (-93) -> Rabs R <= 0.000677 -> (j < 512)%nat ->
  let '(y,l) := stage_b_at rh rt j in
  finite y /\ finite l /\ Rabs (B y) <= 4 /\ Rabs (B l) <= bpow radix2 (-20) /\
  Rabs (exp (INR j * ln 2 / 512) * exp R - (B y + B l)) <= IZR 209 * bpow radix2 (-78).
Proof.
  intros Frh Frt Grh Hrh Hrt Hdr HR Hj.
  unfold stage_b_at. cbv zeta.
  set (dr := B rh + B rt - R) in *.
  pose proof (bpow_le1 (-40) ltac:(lia)) as P41.
  (* r_hi *)
  destruct (fadd16 rh rt Frh Frt) as [Frhi Brhi].
  { apply Rle_trans with (0.000678 + 1); [apply add1; lra | lra]. }
  rewrite rndF_rn in Brhi.
  set (rhi := fadd rh rt) in *.
  assert (Ehi : Rabs (B rhi - (B rh + B rt)) <= bpow radix2 (-64)).
  { rewrite Brhi. apply (rnd_err_below _ (-10)); [lia | ].
    change (bpow radix2 (-10)) with (/ 1024). change (bpow radix2 (-40)) with (/ 1099511627776) in Hrt.
    apply Rle_trans with (0.000678 + / 1099511627776); [apply add1; lra | lra]. }
  assert (Hrhi : Rabs (B rhi) <= 0.00068).
  { change (bpow radix2 (-64)) with (/ 18446744073709551616) in Ehi.
    change (bpow radix2 (-40)) with (/ 1099511627776) in Hrt.
    apply Rabs_le_inv in Ehi. apply Rabs_le_inv in Hrh. apply Rabs_le_inv in Hrt. apply Rabs_le. lra. }
  assert (RN_rhi : rn (B rhi) = B rhi) by (apply round_generic; [apply valid_rnd_N | apply B_fmt]).
  (* the polynomial *)
  assert (Hrhi' : -0.00068 <= rn (B rhi) <= 0.00068)
    by (rewrite RN_rhi; pose proof (Rabs_le_inv _ _ Hrhi); lra).
  pose proof (stage_b_poly_bound (B rhi) Hrhi') as PB.
  cbv zeta in PB. rewrite RN_rhi in PB.
  destruct PB as [Peq [Pq [Pt4 [Pt3 [Ph Pr2]]]]].
  assert (C5 : Rabs d5_g <= 1) by (rewrite <- d5_g_eq, st_d5_val; interval with (i_prec 64)).
  assert (C4 : Rabs d4_g <= 1) by (rewrite <- d4_g_eq, st_d4_val; interval with (i_prec 64)).
  assert (C3 : Rabs d3_g <= 1) by (rewrite <- d3_g_eq, st_d3_val; interval with (i_prec 64)).
  assert (Ch : Rabs half_g <= 1) by (rewrite half_g_eq, Rabs_pos_eq; lra).
  assert (Rh1 : Rabs (B rhi) <= 1) by lra.
  destruct (fmul16 rhi st_d5 Frhi st_d5_finite) as [F1 B1].
  { rewrite d5_g_eq. apply Rle_trans with (1 * 1); [apply mul1; assumption | lra]. }
  rewrite d5_g_eq, rndF_rn in B1.
  assert (A1 : Rabs (B (fmul rhi st_d5)) <= 1)
    by (rewrite B1; apply rnd_le1; apply Rle_trans with (1 * 1); [apply mul1; assumption | lra]).
  destruct (fadd16 st_d4 _ st_d4_finite F1) as [F2 B2].
  { rewrite d4_g_eq. apply Rle_trans with (1 + 1); [apply add1; assumption | lra]. }
  rewrite d4_g_eq, B1, rndF_rn in B2.
  destruct (fmul16 rhi _ Frhi F2) as [F3 B3].
  { rewrite B2. apply Rle_trans with (1 * 1); [apply mul1; assumption | lra]. }
  rewrite B2, rndF_rn in B3.
  assert (A3 : Rabs (B (fmul rhi (fadd st_d4 (fmul rhi st_d5)))) <= 1)
    by (rewrite B3; apply rnd_le1; apply Rle_trans with (1 * 1); [apply mul1; assumption | lra]).
  destruct (fadd16 st_d3 _ st_d3_finite F3) as [F4 B4].
  { rewrite d3_g_eq. apply Rle_trans with (1 + 1); [apply add1; assumption | lra]. }
  rewrite d3_g_eq, B3, rndF_rn in B4.
  destruct (fmul16 rhi _ Frhi F4) as [F5 B5].
  { rewrite B4. apply Rle_trans with (1 * 1); [apply mul1; assumption | lra]. }
  rewrite B4, rndF_rn in B5.
  assert (A5 : Rabs (B (fmul rhi (fadd st_d3 (fmul rhi (fadd st_d4 (fmul rhi st_d5)))))) <= 1)
    by (rewrite B5; apply rnd_le1; apply Rle_trans with (1 * 1); [apply mul1; assumption | lra]).
  destruct (fadd16 c_half _ c_half_finite F5) as [F6 B6].
  { rewrite c_half_g. apply Rle_trans with (1 + 1); [apply add1; assumption | lra]. }
  rewrite c_half_g, B5, rndF_rn in B6.
  destruct (fmul16 rhi rhi Frhi Frhi) as [F7 B7].
  { apply Rle_trans with (1 * 1); [apply mul1; assumption | lra]. }
  rewrite rndF_rn in B7.
  destruct (fmul16 (fmul rhi rhi) _ F7 F6) as [F8 B8].
  { rewrite B7, B6. apply Rle_trans with (1 * 1); [apply mul1; assumption | lra]. }
  rewrite B7, B6, rndF_rn in B8.
  set (q := fmul (fmul rhi rhi) (fadd c_half (fmul rhi (fadd st_d3 (fmul rhi (fadd st_d4 (fmul rhi st_d5))))))) in *.
  rewrite <- B8 in Peq, Pq.
  assert (RN_q : rn (B q) = B q) by (apply round_generic; [apply valid_rnd_N | apply B_fmt]).
  (* the table entry and its leading 21 bits *)
  destruct (st_t_ok j Hj) as [Fth [Ftl [Rhb [[f [Hf Hf']] [_ [Th12 [Ttl Ttab]]]]]]].
  fold (st_t_hi j) in Fth, Th12, Ttab. fold (st_t_lo j) in Ftl, Ttl, Ttab.
  pose proof (mask_ok _ f Hf Hf') as MK. cbv zeta in MK.
  fold (st_t_hi j) in MK.
  set (th := st_t_hi j) in *. set (tl := st_t_lo j) in *.
  set (a := b64_of_bits (Z.land (bits_of_b64 th) high21)) in *.
  destruct MK as [Fa [A [Ba [HA Dth]]]].
  pose proof (Z.mod_pos_bound f (2 ^ 32) ltac:(lia)) as Fm.
  (* d = th − a, exact *)
  destruct (fsub16 th a Fth Fa) as [Fd Bd'].
  { rewrite Dth, Rabs_mult, (Rabs_pos_eq (bpow radix2 (-52))) by apply bpow_ge_0.
    rewrite <- abs_IZR. change (bpow radix2 (-52)) with (/ 4503599627370496).
    assert (IZR (Z.abs (f mod 2 ^ 32)) <= 4294967296) by (apply IZR_le; change (2 ^ 32)%Z with 4294967296%Z in *; lia).
    lra. }
  assert (Bd : B (fsub th a) = B th - B a).
  { rewrite Bd'. apply round_generic; auto with typeclass_instances. rewrite Dth.
    apply ExpReduction.fmt_int; [ | lia]. change (2 ^ 32)%Z with 4294967296%Z in *.
    change (2 ^ 53)%Z with 9007199254740992%Z. lia. }
  set (d := B th - B a) in *.
  assert (Hd : 0 <= d <= bpow radix2 (-20)).
  { rewrite Dth. change (bpow radix2 (-52)) with (/ 4503599627370496).
    change (bpow radix2 (-20)) with (/ 1048576).
    assert (0 <= IZR (f mod 2 ^ 32) <= 4294967296) by (split; apply IZR_le; change (2 ^ 32)%Z with 4294967296%Z in *; lia).
    split; lra. }
  (* A·r_h, exact *)
  destruct Grh as [K HK].
  assert (Kb : (Z.abs K <= 745500000)%Z).
  { assert (Rabs (IZR K) <= 745500000).
    { apply Rmult_le_reg_r with (bpow radix2 (-40)); [apply bpow_gt_0 | ].
      rewrite <- (Rabs_pos_eq (bpow radix2 (-40))) at 1 by apply bpow_ge_0. rewrite <- Rabs_mult, <- HK.
      change (bpow radix2 (-40)) with (/ 1099511627776). lra. }
    rewrite <- abs_IZR in H. apply le_IZR in H. exact H. }
  assert (PH : B a * B rh = IZR (A * K) * bpow radix2 (-60)).
  { rewrite Ba, HK, mult_IZR. change (-60)%Z with (-20 + -40)%Z. rewrite bpow_plus. ring. }
  assert (PHb : Rabs (B a * B rh) <= 1).
  { rewrite PH, Rabs_mult, (Rabs_pos_eq (bpow radix2 (-60))) by apply bpow_ge_0. rewrite <- abs_IZR.
    change (bpow radix2 (-60)) with (/ 1152921504606846976).
    assert (IZR (Z.abs (A * K)) <= 1563426816000000) by (apply IZR_le; rewrite Z.abs_mul; change (2 ^ 21)%Z with 2097152%Z in *; nia).
    lra. }
  destruct (fmul16 a rh Fa Frh ltac:(lra)) as [Fph Bph'].
  assert (Bph : B (fmul a rh) = (B th - d) * B rh).
  { rewrite Bph'. unfold d. replace (B th - (B th - B a)) with (B a) by ring.
    apply round_generic; auto with typeclass_instances. rewrite PH.
    apply ExpReduction.fmt_int; [ | lia]. rewrite Z.abs_mul. change (2 ^ 21)%Z with 2097152%Z in HA.
    change (2 ^ 53)%Z with 9007199254740992%Z. nia. }
  (* Fast2Sum *)
  assert (W1 : Rabs (B th) <= bpow radix2 1021).
  { rewrite Rabs_pos_eq by lra. apply Rle_trans with (bpow radix2 1); [change (bpow radix2 1) with 2; lra | apply bpow_le; lia]. }
  assert (W2 : Rabs (B (fmul a rh)) <= bpow radix2 1021).
  { rewrite Bph'. apply Rle_trans with 1; [apply rnd_le1; lra | change 1 with (bpow radix2 0); apply bpow_le; lia]. }
  assert (W3 : Rabs (B (fmul a rh)) <= Rabs (B th)).
  { rewrite Bph', (Rabs_pos_eq (B th)) by lra. apply Rle_trans with 1; [apply rnd_le1; lra | lra]. }
  pose proof (fast_two_sum_ieee th (fmul a rh) Fth Fph W1 W2 (or_intror (or_introl W3))) as FS.
  revert FS. generalize (fast_two_sum64 th (fmul a rh)). intros [y e] FS.
  destruct FS as [Fy [Fe [By Bye]]].
  rewrite rndF_rn, Bph in By.
  assert (Be : B e = B th + (B th - d) * B rh - B y) by (rewrite <- Bph; lra).
  (* the certificate *)
  set (eqv := B q - Qs (B rhi)).
  assert (Heq : Rabs eqv <= bpow radix2 (-73)) by exact Peq.
  set (m := Qs R - Qs (B rhi)).
  assert (Hm : Rabs m <= bpow radix2 (-74)).
  { unfold m. replace R with (B rhi + (R - B rhi)) at 1 by ring. apply stage_mvt_bound; [exact Hrhi | ].
    change (bpow radix2 (-64)) with (/ 18446744073709551616) in Ehi.
    change (bpow radix2 (-93)) with (/ 9903520314283042199192993792) in Hdr.
    change (bpow radix2 (-72)) with (/ 4722366482869645213696).
    apply Rabs_le_inv in Ehi. apply Rabs_le_inv in Hdr. apply Rabs_le. unfold dr in *. lra. }
  set (av := exp R - 1 - R - Qs R).
  assert (Ha : Rabs av <= IZR 5174524961095286666344419 * bpow radix2 (-158)).
  { pose proof (st_poly_approx R HR) as AP. unfold st_poly_bound, Rdiv in AP.
    rewrite <- (bpow_m 158) in AP. rewrite d3_g_eq, d4_g_eq, d5_g_eq in AP.
    unfold av, Qs. rewrite half_g_eq. replace (/ 2) with (1 / 2) by field. exact AP. }
  set (T := exp (INR j * ln 2 / 512)) in *.
  set (Dt := B th + B tl - T).
  assert (HDt : Rabs Dt <= bpow radix2 (-104)) by exact Ttab.
  assert (HTl : Rabs (B tl) <= bpow radix2 (-53))
    by (change (-53)%Z with (- Z.of_nat 53)%Z; rewrite bpow_m; exact Ttl).
  assert (Hq' : 0 <= rn (B q) <= bpow radix2 (-22)) by (rewrite RN_q; exact Pq).
  pose proof (stage_b_bound (B th) d (B rh) (B tl) (B rt) (B q) Dt dr eqv m av
                Hrh Hrt Hdr Hq' Heq Ha Hm ltac:(lra) HTl HDt Hd) as G.
  cbv zeta in G. rewrite RN_q in G. rewrite <- By, <- Brhi, <- Be in G.
  destruct G as [GY [Gl [Gy [Grhi [Gs1 [Gs2 [Gs3 [Gs4 [Gs5 [Gs6 Grest]]]]]]]]]].
  (* the rest of the transcription computes the certificate's chain *)
  pose proof (bpow_le1 (-53) ltac:(lia)) as P53.
  assert (Hd1 : Rabs d <= 1) by (pose proof (bpow_le1 (-20) ltac:(lia)); rewrite Rabs_pos_eq; lra).
  destruct (fmul16 tl rhi Ftl Frhi) as [Fs5 Bs5].
  { apply Rle_trans with (1 * 1); [apply mul1; lra | lra]. }
  rewrite rndF_rn in Bs5.
  destruct (fmul16 (fsub th a) rh Fd Frh) as [Fs3 Bs3].
  { rewrite Bd. apply Rle_trans with (1 * 1); [apply mul1; lra | lra]. }
  rewrite Bd, rndF_rn in Bs3.
  assert (Hq1 : Rabs (B q) <= 1) by (pose proof (bpow_le1 (-22) ltac:(lia)); rewrite Rabs_pos_eq; lra).
  destruct (fadd16 rt q Frt F8) as [Fs1 Bs1].
  { apply Rle_trans with (1 + 1); [apply add1; lra | lra]. }
  rewrite rndF_rn in Bs1.
  destruct (fmul16 th (fadd rt q) Fth Fs1) as [Fs2 Bs2].
  { rewrite Bs1. apply Rle_trans with (2 * 1); [apply mul1; [rewrite Rabs_pos_eq; lra | lra] | lra]. }
  rewrite Bs1, rndF_rn in Bs2.
  destruct (fadd16 (fmul (fsub th a) rh) (fmul th (fadd rt q)) Fs3 Fs2) as [Fs4 Bs4].
  { rewrite Bs3, Bs2. apply Rle_trans with (1 + 1); [apply add1; lra | lra]. }
  rewrite Bs3, Bs2, rndF_rn in Bs4.
  destruct (fadd16 (fmul tl rhi) _ Fs5 Fs4) as [Fs6 Bs6].
  { rewrite Bs5, Bs4. apply Rle_trans with (1 + 1); [apply add1; lra | lra]. }
  rewrite Bs5, Bs4, rndF_rn in Bs6.
  destruct (fadd16 tl _ Ftl Fs6) as [Frest Brest].
  { rewrite Bs6. apply Rle_trans with (1 + 1); [apply add1; lra | lra]. }
  rewrite Bs6, rndF_rn in Brest.
  pose proof (bpow_le1 (-20) ltac:(lia)) as P20.
  assert (He1 : Rabs (B e) <= 1).
  { rewrite Be, By. set (w := B th + (B th - d) * B rh).
    assert (Hw : Rabs w <= bpow radix2 2).
    { change (bpow radix2 2) with 4. unfold w.
      apply Rle_trans with (2 + 2 * 1); [apply add1; [rewrite Rabs_pos_eq; lra | apply mul1; [rewrite Rabs_pos_eq; lra | lra]] | lra]. }
    pose proof (rnd_err_below w 2 ltac:(lia) Hw) as RE. rewrite rndF_rn in RE.
    rewrite <- Rabs_Ropp, Ropp_minus_distr. apply Rle_trans with (1 := RE). apply bpow_le1. lia. }
  destruct (fadd16 e _ Fe Frest) as [Fl Bl].
  { rewrite Brest. apply Rle_trans with (1 + 1); [apply add1; lra | lra]. }
  rewrite Brest, rndF_rn in Bl.
  split; [exact Fy | split; [exact Fl | split; [rewrite Rabs_pos_eq; lra | split]]].
  - rewrite Bl. exact Gl.
  - rewrite Bl.
    assert (ER : one_g + (B rh + B rt - dr) + (B q - eqv + m) + av = exp R)
      by (rewrite one_g_eq; unfold dr, eqv, m, av; ring).
    rewrite ER in GY. replace (B th + B tl - Dt) with T in GY by (unfold Dt; ring).
    rewrite Rabs_minus_sym. exact GY.
Qed.

Theorem stage_b_value_ok x n r1 (ni : Z) (j : nat) :
  finite x -> finite n -> B n = IZR ni -> (Z.abs ni <= 520018)%Z -> finite r1 ->
  B r1 = B x - IZR ni * B st_l1 -> Rabs (B x - IZR ni * L) <= 0.000677 ->
  Rabs (B r1) < bpow radix2 (-10) ->
  (ni <> 0%Z -> on_grid (-63) (B r1)) -> (ni = 0%Z -> B r1 = B x) -> (j < 512)%nat ->
  let '(y, l) := stage_b_value n r1 j in
  finite y /\ finite l /\ Rabs (B y) <= 4 /\ Rabs (B l) <= bpow radix2 (-20) /\
  Rabs (exp (INR j * ln 2 / 512) * exp (B x - IZR ni * L) - (B y + B l)) <= IZR 209 * bpow radix2 (-78).
Proof.
  intros Fx Fn Bn Hn Fr1 Br1 HR Hr1 G1 Z1 Hj.
  pose proof (stage_b_r_ok x n r1 ni Fx Fn Bn Hn Fr1 Br1 HR Hr1 G1 Z1) as RB. cbv zeta in RB.
  unfold stage_b_value. cbv zeta.
  destruct RB as [Frh [Frt [Grh [Hrh [Hrt Hdr]]]]].
  apply stage_b_at_ok; assumption.
Qed.

(** exp/mod.rs's [E_B], [2^-70]. *)
Definition c_eb : f64 := b64_of_bits 4291930444884082688.   (* 0x3b90000000000000 *)
Lemma c_eb_val : B c_eb = bpow radix2 (-70).
Proof.
  unfold c_eb. rewrite (bits_val 4291930444884082688 false 4503599627370496 122 eq_refl).
  unfold Rdiv. rewrite <- (bpow_m 122). change (-70)%Z with (52 + - Z.of_nat 122)%Z. rewrite bpow_plus.
  change (bpow radix2 52) with (IZR 4503599627370496). reflexivity.
Qed.
Lemma c_eb_finite : finite c_eb.
Proof. exact (bits_finite 4291930444884082688 _ _ _ eq_refl). Qed.

(** [Stages::b]: stage B's value, tested and scaled. *)
Definition stage_b (x : f64) : option f64 :=
  let '(n, j, k, r1) := stage_of x in
  let '(y, l) := stage_b_value n r1 (Z.to_nat j) in
  decide_const y l c_eb k.

(** Stage B end to end: for every finite [|x| < 704], when the test passes,
    the returned value is [RN(e^x)]. *)
Theorem exp_stage_b_ok x v : finite x -> Rabs (B x) < 704 -> stage_b x = Some v ->
  finite v /\ B v = rndF (exp (B x)).
Proof.
  intros Fx Hx. pose proof (stage_of_ok x Fx Hx) as SO. unfold stage_b.
  (* Generalizing, rather than destructing, keeps the kernel from unfolding
     the transcription when it rechecks the proof. *)
  revert SO. generalize (stage_of x). intros [[[n j] k] r1] SO Hd.
  destruct SO as [ni [Bn [Fn [Hn [Hjk [Hj [Hk [Fr1 [Br1 [HR [Hr1 [G1 Z1]]]]]]]]]]]].
  assert (Jn : (Z.to_nat j < 512)%nat) by lia.
  pose proof (stage_b_value_ok x n r1 ni (Z.to_nat j) Fx Fn Bn Hn Fr1 Br1 HR Hr1 G1 Z1 Jn) as SV.
  revert SV Hd. generalize (stage_b_value n r1 (Z.to_nat j)). intros [y l] SV Hd.
  destruct SV as [Fy [Fl [Hy [Hl HZ]]]].
  set (R := B x - IZR ni * L) in *.
  set (Zr := exp (INR (Z.to_nat j) * ln 2 / 512) * exp R) in *.
  assert (Ex : exp (B x) = Zr * bpow radix2 k).
  { unfold Zr. rewrite <- exp_split. f_equal. rewrite Z2Nat.id by lia. unfold R. rewrite Hjk. ring. }
  rewrite Ex.
  pose proof c_eb_val as Ev.
  apply (decide_const_ok y l c_eb k Zr (IZR 209 * bpow radix2 (-78)) (-19) v Fy Fl c_eb_finite Hy
           ltac:(lia)); try assumption; try lia.
  - rewrite Ev. apply bpow_ge_0.
  - rewrite Ev. bpow_num_all. lra.
  - rewrite Ev. change (-19 - 54)%Z with (-73)%Z. bpow_num_all. lra.
  - apply z_range; assumption.
Qed.

(** * The screen and the stages together *)

(** exp/mod.rs's screen, [x.to_bits() & MAGNITUDE < STAGES]: [|x| < 704]. *)
Definition screen (x : f64) : bool :=
  (Z.land (bits_of_b64 x) 9223372036854775807 <? 4649403665306615808)%Z.

Theorem screen_ok x : screen x = true -> finite x /\ Rabs (B x) < 704.
Proof.
  unfold screen. intros H. apply Z.ltb_lt in H.
  pose proof (bits_of_binary_float_range 52 11 eq_refl eq_refl x) as Rg.
  rewrite <- (binary_float_of_bits_of_binary_float 52 11 eq_refl eq_refl eq_refl x).
  change (bits_of_binary_float 52 11 x) with (bits_of_b64 x) in *.
  generalize (bits_of_b64 x) Rg H. clear. intros b Rg H.
  change (2 ^ (52 + 11 + 1))%Z with (2 ^ 64)%Z in Rg.
  change 9223372036854775807%Z with (Z.ones 63) in H. rewrite Z.land_ones in H by lia.
  change (2 ^ 63)%Z with (2 ^ 52 * 2 ^ 11)%Z in H. rewrite Z.rem_mul_r in H by lia.
  assert (Mr : (0 <= b mod 2 ^ 52 < 2 ^ 52)%Z) by (apply Z.mod_pos_bound; lia).
  assert (Er : (0 <= (b / 2 ^ 52) mod 2 ^ 11 < 2 ^ 11)%Z) by (apply Z.mod_pos_bound; lia).
  unfold binary_float_of_bits. rewrite is_finite_FF2B, B2R_FF2B.
  unfold binary_float_of_bits_aux, split_bits. cbv zeta.
  change (Zpower 2 52) with (2 ^ 52)%Z. change (Zpower 2 11) with (2 ^ 11)%Z.
  generalize (Zle_bool (2 ^ 52 * 2 ^ 11) b). intros s.
  remember (b mod 2 ^ 52)%Z as M. remember ((b / 2 ^ 52) mod 2 ^ 11)%Z as E.
  clear HeqM HeqE Rg.
  assert (E1 : (E <= 1032)%Z) by lia.
  assert (E2 : E = 1032%Z -> (M < 1688849860263936)%Z) by lia.
  destruct (Zeq_bool E 0) eqn:Z0.
  - destruct M as [ | pm | pm]; [ | | lia].
    + split; [reflexivity | simpl; rewrite Rabs_R0; lra].
    + split; [reflexivity | ]. simpl FF2R. unfold F2R. cbn [Fnum Fexp].
      rewrite Rabs_mult, Rabs_Zabs, (Rabs_pos_eq (bpow radix2 _)) by apply bpow_ge_0.
      assert (P : IZR (Z.abs (cond_Zopp s (Zpos pm))) <= IZR (2 ^ 52)) by (apply IZR_le; destruct s; simpl; lia).
      apply Rle_lt_trans with (IZR (2 ^ 52) * bpow radix2 (3 - 2 ^ (11 - 1) - (52 + 1))).
      * apply Rmult_le_compat_r; [apply bpow_ge_0 | exact P].
      * change (IZR (2 ^ 52)) with (bpow radix2 52). rewrite <- bpow_plus.
        apply Rlt_trans with 1; [ | lra]. change 1 with (bpow radix2 0). apply bpow_lt. lia.
  - assert (N2047 : Zeq_bool E (2 ^ 11 - 1) = false) by (apply Zeq_bool_false; lia).
    rewrite N2047.
    destruct (M + 2 ^ 52)%Z as [ | px | px] eqn:HP; [lia | | lia].
    split; [reflexivity | ]. simpl FF2R. unfold F2R. cbn [Fnum Fexp].
    rewrite Rabs_mult, Rabs_Zabs, (Rabs_pos_eq (bpow radix2 _)) by apply bpow_ge_0.
    replace (Z.abs (cond_Zopp s (Zpos px))) with (Zpos px) by (destruct s; reflexivity).
    replace (E + -1074 - 1)%Z with (E - 1075)%Z by ring.
    destruct (Z.eq_dec E 1032) as [E32 | E31].
    + subst E. specialize (E2 eq_refl).
      assert (P : IZR (Zpos px) < IZR 6192449487634432) by (apply IZR_lt; lia).
      change (1032 - 1075)%Z with (-43)%Z. change (bpow radix2 (-43)) with (/ 8796093022208).
      lra.
    + assert (P : IZR (Zpos px) < bpow radix2 53) by (change (bpow radix2 53) with (IZR (2 ^ 53)); apply IZR_lt; lia).
      apply Rlt_le_trans with (bpow radix2 53 * bpow radix2 (E - 1075)).
      * apply Rmult_lt_compat_r; [apply bpow_gt_0 | exact P].
      * rewrite <- bpow_plus. apply Rle_trans with (bpow radix2 9); [apply bpow_le; lia | ].
        change (bpow radix2 9) with 512. lra.
Qed.

(** [exp]'s stages, as exp/mod.rs runs them: the screen, then stage A, then
    stage B; [None] where [exp] falls back. *)
Definition exp_stages (x : f64) : option f64 :=
  if screen x then
    match stage_a x with
    | Some v => Some v
    | None => stage_b x
    end
  else None.

(** The stages end to end: whatever they return is [RN(e^x)]. *)
Theorem exp_stages_ok x v : exp_stages x = Some v -> finite v /\ B v = rndF (exp (B x)).
Proof.
  unfold exp_stages. destruct (screen x) eqn:S; [ | discriminate].
  destruct (screen_ok x S) as [Fx Hx].
  destruct (stage_a x) as [va | ] eqn:A.
  - intros Hv. injection Hv as <-. exact (exp_stage_a_ok x va Fx Hx A).
  - intros Hv. exact (exp_stage_b_ok x v Fx Hx Hv).
Qed.
