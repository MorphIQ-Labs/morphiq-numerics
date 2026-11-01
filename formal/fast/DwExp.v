(** The double-word exponential [DoubleWord::exp_split]
    (crates/morphiq-numerics/src/double_word/exp.rs): its binary64 transcription
    and the published bound, relative [16u^2], [u = 2^-53]. Derivation in
    docs/double-word.md#exponential. *)
From Coq Require Import Reals ZArith Lia Lra Psatz List.
From Flocq Require Import Core Relative IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add Binary64Mul IEEE64 IEEE64Add IEEE64Mul IEEE64Eft
  Grid Encodings RoundingGaps RoundingCore RoundingTest.
From Double Require Import DWPlus.
From Interval Require Import Tactic.
Require Import TableCheck FastExpTables DwExpConstants.
Open Scope R_scope.

(** * Transcription *)

Definition dwx_zero : f64 := B754_zero 53 1024 false.

(** [x < y] for binary64 [x], [y]; false when either is a NaN. *)
Definition dwx_lt (x y : f64) : bool :=
  match Bcompare 53 1024 x y with Some Lt => true | _ => false end.

(** [t = RN(RN(hi·INV) + S)], [n = RN(t - S)] and the integer [n] from the
    encodings, as Rust's [n as i64]. *)
Definition dwexp_index (xh : f64) : f64 * Z :=
  let t := fadd (fmul xh fx_inv) dwx_shifter in
  (fsub t dwx_shifter, (bits_of_b64 t - bits_of_b64 dwx_shifter)%Z).

Definition dwexp_reduce (xh xl n : f64) : f64 * f64 :=
  let '(qh, ql) := two_prod64 n dwx_l3 in
  let '(ah, al) := add_f64_64 xh xl (fneg (fmul n fx_l1)) in
  let '(bh, bl) := add_f64_64 ah al (fneg (fmul n dwx_l2)) in
  let '(ch, cl) := add_f64_64 bh bl (fneg ql) in
  add_f64_64 ch cl (fneg qh).

Definition dwx_c_hi (k : nat) : f64 :=
  match k with
  | 0 => dwx_c0_hi | 1 => dwx_c1_hi | 2 => dwx_c2_hi | 3 => dwx_c3_hi
  | 4 => dwx_c4_hi | 5 => dwx_c5_hi | 6 => dwx_c6_hi | _ => dwx_c7_hi
  end.
Definition dwx_c_lo (k : nat) : f64 :=
  match k with
  | 0 => dwx_c0_lo | 1 => dwx_c1_lo | 2 => dwx_c2_lo | 3 => dwx_c3_lo
  | 4 => dwx_c4_lo | 5 => dwx_c5_lo | 6 => dwx_c6_lo | _ => dwx_c7_lo
  end.

(** One Horner step [v <- ((v ⊗ r) ⊕ c_lo) ⊕ c_hi], the low-word addition only
    for [k >= 3], and the trailing-word floor. *)
Definition dwexp_step (k : nat) (rh rl : f64) (v : f64 * f64) : f64 * f64 :=
  let '(vh, vl) := v in
  let '(mh, ml) := mul64 vh vl rh rl in
  let '(sh, sl) := if (3 <=? k)%nat then add_f64_64 mh ml (dwx_c_lo k) else (mh, ml) in
  let '(wh, wl) := add_f64_64 sh sl (dwx_c_hi k) in
  if dwx_lt (b64_abs wl) dwx_v_floor then (wh, dwx_zero) else (wh, wl).

Definition dwexp_horner (rh rl : f64) : f64 * f64 :=
  dwexp_step 0 rh rl (dwexp_step 1 rh rl (dwexp_step 2 rh rl (dwexp_step 3 rh rl
    (dwexp_step 4 rh rl (dwexp_step 5 rh rl (dwexp_step 6 rh rl (dwx_c7_hi, dwx_c7_lo))))))).

Definition dwexp64 (xh xl : f64) : option (f64 * f64 * Z) :=
  if dwx_lt (b64_abs xh) dwx_limit then
    if dwx_lt (b64_abs xh) dwx_tiny then
      let '(zh, zl) := add_f64_64 xh xl dwx_c0_hi in Some (zh, zl, 0%Z)
    else
      let '(n, ni) := dwexp_index xh in
      let j := Z.to_nat (Z.land ni 1023) in
      let k := Z.shiftr ni 10 in
      let '(rh, rl) := dwexp_reduce xh xl n in
      if dwx_lt (b64_abs rh) dwx_r_floor then Some (fx_t_hi j, fx_t_lo j, k)
      else
        let rl' := if dwx_lt (b64_abs rl) dwx_low_floor then dwx_zero else rl in
        let '(vh, vl) := dwexp_horner rh rl' in
        let '(zh, zl) := mul64 (fx_t_hi j) (fx_t_lo j) vh vl in
        Some (zh, zl, k)
  else None.

(** * Small facts *)

Lemma dwx_lt_true x y : finite x -> finite y -> (dwx_lt x y = true <-> B x < B y).
Proof.
  intros Fx Fy; unfold dwx_lt; rewrite Bcompare_correct by assumption.
  destruct (Rcompare_spec (B x) (B y)); split; intros; try discriminate; try reflexivity; lra.
Qed.

Lemma dwx_lt_false x y : finite x -> finite y -> (dwx_lt x y = false <-> B y <= B x).
Proof.
  intros Fx Fy; unfold dwx_lt; rewrite Bcompare_correct by assumption.
  destruct (Rcompare_spec (B x) (B y)); split; intros; try discriminate; try reflexivity; lra.
Qed.

Lemma dwx_abs_finite x : finite x -> finite (b64_abs x).
Proof. intros Fx; unfold b64_abs; rewrite is_finite_Babs; exact Fx. Qed.

Lemma dwx_fneg x : B (fneg x) = - B x.
Proof. apply B2R_Bopp. Qed.

Lemma dwx_fneg_finite x : finite x -> finite (fneg x).
Proof. intros Fx; unfold fneg, b64_opp; now rewrite is_finite_Bopp. Qed.

(** DWPlusFP returns an exact zero for an exact zero sum. *)
Lemma add_f64_zero xh xl y : fmtF xh -> fmtF xl -> fmtF y -> xh + xl + y = 0 ->
  let '(zh, zl) := add_f64 xh xl y in zh = 0 /\ zl = 0.
Proof.
  intros Fh Fl Fy S0. unfold add_f64.
  rewrite (two_sum_eq _ _ Fh Fy).
  pose proof (@TwoSum_correct prec (ltac:(unfold prec; lia)) ne eq_refl xh y
                (fmtF_fmtX _ Fh) (fmtF_fmtX _ Fy)) as E.
  set (sh := TwoSum_sum prec ne xh y) in *. set (sl := TwoSum_err prec ne xh y) in *.
  assert (Fs : fmtF sh).
  { unfold sh, TwoSum_sum, TwoSum; simpl. rewrite <- sum_round by assumption. apply fmtF_rnd. }
  assert (V : rndF (xl + sl) = - sh).
  { replace (xl + sl) with (- sh) by lra. apply round_generic; [exact _ | ]. now apply generic_format_opp. }
  unfold fast_two_sum. rewrite V.
  replace (sh + - sh) with 0 by ring. rewrite round_0 by exact _.
  replace (0 - sh) with (- sh) by ring.
  rewrite (round_generic _ _ _ (- sh)) by (exact _ || now apply generic_format_opp).
  replace (- sh - - sh) with 0 by ring. rewrite round_0 by exact _.
  split; reflexivity.
Qed.

(** The relative bound in multiplied-out form, for every sum including zero. *)
Lemma add_f64_abs xh xl y : fmtF xh -> fmtF xl -> fmtF y -> xh = rndF (xh + xl) ->
  let '(zh, zl) := add_f64 xh xl y in
  Rabs (zh + zl - (xh + xl + y)) <= 2 * bpow radix2 (- prec) ^ 2 * Rabs (xh + xl + y).
Proof.
  intros Fh Fl Fy E.
  destruct (Req_dec (xh + xl + y) 0) as [S0 | S0].
  - pose proof (add_f64_zero xh xl y Fh Fl Fy S0) as Z0.
    destruct (add_f64 xh xl y) as [zh zl]. destruct Z0 as [-> ->].
    rewrite S0. rewrite Rminus_0_r, Rplus_0_r, Rabs_R0. lra.
  - pose proof (add_f64_bound xh xl y Fh Fl Fy E) as Bd.
    destruct (add_f64 xh xl y) as [zh zl].
    unfold Rdiv in Bd. rewrite Rabs_mult, Rabs_Rinv in Bd by exact S0.
    pose proof (Rabs_pos_lt _ S0) as P.
    apply (Rmult_le_reg_r (/ Rabs (xh + xl + y))); [apply Rinv_0_lt_compat; exact P | ].
    rewrite Rmult_assoc, Rinv_r, Rmult_1_r by lra. exact Bd.
Qed.

(** * The index *)

Definition dwx_L : R := ln 2 / 1024.
Lemma dwx_L_range : 0.0006769015 <= dwx_L <= 0.0006769016.
Proof. unfold dwx_L. split; interval with (i_prec 64). Qed.

Lemma dwx_znearest_shift (c : Z) x : Z.even c = true ->
  Znearest ne (x + IZR c) = (Znearest ne x + c)%Z.
Proof.
  intros Hc.
  assert (Fl : Zfloor (x + IZR c) = (Zfloor x + c)%Z).
  { apply Zfloor_imp. rewrite !plus_IZR. pose proof (Zfloor_lb x). pose proof (Zfloor_ub x). lra. }
  assert (Ce : Zceil (x + IZR c) = (Zceil x + c)%Z).
  { apply Zceil_imp. rewrite minus_IZR, !plus_IZR. pose proof (Zceil_ub x). pose proof (Zceil_lb x). lra. }
  unfold Znearest. rewrite Fl, Ce, plus_IZR.
  replace (x + IZR c - (IZR (Zfloor x) + IZR c)) with (x - IZR (Zfloor x)) by ring.
  destruct (Rcompare (x - IZR (Zfloor x)) (/ 2)); try reflexivity.
  unfold ne. rewrite Z.even_add, Hc.
  destruct (Z.even (Zfloor x)); reflexivity.
Qed.

Lemma dwx_fmt_int m e : (Z.abs m < 2 ^ 53)%Z -> (-1074 <= e)%Z -> fmtF (IZR m * bpow radix2 e).
Proof.
  intros Hm He. apply generic_format_FLT. exists (Float radix2 m e); [reflexivity | exact Hm | exact He].
Qed.

Lemma dwx_rnd_abs_err v : Rabs (rndF v - v) <= / 9007199254740992 * Rabs v + / 2 * bpow radix2 (-1074).
Proof.
  destruct (error_N_FLT radix2 (-1074) 53 ltac:(lia) ne v) as [eps [eta [He [Ht [_ Hr]]]]].
  change (FLT_exp (-1074) 53) with (FLT_exp emin prec) in Hr. rewrite Hr.
  replace (v * (1 + eps) + eta - v) with (v * eps + eta) by ring.
  assert (He' : Rabs eps <= / 9007199254740992).
  { change (- (53) + 1)%Z with (-52)%Z in He. change (bpow radix2 (-52)) with (/ 4503599627370496)%R in He. lra. }
  apply Rle_trans with (Rabs (v * eps) + Rabs eta); [apply Rabs_triang | ].
  rewrite Rabs_mult, (Rmult_comm (/ 9007199254740992)).
  apply Rplus_le_compat; [apply Rmult_le_compat_l; [apply Rabs_pos | exact He'] | exact Ht].
Qed.

Lemma dwx_shifter_value : B dwx_shifter = IZR (3 * 2 ^ 51) /\ finite dwx_shifter.
Proof. split; [rewrite dwx_shifter_val; simpl; lra | exact dwx_shifter_finite]. Qed.

Lemma dwx_shifter_add y : finite y -> Rabs (B y) <= bpow radix2 50 ->
  finite (fadd y dwx_shifter) /\ B (fadd y dwx_shifter) = IZR (Znearest ne (B y) + 3 * 2 ^ 51).
Proof.
  intros Fy Hy. destruct dwx_shifter_value as [Bs Fs].
  assert (Ha : bnd 1 53 (B y + B dwx_shifter)).
  { unfold bnd. rewrite Bs. change (IZR (3 * 2 ^ 51)) with 6755399441055744%R.
    change (bpow radix2 50) with 1125899906842624%R in Hy. change (IZR 1 * bpow radix2 53) with (1 * 9007199254740992)%R.
    apply Rabs_le_inv in Hy. apply Rabs_le. lra. }
  destruct (fadd_ok 1 53 y dwx_shifter Fy Fs ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) Ha) as [Fa Ba].
  split; [exact Fa | ]. rewrite Ba, Bs.
  assert (Mag : mag radix2 (B y + IZR (3 * 2 ^ 51)) = 53%Z :> BinNums.Z).
  { apply mag_unique. change (IZR (3 * 2 ^ 51)) with 6755399441055744%R.
    change (bpow radix2 50) with 1125899906842624%R in Hy.
    change (bpow radix2 (53 - 1)) with 4503599627370496%R. change (bpow radix2 53) with 9007199254740992%R.
    apply Rabs_le_inv in Hy. rewrite Rabs_pos_eq by lra. lra. }
  unfold round, scaled_mantissa, cexp. rewrite Mag. unfold FLT_exp, emin, prec.
  change (Z.max (53 - 53) (-1074)) with 0%Z. change (bpow radix2 (- 0)) with 1%R. rewrite Rmult_1_r.
  rewrite dwx_znearest_shift by reflexivity. unfold F2R. cbn [Fnum Fexp].
  change (bpow radix2 0) with 1%R. ring.
Qed.

Lemma dwx_shifter_bits : bits_of_b64 dwx_shifter = 4843621399236968448%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma dwx_shifted_bits t m : finite t -> B t = IZR (m + 3 * 2 ^ 51) -> (Z.abs m <= 2 ^ 50)%Z ->
  bits_of_b64 t = (4843621399236968448 + m)%Z.
Proof.
  intros Ft Bt Hm.
  assert (Rng : bpow radix2 52 <= B t < bpow radix2 53).
  { rewrite Bt. replace (bpow radix2 52) with (IZR (2 ^ 52)) by reflexivity.
    replace (bpow radix2 53) with (IZR (2 ^ 53)) by reflexivity.
    split; [apply IZR_le | apply IZR_lt]; lia. }
  assert (Nm : bpow radix2 (-1022) <= B t) by (apply Rle_trans with (bpow radix2 52); [apply bpow_le; lia | lra]).
  destruct (pos_normal t Ft Nm) as [mx [ex [Hx [_ [Mx [Ex [V [M [_ Bits]]]]]]]]].
  assert (Mg : mag radix2 (B t) = 53%Z :> Z).
  { apply mag_unique. rewrite Rabs_pos_eq by (pose proof (bpow_gt_0 radix2 52); lra).
    replace (53 - 1)%Z with 52%Z by reflexivity. exact Rng. }
  assert (E0 : ex = 0%Z) by lia. subst ex.
  rewrite V in Bt. change (bpow radix2 0) with 1 in Bt. rewrite Rmult_1_r in Bt.
  apply eq_IZR in Bt. rewrite Bits, join_eq, Bt. lia.
Qed.

Theorem dwexp_index_ok xh : finite xh -> Rabs (B xh) < 1455 ->
  let '(n, ni) := dwexp_index xh in
  finite n /\ B n = IZR ni /\ (Z.abs ni <= 2149501)%Z /\
  Rabs (B xh / dwx_L - IZR ni) <= / 2 + / 1000000000.
Proof.
  intros Fx Hx. unfold dwexp_index.
  pose proof fx_inv_finite as Fi. pose proof dwx_L_range as Lr.
  assert (Iv : 1477.3196 <= B fx_inv <= 1477.3198) by (rewrite fx_inv_val; split; lra).
  assert (Xb : Rabs (B xh * B fx_inv) <= 2149501).
  { rewrite Rabs_mult, (Rabs_pos_eq (B fx_inv)) by lra. nra. }
  destruct (fmul_ok 1 22 xh fx_inv Fx Fi ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)
              ltac:(unfold bnd; change (bpow radix2 22) with 4194304; lra)) as [Fy By].
  set (y := fmul xh fx_inv) in *.
  assert (Yb : Rabs (B y) <= bpow radix2 50).
  { rewrite By. apply Rle_trans with (IZR 1 * bpow radix2 22).
    - apply bnd_round; [lia | lia | unfold bnd; change (bpow radix2 22) with 4194304; lra].
    - change (bpow radix2 22) with 4194304. change (bpow radix2 50) with 1125899906842624. lra. }
  destruct (dwx_shifter_add y Fy Yb) as [Ft Bt].
  set (t := fadd y dwx_shifter) in *.
  set (ni := Znearest ne (B y)) in *.
  assert (Hk : Rabs (B y - IZR ni) <= / 2) by (unfold ni; apply Znearest_half).
  pose proof (dwx_rnd_abs_err (B xh * B fx_inv)) as Ey. rewrite <- By in Ey.
  assert (Tiny : / 2 * bpow radix2 (-1074) <= / 1000000000000000) by (interval with (i_prec 64)).
  assert (Ic : Rabs (B fx_inv - / dwx_L) <= / 2 ^ 41).
  { replace (/ dwx_L) with (1024 / ln 2) by (unfold dwx_L; field; interval with (i_prec 64)).
    exact fx_inv_close. }
  assert (XL : Rabs (B xh / dwx_L - IZR ni) <= / 2 + / 1000000000).
  { replace (B xh / dwx_L - IZR ni)
      with (B xh * (/ dwx_L - B fx_inv) + (B xh * B fx_inv - B y) + (B y - IZR ni)) by (unfold Rdiv; ring).
    assert (A1 : Rabs (B xh * (/ dwx_L - B fx_inv)) <= 1455 * / 2 ^ 41).
    { rewrite Rabs_mult, Rabs_minus_sym. apply Rmult_le_compat; try apply Rabs_pos; lra. }
    assert (A2 : Rabs (B xh * B fx_inv - B y) <= / 9007199254740992 * 2149501 + / 1000000000000000).
    { rewrite Rabs_minus_sym. apply Rle_trans with (1 := Ey).
      assert (/ 9007199254740992 * Rabs (B xh * B fx_inv) <= / 9007199254740992 * 2149501) by lra. lra. }
    assert (P41 : / 2 ^ 41 = / 2199023255552) by (simpl; lra). rewrite P41 in A1.
    eapply Rle_trans; [apply Rabs_triang | ]. eapply Rle_trans; [apply Rplus_le_compat_r, Rabs_triang | ]. lra. }
  assert (Ni : (Z.abs ni <= 2149501)%Z).
  { assert (A : Rabs (B xh / dwx_L) <= 2149500.4).
    { unfold Rdiv. rewrite Rabs_mult, (Rabs_pos_eq (/ dwx_L)) by (apply Rlt_le, Rinv_0_lt_compat; lra).
      apply Rle_trans with (1455 * / 0.0006769015).
      - apply Rmult_le_compat; [apply Rabs_pos | apply Rlt_le, Rinv_0_lt_compat; lra | lra | ].
        apply Rinv_le_contravar; lra.
      - interval with (i_prec 64). }
    assert (T : Rabs (IZR ni - B xh / dwx_L + B xh / dwx_L) <= Rabs (IZR ni - B xh / dwx_L) + Rabs (B xh / dwx_L))
      by apply Rabs_triang.
    replace (IZR ni - B xh / dwx_L + B xh / dwx_L) with (IZR ni) in T by ring.
    rewrite Rabs_minus_sym in T.
    assert (Rabs (IZR ni) <= 2149501) by lra.
    rewrite <- abs_IZR in H. apply le_IZR in H. lia. }
  destruct dwx_shifter_value as [Bs Fs].
  assert (Hd : bnd 1 53 (B t - B dwx_shifter)).
  { unfold bnd. rewrite Bt, Bs, <- minus_IZR. replace (ni + 3 * 2 ^ 51 - 3 * 2 ^ 51)%Z with ni by ring.
    rewrite <- abs_IZR. replace (IZR 1 * bpow radix2 53) with (IZR (2 ^ 53)) by (simpl; ring). apply IZR_le. lia. }
  destruct (fsub_ok 1 53 t dwx_shifter Ft Fs ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) Hd) as [Fn Bn].
  assert (Bn' : B (fsub t dwx_shifter) = IZR ni).
  { rewrite Bn, Bt, Bs, <- minus_IZR. replace (ni + 3 * 2 ^ 51 - 3 * 2 ^ 51)%Z with ni by ring.
    apply round_generic; auto with typeclass_instances.
    replace (IZR ni) with (IZR ni * bpow radix2 0) by (change (bpow radix2 0) with 1; ring).
    apply dwx_fmt_int; lia. }
  assert (Bits : (bits_of_b64 t - bits_of_b64 dwx_shifter)%Z = ni).
  { rewrite (dwx_shifted_bits t ni Ft Bt ltac:(lia)), dwx_shifter_bits. ring. }
  rewrite Bits. split; [exact Fn | split; [exact Bn' | split; [exact Ni | exact XL]]].
Qed.

(** [n·L1] and [n·L2] are exact for [|n| <= 2149501]. *)
Lemma dwx_l1_eq : B fx_l1 = IZR 1488522236 * bpow radix2 (-41).
Proof. rewrite fx_l1_val. change (-41)%Z with (- Z.of_nat 41)%Z. rewrite dwx_bpow_m. field. Qed.

Lemma dwexp_product_exact n ni l m e : finite n -> B n = IZR ni -> (Z.abs ni <= 2149501)%Z ->
  finite l -> B l = IZR m * bpow radix2 e -> (Z.abs m < 2 ^ 31)%Z -> (-200 <= e <= -30)%Z ->
  finite (fmul n l) /\ B (fmul n l) = IZR ni * B l.
Proof.
  intros Fn Bn Hn Fl Bl Hm He.
  assert (P : B n * B l = IZR (ni * m) * bpow radix2 e) by (rewrite Bn, Bl, mult_IZR; ring).
  assert (Mb : (Z.abs (ni * m) < 2 ^ 53)%Z).
  { rewrite Z.abs_mul. apply Z.le_lt_trans with (2149501 * (2 ^ 31 - 1))%Z; [ | reflexivity].
    apply Z.mul_le_mono_nonneg; lia. }
  destruct (fmul_exact n l Fn Fl) as [F E].
  - rewrite P. apply generic_format_FLT.
    exists (Float radix2 (ni * m) e); [reflexivity | exact Mb | simpl; lia].
  - rewrite P, Rabs_mult, (Rabs_pos_eq (bpow radix2 e)) by apply bpow_ge_0. rewrite <- abs_IZR.
    apply Rlt_trans with (IZR (2 ^ 53) * bpow radix2 e).
    + apply Rmult_lt_compat_r; [apply bpow_gt_0 | apply IZR_lt; exact Mb].
    + change (IZR (2 ^ 53)) with (bpow radix2 53). rewrite <- bpow_plus. apply bpow_lt. lia.
  - split; [exact F | rewrite E, Bn; reflexivity].
Qed.

(** * The reduction *)

Definition dwx_u2 : R := bpow radix2 (-106).

Lemma dwx_u2_eq : 2 * bpow radix2 (- prec) ^ 2 = 2 * dwx_u2.
Proof.
  unfold dwx_u2, prec. change (- (53))%Z with (-53)%Z.
  replace (bpow radix2 (-53) ^ 2) with (bpow radix2 (-53) * bpow radix2 (-53)) by ring.
  rewrite <- bpow_plus. reflexivity.
Qed.

(** The words of a normalized double word are bounded by twice its value plus
    the smallest subnormal. *)
Lemma dwx_dw_words zh zl M : B zh = rndF (B zh + B zl) -> Rabs (B zh + B zl) <= M ->
  Rabs (B zh) <= 2 * M + bpow radix2 (-1074) /\ Rabs (B zl) <= 3 * M + bpow radix2 (-1074).
Proof.
  intros E Hm. pose proof (dwx_rnd_abs_err (B zh + B zl)) as R0. rewrite <- E in R0.
  assert (T : / 2 * bpow radix2 (-1074) <= bpow radix2 (-1074)) by (pose proof (bpow_gt_0 radix2 (-1074)); lra).
  assert (H1 : Rabs (B zh) <= Rabs (B zh + B zl) + Rabs (B zh - (B zh + B zl))).
  { replace (B zh) with ((B zh + B zl) + (B zh - (B zh + B zl))) at 1 by ring. apply Rabs_triang. }
  assert (H2 : Rabs (B zl) <= Rabs (B zh + B zl) + Rabs (B zh)).
  { replace (B zl) with ((B zh + B zl) - B zh) at 1 by ring. eapply Rle_trans; [apply Rabs_triang | ].
    rewrite Rabs_Ropp. lra. }
  pose proof (Rabs_pos (B zh + B zl)). split; nra.
Qed.

(** One DWPlusFP step in binary64: finite, normalized, within [2u²] of the
    exact sum, for words at most [2^1018]. *)
Lemma dwx_add_step xh xl y : finite xh -> finite xl -> finite y -> B xh = rndF (B xh + B xl) ->
  Rabs (B xh) <= bpow radix2 1018 -> Rabs (B xl) <= bpow radix2 1018 -> Rabs (B y) <= bpow radix2 1018 ->
  let '(zh, zl) := add_f64_64 xh xl y in
  finite zh /\ finite zl /\ B zh = rndF (B zh + B zl) /\
  Rabs (B zh + B zl - (B xh + B xl + B y)) <= 2 * dwx_u2 * Rabs (B xh + B xl + B y).
Proof.
  intros Fh Fl Fy E Bh Bl By.
  assert (U : forall v, Rabs v <= bpow radix2 1018 -> bnd 1 1018 v) by (intros v Hv; unfold bnd; lra).
  destruct (add_f64_64_ok 1 1018 xh xl y Fh Fl Fy (U _ Bh) (U _ Bl) (U _ By)
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [Fzh [Fzl Ez]].
  pose proof (add_f64_dw (B xh) (B xl) (B y) (B_fmt xh) (B_fmt xl) (B_fmt y) E) as D.
  pose proof (add_f64_abs (B xh) (B xl) (B y) (B_fmt xh) (B_fmt xl) (B_fmt y) E) as A.
  rewrite <- Ez in D, A. rewrite <- dwx_u2_eq.
  destruct (add_f64_64 xh xl y) as [zh zl]. cbn [fst snd] in *.
  repeat split; assumption.
Qed.

(** The double word's trailing word is below [2^-53] of its value plus the
    smallest subnormal. *)
Lemma dwx_low_small xh xl : B xh = rndF (B xh + B xl) -> Rabs (B xh) < 1455 -> Rabs (B xl) <= / 5000000000000.
Proof.
  intros E Hx. pose proof (dwx_rnd_abs_err (B xh + B xl)) as R0. rewrite <- E in R0.
  replace (B xh - (B xh + B xl)) with (- B xl) in R0 by ring. rewrite Rabs_Ropp in R0.
  assert (Tiny : / 2 * bpow radix2 (-1074) <= / 1000000000000000000) by (interval with (i_prec 64)).
  assert (Tr : Rabs (B xh + B xl) <= Rabs (B xh) + Rabs (B xl)) by apply Rabs_triang.
  clear E. nra.
Qed.

Lemma dwx_l1_gap : Rabs (dwx_L - B fx_l1) <= / 23000000000000.
Proof. unfold dwx_L. rewrite fx_l1_val. interval with (i_prec 100). Qed.

Lemma dwx_l12_gap : Rabs (dwx_L - B fx_l1 - B dwx_l2) <= / 70000000000000000000000.
Proof. unfold dwx_L. rewrite fx_l1_val, dwx_l2_val. interval with (i_prec 200). Qed.

Lemma dwx_l3_small : Rabs (B dwx_l3) <= bpow radix2 (-76).
Proof. rewrite dwx_l3_val. change (-76)%Z with (- Z.of_nat 76)%Z. rewrite dwx_bpow_m. interval with (i_prec 200). Qed.

Lemma dwx_l3_big : bpow radix2 (-969) <= Rabs (B dwx_l3).
Proof. rewrite dwx_l3_val. change (-969)%Z with (- Z.of_nat 969)%Z. rewrite dwx_bpow_m. interval with (i_prec 200). Qed.

Lemma dwx_split' : Rabs (B fx_l1 + B dwx_l2 + B dwx_l3 - dwx_L) <= / 2 ^ 128.
Proof. exact dwx_split. Qed.

Lemma dwx_u2_val : dwx_u2 = / 2 ^ 106.
Proof. unfold dwx_u2. change (-106)%Z with (- Z.of_nat 106)%Z. apply dwx_bpow_m. Qed.

Theorem dwexp_reduce_ok xh xl n ni :
  finite xh -> finite xl -> B xh = rndF (B xh + B xl) -> Rabs (B xh) < 1455 ->
  finite n -> B n = IZR ni -> (Z.abs ni <= 2149501)%Z ->
  Rabs (B xh / dwx_L - IZR ni) <= / 2 + / 1000000000 ->
  let '(rh, rl) := dwexp_reduce xh xl n in
  finite rh /\ finite rl /\ B rh = rndF (B rh + B rl) /\
  Rabs (B rh + B rl - (B xh + B xl - IZR ni * dwx_L)) <= 52 / 100 * dwx_u2 /\
  Rabs (B xh + B xl - IZR ni * dwx_L) <= 0.000338451.
Proof.
  intros Fh Fl E Hx Fn Bn Ni Q.
  pose proof dwx_L_range as Lr.
  assert (Nr : Rabs (IZR ni) <= 2149501) by (rewrite <- abs_IZR; apply IZR_le; lia).
  pose proof (dwx_low_small xh xl E Hx) as Xl.
  set (R := B xh + B xl - IZR ni * dwx_L).
  assert (HR : Rabs R <= 0.000338451).
  { assert (H1 : B xh - IZR ni * dwx_L = dwx_L * (B xh / dwx_L - IZR ni)) by (field; lra).
    assert (H2 : Rabs (B xh - IZR ni * dwx_L) <= 0.0006769016 * (/ 2 + / 1000000000)).
    { rewrite H1, Rabs_mult, (Rabs_pos_eq dwx_L) by lra. apply Rmult_le_compat; try lra. apply Rabs_pos. }
    unfold R. replace (B xh + B xl - IZR ni * dwx_L) with ((B xh - IZR ni * dwx_L) + B xl) by ring.
    eapply Rle_trans; [apply Rabs_triang | ]. lra. }
  (* the exact products *)
  destruct (dwexp_product_exact n ni fx_l1 1488522236 (-41) Fn Bn Ni fx_l1_finite dwx_l1_eq
              ltac:(lia) ltac:(lia)) as [Fe1 Be1].
  destruct (dwexp_product_exact n ni dwx_l2 (-1549864104) (-75) Fn Bn Ni dwx_l2_finite dwx_l2_eq
              ltac:(lia) ltac:(lia)) as [Fe2 Be2].
  assert (Nb : Rabs (B n) <= bpow radix2 22).
  { rewrite Bn. change (bpow radix2 22) with 4194304. lra. }
  assert (Dom : in_two_prod_domain (B n) (B dwx_l3)).
  { destruct (Z.eq_dec ni 0) as [Z0 | N0].
    - left. rewrite Bn, Z0. ring.
    - right. rewrite Rabs_mult. pose proof dwx_l3_big as L3b.
      assert (1 <= Rabs (B n)) by (rewrite Bn, <- abs_IZR; apply IZR_le; lia).
      pose proof (Rabs_pos (B dwx_l3)). nra. }
  pose proof (two_prod_ieee 22 (-76) n dwx_l3 Fn dwx_l3_finite Nb dwx_l3_small
                ltac:(lia) ltac:(lia) ltac:(lia) Dom) as TP.
  unfold dwexp_reduce.
  destruct (two_prod64 n dwx_l3) as [qh ql]. destruct TP as [Fqh [Fql [Pq Eq]]].
  rewrite Bn in Pq, Eq.
  pose proof dwx_l1_gap as G1. pose proof dwx_l12_gap as G12. pose proof dwx_split' as Sp.
  pose proof dwx_l3_small as L3s.
  assert (U2 : 0 < dwx_u2 <= / 81129638414606681695789005144064) by (rewrite dwx_u2_val; split; [apply Rinv_0_lt_compat; apply pow_lt; lra | simpl; lra]).
  assert (W : forall v, Rabs v <= 2000 -> Rabs v <= bpow radix2 1018).
  { intros v Hv. apply Rle_trans with (bpow radix2 11); [change (bpow radix2 11) with 2048; lra | apply bpow_le; lia]. }
  assert (Wd : forall zh zl M, B zh = rndF (B zh + B zl) -> Rabs (B zh + B zl) <= M -> M <= / 10 ->
            Rabs (B zh) <= bpow radix2 1018 /\ Rabs (B zl) <= bpow radix2 1018).
  { intros zh zl M Ez Hz HM. destruct (dwx_dw_words zh zl M Ez Hz) as [A1 A2].
    assert (bpow radix2 (-1074) <= / 10) by (interval with (i_prec 64)).
    split; apply W; lra. }
  assert (Wx : Rabs (B xh) <= bpow radix2 1018 /\ Rabs (B xl) <= bpow radix2 1018).
  { split; apply W; lra. }
  assert (Ebd : forall e s M, Rabs e <= 2 * dwx_u2 * Rabs s -> Rabs s <= M -> Rabs e <= 2 * dwx_u2 * M).
  { intros e s M He Hs. apply Rle_trans with (2 * dwx_u2 * Rabs s); [exact He | apply Rmult_le_compat_l; lra]. }
  (* step a: x - n L1 *)
  assert (Y1 : Rabs (B (fneg (fmul n fx_l1))) <= bpow radix2 1018).
  { rewrite dwx_fneg, Rabs_Ropp, Be1. apply W.
    assert (C : 0 <= B fx_l1 <= 0.000677) by (rewrite fx_l1_val; split; interval with (i_prec 64)).
    rewrite Rabs_mult, (Rabs_pos_eq (B fx_l1)) by lra.
    assert (Rabs (IZR ni) * B fx_l1 <= 2149501 * 0.000677) by (apply Rmult_le_compat; try apply Rabs_pos; lra). lra. }
  destruct Wx as [Wxh Wxl].
  pose proof (dwx_add_step xh xl (fneg (fmul n fx_l1)) Fh Fl (dwx_fneg_finite _ Fe1) E Wxh Wxl Y1) as SA.
  destruct (add_f64_64 xh xl (fneg (fmul n fx_l1))) as [ah al]. destruct SA as [Fah [Fal [Ea Ra]]].
  rewrite dwx_fneg, Be1 in Ra.
  set (s1 := B xh + B xl + - (IZR ni * B fx_l1)) in Ra.
  assert (S1 : s1 = R + IZR ni * (dwx_L - B fx_l1)) by (unfold s1, R; ring).
  assert (S1b : Rabs s1 <= 0.00034).
  { rewrite S1. eapply Rle_trans; [apply Rabs_triang | ]. rewrite Rabs_mult.
    assert (Rabs (IZR ni) * Rabs (dwx_L - B fx_l1) <= 2149501 * / 23000000000000)
      by (apply Rmult_le_compat; try apply Rabs_pos; assumption). lra. }
  set (e1 := B ah + B al - s1) in Ra.
  assert (E1 : Rabs e1 <= 2 * dwx_u2 * 0.00034) by exact (Ebd e1 s1 _ Ra S1b).
  assert (Av : Rabs (B ah + B al) <= 0.00035) by (replace (B ah + B al) with (s1 + e1) by (unfold e1; ring);
    eapply Rle_trans; [apply Rabs_triang | ]; lra).
  destruct (Wd ah al 0.00035 Ea Av ltac:(lra)) as [Wah Wal].
  (* step b: a - n L2 *)
  assert (Y2 : Rabs (B (fneg (fmul n dwx_l2))) <= bpow radix2 1018).
  { rewrite dwx_fneg, Rabs_Ropp, Be2. apply W.
    assert (C : Rabs (B dwx_l2) <= / 1000000000000) by (rewrite dwx_l2_val; interval with (i_prec 64)).
    rewrite Rabs_mult.
    assert (Rabs (IZR ni) * Rabs (B dwx_l2) <= 2149501 * / 1000000000000)
      by (apply Rmult_le_compat; try apply Rabs_pos; assumption). lra. }
  pose proof (dwx_add_step ah al (fneg (fmul n dwx_l2)) Fah Fal (dwx_fneg_finite _ Fe2) Ea Wah Wal Y2) as SB.
  destruct (add_f64_64 ah al (fneg (fmul n dwx_l2))) as [bh bl]. destruct SB as [Fbh [Fbl [Eb Rb]]].
  rewrite dwx_fneg, Be2 in Rb.
  set (s2 := B ah + B al + - (IZR ni * B dwx_l2)) in Rb.
  assert (S2 : s2 = R + IZR ni * (dwx_L - B fx_l1 - B dwx_l2) + e1) by (unfold s2, e1, s1, R; ring).
  assert (S2b : Rabs s2 <= 0.00034).
  { rewrite S2. eapply Rle_trans; [apply Rabs_triang | ]. eapply Rle_trans; [apply Rplus_le_compat_r, Rabs_triang | ].
    rewrite Rabs_mult.
    assert (Rabs (IZR ni) * Rabs (dwx_L - B fx_l1 - B dwx_l2) <= 2149501 * / 70000000000000000000000)
      by (apply Rmult_le_compat; try apply Rabs_pos; assumption). lra. }
  set (e2 := B bh + B bl - s2) in Rb.
  assert (E2 : Rabs e2 <= 2 * dwx_u2 * 0.00034) by exact (Ebd e2 s2 _ Rb S2b).
  assert (Bv : Rabs (B bh + B bl) <= 0.00035) by (replace (B bh + B bl) with (s2 + e2) by (unfold e2; ring);
    eapply Rle_trans; [apply Rabs_triang | ]; lra).
  destruct (Wd bh bl 0.00035 Eb Bv ltac:(lra)) as [Wbh Wbl].
  (* the exact product's words are small *)
  assert (L3v : Rabs (B dwx_l3) <= / 10000000000000000000000) by (rewrite dwx_l3_val; interval with (i_prec 64)).
  assert (Qs : Rabs (B qh + B ql) <= / 1000000000000000).
  { rewrite Eq, Rabs_mult.
    assert (Rabs (IZR ni) * Rabs (B dwx_l3) <= 2149501 * / 10000000000000000000000)
      by (apply Rmult_le_compat; try apply Rabs_pos; assumption). lra. }
  assert (Qe : B qh = rndF (B qh + B ql)) by (rewrite Eq; exact Pq).
  destruct (dwx_dw_words qh ql (/ 1000000000000000) Qe Qs) as [Wqh0 Wql0].
  assert (Tb : bpow radix2 (-1074) <= / 1000000000000000) by (interval with (i_prec 64)).
  assert (Wqh : Rabs (B (fneg qh)) <= bpow radix2 1018) by (rewrite dwx_fneg, Rabs_Ropp; apply W; lra).
  assert (Wql : Rabs (B (fneg ql)) <= bpow radix2 1018) by (rewrite dwx_fneg, Rabs_Ropp; apply W; lra).
  (* step c: b - q_lo *)
  pose proof (dwx_add_step bh bl (fneg ql) Fbh Fbl (dwx_fneg_finite _ Fql) Eb Wbh Wbl Wql) as SC.
  destruct (add_f64_64 bh bl (fneg ql)) as [ch cl]. destruct SC as [Fch [Fcl [Ec Rc]]].
  rewrite dwx_fneg in Rc.
  set (s3 := B bh + B bl + - B ql) in Rc.
  assert (S3b : Rabs s3 <= 0.00034001).
  { unfold s3. replace (B bh + B bl + - B ql) with (s2 + e2 - B ql) by (unfold e2; ring).
    eapply Rle_trans; [apply Rabs_triang | ]. rewrite Rabs_Ropp.
    eapply Rle_trans; [apply Rplus_le_compat_r, Rabs_triang | ]. lra. }
  set (e3 := B ch + B cl - s3) in Rc.
  assert (E3 : Rabs e3 <= 2 * dwx_u2 * 0.00034001) by exact (Ebd e3 s3 _ Rc S3b).
  assert (Cv : Rabs (B ch + B cl) <= 0.00035) by (replace (B ch + B cl) with (s3 + e3) by (unfold e3; ring);
    eapply Rle_trans; [apply Rabs_triang | ]; lra).
  destruct (Wd ch cl 0.00035 Ec Cv ltac:(lra)) as [Wch Wcl].
  (* step d: c - q_hi *)
  pose proof (dwx_add_step ch cl (fneg qh) Fch Fcl (dwx_fneg_finite _ Fqh) Ec Wch Wcl Wqh) as SD.
  destruct (add_f64_64 ch cl (fneg qh)) as [rh rl]. destruct SD as [Frh [Frl [Er Rr]]].
  rewrite dwx_fneg in Rr.
  set (s4 := B ch + B cl + - B qh) in Rr.
  assert (S4 : s4 = R - IZR ni * (B fx_l1 + B dwx_l2 + B dwx_l3 - dwx_L) + e1 + e2 + e3).
  { assert (Qh : B qh = IZR ni * B dwx_l3 - B ql) by lra.
    unfold s4, e3, s3, e2, s2, e1, s1, R. rewrite Qh. ring. }
  assert (Sig : Rabs (IZR ni * (B fx_l1 + B dwx_l2 + B dwx_l3 - dwx_L)) <= 2149501 * / 2 ^ 128).
  { rewrite Rabs_mult. apply Rmult_le_compat; try apply Rabs_pos; assumption. }
  set (D := IZR ni * (B fx_l1 + B dwx_l2 + B dwx_l3 - dwx_L)) in S4, Sig.
  assert (T4 : forall a b c d e, Rabs (a + b + c + d + e) <= Rabs a + Rabs b + Rabs c + Rabs d + Rabs e).
  { intros a b c d e.
    pose proof (Rabs_triang (a + b + c + d) e). pose proof (Rabs_triang (a + b + c) d).
    pose proof (Rabs_triang (a + b) c). pose proof (Rabs_triang a b). lra. }
  assert (Sg : 2149501 * / 2 ^ 128 <= 513 / 1000 * dwx_u2) by (rewrite dwx_u2_val; interval with (i_prec 64)).
  assert (S4b : Rabs s4 <= 0.00034).
  { replace s4 with (R + - D + e1 + e2 + e3) by (rewrite S4; ring).
    eapply Rle_trans; [apply T4 | ]. rewrite Rabs_Ropp. lra. }
  set (e4 := B rh + B rl - s4) in Rr.
  assert (E4 : Rabs e4 <= 2 * dwx_u2 * 0.00034) by exact (Ebd e4 s4 _ Rr S4b).
  split; [exact Frh | split; [exact Frl | split; [exact Er | split; [ | exact HR]]]].
  replace (B rh + B rl - R) with (- D + e1 + e2 + e3 + e4) by (unfold e4; rewrite S4; ring).
  eapply Rle_trans; [apply T4 | ]. rewrite Rabs_Ropp. lra.
Qed.

(** * The table as double words *)

Definition dwx_eqb (x y : f64) : bool :=
  match Bcompare 53 1024 x y with Some Eq => true | _ => false end.

Lemma dwx_eqb_true x y : finite x -> finite y -> dwx_eqb x y = true -> B x = B y.
Proof.
  intros Fx Fy; unfold dwx_eqb; rewrite Bcompare_correct by assumption.
  destruct (Rcompare_spec (B x) (B y)); intros; try discriminate; lra.
Qed.

(** Every entry is a normalized double word whose trailing word is zero or at
    least [LOW_FLOOR], so its products with a value near 1 are zero or normal. *)
Definition dwx_tab_entry (j : nat) : bool :=
  dwx_eqb (fadd (fx_t_hi j) (fx_t_lo j)) (fx_t_hi j) &&
  (negb (dwx_lt dwx_zero (b64_abs (fx_t_lo j))) || negb (dwx_lt (b64_abs (fx_t_lo j)) dwx_low_floor)).

Lemma dwx_tab_check : forallb dwx_tab_entry (seq 0 1024) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma dwx_tab j : (j < 1024)%nat ->
  finite (fx_t_hi j) /\ finite (fx_t_lo j) /\ B (fx_t_hi j) = rndF (B (fx_t_hi j) + B (fx_t_lo j)) /\
  (B (fx_t_lo j) = 0 \/ B dwx_low_floor <= Rabs (B (fx_t_lo j))) /\
  1 <= B (fx_t_hi j) < 2 /\ Rabs (B (fx_t_lo j)) <= / 2 ^ 53 /\
  Rabs (B (fx_t_hi j) + B (fx_t_lo j) - exp (INR j * ln 2 / 1024)) <= bpow radix2 (-104).
Proof.
  intros Hj. destruct (fx_t_ok j Hj) as [Fh [Fl [_ [_ [_ [Th [Tl D]]]]]]].
  unfold fx_t_hi, fx_t_lo.
  pose proof dwx_tab_check as C. rewrite forallb_forall in C.
  specialize (C j ltac:(apply in_seq; lia)). unfold dwx_tab_entry, fx_t_hi, fx_t_lo in C.
  apply andb_prop in C. destruct C as [C1 C2].
  set (th := b64_of_bits (fst (nth j fx_t_bits (0%Z, 0%Z)))) in *.
  set (tl := b64_of_bits (snd (nth j fx_t_bits (0%Z, 0%Z)))) in *.
  assert (Bd : bnd 1 2 (B th + B tl)).
  { unfold bnd. change (bpow radix2 2) with 4.
    assert (/ 2 ^ 53 <= 1) by (interval with (i_prec 64)).
    pose proof (Rabs_triang (B th) (B tl)) as T. rewrite (Rabs_pos_eq (B th)) in T by lra. lra. }
  destruct (fadd_ok 1 2 _ _ Fh Fl ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Bd) as [Fs Es].
  pose proof (dwx_eqb_true _ _ Fs Fh C1) as E1. rewrite Es in E1.
  pose proof (dwx_abs_finite _ Fl) as Fa.
  assert (Fz : finite dwx_zero) by reflexivity.
  assert (Ab : B (b64_abs tl) = Rabs (B tl)) by (unfold b64_abs; apply B2R_Babs).
  split; [exact Fh | split; [exact Fl | split; [symmetry; exact E1 | split; [ | ]]]].
  2: { repeat split; try assumption; lra. }
  apply Bool.orb_true_iff in C2. destruct C2 as [C2 | C2]; apply Bool.negb_true_iff in C2.
  - left. apply (dwx_lt_false _ _ Fz Fa) in C2. rewrite Ab in C2.
    change (B dwx_zero) with 0 in C2. pose proof (Rabs_pos (B tl)).
    destruct (Req_dec (B tl) 0) as [Z0 | Z0]; [exact Z0 | pose proof (Rabs_pos_lt _ Z0); lra].
  - right. apply (dwx_lt_false _ _ Fa dwx_low_floor_finite) in C2. rewrite Ab in C2. exact C2.
Qed.

(** * Products *)

Lemma dwx_mul_step xh xl yh yl :
  finite xh -> finite xl -> B xh = rndF (B xh + B xl) ->
  finite yh -> finite yl -> B yh = rndF (B yh + B yl) ->
  Rabs (B xh) <= 4 -> Rabs (B xl) <= 4 -> Rabs (B yh) <= 4 -> Rabs (B yl) <= 4 ->
  in_two_prod_domain (B xh) (B yh) -> normal_or_zero (B xh * B yl) -> normal_or_zero (B xl * B yh) ->
  (B xh + B xl) * (B yh + B yl) <> 0 ->
  let '(zh, zl) := mul64 xh xl yh yl in
  finite zh /\ finite zl /\ B zh = rndF (B zh + B zl) /\
  Rabs (B zh + B zl - (B xh + B xl) * (B yh + B yl)) <= 5 * dwx_u2 * Rabs ((B xh + B xl) * (B yh + B yl)).
Proof.
  intros Fxh Fxl Ex Fyh Fyl Ey Bxh Bxl Byh Byl Dhh Dhl Dlh NZ.
  assert (W : forall v, Rabs v <= 4 -> Rabs v <= bpow radix2 508).
  { intros v Hv. apply Rle_trans with (bpow radix2 2); [change (bpow radix2 2) with 4; lra | apply bpow_le; lia]. }
  pose proof (mul_ieee xh xl yh yl Fxh Fxl Ex Fyh Fyl Ey (W _ Bxh) (W _ Bxl) (W _ Byh) (W _ Byl) Dhh Dhl Dlh) as M.
  assert (U : forall v, Rabs v <= 4 -> bnd 1 2 v) by (intros v Hv; unfold bnd; (change (bpow radix2 2) with 4); lra).
  destruct (mul64_ok 2 xh xl yh yl Fxh Fxl Fyh Fyl (U _ Bxh) (U _ Bxl) (U _ Byh) (U _ Byl) ltac:(lia)) as [_ [_ Ez]].
  pose proof (mul_dw (B xh) (B xl) (B yh) (B yl) (B_fmt xh) (B_fmt xl) Ex (B_fmt yh) (B_fmt yl) Ey Dhh Dhl Dlh) as D.
  rewrite <- Ez in D.
  destruct (mul64 xh xl yh yl) as [zh zl]. cbn [fst snd] in *. destruct M as [Fzh [Fzl Rl]].
  split; [exact Fzh | split; [exact Fzl | split; [exact D | ]]].
  assert (Uq : bpow radix2 (- prec) * bpow radix2 (- prec) = dwx_u2) by (rewrite <- bpow_plus; reflexivity).
  rewrite Uq in Rl. unfold Rdiv in Rl. rewrite Rabs_mult, Rabs_Rinv in Rl by exact NZ.
  pose proof (Rabs_pos_lt _ NZ) as P.
  apply (Rmult_lt_compat_r (Rabs ((B xh + B xl) * (B yh + B yl)))) in Rl; [ | exact P].
  rewrite Rmult_assoc, Rinv_l, Rmult_1_r in Rl by lra. lra.
Qed.

(** * One Horner step *)

Lemma dwx_low_le xh xl : B xh = rndF (B xh + B xl) -> Rabs (B xl) <= Rabs (B xh) + 2.
Proof.
  intros E. pose proof (dwx_rnd_abs_err (B xh + B xl)) as R0. rewrite <- E in R0.
  replace (B xh - (B xh + B xl)) with (- B xl) in R0 by ring. rewrite Rabs_Ropp in R0.
  assert (Tiny : / 2 * bpow radix2 (-1074) <= 1) by (interval with (i_prec 64)).
  pose proof (Rabs_triang (B xh) (B xl)). pose proof (Rabs_pos (B xh)). lra.
Qed.

Lemma dwx_nonzero xh xl : B xh = rndF (B xh + B xl) -> B xh <> 0 -> B xh + B xl <> 0.
Proof. intros E N Z0. rewrite Z0, round_0 in E by exact _. exact (N E). Qed.

Lemma dwx_rndF_float x : rndF (B x) = B x.
Proof. apply round_generic; [exact _ | apply B_fmt]. Qed.

Lemma dwx_floors :
  bpow radix2 (-969) <= / 10000 * B dwx_r_floor /\
  bpow radix2 (-1022) <= / 10000 * B dwx_low_floor /\
  bpow radix2 (-1022) <= B dwx_v_floor * B dwx_r_floor /\
  0 < B dwx_v_floor <= / 10 ^ 59 /\ 0 < B dwx_r_floor <= / 10 ^ 200 /\ 0 < B dwx_low_floor <= / 10 ^ 299.
Proof.
  rewrite dwx_r_floor_val, dwx_low_floor_val, dwx_v_floor_val.
  change (-969)%Z with (- Z.of_nat 969)%Z. change (-1022)%Z with (- Z.of_nat 1022)%Z.
  rewrite !dwx_bpow_m. repeat split; interval with (i_prec 64).
Qed.

Definition dwexp_err (A d rho cl ch : R) : R :=
  let m := (A + d) * rho * (1 + 5 * dwx_u2) in
  let s := (m + cl) * (1 + 2 * dwx_u2) in
  d * rho + 5 * dwx_u2 * (A + d) * rho + 2 * dwx_u2 * (m + cl) + 2 * dwx_u2 * (s + ch) + B dwx_v_floor.

Lemma dwexp_step_ok k (vh vl rh rl : f64) P A d rho :
  finite vh -> finite vl -> B vh = rndF (B vh + B vl) ->
  / 10000 <= Rabs (B vh) <= 2 -> (B vl = 0 \/ B dwx_v_floor <= Rabs (B vl)) ->
  finite rh -> finite rl -> B rh = rndF (B rh + B rl) ->
  B dwx_r_floor <= Rabs (B rh) <= / 1000 -> (B rl = 0 \/ B dwx_low_floor <= Rabs (B rl)) ->
  Rabs (B rh + B rl) <= rho -> rho <= / 1000 ->
  Rabs P <= A -> Rabs (B vh + B vl - P) <= d -> 0 <= d -> A + d <= 3 ->
  finite (dwx_c_hi k) -> finite (dwx_c_lo k) ->
  Rabs (B (dwx_c_hi k)) <= 1 -> Rabs (B (dwx_c_lo k)) <= / 1000 ->
  ((k < 3)%nat -> B (dwx_c_lo k) = 0) ->
  let '(wh, wl) := dwexp_step k rh rl (vh, vl) in
  finite wh /\ finite wl /\ B wh = rndF (B wh + B wl) /\
  (B wl = 0 \/ B dwx_v_floor <= Rabs (B wl)) /\
  Rabs (B wh + B wl - (P * (B rh + B rl) + B (dwx_c_hi k) + B (dwx_c_lo k)))
    <= dwexp_err A d rho (Rabs (B (dwx_c_lo k))) (Rabs (B (dwx_c_hi k))).
Proof.
  intros Fvh Fvl Ev Bv Lv Frh Frl Er Br Lr Hr Hrho HP Hd Hd0 HAd Fch Fcl Bch Bcl Kl.
  destruct dwx_floors as [F1 [F2 [F3 [[Vf0 Vf1] [[Rf0 Rf1] [Lf0 Lf1]]]]]].
  assert (U2 : 0 < dwx_u2 <= / 10 ^ 30) by (rewrite dwx_u2_val; split; interval with (i_prec 64)).
  set (V := B vh + B vl) in *. set (r := B rh + B rl) in *.
  pose proof (dwx_low_le _ _ Ev) as Bvl. pose proof (dwx_low_le _ _ Er) as Brl.
  assert (NV : V <> 0) by (apply dwx_nonzero; [exact Ev | intros Z0; rewrite Z0, Rabs_R0 in Bv; lra]).
  assert (Nr : r <> 0) by (apply dwx_nonzero; [exact Er | intros Z0; rewrite Z0, Rabs_R0 in Br; lra]).
  assert (HV : Rabs V <= A + d).
  { replace V with (P + (V - P)) by ring. pose proof (Rabs_triang P (V - P)). lra. }
  (* the product's domain *)
  assert (Dhh : in_two_prod_domain (B vh) (B rh)).
  { right. rewrite Rabs_mult. apply Rle_trans with (/ 10000 * B dwx_r_floor); [exact F1 | ].
    apply Rmult_le_compat; lra. }
  assert (Dhl : normal_or_zero (B vh * B rl)).
  { destruct Lr as [Z0 | Lr]; [left; rewrite Z0; ring | right].
    rewrite Rabs_mult. apply Rle_trans with (/ 10000 * B dwx_low_floor); [exact F2 | ].
    apply Rmult_le_compat; lra. }
  assert (Dlh : normal_or_zero (B vl * B rh)).
  { destruct Lv as [Z0 | Lv]; [left; rewrite Z0; ring | right].
    rewrite Rabs_mult. apply Rle_trans with (B dwx_v_floor * B dwx_r_floor); [exact F3 | ].
    apply Rmult_le_compat; lra. }
  assert (NVr : V * r <> 0) by (apply Rmult_integral_contrapositive; split; assumption).
  pose proof (dwx_mul_step vh vl rh rl Fvh Fvl Ev Frh Frl Er ltac:(lra) ltac:(lra) ltac:(lra) ltac:(lra)
                Dhh Dhl Dlh NVr) as SM.
  unfold dwexp_step. fold V r in SM.
  destruct (mul64 vh vl rh rl) as [mh ml]. destruct SM as [Fmh [Fml [Em Rm]]].
  set (cl := B (dwx_c_lo k)) in *. set (ch := B (dwx_c_hi k)) in *.
  set (mb := (A + d) * rho * (1 + 5 * dwx_u2)).
  assert (VR : Rabs (V * r) <= (A + d) * rho) by (rewrite Rabs_mult; apply Rmult_le_compat; try apply Rabs_pos; lra).
  assert (HM : Rabs (B mh + B ml) <= mb).
  { unfold mb. replace (B mh + B ml) with (V * r + (B mh + B ml - V * r)) by ring.
    pose proof (Rabs_triang (V * r) (B mh + B ml - V * r)).
    assert (5 * dwx_u2 * Rabs (V * r) <= 5 * dwx_u2 * ((A + d) * rho)) by (apply Rmult_le_compat_l; lra). nra. }
  assert (R0 : 0 <= rho) by (pose proof (Rabs_pos r); lra).
  assert (A0 : 0 <= A + d) by (pose proof (Rabs_pos P); lra).
  assert (Mb : mb <= / 100).
  { unfold mb. assert ((A + d) * rho <= 3 * / 1000) by (apply Rmult_le_compat; lra).
    assert ((A + d) * rho * (1 + 5 * dwx_u2) <= 3 * / 1000 * (1 + 5 * dwx_u2))
      by (apply Rmult_le_compat_r; lra). lra. }
  assert (W : forall v, Rabs v <= 4 -> Rabs v <= bpow radix2 1018).
  { intros v Hv. apply Rle_trans with (bpow radix2 2); [change (bpow radix2 2) with 4; lra | apply bpow_le; lia]. }
  assert (Wd : forall zh zl M, B zh = rndF (B zh + B zl) -> Rabs (B zh + B zl) <= M -> M <= 1 ->
            Rabs (B zh) <= bpow radix2 1018 /\ Rabs (B zl) <= bpow radix2 1018).
  { intros zh zl M Ez Hz HM'. destruct (dwx_dw_words zh zl M Ez Hz) as [A1 A2].
    assert (bpow radix2 (-1074) <= / 10) by (interval with (i_prec 64)).
    split; apply W; lra. }
  destruct (Wd mh ml mb Em HM ltac:(lra)) as [Wmh Wml].
  (* the low coefficient word *)
  assert (SL : exists sh sl,
      (if (3 <=? k)%nat then add_f64_64 mh ml (dwx_c_lo k) else (mh, ml)) = (sh, sl) /\
      finite sh /\ finite sl /\ B sh = rndF (B sh + B sl) /\
      Rabs (B sh + B sl - (B mh + B ml + cl)) <= 2 * dwx_u2 * (mb + Rabs cl)).
  { destruct (3 <=? k)%nat eqn:K.
    - pose proof (dwx_add_step mh ml (dwx_c_lo k) Fmh Fml Fcl Em Wmh Wml ltac:(apply W; change (Rabs cl <= 4); lra)) as SA.
      destruct (add_f64_64 mh ml (dwx_c_lo k)) as [sh sl]. destruct SA as [Fsh [Fsl [Es Rs]]]. fold cl in Rs.
      exists sh, sl. split; [reflexivity | repeat split; try assumption].
      eapply Rle_trans; [exact Rs | ]. apply Rmult_le_compat_l; [lra | ].
      pose proof (Rabs_triang (B mh + B ml) cl). lra.
    - apply Nat.leb_gt in K. exists mh, ml. split; [reflexivity | repeat split; try assumption].
      fold cl in Kl. rewrite (Kl K), Rplus_0_r. unfold Rminus. rewrite Rplus_opp_r, Rabs_R0.
      pose proof (Rabs_pos cl). assert (0 <= mb) by (unfold mb; apply Rmult_le_pos; [apply Rmult_le_pos | ]; lra). assert (0 <= 2 * dwx_u2) by lra. apply Rmult_le_pos; lra. }
  destruct SL as [sh [sl [Hs [Fsh [Fsl [Es Rs]]]]]]. rewrite Hs.
  set (sb := (mb + Rabs cl) * (1 + 2 * dwx_u2)).
  assert (HS : Rabs (B sh + B sl) <= sb).
  { unfold sb. replace (B sh + B sl) with ((B mh + B ml + cl) + (B sh + B sl - (B mh + B ml + cl))) by ring.
    pose proof (Rabs_triang (B mh + B ml + cl) (B sh + B sl - (B mh + B ml + cl))).
    pose proof (Rabs_triang (B mh + B ml) cl). nra. }
  assert (Sb : sb <= / 10).
  { unfold sb. assert ((mb + Rabs cl) * (1 + 2 * dwx_u2) <= (/ 100 + / 1000) * (1 + 2 * dwx_u2))
      by (apply Rmult_le_compat_r; lra). lra. }
  destruct (Wd sh sl sb Es HS ltac:(lra)) as [Wsh Wsl].
  (* the high coefficient word *)
  pose proof (dwx_add_step sh sl (dwx_c_hi k) Fsh Fsl Fch Es Wsh Wsl ltac:(apply W; change (Rabs ch <= 4); lra)) as SA.
  destruct (add_f64_64 sh sl (dwx_c_hi k)) as [wh wl]. destruct SA as [Fwh [Fwl [Ew Rw]]].
  fold ch in Rw.
  assert (Rw' : Rabs (B wh + B wl - (B sh + B sl + ch)) <= 2 * dwx_u2 * (sb + Rabs ch)).
  { eapply Rle_trans; [exact Rw | ]. apply Rmult_le_compat_l; [lra | ].
    pose proof (Rabs_triang (B sh + B sl) ch). lra. }
  (* the error before the floor *)
  assert (Tot : Rabs (B wh + B wl - (P * r + ch + cl))
                <= d * rho + 5 * dwx_u2 * (A + d) * rho + 2 * dwx_u2 * (mb + Rabs cl) + 2 * dwx_u2 * (sb + Rabs ch)).
  { replace (B wh + B wl - (P * r + ch + cl))
      with ((B wh + B wl - (B sh + B sl + ch)) + (B sh + B sl - (B mh + B ml + cl))
            + (B mh + B ml - V * r) + (V - P) * r) by ring.
    assert (E1 : Rabs ((V - P) * r) <= d * rho)
      by (rewrite Rabs_mult; apply Rmult_le_compat; try apply Rabs_pos; lra).
    assert (E2 : Rabs (B mh + B ml - V * r) <= 5 * dwx_u2 * (A + d) * rho).
    { assert (G : 5 * dwx_u2 * Rabs (V * r) <= 5 * dwx_u2 * ((A + d) * rho)) by (apply Rmult_le_compat_l; lra).
      eapply Rle_trans; [exact Rm | ]. replace (5 * dwx_u2 * (A + d) * rho) with (5 * dwx_u2 * ((A + d) * rho)) by ring.
      exact G. }
    pose proof (Rabs_triang (B wh + B wl - (B sh + B sl + ch) + (B sh + B sl - (B mh + B ml + cl))
                              + (B mh + B ml - V * r)) ((V - P) * r)).
    pose proof (Rabs_triang (B wh + B wl - (B sh + B sl + ch) + (B sh + B sl - (B mh + B ml + cl)))
                              (B mh + B ml - V * r)).
    pose proof (Rabs_triang (B wh + B wl - (B sh + B sl + ch)) (B sh + B sl - (B mh + B ml + cl))).
    lra. }
  unfold dwexp_err. fold mb. fold sb.
  pose proof (dwx_abs_finite _ Fwl) as Fa.
  assert (Ab : B (b64_abs wl) = Rabs (B wl)) by (unfold b64_abs; apply B2R_Babs).
  destruct (dwx_lt (b64_abs wl) dwx_v_floor) eqn:Fl.
  - apply (dwx_lt_true _ _ Fa dwx_v_floor_finite) in Fl. rewrite Ab in Fl.
    split; [exact Fwh | split; [reflexivity | split; [ | split; [left; reflexivity | ]]]].
    + change (B dwx_zero) with 0. rewrite Rplus_0_r. symmetry. apply dwx_rndF_float.
    + change (B dwx_zero) with 0. rewrite Rplus_0_r.
      replace (B wh - (P * r + ch + cl)) with ((B wh + B wl - (P * r + ch + cl)) + - B wl) by ring.
      pose proof (Rabs_triang (B wh + B wl - (P * r + ch + cl)) (- B wl)) as T. rewrite Rabs_Ropp in T. lra.
  - apply (dwx_lt_false _ _ Fa dwx_v_floor_finite) in Fl. rewrite Ab in Fl.
    split; [exact Fwh | split; [exact Fwl | split; [exact Ew | split; [right; exact Fl | ]]]]. lra.
Qed.

(** * The Horner chain *)

Definition dwx_inv (vh vl : f64) (P A d : R) : Prop :=
  finite vh /\ finite vl /\ B vh = rndF (B vh + B vl) /\ / 10000 <= Rabs (B vh) <= 2 /\
  (B vl = 0 \/ B dwx_v_floor <= Rabs (B vl)) /\ Rabs P <= A /\ Rabs (B vh + B vl - P) <= d /\ 0 <= d.

Definition dwx_rinv (rh rl : f64) (rho : R) : Prop :=
  finite rh /\ finite rl /\ B rh = rndF (B rh + B rl) /\ B dwx_r_floor <= Rabs (B rh) <= / 1000 /\
  (B rl = 0 \/ B dwx_low_floor <= Rabs (B rl)) /\ Rabs (B rh + B rl) <= rho /\ rho <= / 1000.

Lemma dwx_high_bounds xh xl : B xh = rndF (B xh + B xl) ->
  Rabs (B xh + B xl) * (1 - / 9007199254740992) - / 2 * bpow radix2 (-1074) <= Rabs (B xh) /\
  Rabs (B xh) <= Rabs (B xh + B xl) * (1 + / 9007199254740992) + / 2 * bpow radix2 (-1074).
Proof.
  intros E. pose proof (dwx_rnd_abs_err (B xh + B xl)) as R0. rewrite <- E in R0.
  pose proof (Rabs_triang_inv (B xh) (B xh + B xl)) as T1.
  pose proof (Rabs_triang_inv (B xh + B xl) (B xh)) as T2.
  rewrite Rabs_minus_sym in T2. split; lra.
Qed.

Lemma dwx_coef k :
  finite (dwx_c_hi k) /\ finite (dwx_c_lo k) /\ Rabs (B (dwx_c_hi k)) <= 1 /\
  Rabs (B (dwx_c_lo k)) <= / 1000 /\ ((k < 3)%nat -> B (dwx_c_lo k) = 0).
Proof.
  destruct k as [|[|[|[|[|[|[|k]]]]]]]; cbn [dwx_c_hi dwx_c_lo];
    repeat split; try apply dwx_c0_hi_finite; try apply dwx_c0_lo_finite;
    try apply dwx_c1_hi_finite; try apply dwx_c1_lo_finite; try apply dwx_c2_hi_finite; try apply dwx_c2_lo_finite;
    try apply dwx_c3_hi_finite; try apply dwx_c3_lo_finite; try apply dwx_c4_hi_finite; try apply dwx_c4_lo_finite;
    try apply dwx_c5_hi_finite; try apply dwx_c5_lo_finite; try apply dwx_c6_hi_finite; try apply dwx_c6_lo_finite;
    try apply dwx_c7_hi_finite; try apply dwx_c7_lo_finite;
    rewrite ?dwx_c0_hi_val, ?dwx_c0_lo_val, ?dwx_c1_hi_val, ?dwx_c1_lo_val, ?dwx_c2_hi_val, ?dwx_c2_lo_val,
      ?dwx_c3_hi_val, ?dwx_c3_lo_val, ?dwx_c4_hi_val, ?dwx_c4_lo_val, ?dwx_c5_hi_val, ?dwx_c5_lo_val,
      ?dwx_c6_hi_val, ?dwx_c6_lo_val, ?dwx_c7_hi_val, ?dwx_c7_lo_val;
    try (intros; reflexivity); try (intros; lia); interval with (i_prec 64).
Qed.

Lemma dwx_chain k (vh vl rh rl : f64) P A d rho A' d' :
  dwx_inv vh vl P A d -> dwx_rinv rh rl rho -> A + d <= 3 ->
  dwexp_err A d rho (Rabs (B (dwx_c_lo k))) (Rabs (B (dwx_c_hi k))) <= d' ->
  A * rho + Rabs (B (dwx_c_hi k)) + Rabs (B (dwx_c_lo k)) <= A' ->
  / 5000 <= Rabs (B (dwx_c_hi k) + B (dwx_c_lo k)) - A * rho - d' ->
  A' + d' <= 3 / 2 ->
  let '(wh, wl) := dwexp_step k rh rl (vh, vl) in
  dwx_inv wh wl (P * (B rh + B rl) + B (dwx_c_hi k) + B (dwx_c_lo k)) A' d'.
Proof.
  intros [Fvh [Fvl [Ev [Bv [Lv [HP [Hd Hd0]]]]]]] [Frh [Frl [Er [Br [Lr [Hr Hrho]]]]]] HAd Hd' HA' Hlow Hup.
  destruct (dwx_coef k) as [Fch [Fcl [Bch [Bcl Kl]]]].
  pose proof (dwexp_step_ok k vh vl rh rl P A d rho Fvh Fvl Ev Bv Lv Frh Frl Er Br Lr Hr Hrho HP Hd Hd0 HAd
                Fch Fcl Bch Bcl Kl) as S.
  revert S. destruct (dwexp_step k rh rl (vh, vl)) as [wh wl]. intros S. destruct S as [Fwh [Fwl [Ew [Lw Rw]]]].
  set (r := B rh + B rl) in *. set (ch := B (dwx_c_hi k)) in *. set (cl := B (dwx_c_lo k)) in *.
  set (P' := P * r + ch + cl).
  assert (Pr : Rabs (P * r) <= A * rho) by (rewrite Rabs_mult; apply Rmult_le_compat; try apply Rabs_pos; lra).
  assert (W' : Rabs (B wh + B wl - P') <= d') by (unfold P'; lra).
  assert (HP' : Rabs P' <= A').
  { unfold P'. pose proof (Rabs_triang (P * r + ch) cl). pose proof (Rabs_triang (P * r) ch). lra. }
  assert (LP' : Rabs (ch + cl) - A * rho <= Rabs P').
  { unfold P'. replace (P * r + ch + cl) with ((ch + cl) + P * r) by ring.
    pose proof (Rabs_triang_inv (ch + cl + P * r) (- (P * r))) as T.
    replace (ch + cl + P * r - - (P * r)) with (ch + cl + 2 * (P * r)) in T by ring.
    pose proof (Rabs_triang (ch + cl + P * r) (- (P * r))) as T2.
    replace (ch + cl + P * r + - (P * r)) with (ch + cl) in T2 by ring. rewrite Rabs_Ropp in T2. lra. }
  assert (HW : Rabs P' - d' <= Rabs (B wh + B wl) <= Rabs P' + d').
  { pose proof (Rabs_triang_inv P' (P' - (B wh + B wl))) as T1.
    replace (P' - (P' - (B wh + B wl))) with (B wh + B wl) in T1 by ring.
    rewrite Rabs_minus_sym in T1.
    pose proof (Rabs_triang P' (B wh + B wl - P')) as T2.
    replace (P' + (B wh + B wl - P')) with (B wh + B wl) in T2 by ring. split; lra. }
  destruct (dwx_high_bounds wh wl Ew) as [H1 H2].
  assert (Tiny : / 2 * bpow radix2 (-1074) <= / 10 ^ 300) by (interval with (i_prec 64)).
  assert (Wl : / 5000 <= Rabs (B wh + B wl)) by lra.
  unfold dwx_inv. repeat split; try assumption.
  - assert (/ 5000 * (1 - / 9007199254740992) <= Rabs (B wh + B wl) * (1 - / 9007199254740992))
      by (apply Rmult_le_compat_r; lra).
    assert (/ 10 ^ 300 <= / 10 ^ 10) by (interval with (i_prec 64)). lra.
  - assert (Rabs (B wh + B wl) * (1 + / 9007199254740992) <= 3 / 2 * (1 + / 9007199254740992))
      by (apply Rmult_le_compat_r; lra).
    assert (/ 10 ^ 300 <= / 10 ^ 10) by (interval with (i_prec 64)). lra.
  - pose proof (Rabs_pos (B wh + B wl - P')). lra.
Qed.

(** The polynomial the chain evaluates, with the coefficients' words. *)
Definition dwx_hstep (k : nat) (P r : R) : R := P * r + B (dwx_c_hi k) + B (dwx_c_lo k).
Definition dwx_poly (r : R) : R :=
  dwx_hstep 0 (dwx_hstep 1 (dwx_hstep 2 (dwx_hstep 3 (dwx_hstep 4 (dwx_hstep 5 (dwx_hstep 6
    (B dwx_c7_hi + B dwx_c7_lo) r) r) r) r) r) r) r.

Definition dwx_rho : R := 3384511 / 10000000000.

Ltac dwx_numeric :=
  cbn [dwx_c_hi dwx_c_lo]; unfold dwexp_err, dwx_rho;
  rewrite ?dwx_c0_hi_val, ?dwx_c0_lo_val, ?dwx_c1_hi_val, ?dwx_c1_lo_val, ?dwx_c2_hi_val, ?dwx_c2_lo_val,
    ?dwx_c3_hi_val, ?dwx_c3_lo_val, ?dwx_c4_hi_val, ?dwx_c4_lo_val, ?dwx_c5_hi_val, ?dwx_c5_lo_val,
    ?dwx_c6_hi_val, ?dwx_c6_lo_val, ?dwx_c7_hi_val, ?dwx_c7_lo_val, ?dwx_u2_val, ?dwx_v_floor_val;
  repeat split; interval with (i_prec 200).

Lemma dwx_c7_norm : B dwx_c7_hi = rndF (B dwx_c7_hi + B dwx_c7_lo).
Proof.
  assert (Bd : bnd 1 2 (B dwx_c7_hi + B dwx_c7_lo)).
  { unfold bnd. change (bpow radix2 2) with 4. rewrite dwx_c7_hi_val, dwx_c7_lo_val. interval with (i_prec 64). }
  destruct (fadd_ok 1 2 _ _ dwx_c7_hi_finite dwx_c7_lo_finite ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Bd) as [Fs Es].
  rewrite <- Es. symmetry. apply dwx_eqb_true; [exact Fs | exact dwx_c7_hi_finite | vm_compute; reflexivity].
Qed.

Theorem dwexp_horner_ok rh rl : dwx_rinv rh rl dwx_rho ->
  let '(vh, vl) := dwexp_horner rh rl in
  dwx_inv vh vl (dwx_poly (B rh + B rl)) (10004 / 10000) (20042 / 10000 * dwx_u2).
Proof.
  intros Rinv.
  assert (I7 : dwx_inv dwx_c7_hi dwx_c7_lo (B dwx_c7_hi + B dwx_c7_lo) (1985 / 10000000) 0).
  { unfold dwx_inv. repeat split; try apply dwx_c7_hi_finite; try apply dwx_c7_lo_finite; try apply dwx_c7_norm.
    - rewrite dwx_c7_hi_val. interval with (i_prec 64).
    - rewrite dwx_c7_hi_val. interval with (i_prec 64).
    - right. rewrite dwx_c7_lo_val, dwx_v_floor_val. interval with (i_prec 64).
    - rewrite dwx_c7_hi_val, dwx_c7_lo_val. interval with (i_prec 64).
    - unfold Rminus. rewrite Rplus_opp_r, Rabs_R0. lra.
    - lra. }
  unfold dwexp_horner, dwx_poly. set (r := B rh + B rl).
  pose proof (dwx_chain 6 _ _ rh rl _ _ _ dwx_rho (1389 / 1000000) (28 / 10000 * dwx_u2) I7 Rinv
    ltac:(lra) ltac:(dwx_numeric) ltac:(dwx_numeric) ltac:(dwx_numeric) ltac:(dwx_numeric)) as I6.
  destruct (dwexp_step 6 rh rl (dwx_c7_hi, dwx_c7_lo)) as [v6h v6l].
  pose proof (dwx_chain 5 _ _ rh rl _ _ _ dwx_rho (8334 / 1000000) (167 / 10000 * dwx_u2) I6 Rinv
    ltac:(rewrite dwx_u2_val; interval with (i_prec 64)) ltac:(dwx_numeric) ltac:(dwx_numeric) ltac:(dwx_numeric) ltac:(dwx_numeric)) as I5.
  destruct (dwexp_step 5 rh rl (v6h, v6l)) as [v5h v5l].
  pose proof (dwx_chain 4 _ _ rh rl _ _ _ dwx_rho (41670 / 1000000) (835 / 10000 * dwx_u2) I5 Rinv
    ltac:(rewrite dwx_u2_val; interval with (i_prec 64)) ltac:(dwx_numeric) ltac:(dwx_numeric) ltac:(dwx_numeric) ltac:(dwx_numeric)) as I4.
  destruct (dwexp_step 4 rh rl (v5h, v5l)) as [v4h v4l].
  pose proof (dwx_chain 3 _ _ rh rl _ _ _ dwx_rho (166690 / 1000000) (3336 / 10000 * dwx_u2) I4 Rinv
    ltac:(rewrite dwx_u2_val; interval with (i_prec 64)) ltac:(dwx_numeric) ltac:(dwx_numeric) ltac:(dwx_numeric) ltac:(dwx_numeric)) as I3.
  destruct (dwexp_step 3 rh rl (v4h, v4l)) as [v3h v3l].
  pose proof (dwx_chain 2 _ _ rh rl _ _ _ dwx_rho (500060 / 1000000) (10008 / 10000 * dwx_u2) I3 Rinv
    ltac:(rewrite dwx_u2_val; interval with (i_prec 64)) ltac:(dwx_numeric) ltac:(dwx_numeric) ltac:(dwx_numeric) ltac:(dwx_numeric)) as I2.
  destruct (dwexp_step 2 rh rl (v3h, v3l)) as [v2h v2l].
  pose proof (dwx_chain 1 _ _ rh rl _ _ _ dwx_rho (10002 / 10000) (20021 / 10000 * dwx_u2) I2 Rinv
    ltac:(rewrite dwx_u2_val; interval with (i_prec 64)) ltac:(dwx_numeric) ltac:(dwx_numeric) ltac:(dwx_numeric) ltac:(dwx_numeric)) as I1.
  destruct (dwexp_step 1 rh rl (v2h, v2l)) as [v1h v1l].
  pose proof (dwx_chain 0 _ _ rh rl _ _ _ dwx_rho (10004 / 10000) (20042 / 10000 * dwx_u2) I1 Rinv
    ltac:(rewrite dwx_u2_val; interval with (i_prec 64)) ltac:(dwx_numeric) ltac:(dwx_numeric) ltac:(dwx_numeric) ltac:(dwx_numeric)) as I0.
  destruct (dwexp_step 0 rh rl (v1h, v1l)) as [v0h v0l].
  exact I0.
Qed.

(** * Truncation and the exponential near zero *)

Lemma dwx_abs_le r a : Rabs r <= a -> - a <= r <= a.
Proof. unfold Rabs. destruct (Rcase_abs r); intros; lra. Qed.

Theorem dwx_trunc r : Rabs r <= dwx_rho -> Rabs (dwx_poly r - exp r) <= 4 / 10 * dwx_u2.
Proof.
  intros Hr. apply dwx_abs_le in Hr. unfold dwx_rho in Hr.
  unfold dwx_poly, dwx_hstep. cbn [dwx_c_hi dwx_c_lo].
  rewrite dwx_c0_hi_val, dwx_c0_lo_val, dwx_c1_hi_val, dwx_c1_lo_val, dwx_c2_hi_val, dwx_c2_lo_val,
    dwx_c3_hi_val, dwx_c3_lo_val, dwx_c4_hi_val, dwx_c4_lo_val, dwx_c5_hi_val, dwx_c5_lo_val,
    dwx_c6_hi_val, dwx_c6_lo_val, dwx_c7_hi_val, dwx_c7_lo_val, dwx_u2_val.
  interval with (i_taylor r, i_degree 10, i_prec 250).
Qed.

Lemma dwx_exp_mono a b : a <= b -> exp a <= exp b.
Proof. intros H. destruct (Req_dec a b) as [-> | N]; [lra | apply Rlt_le, exp_increasing; lra]. Qed.

(** [exp y] within [e(1 + 2e)] of 1 for [|y| <= e <= 1/1000]: [1 + x <= exp x]
    at [±e] and the exponential's monotonicity. *)
Lemma dwx_exp_small y e : Rabs y <= e -> e <= / 1000 -> Rabs (exp y - 1) <= e * (1 + 2 * e).
Proof.
  intros Hy He. apply dwx_abs_le in Hy.
  pose proof (dwx_exp_mono _ _ (proj1 Hy)) as L. pose proof (dwx_exp_mono _ _ (proj2 Hy)) as U.
  assert (E0 : 0 <= e) by lra.
  pose proof (exp_ineq1_le (- e)) as Lo.
  assert (P : exp e * exp (- e) = 1) by (rewrite <- exp_plus; replace (e + - e) with 0 by ring; apply exp_0).
  assert (Up : exp e <= 1 + e + 2 * e * e).
  { assert (G : exp e * (1 - e) <= (1 + e + 2 * e * e) * (1 - e)).
    { assert (exp e * (1 - e) <= exp e * exp (- e)) by (apply Rmult_le_compat_l; [apply Rlt_le, exp_pos | lra]).
      assert (1 <= (1 + e + 2 * e * e) * (1 - e)) by nra. lra. }
    apply Rmult_le_reg_r with (1 - e); [lra | exact G]. }
  unfold Rabs. destruct (Rcase_abs (exp y - 1)); nra.
Qed.

(** * Composition *)

(** [Z ≈ T·V], [T ≈ E], [V ≈ G] relatively by [M], [A] and [Bb]: [Z ≈ E·G]. *)
Lemma dwx_compose Z T V E G M A Bb :
  0 < E -> 0 < G -> 0 <= M -> 0 <= A -> 0 <= Bb ->
  Rabs (Z - T * V) <= M * Rabs (T * V) -> Rabs (T - E) <= A * E -> Rabs (V - G) <= Bb * G ->
  Rabs (Z - E * G) <= (M * (1 + A) * (1 + Bb) + A * (1 + Bb) + Bb) * (E * G).
Proof.
  intros E0 G0 M0 A0 B0 HZ HT HV.
  assert (Tb : Rabs T <= E * (1 + A)).
  { replace T with (E + (T - E)) by ring. pose proof (Rabs_triang E (T - E)). rewrite (Rabs_pos_eq E) in H by lra. lra. }
  assert (Vb : Rabs V <= G * (1 + Bb)).
  { replace V with (G + (V - G)) by ring. pose proof (Rabs_triang G (V - G)). rewrite (Rabs_pos_eq G) in H by lra. lra. }
  assert (TV : Rabs (T * V) <= E * (1 + A) * (G * (1 + Bb)))
    by (rewrite Rabs_mult; apply Rmult_le_compat; try apply Rabs_pos; assumption).
  assert (E1 : Rabs (Z - T * V) <= M * (E * (1 + A) * (G * (1 + Bb)))).
  { eapply Rle_trans; [exact HZ | ]. apply Rmult_le_compat_l; assumption. }
  assert (E2 : Rabs ((T - E) * V) <= A * E * (G * (1 + Bb)))
    by (rewrite Rabs_mult; apply Rmult_le_compat; try apply Rabs_pos; assumption).
  assert (E3 : Rabs (E * (V - G)) <= E * (Bb * G))
    by (rewrite Rabs_mult, (Rabs_pos_eq E) by lra; apply Rmult_le_compat_l; lra).
  replace (Z - E * G) with ((Z - T * V) + (T - E) * V + E * (V - G)) by ring.
  pose proof (Rabs_triang ((Z - T * V) + (T - E) * V) (E * (V - G))).
  pose proof (Rabs_triang (Z - T * V) ((T - E) * V)).
  replace ((M * (1 + A) * (1 + Bb) + A * (1 + Bb) + Bb) * (E * G))
    with (M * (E * (1 + A) * (G * (1 + Bb))) + A * E * (G * (1 + Bb)) + E * (Bb * G)) by ring.
  lra.
Qed.

(** The index's table entry and binary exponent. *)
Lemma dwx_scale ni : (Z.abs ni <= 2149501)%Z ->
  (Z.to_nat (Z.land ni 1023) < 1024)%nat /\ (-2100 <= Z.shiftr ni 10 <= 2099)%Z /\
  exp (IZR ni * dwx_L) = bpow radix2 (Z.shiftr ni 10) * exp (INR (Z.to_nat (Z.land ni 1023)) * ln 2 / 1024).
Proof.
  intros Hn.
  assert (Lm : Z.land ni 1023 = (ni mod 1024)%Z) by (change 1023%Z with (Z.ones 10); rewrite Z.land_ones by lia; reflexivity).
  assert (Sh : Z.shiftr ni 10 = (ni / 1024)%Z) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  rewrite Lm, Sh.
  pose proof (Z.mod_pos_bound ni 1024 ltac:(lia)) as Mb.
  pose proof (Z_div_mod_eq_full ni 1024) as D.
  split; [apply Nat2Z.inj_lt; rewrite Z2Nat.id by lia; simpl; lia | ].
  split; [Z.div_mod_to_equations; lia | ].
  rewrite INR_IZR_INZ, Z2Nat.id by lia.
  rewrite bpow_exp, <- exp_plus. f_equal.
  replace (IZR ni) with (IZR (1024 * (ni / 1024) + ni mod 1024)%Z) by (f_equal; lia).
  rewrite plus_IZR, mult_IZR. unfold dwx_L. change (IZR radix2) with 2. field.
Qed.

Lemma dwx_E_range j : (j < 1024)%nat ->
  1 <= exp (INR j * ln 2 / 1024) <= 19987 / 10000.
Proof.
  intros Hj. assert (Jr : 0 <= INR j <= 1023).
  { split; [apply pos_INR | ]. replace 1023 with (INR 1023) by (simpl; lra). apply le_INR; lia. }
  assert (L0 : 0 < ln 2) by (rewrite <- ln_1; apply ln_increasing; lra).
  split.
  - assert (0 <= INR j * ln 2 / 1024) by (unfold Rdiv; apply Rmult_le_pos; [apply Rmult_le_pos | ]; lra).
    rewrite <- exp_0. apply dwx_exp_mono. lra.
  - assert (H : INR j * ln 2 / 1024 <= 1023 * ln 2 / 1024).
    { unfold Rdiv. apply Rmult_le_compat_r; [lra | ]. apply Rmult_le_compat_r; lra. }
    apply dwx_exp_mono in H. eapply Rle_trans; [exact H | ]. interval with (i_prec 64).
Qed.

(** * The branches *)

Lemma dwx_u2_range : / 10 ^ 32 <= dwx_u2 <= / 10 ^ 31.
Proof. rewrite dwx_u2_val. split; interval with (i_prec 64). Qed.

Lemma dwx_word_sum xh xl : B xh = rndF (B xh + B xl) ->
  Rabs (B xh + B xl) <= (Rabs (B xh) + / 2 * bpow radix2 (-1074)) / (1 - / 9007199254740992).
Proof.
  intros E. pose proof (dwx_rnd_abs_err (B xh + B xl)) as R0. rewrite <- E in R0.
  replace (B xh - (B xh + B xl)) with (- B xl) in R0 by ring. rewrite Rabs_Ropp in R0.
  pose proof (Rabs_triang (B xh) (B xl)).
  apply Rmult_le_reg_r with (1 - / 9007199254740992); [lra | ].
  unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra. lra.
Qed.

Theorem dwexp_tiny_ok xh xl : finite xh -> finite xl -> B xh = rndF (B xh + B xl) -> Rabs (B xh) < B dwx_tiny ->
  let '(zh, zl) := add_f64_64 xh xl dwx_c0_hi in
  finite zh /\ finite zl /\ B zh = rndF (B zh + B zl) /\ 9996 / 10000 <= B zh + B zl < 20008 / 10000 /\
  Rabs (B zh + B zl - exp (B xh + B xl)) <= 16 * dwx_u2 * exp (B xh + B xl).
Proof.
  intros Fh Fl E Hx.
  assert (Tv : B dwx_tiny <= 868 / 1000000000000000000000) by (rewrite dwx_tiny_val; interval with (i_prec 64)).
  pose proof (dwx_word_sum xh xl E) as S.
  set (X := B xh + B xl) in *.
  assert (Xb : Rabs X <= 174 / 100000000000000000000).
  { eapply Rle_trans; [exact S | ].
    assert (/ 2 * bpow radix2 (-1074) <= / 10 ^ 300) by (interval with (i_prec 64)).
    apply Rmult_le_reg_r with (1 - / 9007199254740992); [lra | ].
    unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra. lra. }
  assert (W : forall v, Rabs v <= 4 -> Rabs v <= bpow radix2 1018).
  { intros v Hv. apply Rle_trans with (bpow radix2 2); [change (bpow radix2 2) with 4; lra | apply bpow_le; lia]. }
  pose proof (dwx_low_le _ _ E) as Bl.
  assert (C0 : B dwx_c0_hi = 1) by (rewrite dwx_c0_hi_val; field).
  pose proof (dwx_add_step xh xl dwx_c0_hi Fh Fl dwx_c0_hi_finite E ltac:(apply W; lra) ltac:(apply W; lra)
                ltac:(apply W; rewrite C0, Rabs_R1; lra)) as SA.
  destruct (add_f64_64 xh xl dwx_c0_hi) as [zh zl]. destruct SA as [Fzh [Fzl [Ez Rz]]].
  rewrite C0 in Rz. fold X in Rz.
  pose proof dwx_u2_range as U2.
  apply dwx_abs_le in Xb.
  assert (T2 : Rabs (exp X - (1 + X)) <= / 10 ^ 35) by (interval with (i_taylor X, i_prec 128)).
  assert (Eg : 99 / 100 <= exp X <= 101 / 100) by (split; interval with (i_prec 64)).
  assert (Xr : Rabs (X + 1) <= 102 / 100) by (apply Rabs_le; lra).
  assert (Zr : Rabs (B zh + B zl - (X + 1)) <= 2 * dwx_u2 * (102 / 100)).
  { eapply Rle_trans; [exact Rz | ]. apply Rmult_le_compat_l; lra. }
  split; [exact Fzh | split; [exact Fzl | split; [exact Ez | split]]].
  - apply dwx_abs_le in Zr. split; lra.
  - replace (B zh + B zl - exp X) with ((B zh + B zl - (X + 1)) + - (exp X - (1 + X))) by ring.
    pose proof (Rabs_triang (B zh + B zl - (X + 1)) (- (exp X - (1 + X)))) as T.
    rewrite Rabs_Ropp in T.
    assert (16 * dwx_u2 * (99 / 100) <= 16 * dwx_u2 * exp X) by (apply Rmult_le_compat_l; lra).
    lra.
Qed.
