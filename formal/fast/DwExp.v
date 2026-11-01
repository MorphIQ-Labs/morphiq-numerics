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
