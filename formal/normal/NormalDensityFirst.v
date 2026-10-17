(** normal_distribution/mod.rs's [density_first] (docs/normal.md, the
    density's first stage): [φ(x) = exp(-x²/2 - ln √(2π))] through exp's
    stage A at the exact double-word argument, transcribed on binary64 and
    proved: a value its rounding test returns is [RN(φ(x))]
    ([normal_density_first_ok]). *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Mul IEEE64Eft Encodings
  RoundingConstant RoundingTest.
Require Import StageGappa ExpStageTables ExpStageReduction ExpStageA ExpStageADw
  NormalConstants NormalCentered NormalAccurateDensity NormalGaussianKernel NormalFastDispatch.
Open Scope R_scope.

(** normal_distribution/mod.rs's [E_DENSITY_FIRST], [1.75·2^-61]. *)
Definition normal_density_first_e : f64 := b64_of_bits 4335840541250945024.
Lemma normal_density_first_e_ok :
  finite normal_density_first_e /\ B normal_density_first_e = IZR 7 * bpow radix2 (-63).
Proof.
  split; [exact (bits_finite 4335840541250945024 false 7881299347898368 (-113) eq_refl) | ].
  unfold normal_density_first_e.
  rewrite (bits_val 4335840541250945024 false 7881299347898368 113 eq_refl).
  unfold Rdiv. rewrite <- (bpow_m 113). change (-63)%Z with (50 + - Z.of_nat 113)%Z. rewrite bpow_plus.
  change (bpow radix2 50) with (IZR 1125899906842624). simpl cond_Zopp. rewrite <- Rmult_assoc, <- mult_IZR.
  reflexivity.
Qed.

(** [density_first_parts]: [(s, se, y, l, k)]. *)
Definition normal_density_first_parts64 x :=
  let '(h, l) := normal_half_square64 (b64_abs x) in
  let '(s, e) := two_sum64 h (fneg normal_ln_sqrt_2pi_hi) in
  let se := fadd e (fsub l normal_ln_sqrt_2pi_lo) in
  let '(y, w, k) := stage_a_dw_value s se in
  (s, se, y, w, k).

(** [density_first]. *)
Definition normal_density_first64 x :=
  let '(_, _, y, w, k) := normal_density_first_parts64 x in
  decide_const y w normal_density_first_e k.

Lemma normal_density_log_form v :
  normal_density v = exp (- v * v / 2 - ln (2 * PI) / 2).
Proof.
  unfold normal_density, normal_density_constant.
  assert (P : 0 < 2 * PI) by (pose proof PI_RGT_0; lra).
  assert (S : sqrt (2 * PI) = exp (ln (2 * PI) / 2)).
  { rewrite <- (sqrt_square (exp (ln (2 * PI) / 2))) by (left; apply exp_pos).
    f_equal. rewrite <- exp_plus. replace (ln (2 * PI) / 2 + ln (2 * PI) / 2) with (ln (2 * PI)) by field.
    rewrite exp_ln by exact P. reflexivity. }
  unfold Rminus. rewrite exp_plus, exp_Ropp, S.
  field. apply Rgt_not_eq, exp_pos.
Qed.

(** [|e^d - 1| <= 2|d|] for [|d| <= 2^-90]. *)
Lemma exp_near_one d : Rabs d <= bpow radix2 (-90) -> Rabs (exp d - 1) <= 2 * Rabs d.
Proof.
  intros H. change (bpow radix2 (-90)) with (/ 1237940039285380274899124224) in H.
  apply Rabs_le_inv in H as [H1 H2].
  destruct (Rle_dec 0 d) as [P | N].
  - rewrite (Rabs_pos_eq d P). pose proof (exp_ineq1_le d) as Lo.
    assert (Hi : exp d <= 1 + 2 * d).
    { pose proof (exp_ineq1_le (- d)) as Neg. pose proof (exp_pos d) as Pd.
      assert (Prod : exp d * exp (- d) = 1) by (rewrite <- exp_plus; replace (d + - d) with 0 by ring; apply exp_0).
      nra. }
    rewrite Rabs_pos_eq; lra.
  - assert (Nd : d < 0) by lra. rewrite (Rabs_left d Nd).
    pose proof (exp_ineq1_le d) as Lo.
    assert (Hi : exp d <= 1) by (rewrite <- exp_0; apply Rlt_le, exp_increasing; lra).
    rewrite Rabs_left1; lra.
Qed.

Theorem normal_density_first_ok x v : finite x ->
  bpow radix2 (-33) <= Rabs (B x) <= 37 ->
  normal_density_first64 x = Some v ->
  finite v /\ B v = rndF (normal_density (B x)).
Proof.
  intros Fx X.
  assert (Fa : finite (b64_abs x)) by (unfold b64_abs; destruct x; simpl in *; congruence).
  pose proof (B_abs x) as Ba. unfold normal_density_first64, normal_density_first_parts64.
  revert Fa Ba. generalize (b64_abs x). intros a Fa Ba.
  assert (Xa : bpow radix2 (-400) <= B a <= 39).
  { rewrite Ba. split; [apply Rle_trans with (bpow radix2 (-33)); [apply bpow_le; lia | lra] | lra]. }
  pose proof (normal_half_square_exact a Fa Xa) as Sq.
  revert Sq. generalize (normal_half_square64 a). intros [h l] Sq.
  destruct Sq as [Fh [Fl [HL [_ Hl]]]].
  assert (Hh : Rabs (B h) <= 685).
  { assert (Q : Rabs (B h + B l) <= 684.5).
    { rewrite HL, Ba. pose proof (Rabs_pos (B x)). rewrite Rabs_left1 by nra. nra. }
    replace (B h) with ((B h + B l) + - B l) by ring.
    apply Rle_trans with (1 := Rabs_triang _ _). rewrite Rabs_Ropp.
    change (bpow radix2 (-44)) with (/ 17592186044416) in Hl. lra. }
  destruct normal_ln_sqrt_2pi_hi_ok as [Fchi Chi].
  destruct normal_ln_sqrt_2pi_lo_ok as [Fclo Clo].
  assert (Fnchi : finite (fneg normal_ln_sqrt_2pi_hi)) by (unfold fneg, b64_opp; rewrite is_finite_Bopp; exact Fchi).
  assert (Bnchi : B (fneg normal_ln_sqrt_2pi_hi) = - B normal_ln_sqrt_2pi_hi) by apply B2R_Bopp.
  assert (Chir : 0.91 <= B normal_ln_sqrt_2pi_hi <= 0.92) by (rewrite Chi; split; interval with (i_prec 80)).
  assert (Clor : Rabs (B normal_ln_sqrt_2pi_lo) <= bpow radix2 (-54)) by (rewrite Clo; bpow_num; interval with (i_prec 80)).
  pose proof (two_sum_ieee h (fneg normal_ln_sqrt_2pi_hi) Fh Fnchi
    ltac:(apply Rle_trans with 685; [exact Hh | bpow_num; lra])
    ltac:(rewrite Bnchi, Rabs_Ropp, Rabs_pos_eq by lra; bpow_num; lra)) as Sum.
  revert Sum. generalize (two_sum64 h (fneg normal_ln_sqrt_2pi_hi)). intros [s e] Sum.
  destruct Sum as [Fs [Fe [Bs Se]]]. rewrite Bnchi in Bs, Se.
  assert (Vs : Rabs (B h + - B normal_ln_sqrt_2pi_hi) <= bpow radix2 10).
  { bpow_num. apply Rle_trans with (1 := Rabs_triang _ _). rewrite Rabs_Ropp, (Rabs_pos_eq (B normal_ln_sqrt_2pi_hi)) by lra. lra. }
  assert (He : Rabs (B e) <= bpow radix2 (-44)).
  { pose proof (rnd_err_below _ 10 ltac:(lia) Vs) as E. rewrite <- Bs in E.
    replace (B e) with (- (B s - (B h + - B normal_ln_sqrt_2pi_hi))) by lra.
    rewrite Rabs_Ropp. change (10 - 54)%Z with (-44)%Z in E. exact E. }
  assert (Hs : Rabs (B s) < 704).
  { change (bpow radix2 (-44)) with (/ 17592186044416) in He.
    replace (B s) with (B h - B normal_ln_sqrt_2pi_hi - B e) by lra.
    apply Rabs_le_inv in Hh. apply Rabs_le_inv in He. apply Rabs_def1; lra. }
  (* the low word *)
  destruct (fsub16 l normal_ln_sqrt_2pi_lo Fl Fclo) as [Fw Bw].
  { apply Rle_trans with (1 := Rabs_triang _ _). rewrite Rabs_Ropp. bpow_num_all. lra. }
  assert (Vw : Rabs (B l - B normal_ln_sqrt_2pi_lo) <= bpow radix2 (-43)).
  { unfold Rminus. apply Rle_trans with (1 := Rabs_triang _ _). rewrite Rabs_Ropp. bpow_num_all. lra. }
  assert (Ew : Rabs (B (fsub l normal_ln_sqrt_2pi_lo) - (B l - B normal_ln_sqrt_2pi_lo)) <= bpow radix2 (-97)).
  { rewrite Bw. exact (rnd_err_below _ (-43) ltac:(lia) Vw). }
  set (w := fsub l normal_ln_sqrt_2pi_lo) in *.
  destruct (fadd16 e w Fe Fw) as [Fse Bse].
  { apply Rle_trans with (1 := Rabs_triang _ _). apply Rabs_le_inv in Ew. bpow_num_all.
    apply Rle_trans with (/ 17592186044416 + (/ 8796093022208 + / 158456325028528675187087900672)); [ | lra].
    apply Rplus_le_compat; [lra | ]. apply Rabs_le. split; apply Rabs_le_inv in Vw; lra. }
  set (se := fadd e w) in *.
  assert (Vse : Rabs (B e + B w) <= bpow radix2 (-42)).
  { apply Rle_trans with (1 := Rabs_triang _ _). apply Rabs_le_inv in Ew. apply Rabs_le_inv in Vw. bpow_num_all.
    assert (Rabs (B w) <= / 8796093022208 + / 158456325028528675187087900672) by (apply Rabs_le; lra). lra. }
  assert (Hse : Rabs (B se) <= bpow radix2 (-42)).
  { rewrite Bse. apply abs_round_le_generic; auto with typeclass_instances.
    apply generic_format_bpow. unfold FLT_exp, emin, prec. lia. }
  assert (Ese : Rabs (B se - (B e + B w)) <= bpow radix2 (-96)).
  { rewrite Bse. exact (rnd_err_below _ (-42) ltac:(lia) Vse). }
  (* the argument's error *)
  set (C := ln (2 * PI) / 2).
  assert (Cerr : Rabs (B normal_ln_sqrt_2pi_hi + B normal_ln_sqrt_2pi_lo - C) <= bpow radix2 (-105)).
  { pose proof normal_ln_sqrt_2pi_dw_error as D. fold C in D.
    assert (Cr : 0.9 <= C <= 1) by (unfold C; split; interval with (i_prec 80)).
    replace (B normal_ln_sqrt_2pi_hi + B normal_ln_sqrt_2pi_lo - C) with
      (((B normal_ln_sqrt_2pi_hi + B normal_ln_sqrt_2pi_lo) / C - 1) * C) by (field; lra).
    rewrite Rabs_mult, (Rabs_pos_eq C) by lra. pose proof (bpow_gt_0 radix2 (-105)). nra. }
  set (delta := B s + B se - (- B a * B a / 2 - C)).
  assert (Hdelta : Rabs delta <= bpow radix2 (-95)).
  { unfold delta. rewrite <- HL.
    replace (B s + B se - (B h + B l - C)) with
      ((B se - (B e + B w)) + (B w - (B l - B normal_ln_sqrt_2pi_lo))
       - (B normal_ln_sqrt_2pi_hi + B normal_ln_sqrt_2pi_lo - C)) by lra.
    apply Rabs_le_inv in Ese. apply Rabs_le_inv in Ew. apply Rabs_le_inv in Cerr. bpow_num_all. apply Rabs_le. lra. }
  (* stage A at the double-word argument *)
  pose proof (stage_a_dw_value_ok s se Fs Hs Fse Hse) as A.
  revert A. generalize (stage_a_dw_value s se). intros [[y yl] k] A.
  destruct A as [ni [j [Nk [Hj [Hk [Fy [Fyl [Hy [Hyl [HR HZ]]]]]]]]]].
  set (R := B s + B se - IZR ni * L) in *.
  set (T := exp (INR j * ln 2 / 512)) in *.
  set (Z := T * exp (R - delta)).
  assert (Density : normal_density (B x) = Z * bpow radix2 k).
  { rewrite <- normal_density_abs, <- Ba, normal_density_log_form. unfold Z, T.
    rewrite <- exp_split. f_equal. rewrite <- Nk. unfold R, delta. fold C. ring. }
  assert (Hd' : Rabs delta <= bpow radix2 (-90)).
  { apply Rle_trans with (1 := Hdelta). apply bpow_le. lia. }
  assert (Zerr : Rabs (Z - (B y + B yl)) <= IZR 23 * bpow radix2 (-65) + bpow radix2 (-92)).
  { assert (Tr : 9 / 10 <= T * exp R <= 21 / 10) by (apply z_range_dw; [exact Hj | apply Rle_trans with 0.000677; [exact HR | lra]]).
    unfold Z. replace (exp (R - delta)) with (exp R * exp (- delta)) by (rewrite <- exp_plus; f_equal; ring).
    replace (T * (exp R * exp (- delta)) - (B y + B yl)) with
      ((T * exp R - (B y + B yl)) + T * exp R * (exp (- delta) - 1)) by ring.
    apply Rle_trans with (1 := Rabs_triang _ _). apply Rplus_le_compat; [exact HZ | ].
    rewrite Rabs_mult, (Rabs_pos_eq (T * exp R)) by lra.
    pose proof (exp_near_one (- delta) ltac:(rewrite Rabs_Ropp; exact Hd')) as En. rewrite Rabs_Ropp in En.
    apply Rle_trans with (21 / 10 * (2 * bpow radix2 (-95))).
    - apply Rmult_le_compat; [lra | apply Rabs_pos | lra | ].
      clear - En Hdelta. lra.
    - clear. bpow_num. lra. }
  destruct normal_density_first_e_ok as [Fe' Ev].
  intros Hd. rewrite Density.
  assert (Zr : 9 / 10 <= Z <= 21 / 10).
  { unfold Z. apply z_range_dw; [exact Hj | ].
    replace (R - delta) with (R + - delta) by ring.
    apply Rle_trans with (1 := Rabs_triang _ _). rewrite Rabs_Ropp.
    clear - HR Hdelta. bpow_num_all. lra. }
  assert (Yl : Rabs (B yl) + B normal_density_first_e <= bpow radix2 (-9)).
  { rewrite Ev. clear - Hyl. bpow_num_all. lra. }
  assert (Eps : IZR 23 * bpow radix2 (-65) + bpow radix2 (-92) + bpow radix2 (-9 - 54) <= B normal_density_first_e).
  { rewrite Ev. clear. change (-9 - 54)%Z with (-63)%Z. bpow_num. lra. }
  assert (E0 : 0 <= B normal_density_first_e).
  { rewrite Ev. clear. pose proof (bpow_ge_0 radix2 (-63)). lra. }
  exact (decide_const_ok y yl normal_density_first_e k Z (IZR 23 * bpow radix2 (-65) + bpow radix2 (-92)) (-9) v
           Fy Fyl Fe' Hy ltac:(lia) E0 Yl Eps Zerr Zr Hk Hd).
Qed.
