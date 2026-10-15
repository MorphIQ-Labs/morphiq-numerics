(** normal_distribution/mod.rs's [tail_first] (docs/normal.md, the CDF
    family's first stage): [q = Φ(-a) = exp(-a²/2)·erfcx(a/√2)/2] with the
    Gaussian through exp's stage A at the exact double-word [-a²/2], one exact
    product with the fast scaled erfcx and binary64 cross terms, then [q],
    [1 - q] or [±(1/2 - q)] and an interval rounding test, transcribed on
    binary64 and proved:
    - [normal_tail_first_parts_ok]: the scaled words [qh + ql] are within
      [33·2^-64] of [q] relatively, for [1/2 < |x| <= 36];
    - [normal_tail_first_ok]: a value the test returns is the correctly
      rounded CDF or centered CDF. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add Binary64Mul IEEE64 IEEE64Add IEEE64Mul IEEE64Eft Encodings
  RoundingConstant RoundingTest RoundingCore.
Require Import StageGappa ExpStageTables ExpStageReduction ExpStageA ExpStageADw
  ErfcxDecision ErfcxGaussianTarget NormalComparisons NormalGaussianKernel NormalErfcxFastScaled
  NormalTailAnalytic NormalTailRange NormalTailScale NormalFastDecision NormalFastDispatch.
Open Scope R_scope.

(** normal_distribution/mod.rs's [E_TAIL_FIRST], [2^-58], and
    [E_TAIL_FIRST_ONE], [2^-100]. *)
Definition normal_tail_first_e : f64 := b64_of_bits 4345973640412528640.
Lemma normal_tail_first_e_ok : finite normal_tail_first_e /\ B normal_tail_first_e = bpow radix2 (-58).
Proof.
  split; [exact (bits_finite 4345973640412528640 false 4503599627370496 (-110) eq_refl) | ].
  unfold normal_tail_first_e. rewrite (bits_val 4345973640412528640 false 4503599627370496 110 eq_refl).
  unfold Rdiv. rewrite <- (bpow_m 110). change (-58)%Z with (52 + - Z.of_nat 110)%Z. rewrite bpow_plus.
  change (bpow radix2 52) with (IZR 4503599627370496). simpl cond_Zopp. reflexivity.
Qed.
Definition normal_tail_first_one : f64 := b64_of_bits 4156822456062967808.
Lemma normal_tail_first_one_ok : finite normal_tail_first_one /\ B normal_tail_first_one = bpow radix2 (-100).
Proof.
  split; [exact (bits_finite 4156822456062967808 false 4503599627370496 (-152) eq_refl) | ].
  unfold normal_tail_first_one. rewrite (bits_val 4156822456062967808 false 4503599627370496 152 eq_refl).
  unfold Rdiv. rewrite <- (bpow_m 152). change (-100)%Z with (52 + - Z.of_nat 152)%Z. rewrite bpow_plus.
  change (bpow radix2 52) with (IZR 4503599627370496). simpl cond_Zopp. reflexivity.
Qed.

(** [tail_first_parts]: [(qh, ql)]. *)
Definition normal_tail_first_parts64 x :=
  let '(h, l) := normal_half_square64 (b64_abs x) in
  let '(ye, le, k) := stage_a_dw_value h l in
  let '(fh, fl) := normal_erfcx_fast_scaled64 (b64_abs x) in
  let '(p, pe) := two_prod64 ye fh in
  let pl := fadd pe (fadd (fmul ye fl) (fmul le fh)) in
  (fmul p (erfcx_pow2 (k - 1)), fmul pl (erfcx_pow2 (k - 1))).

(** [tail_first]. *)
Definition normal_tail_first64 op x :=
  let '(qh, ql) := normal_tail_first_parts64 x in
  let e := fmul qh normal_tail_first_e in
  match op with
  | NormalCdf =>
      if normal_lt x normal_zero then normal_interval_decide64 qh ql e
      else let '(s, t) := fast_two_sum64 (erfcx_pow2 0) (fneg qh) in
        normal_interval_decide64 s (fsub t ql) (fadd e normal_tail_first_one)
  | NormalCentered =>
      let '(s, t) := fast_two_sum64 (erfcx_pow2 (-1)) (fneg qh) in
      let w := fsub t ql in
      let e' := fadd e normal_tail_first_one in
      if Bsign 53 1024 x then normal_interval_decide64 (fneg s) (fneg w) e'
      else normal_interval_decide64 s w e'
  | _ => None
  end.

(** Rounding to nearest anywhere: relative in the normal range, absolute
    below it. *)
Lemma rnd_err_any v : Rabs (rndF v - v) <= bpow radix2 (-53) * Rabs v + bpow radix2 (-1075).
Proof.
  destruct (Rle_lt_dec (bpow radix2 (-1022)) (Rabs v)) as [N | S].
  - pose proof (rnd_rel v N) as R.
    change (round radix2 (FLT_exp (-1074) 53) (Znearest (fun n => negb (Z.even n))) v) with (rndF v) in R.
    pose proof (bpow_gt_0 radix2 (-1075)). lra.
  - pose proof (rnd_err_below v (-1021) ltac:(lia) ltac:(apply Rlt_le, Rlt_le_trans with (1 := S); apply bpow_le; lia)) as R.
    change (-1021 - 54)%Z with (-1075)%Z in R. pose proof (Rabs_pos v).
    pose proof (bpow_ge_0 radix2 (-53)). nra.
Qed.

Lemma neg_finite w : finite w -> finite (fneg w).
Proof. intros Fw. unfold fneg, b64_opp. rewrite is_finite_Bopp. exact Fw. Qed.
Lemma neg_value w : B (fneg w) = - B w.
Proof. apply B2R_Bopp. Qed.

Theorem normal_tail_first_parts_ok x : finite x -> /2 < Rabs (B x) <= 36 ->
  let '(qh, ql) := normal_tail_first_parts64 x in
  finite qh /\ finite ql /\ bpow radix2 (-960) <= B qh <= 2 / 5 /\
  Rabs (B ql) <= / 256 * B qh /\ 0 < normal_tail (Rabs (B x)) <= 3 / 8 /\
  Rabs (B qh + B ql - normal_tail (Rabs (B x))) <= IZR 33 * bpow radix2 (-64) * normal_tail (Rabs (B x)).
Proof.
  intros Fx X.
  assert (Fa : finite (b64_abs x)) by (unfold b64_abs; destruct x; simpl in *; congruence).
  pose proof (B_abs x) as Ba. unfold normal_tail_first_parts64.
  revert Fa Ba. generalize (b64_abs x). intros a Fa Ba.
  assert (Xa : bpow radix2 (-400) <= B a <= 39).
  { rewrite Ba. split; [apply Rle_trans with (/2); [bpow_num; lra | lra] | lra]. }
  assert (Xe : /2 <= B a <= 37) by (rewrite Ba; lra).
  pose proof (normal_half_square_exact a Fa Xa) as Sq.
  revert Sq. generalize (normal_half_square64 a). intros [h l] Sq.
  destruct Sq as [Fh [Fl [HL [_ Hl]]]].
  assert (Hsum : - 648 <= B h + B l < - / 8).
  { rewrite HL, Ba. pose proof (Rabs_pos (B x)). split; nra. }
  assert (Hh : Rabs (B h) < 704).
  { change (bpow radix2 (-44)) with (/ 17592186044416) in Hl. apply Rabs_le_inv in Hl. apply Rabs_def1; lra. }
  assert (Hl' : Rabs (B l) <= bpow radix2 (-42)) by (apply Rle_trans with (1 := Hl); apply bpow_le; lia).
  pose proof (stage_a_dw_value_ok h l Fh Hh Fl Hl') as SA.
  revert SA. generalize (stage_a_dw_value h l). intros [[ye le] k] SA.
  destruct SA as [ni [j [Nk [Hj [Hk [Fye [Fle [Hye [Hle [HR HZ]]]]]]]]]].
  set (R := B h + B l - IZR ni * L) in *.
  set (T := exp (INR j * ln 2 / 512)) in *.
  set (Z := T * exp R) in *.
  assert (Zr : 9 / 10 <= Z <= 21 / 10) by (apply z_range_dw; [exact Hj | lra]).
  (* the scale: -936 <= k <= -1 *)
  assert (Lr : 0.0013537 <= L <= 0.0013539) by (unfold L; split; interval with (i_prec 64)).
  assert (NiL : - 648.001 <= IZR ni * L <= - / 8 + 0.000677).
  { apply Rabs_le_inv in HR. unfold R in HR. split; lra. }
  assert (Kr : (-936 <= k <= -1)%Z).
  { assert (N1 : (-478700 <= ni)%Z).
    { apply le_IZR. apply Rle_trans with (- 648.001 / L); [ | apply Rmult_le_reg_r with L; [lra | ]; unfold Rdiv; rewrite Rmult_assoc, Rinv_l by lra; lra].
      apply Rmult_le_reg_r with L; [lra | ]. unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. nra. }
    assert (N2 : (ni <= -1)%Z).
    { assert (Hn : IZR ni < IZR 0) by (simpl; nra). apply lt_IZR in Hn. lia. }
    lia. }
  (* the scaled erfcx *)
  pose proof (normal_erfcx_fast_scaled_ieee a Fa Xe) as Er.
  revert Er. generalize (normal_erfcx_fast_scaled64 a). intros [fh fl] Er.
  destruct Er as [Ffh [Ffl [Fn [Fhr [Flr FG]]]]].
  set (G := gaussian_erfcx (B a / sqrt 2)) in *.
  set (F := B fh + B fl) in *.
  assert (Fpos : bpow radix2 (-9) - bpow radix2 (-53) <= F) by (unfold F; apply Rabs_le_inv in Flr; lra).
  assert (Gpos : 0 < G).
  { apply Rabs_le_inv in FG. bpow_num_all. nra. }
  assert (FleG : F <= (1 + bpow radix2 (-66)) * G) by (apply Rabs_le_inv in FG; lra).
  assert (GleF : G <= 2 * F) by (apply Rabs_le_inv in FG; bpow_num_all; nra).
  assert (FlRel : Rabs (B fl) <= bpow radix2 (-53) * F).
  { pose proof (rnd_rel F ltac:(rewrite Rabs_pos_eq by (bpow_num_all; lra); apply Rle_trans with (2 := Fpos); bpow_num; lra)) as RF.
    change (round radix2 (FLT_exp (-1074) 53) (Znearest (fun n => negb (Z.even n))) F) with (rndF F) in RF.
    unfold F in *. rewrite <- Fn in RF. replace (B fh - (B fh + B fl)) with (- B fl) in RF by ring.
    rewrite Rabs_Ropp, (Rabs_pos_eq (B fh + B fl)) in RF by (bpow_num_all; lra). exact RF. }
  (* ye's range *)
  assert (Yr : 0.89 <= B ye <= 2.2).
  { apply Rabs_le_inv in HZ. change (bpow radix2 (-17)) with (/ 131072) in Hle. change (bpow radix2 (-65)) with (/ 36893488147419103232) in HZ.
    apply Rabs_le_inv in Hle. split; lra. }
  (* the exact product *)
  pose proof (two_prod_ieee 2 1 ye fh Fye Ffh
    ltac:(change (bpow radix2 2) with 4; rewrite Rabs_pos_eq; lra)
    ltac:(change (bpow radix2 1) with 2; rewrite Rabs_pos_eq; [lra | bpow_num_all; lra])
    ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(right; rewrite Rabs_pos_eq by (bpow_num_all; nra); bpow_num_all; nra)) as TP.
  revert TP. generalize (two_prod64 ye fh). intros [p pe] TP.
  destruct TP as [Fp [Fpe [Bp Ppe]]].
  set (W := B ye * B fh) in *.
  assert (Wr : 0.89 * bpow radix2 (-9) <= W <= 4.4) by (unfold W; bpow_num_all; split; nra).
  assert (Hpe : Rabs (B pe) <= bpow radix2 (-53) * W).
  { replace (B pe) with (- (rndF W - W)) by (rewrite <- Bp; lra). rewrite Rabs_Ropp.
    pose proof (rnd_rel W ltac:(rewrite Rabs_pos_eq by (bpow_num_all; nra); apply Rle_trans with (2 := proj1 Wr); bpow_num; lra)) as RW.
    rewrite (Rabs_pos_eq W) in RW by (bpow_num_all; nra). exact RW. }
  (* the cross terms *)
  destruct (fmul16 ye fl Fye Ffl) as [Fm1 Bm1].
  { rewrite Rabs_mult, (Rabs_pos_eq (B ye)) by lra. apply Rle_trans with (2.2 * 1); [ | lra].
    apply Rmult_le_compat; try apply Rabs_pos; bpow_num_all; lra. }
  destruct (fmul16 le fh Fle Ffh) as [Fm2 Bm2].
  { rewrite Rabs_mult, (Rabs_pos_eq (B fh)) by (bpow_num_all; lra). apply Rle_trans with (1 * 2); [ | lra].
    apply Rmult_le_compat; try apply Rabs_pos; bpow_num_all; lra. }
  set (m1 := fmul ye fl) in *. set (m2 := fmul le fh) in *.
  assert (Fhf : B fh <= F * (1 + bpow radix2 (-52))).
  { apply Rabs_le_inv in FlRel. unfold F in *. bpow_num_all. nra. }
  assert (Fle2 : F <= 2.01) by (unfold F; apply Rabs_le_inv in Flr; bpow_num_all; lra).
  assert (Fge : 0 < F) by (bpow_num_all; lra).
  change (bpow radix2 (-17)) with (/ 131072) in Hle.
  assert (V1 : Rabs (B ye * B fl) <= 2.2 * (bpow radix2 (-53) * F)).
  { rewrite Rabs_mult, (Rabs_pos_eq (B ye)) by lra. apply Rmult_le_compat; try apply Rabs_pos; lra. }
  assert (V2 : Rabs (B le * B fh) <= 0.00139 * F).
  { rewrite Rabs_mult, (Rabs_pos_eq (B fh)) by (bpow_num_all; lra).
    apply Rle_trans with (181 * / 131072 * (F * (1 + bpow radix2 (-52)))).
    - pose proof (bpow_gt_0 radix2 (-9)). apply Rmult_le_compat; try apply Rabs_pos; lra.
    - bpow_num_all. nra. }
  assert (E1 : Rabs (B m1 - B ye * B fl) <= bpow radix2 (-53) * (2.2 * (bpow radix2 (-53) * F)) + bpow radix2 (-1075)).
  { rewrite Bm1. pose proof (rnd_err_any (B ye * B fl)) as R1. pose proof (bpow_ge_0 radix2 (-53)). nra. }
  assert (E2 : Rabs (B m2 - B le * B fh) <= bpow radix2 (-53) * (0.00139 * F) + bpow radix2 (-1075)).
  { rewrite Bm2. pose proof (rnd_err_any (B le * B fh)) as R2. pose proof (bpow_ge_0 radix2 (-53)). nra. }
  assert (A1 : Rabs (B m1) <= bpow radix2 (-50) * F).
  { clear - E1 V1 Fge Fpos. apply Rabs_le_inv in E1. apply Rabs_le_inv in V1. bpow_num_all. apply Rabs_le. split; lra. }
  assert (A2 : Rabs (B m2) <= 0.001391 * F).
  { clear - E2 V2 Fge Fpos. apply Rabs_le_inv in E2. apply Rabs_le_inv in V2. bpow_num_all. apply Rabs_le. split; lra. }
  destruct (fadd16 m1 m2 Fm1 Fm2) as [Fs1 Bs1].
  { apply Rle_trans with (1 := Rabs_triang _ _). clear - A1 A2 Fle2 Fge. bpow_num_all. lra. }
  set (s1 := fadd m1 m2) in *.
  assert (Vs1 : Rabs (B m1 + B m2) <= 0.001392 * F).
  { apply Rle_trans with (1 := Rabs_triang _ _). clear - A1 A2 Fge. bpow_num_all. lra. }
  assert (Es1 : Rabs (B s1 - (B m1 + B m2)) <= bpow radix2 (-53) * (0.001392 * F) + bpow radix2 (-1075)).
  { rewrite Bs1. pose proof (rnd_err_any (B m1 + B m2)) as R3. pose proof (bpow_ge_0 radix2 (-53)). nra. }
  assert (As1 : Rabs (B s1) <= 0.001393 * F).
  { clear - Es1 Vs1 Fge Fpos. apply Rabs_le_inv in Es1. apply Rabs_le_inv in Vs1. bpow_num_all. apply Rabs_le. split; lra. }
  assert (Ape : Rabs (B pe) <= bpow radix2 (-50) * F).
  { apply Rle_trans with (1 := Hpe).
    assert (Wb : W <= 2.2 * (F * (1 + bpow radix2 (-52)))).
    { change W with (B ye * B fh). pose proof (bpow_gt_0 radix2 (-9)). apply Rmult_le_compat; lra. }
    clear - Wb Fge. bpow_num_all. lra. }
  destruct (fadd16 pe s1 Fpe Fs1) as [Fpl Bpl].
  { apply Rle_trans with (1 := Rabs_triang _ _). clear - Ape As1 Fle2 Fge. bpow_num_all. lra. }
  set (pl := fadd pe s1) in *.
  assert (Vpl : Rabs (B pe + B s1) <= 0.001394 * F).
  { apply Rle_trans with (1 := Rabs_triang _ _). clear - Ape As1 Fge. bpow_num_all. lra. }
  assert (Epl : Rabs (B pl - (B pe + B s1)) <= bpow radix2 (-53) * (0.001394 * F) + bpow radix2 (-1075)).
  { rewrite Bpl. pose proof (rnd_err_any (B pe + B s1)) as R4. pose proof (bpow_ge_0 radix2 (-53)). nra. }
  assert (Apl : Rabs (B pl) <= 0.001395 * F).
  { clear - Epl Vpl Fge Fpos. apply Rabs_le_inv in Epl. apply Rabs_le_inv in Vpl. bpow_num_all. apply Rabs_le. split; lra. }
  (* P = p + pl against Y·F *)
  set (Y := B ye + B le).
  assert (Tiny : bpow radix2 (-1075) <= bpow radix2 (-1000) * F).
  { clear - Fpos. bpow_num_all. lra. }
  assert (PYF : Rabs (B p + B pl - Y * F) <= IZR 23 * bpow radix2 (-65) * F).
  { assert (Id : B p + B pl - Y * F =
      (B pl - (B pe + B s1)) + (B s1 - (B m1 + B m2)) + (B m1 - B ye * B fl) + (B m2 - B le * B fh) - B le * B fl).
    { unfold Y, F. change W with (B ye * B fh) in Ppe. replace (B pe) with (B ye * B fh - B p) by lra. ring. }
    rewrite Id.
    assert (Lf : Rabs (B le * B fl) <= 0.00139 * (bpow radix2 (-53) * F)).
    { rewrite Rabs_mult. apply Rmult_le_compat; try apply Rabs_pos; [lra | exact FlRel]. }
    clear - Epl Es1 E1 E2 Lf Fge Tiny. apply Rabs_le_inv in Epl. apply Rabs_le_inv in Es1. apply Rabs_le_inv in E1. apply Rabs_le_inv in E2.
    apply Rabs_le_inv in Lf. bpow_num_all. apply Rabs_le. split; lra. }
  (* Y·F against Z·G, then P against Z·G *)
  assert (YFZG : Rabs (Y * F - Z * G) <= IZR 23 * bpow radix2 (-65) * F + Z * (bpow radix2 (-66) * G)).
  { replace (Y * F - Z * G) with ((Y - Z) * F + Z * (F - G)) by ring.
    apply Rle_trans with (1 := Rabs_triang _ _). rewrite !Rabs_mult, (Rabs_pos_eq F), (Rabs_pos_eq Z) by lra.
    rewrite Rabs_minus_sym in HZ. fold Y in HZ.
    apply Rplus_le_compat; [apply Rmult_le_compat_r; lra | apply Rmult_le_compat_l; lra]. }
  assert (FZG : F <= 1.12 * (Z * G)).
  { clear - FleG Zr Gpos. bpow_num_all. nra. }
  assert (PZG : Rabs (B p + B pl - Z * G) <= bpow radix2 (-59) * (Z * G)).
  { replace (B p + B pl - Z * G) with ((B p + B pl - Y * F) + (Y * F - Z * G)) by ring.
    apply Rle_trans with (1 := Rabs_triang _ _). clear - PYF YFZG FZG Zr Gpos Fge. bpow_num_all. nra. }
  (* the target *)
  set (Q := normal_tail (Rabs (B x))).
  assert (Qv : Q = Z * G * bpow radix2 (k - 1)).
  { unfold Q, normal_tail. rewrite <- Ba. fold G.
    assert (Ex : exp (- B a * B a / 2) = Z * bpow radix2 k).
    { rewrite <- HL. unfold Z, T. rewrite <- exp_split. f_equal. rewrite <- Nk. unfold R. ring. }
    rewrite Ex. change (k - 1)%Z with (k + -1)%Z. rewrite bpow_plus. change (bpow radix2 (-1)) with (/ 2). field. }
  pose proof (normal_tail_outer_range (Rabs (B x)) ltac:(lra)) as QR. fold Q in QR.
  (* the scaling *)
  assert (Pb : Rabs (B p) <= 8).
  { rewrite Bp. pose proof (rnd_err_any W) as RW. assert (W0 : 0 <= W) by (clear - Wr; bpow_num_all; lra).
    rewrite (Rabs_pos_eq W) in RW by exact W0. clear - RW Wr W0. apply Rabs_le_inv in RW. bpow_num_all. apply Rabs_le. split; lra. }
  assert (PLb : Rabs (B pl) <= 8) by (clear - Apl Fle2 Fge; apply Rabs_le_inv in Apl; apply Rabs_le; split; lra).
  pose proof (normal_tail_scaled_word_ieee p (k - 1) Fp Pb ltac:(lia)) as Sh.
  pose proof (normal_tail_scaled_word_ieee pl (k - 1) Fpl PLb ltac:(lia)) as Sl.
  destruct Sh as [Fqh [_ [_ [_ Exh]]]]. destruct Sl as [Fql [_ [_ [Eql _]]]].
  set (s := bpow radix2 (k - 1)) in *.
  assert (Sp : 0 < s) by apply bpow_gt_0.
  assert (Pr : bpow radix2 (-20) <= Rabs (B p)).
  { rewrite Bp. pose proof (rnd_err_any W) as RW. rewrite Rabs_pos_eq.
    - apply Rabs_le_inv in RW. bpow_num_all. rewrite Rabs_pos_eq in RW by nra. nra.
    - apply Rabs_le_inv in RW. bpow_num_all. rewrite Rabs_pos_eq in RW by nra. nra. }
  specialize (Exh Pr). set (qh := fmul p (erfcx_pow2 (k - 1))) in *. set (ql := fmul pl (erfcx_pow2 (k - 1))) in *.
  assert (Sk : s <= bpow radix2 (-2)) by (apply bpow_le; lia).
  assert (Sk2 : bpow radix2 (-937) <= s) by (apply bpow_le; lia).
  assert (ZG : 0.89 * (bpow radix2 (-9) - bpow radix2 (-53)) / 2 <= Z * G).
  { assert (G >= F / (1 + bpow radix2 (-66))) by (apply Rle_ge; apply Rmult_le_reg_r with (1 + bpow radix2 (-66)); [bpow_num; lra | unfold Rdiv; rewrite Rmult_assoc, Rinv_l by (bpow_num; lra); lra]).
    bpow_num_all. nra. }
  assert (Total : Rabs (B qh + B ql - Q) <= IZR 33 * bpow radix2 (-64) * Q).
  { rewrite Exh, Qv.
    replace (B p * s + B ql - Z * G * s) with ((B p + B pl - Z * G) * s + (B ql - B pl * s)) by ring.
    apply Rle_trans with (1 := Rabs_triang _ _). rewrite Rabs_mult, (Rabs_pos_eq s) by lra.
    assert (Eqs : bpow radix2 (k - 1 - 84) <= bpow radix2 (-70) * (Z * G * s)).
    { replace (k - 1 - 84)%Z with (-84 + (k - 1))%Z by ring. rewrite bpow_plus. fold s.
      replace (bpow radix2 (-70) * (Z * G * s)) with (bpow radix2 (-70) * (Z * G) * s) by ring.
      apply Rmult_le_compat_r; [lra | ]. clear - ZG. bpow_num_all. lra. }
    assert (ZGs : 0 <= Z * G * s) by (apply Rmult_le_pos; [apply Rmult_le_pos | ]; lra).
    apply Rle_trans with (bpow radix2 (-59) * (Z * G) * s + bpow radix2 (-70) * (Z * G * s)).
    - apply Rplus_le_compat; [apply Rmult_le_compat_r; lra | lra].
    - clear - ZGs. bpow_num_all. lra. }
  assert (W0 : 0 <= W) by (clear - Wr; bpow_num_all; lra).
  assert (Pw : W * (1 - bpow radix2 (-52)) <= B p).
  { rewrite Bp. pose proof (rnd_err_any W) as RW. rewrite (Rabs_pos_eq W) in RW by exact W0.
    clear - RW Wr W0. apply Rabs_le_inv in RW. bpow_num_all. lra. }
  assert (Qql : Rabs (B ql) <= 0.0016 * Q).
  { rewrite Qv. replace (k - 1 - 84)%Z with (-84 + (k - 1))%Z in Eql by ring. rewrite bpow_plus in Eql. fold s in Eql.
    replace (B ql) with ((B ql - B pl * s) + B pl * s) by ring.
    apply Rle_trans with (1 := Rabs_triang _ _). rewrite Rabs_mult, (Rabs_pos_eq s) by lra.
    apply Rle_trans with ((bpow radix2 (-84) + Rabs (B pl)) * s); [lra | ].
    replace (0.0016 * (Z * G * s)) with ((0.0016 * (Z * G)) * s) by ring.
    apply Rmult_le_compat_r; [lra | ]. clear - Apl FZG ZG. bpow_num_all. lra. }
  repeat split; try assumption; try lra.
  - (* qh lower bound *)
    rewrite Exh. apply Rle_trans with (0.89 * bpow radix2 (-9) * (1 - bpow radix2 (-52)) * bpow radix2 (-937)).
    + clear. bpow_num. lra.
    + apply Rmult_le_compat; [clear; bpow_num; lra | clear; bpow_num; lra | | exact Sk2].
      apply Rle_trans with (2 := Pw). apply Rmult_le_compat_r; [clear; bpow_num; lra | ].
      clear - Wr. bpow_num_all. lra.
  - (* qh upper bound *)
    clear - Total Qql QR. apply Rabs_le_inv in Total. apply Rabs_le_inv in Qql. bpow_num_all. lra.
  - (* ql relative to qh *)
    clear - Total Qql QR. apply Rabs_le_inv in Total. pose proof Qql as Q2. apply Rabs_le_inv in Q2. bpow_num_all.
    apply Rle_trans with (1 := Qql). lra.
Qed.

Lemma normal_tail_first_sign x : finite x -> if Bsign 53 1024 x then B x <= 0 else 0 <= B x.
Proof.
  intros Fx; destruct x as [s|s|s p Hp|s m e Hm]; try discriminate.
  - destruct s; cbn; lra.
  - destruct s; cbn [Bsign B2R]; unfold F2R; cbn.
    all: pose proof (bpow_gt_0 radix2 e); pose proof (IZR_lt 0 (Z.pos m) ltac:(lia)); cbn in *.
    all: try nra.
    change (IZR (- Z.pos m) * bpow radix2 e <= 0); rewrite opp_IZR; nra.
Qed.

(** The guard [e = RN(qh·2^-58)], a normal number for the first stage's [qh]. *)
Lemma normal_tail_first_guard qh : finite qh -> bpow radix2 (-960) <= B qh <= 2 / 5 ->
  finite (fmul qh normal_tail_first_e) /\
  Rabs (B (fmul qh normal_tail_first_e) - bpow radix2 (-58) * B qh) <= bpow radix2 (-53) * (bpow radix2 (-58) * B qh).
Proof.
  intros Fq Q. destruct normal_tail_first_e_ok as [Fe Ev].
  destruct (fmul16 qh normal_tail_first_e Fq Fe) as [F Bv].
  { rewrite Ev, Rabs_mult, Rabs_pos_eq, Rabs_pos_eq by (try apply bpow_ge_0; bpow_num_all; lra). bpow_num_all. nra. }
  split; [exact F | ]. rewrite Bv, Ev, Rmult_comm.
  assert (N : bpow radix2 (-1022) <= Rabs (bpow radix2 (-58) * B qh)).
  { rewrite Rabs_pos_eq by (apply Rmult_le_pos; [apply bpow_ge_0 | bpow_num_all; lra]).
    replace (-1022)%Z with (-58 + -964)%Z by ring. rewrite bpow_plus. apply Rmult_le_compat_l; [apply bpow_ge_0 | ].
    apply Rle_trans with (2 := proj1 Q). apply bpow_le. lia. }
  pose proof (rnd_rel _ N) as R.
  change (round radix2 (FLT_exp (-1074) 53) (Znearest (fun n => negb (Z.even n))) (bpow radix2 (-58) * B qh)) with (rndF (bpow radix2 (-58) * B qh)) in R.
  rewrite (Rabs_pos_eq (bpow radix2 (-58) * B qh)) in R by (apply Rmult_le_pos; [apply bpow_ge_0 | bpow_num_all; lra]). exact R.
Qed.

(** [c - q] and its negation, [c] one or one half: the complement branches. *)
Lemma normal_tail_first_complement c qh ql (Q : R) (negative : bool) v :
  finite c -> /2 <= B c <= 1 -> finite qh -> finite ql ->
  bpow radix2 (-960) <= B qh <= 2 / 5 -> Rabs (B ql) <= / 256 * B qh -> 0 < Q <= 3 / 8 ->
  Rabs (B qh + B ql - Q) <= IZR 33 * bpow radix2 (-64) * Q ->
  (let '(s, t) := fast_two_sum64 c (fneg qh) in
   let w := fsub t ql in
   let e' := fadd (fmul qh normal_tail_first_e) normal_tail_first_one in
   if negative then normal_interval_decide64 (fneg s) (fneg w) e' else normal_interval_decide64 s w e') = Some v ->
  finite v /\ B v = rndF (if negative then - (B c - Q) else B c - Q).
Proof.
  intros Fc C Fqh Fql Qh Ql QR QE.
  pose proof (normal_tail_first_guard qh Fqh Qh) as [Fe Ee].
  destruct normal_tail_first_one_ok as [Fo Ov].
  pose proof (two_sum_ieee c (fneg qh) Fc (neg_finite _ Fqh)
    ltac:(rewrite Rabs_pos_eq by lra; bpow_num; lra) ltac:(rewrite neg_value, Rabs_Ropp, Rabs_pos_eq by (bpow_num_all; lra); bpow_num; lra)) as _.
  pose proof (fast_two_sum_ieee c (fneg qh) Fc (neg_finite _ Fqh)
    ltac:(rewrite Rabs_pos_eq by lra; bpow_num; lra) ltac:(rewrite neg_value, Rabs_Ropp, Rabs_pos_eq by (bpow_num_all; lra); bpow_num; lra)
    ltac:(right; left; rewrite neg_value, Rabs_Ropp, !Rabs_pos_eq by (bpow_num_all; lra); lra)) as FS.
  revert FS. generalize (fast_two_sum64 c (fneg qh)). intros [s t] FS.
  destruct FS as [Fs [Ft [Bs St]]]. rewrite neg_value in Bs, St.
  assert (Tb : Rabs (B t) <= bpow radix2 (-54)).
  { replace (B t) with (- (rndF (B c + - B qh) - (B c + - B qh))) by (rewrite <- Bs; lra). rewrite Rabs_Ropp.
    apply (rnd_err_below _ 0 ltac:(lia)). rewrite Rabs_pos_eq by (bpow_num_all; lra). change (bpow radix2 0) with 1.
    pose proof (bpow_ge_0 radix2 (-960)). lra. }
  destruct (fsub16 t ql Ft Fql) as [Fw Bw].
  { apply Rle_trans with (1 := Rabs_triang _ _). rewrite Rabs_Ropp. bpow_num_all. lra. }
  set (w := fsub t ql) in *.
  assert (Ew : Rabs (B w - (B t - B ql)) <= bpow radix2 (-53) * (bpow radix2 (-54) + / 256 * B qh) + bpow radix2 (-1075)).
  { rewrite Bw. pose proof (rnd_err_any (B t - B ql)) as R. pose proof (bpow_ge_0 radix2 (-53)).
    assert (Rabs (B t - B ql) <= bpow radix2 (-54) + / 256 * B qh) by (unfold Rminus; apply Rle_trans with (1 := Rabs_triang _ _); rewrite Rabs_Ropp; lra).
    nra. }
  set (e := fmul qh normal_tail_first_e) in *.
  destruct (fadd16 e normal_tail_first_one Fe Fo) as [Fe' Be'].
  { apply Rle_trans with (1 := Rabs_triang _ _). rewrite Ov. apply Rabs_le_inv in Ee. bpow_num_all.
    rewrite (Rabs_pos_eq (/ _)) by lra. assert (Rabs (B e) <= 1) by (apply Rabs_le; split; nra). lra. }
  set (e' := fadd e normal_tail_first_one) in *.
  assert (E' : (bpow radix2 (-58) * B qh + bpow radix2 (-100)) * (1 - bpow radix2 (-52)) <= B e').
  { rewrite Be', Ov. pose proof (rnd_err_any (B e + bpow radix2 (-100))) as R.
    apply Rabs_le_inv in Ee. pose proof (bpow_gt_0 radix2 (-100)).
    assert (P : 0 <= B e + bpow radix2 (-100)) by (bpow_num_all; nra).
    rewrite (Rabs_pos_eq (B e + bpow radix2 (-100))) in R by exact P. apply Rabs_le_inv in R. bpow_num_all. nra. }
  assert (E'u : B e' <= (bpow radix2 (-58) * B qh + bpow radix2 (-100)) * (1 + bpow radix2 (-52))).
  { rewrite Be', Ov. pose proof (rnd_err_any (B e + bpow radix2 (-100))) as R.
    apply Rabs_le_inv in Ee. pose proof (bpow_gt_0 radix2 (-100)).
    assert (P : 0 <= B e + bpow radix2 (-100)) by (bpow_num_all; nra).
    rewrite (Rabs_pos_eq (B e + bpow radix2 (-100))) in R by exact P. apply Rabs_le_inv in R. bpow_num_all. nra. }
  (* the error of s + w against c - Q *)
  set (eps := IZR 33 * bpow radix2 (-64) * Q + (bpow radix2 (-53) * (bpow radix2 (-54) + / 256 * B qh) + bpow radix2 (-1075))).
  assert (Err : Rabs ((B c - Q) - (B s + B w)) <= eps).
  { replace ((B c - Q) - (B s + B w)) with ((B qh + B ql - Q) - (B w - (B t - B ql))) by lra.
    apply Rle_trans with (1 := Rabs_triang _ _). rewrite Rabs_Ropp. unfold eps. lra. }
  assert (Qq : Q <= B qh * (1 + / 128)).
  { apply Rabs_le_inv in QE. apply Rabs_le_inv in Ql. bpow_num_all. nra. }
  (* the test's scale *)
  assert (Qnz : B qh <> 0) by (bpow_num_all; lra).
  pose proof (bpow_mag_le radix2 (B qh) Qnz) as Mlo. pose proof (bpow_mag_gt radix2 (B qh)) as Mhi.
  rewrite Rabs_pos_eq in Mlo, Mhi by (bpow_num_all; lra).
  set (m := mag radix2 (B qh)) in *.
  assert (Mr : (-959 <= m <= -1)%Z).
  { assert (A : (-960 < m)%Z).
    { apply (lt_bpow radix2). apply Rle_lt_trans with (B qh); [ | exact Mhi]. exact (proj1 Qh). }
    assert (B' : (m - 1 < -1)%Z).
    { apply (lt_bpow radix2). apply Rle_lt_trans with (1 := Mlo). change (bpow radix2 (-1)) with (/ 2). lra. }
    lia. }
  set (em := Z.max (-52) (m - 7)).
  assert (Scale : Rabs (B s + B w - (B s + B w)) = 0) by (rewrite Rminus_diag_eq by reflexivity; apply Rabs_R0).
  assert (Wb : Rabs (B w) + B e' <= bpow radix2 em).
  { apply Rabs_le_inv in Ew. apply Rabs_le_inv in Ql.
    assert (Aw : Rabs (B w) <= bpow radix2 (-54) + / 256 * B qh + bpow radix2 (-53) * (bpow radix2 (-54) + / 256 * B qh) + bpow radix2 (-1075)).
    { apply Rabs_le. apply Rabs_le_inv in Tb. split; lra. }
    unfold em. destruct (Z.max_spec (-52) (m - 7)) as [[L M] | [L M]]; rewrite M.
    - assert (Bq : bpow radix2 (-52) <= bpow radix2 (m - 7)) by (apply bpow_le; lia).
      assert (Bq2 : B qh * / 128 <= bpow radix2 (m - 7)).
      { replace (m - 7)%Z with (m + -7)%Z by ring. rewrite bpow_plus. change (bpow radix2 (-7)) with (/ 128). lra. }
      clear - Aw E'u Bq Bq2 Qh. bpow_num_all. lra.
    - assert (Bq : B qh <= bpow radix2 (-45)) by (apply Rlt_le, Rlt_le_trans with (1 := Mhi); apply bpow_le; lia).
      clear - Aw E'u Bq Qh. bpow_num_all. lra. }
  assert (Budget : eps + bpow radix2 (em - 54) <= B e').
  { assert (Sm : bpow radix2 (em - 54) <= bpow radix2 (-106) + B qh * bpow radix2 (-60)).
    { unfold em. destruct (Z.max_spec (-52) (m - 7)) as [[_ M] | [_ M]]; rewrite M.
      - replace (m - 7 - 54)%Z with ((m - 1) + -60)%Z by ring. rewrite bpow_plus.
        pose proof (bpow_ge_0 radix2 (-106)). assert (bpow radix2 (m - 1) * bpow radix2 (-60) <= B qh * bpow radix2 (-60)).
        { apply Rmult_le_compat_r; [apply bpow_ge_0 | exact Mlo]. } lra.
      - assert (0 <= B qh * bpow radix2 (-60)) by (apply Rmult_le_pos; [bpow_num_all; lra | apply bpow_ge_0]).
        change (-52 - 54)%Z with (-106)%Z. lra. }
    unfold eps. clear - Sm E' Qq Qh QR. bpow_num_all. nra. }
  assert (Fneg : forall u, finite u -> finite (fneg u)) by exact neg_finite.
  destruct negative; intros Hd.
  - apply (normal_interval_decide_ok (fneg s) (fneg w) e' (- (B c - Q)) eps em v (Fneg s Fs) (Fneg w Fw) Fe'); try assumption.
    + rewrite neg_value, Rabs_Ropp, Bs. apply Rle_trans with 1; [apply abs_round_le_generic; auto with typeclass_instances;
        [change 1 with (bpow radix2 0); apply generic_format_bpow; unfold FLT_exp, emin, prec; lia | rewrite Rabs_pos_eq by (bpow_num_all; lra); lra] | lra].
    + unfold em. split; [lia | ]. apply Z.max_lub; lia.
    + apply Rle_trans with (2 := E'). apply Rmult_le_pos; [apply Rplus_le_le_0_compat; [apply Rmult_le_pos; [apply bpow_ge_0 | bpow_num_all; lra] | apply bpow_ge_0] | bpow_num; lra].
    + rewrite neg_value, Rabs_Ropp. exact Wb.
    + rewrite !neg_value. replace (- (B c - Q) - (- B s + - B w)) with (- ((B c - Q) - (B s + B w))) by ring.
      rewrite Rabs_Ropp. exact Err.
  - apply (normal_interval_decide_ok s w e' (B c - Q) eps em v Fs Fw Fe'); try assumption.
    + rewrite Bs. apply Rle_trans with 1; [apply abs_round_le_generic; auto with typeclass_instances;
        [change 1 with (bpow radix2 0); apply generic_format_bpow; unfold FLT_exp, emin, prec; lia | rewrite Rabs_pos_eq by (bpow_num_all; lra); lra] | lra].
    + unfold em. split; [lia | ]. apply Z.max_lub; lia.
    + apply Rle_trans with (2 := E'). apply Rmult_le_pos; [apply Rplus_le_le_0_compat; [apply Rmult_le_pos; [apply bpow_ge_0 | bpow_num_all; lra] | apply bpow_ge_0] | bpow_num; lra].
Qed.

(** A value the first stage returns is the correctly rounded CDF or
    centered CDF. *)
Theorem normal_tail_first_ok op x v : finite x -> /2 < Rabs (B x) <= 36 ->
  normal_tail_first64 op x = Some v -> finite v /\ B v = rndF (normal_target op (B x)).
Proof.
  intros Fx X. pose proof (normal_tail_first_parts_ok x Fx X) as P.
  unfold normal_tail_first64. revert P. generalize (normal_tail_first_parts64 x). intros [qh ql] P.
  destruct P as [Fqh [Fql [Qh [Ql [QR QE]]]]].
  set (Q := normal_tail (Rabs (B x))) in *.
  pose proof (normal_tail_first_guard qh Fqh Qh) as [Fe Ee].
  assert (Zero : B normal_zero = 0) by reflexivity.
  assert (Fz : finite normal_zero) by reflexivity.
  destruct (erfcx_pow2_ok 0 ltac:(lia)) as [F1 B1]. change (bpow radix2 0) with 1 in B1.
  destruct (erfcx_pow2_ok (-1) ltac:(lia)) as [Fh Bh]. change (bpow radix2 (-1)) with (/ 2) in Bh.
  destruct op; try discriminate.
  - (* CDF *)
    destruct (normal_lt x normal_zero) eqn:Neg.
    + apply (normal_lt_true x normal_zero Fx Fz) in Neg. rewrite Zero in Neg. intros Hd.
      assert (Target : normal_target NormalCdf (B x) = Q).
      { simpl. unfold Q. rewrite normal_negative_cdf by lra. reflexivity. }
      rewrite Target.
      assert (Qnz : B qh <> 0) by (bpow_num_all; lra).
      pose proof (bpow_mag_le radix2 (B qh) Qnz) as Mlo. pose proof (bpow_mag_gt radix2 (B qh)) as Mhi.
      rewrite Rabs_pos_eq in Mlo, Mhi by (bpow_num_all; lra).
      set (m := mag radix2 (B qh)) in *.
      assert (Mr : (-959 <= m <= -1)%Z).
      { assert (A : (-960 < m)%Z).
        { apply (lt_bpow radix2). apply Rle_lt_trans with (B qh); [ | exact Mhi]. exact (proj1 Qh). }
        assert (B' : (m - 1 < -1)%Z).
        { apply (lt_bpow radix2). apply Rle_lt_trans with (1 := Mlo). change (bpow radix2 (-1)) with (/ 2). lra. }
        lia. }
      assert (Qq : Q <= B qh * (1 + / 128)).
      { apply Rabs_le_inv in QE. apply Rabs_le_inv in Ql. clear - QE Ql Qh QR. bpow_num_all. nra. }
      apply (normal_interval_decide_ok qh ql (fmul qh normal_tail_first_e) Q (IZR 33 * bpow radix2 (-64) * Q) (m - 7) v
               Fqh Fql Fe); try assumption; try lia.
      * apply Rle_trans with 1; [rewrite Rabs_pos_eq by (bpow_num_all; lra); lra | lra].
      * apply Rabs_le_inv in Ee. clear - Ee Qh. bpow_num_all. nra.
      * assert (Bq2 : B qh * / 128 <= bpow radix2 (m - 7)).
        { replace (m - 7)%Z with (m + -7)%Z by ring. rewrite bpow_plus. change (bpow radix2 (-7)) with (/ 128). lra. }
        apply Rabs_le_inv in Ee. clear - Ee Ql Bq2 Qh. bpow_num_all. nra.
      * assert (Sm : bpow radix2 (m - 7 - 54) <= B qh * bpow radix2 (-60)).
        { replace (m - 7 - 54)%Z with ((m - 1) + -60)%Z by ring. rewrite bpow_plus.
          apply Rmult_le_compat_r; [apply bpow_ge_0 | exact Mlo]. }
        apply Rabs_le_inv in Ee. clear - Ee Sm Qq Qh QR. bpow_num_all. nra.
      * rewrite Rabs_minus_sym. exact QE.
    + apply (normal_lt_false x normal_zero Fx Fz) in Neg. rewrite Zero in Neg.
      assert (Xp : B x = Rabs (B x)) by (rewrite Rabs_pos_eq by lra; reflexivity).
      intros Hd.
      pose proof (normal_tail_first_complement (erfcx_pow2 0) qh ql Q false v F1 ltac:(rewrite B1; lra)
                    Fqh Fql Qh Ql QR QE Hd) as [Fv Bv].
      split; [exact Fv | ]. rewrite Bv, B1. f_equal. simpl. unfold Q. rewrite <- Xp. apply normal_positive_cdf.
  - (* centered *)
    intros Hd. pose proof (normal_tail_first_sign x Fx) as Sign.
    pose proof (normal_tail_first_complement (erfcx_pow2 (-1)) qh ql Q (Bsign 53 1024 x) v Fh ltac:(rewrite Bh; lra)
                  Fqh Fql Qh Ql QR QE Hd) as [Fv Bv].
    split; [exact Fv | ]. rewrite Bv, Bh. f_equal. simpl. unfold Q.
    destruct (Bsign 53 1024 x).
    + assert (Xn : B x < 0) by (destruct (Rle_lt_or_eq_dec _ _ Sign) as [L | E]; [exact L | rewrite E, Rabs_R0 in X; lra]).
      exact (normal_outer_center_target true (B x) (fun _ => Xn) (fun H => ltac:(discriminate H))).
    + assert (Xp : 0 <= B x) by exact Sign.
      exact (normal_outer_center_target false (B x) (fun H => ltac:(discriminate H)) (fun _ => Xp)).
Qed.
