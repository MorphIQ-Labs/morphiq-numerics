(** normal_distribution/mod.rs's [center_first] (docs/normal.md, the central
    first stage): [C(x) = φ(0)·x·P(x²)] for [2^-33 <= |x| <= 1/2] with only
    the exact square, [φ(0)·x] and the [c1·z] term carried as double words,
    transcribed on binary64 and proved:
    - [normal_center_first_parts_ok]: [ch + cl] is within [3.2·2^-60] of the
      centered CDF relatively;
    - [normal_center_first_ok]: a value its rounding test returns is the
      correctly rounded centered CDF or CDF. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Interval Require Import Tactic.
From Gappa Require Gappa_definitions.
From Gappa Require Import Gappa_library.
From Binary64 Require Import Binary64Add Binary64Mul IEEE64 IEEE64Add IEEE64Mul IEEE64Eft Encodings
  RoundingConstant RoundingTest RoundingCore.
Require Import StageGappa ErfcxDecision NormalConstants NormalCentered NormalCenterFastConstants
  NormalCenterFastTail NormalCenterFastAnalytic NormalFastDecision NormalFastDispatch
  NormalAccurateCentralCdf NormalTailFirst.
Require normal_center_first.
Open Scope R_scope.

Lemma rndF_rn v : rndF v = rn v.
Proof. reflexivity. Qed.

(** The certificate's spelling of the stored coefficients. *)
Definition g_c1h : R := Gappa_definitions.float2R (Gappa_definitions.Float2 (-6004799503160661) (-55)).
Definition g_c1l : R := Gappa_definitions.float2R (Gappa_definitions.Float2 (-6004799503160661) (-109)).
Definition g_c2 : R := Gappa_definitions.float2R (Gappa_definitions.Float2 3602879701896397 (-57)).
Definition g_c3 : R := Gappa_definitions.float2R (Gappa_definitions.Float2 (-857828500451523) (-58)).

(** formal/normal/center_first.g's theorem. *)
Theorem center_first_bound (x t4 TZ TH : R) :
  Rabs x <= / 2 -> Rabs (t4 - TH) <= bpow radix2 (-62) -> Rabs (TH - TZ) <= bpow radix2 (-64) ->
  Rabs TZ <= bpow radix2 (-9) ->
  let zh := rn (x * x) in
  let zl := x * x - zh in
  let e1h := rn (g_c1h * zh) in
  let e1p := g_c1h * zh - e1h in
  let r1 := rn (g_c1h * zl) in
  let r2 := rn (g_c1l * zh) in
  let r := rn (r1 + r2) in
  let e1l := rn (e1p + r) in
  let t3 := rn (g_c3 + rn (zh * t4)) in
  let zz := rn (zh * zh) in
  let m := rn (zh * t3) in
  let w := rn (g_c2 + m) in
  let e2 := rn (zz * w) in
  let E := Float1 (-1) / Float1 6 * (x * x) + x * x * (x * x) *
             (Float1 1 / Float1 40 + x * x * (Float1 (-1) / Float1 336 + x * x * TZ)) in
  Rabs (e1h + e1l + e2 - E) <= bpow radix2 (-60) /\
  -0.0417 <= e1h <= 0 /\ Rabs e1l <= bpow radix2 (-55) /\ 0 <= e2 <= 0.0016 /\ 0 <= zh <= 0.25 /\
  Rabs (g_c1h * zl) <= 1 /\ Rabs (g_c1l * zh) <= 1 /\ Rabs (r1 + r2) <= 1 /\ Rabs (e1p + r) <= 1 /\
  Rabs (zh * t4) <= 1 /\ Rabs (g_c3 + rn (zh * t4)) <= 1 /\ Rabs (zh * zh) <= 1 /\ Rabs (zh * t3) <= 1 /\
  Rabs (g_c2 + m) <= 1 /\ Rabs (zz * w) <= 1 /\ Rabs (g_c1h * zh) <= 1.
Proof.
  intros X T Tz Tr. cbv zeta. unfold g_c1h, g_c1l, g_c2, g_c3.
  apply Rabs_le_inv in X. apply Rabs_le_inv in T. apply Rabs_le_inv in Tz. apply Rabs_le_inv in Tr.
  repeat split; try apply Rabs_le; gappa_goal (normal_center_first.l1 x t4 TZ TH).
Qed.

(** [center_first_parts]: [(ch, cl)]. *)
Definition normal_center_first_parts64 x :=
  let '(zh, zl) := two_prod64 x x in
  let '(e1h, e1p) := two_prod64 normal_center_1_hi zh in
  let e1l := fadd e1p (fadd (fmul normal_center_1_hi zl) (fmul normal_center_1_lo zh)) in
  let t3 := fadd normal_center_3_hi (fmul zh (normal_center_tail64 zh 8)) in
  let e2 := fmul (fmul zh zh) (fadd normal_center_2_hi (fmul zh t3)) in
  let '(dh, dp) := two_prod64 normal_density_hi x in
  let dl := fadd dp (fmul normal_density_lo x) in
  let '(q, qp) := two_prod64 dh e1h in
  let rest := fadd dl (fadd qp (fadd (fadd (fmul dh e1l) (fmul dl e1h)) (fmul dh e2))) in
  let '(s, s2) := fast_two_sum64 dh q in
  fast_two_sum64 s (fadd s2 rest).

(** [center_first]. *)
Definition normal_center_first64 op x :=
  let '(ch, cl) := normal_center_first_parts64 x in
  let e := fmul (b64_abs ch) normal_tail_first_e in
  match op with
  | NormalCentered => normal_interval_decide64 ch cl e
  | NormalCdf => let '(u, v) := fast_two_sum64 (erfcx_pow2 (-1)) ch in normal_interval_decide64 u (fadd v cl) e
  | _ => None
  end.

Lemma g_c1h_eq : B normal_center_1_hi = g_c1h.
Proof. rewrite (proj2 normal_center_1_hi_ok). unfold g_c1h, Gappa_definitions.float2R, F2R. cbn [Defs.Fnum Defs.Fexp Gappa_definitions.Fnum Gappa_definitions.Fexp]. bpow_num. field. Qed.
Lemma g_c1l_eq : B normal_center_1_lo = g_c1l.
Proof. rewrite (proj2 normal_center_1_lo_ok). unfold g_c1l, Gappa_definitions.float2R, F2R. cbn [Defs.Fnum Defs.Fexp Gappa_definitions.Fnum Gappa_definitions.Fexp]. bpow_num. field. Qed.
Lemma g_c2_eq : B normal_center_2_hi = g_c2.
Proof. rewrite (proj2 normal_center_2_hi_ok). unfold g_c2, Gappa_definitions.float2R, F2R. cbn [Defs.Fnum Defs.Fexp Gappa_definitions.Fnum Gappa_definitions.Fexp]. bpow_num. field. Qed.
Lemma g_c3_eq : B normal_center_3_hi = g_c3.
Proof. rewrite (proj2 normal_center_3_hi_ok). unfold g_c3, Gappa_definitions.float2R, F2R. cbn [Defs.Fnum Defs.Fexp Gappa_definitions.Fnum Gappa_definitions.Fexp]. bpow_num. field. Qed.

(** [P(x²) - 1] with the exact coefficients and the exact tail. *)
Definition center_first_E (X : R) := Float1 (-1) / Float1 6 * (X * X) + X * X * (X * X) *
  (Float1 1 / Float1 40 + X * X * (Float1 (-1) / Float1 336 + X * X * normal_center_tail_polynomial (X * X) 8)).

Lemma center_first_E_shape X :
  1 + center_first_E X = normal_center_mixed_shape (X * X) (normal_center_tail_polynomial (X * X) 8).
Proof.
  unfold center_first_E, normal_center_mixed_shape, normal_fast_center_coefficient.
  change (Float1 (-1)) with (-1). change (Float1 6) with 6. change (Float1 1) with 1.
  change (Float1 40) with 40. change (Float1 336) with 336.
  cbn [pow fact INR Nat.mul Nat.add]. simpl. field.
Qed.

(** The polynomial part: every operation finite and as the certificate
    models it, and [e1h + e1l + e2] within [2^-60] of [E]. *)
Lemma center_first_poly x : finite x -> bpow radix2 (-33) <= Rabs (B x) <= / 2 ->
  let '(zh, zl) := two_prod64 x x in
  let '(e1h, e1p) := two_prod64 normal_center_1_hi zh in
  let e1l := fadd e1p (fadd (fmul normal_center_1_hi zl) (fmul normal_center_1_lo zh)) in
  let t3 := fadd normal_center_3_hi (fmul zh (normal_center_tail64 zh 8)) in
  let e2 := fmul (fmul zh zh) (fadd normal_center_2_hi (fmul zh t3)) in
  finite e1h /\ finite e1l /\ finite e2 /\
  Rabs (B e1h + B e1l + B e2 - center_first_E (B x)) <= bpow radix2 (-60) /\
  -0.0417 <= B e1h <= 0 /\ Rabs (B e1l) <= bpow radix2 (-55) /\ 0 <= B e2 <= 0.0016 /\
  bpow radix2 (-70) <= Rabs (B e1h).
Proof.
  intros Fx X.
  assert (Xb : Rabs (B x) <= bpow radix2 (-1)) by (change (bpow radix2 (-1)) with (/ 2); lra).
  assert (X2 : bpow radix2 (-66) <= B x * B x).
  { replace (B x * B x) with (Rabs (B x) * Rabs (B x)) by (rewrite <- Rabs_mult; apply Rabs_pos_eq; nra).
    replace (-66)%Z with (-33 + -33)%Z by ring. rewrite bpow_plus. pose proof (bpow_ge_0 radix2 (-33)). nra. }
  assert (X4 : B x * B x <= / 4) by (pose proof (Rabs_le_inv _ _ (proj2 X)); nra).
  pose proof (two_prod_ieee (-1) (-1) x x Fx Fx Xb Xb ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(right; rewrite Rabs_pos_eq by nra; apply Rle_trans with (2 := X2); apply bpow_le; lia)) as Sq.
  revert Sq. generalize (two_prod64 x x). intros [zh zl] Sq. destruct Sq as [Fzh [Fzl [Bzh Zs]]].
  rewrite rndF_rn in Bzh.
  assert (Bzl : B zl = B x * B x - B zh) by lra.
  assert (Zr : 0 <= B zh <= / 4).
  { rewrite Bzh, <- rndF_rn. split.
    - apply round_ge_generic; auto with typeclass_instances; [apply generic_format_0 | nra].
    - apply round_le_generic; auto with typeclass_instances; try lra.
      change (/ 4) with (bpow radix2 (-2)). apply generic_format_bpow. unfold FLT_exp, emin, prec. lia. }
  assert (Zl : Rabs (B zh - B x * B x) <= bpow radix2 (-56)).
  { rewrite Bzh, <- rndF_rn. apply (rnd_err_below _ (-2) ltac:(lia)). rewrite Rabs_pos_eq by nra. change (bpow radix2 (-2)) with (/ 4). lra. }
  assert (Zlow : bpow radix2 (-67) <= B zh).
  { assert (R : Rabs (rndF (B x * B x) - B x * B x) <= bpow radix2 (-53) * Rabs (B x * B x)).
    { apply rnd_rel. rewrite Rabs_pos_eq by nra. apply Rle_trans with (2 := X2). apply bpow_le. lia. }
    rewrite rndF_rn, <- Bzh, (Rabs_pos_eq (B x * B x)) in R by nra. apply Rabs_le_inv in R. clear - R X2. bpow_num_all. nra. }
  (* the tail *)
  destruct (normal_center_tail_ieee zh 8 Fzh ltac:(rewrite Rabs_pos_eq by lra; lra) ltac:(lia)) as [Ft4 [Bt4 Et4]].
  set (t4 := normal_center_tail64 zh 8) in *.
  set (TH := normal_center_tail_polynomial (B zh) 8) in *.
  set (TZ := normal_center_tail_polynomial (B x * B x) 8).
  assert (Lip : Rabs (TH - TZ) <= bpow radix2 (-64)).
  { unfold TH, TZ. eapply Rle_trans.
    - apply normal_center_tail_lipschitz; [rewrite Rabs_pos_eq by lra; lra | rewrite Rabs_pos_eq by nra; lra | lia].
    - replace (-64)%Z with (-8 + -56)%Z by ring. rewrite bpow_plus. apply Rmult_le_compat_l; [apply bpow_ge_0 | exact Zl]. }
  assert (TZr : Rabs TZ <= bpow radix2 (-9)).
  { apply normal_center_tail_polynomial_range; [rewrite Rabs_pos_eq by nra; lra | lia]. }
  pose proof (center_first_bound (B x) (B t4) TZ TH ltac:(lra) Et4 Lip TZr) as G.
  cbv zeta in G. rewrite <- Bzh in G. rewrite <- Bzl in G.
  destruct G as [GE [Ge1h [Ge1l [Ge2 [Gzh [B1 [B2 [B3 [B4 [B5 [B6 [B7 [B8 [B9 [B10 B11]]]]]]]]]]]]]]].
  (* c1h·zh exactly *)
  pose proof (two_prod_ieee 0 (-2) normal_center_1_hi zh (proj1 normal_center_1_hi_ok) Fzh
    ltac:(rewrite g_c1h_eq; unfold g_c1h; change (bpow radix2 0) with 1; unfold Gappa_definitions.float2R, F2R;
          cbn [Defs.Fnum Defs.Fexp Gappa_definitions.Fnum Gappa_definitions.Fexp]; bpow_num; interval)
    ltac:(rewrite Rabs_pos_eq by lra; change (bpow radix2 (-2)) with (/ 4); lra) ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(right; rewrite g_c1h_eq, Rabs_mult, (Rabs_pos_eq (B zh)) by lra; unfold g_c1h, Gappa_definitions.float2R, F2R;
          cbn [Defs.Fnum Defs.Fexp Gappa_definitions.Fnum Gappa_definitions.Fexp];
          apply Rle_trans with (/ 7 * bpow radix2 (-67)); [bpow_num; lra | apply Rmult_le_compat; [lra | apply bpow_ge_0 | bpow_num; interval | exact Zlow]])) as P1.
  revert P1. generalize (two_prod64 normal_center_1_hi zh). intros [e1h e1p] P1.
  destruct P1 as [Fe1h [Fe1p [Be1h E1]]]. rewrite g_c1h_eq, rndF_rn in Be1h. rewrite g_c1h_eq in E1.
  assert (Be1p : B e1p = g_c1h * B zh - B e1h) by lra.
  (* e1l *)
  destruct (fmul16 _ _ (proj1 normal_center_1_hi_ok) Fzl ltac:(rewrite g_c1h_eq; lra)) as [Fr1 Br1].
  rewrite g_c1h_eq, rndF_rn in Br1.
  destruct (fmul16 _ _ (proj1 normal_center_1_lo_ok) Fzh ltac:(rewrite g_c1l_eq; lra)) as [Fr2 Br2].
  rewrite g_c1l_eq, rndF_rn in Br2.
  destruct (fadd16 _ _ Fr1 Fr2 ltac:(rewrite Br1, Br2; lra)) as [Fr Br]. rewrite Br1, Br2, rndF_rn in Br.
  destruct (fadd16 _ _ Fe1p Fr ltac:(rewrite Be1p, Be1h, Br; lra)) as [Fe1l Be1l].
  rewrite Be1p, Be1h, Br, rndF_rn in Be1l.
  (* t3 *)
  destruct (fmul16 _ _ Fzh Ft4 ltac:(lra)) as [Fm0 Bm0]. rewrite rndF_rn in Bm0.
  destruct (fadd16 _ _ (proj1 normal_center_3_hi_ok) Fm0 ltac:(rewrite g_c3_eq, Bm0; lra)) as [Ft3 Bt3].
  rewrite g_c3_eq, Bm0, rndF_rn in Bt3.
  (* e2 *)
  destruct (fmul16 _ _ Fzh Fzh ltac:(lra)) as [Fzz Bzz]. rewrite rndF_rn in Bzz.
  destruct (fmul16 _ _ Fzh Ft3 ltac:(rewrite Bt3; lra)) as [Fm Bm]. rewrite Bt3, rndF_rn in Bm.
  destruct (fadd16 _ _ (proj1 normal_center_2_hi_ok) Fm ltac:(rewrite g_c2_eq, Bm; lra)) as [Fw Bw].
  rewrite g_c2_eq, Bm, rndF_rn in Bw.
  destruct (fmul16 _ _ Fzz Fw ltac:(rewrite Bzz, Bw; lra)) as [Fe2 Be2]. rewrite Bzz, Bw, rndF_rn in Be2.
  repeat split; try assumption.
  - rewrite Be1h, Be1l, Be2. unfold center_first_E. fold TZ. exact GE.
  - rewrite Be1h; lra.
  - rewrite Be1h; lra.
  - rewrite Be1l; exact Ge1l.
  - rewrite Be2; lra.
  - rewrite Be2; lra.
  - (* e1h is nonzero *)
    rewrite Be1h, <- rndF_rn.
    assert (P : Rabs (g_c1h * B zh) >= / 7 * bpow radix2 (-67)).
    { rewrite Rabs_mult, (Rabs_pos_eq (B zh)) by lra. unfold g_c1h, Gappa_definitions.float2R, F2R.
      cbn [Defs.Fnum Defs.Fexp Gappa_definitions.Fnum Gappa_definitions.Fexp].
      apply Rle_ge, Rmult_le_compat; [lra | apply bpow_ge_0 | bpow_num; interval | exact Zlow]. }
    pose proof (rnd_rel (g_c1h * B zh) ltac:(apply Rle_trans with (/ 7 * bpow radix2 (-67)); [bpow_num; lra | lra])) as R.
    change (round radix2 (FLT_exp (-1074) 53) (Znearest (fun n => negb (Z.even n))) (g_c1h * B zh)) with (rndF (g_c1h * B zh)) in R.
    pose proof (Rabs_triang_inv (g_c1h * B zh) (g_c1h * B zh - rndF (g_c1h * B zh))) as T.
    replace (g_c1h * B zh - (g_c1h * B zh - rndF (g_c1h * B zh))) with (rndF (g_c1h * B zh)) in T by ring.
    rewrite Rabs_minus_sym in R. clear - R T P. bpow_num_all. nra.
Qed.

Theorem normal_center_first_parts_ok x : finite x -> bpow radix2 (-33) <= Rabs (B x) <= / 2 ->
  let '(ch, cl) := normal_center_first_parts64 x in
  finite ch /\ finite cl /\ B ch = rndF (B ch + B cl) /\ Rabs (B ch) <= 0.21 /\
  bpow radix2 (-36) <= Rabs (B ch) /\
  Rabs (B ch + B cl - normal_center (B x)) <= / 5 * bpow radix2 (-56) * Rabs (normal_center (B x)).
Proof.
  intros Fx X. pose proof (center_first_poly x Fx X) as P.
  unfold normal_center_first_parts64.
  revert P. generalize (two_prod64 x x). intros [zh zl] P.
  revert P. generalize (two_prod64 normal_center_1_hi zh). intros [e1h e1p] P.
  cbv zeta in P |- *.
  set (e1l := fadd e1p (fadd (fmul normal_center_1_hi zl) (fmul normal_center_1_lo zh))) in *.
  set (e2 := fmul (fmul zh zh) (fadd normal_center_2_hi (fmul zh (fadd normal_center_3_hi (fmul zh (normal_center_tail64 zh 8)))))) in *.
  destruct P as [Fe1h [Fe1l [Fe2 [PE [He1h [He1l [He2 He1hlow]]]]]]].
  set (E := center_first_E (B x)) in *.
  destruct normal_density_hi_ok as [Fph Ph]. destruct normal_density_lo_ok as [Fpl Pl].
  assert (Phr : 0.3989 <= B normal_density_hi <= 0.399) by (rewrite Ph; split; interval).
  assert (Plr : Rabs (B normal_density_lo) <= bpow radix2 (-55)) by (rewrite Pl; bpow_num; interval).
  assert (Xb : Rabs (B x) <= bpow radix2 (-1)) by (change (bpow radix2 (-1)) with (/ 2); lra).
  assert (Xpos : 0 < Rabs (B x)) by (pose proof (bpow_gt_0 radix2 (-33)); lra).
  (* φ(0)·x exactly *)
  pose proof (two_prod_ieee (-1) (-1) normal_density_hi x Fph Fx
    ltac:(rewrite Rabs_pos_eq by lra; change (bpow radix2 (-1)) with (/ 2); lra) Xb ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(right; rewrite Rabs_mult, (Rabs_pos_eq (B normal_density_hi)) by lra;
          apply Rle_trans with (0.3989 * bpow radix2 (-33)); [bpow_num; lra | apply Rmult_le_compat; try lra; apply bpow_ge_0])) as TD.
  revert TD. generalize (two_prod64 normal_density_hi x). intros [dh dp] TD. destruct TD as [Fdh [Fdp [Bdh Ddp]]].
  set (A := Rabs (B dh)).
  assert (Ar : 0.39 * Rabs (B x) <= A <= 0.4 * Rabs (B x)).
  { unfold A. rewrite Bdh. pose proof (rnd_err_any (B normal_density_hi * B x)) as R.
    rewrite Rabs_mult, (Rabs_pos_eq (B normal_density_hi)) in R by lra.
    pose proof (Rabs_triang_inv (rndF (B normal_density_hi * B x)) (B normal_density_hi * B x)) as T1.
    pose proof (Rabs_triang_inv (B normal_density_hi * B x) (B normal_density_hi * B x - rndF (B normal_density_hi * B x))) as T2.
    replace (B normal_density_hi * B x - (B normal_density_hi * B x - rndF (B normal_density_hi * B x))) with (rndF (B normal_density_hi * B x)) in T2 by ring.
    rewrite Rabs_mult, (Rabs_pos_eq (B normal_density_hi)) in T1, T2 by lra.
    pose proof R as R'. rewrite Rabs_minus_sym in R'.
    assert (bpow radix2 (-1075) <= bpow radix2 (-1000) * Rabs (B x)) by (clear - X; bpow_num_all; lra).
    rewrite Ph in R, R', T1, T2 |- *. clear - R R' T1 T2 H Xpos. bpow_num_all. split; lra. }
  assert (Dp : Rabs (B dp) <= bpow radix2 (-52) * A).
  { replace (B dp) with (- (rndF (B normal_density_hi * B x) - B normal_density_hi * B x)) by (rewrite <- Bdh; lra).
    rewrite Rabs_Ropp.
    pose proof (rnd_rel (B normal_density_hi * B x)) as R.
    change (round radix2 (FLT_exp (-1074) 53) (Znearest (fun n => negb (Z.even n))) (B normal_density_hi * B x)) with (rndF (B normal_density_hi * B x)) in R.
    assert (N : bpow radix2 (-1022) <= Rabs (B normal_density_hi * B x)).
    { rewrite Rabs_mult, (Rabs_pos_eq (B normal_density_hi)) by lra. apply Rle_trans with (0.3989 * bpow radix2 (-33)); [bpow_num; lra | ].
      apply Rmult_le_compat; try lra; apply bpow_ge_0. }
    specialize (R N). eapply Rle_trans; [exact R | ].
    rewrite Rabs_mult, (Rabs_pos_eq (B normal_density_hi)) by lra.
    assert (Pb : B normal_density_hi * Rabs (B x) <= 0.399 * Rabs (B x)) by (apply Rmult_le_compat_r; [apply Rabs_pos | lra]).
    clear - Pb Ar. bpow_num_all. lra. }
  assert (Alow : bpow radix2 (-36) <= A).
  { apply Rle_trans with (0.39 * bpow radix2 (-33)); [bpow_num; lra | ]. apply Rle_trans with (2 := proj1 Ar).
    apply Rmult_le_compat_l; lra. }
  assert (Aup : A <= / 5) by lra.
  assert (Tiny : bpow radix2 (-1075) <= bpow radix2 (-1000) * A) by (clear - Alow; bpow_num_all; lra).
  assert (Rel : forall v, Rabs (rndF v - v) <= bpow radix2 (-53) * Rabs v + bpow radix2 (-1000) * A).
  { intros v. pose proof (rnd_err_any v). lra. }
  (* dl *)
  assert (PlX : Rabs (B normal_density_lo * B x) <= bpow radix2 (-53) * A).
  { rewrite Rabs_mult. apply Rle_trans with (bpow radix2 (-55) * (A / 0.39)).
    - apply Rmult_le_compat; try apply Rabs_pos; [exact Plr | ]. apply Rmult_le_reg_r with 0.39; [lra | ]. unfold Rdiv.
      rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra. lra.
    - clear - Alow. bpow_num_all. nra. }
  destruct (fmul16 _ _ Fpl Fx ltac:(clear - PlX Aup; bpow_num_all; apply Rabs_le_inv in PlX; apply Rabs_le; split; nra)) as [Fpx Bpx].
  set (px := fmul normal_density_lo x) in *.
  assert (Epx : Rabs (B px - B normal_density_lo * B x) <= bpow radix2 (-53) * (bpow radix2 (-53) * A) + bpow radix2 (-1000) * A).
  { rewrite Bpx. pose proof (Rel (B normal_density_lo * B x)). pose proof (bpow_ge_0 radix2 (-53)). nra. }
  destruct (fadd16 _ _ Fdp Fpx ltac:(apply Rle_trans with (1 := Rabs_triang _ _); clear - Dp Epx PlX Aup; apply Rabs_le_inv in Epx; apply Rabs_le_inv in PlX;
     assert (Rabs (B px) <= 1) by (apply Rabs_le; bpow_num_all; split; nra); bpow_num_all; nra)) as [Fdl Bdl].
  set (dl := fadd dp px) in *.
  assert (Edl : Rabs (B dl - (B dp + B px)) <= bpow radix2 (-53) * (bpow radix2 (-51) * A) + bpow radix2 (-1000) * A).
  { rewrite Bdl. pose proof (Rel (B dp + B px)) as R. eapply Rle_trans; [exact R | ].
    apply Rplus_le_compat_r, Rmult_le_compat_l; [apply bpow_ge_0 | ]. apply Rle_trans with (1 := Rabs_triang _ _).
    apply Rabs_le_inv in Epx. apply Rabs_le_inv in PlX. clear - Dp Epx PlX Alow. assert (Rabs (B px) <= bpow radix2 (-52) * A) by (apply Rabs_le; bpow_num_all; split; nra).
    bpow_num_all. lra. }
  assert (Adl : Rabs (B dl) <= bpow radix2 (-51) * A).
  { apply Rabs_le_inv in Edl. apply Rabs_le_inv in Epx. apply Rabs_le_inv in PlX. apply Rabs_le_inv in Dp. clear - Edl Epx PlX Dp Alow. apply Rabs_le. bpow_num_all. split; lra. }
  (* dh·e1h exactly *)
  assert (Ae1h : Rabs (B e1h) <= 0.0417) by (apply Rabs_le; lra).
  pose proof (two_prod_ieee (-1) (-4) dh e1h Fdh Fe1h
    ltac:(change (bpow radix2 (-1)) with (/ 2); fold A; lra) ltac:(change (bpow radix2 (-4)) with (/ 16); lra) ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(right; rewrite Rabs_mult; fold A; apply Rle_trans with (bpow radix2 (-36) * bpow radix2 (-70));
          [rewrite <- bpow_plus; apply bpow_le; lia | apply Rmult_le_compat; try apply bpow_ge_0; assumption])) as TQ.
  revert TQ. generalize (two_prod64 dh e1h). intros [q qp] TQ. destruct TQ as [Fq [Fqp [Bq Qqp]]].
  assert (DE : Rabs (B dh * B e1h) <= 0.0417 * A) by (rewrite Rabs_mult; fold A; rewrite (Rmult_comm 0.0417 A); apply Rmult_le_compat_l; [unfold A; apply Rabs_pos | exact Ae1h]).
  assert (Aqp : Rabs (B qp) <= bpow radix2 (-53) * (0.0417 * A) + bpow radix2 (-1000) * A).
  { replace (B qp) with (- (rndF (B dh * B e1h) - B dh * B e1h)) by (rewrite <- Bq; lra). rewrite Rabs_Ropp.
    pose proof (Rel (B dh * B e1h)). pose proof (bpow_ge_0 radix2 (-53)). nra. }
  assert (Aq : Rabs (B q) <= 0.042 * A) by (rewrite Bq; pose proof (Rel (B dh * B e1h)); pose proof (Rabs_triang_inv (rndF (B dh * B e1h)) (B dh * B e1h));
    clear - H H0 DE Alow; bpow_num_all; nra).
  (* the remainder *)
  assert (A1 : Rabs (B e1l) <= 1) by (clear - He1l; bpow_num_all; lra).
  destruct (fmul16 _ _ Fdh Fe1l ltac:(rewrite Rabs_mult; fold A; apply Rle_trans with (1 * 1); [apply Rmult_le_compat; try apply Rabs_pos; lra | lra])) as [Fa1 Ba1]. set (a1 := fmul dh e1l) in *.
  assert (Dl1 : Rabs (B dl) <= 1) by (clear - Adl Aup; bpow_num_all; nra).
  destruct (fmul16 _ _ Fdl Fe1h ltac:(rewrite Rabs_mult; apply Rle_trans with (1 * 1); [apply Rmult_le_compat; try apply Rabs_pos; lra | lra])) as [Fa2 Ba2]. set (a2 := fmul dl e1h) in *.
  assert (V1 : Rabs (B dh * B e1l) <= bpow radix2 (-55) * A) by (rewrite Rabs_mult; fold A; rewrite Rmult_comm; apply Rmult_le_compat_r; [unfold A; apply Rabs_pos | exact He1l]).
  assert (V2 : Rabs (B dl * B e1h) <= bpow radix2 (-55) * A).
  { rewrite Rabs_mult. apply Rle_trans with (bpow radix2 (-51) * A * 0.0417); [apply Rmult_le_compat; try apply Rabs_pos; lra | ].
    clear - Alow. bpow_num_all. lra. }
  assert (E1 : Rabs (B a1 - B dh * B e1l) <= bpow radix2 (-53) * (bpow radix2 (-55) * A) + bpow radix2 (-1000) * A).
  { rewrite Ba1. pose proof (Rel (B dh * B e1l)). pose proof (bpow_ge_0 radix2 (-53)). nra. }
  assert (E2 : Rabs (B a2 - B dl * B e1h) <= bpow radix2 (-53) * (bpow radix2 (-55) * A) + bpow radix2 (-1000) * A).
  { rewrite Ba2. pose proof (Rel (B dl * B e1h)). pose proof (bpow_ge_0 radix2 (-53)). nra. }
  assert (W12 : Rabs (B a1 + B a2) <= bpow radix2 (-53) * A).
  { apply Rle_trans with (1 := Rabs_triang _ _). apply Rabs_le_inv in E1. apply Rabs_le_inv in E2. apply Rabs_le_inv in V1. apply Rabs_le_inv in V2.
    clear - E1 E2 V1 V2 Alow. assert (Rabs (B a1) <= bpow radix2 (-54) * A) by (apply Rabs_le; bpow_num_all; split; lra).
    assert (Rabs (B a2) <= bpow radix2 (-54) * A) by (apply Rabs_le; bpow_num_all; split; lra). bpow_num_all. lra. }
  destruct (fadd16 _ _ Fa1 Fa2 ltac:(apply Rle_trans with (1 := W12); clear - Aup; bpow_num_all; lra)) as [Fa3 Ba3]. set (a3 := fadd a1 a2) in *.
  assert (E3 : Rabs (B a3 - (B a1 + B a2)) <= bpow radix2 (-53) * (bpow radix2 (-53) * A) + bpow radix2 (-1000) * A).
  { rewrite Ba3. pose proof (Rel (B a1 + B a2)). pose proof (bpow_ge_0 radix2 (-53)). nra. }
  assert (A2 : Rabs (B e2) <= 0.0016) by (apply Rabs_le; lra).
  destruct (fmul16 _ _ Fdh Fe2 ltac:(rewrite Rabs_mult; fold A; apply Rle_trans with (1 * 1); [apply Rmult_le_compat; try apply Rabs_pos; lra | lra])) as [Fa4 Ba4]. set (a4 := fmul dh e2) in *.
  assert (V4 : Rabs (B dh * B e2) <= 0.0016 * A) by (rewrite Rabs_mult; fold A; rewrite Rmult_comm; apply Rmult_le_compat_r; [unfold A; apply Rabs_pos | exact A2]).
  assert (E4 : Rabs (B a4 - B dh * B e2) <= bpow radix2 (-53) * (0.0016 * A) + bpow radix2 (-1000) * A).
  { rewrite Ba4. pose proof (Rel (B dh * B e2)). pose proof (bpow_ge_0 radix2 (-53)). nra. }
  assert (W34 : Rabs (B a3 + B a4) <= 0.00161 * A).
  { apply Rle_trans with (1 := Rabs_triang _ _). apply Rabs_le_inv in E3. apply Rabs_le_inv in E4. apply Rabs_le_inv in W12. apply Rabs_le_inv in V4.
    clear - E3 E4 W12 V4 Alow. assert (Rabs (B a3) <= bpow radix2 (-52) * A) by (apply Rabs_le; bpow_num_all; split; lra).
    assert (Rabs (B a4) <= 0.001601 * A) by (apply Rabs_le; bpow_num_all; split; lra). bpow_num_all. lra. }
  destruct (fadd16 _ _ Fa3 Fa4 ltac:(apply Rle_trans with (1 := W34); lra)) as [Fa5 Ba5]. set (a5 := fadd a3 a4) in *.
  assert (E5 : Rabs (B a5 - (B a3 + B a4)) <= bpow radix2 (-53) * (0.00161 * A) + bpow radix2 (-1000) * A).
  { rewrite Ba5. pose proof (Rel (B a3 + B a4)). pose proof (bpow_ge_0 radix2 (-53)). nra. }
  assert (W56 : Rabs (B qp + B a5) <= 0.00162 * A).
  { apply Rle_trans with (1 := Rabs_triang _ _). apply Rabs_le_inv in E5. apply Rabs_le_inv in W34.
    clear - E5 W34 Aqp Alow. assert (Rabs (B a5) <= 0.001611 * A) by (apply Rabs_le; bpow_num_all; split; lra). bpow_num_all. lra. }
  destruct (fadd16 _ _ Fqp Fa5 ltac:(apply Rle_trans with (1 := W56); lra)) as [Fa6 Ba6]. set (a6 := fadd qp a5) in *.
  assert (E6 : Rabs (B a6 - (B qp + B a5)) <= bpow radix2 (-53) * (0.00162 * A) + bpow radix2 (-1000) * A).
  { rewrite Ba6. pose proof (Rel (B qp + B a5)). pose proof (bpow_ge_0 radix2 (-53)). nra. }
  assert (W7 : Rabs (B dl + B a6) <= 0.00163 * A).
  { apply Rle_trans with (1 := Rabs_triang _ _). apply Rabs_le_inv in E6. apply Rabs_le_inv in W56.
    clear - E6 W56 Adl Alow. assert (Rabs (B a6) <= 0.001621 * A) by (apply Rabs_le; bpow_num_all; split; lra). bpow_num_all. lra. }
  destruct (fadd16 _ _ Fdl Fa6 ltac:(apply Rle_trans with (1 := W7); lra)) as [Fr Br]. set (rest := fadd dl a6) in *.
  assert (E7 : Rabs (B rest - (B dl + B a6)) <= bpow radix2 (-53) * (0.00163 * A) + bpow radix2 (-1000) * A).
  { rewrite Br. pose proof (Rel (B dl + B a6)). pose proof (bpow_ge_0 radix2 (-53)). nra. }
  assert (Arest : Rabs (B rest) <= 0.00164 * A).
  { apply Rabs_le_inv in E7. apply Rabs_le_inv in W7. clear - E7 W7 Alow. apply Rabs_le. bpow_num_all. split; lra. }
  (* s + s2 = dh + q exactly *)
  assert (DQ : 0.958 * A <= Rabs (B dh + B q) <= 1.042 * A).
  { pose proof (Rabs_triang_inv (B dh) (- B q)) as T1. pose proof (Rabs_triang (B dh) (B q)) as T2.
    rewrite Rabs_Ropp in T1. replace (B dh - - B q) with (B dh + B q) in T1 by ring. fold A in T1, T2. split; lra. }
  pose proof (fast_two_sum_ieee dh q Fdh Fq ltac:(fold A; apply Rle_trans with 1; [lra | bpow_num; lra])
    ltac:(apply Rle_trans with 1; [lra | bpow_num; lra]) ltac:(right; left; fold A; lra)) as FS1.
  revert FS1. generalize (fast_two_sum64 dh q). intros [s0 s2] FS1. destruct FS1 as [Fs0 [Fs2 [Bs0 Ss]]].
  assert (As2 : Rabs (B s2) <= bpow radix2 (-53) * (1.042 * A)).
  { replace (B s2) with (- (rndF (B dh + B q) - (B dh + B q))) by (rewrite <- Bs0; lra). rewrite Rabs_Ropp.
    pose proof (rnd_rel (B dh + B q)) as R.
    change (round radix2 (FLT_exp (-1074) 53) (Znearest (fun n => negb (Z.even n))) (B dh + B q)) with (rndF (B dh + B q)) in R.
    eapply Rle_trans; [apply R; apply Rle_trans with (2 := proj1 DQ); clear - Alow; bpow_num_all; lra | ].
    apply Rmult_le_compat_l; [apply bpow_ge_0 | lra]. }
  assert (As0 : 0.957 * A <= Rabs (B s0)).
  { replace (B s0) with ((B dh + B q) - B s2) by lra. pose proof (Rabs_triang_inv (B dh + B q) (B s2)) as T.
    clear - T DQ As2 Alow. bpow_num_all. lra. }
  assert (As0u : Rabs (B s0) <= 1.043 * A).
  { replace (B s0) with ((B dh + B q) - B s2) by lra. apply Rle_trans with (1 := Rabs_triang _ _).
    rewrite Rabs_Ropp. clear - DQ As2 Alow. bpow_num_all. lra. }
  (* u *)
  destruct (fadd16 _ _ Fs2 Fr ltac:(apply Rle_trans with (1 := Rabs_triang _ _); clear - As2 Arest Aup; bpow_num_all; lra)) as [Fu Bu].
  set (u := fadd s2 rest) in *.
  assert (Eu : Rabs (B u - (B s2 + B rest)) <= bpow radix2 (-53) * (0.00165 * A) + bpow radix2 (-1000) * A).
  { rewrite Bu. pose proof (Rel (B s2 + B rest)) as R. eapply Rle_trans; [exact R | ].
    apply Rplus_le_compat_r, Rmult_le_compat_l; [apply bpow_ge_0 | ]. apply Rle_trans with (1 := Rabs_triang _ _).
    clear - As2 Arest Alow. bpow_num_all. lra. }
  assert (Au : Rabs (B u) <= 0.0017 * A).
  { apply Rabs_le_inv in Eu. clear - Eu As2 Arest Alow. apply Rabs_le. assert (Rabs (B s2) <= 0.00001 * A) by (bpow_num_all; lra).
    apply Rabs_le_inv in Arest. apply Rabs_le_inv in H. bpow_num_all. split; lra. }
  pose proof (fast_two_sum_ieee s0 u Fs0 Fu ltac:(apply Rle_trans with 1; [clear - As0u Aup; lra | bpow_num; lra])
    ltac:(apply Rle_trans with 1; [lra | bpow_num; lra]) ltac:(right; left; lra)) as FS2.
  revert FS2. generalize (fast_two_sum64 s0 u). intros [ch cl] FS2. destruct FS2 as [Fch [Fcl [Bch Sum]]].
  (* the computed value against (dh + dl)·P *)
  set (Pc := 1 + B e1h + B e1l + B e2).
  assert (Assembly : Rabs (B ch + B cl - (B dh + B dl) * Pc) <= bpow radix2 (-53) * (0.015 * A) + bpow radix2 (-990) * A).
  { rewrite Sum. replace (B s0 + B u - (B dh + B dl) * Pc) with
      ((B u - (B s2 + B rest)) + (B rest - (B dl + B a6)) + (B a6 - (B qp + B a5)) + (B a5 - (B a3 + B a4))
       + (B a3 - (B a1 + B a2)) + (B a1 - B dh * B e1l) + (B a2 - B dl * B e1h) + (B a4 - B dh * B e2)
       - B dl * (B e1l + B e2)) by (unfold Pc; nra).
    assert (L : Rabs (B dl * (B e1l + B e2)) <= bpow radix2 (-51) * A * 0.0017).
    { rewrite Rabs_mult. apply Rmult_le_compat; try apply Rabs_pos; [exact Adl | ].
      apply Rle_trans with (1 := Rabs_triang _ _). clear - He1l A2. bpow_num_all. lra. }
    apply Rabs_le_inv in Eu. apply Rabs_le_inv in E7. apply Rabs_le_inv in E6. apply Rabs_le_inv in E5.
    apply Rabs_le_inv in E3. apply Rabs_le_inv in E1. apply Rabs_le_inv in E2. apply Rabs_le_inv in E4. apply Rabs_le_inv in L.
    clear - Eu E7 E6 E5 E3 E1 E2 E4 L Alow. apply Rabs_le. bpow_num_all. split; lra. }
  (* (dh + dl) against φ(0)·x *)
  set (Phi := normal_density_constant). set (P := Phi * Rabs (B x)).
  assert (PhiR : 0.39894 <= Phi <= 0.398943) by (unfold Phi, normal_density_constant; split; interval).
  assert (DW : Rabs (B normal_density_hi + B normal_density_lo - Phi) <= bpow radix2 (-105) * Phi).
  { pose proof normal_density_dw_error as D. change (/ sqrt (2 * PI)) with Phi in D.
    replace (B normal_density_hi + B normal_density_lo - Phi) with (((B normal_density_hi + B normal_density_lo) / Phi - 1) * Phi)
      by (field; lra). rewrite Rabs_mult, (Rabs_pos_eq Phi) by lra. apply Rmult_le_compat_r; lra. }
  assert (T3 : Rabs (B dh + B dl - Phi * B x) <= bpow radix2 (-100) * A).
  { replace (B dh + B dl - Phi * B x) with ((B dl - (B dp + B px)) + (B px - B normal_density_lo * B x)
      + (B normal_density_hi + B normal_density_lo - Phi) * B x)
      by (replace (B dh) with (B normal_density_hi * B x - B dp) by lra; ring).
    assert (M : Rabs ((B normal_density_hi + B normal_density_lo - Phi) * B x) <= bpow radix2 (-105) * (0.4 * Rabs (B x))).
    { rewrite Rabs_mult. apply Rle_trans with (bpow radix2 (-105) * Phi * Rabs (B x)).
      - apply Rmult_le_compat_r; [apply Rabs_pos | exact DW].
      - rewrite Rmult_assoc. apply Rmult_le_compat_l; [apply bpow_ge_0 | ]. apply Rmult_le_compat_r; [apply Rabs_pos | lra]. }
    apply Rabs_le_inv in M. apply Rabs_le_inv in Edl. apply Rabs_le_inv in Epx.
    clear - M Edl Epx Ar Alow. apply Rabs_le. bpow_num_all. split; lra. }
  assert (P0 : 0 <= P) by (unfold P; apply Rmult_le_pos; [lra | apply Rabs_pos]).
  assert (AP : A <= P * (1 + bpow radix2 (-49))).
  { assert (Hp : Rabs (Phi * B x) = P) by (unfold P; rewrite Rabs_mult, (Rabs_pos_eq Phi) by lra; reflexivity).
    pose proof (Rabs_triang (B dh + B dl - Phi * B x) (Phi * B x)) as T1.
    pose proof (Rabs_triang ((B dh + B dl - Phi * B x) + Phi * B x) (- B dl)) as T2.
    replace ((B dh + B dl - Phi * B x) + Phi * B x + - B dl) with (B dh) in T2 by ring.
    rewrite Rabs_Ropp in T2. fold A in T2. rewrite Hp in T1.
    assert (0 <= A) by (unfold A; apply Rabs_pos).
    clear - T1 T2 T3 Adl P0 H. bpow_num_all. lra. }
  (* the shape *)
  pose proof (center_first_E_shape (B x)) as Sh. fold E in Sh.
  pose proof (normal_center_mixed_tail_error (B x) (normal_center_tail_polynomial (B x * B x) 8) ltac:(lra)
    ltac:(unfold Rminus; rewrite Rplus_opp_r, Rabs_R0; apply bpow_ge_0)) as Tl.
  rewrite <- Sh in Tl. fold Phi in Tl. set (C := normal_center (B x)) in *.
  assert (Er : -0.0418 <= E <= 0.0017) by (apply Rabs_le_inv in PE; clear - PE He1h He1l He2; apply Rabs_le_inv in He1l; bpow_num_all; lra).
  assert (PxE : Rabs (Phi * B x * (1 + E)) = P * (1 + E)) by
    (unfold P; rewrite !Rabs_mult, (Rabs_pos_eq Phi), (Rabs_pos_eq (1 + E)) by lra; ring).
  assert (Clow : 0.958 * P <= Rabs C).
  { pose proof (Rabs_triang_inv (Phi * B x * (1 + E)) (Phi * B x * (1 + E) - C)) as T.
    replace (Phi * B x * (1 + E) - (Phi * B x * (1 + E) - C)) with C in T by ring. rewrite PxE in T.
    clear - T Tl Er P0. unfold P in *. bpow_num_all. nra. }
  assert (Pc1 : Rabs (Pc - (1 + E)) <= bpow radix2 (-60)) by (unfold Pc; replace (1 + B e1h + B e1l + B e2 - (1 + E)) with (B e1h + B e1l + B e2 - E) by ring; exact PE).
  assert (DD : Rabs (B dh + B dl) <= A * (1 + bpow radix2 (-51))).
  { apply Rle_trans with (1 := Rabs_triang _ _). fold A. lra. }
  assert (T2 : Rabs ((B dh + B dl) * (Pc - (1 + E))) <= A * (1 + bpow radix2 (-51)) * bpow radix2 (-60)).
  { rewrite Rabs_mult. apply Rmult_le_compat; try apply Rabs_pos; assumption. }
  assert (T3' : Rabs ((B dh + B dl - Phi * B x) * (1 + E)) <= bpow radix2 (-100) * A * 1.1).
  { rewrite Rabs_mult. apply Rmult_le_compat; try apply Rabs_pos; [exact T3 | apply Rabs_le; lra]. }
  assert (Main : Rabs (B ch + B cl - C) <= bpow radix2 (-53) * (0.015 * A) + bpow radix2 (-990) * A
      + A * (1 + bpow radix2 (-51)) * bpow radix2 (-60) + bpow radix2 (-100) * A * 1.1 + Phi * Rabs (B x) * bpow radix2 (-68)).
  { replace (B ch + B cl - C) with ((B ch + B cl - (B dh + B dl) * Pc) + (B dh + B dl) * (Pc - (1 + E))
      + (B dh + B dl - Phi * B x) * (1 + E) + (Phi * B x * (1 + E) - C)) by ring.
    apply Rabs_le_inv in Assembly. apply Rabs_le_inv in T2. apply Rabs_le_inv in T3'. apply Rabs_le_inv in Tl.
    apply Rabs_le. split; lra. }
  fold P in Main.
  assert (Fin : Rabs (B ch + B cl - C) <= / 5 * bpow radix2 (-56) * Rabs C).
  { assert (0 <= A) by (unfold A; apply Rabs_pos).
    clear - Main Clow AP H P0. bpow_num_all. nra. }
  assert (SU : 0.955 * A <= Rabs (B s0 + B u) <= 1.045 * A).
  { pose proof (Rabs_triang_inv (B s0) (- B u)) as U1. pose proof (Rabs_triang (B s0) (B u)) as U2.
    rewrite Rabs_Ropp in U1. replace (B s0 - - B u) with (B s0 + B u) in U1 by ring. split; lra. }
  assert (Ech : Rabs (B ch - (B s0 + B u)) <= bpow radix2 (-53) * (1.045 * A) + bpow radix2 (-1000) * A).
  { rewrite Bch. pose proof (Rel (B s0 + B u)). pose proof (bpow_ge_0 radix2 (-53)). nra. }
  assert (A33 : 0.39 * bpow radix2 (-33) <= A) by (apply Rle_trans with (2 := proj1 Ar); apply Rmult_le_compat_l; lra).
  repeat split; try assumption.
  - rewrite Sum. exact Bch.
  - pose proof (Rabs_triang (B ch - (B s0 + B u)) (B s0 + B u)) as T. replace (B ch - (B s0 + B u) + (B s0 + B u)) with (B ch) in T by ring.
    clear - T Ech SU Aup. bpow_num_all. lra.
  - pose proof (Rabs_triang_inv (B s0 + B u) (B s0 + B u - B ch)) as T. replace (B s0 + B u - (B s0 + B u - B ch)) with (B ch) in T by ring.
    rewrite Rabs_minus_sym in Ech. clear - T Ech SU A33. bpow_num_all. lra.
Qed.

(** A value the central first stage returns is the correctly rounded
    centered CDF or CDF. *)
Theorem normal_center_first_ok op x v : finite x -> bpow radix2 (-33) <= Rabs (B x) <= / 2 ->
  normal_center_first64 op x = Some v -> finite v /\ B v = rndF (normal_target op (B x)).
Proof.
  intros Fx X. pose proof (normal_center_first_parts_ok x Fx X) as P.
  unfold normal_center_first64. revert P. generalize (normal_center_first_parts64 x). intros [ch cl] P.
  destruct P as [Fch [Fcl [Rch [Hu [Hl Err]]]]].
  set (C := normal_center (B x)) in *.
  assert (Fa : finite (b64_abs ch)) by (unfold b64_abs; rewrite is_finite_Babs; exact Fch).
  pose proof (normal_tail_first_guard (b64_abs ch) Fa ltac:(rewrite B_abs; split; [apply Rle_trans with (2 := Hl); apply bpow_le; lia | lra])) as [Fe Ee].
  rewrite B_abs in Ee. set (e := fmul (b64_abs ch) normal_tail_first_e) in *.
  set (H := Rabs (B ch)) in *.
  (* the low word against the high word *)
  assert (Ncl : bpow radix2 (-1022) <= Rabs (B ch + B cl)).
  { destruct (Rle_lt_dec (bpow radix2 (-1022)) (Rabs (B ch + B cl))) as [L | L]; [exact L | exfalso].
    assert (Rabs (B ch) <= bpow radix2 (-1022)).
    { unfold rndF in Rch. rewrite Rch. apply abs_round_le_generic; auto with typeclass_instances; [ | lra].
      apply generic_format_bpow. unfold FLT_exp, emin, prec. lia. }
    fold H in H0. clear - H0 Hl. bpow_num_all. lra. }
  assert (Acl : Rabs (B cl) <= bpow radix2 (-53) * Rabs (B ch + B cl)).
  { pose proof (rnd_rel _ Ncl) as R. change (RNE (B ch + B cl)) with (rndF (B ch + B cl)) in R. rewrite <- Rch in R.
    replace (B ch - (B ch + B cl)) with (- B cl) in R by ring. rewrite Rabs_Ropp in R. exact R. }
  assert (Acl' : Rabs (B cl) <= bpow radix2 (-52) * H).
  { pose proof (Rabs_triang (B ch) (B cl)) as T. fold H in T. assert (0 <= H) by apply Rabs_pos. clear - Acl T H0. bpow_num_all. lra. }
  assert (Cup : Rabs C <= H * (1 + bpow radix2 (-51))).
  { pose proof (Rabs_triang_inv C (C - (B ch + B cl))) as T1. replace (C - (C - (B ch + B cl))) with (B ch + B cl) in T1 by ring.
    pose proof (Rabs_triang (B ch) (B cl)) as T2. fold H in T2. rewrite Rabs_minus_sym in Err.
    assert (0 <= Rabs C) by apply Rabs_pos. clear - T1 T2 Err Acl' H0. bpow_num_all. nra. }
  assert (Eps : / 5 * bpow radix2 (-56) * Rabs C <= / 5 * bpow radix2 (-56) * (H * (1 + bpow radix2 (-51))))
    by (apply Rmult_le_compat_l; [bpow_num_all; lra | exact Cup]).
  assert (H0 : 0 < H) by (apply Rlt_le_trans with (2 := Hl); apply bpow_gt_0).
  destruct op; try discriminate.
  - (* CDF: 1/2 + ch + cl *)
    destruct (erfcx_pow2_ok (-1) ltac:(lia)) as [Fh Bh]. change (bpow radix2 (-1)) with (/ 2) in Bh.
    pose proof (fast_two_sum_ieee (erfcx_pow2 (-1)) ch Fh Fch ltac:(rewrite Bh, (Rabs_pos_eq (/ 2)) by lra; bpow_num; lra)
      ltac:(fold H; bpow_num; lra) ltac:(right; left; rewrite Bh, (Rabs_pos_eq (/ 2)) by lra; fold H; lra)) as FS.
    revert FS. generalize (fast_two_sum64 (erfcx_pow2 (-1)) ch). intros [u w] FS. destruct FS as [Fu [Fw [Bu Uw]]].
    rewrite Bh in Bu, Uw.
    assert (Y : 0.29 <= / 2 + B ch <= 0.71) by (apply Rabs_le_inv in Hu; split; lra).
    assert (Aw : Rabs (B w) <= bpow radix2 (-53) * 0.71).
    { replace (B w) with (- (rndF (/ 2 + B ch) - (/ 2 + B ch))) by (rewrite <- Bu; lra). rewrite Rabs_Ropp.
      assert (N : bpow radix2 (-1022) <= Rabs (/ 2 + B ch)) by (rewrite Rabs_pos_eq by lra; bpow_num; lra).
      pose proof (rnd_rel _ N) as R. change (RNE (/ 2 + B ch)) with (rndF (/ 2 + B ch)) in R.
      rewrite (Rabs_pos_eq (/ 2 + B ch)) in R by lra. apply Rle_trans with (1 := R). apply Rmult_le_compat_l; [apply bpow_ge_0 | lra]. }
    assert (Au : Rabs (B u) <= 1).
    { replace (B u) with ((/ 2 + B ch) - B w) by lra. apply Rabs_le. apply Rabs_le_inv in Aw. bpow_num_all. lra. }
    assert (WC : Rabs (B w + B cl) <= bpow radix2 (-53) * 1.2).
    { apply Rle_trans with (1 := Rabs_triang _ _). clear - Aw Acl' Hu. bpow_num_all. lra. }
    destruct (fadd16 _ _ Fw Fcl ltac:(apply Rle_trans with (1 := WC); bpow_num; lra)) as [Fl Bl].
    pose proof (rnd_err_any (B w + B cl)) as El. rewrite <- Bl in El.
    set (l := fadd w cl) in *.
    set (eps := / 5 * bpow radix2 (-56) * (H * (1 + bpow radix2 (-51))) + bpow radix2 (-105)).
    assert (Hd : normal_interval_decide64 u l e = Some v -> finite v /\ B v = rndF (/ 2 + C)).
    { apply (normal_interval_decide_ok u l e (/ 2 + C) eps (-52) v Fu Fl Fe).
      - apply Rle_trans with 1; [exact Au | lra].
      - lia.
      - apply Rabs_le_inv in Ee. clear - Ee H0. bpow_num_all. lra.
      - apply Rabs_le_inv in Ee. clear - Ee El WC Hu. assert (Rabs (B l) <= bpow radix2 (-52) * 0.61).
        { apply Rabs_le. apply Rabs_le_inv in El. pose proof (Rabs_pos (B w + B cl)). pose proof (Rabs_le_inv _ _ WC) as WC2. bpow_num_all. split; lra. }
        bpow_num_all. lra.
      - unfold eps. change (-52 - 54)%Z with (-106)%Z. apply Rabs_le_inv in Ee. clear - Ee Hl H0. bpow_num_all. lra.
      - replace (/ 2 + C - (B u + B l)) with ((C - (B ch + B cl)) - (B l - (B w + B cl))) by lra.
        apply Rle_trans with (1 := Rabs_triang _ _). rewrite Rabs_Ropp, Rabs_minus_sym.
        unfold eps. clear - Err Eps El WC. bpow_num_all. lra. }
    intros D. destruct (Hd D) as [Fv Bv]. split; [exact Fv | ]. rewrite Bv. reflexivity.
  - (* centered *)
    assert (Qnz : B ch <> 0) by (intro Z; fold H in H0; unfold H in H0; rewrite Z, Rabs_R0 in H0; lra).
    pose proof (bpow_mag_le radix2 (B ch) Qnz) as Mlo. pose proof (bpow_mag_gt radix2 (B ch)) as Mhi.
    fold H in Mlo, Mhi. set (m := mag radix2 (B ch)) in *.
    assert (Mr : (-35 <= m <= -2)%Z).
    { assert (L1 : (-36 < m)%Z) by (apply (lt_bpow radix2); apply Rle_lt_trans with H; [exact Hl | exact Mhi]).
      assert (L2 : (m - 1 < -2)%Z) by (apply (lt_bpow radix2); apply Rle_lt_trans with (1 := Mlo); bpow_num; lra).
      lia. }
    assert (Cl53 : Rabs (B cl) <= bpow radix2 (-53) * H * (1 + bpow radix2 (-52))).
    { pose proof (Rabs_triang (B ch) (B cl)) as T. fold H in T. clear - Acl T Acl' H0. bpow_num_all. nra. }
    assert (Sm : bpow radix2 (m - 52 - 54) <= H * bpow radix2 (-105)).
    { replace (m - 52 - 54)%Z with ((m - 1) + -105)%Z by ring. rewrite bpow_plus.
      apply Rmult_le_compat_r; [apply bpow_ge_0 | exact Mlo]. }
    assert (Mh : H * bpow radix2 (-52) <= bpow radix2 (m - 52)).
    { replace (m - 52)%Z with (m + -52)%Z by ring. rewrite bpow_plus.
      apply Rmult_le_compat_r; [apply bpow_ge_0 | lra]. }
    set (eps := / 5 * bpow radix2 (-56) * (H * (1 + bpow radix2 (-51)))).
    intros D. apply (normal_interval_decide_ok ch cl e C eps (m - 52) v Fch Fcl Fe); try assumption.
    + fold H. bpow_num. lra.
    + lia.
    + apply Rabs_le_inv in Ee. clear - Ee H0. bpow_num_all. lra.
    + apply Rle_trans with (2 := Mh). apply Rabs_le_inv in Ee. clear - Ee Cl53 H0. bpow_num_all. lra.
    + unfold eps. apply Rabs_le_inv in Ee. clear - Ee Sm H0. bpow_num_all. lra.
    + rewrite Rabs_minus_sym. unfold eps. lra.
Qed.
