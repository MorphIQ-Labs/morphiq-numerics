(** exp/mod.rs's stage reduction [Stages::of] and the reduced arguments of
    stages A and B (docs/exp.md, section 3), transcribed on binary64 and
    proved, for every finite [|x| < 704]:
    - [stage_of_ok]: [n] is the integer [ni] nearest [RN(x·INV_N)], read back
      from the shifter's encoding; [j = ni mod 512] and [k = ni div 512]
      from its bits; [r1 = x − ni·L1] exactly; and the exact reduced argument
      [R = x − ni·ln 2/512] is at most [0.000677];
    - [stage_a_r_ok]: stage A's [r = r1 − RN(ni·L2D)] is [RN(R + dr)],
      [|dr| <= 2^-77] (formal/exp/stage_a_reduction.g);
    - [stage_b_r_ok]: stage B's [r_h], on [2^-40]'s grid, and [r_t], with
      [r1 − r_h] and [r1 − r_h − ni·L2] exact, have [|r_h + r_t − R| <= 2^-93]
      (formal/exp/stage_b_reduction.g). *)

From Coq Require Import ZArith Reals Lia Lra Psatz Classical.
From Flocq Require Import Core Relative IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Mul Grid Encodings RoundingConstant.
From Gappa Require Gappa_definitions Gappa_round_def.
From Interval Require Import Tactic.
Require ExpReduction ExpStageTables StageGappa.
Require exp_stage_a_reduction exp_stage_b_reduction.
Import ExpStageTables StageGappa.

Open Scope R_scope.

Notation shifter := ExpReduction.shifter.

(** * The index *)

(** [y + SHIFTER], for [|y| <= 2^50]: [1.5·2^52] plus the integer nearest [y]. *)
Lemma shifter_add y : finite y -> Rabs (B y) <= bpow radix2 50 ->
  finite (fadd y shifter) /\ B (fadd y shifter) = IZR (Znearest ne (B y) + 3 * 2 ^ 51).
Proof.
  intros Fy Hy. destruct ExpReduction.shifter_value as [Bs Fs].
  assert (Ha : bnd 1 53 (B y + B shifter)).
  { unfold bnd. rewrite Bs. change (IZR (3 * 2 ^ 51)) with 6755399441055744%R.
    change (bpow radix2 50) with 1125899906842624%R in Hy. change (IZR 1 * bpow radix2 53) with (1 * 9007199254740992)%R.
    apply Rabs_le_inv in Hy. apply Rabs_le. lra. }
  destruct (fadd_ok 1 53 y shifter Fy Fs ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) Ha) as [Fa Ba].
  split; [exact Fa | ]. rewrite Ba, Bs.
  assert (Mag : mag radix2 (B y + IZR (3 * 2 ^ 51)) = 53%Z :> BinNums.Z).
  { apply mag_unique. change (IZR (3 * 2 ^ 51)) with 6755399441055744%R.
    change (bpow radix2 50) with 1125899906842624%R in Hy.
    change (bpow radix2 (53 - 1)) with 4503599627370496%R. change (bpow radix2 53) with 9007199254740992%R.
    apply Rabs_le_inv in Hy. rewrite Rabs_pos_eq by lra. lra. }
  unfold round, scaled_mantissa, cexp. rewrite Mag. unfold FLT_exp, emin, prec.
  change (Z.max (53 - 53) (-1074)) with 0%Z. change (bpow radix2 (- 0)) with 1%R. rewrite Rmult_1_r.
  rewrite ExpReduction.znearest_shift by reflexivity. unfold F2R. cbn [Fnum Fexp].
  change (bpow radix2 0) with 1%R. ring.
Qed.

Lemma shifter_bits : bits_of_b64 shifter = 4843621399236968448%Z.
Proof. vm_compute. reflexivity. Qed.

(** A number [1.5·2^52 + m], [|m| <= 2^50], is encoded as [SHIFTER]'s
    encoding plus [m]. *)
Lemma shifted_bits t m : finite t -> B t = IZR (m + 3 * 2 ^ 51) -> (Z.abs m <= 2 ^ 50)%Z ->
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

(** [L = ln 2 / 512] and the constants' values. *)
Definition L : R := ln 2 / 512.

Lemma L_range : 0.001353803 <= L <= 0.0013538031.
Proof. unfold L. split; interval with (i_prec 64). Qed.

Lemma bpow_m (k : nat) : bpow radix2 (- Z.of_nat k) = / 2 ^ k.
Proof. rewrite bpow_opp, bpow_powerRZ, <- pow_powerRZ. reflexivity. Qed.

Lemma l1_eq : B st_l1 = IZR 1488522236 * bpow radix2 (-40).
Proof.
  rewrite st_l1_val. change (-40)%Z with (- Z.of_nat 40)%Z. rewrite bpow_m. field.
Qed.

Lemma l2_eq : B st_l2 = IZR (-387466026) * bpow radix2 (-72).
Proof.
  rewrite st_l2_val. unfold Rdiv. rewrite <- (bpow_m 96).
  change (-72)%Z with (24 + - Z.of_nat 96)%Z. rewrite bpow_plus.
  change (bpow radix2 24) with (IZR 16777216). rewrite <- Rmult_assoc, <- mult_IZR.
  reflexivity.
Qed.

Lemma l1_close : Rabs (L - B st_l1) <= bpow radix2 (-41).
Proof.
  unfold L. rewrite st_l1_val. change (-41)%Z with (- Z.of_nat 41)%Z. rewrite bpow_m.
  interval with (i_prec 100).
Qed.

(** An integer multiple of [2^q] below [2^(q + 53)] is representable. *)
Lemma grid_fmt_small q v : (-1074 <= q)%Z -> on_grid q v -> Rabs v < bpow radix2 (q + 53) -> fmtF v.
Proof.
  intros Hq [m ->] Hv. apply ExpReduction.fmt_int; [ | exact Hq].
  rewrite Rabs_mult, (Rabs_pos_eq (bpow radix2 q)) in Hv by apply bpow_ge_0.
  rewrite bpow_plus in Hv. rewrite <- abs_IZR in Hv.
  assert (IZR (Z.abs m) < bpow radix2 53) by (apply Rmult_lt_reg_r with (bpow radix2 q); [apply bpow_gt_0 | lra]).
  change (bpow radix2 53) with (IZR (2 ^ 53)) in H. apply lt_IZR in H. exact H.
Qed.

(** [Stages::of]: [(n, j, k, r1)]. *)
Definition stage_of (x : f64) : f64 * Z * Z * f64 :=
  let t := fadd (fmul x st_inv) shifter in
  let n := fsub t shifter in
  let ni := (bits_of_b64 t - bits_of_b64 shifter)%Z in
  (n, Z.land ni 511, Z.shiftr ni 9, fsub x (fmul n st_l1)).

Theorem stage_of_ok x : finite x -> Rabs (B x) < 704 ->
  let '(n, j, k, r1) := stage_of x in
  exists ni : Z, B n = IZR ni /\ finite n /\ (Z.abs ni <= 520018)%Z /\
    ni = (512 * k + j)%Z /\ (0 <= j < 512)%Z /\ (-1016 <= k <= 1016)%Z /\
    finite r1 /\ B r1 = B x - IZR ni * B st_l1 /\
    Rabs (B x - IZR ni * L) <= 0.000677 /\ Rabs (B r1) < bpow radix2 (-10) /\
    (ni <> 0%Z -> on_grid (-63) (B r1)) /\ (ni = 0%Z -> B r1 = B x).
Proof.
  intros Fx Hx. unfold stage_of.
  pose proof st_inv_finite as Fi. pose proof st_l1_finite as F1.
  pose proof L_range as Lr.
  assert (Iv : 738.6598 <= B st_inv <= 738.6599) by (rewrite st_inv_val; split; lra).
  (* y = RN(x·INV_N) *)
  assert (Xb : Rabs (B x * B st_inv) <= 520017).
  { rewrite Rabs_mult, (Rabs_pos_eq (B st_inv)) by lra. nra. }
  destruct (fmul_ok 1 20 x st_inv Fx Fi ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)
              ltac:(unfold bnd; change (bpow radix2 20) with 1048576; lra)) as [Fy By].
  set (y := fmul x st_inv) in *.
  assert (Yb : Rabs (B y) <= bpow radix2 50).
  { rewrite By. apply Rle_trans with (IZR 1 * bpow radix2 20).
    - apply bnd_round; [lia | lia | unfold bnd; change (bpow radix2 20) with 1048576; lra].
    - change (bpow radix2 20) with 1048576. change (bpow radix2 50) with 1125899906842624. lra. }
  destruct (shifter_add y Fy Yb) as [Ft Bt].
  set (t := fadd y shifter) in *.
  set (ni := Znearest ne (B y)) in *.
  assert (Hk : Rabs (B y - IZR ni) <= / 2) by (unfold ni; apply Znearest_half).
  pose proof (ExpReduction.rnd_abs_err (B x * B st_inv)) as Ey. rewrite <- By in Ey.
  change (bpow radix2 (-1074)) with (/ 202402253307310618352495346718917307049556649764142118356901358027430339567995346891960383701437124495187077864316811911389808737385793476867013399940738509921517424276566361364466907742093216341239767678472745068562007483424692698618103355649159556340810056512358769552333414615230502532186327508646006263307707741093494784)%R in Ey.
  (* |x/L − ni| <= 1/2 + 2^-31 *)
  assert (Ic : Rabs (B st_inv - / L) <= / 2 ^ 42).
  { replace (/ L) with (512 / ln 2) by (unfold L; field; interval with (i_prec 64)).
    exact st_inv_close. }
  assert (XL : Rabs (B x / L - IZR ni) <= / 2 + / 2147483648).
  { replace (B x / L - IZR ni) with (B x * (/ L - B st_inv) + (B x * B st_inv - B y) + (B y - IZR ni))
      by (unfold Rdiv; ring).
    assert (A1 : Rabs (B x * (/ L - B st_inv)) <= 704 * / 2 ^ 42).
    { rewrite Rabs_mult, Rabs_minus_sym. apply Rmult_le_compat; try apply Rabs_pos; lra. }
    assert (A2 : Rabs (B x * B st_inv - B y) <= / 9007199254740992 * 520017 + / 1000000000000).
    { rewrite Rabs_minus_sym. apply Rle_trans with (1 := Ey).
      assert (/ 9007199254740992 * Rabs (B x * B st_inv) <= / 9007199254740992 * 520017) by lra.
      pose proof (Rinv_0_lt_compat 202402253307310618352495346718917307049556649764142118356901358027430339567995346891960383701437124495187077864316811911389808737385793476867013399940738509921517424276566361364466907742093216341239767678472745068562007483424692698618103355649159556340810056512358769552333414615230502532186327508646006263307707741093494784 ltac:(lra)).
      lra. }
    assert (P42 : / 2 ^ 42 = / 4398046511104) by (simpl; lra).
    rewrite P42 in A1.
    eapply Rle_trans; [apply Rabs_triang | ]. eapply Rle_trans; [apply Rplus_le_compat_r, Rabs_triang | ]. lra. }
  assert (Ni : (Z.abs ni <= 520018)%Z).
  { assert (A : Rabs (B x / L) <= 520016.9).
    { unfold Rdiv. rewrite Rabs_mult, (Rabs_pos_eq (/ L)) by (apply Rlt_le, Rinv_0_lt_compat; lra).
      apply Rle_trans with (704 * / 0.001353803).
      - apply Rmult_le_compat; [apply Rabs_pos | apply Rlt_le, Rinv_0_lt_compat; lra | lra | ].
        apply Rinv_le_contravar; lra.
      - interval with (i_prec 64). }
    assert (T : Rabs (IZR ni - B x / L + B x / L) <= Rabs (IZR ni - B x / L) + Rabs (B x / L))
      by apply Rabs_triang.
    replace (IZR ni - B x / L + B x / L) with (IZR ni) in T by ring.
    rewrite Rabs_minus_sym in T.
    assert (Rabs (IZR ni) <= 520018) by lra.
    rewrite <- abs_IZR in H. apply le_IZR in H. lia. }
  (* n = t − SHIFTER *)
  destruct ExpReduction.shifter_value as [Bs Fs].
  assert (Hd : bnd 1 53 (B t - B shifter)).
  { unfold bnd. rewrite Bt, Bs, <- minus_IZR. replace (ni + 3 * 2 ^ 51 - 3 * 2 ^ 51)%Z with ni by ring.
    rewrite <- abs_IZR. replace (IZR 1 * bpow radix2 53) with (IZR (2 ^ 53)) by (simpl; ring). apply IZR_le. lia. }
  destruct (fsub_ok 1 53 t shifter Ft Fs ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) Hd) as [Fn Bn].
  assert (Bn' : B (fsub t shifter) = IZR ni).
  { rewrite Bn, Bt, Bs, <- minus_IZR. replace (ni + 3 * 2 ^ 51 - 3 * 2 ^ 51)%Z with ni by ring.
    apply round_generic; auto with typeclass_instances.
    replace (IZR ni) with (IZR ni * bpow radix2 0) by (change (bpow radix2 0) with 1; ring).
    apply ExpReduction.fmt_int; lia. }
  set (n := fsub t shifter) in *.
  assert (Bits : (bits_of_b64 t - bits_of_b64 shifter)%Z = ni).
  { rewrite (shifted_bits t ni Ft Bt ltac:(lia)), shifter_bits. ring. }
  rewrite Bits.
  (* j and k *)
  assert (Jk : Z.land ni 511 = (ni mod 512)%Z /\ Z.shiftr ni 9 = (ni / 512)%Z).
  { split; [change 511%Z with (Z.ones 9); rewrite Z.land_ones by lia; reflexivity
           | rewrite Z.shiftr_div_pow2 by lia; reflexivity]. }
  destruct Jk as [J K]. rewrite J, K.
  pose proof (Z.div_mod ni 512 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound ni 512 ltac:(lia)) as MB.
  (* r1 = x − ni·L1, exact *)
  assert (P1 : B n * B st_l1 = IZR (ni * 1488522236) * bpow radix2 (-40)).
  { rewrite Bn', l1_eq, mult_IZR. ring. }
  assert (P1f : fmtF (B n * B st_l1)).
  { rewrite P1. apply ExpReduction.fmt_int; [ | lia]. rewrite Z.abs_mul. change (2 ^ 53)%Z with 9007199254740992%Z. lia. }
  assert (P1b : Rabs (B n * B st_l1) <= 1024).
  { assert (C : 0 <= B st_l1 <= 0.001354) by (rewrite st_l1_val; split; interval with (i_prec 64)).
    rewrite Bn', Rabs_mult, <- abs_IZR. rewrite (Rabs_pos_eq (B st_l1)) by (destruct C; assumption).
    assert (0 <= IZR (Z.abs ni) <= 520018) by (split; apply IZR_le; lia). nra. }
  destruct (fmul_ok 1 10 n st_l1 Fn F1 ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)
              ltac:(unfold bnd; change (bpow radix2 10) with 1024; lra)) as [Fm1 Bm1].
  assert (Em1 : B (fmul n st_l1) = IZR ni * B st_l1).
  { rewrite Bm1, round_generic by (auto with typeclass_instances || exact P1f). rewrite Bn'. reflexivity. }
  set (R := B x - IZR ni * L).
  assert (HR : Rabs R <= 0.000677).
  { replace R with (L * (B x / L - IZR ni)) by (unfold R; field; lra).
    rewrite Rabs_mult, (Rabs_pos_eq L) by lra.
    apply Rle_trans with (0.0013538031 * (/ 2 + / 2147483648)); [ | lra].
    apply Rmult_le_compat; try lra. apply Rabs_pos. }
  assert (Dr : Rabs (B x - IZR ni * B st_l1) < bpow radix2 (-10)).
  { replace (B x - IZR ni * B st_l1) with (R + IZR ni * (L - B st_l1)) by (unfold R; ring).
    pose proof l1_close as C. change (bpow radix2 (-41)) with (/ 2199023255552) in C.
    change (bpow radix2 (-10)) with (/ 1024).
    apply Rle_lt_trans with (Rabs R + Rabs (IZR ni) * Rabs (L - B st_l1)).
    - rewrite <- Rabs_mult. apply Rabs_triang.
    - assert (Rabs (IZR ni) <= 520018) by (rewrite <- abs_IZR; apply IZR_le; lia).
      assert (Rabs (IZR ni) * Rabs (L - B st_l1) <= 520018 * / 2199023255552)
        by (apply Rmult_le_compat; try apply Rabs_pos; assumption).
      lra. }
  (* the grids, when ni <> 0: |x| >= 2^-12 *)
  assert (Big : ni <> 0%Z -> bpow radix2 (-11) <= Rabs (B x)).
  { intros N0. assert (K1 : 1 <= Rabs (IZR ni)) by (rewrite <- abs_IZR; apply IZR_le; lia).
    assert (Q : Rabs (B x / L) >= / 2 - / 2147483648).
    { pose proof (Rabs_triang_inv (IZR ni) (IZR ni - B x / L)) as T.
      replace (IZR ni - (IZR ni - B x / L)) with (B x / L) in T by ring.
      rewrite Rabs_minus_sym in T. lra. }
    replace (B x) with (L * (B x / L)) by (field; lra).
    rewrite Rabs_mult, (Rabs_pos_eq L) by lra.
    change (bpow radix2 (-11)) with (/ 2048). nra. }
  assert (Gr : ni <> 0%Z -> on_grid (-63) (B x - IZR ni * B st_l1)).
  { intros N0. apply grid_minus.
    - apply (grid_fmt_bound (FLT_exp emin prec) (-11)); [intros e; unfold FLT_exp, emin, prec; lia | apply B_fmt | right; exact (Big N0)].
    - apply grid_le with (-40)%Z; [lia | ]. rewrite l1_eq. exists (ni * 1488522236)%Z. rewrite mult_IZR. ring. }
  assert (Fr : fmtF (B x - IZR ni * B st_l1)).
  { destruct (Z.eq_dec ni 0) as [Z0 | N0].
    - rewrite Z0, Rmult_0_l, Rminus_0_r. apply B_fmt.
    - apply (grid_fmt_small (-63)); [lia | exact (Gr N0) | exact Dr]. }
  destruct (fsub_ok 1 0 x (fmul n st_l1) Fx Fm1 ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)
              ltac:(unfold bnd; rewrite Em1; change (bpow radix2 0) with 1;
                    change (bpow radix2 (-10)) with (/ 1024) in Dr; lra)) as [Fr1 Br1].
  assert (Er1 : B (fsub x (fmul n st_l1)) = B x - IZR ni * B st_l1)
    by (rewrite Br1, Em1; apply round_generic; [auto with typeclass_instances | exact Fr]).
  exists ni. rewrite Er1.
  split; [exact Bn' | split; [exact Fn | split; [exact Ni | split; [lia | split; [lia | split; [lia | ]]]]]].
  split; [exact Fr1 | split; [reflexivity | split; [exact HR | split; [exact Dr | split; [exact Gr | ]]]]].
  intros Z0. rewrite Z0, Rmult_0_l, Rminus_0_r. reflexivity.
Qed.

(** * Stage A's reduced argument *)

Lemma bnd_abs v c : IZR (-1) * c <= v <= IZR 1 * c -> Rabs v <= c.
Proof. intros [H1 H2]. apply Rabs_le. split; lra. Qed.

(** An integer is its own rounding to an integer. *)
Lemma rnd_int k : round radix2 (FIX_exp 0) Gappa_round_def.rndNE (IZR k) = IZR k.
Proof.
  apply round_generic; [unfold Gappa_round_def.rndNE; apply valid_rnd_N | ].
  apply generic_format_FIX. exists (Float radix2 k 0); [unfold F2R; simpl; ring | reflexivity].
Qed.

(** [L2D] as stage_a_reduction.g spells it. *)
Definition l2d_g : R := Gappa_definitions.float2R (Gappa_definitions.Float2 (-3250300606318355) (-95)).

Lemma l2d_g_eq : B st_l2d = l2d_g.
Proof.
  rewrite st_l2d_val. unfold l2d_g, Gappa_definitions.float2R, F2R. simpl.
  change (bpow radix2 (-96)) with (/ 39614081257132168796771975168). lra.
Qed.

(** formal/exp/stage_a_reduction.g's theorem. *)
Theorem stage_a_reduction_bound (R dL : R) (k : Z) :
  (Z.abs k <= 520018)%Z -> Rabs R <= 0.000677 -> Rabs dL <= bpow radix2 (-98) ->
  Rabs (R + IZR k * (l2d_g + dL) - rn (IZR k * l2d_g) - R) <= bpow radix2 (-77).
Proof.
  intros Hk HR HdL.
  assert (Hn : -520018 <= round radix2 (FIX_exp 0) Gappa_round_def.rndNE (IZR k) <= 520018)
    by (rewrite rnd_int; split; apply IZR_le; lia).
  apply Rabs_le_inv in HR. apply Rabs_le_inv in HdL.
  assert (G : IZR (-1) * bpow radix2 (-77)
              <= R + round radix2 (FIX_exp 0) Gappa_round_def.rndNE (IZR k) * (l2d_g + dL)
                 - rn (round radix2 (FIX_exp 0) Gappa_round_def.rndNE (IZR k) * l2d_g) - R
              <= IZR 1 * bpow radix2 (-77)).
  { unfold l2d_g. apply NNPP. intros Hneg. apply (exp_stage_a_reduction.l1 R (IZR k) dL).
    gappa_hyps. gappa_pick Hneg. }
  rewrite rnd_int in G. apply bnd_abs. exact G.
Qed.

Lemma rndF_rn v : rndF v = rn v.
Proof. reflexivity. Qed.

Lemma split_d : Rabs (L - B st_l1 - B st_l2d) <= bpow radix2 (-98).
Proof.
  pose proof st_l_split_d as H. change (-98)%Z with (- Z.of_nat 98)%Z. rewrite bpow_m.
  replace (L - B st_l1 - B st_l2d) with (- (B st_l1 + B st_l2d - ln 2 / 512)) by (unfold L; ring).
  rewrite Rabs_Ropp. exact H.
Qed.

(** Stage A's [r = r1 − n·L2D]: [RN(R + dr)], [|dr| <= 2^-77]. *)
Theorem stage_a_r_ok n r1 (ni : Z) (X : R) :
  finite n -> B n = IZR ni -> (Z.abs ni <= 520018)%Z -> finite r1 ->
  B r1 = X - IZR ni * B st_l1 -> Rabs (X - IZR ni * L) <= 0.000677 -> Rabs (B r1) < bpow radix2 (-10) ->
  finite (fsub r1 (fmul n st_l2d)) /\
  B (fsub r1 (fmul n st_l2d)) = rn (B r1 - B (fmul n st_l2d)) /\
  Rabs (B r1 - B (fmul n st_l2d) - (X - IZR ni * L)) <= bpow radix2 (-77).
Proof.
  intros Fn Bn Hn Fr1 Br1 HR Hr1.
  assert (C : Rabs (B st_l2d) <= / 1000000000000) by (rewrite st_l2d_val; interval with (i_prec 64)).
  assert (Ni : Rabs (IZR ni) <= 520018) by (rewrite <- abs_IZR; apply IZR_le; lia).
  assert (Pm : Rabs (B n * B st_l2d) <= 16).
  { rewrite Bn, Rabs_mult. apply Rle_trans with (520018 * / 1000000000000); [ | lra].
    apply Rmult_le_compat; try apply Rabs_pos; assumption. }
  destruct (fmul16 n st_l2d Fn st_l2d_finite Pm) as [Fp Bp].
  assert (Pb : Rabs (B (fmul n st_l2d)) <= 1).
  { rewrite Bp. apply abs_round_le_generic; auto with typeclass_instances.
    - change 1 with (bpow radix2 0). apply generic_format_bpow. unfold FLT_exp, emin, prec. lia.
    - rewrite Bn, Rabs_mult. apply Rle_trans with (520018 * / 1000000000000); [ | lra].
      apply Rmult_le_compat; try apply Rabs_pos; assumption. }
  change (bpow radix2 (-10)) with (/ 1024) in Hr1.
  destruct (fsub16 r1 (fmul n st_l2d) Fr1 Fp) as [Fr Br].
  { apply Rle_trans with (Rabs (B r1) + Rabs (B (fmul n st_l2d))); [ | lra].
    unfold Rminus. rewrite <- (Rabs_Ropp (B (fmul n st_l2d))). apply Rabs_triang. }
  split; [exact Fr | split; [exact Br | ]].
  set (R := X - IZR ni * L) in *.
  pose proof (stage_a_reduction_bound R (L - B st_l1 - B st_l2d) ni Hn HR split_d) as G.
  rewrite <- l2d_g_eq in G.
  replace (R + IZR ni * (B st_l2d + (L - B st_l1 - B st_l2d))) with (B r1) in G by (rewrite Br1; unfold R; ring).
  rewrite Bp, Bn. exact G.
Qed.

(** * Stage B's reduced argument *)

(** [L2] and [L3] as stage_b_reduction.g spells them. *)
Definition l2_g : R := Gappa_definitions.float2R (Gappa_definitions.Float2 (-193733013) (-71)).
Definition l3_g : R := Gappa_definitions.float2R (Gappa_definitions.Float2 (-7615381615019653) (-128)).

Lemma l2_g_eq : B st_l2 = l2_g.
Proof.
  rewrite l2_eq. unfold l2_g, Gappa_definitions.float2R, F2R. cbn [Defs.Fnum Defs.Fexp Gappa_definitions.Fnum Gappa_definitions.Fexp].
  change (-72)%Z with (-1 + -71)%Z. rewrite bpow_plus, <- Rmult_assoc. f_equal.
  change (bpow radix2 (-1)) with (/ 2). rewrite !IZR_NEG. field.
Qed.

Lemma l3_g_eq : B st_l3 = l3_g.
Proof.
  rewrite st_l3_val. unfold l3_g, Gappa_definitions.float2R, F2R. cbn [Defs.Fnum Defs.Fexp Gappa_definitions.Fnum Gappa_definitions.Fexp].
  unfold Rdiv. rewrite <- (bpow_m 128). reflexivity.
Qed.

(** formal/exp/stage_b_reduction.g's theorem. *)
Theorem stage_b_reduction_bound (R dL dh : R) (k : Z) :
  (Z.abs k <= 520018)%Z -> Rabs R <= 0.000677 -> Rabs dL <= bpow radix2 (-129) ->
  Rabs dh <= bpow radix2 (-41) ->
  let r1 := R + IZR k * (l2_g + l3_g + dL) in
  let rh := rn (r1 - IZR k * l2_g) + dh in
  let rt := rn (r1 - rh - IZR k * l2_g - rn (IZR k * l3_g)) in
  Rabs (rh + rt - R) <= bpow radix2 (-93) /\ Rabs rt <= bpow radix2 (-40) /\ Rabs rh <= 0.000678.
Proof.
  intros Hk HR HdL Hdh. cbv zeta.
  assert (Hn : -520018 <= round radix2 (FIX_exp 0) Gappa_round_def.rndNE (IZR k) <= 520018)
    by (rewrite rnd_int; split; apply IZR_le; lia).
  apply Rabs_le_inv in HR. apply Rabs_le_inv in HdL. apply Rabs_le_inv in Hdh.
  rewrite <- (rnd_int k). unfold l2_g, l3_g.
  split; [ | split]; apply Rabs_le.
  - gappa_goal (exp_stage_b_reduction.l1 R (IZR k) dL dh).
  - gappa_goal (exp_stage_b_reduction.l1 R (IZR k) dL dh).
  - gappa_goal (exp_stage_b_reduction.l1 R (IZR k) dL dh).
Qed.

(** exp/mod.rs's [SPLIT], [1.5·2^12]. *)
Definition c_split : f64 := b64_of_bits 4663477414142148608.   (* 0x40b8000000000000 *)
Lemma c_split_val : B c_split = 6144.
Proof.
  unfold c_split. rewrite (bits_val 4663477414142148608 false 6755399441055744 40 eq_refl).
  simpl. field.
Qed.
Lemma c_split_finite : finite c_split.
Proof. exact (bits_finite 4663477414142148608 _ _ _ eq_refl). Qed.

(** [(v + SPLIT) − SPLIT] rounds [v], [|v| <= 2^-10], to the nearest multiple
    of [2^-40], ties to even. *)
Lemma split_round v : finite v -> Rabs (B v) <= bpow radix2 (-10) ->
  let h := fsub (fadd v c_split) c_split in
  finite h /\ B h = IZR (Znearest ne (B v * bpow radix2 40)) * bpow radix2 (-40).
Proof.
  intros Fv Hv h. pose proof c_split_val as Bs. pose proof c_split_finite as Fs.
  change (bpow radix2 (-10)) with (/ 1024) in Hv. apply Rabs_le_inv in Hv.
  destruct (fadd_ok 1 13 v c_split Fv Fs ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)
              ltac:(unfold bnd; rewrite Bs; change (bpow radix2 13) with 8192; apply Rabs_le; lra)) as [Fa Ba].
  set (K := Znearest ne (B v * bpow radix2 40)).
  assert (Ra : B (fadd v c_split) = IZR (K + 3 * 2 ^ 51) * bpow radix2 (-40)).
  { rewrite Ba, Bs.
    assert (Mag : mag radix2 (B v + 6144) = 13%Z :> BinNums.Z).
    { apply mag_unique. change (bpow radix2 (13 - 1)) with 4096. change (bpow radix2 13) with 8192.
      rewrite Rabs_pos_eq by lra. lra. }
    unfold round, scaled_mantissa, cexp. rewrite Mag. unfold FLT_exp, emin, prec.
    change (Z.max (13 - 53) (-1074)) with (-40)%Z. change (- -40)%Z with 40%Z.
    replace ((B v + 6144) * bpow radix2 40) with (B v * bpow radix2 40 + IZR (3 * 2 ^ 51))
      by (change (bpow radix2 40) with 1099511627776; change (IZR (3 * 2 ^ 51)) with 6755399441055744; ring).
    rewrite ExpReduction.znearest_shift by reflexivity. reflexivity. }
  assert (Kb : (Z.abs K <= 2 ^ 31)%Z).
  { assert (Hk : Rabs (B v * bpow radix2 40 - IZR K) <= / 2) by (unfold K; apply Znearest_half).
    change (bpow radix2 40) with 1099511627776 in Hk. apply Rabs_le_inv in Hk.
    assert (Rabs (IZR K) <= 2147483648) by (apply Rabs_le; lra).
    rewrite <- abs_IZR in H. apply le_IZR in H. change (2 ^ 31)%Z with 2147483648%Z. exact H. }
  assert (Hd : bnd 1 13 (B (fadd v c_split) - B c_split)).
  { unfold bnd. rewrite Ra, Bs. change (bpow radix2 13) with 8192. change (bpow radix2 (-40)) with (/ 1099511627776).
    rewrite plus_IZR. change (IZR (3 * 2 ^ 51)) with 6755399441055744.
    assert (Rabs (IZR K) <= 2147483648) by (rewrite <- abs_IZR; apply IZR_le; change (2 ^ 31)%Z with 2147483648%Z in Kb; lia).
    apply Rabs_le_inv in H. apply Rabs_le. lra. }
  destruct (fsub_ok 1 13 _ _ Fa Fs ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) Hd) as [Fh Bh].
  split; [exact Fh | ]. unfold h. rewrite Bh, Ra, Bs.
  replace (IZR (K + 3 * 2 ^ 51) * bpow radix2 (-40) - 6144) with (IZR K * bpow radix2 (-40))
    by (rewrite plus_IZR; change (IZR (3 * 2 ^ 51)) with 6755399441055744; change (bpow radix2 (-40)) with (/ 1099511627776); field).
  apply round_generic; auto with typeclass_instances. apply ExpReduction.fmt_int; [ | lia].
  change (2 ^ 31)%Z with 2147483648%Z in Kb. change (2 ^ 53)%Z with 9007199254740992%Z. lia.
Qed.

Lemma split_3 : Rabs (L - B st_l1 - B st_l2 - B st_l3) <= bpow radix2 (-129).
Proof.
  pose proof st_l_split as H. change (-129)%Z with (- Z.of_nat 129)%Z. rewrite bpow_m.
  replace (L - B st_l1 - B st_l2 - B st_l3) with (- (B st_l1 + B st_l2 + B st_l3 - ln 2 / 512)) by (unfold L; ring).
  rewrite Rabs_Ropp. exact H.
Qed.

(** Stage B's [r_h] and [r_t]: [r_h] on [2^-40]'s grid, and
    [|r_h + r_t − R| <= 2^-93]. *)
Theorem stage_b_r_ok x n r1 (ni : Z) :
  finite x -> finite n -> B n = IZR ni -> (Z.abs ni <= 520018)%Z -> finite r1 ->
  B r1 = B x - IZR ni * B st_l1 -> Rabs (B x - IZR ni * L) <= 0.000677 ->
  Rabs (B r1) < bpow radix2 (-10) ->
  (ni <> 0%Z -> on_grid (-63) (B r1)) -> (ni = 0%Z -> B r1 = B x) ->
  let p2 := fmul n st_l2 in
  let rh := fsub (fadd (fsub r1 p2) c_split) c_split in
  let rt := fsub (fsub (fsub r1 rh) p2) (fmul n st_l3) in
  finite rh /\ finite rt /\ on_grid (-40) (B rh) /\ Rabs (B rh) <= 0.000678 /\
  Rabs (B rt) <= bpow radix2 (-40) /\ Rabs (B rh + B rt - (B x - IZR ni * L)) <= bpow radix2 (-93).
Proof.
  intros Fx Fn Bn Hn Fr1 Br1 HR Hr1 G1 Z1 p2 rh rt.
  pose proof L_range as Lr.
  assert (Ni : Rabs (IZR ni) <= 520018) by (rewrite <- abs_IZR; apply IZR_le; lia).
  (* p2 = n·L2, exact *)
  assert (P2v : B n * B st_l2 = IZR (ni * -387466026) * bpow radix2 (-72)) by (rewrite Bn, l2_eq, mult_IZR; ring).
  assert (L2b : Rabs (B st_l2) <= / 10000000000000) by (rewrite st_l2_val; interval with (i_prec 64)).
  assert (P2b : Rabs (B n * B st_l2) <= / 1000000) .
  { rewrite Bn, Rabs_mult. apply Rle_trans with (520018 * / 10000000000000); [ | lra].
    apply Rmult_le_compat; try apply Rabs_pos; assumption. }
  destruct (fmul16 n st_l2 Fn st_l2_finite ltac:(lra)) as [Fp2 Bp2'].
  assert (Bp2 : B p2 = B n * B st_l2).
  { unfold p2. rewrite Bp2'. apply round_generic; auto with typeclass_instances. rewrite P2v.
    apply ExpReduction.fmt_int; [ | lia]. rewrite Z.abs_mul. change (2 ^ 53)%Z with 9007199254740992%Z. lia. }
  (* r0 *)
  assert (L23 : Rabs (L - B st_l1 - B st_l2) <= / 10000000000000000000000).
  { pose proof split_3 as S. change (bpow radix2 (-129)) with (/ 680564733841876926926749214863536422912) in S.
    assert (Rabs (B st_l3) <= / 25000000000000000000000) by (rewrite st_l3_val; interval with (i_prec 64)).
    replace (L - B st_l1 - B st_l2) with ((L - B st_l1 - B st_l2 - B st_l3) + B st_l3) by ring.
    apply Rle_trans with (1 := Rabs_triang _ _). lra. }
  set (R := B x - IZR ni * L) in *.
  assert (V0 : B r1 - B p2 = R + IZR ni * (L - B st_l1 - B st_l2)) by (rewrite Bp2, Br1, Bn; unfold R; ring).
  assert (V0b : Rabs (B r1 - B p2) <= bpow radix2 (-10)).
  { rewrite V0. change (bpow radix2 (-10)) with (/ 1024).
    apply Rle_trans with (1 := Rabs_triang _ _). rewrite Rabs_mult.
    assert (Rabs (IZR ni) * Rabs (L - B st_l1 - B st_l2) <= 520018 * / 10000000000000000000000)
      by (apply Rmult_le_compat; try apply Rabs_pos; assumption).
    lra. }
  destruct (fsub16 r1 p2 Fr1 Fp2 ltac:(change (bpow radix2 (-10)) with (/ 1024) in V0b; lra)) as [Fr0 Br0].
  set (r0 := fsub r1 p2) in *.
  assert (R0b : Rabs (B r0) <= bpow radix2 (-10)).
  { rewrite Br0. apply abs_round_le_generic; try exact V0b;
      try (apply generic_format_bpow; unfold FLT_exp, emin, prec; lia); auto with typeclass_instances. }
  assert (E0 : Rabs (B r0 - (B r1 - B p2)) <= bpow radix2 (-64)).
  { rewrite Br0. apply (rnd_err_below _ (-10)); [lia | exact V0b]. }
  (* r_h *)
  destruct (split_round r0 Fr0 R0b) as [Frh Brh]. fold rh in Frh, Brh.
  set (K := Znearest ne (B r0 * bpow radix2 40)) in Brh.
  assert (Dh : Rabs (B rh - B r0) <= bpow radix2 (-41)).
  { pose proof (Znearest_half ne (B r0 * bpow radix2 40)) as H. fold K in H.
    replace (B rh - B r0) with (- ((B r0 * bpow radix2 40 - IZR K) * bpow radix2 (-40))) by
      (rewrite Brh; change (bpow radix2 40) with 1099511627776; change (bpow radix2 (-40)) with (/ 1099511627776); field).
    rewrite Rabs_Ropp, Rabs_mult, (Rabs_pos_eq (bpow radix2 (-40))) by apply bpow_ge_0.
    change (bpow radix2 (-40)) with (/ 1099511627776). change (bpow radix2 (-41)) with (/ 2199023255552). lra. }
  assert (Grh : on_grid (-40) (B rh)) by (rewrite Brh; exists K; reflexivity).
  (* r1 − r_h, exact *)
  assert (Bp2b : Rabs (B p2) <= / 1000000) by (rewrite Bp2; exact P2b).
  assert (U1f : fmtF (B r1 - B rh)).
  { destruct (Z.eq_dec ni 0) as [Z0 | N0].
    - assert (P0 : B p2 = 0) by (rewrite Bp2, Bn, Z0; ring).
      destruct (Z.eq_dec K 0) as [K0 | K1].
      + replace (B r1 - B rh) with (B r1) by (rewrite Brh, K0; ring). apply B_fmt.
      + (* |r1| >= 2^-42: r1 is on 2^-94's grid *)
        assert (R0e : B r0 = B r1).
        { rewrite Br0, P0, Rminus_0_r. apply round_generic; auto with typeclass_instances. apply B_fmt. }
        assert (Hk : bpow radix2 (-40) <= Rabs (B rh)).
        { rewrite Brh, Rabs_mult, (Rabs_pos_eq (bpow radix2 (-40))) by apply bpow_ge_0.
          rewrite <- abs_IZR. assert (1 <= IZR (Z.abs K)) by (apply IZR_le; lia).
          pose proof (bpow_gt_0 radix2 (-40)). nra. }
        assert (Big : bpow radix2 (-41) <= Rabs (B r1)).
        { rewrite <- R0e. pose proof (Rabs_triang_inv (B rh) (B rh - B r0)) as T.
          replace (B rh - (B rh - B r0)) with (B r0) in T by ring.
          change (bpow radix2 (-40)) with (/ 1099511627776) in Hk. change (bpow radix2 (-41)) with (/ 2199023255552) in *. lra. }
        apply (grid_fmt_small (-93)); [lia | | ].
        * apply grid_minus; [ | apply grid_le with (-40)%Z; [lia | exact Grh]].
          apply (grid_fmt_bound (FLT_exp emin prec) (-41)); [intros e; unfold FLT_exp, emin, prec; lia | apply B_fmt | right; exact Big].
        * rewrite <- R0e, <- Rabs_Ropp, Ropp_minus_distr. apply Rle_lt_trans with (1 := Dh).
          apply bpow_lt. lia.
    - apply (grid_fmt_small (-63)); [lia | | ].
      + apply grid_minus; [exact (G1 N0) | apply grid_le with (-40)%Z; [lia | exact Grh]].
      + replace (B r1 - B rh) with ((B r1 - B p2 - B r0) + B p2 - (B rh - B r0)) by ring.
        rewrite Rabs_minus_sym in E0.
        change (bpow radix2 (-64)) with (/ 18446744073709551616) in E0. change (bpow radix2 (-41)) with (/ 2199023255552) in Dh.
        change (bpow radix2 (-63 + 53)) with (/ 1024).
        apply Rle_lt_trans with (Rabs (B r1 - B p2 - B r0) + Rabs (B p2) + Rabs (B rh - B r0)).
        * unfold Rminus at 1. apply Rle_trans with (Rabs (B r1 - B p2 - B r0 + B p2) + Rabs (- (B rh - B r0))).
          { apply Rabs_triang. }
          rewrite Rabs_Ropp. pose proof (Rabs_triang (B r1 - B p2 - B r0) (B p2)). lra.
        * lra. }
  assert (U1b : Rabs (B r1 - B rh) <= 1).
  { replace (B r1 - B rh) with ((B r1 - B p2 - B r0) + B p2 - (B rh - B r0)) by ring.
    rewrite Rabs_minus_sym in E0.
    change (bpow radix2 (-64)) with (/ 18446744073709551616) in E0. change (bpow radix2 (-41)) with (/ 2199023255552) in Dh.
    apply Rle_trans with (Rabs (B r1 - B p2 - B r0 + B p2) + Rabs (- (B rh - B r0))); [apply Rabs_triang | ].
    rewrite Rabs_Ropp. pose proof (Rabs_triang (B r1 - B p2 - B r0) (B p2)). lra. }
  destruct (fsub16 r1 rh Fr1 Frh ltac:(lra)) as [Fu1 Bu1'].
  assert (Bu1 : B (fsub r1 rh) = B r1 - B rh) by (rewrite Bu1'; apply round_generic; auto with typeclass_instances).
  (* (r1 − r_h) − p2, exact *)
  assert (Uv : B (fsub r1 rh) - B p2 = (B r1 - B p2 - B r0) - (B rh - B r0)) by (rewrite Bu1; ring).
  assert (Ub : Rabs (B (fsub r1 rh) - B p2) <= bpow radix2 (-40)).
  { rewrite Uv. rewrite Rabs_minus_sym in E0.
    change (bpow radix2 (-64)) with (/ 18446744073709551616) in E0. change (bpow radix2 (-41)) with (/ 2199023255552) in Dh.
    change (bpow radix2 (-40)) with (/ 1099511627776).
    unfold Rminus at 1. apply Rle_trans with (1 := Rabs_triang _ _). rewrite Rabs_Ropp. lra. }
  assert (Uf : fmtF (B (fsub r1 rh) - B p2)).
  { destruct (Z.eq_dec ni 0) as [Z0 | N0].
    - assert (P0 : B p2 = 0) by (rewrite Bp2, Bn, Z0; ring).
      rewrite P0, Rminus_0_r. apply B_fmt.
    - apply (grid_fmt_small (-72)); [lia | | ].
      + rewrite Bu1. apply grid_minus; [apply grid_minus | ].
        * apply grid_le with (-63)%Z; [lia | exact (G1 N0)].
        * apply grid_le with (-40)%Z; [lia | exact Grh].
        * rewrite Bp2, P2v. exists (ni * -387466026)%Z. reflexivity.
      + apply Rle_lt_trans with (1 := Ub). apply bpow_lt. lia. }
  destruct (fsub16 (fsub r1 rh) p2 Fu1 Fp2 ltac:(change (bpow radix2 (-40)) with (/ 1099511627776) in Ub; lra)) as [Fu Bu'].
  assert (Bu : B (fsub (fsub r1 rh) p2) = B r1 - B rh - B p2)
    by (rewrite Bu', round_generic by (auto with typeclass_instances || exact Uf); rewrite Bu1; ring).
  (* p3 and r_t *)
  assert (L3b : Rabs (B st_l3) <= / 25000000000000000000000) by (rewrite st_l3_val; interval with (i_prec 64)).
  destruct (fmul16 n st_l3 Fn st_l3_finite) as [Fp3 Bp3].
  { rewrite Bn, Rabs_mult. apply Rle_trans with (520018 * / 25000000000000000000000); [ | lra].
    apply Rmult_le_compat; try apply Rabs_pos; assumption. }
  assert (P3b : Rabs (B (fmul n st_l3)) <= 1).
  { rewrite Bp3. apply abs_round_le_generic; auto with typeclass_instances.
    - change 1 with (bpow radix2 0). apply generic_format_bpow. unfold FLT_exp, emin, prec. lia.
    - rewrite Bn, Rabs_mult. apply Rle_trans with (520018 * / 25000000000000000000000); [ | lra].
      apply Rmult_le_compat; try apply Rabs_pos; assumption. }
  destruct (fsub16 (fsub (fsub r1 rh) p2) (fmul n st_l3) Fu Fp3) as [Frt Brt].
  { rewrite Bu. replace (B r1 - B rh - B p2) with (B (fsub r1 rh) - B p2) by (rewrite Bu1; ring).
    change (bpow radix2 (-40)) with (/ 1099511627776) in Ub.
    unfold Rminus at 1. apply Rle_trans with (1 := Rabs_triang _ _). rewrite Rabs_Ropp. lra. }
  fold rt in Frt, Brt.
  (* the certificate *)
  pose proof (stage_b_reduction_bound R (L - B st_l1 - B st_l2 - B st_l3) (B rh - B r0) ni Hn HR split_3 Dh) as SB.
  cbv zeta in SB. rewrite <- l2_g_eq, <- l3_g_eq in SB.
  replace (R + IZR ni * (B st_l2 + B st_l3 + (L - B st_l1 - B st_l2 - B st_l3))) with (B r1) in SB
    by (rewrite Br1; unfold R; ring).
  replace (rn (B r1 - IZR ni * B st_l2)) with (B r0) in SB
    by (rewrite Br0, Bp2, Bn; reflexivity).
  replace (B r0 + (B rh - B r0)) with (B rh) in SB by ring.
  replace (rn (B r1 - B rh - IZR ni * B st_l2 - rn (IZR ni * B st_l3))) with (B rt) in SB
    by (rewrite Brt, Bu, Bp3, Bp2, Bn; reflexivity).
  destruct SB as [S1 [S2 S3]].
  repeat split; assumption.
Qed.
