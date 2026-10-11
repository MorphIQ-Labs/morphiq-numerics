(** exp/mod.rs's stage A ([Stages::a_value] and [Stages::a], docs/exp.md,
    sections 5 and 7), transcribed on binary64 and proved:
    - [stage_a_value_ok]: for the reduction of [ExpStageReduction.stage_of],
      [y + l = th + fl] is within [302·2^-69 < 2^-60.7] of [T_j·e^R], where
      [T_j = 2^(j/512)] and [R] is the exact reduced argument, and
      [|fl| <= 181·2^-17]: formal/exp/stage_a.g's theorem, with its
      hypotheses proved here (the reduction, formal/exp/stage_mvt.g, the
      approximation and table bounds of ExpStageTables.v);
    - [exp_stage_a_ok]: for every finite [|x| < 704], when stage A's test
      passes, the returned value is [RN(e^x)]
      (formal/binary64/RoundingConstant.v, with [E_A = 1.5·2^-61 >= 302·2^-69
      + 2^-63]).
    The stages' polynomial, its certificates' spelling and the mean value
    term are shared with stage B (ExpStageB.v). *)

From Coq Require Import ZArith Reals Lia Lra Psatz Classical.
From Flocq Require Import Core Relative IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Mul Grid Encodings RoundingConstant.
From Gappa Require Gappa_definitions Gappa_round_def.
From Interval Require Import Tactic.
Require Import TableCheck.
Require ExpReduction ExpStageTables StageGappa ExpStageReduction.
Require exp_stage_a exp_stage_mvt.
Import ExpStageTables StageGappa ExpStageReduction.

Open Scope R_scope.

(** The stages' coefficients as the certificates spell them. *)
Definition d3_g : R := Gappa_definitions.float2R (Gappa_definitions.Float2 1501199875790165 (-53)).
Definition d4_g : R := Gappa_definitions.float2R (Gappa_definitions.Float2 1501199896296289 (-55)).
Definition d5_g : R := Gappa_definitions.float2R (Gappa_definitions.Float2 4803839709418455 (-59)).

Lemma d3_g_eq : B st_d3 = d3_g.
Proof.
  rewrite st_d3_val. unfold d3_g, Gappa_definitions.float2R, F2R.
  cbn [Defs.Fnum Defs.Fexp Gappa_definitions.Fnum Gappa_definitions.Fexp].
  unfold Rdiv. rewrite <- (bpow_m 55). change (IZR 6004799503160660) with (IZR (1501199875790165 * 4)).
  rewrite mult_IZR. change (IZR 4) with (bpow radix2 2). rewrite Rmult_assoc, <- bpow_plus. reflexivity.
Qed.
Lemma d4_g_eq : B st_d4 = d4_g.
Proof.
  rewrite st_d4_val. unfold d4_g, Gappa_definitions.float2R, F2R.
  cbn [Defs.Fnum Defs.Fexp Gappa_definitions.Fnum Gappa_definitions.Fexp].
  unfold Rdiv. rewrite <- (bpow_m 57). change (IZR 6004799585185156) with (IZR (1501199896296289 * 4)).
  rewrite mult_IZR. change (IZR 4) with (bpow radix2 2). rewrite Rmult_assoc, <- bpow_plus. reflexivity.
Qed.
Lemma d5_g_eq : B st_d5 = d5_g.
Proof.
  rewrite st_d5_val. unfold d5_g, Gappa_definitions.float2R, F2R.
  cbn [Defs.Fnum Defs.Fexp Gappa_definitions.Fnum Gappa_definitions.Fexp].
  unfold Rdiv. rewrite <- (bpow_m 59). reflexivity.
Qed.

(** [Q(v) = v²·(1/2 + v·(d3 + v·(d4 + v·d5)))], as the certificates spell it. *)
Definition Qs (v : R) : R := v * v * (half_g + v * (d3_g + v * (d4_g + v * d5_g))).

(** formal/exp/stage_mvt.g's theorem. *)
Theorem stage_mvt_bound r delta :
  Rabs r <= 0.00068 -> Rabs delta <= IZR 257 * bpow radix2 (-72) ->
  Rabs (Qs (r + delta) - Qs r) <= bpow radix2 (-74).
Proof.
  intros Hr Hd. unfold Qs, half_g, d3_g, d4_g, d5_g.
  apply Rabs_le_inv in Hr. apply Rabs_le_inv in Hd. apply Rabs_le.
  gappa_goal (exp_stage_mvt.l1 r delta).
Qed.

(** formal/exp/stage_a.g's theorem. *)
Theorem stage_a_bound (th tl R dr Dt m a : R) :
  1 <= th <= 2 -> Rabs tl <= bpow radix2 (-53) -> Rabs R <= 0.000677 ->
  Rabs dr <= bpow radix2 (-77) -> Rabs Dt <= bpow radix2 (-104) -> Rabs m <= bpow radix2 (-74) ->
  Rabs a <= IZR 5174524961095286666344419 * bpow radix2 (-158) ->
  let r := rn (R + dr) in
  let t4 := rn (d4_g + rn (r * d5_g)) in
  let t3 := rn (d3_g + rn (r * t4)) in
  let h := rn (half_g + rn (r * t3)) in
  let w := rn (rn (r * r) * h) in
  let u := rn (r + w) in
  let p := rn (th * u) in
  let fl := rn (tl + p) in
  let expR := one_g + R + (r * r * (half_g + r * (d3_g + r * (d4_g + r * d5_g))) + m) + a in
  Rabs (th + fl - (th + tl - Dt) * expR) <= IZR 302 * bpow radix2 (-69) /\
  Rabs fl <= IZR 181 * bpow radix2 (-17) /\
  Rabs r <= 1 /\ Rabs t4 <= 1 /\ Rabs t3 <= 1 /\ Rabs h <= 1 /\ Rabs w <= 1 /\ Rabs u <= 1 /\ Rabs p <= 1.
Proof.
  intros Hth Htl HR Hdr HDt Hm Ha. cbv zeta. unfold half_g, one_g, d3_g, d4_g, d5_g.
  apply Rabs_le_inv in Htl. apply Rabs_le_inv in HR. apply Rabs_le_inv in Hdr.
  apply Rabs_le_inv in HDt. apply Rabs_le_inv in Hm. apply Rabs_le_inv in Ha.
  repeat split; apply Rabs_le; gappa_goal (exp_stage_a.l1 th tl R dr Dt m a).
Qed.
(** [0.5]. *)
Definition c_half : f64 := b64_of_bits 4602678819172646912.   (* 0x3fe0000000000000 *)
Lemma c_half_g : B c_half = half_g.
Proof.
  rewrite half_g_eq. unfold c_half.
  rewrite (bits_val 4602678819172646912 false 4503599627370496 53 eq_refl). simpl. field.
Qed.
Lemma c_half_finite : finite c_half.
Proof. exact (bits_finite 4602678819172646912 _ _ _ eq_refl). Qed.

(** [Stages::a_value]: [(th, tl + th·u)],
    [u = r + r²·(1/2 + r·(d3 + r·(d4 + r·d5)))], [r = r1 − n·L2D]. *)
Definition stage_a_value (n r1 : f64) (j : nat) : f64 * f64 :=
  let r := fsub r1 (fmul n st_l2d) in
  let u := fadd r (fmul (fmul r r)
                        (fadd c_half (fmul r (fadd st_d3 (fmul r (fadd st_d4 (fmul r st_d5))))))) in
  let th := st_t_hi j in
  (th, fadd (st_t_lo j) (fmul th u)).

Lemma rnd_le1 v : Rabs v <= 1 -> Rabs (rndF v) <= 1.
Proof.
  intros H. apply abs_round_le_generic; try exact H; auto with typeclass_instances.
  change 1 with (bpow radix2 0). apply generic_format_bpow. unfold FLT_exp, emin, prec. lia.
Qed.

Lemma bpow_le1 e : (e <= 0)%Z -> bpow radix2 e <= 1.
Proof. intros H. change 1 with (bpow radix2 0). apply bpow_le. exact H. Qed.

(** The table entry's facts, as the certificates take them. *)
Lemma table_facts j : (j < 512)%nat ->
  finite (st_t_hi j) /\ finite (st_t_lo j) /\ 1 <= B (st_t_hi j) <= 2 /\
  Rabs (B (st_t_lo j)) <= bpow radix2 (-53) /\
  Rabs (B (st_t_hi j) + B (st_t_lo j) - exp (INR j * ln 2 / 512)) <= bpow radix2 (-104).
Proof.
  intros Hj. destruct (st_t_ok j Hj) as [Fh [Fl [_ [_ [_ [Th [Tl D]]]]]]].
  unfold st_t_hi, st_t_lo. repeat split; try assumption; try lra.
  change (-53)%Z with (- Z.of_nat 53)%Z. rewrite bpow_m. exact Tl.
Qed.

Theorem stage_a_value_ok x n r1 (ni : Z) (j : nat) :
  finite x -> finite n -> B n = IZR ni -> (Z.abs ni <= 520018)%Z -> finite r1 ->
  B r1 = B x - IZR ni * B st_l1 -> Rabs (B x - IZR ni * L) <= 0.000677 ->
  Rabs (B r1) < bpow radix2 (-10) -> (j < 512)%nat ->
  let '(y, l) := stage_a_value n r1 j in
  finite y /\ finite l /\ Rabs (B y) <= 4 /\ Rabs (B l) <= IZR 181 * bpow radix2 (-17) /\
  Rabs (exp (INR j * ln 2 / 512) * exp (B x - IZR ni * L) - (B y + B l)) <= IZR 302 * bpow radix2 (-69).
Proof.
  intros Fx Fn Bn Hn Fr1 Br1 HR Hr1 Hj.
  destruct (stage_a_r_ok n r1 ni (B x) Fn Bn Hn Fr1 Br1 HR Hr1) as [Fr [Br Hdr]].
  destruct (table_facts j Hj) as [Fth [Ftl [Hth [Htl Htab]]]].
  set (R := B x - IZR ni * L) in *.
  set (dr := B r1 - B (fmul n st_l2d) - R) in *.
  set (th := st_t_hi j) in *. set (tl := st_t_lo j) in *.
  set (T := exp (INR j * ln 2 / 512)) in *.
  set (r := fsub r1 (fmul n st_l2d)) in *.
  assert (Br' : B r = rn (R + dr)) by (rewrite Br; f_equal; unfold dr; ring).
  (* |r| <= 0.00068, and R − r for the mean value term *)
  assert (Er : Rabs (B r - (R + dr)) <= bpow radix2 (-64)).
  { rewrite Br'. apply (rnd_err_below _ (-10)); [lia | ].
    apply Rle_trans with (Rabs R + Rabs dr); [apply Rabs_triang | ].
    change (bpow radix2 (-10)) with (/ 1024). change (bpow radix2 (-77)) with (/ 151115727451828646838272) in Hdr. lra. }
  assert (Hr : Rabs (B r) <= 0.00068).
  { change (bpow radix2 (-64)) with (/ 18446744073709551616) in Er.
    change (bpow radix2 (-77)) with (/ 151115727451828646838272) in Hdr.
    apply Rabs_le_inv in Er. apply Rabs_le_inv in Hdr. apply Rabs_le_inv in HR. apply Rabs_le. lra. }
  (* the approximation and the mean value terms *)
  set (m := Qs R - Qs (B r)).
  assert (Hm : Rabs m <= bpow radix2 (-74)).
  { unfold m. replace R with (B r + (R - B r)) at 1 by ring. apply stage_mvt_bound; [exact Hr | ].
    change (bpow radix2 (-64)) with (/ 18446744073709551616) in Er.
    change (bpow radix2 (-77)) with (/ 151115727451828646838272) in Hdr.
    change (bpow radix2 (-72)) with (/ 4722366482869645213696).
    apply Rabs_le_inv in Er. apply Rabs_le_inv in Hdr. apply Rabs_le. lra. }
  set (a := exp R - 1 - R - Qs R).
  assert (Ha : Rabs a <= IZR 5174524961095286666344419 * bpow radix2 (-158)).
  { pose proof (st_poly_approx R HR) as A. unfold st_poly_bound, Rdiv in A.
    rewrite <- (bpow_m 158) in A. rewrite d3_g_eq, d4_g_eq, d5_g_eq in A.
    unfold a, Qs. rewrite half_g_eq. replace (/ 2) with (1 / 2) by field. exact A. }
  set (Dt := B th + B tl - T).
  assert (HDt : Rabs Dt <= bpow radix2 (-104)) by exact Htab.
  pose proof (stage_a_bound (B th) (B tl) R dr Dt m a Hth Htl HR Hdr HDt Hm Ha) as G.
  cbv zeta in G. rewrite <- Br' in G.
  destruct G as [GY [Gfl [Gr [Gt4 [Gt3 [Gh [Gw [Gu Gp]]]]]]]].
  (* the transcription computes the certificate's chain *)
  assert (C5 : Rabs d5_g <= 1) by (rewrite <- d5_g_eq, st_d5_val; interval).
  assert (C4 : Rabs d4_g <= 1) by (rewrite <- d4_g_eq, st_d4_val; interval).
  assert (C3 : Rabs d3_g <= 1) by (rewrite <- d3_g_eq, st_d3_val; interval).
  assert (Ch : Rabs half_g <= 1) by (rewrite half_g_eq; rewrite Rabs_pos_eq; lra).
  assert (M11 : forall u v, Rabs u <= 1 -> Rabs v <= 1 -> Rabs (u * v) <= 1).
  { intros u v Hu Hv. rewrite Rabs_mult. apply Rle_trans with (1 * 1); [apply Rmult_le_compat; try apply Rabs_pos; lra | lra]. }
  unfold stage_a_value. fold r th tl.
  destruct (fmul16 r st_d5 Fr st_d5_finite) as [F0 B0].
  { rewrite d5_g_eq. apply Rle_trans with 1; [apply M11; lra | lra]. }
  rewrite d5_g_eq, rndF_rn in B0.
  assert (A0 : Rabs (B (fmul r st_d5)) <= 1) by (rewrite B0; apply rnd_le1; apply M11; lra).
  destruct (fadd16 st_d4 (fmul r st_d5) st_d4_finite F0) as [F1 B1].
  { rewrite d4_g_eq. apply Rle_trans with (1 := Rabs_triang _ _). lra. }
  rewrite d4_g_eq, B0, rndF_rn in B1.
  destruct (fmul16 r (fadd st_d4 (fmul r st_d5)) Fr F1) as [F1' B1'].
  { rewrite B1. apply Rle_trans with 1; [apply M11; lra | lra]. }
  rewrite B1, rndF_rn in B1'.
  assert (A1 : Rabs (B (fmul r (fadd st_d4 (fmul r st_d5)))) <= 1) by (rewrite B1'; apply rnd_le1; apply M11; lra).
  destruct (fadd16 st_d3 _ st_d3_finite F1') as [F2 B2].
  { rewrite d3_g_eq. apply Rle_trans with (1 := Rabs_triang _ _). lra. }
  rewrite d3_g_eq, B1', rndF_rn in B2.
  destruct (fmul16 r _ Fr F2) as [F3 B3].
  { rewrite B2. apply Rle_trans with 1; [apply M11; lra | lra]. }
  rewrite B2, rndF_rn in B3.
  assert (A3 : Rabs (B (fmul r (fadd st_d3 (fmul r (fadd st_d4 (fmul r st_d5)))))) <= 1)
    by (rewrite B3; apply rnd_le1; apply M11; lra).
  destruct (fadd16 c_half _ c_half_finite F3) as [F4 B4].
  { rewrite c_half_g. apply Rle_trans with (1 := Rabs_triang _ _). lra. }
  rewrite c_half_g, B3, rndF_rn in B4.
  destruct (fmul16 r r Fr Fr) as [F5 B5].
  { apply Rle_trans with 1; [apply M11; lra | lra]. }
  rewrite rndF_rn in B5.
  assert (A5 : Rabs (B (fmul r r)) <= 1) by (rewrite B5; apply rnd_le1; apply M11; lra).
  destruct (fmul16 (fmul r r) _ F5 F4) as [F6 B6].
  { rewrite B4. apply Rle_trans with 1; [apply M11; lra | lra]. }
  rewrite B5, B4, rndF_rn in B6.
  destruct (fadd16 r _ Fr F6) as [F7 B7].
  { rewrite B6. apply Rle_trans with (1 := Rabs_triang _ _). lra. }
  rewrite B6, rndF_rn in B7.
  destruct (fmul16 th _ Fth F7) as [F8 B8].
  { rewrite B7, Rabs_mult. apply Rle_trans with (2 * 1); [apply Rmult_le_compat; try apply Rabs_pos; [rewrite Rabs_pos_eq; lra | lra] | lra]. }
  rewrite B7, rndF_rn in B8.
  destruct (fadd16 tl _ Ftl F8) as [F9 B9].
  { rewrite B8. apply Rle_trans with (1 := Rabs_triang _ _). pose proof (bpow_le1 (-53) ltac:(lia)). lra. }
  rewrite B8, rndF_rn in B9.
  split; [exact Fth | split; [exact F9 | split; [rewrite Rabs_pos_eq; lra | split]]].
  - rewrite B9. exact Gfl.
  - (* Y against T·e^R *)
    rewrite B9.
    assert (ER : one_g + R + (Qs (B r) + m) + a = exp R) by (rewrite one_g_eq; unfold m, a; ring).
    unfold Qs in ER. rewrite ER in GY.
    replace (B th + B tl - Dt) with T in GY by (unfold Dt; ring).
    rewrite Rabs_minus_sym. exact GY.
Qed.

(** [e^x = 2^k·2^(j/512)·e^R] for [x = (512k + j)·ln 2/512 + R]. *)
Lemma exp_split k j R :
  exp (IZR (512 * k + Z.of_nat j) * L + R) = exp (INR j * ln 2 / 512) * exp R * bpow radix2 k.
Proof.
  rewrite bpow_powerRZ, powerRZ_Rpower by (simpl; lra). unfold Rpower, L.
  rewrite <- !exp_plus. f_equal.
  rewrite plus_IZR, mult_IZR, INR_IZR_INZ. simpl (IZR radix2). field.
Qed.

(** exp/mod.rs's [E_A], [1.5·2^-61]. *)
Definition c_ea : f64 := b64_of_bits 4334714641344102400.   (* 0x3c28000000000000 *)
Lemma c_ea_val : B c_ea = IZR 3 * bpow radix2 (-62).
Proof.
  unfold c_ea. rewrite (bits_val 4334714641344102400 false 6755399441055744 113 eq_refl).
  unfold Rdiv. rewrite <- (bpow_m 113). change (-62)%Z with (51 + - Z.of_nat 113)%Z. rewrite bpow_plus.
  change (bpow radix2 51) with (IZR 2251799813685248). simpl cond_Zopp. rewrite <- Rmult_assoc, <- mult_IZR.
  reflexivity.
Qed.
Lemma c_ea_finite : finite c_ea.
Proof. exact (bits_finite 4334714641344102400 _ _ _ eq_refl). Qed.

(** [Stages::a]: stage A's value, tested and scaled. *)
Definition stage_a (x : f64) : option f64 :=
  let '(n, j, k, r1) := stage_of x in
  let '(y, l) := stage_a_value n r1 (Z.to_nat j) in
  decide_const y l c_ea k.

(** [2^(j/512)·e^R] lies in [[0.9, 2.1]]. *)
Lemma z_range j R : (j < 512)%nat -> Rabs R <= 0.000677 ->
  9 / 10 <= exp (INR j * ln 2 / 512) * exp R <= 21 / 10.
Proof.
  intros Hj HR. apply Rabs_le_inv in HR.
  assert (J : 0 <= INR j <= 511).
  { split; [apply pos_INR | ]. assert (H : (j <= 511)%nat) by lia. apply le_INR in H.
    rewrite (INR_IZR_INZ 511) in H. exact H. }
  generalize (INR j) J; intros v Jv.
  assert (T : 0.999 <= exp (v * ln 2 / 512) <= 2) by (split; interval).
  assert (E : 0.999 <= exp R <= 1.001) by (split; interval).
  split; nra.
Qed.

(** Stage A end to end: for every finite [|x| < 704], when the test passes,
    the returned value is [RN(e^x)]. *)
Theorem exp_stage_a_ok x v : finite x -> Rabs (B x) < 704 -> stage_a x = Some v ->
  finite v /\ B v = rndF (exp (B x)).
Proof.
  intros Fx Hx. pose proof (stage_of_ok x Fx Hx) as SO. unfold stage_a.
  (* Generalizing, rather than destructing, keeps the kernel from unfolding
     the transcription when it rechecks the proof. *)
  revert SO. generalize (stage_of x). intros [[[n j] k] r1] SO Hd.
  destruct SO as [ni [Bn [Fn [Hn [Hjk [Hj [Hk [Fr1 [Br1 [HR [Hr1 _]]]]]]]]]]].
  assert (Jn : (Z.to_nat j < 512)%nat) by lia.
  pose proof (stage_a_value_ok x n r1 ni (Z.to_nat j) Fx Fn Bn Hn Fr1 Br1 HR Hr1 Jn) as SV.
  revert SV Hd. generalize (stage_a_value n r1 (Z.to_nat j)). intros [y l] SV Hd.
  destruct SV as [Fy [Fl [Hy [Hl HZ]]]].
  set (R := B x - IZR ni * L) in *.
  set (Zr := exp (INR (Z.to_nat j) * ln 2 / 512) * exp R) in *.
  assert (Ex : exp (B x) = Zr * bpow radix2 k).
  { unfold Zr. rewrite <- exp_split. f_equal. rewrite Z2Nat.id by lia. unfold R. rewrite Hjk. ring. }
  rewrite Ex.
  pose proof c_ea_val as Ev.
  apply (decide_const_ok y l c_ea k Zr (IZR 302 * bpow radix2 (-69)) (-9) v Fy Fl c_ea_finite Hy
           ltac:(lia)); try assumption; try lia.
  - rewrite Ev. pose proof (bpow_ge_0 radix2 (-62)). lra.
  - rewrite Ev. bpow_num_all. lra.
  - rewrite Ev. change (-9 - 54)%Z with (-63)%Z. bpow_num_all. lra.
  - apply z_range; assumption.
Qed.
