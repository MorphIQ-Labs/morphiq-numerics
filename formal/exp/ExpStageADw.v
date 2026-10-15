(** exp/mod.rs's [stage_a_double_word] (docs/exp.md, section 5a): stage A
    at a double-word argument [s + se], transcribed on binary64 and proved:
    - [stage_a_at_chain]: [Stages::a_value]'s operation chain, for any
      binary64 [r] with [|r| <= 2^-10], computes the certificates' rounded
      expressions;
    - [stage_a_dw_value_ok]: for every finite [|s| < 704] and
      [|se| <= 2^-42], [y + l] is within [23·2^-65 = 0x1.7p-61] of
      [T_j·e^R], [R = s + se - (512k + j)·L], [|R| <= 0.000677], and
      [|l| <= 181·2^-17]: formal/exp/stage_a_dw.g's theorem, with its
      hypotheses proved here (the reduction of ExpStageReduction.v,
      formal/exp/stage_mvt_dw.g, the approximation and table bounds of
      ExpStageTables.v). *)

From Coq Require Import ZArith Reals Lia Lra Psatz Classical.
From Flocq Require Import Core.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Mul Grid RoundingConstant.
From Gappa Require Gappa_definitions Gappa_round_def.
From Interval Require Import Tactic.
Require ExpStageTables StageGappa ExpStageReduction ExpStageA.
Require exp_stage_a_dw exp_stage_mvt_dw.
Import ExpStageTables StageGappa ExpStageReduction ExpStageA.

Open Scope R_scope.

(** formal/exp/stage_mvt_dw.g's theorem. *)
Theorem stage_mvt_dw_bound r delta :
  Rabs r <= 0.00068 -> Rabs delta <= IZR 257 * bpow radix2 (-71) ->
  Rabs (Qs (r + delta) - Qs r) <= bpow radix2 (-73).
Proof.
  intros Hr Hd. unfold Qs, half_g, d3_g, d4_g, d5_g.
  apply Rabs_le_inv in Hr. apply Rabs_le_inv in Hd. apply Rabs_le.
  gappa_goal (exp_stage_mvt_dw.l1 r delta).
Qed.

(** formal/exp/stage_a_dw.g's theorem. *)
Theorem stage_a_dw_bound (th tl R0 dr se Dt m a : R) :
  1 <= th <= 2 -> Rabs tl <= bpow radix2 (-53) -> Rabs R0 <= 0.000677 ->
  Rabs dr <= bpow radix2 (-77) -> Rabs se <= bpow radix2 (-42) ->
  Rabs Dt <= bpow radix2 (-104) -> Rabs m <= bpow radix2 (-73) ->
  Rabs a <= IZR 5174524961095286666344419 * bpow radix2 (-158) ->
  let r := rn (rn (R0 + dr) + se) in
  let fl := rn (tl + rn (th * rn (r + rn (rn (r * r) *
              rn (half_g + rn (r * rn (d3_g + rn (r * rn (d4_g + rn (r * d5_g)))))))))) in
  let expR := one_g + (R0 + se) + (r * r * (half_g + r * (d3_g + r * (d4_g + r * d5_g))) + m) + a in
  Rabs (th + fl - (th + tl - Dt) * expR) <= IZR 23 * bpow radix2 (-65) /\
  Rabs fl <= IZR 181 * bpow radix2 (-17).
Proof.
  intros Hth Htl HR Hdr Hse HDt Hm Ha. cbv zeta. unfold half_g, one_g, d3_g, d4_g, d5_g.
  apply Rabs_le_inv in Htl. apply Rabs_le_inv in HR. apply Rabs_le_inv in Hdr.
  apply Rabs_le_inv in Hse. apply Rabs_le_inv in HDt. apply Rabs_le_inv in Hm. apply Rabs_le_inv in Ha.
  split; apply Rabs_le; gappa_goal (exp_stage_a_dw.l1 th tl R0 dr se Dt m a).
Qed.

Lemma rnd_le_small v e : (-1000 <= e)%Z -> Rabs v <= bpow radix2 e -> Rabs (rn v) <= bpow radix2 e.
Proof.
  intros He H. rewrite <- rndF_rn. apply abs_round_le_generic; try exact H; auto with typeclass_instances.
  apply generic_format_bpow. unfold FLT_exp, emin, prec. lia.
Qed.

(** [Stages::a_value]'s chain at any binary64 [|r| <= 2^-10]: each
    operation is finite and rounds as the certificates model it. *)
Lemma stage_a_at_chain r j : finite r -> Rabs (B r) <= bpow radix2 (-10) -> (j < 512)%nat ->
  let '(y, l) := stage_a_at r j in
  finite y /\ finite l /\ B y = B (st_t_hi j) /\
  B l = rn (B (st_t_lo j) + rn (B (st_t_hi j) * rn (B r + rn (rn (B r * B r) *
          rn (half_g + rn (B r * rn (d3_g + rn (B r * rn (d4_g + rn (B r * d5_g)))))))))).
Proof.
  intros Fr Hr Hj.
  destruct (table_facts j Hj) as [Fth [Ftl [Hth [Htl _]]]].
  set (th := st_t_hi j) in *. set (tl := st_t_lo j) in *.
  assert (R1 : Rabs (B r) <= 1) by (pose proof (bpow_le1 (-10) ltac:(lia)); lra).
  assert (Rs : Rabs (B r) <= / 1024) by (change (bpow radix2 (-10)) with (/ 1024) in Hr; exact Hr).
  assert (C5 : Rabs d5_g <= 1) by (rewrite <- d5_g_eq, st_d5_val; interval with (i_prec 64)).
  assert (C4 : Rabs d4_g <= 1) by (rewrite <- d4_g_eq, st_d4_val; interval with (i_prec 64)).
  assert (C3 : Rabs d3_g <= 1) by (rewrite <- d3_g_eq, st_d3_val; interval with (i_prec 64)).
  assert (Ch : Rabs half_g <= / 2) by (rewrite half_g_eq; rewrite Rabs_pos_eq; lra).
  assert (C4h : Rabs d4_g <= / 2) by (rewrite <- d4_g_eq, st_d4_val; interval with (i_prec 64)).
  assert (C3h : Rabs d3_g <= / 2) by (rewrite <- d3_g_eq, st_d3_val; interval with (i_prec 64)).
  assert (M11 : forall u v, Rabs u <= 1 -> Rabs v <= 1 -> Rabs (u * v) <= 1).
  { intros u v Hu Hv. rewrite Rabs_mult. apply Rle_trans with (1 * 1); [apply Rmult_le_compat; try apply Rabs_pos; lra | lra]. }
  assert (Ms : forall v, Rabs v <= 1 -> Rabs (B r * v) <= / 1024).
  { intros v Hv. rewrite Rabs_mult. apply Rle_trans with (/ 1024 * 1); [apply Rmult_le_compat; try apply Rabs_pos; lra | lra]. }
  assert (Rn1 : forall v, Rabs v <= 1 -> Rabs (rn v) <= 1).
  { intros v Hv. rewrite <- rndF_rn. apply rnd_le1. exact Hv. }
  assert (Rns : forall v, Rabs v <= / 1024 -> Rabs (rn v) <= / 1024).
  { intros v Hv. change (/ 1024) with (bpow radix2 (-10)) in *. apply rnd_le_small; [lia | exact Hv]. }
  unfold stage_a_at. fold th tl.
  destruct (fmul16 r st_d5 Fr st_d5_finite) as [F0 B0].
  { rewrite d5_g_eq. apply Rle_trans with 1; [apply M11; lra | lra]. }
  rewrite d5_g_eq, rndF_rn in B0.
  assert (A0 : Rabs (B (fmul r st_d5)) <= / 1024) by (rewrite B0; apply Rns, Ms; lra).
  destruct (fadd16 st_d4 (fmul r st_d5) st_d4_finite F0) as [F1 B1].
  { rewrite d4_g_eq. apply Rle_trans with (1 := Rabs_triang _ _). lra. }
  rewrite d4_g_eq, B0, rndF_rn in B1.
  assert (A1 : Rabs (B (fadd st_d4 (fmul r st_d5))) <= 1).
  { rewrite B1. apply Rn1. rewrite <- B0. apply Rle_trans with (1 := Rabs_triang _ _).
    lra. }
  destruct (fmul16 r (fadd st_d4 (fmul r st_d5)) Fr F1) as [F2 B2].
  { apply Rle_trans with 1; [apply M11; lra | lra]. }
  rewrite B1, rndF_rn in B2.
  assert (A2 : Rabs (B (fmul r (fadd st_d4 (fmul r st_d5)))) <= / 1024)
    by (rewrite B2; apply Rns, Ms; rewrite <- B1; exact A1).
  destruct (fadd16 st_d3 _ st_d3_finite F2) as [F3 B3].
  { rewrite d3_g_eq. apply Rle_trans with (1 := Rabs_triang _ _). lra. }
  rewrite d3_g_eq, B2, rndF_rn in B3.
  assert (A3 : Rabs (B (fadd st_d3 (fmul r (fadd st_d4 (fmul r st_d5))))) <= 1).
  { rewrite B3. apply Rn1. rewrite <- B2. apply Rle_trans with (1 := Rabs_triang _ _).
    lra. }
  destruct (fmul16 r _ Fr F3) as [F4 B4].
  { apply Rle_trans with 1; [apply M11; lra | lra]. }
  rewrite B3, rndF_rn in B4.
  assert (A4 : Rabs (B (fmul r (fadd st_d3 (fmul r (fadd st_d4 (fmul r st_d5)))))) <= / 1024)
    by (rewrite B4; apply Rns, Ms; rewrite <- B3; exact A3).
  destruct (fadd16 c_half _ c_half_finite F4) as [F5 B5].
  { rewrite c_half_g. apply Rle_trans with (1 := Rabs_triang _ _). lra. }
  rewrite c_half_g, B4, rndF_rn in B5.
  assert (A5 : Rabs (B (fadd c_half (fmul r (fadd st_d3 (fmul r (fadd st_d4 (fmul r st_d5))))))) <= 1).
  { rewrite B5. apply Rn1. rewrite <- B4. apply Rle_trans with (1 := Rabs_triang _ _). lra. }
  destruct (fmul16 r r Fr Fr) as [F6 B6].
  { apply Rle_trans with 1; [apply M11; lra | lra]. }
  rewrite rndF_rn in B6.
  assert (A6 : Rabs (B (fmul r r)) <= / 1024) by (rewrite B6; apply Rns, Ms; lra).
  destruct (fmul16 (fmul r r) _ F6 F5) as [F7 B7].
  { apply Rle_trans with 1; [apply M11; lra | lra]. }
  rewrite B6, B5, rndF_rn in B7.
  match type of B7 with B ?t = _ => assert (A7 : Rabs (B t) <= / 1024) end.
  { rewrite B7. apply Rns. rewrite <- B6, <- B5. rewrite Rabs_mult.
    apply Rle_trans with (/ 1024 * 1); [apply Rmult_le_compat; try apply Rabs_pos; lra | lra]. }
  destruct (fadd16 r _ Fr F7) as [F8 B8].
  { apply Rle_trans with (1 := Rabs_triang _ _). lra. }
  rewrite B7, rndF_rn in B8.
  match type of B8 with B ?t = _ => assert (A8 : Rabs (B t) <= 1) end.
  { rewrite B8. apply Rn1. rewrite <- B7. apply Rle_trans with (1 := Rabs_triang _ _). lra. }
  destruct (fmul16 th _ Fth F8) as [F9 B9].
  { rewrite Rabs_mult. apply Rle_trans with (2 * 1); [apply Rmult_le_compat; try apply Rabs_pos; [rewrite Rabs_pos_eq; lra | lra] | lra]. }
  rewrite B8, rndF_rn in B9.
  destruct (fadd16 tl _ Ftl F9) as [F10 B10].
  { apply Rle_trans with (1 := Rabs_triang _ _). pose proof (bpow_le1 (-53) ltac:(lia)).
    match type of B9 with B ?t = _ => assert (Rabs (B t) <= 2) end.
    { rewrite B9, <- B8, <- rndF_rn. apply abs_round_le_generic; auto with typeclass_instances.
      - change 2 with (bpow radix2 1). apply generic_format_bpow. unfold FLT_exp, emin, prec. lia.
      - rewrite Rabs_mult. apply Rle_trans with (2 * 1); [apply Rmult_le_compat; try apply Rabs_pos; [rewrite Rabs_pos_eq; lra | lra] | lra]. }
    lra. }
  rewrite B9, rndF_rn in B10.
  repeat split; try assumption.
Qed.

(** [stage_a_double_word]: [Stages::of(s)], stage A's reduced argument plus
    the low word, and [Stages::a_value]'s chain. *)
Definition stage_a_dw_value (s se : f64) : f64 * f64 * Z :=
  let '(n, j, k, r1) := stage_of s in
  let '(y, l) := stage_a_at (fadd (fsub r1 (fmul n st_l2d)) se) (Z.to_nat j) in
  (y, l, k).

(** [2^(j/512)·e^R] lies in [[0.9, 2.1]] slightly beyond stage A's [|R|]. *)
Lemma z_range_dw j R : (j < 512)%nat -> Rabs R <= 0.000678 ->
  9 / 10 <= exp (INR j * ln 2 / 512) * exp R <= 21 / 10.
Proof.
  intros Hj HR. apply Rabs_le_inv in HR.
  assert (J : 0 <= INR j <= 511).
  { split; [apply pos_INR | ]. assert (H : (j <= 511)%nat) by lia. apply le_INR in H.
    rewrite (INR_IZR_INZ 511) in H. exact H. }
  generalize (INR j) J; intros v Jv.
  assert (T : 0.999 <= exp (v * ln 2 / 512) <= 2) by (split; interval with (i_prec 64)).
  assert (E : 0.999 <= exp R <= 1.001) by (split; interval with (i_prec 64)).
  split; nra.
Qed.

Theorem stage_a_dw_value_ok s se : finite s -> Rabs (B s) < 704 -> finite se ->
  Rabs (B se) <= bpow radix2 (-42) ->
  let '(y, l, k) := stage_a_dw_value s se in
  exists (ni : Z) (j : nat), ni = (512 * k + Z.of_nat j)%Z /\ (j < 512)%nat /\
    (-1016 <= k <= 1016)%Z /\ finite y /\ finite l /\ Rabs (B y) <= 4 /\
    Rabs (B l) <= IZR 181 * bpow radix2 (-17) /\
    Rabs (B s + B se - IZR ni * L) <= 0.000677 /\
    Rabs (exp (INR j * ln 2 / 512) * exp (B s + B se - IZR ni * L) - (B y + B l))
      <= IZR 23 * bpow radix2 (-65).
Proof.
  intros Fs Hs Fse Hse.
  pose proof (stage_of_ok s Fs Hs) as SO. pose proof (stage_of_extended_ok s Fs ltac:(lra)) as SE.
  unfold stage_a_dw_value.
  revert SO SE. generalize (stage_of s). intros [[[n j] k] r1] SO SE.
  destruct SO as [ni [Bn [Fn [Hn [Hjk [Hj [Hk [Fr1 [Br1 [HR [Hr1 _]]]]]]]]]]].
  destruct SE as [ni' [Bn' [_ [_ [_ [_ [_ [_ [_ [HR' _]]]]]]]]]].
  assert (Ni : ni' = ni) by (apply eq_IZR; rewrite <- Bn, <- Bn'; reflexivity). subst ni'.
  assert (Jn : (Z.to_nat j < 512)%nat) by lia.
  destruct (stage_a_r_ok n r1 ni (B s) Fn Bn Hn Fr1 Br1 HR Hr1) as [Fr0 [Br0 Hdr]].
  set (r0 := fsub r1 (fmul n st_l2d)) in *.
  set (R0 := B s - IZR ni * L) in *.
  set (dr := B r1 - B (fmul n st_l2d) - R0) in *.
  assert (Br0' : B r0 = rn (R0 + dr)) by (rewrite Br0; f_equal; unfold dr; ring).
  assert (HR0 : Rabs R0 <= 0.000676902) by exact HR'.
  assert (Hse' : Rabs (B se) <= / 4398046511104) by (change (bpow radix2 (-42)) with (/ 4398046511104) in Hse; exact Hse).
  assert (Hdr' : Rabs dr <= / 151115727451828646838272) by (change (bpow radix2 (-77)) with (/ 151115727451828646838272) in Hdr; exact Hdr).
  (* |r0| and the low word's rounding *)
  assert (Ar0 : Rabs (B r0) <= 0.000677).
  { rewrite Br0'. rewrite <- rndF_rn. apply Rle_trans with (Rabs (R0 + dr) + bpow radix2 (-64)).
    - pose proof (rnd_err_below (R0 + dr) (-10) ltac:(lia)) as E.
      assert (V : Rabs (R0 + dr) <= bpow radix2 (-10)).
      { apply Rle_trans with (1 := Rabs_triang _ _). change (bpow radix2 (-10)) with (/ 1024). lra. }
      specialize (E V). change (-10 - 54)%Z with (-64)%Z in E.
      pose proof (Rabs_triang_inv (rndF (R0 + dr)) (R0 + dr)). lra.
    - pose proof (Rabs_triang R0 dr). change (bpow radix2 (-64)) with (/ 18446744073709551616). lra. }
  destruct (fadd16 r0 se Fr0 Fse) as [Fr Br].
  { apply Rle_trans with (1 := Rabs_triang _ _). lra. }
  set (r := fadd r0 se) in *. rewrite rndF_rn in Br.
  assert (Er : Rabs (B r - (B r0 + B se)) <= bpow radix2 (-64)).
  { rewrite Br, <- rndF_rn. apply (rnd_err_below _ (-10)); [lia | ].
    apply Rle_trans with (1 := Rabs_triang _ _). change (bpow radix2 (-10)) with (/ 1024). lra. }
  assert (Er0 : Rabs (B r0 - (R0 + dr)) <= bpow radix2 (-64)).
  { rewrite Br0', <- rndF_rn. apply (rnd_err_below _ (-10)); [lia | ].
    apply Rle_trans with (1 := Rabs_triang _ _). change (bpow radix2 (-10)) with (/ 1024). lra. }
  assert (Hr : Rabs (B r) <= 0.00068).
  { change (bpow radix2 (-64)) with (/ 18446744073709551616) in Er.
    apply Rabs_le_inv in Er. apply Rabs_le_inv in Ar0. apply Rabs_le_inv in Hse'. apply Rabs_le. lra. }
  pose proof (stage_a_at_chain r (Z.to_nat j) Fr ltac:(change (bpow radix2 (-10)) with (/ 1024); lra) Jn) as Chain.
  destruct (table_facts (Z.to_nat j) Jn) as [Fth [Ftl [Hth [Htl Htab]]]].
  revert Chain. generalize (stage_a_at r (Z.to_nat j)). intros [y l] Chain.
  destruct Chain as [Fy [Fl [By Bl]]].
  set (th := st_t_hi (Z.to_nat j)) in *. set (tl := st_t_lo (Z.to_nat j)) in *.
  set (T := exp (INR (Z.to_nat j) * ln 2 / 512)) in *.
  set (R := R0 + B se).
  (* the mean value term at r against R *)
  assert (Delta : Rabs (R - B r) <= IZR 257 * bpow radix2 (-71)).
  { unfold R. change (bpow radix2 (-64)) with (/ 18446744073709551616) in Er, Er0.
    change (bpow radix2 (-71)) with (/ 2361183241434822606848).
    apply Rabs_le_inv in Er. apply Rabs_le_inv in Er0. apply Rabs_le_inv in Hdr'. apply Rabs_le. lra. }
  set (m := Qs R - Qs (B r)).
  assert (Hm : Rabs m <= bpow radix2 (-73)).
  { unfold m. replace R with (B r + (R - B r)) at 1 by ring. apply stage_mvt_dw_bound; assumption. }
  assert (HRw : Rabs R <= 0.000677).
  { unfold R. apply Rabs_le_inv in HR0. apply Rabs_le_inv in Hse'. apply Rabs_le. lra. }
  set (a := exp R - 1 - R - Qs R).
  assert (Ha : Rabs a <= IZR 5174524961095286666344419 * bpow radix2 (-158)).
  { pose proof (st_poly_approx R HRw) as A. unfold st_poly_bound, Rdiv in A.
    rewrite <- (bpow_m 158) in A. rewrite d3_g_eq, d4_g_eq, d5_g_eq in A.
    unfold a, Qs. rewrite half_g_eq. replace (/ 2) with (1 / 2) by field. exact A. }
  set (Dt := B th + B tl - T).
  pose proof (stage_a_dw_bound (B th) (B tl) R0 dr (B se) Dt m a Hth Htl
    ltac:(apply Rabs_le_inv in HR0; apply Rabs_le; lra) Hdr Hse Htab Hm Ha) as G.
  cbv zeta in G. rewrite <- Br0', <- Br in G.
  destruct G as [GY Gfl].
  exists ni, (Z.to_nat j). rewrite Z2Nat.id by lia.
  repeat split; try assumption; try lia.
  - rewrite By. rewrite Rabs_pos_eq; lra.
  - rewrite Bl. exact Gfl.
  - replace (B s + B se - IZR ni * L) with R by (unfold R, R0; ring). exact HRw.
  - replace (B s + B se - IZR ni * L) with R by (unfold R, R0; ring).
    rewrite By, Bl.
    assert (ER : one_g + (R0 + B se) + (Qs (B r) + m) + a = exp R) by (rewrite one_g_eq; unfold m, a, R; ring).
    unfold Qs in ER. rewrite ER in GY.
    replace (B th + B tl - Dt) with T in GY by (unfold Dt; ring).
    rewrite Rabs_minus_sym. exact GY.
Qed.
