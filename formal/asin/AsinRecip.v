(** [Q256::recip] ([AsinKernel.q_recip]): a binary64 start and three Newton
    steps, each squaring the relative error up to the [Q256] rounding, so
    [|c * recip c - 1| <= 2^-252] for [2^-28 <= c <= 1.0001]. *)
From Coq Require Import Reals ZArith Lia Lra Psatz List.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 RoundingCore.
From Interval Require Import Tactic.
From Q Require Import Q256 Q256Real QSpec.
Require Import Ln1pLemmas AsinTables AsinKernel AsinSqrtStep AsinNormal AsinQSeries ErfcxAccurateInputs.
Open Scope R_scope.

(** The algebra of one Newton step with its four roundings. *)
Lemma recip_alg cv yv e d1 g1 d2 g2 U E :
  cv * yv = 1 + e -> Rabs e <= E -> E <= / 1000000 -> 0 < U <= / 1000000 ->
  Rabs d1 <= U / 2 -> Rabs g1 <= 1.001 * U -> Rabs d2 <= U / 2 -> Rabs g2 <= U * yv -> 0 < cv -> 0 < yv ->
  Rabs (cv * (yv + yv * ((1 - (1 + e) * (1 + d1)) + g1) * (1 + d2) + g2) - 1) <= E * E + 3 * U /\
  0 < yv + yv * ((1 - (1 + e) * (1 + d1)) + g1) * (1 + d2) + g2.
Proof.
  intros Hcy He HE [U0 U1] D1 G1 D2 G2 Hc Hy.
  set (rho := - d1 * (1 + e) + g1).
  set (qv := (1 - (1 + e) * (1 + d1)) + g1).
  assert (Hq : qv = - e + rho) by (unfold qv, rho; ring).
  assert (Hrho : Rabs rho <= 1.52 * U).
  { unfold rho. apply Rle_trans with (Rabs (- d1 * (1 + e)) + Rabs g1); [apply Rabs_triang | ].
    rewrite Rabs_mult, Rabs_Ropp. apply Rabs_le_inv in He.
    assert (Rabs (1 + e) <= 1.0001) by (apply Rabs_le; split; nra).
    pose proof (Rabs_pos d1). pose proof (Rabs_pos (1 + e)).
    assert (Rabs d1 * Rabs (1 + e) <= U / 2 * 1.0001) by (apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | exact D1 | lra]).
    lra. }
  set (y' := yv + yv * qv * (1 + d2) + g2).
  assert (Hqs : Rabs qv <= 0.001).
  { rewrite Hq. apply Rabs_le_inv in He. apply Rabs_le_inv in Hrho. apply Rabs_le; split; nra. }
  assert (Hkey : cv * y' - 1 = - (e * e) + (1 + e) * rho + (1 + e) * (- e + rho) * d2 + cv * g2).
  { unfold y'. replace (cv * (yv + yv * qv * (1 + d2) + g2)) with ((cv * yv) * (1 + qv * (1 + d2)) + cv * g2) by ring.
    rewrite Hcy, Hq. ring. }
  split.
  - change (Rabs (cv * y' - 1) <= E * E + 3 * U). rewrite Hkey.
    pose proof He as Hec. pose proof Hrho as Hrho0. apply Rabs_le_inv in Hec as [He1 He2]. apply Rabs_le_inv in Hrho as [Hr1 Hr2].
    pose proof D2 as D2c. apply Rabs_le_inv in D2 as [Hd1 Hd2]. apply Rabs_le_inv in G2 as [Hg1 Hg2].
    assert (Hee : e * e <= E * E) by nra.
    assert (Hcg : Rabs (cv * g2) <= 1.0001 * U).
    { rewrite Rabs_mult, (Rabs_pos_eq cv) by lra. 
      apply Rle_trans with (cv * (U * yv)); [apply Rmult_le_compat_l; [lra | ] | ].
      - apply Rabs_le. split; lra.
      - assert (cv * yv <= 1.0001) by nra. nra. }
    apply Rabs_le_inv in Hcg as [Hc1 Hc2].
    assert (HT2 : Rabs ((1 + e) * rho) <= 1.53 * U).
    { rewrite Rabs_mult. assert (Rabs (1 + e) <= 1.0001) by (apply Rabs_le; split; nra).
      pose proof (Rabs_pos rho). pose proof (Rabs_pos (1 + e)).
      apply Rle_trans with (1.0001 * (1.52 * U)); [apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | lra | exact Hrho0] | lra]. }
    assert (HT3 : Rabs ((1 + e) * (- e + rho) * d2) <= 0.001 * U).
    { rewrite !Rabs_mult. assert (Rabs (1 + e) <= 1.0001) by (apply Rabs_le; split; nra).
      assert (Rabs (- e + rho) <= 0.0001) by (apply Rabs_le; split; nra).
      pose proof (Rabs_pos rho). pose proof (Rabs_pos (1 + e)). pose proof (Rabs_pos (- e + rho)). pose proof (Rabs_pos d2).
      assert (Hp1 : Rabs (1 + e) * Rabs (- e + rho) <= 1.0001 * 0.0001) by (apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | lra | lra]).
      assert (Rabs (1 + e) * Rabs (- e + rho) * Rabs d2 <= 1.0001 * 0.0001 * (U / 2)) by (apply Rmult_le_compat; [apply Rmult_le_pos; apply Rabs_pos | apply Rabs_pos | exact Hp1 | exact D2c]).
      lra. }
    apply Rabs_le_inv in HT2 as [Ht21 Ht22]. apply Rabs_le_inv in HT3 as [Ht31 Ht32].
    apply Rabs_le. split; nra.
  - change (0 < y'). unfold y'.
    apply Rabs_le_inv in Hqs as [Hq1 Hq2]. apply Rabs_le_inv in D2 as [Hd1 Hd2]. apply Rabs_le_inv in G2 as [Hg1 Hg2].
    assert (Hf : 0.998 <= 1 + qv * (1 + d2)) by nra.
    replace (yv + yv * qv * (1 + d2) + g2) with (yv * (1 + qv * (1 + d2)) + g2) by ring.
    nra.
Qed.

Definition recip_step (c y : q256) : q256 :=
  Q256.add y (Q256.mul y (q_sub q_one (Q256.mul c y))).

Lemma q_recip_steps c : q_recip c =
  recip_step c (recip_step c (recip_step c (qf (fdiv asin_one (Q256.to_f64 c))))).
Proof. reflexivity. Qed.

Lemma recip_step_ok c y E : Q256Real.valid c -> Q256Real.valid y -> 0 < qval c -> 0 < qval y ->
  Rabs (qval c * qval y - 1) <= E -> E <= / 1000000 ->
  Q256Real.valid (recip_step c y) /\ 0 < qval (recip_step c y) /\
  Rabs (qval c * qval (recip_step c y) - 1) <= E * E + 3 * bpow radix2 (-254).
Proof.
  intros Vc Vy Hc Hy HE HEs. unfold recip_step.
  destruct q_one_valid as [Vone Qone].
  destruct (mul_relative c y Vc Vy) as [V1 [d1 [D1 E1]]].
  destruct (neg_any (Q256.mul c y) V1) as [V2 E2].
  destruct (add_any q_one (neg_q (Q256.mul c y)) Vone V2) as [V3 E3].
  destruct (mul_relative y (q_sub q_one (Q256.mul c y)) Vy V3) as [V4 [d2 [D2 E4]]].
  destruct (add_any y (Q256.mul y (q_sub q_one (Q256.mul c y))) Vy V4) as [V5 E5].
  destruct bpow_254 as [B252 [B255 [Upos Usmall]]]. set (U := bpow radix2 (-254)) in *.
  rewrite B255 in D1, D2.
  set (cv := qval c) in *. set (yv := qval y) in *.
  set (e := cv * yv - 1).
  assert (Hcy : cv * yv = 1 + e) by (unfold e; ring).
  assert (HUs : 0 < U <= / 1000000) by (split; [exact Upos | apply Rle_trans with (1 := Usmall); apply Rinv_le_contravar; lra]).
  set (p1 := qval (Q256.mul c y)) in *.
  assert (Hp1 : p1 = (1 + e) * (1 + d1)) by (rewrite E1; rewrite Hcy; ring).
  set (qq := qval (q_sub q_one (Q256.mul c y))) in *.
  set (g1 := qq - (1 - p1)).
  rewrite E2, Qone in E3.
  assert (Hp1b : Rabs p1 <= 1.001).
  { rewrite Hp1. apply Rabs_le_inv in HE. apply Rabs_le_inv in D1. apply Rabs_le. split; nra. }
  assert (Hg1 : Rabs g1 <= 1.001 * U).
  { unfold g1. replace (qq - (1 - p1)) with (qq - (1 + - p1)) by ring.
    apply Rle_trans with (1 := E3).
    assert (Rmax (Rabs 1) (Rabs (- p1)) <= 1.001).
    { apply Rmax_lub; [rewrite Rabs_pos_eq by lra; lra | rewrite Rabs_Ropp; exact Hp1b]. }
    nra. }
  set (p2 := qval (Q256.mul y (q_sub q_one (Q256.mul c y)))) in *.
  set (g2 := qval (Q256.add y (Q256.mul y (q_sub q_one (Q256.mul c y)))) - (yv + p2)).
  assert (Hp2 : p2 = yv * ((1 - (1 + e) * (1 + d1)) + g1) * (1 + d2)).
  { rewrite E4. replace qq with ((1 - (1 + e) * (1 + d1)) + g1) by (unfold g1; rewrite Hp1; ring). reflexivity. }
  assert (Hqs : Rabs ((1 - (1 + e) * (1 + d1)) + g1) <= 0.001).
  { apply Rabs_le_inv in HE. apply Rabs_le_inv in D1. apply Rabs_le_inv in Hg1. apply Rabs_le. split; nra. }
  assert (Hp2y : Rabs p2 <= yv).
  { rewrite Hp2. rewrite !Rabs_mult. rewrite (Rabs_pos_eq yv) by lra.
    assert (Rabs (1 + d2) <= 1.0001) by (apply Rabs_le_inv in D2; apply Rabs_le; split; nra).
    pose proof (Rabs_pos (1 + d2)). pose proof (Rabs_pos ((1 - (1 + e) * (1 + d1)) + g1)).
    assert (Rabs ((1 - (1 + e) * (1 + d1)) + g1) * Rabs (1 + d2) <= 0.001 * 1.0001) by (apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | exact Hqs | lra]).
    nra. }
  assert (Hg2 : Rabs g2 <= U * yv).
  { unfold g2. apply Rle_trans with (1 := E5).
    assert (Rmax (Rabs yv) (Rabs p2) <= yv) by (apply Rmax_lub; [rewrite Rabs_pos_eq by lra; lra | exact Hp2y]).
    nra. }
  destruct (recip_alg cv yv e d1 g1 d2 g2 U E Hcy HE HEs HUs D1 Hg1 D2 Hg2 Hc Hy) as [Ha Hb].
  rewrite <- Hp2 in Ha, Hb.
  assert (Hy' : qval (Q256.add y (Q256.mul y (q_sub q_one (Q256.mul c y)))) = yv + p2 + g2) by (unfold g2; ring).
  refine (conj V5 (conj _ _)).
  - rewrite Hy'. exact Hb.
  - rewrite Hy'. exact Ha.
Qed.

Lemma chain_step a b : 0 < a -> a * a + 3 * bpow radix2 (-254) <= b -> forall E, 0 <= E <= a -> E * E + 3 * bpow radix2 (-254) <= b.
Proof. intros Ha Hb E [E0 E1]. nra. Qed.

Lemma chain1 : forall E, 0 <= E <= bpow radix2 (-51) -> E * E + 3 * bpow radix2 (-254) <= bpow radix2 (-101).
Proof. apply chain_step; [apply bpow_gt_0 | bpow_num; interval with (i_prec 300)]. Qed.

Lemma chain2 : forall E, 0 <= E <= bpow radix2 (-101) -> E * E + 3 * bpow radix2 (-254) <= bpow radix2 (-201).
Proof. apply chain_step; [apply bpow_gt_0 | bpow_num; interval with (i_prec 300)]. Qed.

Lemma chain3 : forall E, 0 <= E <= bpow radix2 (-201) -> E * E + 3 * bpow radix2 (-254) <= bpow radix2 (-252).
Proof. apply chain_step; [apply bpow_gt_0 | bpow_num; interval with (i_prec 300)]. Qed.

Lemma fmt_two : fmtF 2.
Proof. change 2 with (bpow radix2 1). apply fmt_bpow. lia. Qed.

Lemma rndF_le_two v : v <= 2 -> rndF v <= 2.
Proof.
  intros H. apply Rle_trans with (rndF 2).
  - apply round_le; [exact _ | exact _ | exact H].
  - rewrite round_generic by (try exact _; exact fmt_two). lra.
Qed.

Lemma rndF_ge_bpow e v : (-1074 <= e)%Z -> bpow radix2 e <= v -> bpow radix2 e <= rndF v.
Proof. intros He H. apply round_ge_generic; [exact _ | exact _ | apply fmt_bpow; exact He | exact H]. Qed.

(** The binary64 start of the reciprocal. *)
Lemma recip_start c : Q256Real.valid c -> bpow radix2 (-28) <= qval c <= 1.0001 ->
  Q256Real.valid (qf (fdiv asin_one (Q256.to_f64 c))) /\ 0 < qval (qf (fdiv asin_one (Q256.to_f64 c))) /\ Rabs (qval c * qval (qf (fdiv asin_one (Q256.to_f64 c))) - 1) <= bpow radix2 (-51).
Proof.
  intros Vc [Hlo Hhi]. set (cv := qval c) in *.
  assert (Hc28 : 0 < bpow radix2 (-28)) by apply bpow_gt_0.
  assert (Hr : Rabs (rndF cv) < bpow radix2 1024).
  { assert (Hge : bpow radix2 (-28) <= rndF cv) by (apply rndF_ge_bpow; [lia | exact Hlo]).
    assert (Hle : rndF cv <= 2) by (apply rndF_le_two; lra).
    rewrite Rabs_pos_eq by lra.
    apply Rle_lt_trans with 2; [exact Hle | ]. change 2 with (bpow radix2 1). apply bpow_lt; lia. }
  destruct (q_to_float_round c Vc Hr) as [Fx Bx]. change (qval c) with cv in Bx.
  set (x := Q256.to_f64 c) in *.
  assert (Hx28 : bpow radix2 (-28) <= B x) by (rewrite Bx; apply rndF_ge_bpow; [lia | exact Hlo]).
  assert (Hx2 : B x <= 2) by (rewrite Bx; apply rndF_le_two; lra).
  assert (Hcn : bpow radix2 (-1022) <= Rabs cv).
  { rewrite Rabs_pos_eq by lra. apply Rle_trans with (bpow radix2 (-28)); [apply bpow_le; lia | exact Hlo]. }
  pose proof (rnd_rel_f cv Hcn) as R0. rewrite <- Bx in R0. rewrite (Rabs_pos_eq cv) in R0 by lra.
  assert (P53 : bpow radix2 (-53) = / 9007199254740992) by exact bp53. rewrite P53 in R0.
  apply Rabs_le_inv in R0 as [R0a R0b].
  destruct one_val as [V1 Fone].
  assert (Hx0 : B x <> 0) by lra.
  assert (Hb : bnd 1 28 (B asin_one / B x)).
  { unfold bnd. rewrite V1. change (IZR 1) with 1. rewrite Rmult_1_l.
    assert (Hb28 : bpow radix2 28 * bpow radix2 (-28) = 1) by (rewrite <- bpow_plus; reflexivity).
    rewrite Rabs_pos_eq by (apply Rlt_le; apply Rdiv_lt_0_compat; lra).
    apply (Rmult_le_reg_r (B x)); [lra | ]. unfold Rdiv. rewrite Rmult_assoc, Rinv_l by exact Hx0. nra. }
  destruct (fdiv_bnd 1 28 asin_one x Fone Hx0 ltac:(lia) ltac:(lia) (pow_room 1 (1024 - 28) ltac:(lia) ltac:(lia)) ltac:(lia) Hb) as [Ff [Ef _]].
  set (f := fdiv asin_one x) in *.
  rewrite V1 in Ef.
  assert (Hq : bpow radix2 (-1022) <= Rabs (1 / B x)).
  { rewrite Rabs_pos_eq by (apply Rlt_le; apply Rdiv_lt_0_compat; lra).
    apply Rle_trans with (/ 2); [ | apply Rle_trans with (1 / B x); [ | lra]].
    - apply Rle_trans with (bpow radix2 (-1)); [apply bpow_le; lia | bpow_num; lra].
    - unfold Rdiv. rewrite Rmult_1_l. apply Rinv_le_contravar; lra. }
  pose proof (rnd_rel_f _ Hq) as R1. rewrite <- Ef in R1. rewrite P53 in R1.
  rewrite (Rabs_pos_eq (1 / B x)) in R1 by (apply Rlt_le; apply Rdiv_lt_0_compat; lra).
  destruct (q_float_ok f Ff) as [Vy Qy].
  change (qf f) with (q_float f). refine (conj Vy (conj _ _)).
  - rewrite Qy. apply Rabs_le_inv in R1 as [R1a R1b].
    assert (Hw : 0 < 1 / B x). { apply Rdiv_lt_0_compat; [lra | lra]. }
    set (w := 1 / B x) in *. lra.
  - rewrite Qy. set (w := 1 / B x) in *.
    assert (Hwx : w * B x = 1) by (unfold w; field; exact Hx0).
    assert (Hw : 0 < w) by (unfold w; apply Rdiv_lt_0_compat; lra).
    apply Rabs_le_inv in R1 as [R1a R1b].
    assert (Hcw : cv * w <= 1.0001).
    { apply (Rmult_le_reg_r (B x)); [lra | ]. nra. }
    replace (cv * B f - 1) with (cv * (B f - w) + (cv - B x) * w) by (nra).
    assert (bpow radix2 (-51) = / 2251799813685248) by (bpow_num; reflexivity).
    assert (Hs1 : Rabs (cv * (B f - w)) <= / 9007199254740992 * (cv * w)).
    { rewrite Rabs_mult, (Rabs_pos_eq cv) by lra.
      assert (cv * Rabs (B f - w) <= cv * (/ 9007199254740992 * w)) by (apply Rmult_le_compat_l; [lra | apply Rabs_le; split; lra]).
      nra. }
    assert (Hs2 : Rabs ((cv - B x) * w) <= / 9007199254740992 * (cv * w)).
    { rewrite Rabs_mult, (Rabs_pos_eq w) by lra.
      assert (Rabs (cv - B x) <= / 9007199254740992 * cv) by (apply Rabs_le; split; lra).
      nra. }
    apply Rle_trans with (Rabs (cv * (B f - w)) + Rabs ((cv - B x) * w)); [apply Rabs_triang | ].
    nra.
Qed.

Lemma small_bpow n : (n <= -20)%Z -> bpow radix2 n <= / 1000000.
Proof.
  intros H. apply Rle_trans with (bpow radix2 (-20)); [apply bpow_le; lia | bpow_num; interval with (i_prec 100)].
Qed.

Theorem q_recip_ok c : Q256Real.valid c -> bpow radix2 (-28) <= qval c <= 1.0001 ->
  Q256Real.valid (q_recip c) /\ 0 < qval (q_recip c) /\ Rabs (qval c * qval (q_recip c) - 1) <= bpow radix2 (-252).
Proof.
  intros Vc Hc. destruct Hc as [Hlo Hhi].
  assert (Hcp : 0 < qval c) by (pose proof (bpow_gt_0 radix2 (-28)); lra).
  destruct (recip_start c Vc (conj Hlo Hhi)) as [V0 [P0 E0]].
  rewrite q_recip_steps.
  set (y0 := qf (fdiv asin_one (Q256.to_f64 c))) in *.
  destruct (recip_step_ok c y0 (bpow radix2 (-51)) Vc V0 Hcp P0 E0 (small_bpow (-51) ltac:(lia))) as [V1 [P1 E1]].
  assert (E1' : Rabs (qval c * qval (recip_step c y0) - 1) <= bpow radix2 (-101))
    by (apply Rle_trans with (1 := E1); apply chain1; split; [apply bpow_ge_0 | apply Rle_refl]).
  destruct (recip_step_ok c (recip_step c y0) (bpow radix2 (-101)) Vc V1 Hcp P1 E1' (small_bpow (-101) ltac:(lia))) as [V2 [P2 E2]].
  assert (E2' : Rabs (qval c * qval (recip_step c (recip_step c y0)) - 1) <= bpow radix2 (-201))
    by (apply Rle_trans with (1 := E2); apply chain2; split; [apply bpow_ge_0 | apply Rle_refl]).
  destruct (recip_step_ok c (recip_step c (recip_step c y0)) (bpow radix2 (-201)) Vc V2 Hcp P2 E2' (small_bpow (-201) ltac:(lia))) as [V3 [P3 E3]].
  refine (conj V3 (conj P3 _)).
  apply Rle_trans with (1 := E3); apply chain3; split; [apply bpow_ge_0 | apply Rle_refl].
Qed.
