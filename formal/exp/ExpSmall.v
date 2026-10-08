(** exp/mod.rs's accurate path for small arguments, [2^-54 <= |x| < 2^-30]
    ([small_parts] and [small], docs/exp.md, section 6), transcribed on binary64
    and the proved Q128 transcription (formal/q), and proved: [h + w] is within
    [2^-178] of [e^x] ([small_parts_ok]), and when [e^x] keeps the mantissa
    distance [LM] guarantees here, [2^-158], from every rounding breakpoint,
    [small] returns [RN(e^x)] ([exp_small_ok]). [d]'s evaluation is
    formal/exp/small.g's theorem; this file proves its hypotheses. *)

From Coq Require Import ZArith Reals Lia Lra Psatz List Bool.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Q Require QSpec Q128.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Eft RoundingGaps RoundingCore RoundingTest Encodings.
From Gappa Require Gappa_definitions Gappa_pred_bnd.
From Interval Require Import Tactic.
Require ExpTables ExpAccurate exp_small.
Import ExpTables.

Open Scope R_scope.

Ltac gappa_num := cbv beta iota zeta delta -[Rle Rlt Rabs IZR bpow Rdiv Rminus Rinv Ropp pow Rplus Rmult].
Ltac gappa_num_in H := cbv beta iota zeta delta -[Rle Rlt Rabs IZR bpow Rdiv Rminus Rinv Ropp pow Rplus Rmult] in H.

(** formal/exp/small.g's theorem, over reals: [d], computed in Q128 with each
    operation modelled by its contract, is within [2^-122] relatively of
    [D = (x²/2)·(1 + (x/3)·(1 + (x/4)·(1 + x/5)))]. *)
Theorem small_bound x k5 m5 s5 k4 m4a m4b s4 k3 m3a m3b s3 m2a k2 m2b m2c :
  Rabs x <= / 2 ^ 30 -> x <> 0 ->
  Rabs k2 <= / 2 ^ 127 -> Rabs k3 <= / 2 ^ 127 -> Rabs k4 <= / 2 ^ 127 -> Rabs k5 <= / 2 ^ 127 ->
  - / 2 ^ 127 <= m5 <= 0 -> - / 2 ^ 127 <= m4a <= 0 -> - / 2 ^ 127 <= m4b <= 0 ->
  - / 2 ^ 127 <= m3a <= 0 -> - / 2 ^ 127 <= m3b <= 0 ->
  - / 2 ^ 127 <= m2a <= 0 -> - / 2 ^ 127 <= m2b <= 0 -> - / 2 ^ 127 <= m2c <= 0 ->
  Rabs s5 <= / 2 ^ 126 -> Rabs s4 <= / 2 ^ 126 -> Rabs s3 <= / 2 ^ 126 ->
  let g5 := 1 + x * (1 / 5 * (1 + k5)) * (1 + m5) + s5 in
  let g4 := 1 + x * (1 / 4 * (1 + k4)) * (1 + m4a) * g5 * (1 + m4b) + s4 in
  let g3 := 1 + x * (1 / 3 * (1 + k3)) * (1 + m3a) * g4 * (1 + m3b) + s3 in
  let d := x * x * (1 + m2a) * (1 / 2 * (1 + k2)) * (1 + m2b) * g3 * (1 + m2c) in
  let D := x * x / 2 * (1 + x / 3 * (1 + x / 4 * (1 + x / 5))) in
  Rabs ((d - D) / D) <= / 2 ^ 122.
Proof.
  intros Hx Hx0 Hk2 Hk3 Hk4 Hk5 Hm5 Hm4a Hm4b Hm3a Hm3b Hm2a Hm2b Hm2c Hs5 Hs4 Hs3. cbv zeta.
  apply Rabs_le_inv in Hx. apply Rabs_le_inv in Hk2. apply Rabs_le_inv in Hk3. apply Rabs_le_inv in Hk4.
  apply Rabs_le_inv in Hk5. apply Rabs_le_inv in Hs5. apply Rabs_le_inv in Hs4. apply Rabs_le_inv in Hs3.
  apply Rnot_lt_le; intros Hlt.
  apply (exp_small.l1 x k5 m5 s5 k4 m4a m4b s4 k3 m3a m3b s3 m2a k2 m2b m2c).
  repeat split; try exact Hx0; try (gappa_num; simpl; lra).
  intros Hb; gappa_num_in Hb; cbv [Gappa_pred_bnd.Float1] in Hb.
  apply (Rlt_irrefl (/ 2 ^ 122)); apply Rlt_le_trans with (1 := Hlt).
  apply Rabs_le; simpl in Hb |- *; lra.
Qed.

(** * The transcription *)

(** [small_parts]'s [d = e^x - 1 - x] to degree 5, in Q128. *)
Definition small_d (x : binary_float 53 1024) : Q128.q128 :=
  let xq := ExpAccurate.qf x in
  let g5 := Q128.add ExpAccurate.q_one (Q128.mul xq (ExpAccurate.q_recip 5)) in
  let g4 := Q128.add ExpAccurate.q_one (Q128.mul (Q128.mul xq (ExpAccurate.q_recip 4)) g5) in
  let g3 := Q128.add ExpAccurate.q_one (Q128.mul (Q128.mul xq (ExpAccurate.q_recip 3)) g4) in
  Q128.mul (Q128.mul (Q128.mul xq xq) (ExpAccurate.q_recip 2)) g3.

(** [small_parts(x)]: [(h, l) = two_sum(1, x)] and [w = l + d]. *)
Definition small_parts (x : binary_float 53 1024) : binary_float 53 1024 * Q128.q128 :=
  let '(h, l) := two_sum64 ExpFast.c_one x in
  (h, Q128.add (ExpAccurate.qf l) (small_d x)).

(** [small(x)]: [RN(h + w)], [h] unless [|w|] reaches half the gap on [w]'s
    side of [h]. *)
Definition small (x : binary_float 53 1024) : binary_float 53 1024 :=
  let '(h, w) := small_parts x in
  let up := negb (Q128.neg w && negb (Q128.m w =? 0)%Z) in
  let gap := if negb up && fraction_zero h then fmul (ulp_f h) half else ulp_f h in
  match Q128.cmp_abs w (ExpAccurate.qf (fmul gap half)) with
  | Lt => h
  | _ => if up then b64_of_bits (bits_of_b64 h + 1) else b64_of_bits (bits_of_b64 h - 1)
  end.

(** [d]'s exact counterpart. *)
Definition Dpoly (x : R) : R := x * x / 2 * (1 + x / 3 * (1 + x / 4 * (1 + x / 5))).

(** The reciprocal [1/i] as [(1/i)·(1 + k)] with [|k| <= 2^-127]. *)
Lemma recip_k i : (1 <= i <= 12)%nat ->
  ExpAccurate.NZ (ExpAccurate.q_recip i) /\
  exists k, Rabs k <= / 2 ^ 127 /\ Q128.qval (ExpAccurate.q_recip i) = 1 / INR i * (1 + k).
Proof.
  intros Hi. destruct (ExpAccurate.q_recip_ok i Hi) as [N V]. split; [exact N | ].
  assert (P : 0 < INR i) by (apply lt_0_INR; lia).
  exists (Q128.qval (ExpAccurate.q_recip i) * INR i - 1). split; [exact V | field; lra].
Qed.

(** One [1 + b] step: [b] at most [1], so the addition errs by at most [2^-126]. *)
Lemma one_plus b : ExpAccurate.NZ b -> Rabs (Q128.qval b) <= 1 ->
  ExpAccurate.NZ (Q128.add ExpAccurate.q_one b) /\
  exists s, Rabs s <= / 2 ^ 126 /\ Q128.qval (Q128.add ExpAccurate.q_one b) = 1 + Q128.qval b + s.
Proof.
  intros Nb Hb. destruct (ExpAccurate.add_any _ _ ExpAccurate.q_one_nz Nb) as [N E].
  split; [exact N | ]. rewrite ExpAccurate.q_one_val in E.
  exists (Q128.qval (Q128.add ExpAccurate.q_one b) - (1 + Q128.qval b)). split; [ | ring].
  apply Rle_trans with (1 := E). rewrite Rabs_R1, Rmax_left by lra.
  change (bpow radix2 (-126)) with (bpow radix2 (- Z.of_nat 126)). rewrite ExpAccurate.bpow_m. lra.
Qed.

Lemma mul_m a b : ExpAccurate.NZ a -> ExpAccurate.NZ b ->
  ExpAccurate.NZ (Q128.mul a b) /\
  exists m, - / 2 ^ 127 <= m <= 0 /\ Q128.qval (Q128.mul a b) = Q128.qval a * Q128.qval b * (1 + m).
Proof.
  intros Na Nb. destruct (ExpAccurate.mul_any a b Na Nb) as [N [m [Hm E]]].
  split; [exact N | ]. exists m. split; [ | exact E].
  change (bpow radix2 (-127)) with (bpow radix2 (- Z.of_nat 127)) in Hm. rewrite ExpAccurate.bpow_m in Hm. exact Hm.
Qed.

(** [d] is within [2^-122] relatively of [Dpoly x]. *)
Lemma d_ok x : is_finite 53 1024 x = true -> B2R 53 1024 x <> 0 -> Rabs (B2R 53 1024 x) <= / 2 ^ 30 ->
  ExpAccurate.NZ (small_d x) /\
  Rabs ((Q128.qval (small_d x) - Dpoly (B2R 53 1024 x)) / Dpoly (B2R 53 1024 x)) <= / 2 ^ 122.
Proof.
  intros Fx Hx0 Hx. unfold small_d. cbv zeta.
  set (xq := ExpAccurate.qf x).
  set (g5 := Q128.add ExpAccurate.q_one (Q128.mul xq (ExpAccurate.q_recip 5))).
  set (g4 := Q128.add ExpAccurate.q_one (Q128.mul (Q128.mul xq (ExpAccurate.q_recip 4)) g5)).
  set (g3 := Q128.add ExpAccurate.q_one (Q128.mul (Q128.mul xq (ExpAccurate.q_recip 3)) g4)).
  set (d := Q128.mul (Q128.mul (Q128.mul xq xq) (ExpAccurate.q_recip 2)) g3).
  set (v := B2R 53 1024 x) in *.
  assert (Nx : ExpAccurate.NZ xq) by apply ExpAccurate.from_f64_nz.
  assert (Vx : Q128.qval xq = v) by (unfold xq, ExpAccurate.qf; rewrite ExpAccurate.from_f64_b64 by exact Fx; reflexivity).
  assert (U30 : / 2 ^ 30 < / 1000000) by interval with (i_prec 64).
  assert (U127 : 0 < / 2 ^ 127 < / 1000000) by (split; interval with (i_prec 64)).
  assert (U126 : 0 < / 2 ^ 126 < / 1000000) by (split; interval with (i_prec 64)).
  apply Rabs_le_inv in Hx.
  destruct (recip_k 5 ltac:(lia)) as [N5 [k5 [Hk5 V5]]].
  destruct (recip_k 4 ltac:(lia)) as [N4 [k4 [Hk4 V4]]].
  destruct (recip_k 3 ltac:(lia)) as [N3 [k3 [Hk3 V3]]].
  destruct (recip_k 2 ltac:(lia)) as [N2 [k2 [Hk2 V2]]].
  replace (INR 5) with 5 in V5 by (simpl; ring). replace (INR 4) with 4 in V4 by (simpl; ring).
  replace (INR 3) with 3 in V3 by (simpl; ring). replace (INR 2) with 2 in V2 by (simpl; ring).
  pose proof Hk5 as Hk5'. pose proof Hk4 as Hk4'. pose proof Hk3 as Hk3'. apply Rabs_le_inv in Hk5', Hk4', Hk3'.
  (* g5 *)
  destruct (mul_m xq _ Nx N5) as [Nb5 [m5 [Hm5 Eb5]]].
  rewrite Vx, V5 in Eb5.
  assert (Bb5 : Rabs (Q128.qval (Q128.mul xq (ExpAccurate.q_recip 5))) <= 1)
    by (rewrite Eb5; interval).
  destruct (one_plus _ Nb5 Bb5) as [Ng5 [s5 [Hs5 Eg5]]]. fold g5 in Ng5, Eg5. rewrite Eb5 in Eg5.
  assert (G5 : 0.9 <= Q128.qval g5 <= 1.1) by (rewrite Eg5; apply Rabs_le_inv in Hs5; split; interval).
  (* g4 *)
  destruct (mul_m xq _ Nx N4) as [Na4 [m4a [Hm4a Ea4]]]. rewrite Vx, V4 in Ea4.
  destruct (mul_m _ g5 Na4 Ng5) as [Nb4 [m4b [Hm4b Eb4]]]. rewrite Ea4 in Eb4.
  assert (Bb4 : Rabs (Q128.qval (Q128.mul (Q128.mul xq (ExpAccurate.q_recip 4)) g5)) <= 1)
    by (rewrite Eb4; interval).
  destruct (one_plus _ Nb4 Bb4) as [Ng4 [s4 [Hs4 Eg4]]]. fold g4 in Ng4, Eg4. rewrite Eb4 in Eg4.
  assert (G4 : 0.9 <= Q128.qval g4 <= 1.1) by (rewrite Eg4; apply Rabs_le_inv in Hs4; split; interval).
  (* g3 *)
  destruct (mul_m xq _ Nx N3) as [Na3 [m3a [Hm3a Ea3]]]. rewrite Vx, V3 in Ea3.
  destruct (mul_m _ g4 Na3 Ng4) as [Nb3 [m3b [Hm3b Eb3]]]. rewrite Ea3 in Eb3.
  assert (Bb3 : Rabs (Q128.qval (Q128.mul (Q128.mul xq (ExpAccurate.q_recip 3)) g4)) <= 1)
    by (rewrite Eb3; interval).
  destruct (one_plus _ Nb3 Bb3) as [Ng3 [s3 [Hs3 Eg3]]]. fold g3 in Ng3, Eg3. rewrite Eb3 in Eg3.
  (* d *)
  destruct (mul_m xq xq Nx Nx) as [Na2 [m2a [Hm2a Ea2]]]. rewrite Vx in Ea2.
  destruct (mul_m _ _ Na2 N2) as [Nb2 [m2b [Hm2b Eb2]]]. rewrite Ea2, V2 in Eb2.
  destruct (mul_m _ g3 Nb2 Ng3) as [Nd [m2c [Hm2c Ed]]]. fold d in Nd, Ed. rewrite Eb2 in Ed.
  split; [exact Nd | ].
  rewrite Ed, Eg3, Eg4, Eg5.
  exact (small_bound v k5 m5 s5 k4 m4a m4b s4 k3 m3a m3b s3 m2a k2 m2b m2c
           ltac:(apply Rabs_le; lra) Hx0 Hk2 Hk3 Hk4 Hk5 Hm5 Hm4a Hm4b Hm3a Hm3b Hm2a Hm2b Hm2c Hs5 Hs4 Hs3).
Qed.

(** * [h + w] *)

(** Near [1], ulp is [2^-53] or [2^-52]. *)
Lemma ulp_range v : / 2 <= v < 2 -> bpow radix2 (-53) <= ulp radix2 fexp64 v <= bpow radix2 (-52).
Proof.
  intros [H1 H2]. rewrite ulp_neq_0 by lra. unfold cexp, FLT_exp.
  assert (M1 : (0 <= mag radix2 v)%Z).
  { apply mag_ge_bpow. rewrite Rabs_pos_eq by lra. change (bpow radix2 (0 - 1)) with (/ 2). lra. }
  assert (M2 : (mag radix2 v <= 1)%Z).
  { apply mag_le_bpow; [lra | ]. rewrite Rabs_pos_eq by lra. change (bpow radix2 1) with 2. lra. }
  split; apply bpow_le; lia.
Qed.

(** [small_parts(x)]: [h = RN(1 + x)], [|w|] at most half [h]'s ulp and
    [2^-60] more, and [h + w] within [2^-178] of [e^x]. *)
Theorem small_parts_ok x : finite x -> B x <> 0 -> Rabs (B x) <= / 2 ^ 30 ->
  let '(h, w) := small_parts x in
  finite h /\ B h = rndF (1 + B x) /\ 0.99 < B h < 1.01 /\ ExpAccurate.NZ w /\
  Rabs (Q128.qval w) <= / 2 * ulp radix2 fexp64 (B h) + / 2 ^ 60 /\
  Rabs (B h + Q128.qval w - exp (B x)) <= / 2 ^ 178.
Proof.
  intros Fx Hx0 Hx. unfold small_parts.
  destruct (d_ok x Fx Hx0 Hx) as [Nd Hd].
  assert (B1 : B ExpFast.c_one = 1).
  { rewrite ExpFast.c_one_val. assert (E : 2 ^ 52 = 4503599627370496) by ring. rewrite E. field. }
  assert (P1 : 1 <= bpow radix2 1020) by (change 1 with (bpow radix2 0); apply bpow_le; lia).
  assert (U30 : / 2 ^ 30 < / 1000) by interval.
  pose proof (two_sum_ieee ExpFast.c_one x ExpFast.c_one_finite Fx
                ltac:(rewrite B1, Rabs_R1; exact P1) ltac:(lra)) as TS.
  destruct (two_sum64 ExpFast.c_one x) as [h l]. destruct TS as [Fh [Fl [Bh Bhl]]].
  rewrite B1 in Bh, Bhl.
  set (v := B x) in *. set (d := small_d x) in *. set (D := Dpoly v) in *.
  pose proof Hx as Hx'. apply Rabs_le_inv in Hx'.
  (* h *)
  assert (Hr : Rabs (B h - (1 + v)) <= / 2 ^ 53 * (1 + v)).
  { rewrite Bh, <- RNE_rndF.
    assert (Z1 : bpow radix2 (-1022) <= Rabs (1 + v)).
    { apply Rle_trans with (bpow radix2 (-1)); [apply bpow_le; lia | ].
      rewrite Rabs_pos_eq by lra. change (bpow radix2 (-1)) with (/ 2). lra. }
    pose proof (rnd_rel (1 + v) Z1) as R. rewrite (Rabs_pos_eq (1 + v)) in R by lra.
    change (bpow radix2 (-53)) with (bpow radix2 (- Z.of_nat 53)) in R. rewrite ExpAccurate.bpow_m in R.
    exact R. }
  assert (U53 : / 2 ^ 53 < / 1000) by interval.
  apply Rabs_le_inv in Hr.
  assert (Hh : 0.99 < B h < 1.01) by (split; nra).
  destruct (ulp_range (B h) ltac:(lra)) as [Ul Uu].
  change (bpow radix2 (-53)) with (bpow radix2 (- Z.of_nat 53)) in Ul.
  change (bpow radix2 (-52)) with (bpow radix2 (- Z.of_nat 52)) in Uu.
  rewrite ExpAccurate.bpow_m in Ul, Uu.
  assert (Lh : Rabs (B l) <= / 2 * ulp radix2 fexp64 (B h)).
  { assert (El : B l = - (B h - (1 + v))) by lra.
    rewrite El, Rabs_Ropp, Bh. apply error_le_half_ulp_round; exact _. }
  (* d *)
  assert (Dpos : 0 < D).
  { unfold D, Dpoly.
    assert (F : 0.9 <= 1 + v / 3 * (1 + v / 4 * (1 + v / 5)) <= 1.1) by (split; interval).
    assert (0 < v * v) by (apply Rsqr_pos_lt; exact Hx0). nra. }
  assert (Db : D <= / 2 ^ 61 * 1.1) by (unfold D, Dpoly; interval).
  assert (E2 : Rabs (Q128.qval d - D) <= / 2 ^ 122 * D).
  { replace (Q128.qval d - D) with ((Q128.qval d - D) / D * D) by (field; lra).
    rewrite Rabs_mult, (Rabs_pos_eq D) by lra. apply Rmult_le_compat_r; lra. }
  assert (E3 : Rabs (D - (exp v - 1 - v)) <= / 2 ^ 189).
  { unfold D, Dpoly. interval with (i_taylor v, i_degree 8, i_prec 300). }
  (* w *)
  assert (Nl : ExpAccurate.NZ (ExpAccurate.qf l)) by apply ExpAccurate.from_f64_nz.
  assert (Vl : Q128.qval (ExpAccurate.qf l) = B l)
    by (unfold ExpAccurate.qf; rewrite ExpAccurate.from_f64_b64 by exact Fl; reflexivity).
  destruct (ExpAccurate.add_any _ _ Nl Nd) as [Nw E1]. rewrite Vl in E1.
  change (bpow radix2 (-126)) with (bpow radix2 (- Z.of_nat 126)) in E1. rewrite ExpAccurate.bpow_m in E1.
  assert (U122 : / 2 ^ 122 < / 1000) by interval.
  assert (Qd : Rabs (Q128.qval d) <= / 2 ^ 53).
  { apply Rabs_le_inv in E2. assert (/ 2 ^ 61 * 1.1 * (1 + / 1000) <= / 2 ^ 53) by interval.
    apply Rabs_le. nra. }
  assert (Mx : Rmax (Rabs (B l)) (Rabs (Q128.qval d)) <= / 2 ^ 53) by (apply Rmax_lub; lra).
  assert (E1' : Rabs (Q128.qval (Q128.add (ExpAccurate.qf l) d) - (B l + Q128.qval d)) <= / 2 ^ 179).
  { apply Rle_trans with (1 := E1). apply Rle_trans with (/ 2 ^ 126 * / 2 ^ 53).
    - apply Rmult_le_compat_l; [apply Rlt_le, Rinv_0_lt_compat, pow_lt; lra | exact Mx].
    - right. rewrite <- Rinv_mult_distr by (apply pow_nonzero; lra). rewrite <- pow_add. reflexivity. }
  set (w := Q128.add (ExpAccurate.qf l) d) in *.
  assert (E2' : Rabs (Q128.qval d - D) <= / 2 ^ 122 * (/ 2 ^ 61 * 1.1)).
  { apply Rle_trans with (1 := E2). apply Rmult_le_compat_l; [apply Rlt_le, Rinv_0_lt_compat, pow_lt; lra | exact Db]. }
  assert (S1 : / 2 ^ 179 + / 2 ^ 122 * (/ 2 ^ 61 * 1.1) + / 2 ^ 189 <= / 2 ^ 178) by interval.
  assert (S2 : / 2 ^ 61 * 1.1 + / 2 ^ 122 * (/ 2 ^ 61 * 1.1) + / 2 ^ 179 <= / 2 ^ 60) by interval.
  apply Rabs_le_inv in E1'. apply Rabs_le_inv in E2'. apply Rabs_le_inv in E3. apply Rabs_le_inv in Lh.
  repeat split; try assumption; try lra.
  all: apply Rabs_le; lra.
Qed.

(** * The rounding decision *)

(** [h]'s gaps: [ulp(h)] is [2^e], [e] in [-53, -52], the gap below [h] is
    [2^(e-1)] at a power of two and [2^e] otherwise. *)
Lemma gap_ok h : finite h -> 0.99 < B h < 1.01 ->
  exists e, (-53 <= e <= -52)%Z /\ finite (ulp_f h) /\ B (ulp_f h) = bpow radix2 e /\
    ulp radix2 fexp64 (B h) = bpow radix2 e /\
    (fraction_zero h = true -> B h - pred radix2 fexp64 (B h) = bpow radix2 (e - 1)) /\
    (fraction_zero h = false -> B h - pred radix2 fexp64 (B h) = bpow radix2 e).
Proof.
  intros Fh Hh.
  assert (N : bpow radix2 (-1022) <= B h).
  { apply Rle_trans with (bpow radix2 (-1)); [apply bpow_le; lia | ]. change (bpow radix2 (-1)) with (/ 2). lra. }
  destruct (pos_normal h Fh N) as [mx [ex [Hx [Eh [Mx [Ex [V [M [Ulp _]]]]]]]]].
  pose proof (bpow_gt_0 radix2 ex) as Pe.
  assert (Ee : (-53 <= ex <= -52)%Z).
  { split.
    - assert (L : bpow radix2 (-1) < bpow radix2 (53 + ex)).
      { change (bpow radix2 (-1)) with (/ 2). rewrite bpow_plus. apply Rlt_trans with (B h); [lra | ].
        rewrite V. apply Rmult_lt_compat_r; [lra | ].
        replace (bpow radix2 53) with (IZR (2 ^ 53)) by reflexivity. apply IZR_lt. lia. }
      apply lt_bpow in L. lia.
    - assert (L : bpow radix2 (52 + ex) < bpow radix2 1).
      { rewrite bpow_plus. apply Rle_lt_trans with (B h); [ | change (bpow radix2 1) with 2; lra].
        rewrite V. apply Rmult_le_compat_r; [lra | ].
        replace (bpow radix2 52) with (IZR (2 ^ 52)) by reflexivity. apply IZR_le. lia. }
      apply lt_bpow in L. lia. }
  exists ex.
  assert (Uf : ulp_f h = binary_normalize 53 1024 eq_refl eq_refl mode_NE 1 ex false) by (rewrite Eh; reflexivity).
  destruct (pow2_f ex ltac:(lia)) as [Bu Fu]. rewrite <- Uf in Bu, Fu.
  assert (Fz : fraction_zero h = (Zpos mx mod 2 ^ 52 =? 0)%Z) by (rewrite Eh; reflexivity).
  assert (Pos : 0 < B h) by lra.
  split; [lia | ]. split; [exact Fu | ]. split; [exact Bu | ]. split; [exact Ulp | ].
  rewrite Fz. split.
  - intros Z0. apply Z.eqb_eq in Z0.
    assert (Bot : Zpos mx = (2 ^ 52)%Z) by (pose proof (Z.div_mod (Zpos mx) (2 ^ 52) ltac:(lia)); lia).
    rewrite pred_eq_pos by lra. unfold pred_pos. rewrite M.
    assert (P2 : B h = bpow radix2 (ex + 53 - 1)).
    { rewrite V, Bot. replace (ex + 53 - 1)%Z with (52 + ex)%Z by ring. rewrite bpow_plus. reflexivity. }
    rewrite (Req_bool_true _ _ P2). unfold FLT_exp.
    replace (Z.max (ex + 53 - 1 - 53) (-1074)) with (ex - 1)%Z by lia. ring.
  - intros Z1. apply Z.eqb_neq in Z1.
    rewrite pred_eq_pos by lra. unfold pred_pos. rewrite M.
    assert (NP : B h <> bpow radix2 (ex + 53 - 1)).
    { rewrite V. replace (ex + 53 - 1)%Z with (52 + ex)%Z by ring. rewrite bpow_plus. intros E.
      apply Rmult_eq_reg_r in E; [ | lra]. replace (bpow radix2 52) with (IZR (2 ^ 52)) in E by reflexivity.
      apply eq_IZR in E. rewrite E in Z1. apply Z1. reflexivity. }
    rewrite (Req_bool_false _ _ NP), Ulp. ring.
Qed.

Lemma bpow_m1 e : bpow radix2 (e - 1) = bpow radix2 e / 2.
Proof. unfold Zminus. rewrite bpow_plus. reflexivity. Qed.

(** [cmp_abs] compares magnitudes exactly, zero included. *)
Lemma cmp_lt a b : ExpAccurate.NZ a -> ExpAccurate.NZ b -> 0 < Rabs (Q128.qval b) ->
  (Q128.cmp_abs a b = Lt <-> Rabs (Q128.qval a) < Rabs (Q128.qval b)).
Proof.
  intros Na Nb Pb. rewrite <- (ExpAccurate.mag_abs a Na), <- (ExpAccurate.mag_abs b Nb) in *.
  destruct Nb as [Zb | Nb'].
  { exfalso. unfold Q128.mag in Pb. rewrite Zb, F2R_0 in Pb. lra. }
  assert (Mb : (Q128.m b =? 0)%Z = false).
  { apply Z.eqb_neq. unfold QSpec.normalized in Nb'. assert (0 < 2 ^ (128 - 1))%Z by (apply Z.pow_pos_nonneg; lia). lia. }
  destruct Na as [Za | Na'].
  { unfold Q128.cmp_abs. rewrite Za, Mb. cbn. unfold Q128.mag at 1. rewrite Za, F2R_0.
    split; [intros _; exact Pb | reflexivity]. }
  pose proof (Q128.cmp_abs_ok a b Na' Nb') as C.
  destruct (Q128.cmp_abs a b); split; intros L; try reflexivity; try discriminate; lra.
Qed.

(** [!w.is_negative()] is [w >= 0]. *)
Lemma up_sign w : ExpAccurate.NZ w ->
  if negb (Q128.neg w && negb (Q128.m w =? 0)%Z) then 0 <= Q128.qval w else Q128.qval w < 0.
Proof.
  intros Nw. pose proof (ExpAccurate.NZ_nonneg w Nw) as M0.
  unfold Q128.qval, QSpec.val.
  destruct (Q128.neg w); destruct (Z.eqb_spec (Q128.m w) 0) as [Z0 | Z1]; cbn [andb negb].
  - rewrite Z0. unfold F2R. simpl. lra.
  - apply F2R_lt_0. simpl. lia.
  - apply F2R_ge_0. simpl. lia.
  - apply F2R_ge_0. simpl. lia.
Qed.

(** * The small-argument path end to end

    [LM] guarantees [e^x] keeps a mantissa distance of [2^-158] from every
    rounding breakpoint for [2^-54 <= |x| < 2^-30] (docs/exp.md, section 6).
    [h + w] is within [2^-178] of [e^x], so it rounds as [e^x] does and is no
    breakpoint itself, and [small] decides its rounding exactly. *)
Theorem exp_small_ok x : finite x -> / 2 ^ 54 <= Rabs (B x) < / 2 ^ 30 ->
  ExpAccurate.midpoint_far (exp (B x)) (/ 2 ^ 158) ->
  finite (small x) /\ B (small x) = rndF (exp (B x)).
Proof.
  intros Fx [Hx1 Hx2] Far.
  assert (C178 : / 2 ^ 178 < / 2 ^ 158 * 0.99 / 2) by interval.
  assert (C158 : / 2 ^ 158 < / 2) by interval.
  assert (S60 : / 2 ^ 60 < / 2 ^ 53 / 4) by interval.
  assert (C52 : / 2 ^ 52 < / 1000) by interval.
  assert (Hx0 : B x <> 0).
  { intros E. rewrite E, Rabs_R0 in Hx1. assert (0 < / 2 ^ 54) by (apply Rinv_0_lt_compat, pow_lt; lra). lra. }
  pose proof (Rabs_le_inv _ _ (Rlt_le _ _ Hx2)) as Hx'.
  pose proof (small_parts_ok x Fx Hx0 (Rlt_le _ _ Hx2)) as SP.
  unfold small. destruct (small_parts x) as [h w]. destruct SP as [Fh [_ [Hh [Nw [Wb Err]]]]].
  unfold ExpAccurate.midpoint_far in Far.
  assert (Pz : 0.99 < exp (B x)) by interval.
  set (H := B h) in *. set (W := Q128.qval w) in *. set (z := exp (B x)) in *.
  change (FLT_exp (-1074) 53) with (FLT_exp emin prec) in Wb.
  (* [h + w] rounds as [e^x], and is no breakpoint *)
  assert (P158 : 0 < / 2 ^ 158) by (apply Rinv_0_lt_compat, pow_lt; lra).
  destruct (ExpAccurate.far_abs z (/ 2 ^ 158) ltac:(lra) P158) as [D1 D2].
  set (dl := / 2 ^ 158 * bpow radix2 (mag radix2 z - 1)) in *.
  assert (Close : Rabs (H + W - z) < dl).
  { nra. }
  assert (RZ : rndF (H + W) = rndF z).
  { apply (ExpAccurate.same_rounding_abs z (H + W) dl); [lra | nra | exact Far | exact Close]. }
  assert (NoMid : forall u, fmtF u -> 0 <= u -> H + W <> (u + succ radix2 (FLT_exp emin prec) u) / 2).
  { intros u Fu U0 E. pose proof (Far u Fu U0) as F. rewrite <- E, Rabs_minus_sym in F. lra. }
  rewrite <- RZ.
  (* the gaps around [h] *)
  destruct (gap_ok h Fh Hh) as [e [Ee [Fu [Bu [Ulp [Gz Gnz]]]]]].
  change (FLT_exp (-1074) 53) with (FLT_exp emin prec) in Ulp, Gz, Gnz. fold H in Ulp, Gz, Gnz.
  rewrite Ulp in Wb.
  pose proof (bpow_gt_0 radix2 e) as Pe.
  pose proof (bpow_m1 e) as E1. pose proof (bpow_m1 (e - 1)) as E2. rewrite E1 in E2.
  assert (Ue : / 2 ^ 53 <= bpow radix2 e <= / 2 ^ 52).
  { rewrite <- (ExpAccurate.bpow_m 53), <- (ExpAccurate.bpow_m 52). split; apply bpow_le; simpl; lia. }
  assert (FH : fmtF H) by apply B_fmt.
  assert (Sh : succ radix2 (FLT_exp emin prec) H = H + bpow radix2 e) by (rewrite succ_eq_pos by lra; rewrite Ulp; ring).
  pose proof (generic_format_succ radix2 (FLT_exp emin prec) H FH) as FsH.
  set (pH := pred radix2 (FLT_exp emin prec) H) in *.
  assert (Gp : bpow radix2 e / 2 <= H - pH <= bpow radix2 e).
  { destruct (fraction_zero h); [rewrite (Gz eq_refl) | rewrite (Gnz eq_refl)]; lra. }
  assert (FpH : fmtF pH) by (apply generic_format_pred; [exact _ | exact FH]).
  assert (SpH : succ radix2 (FLT_exp emin prec) pH = H) by (apply succ_pred; [exact _ | exact FH]).
  assert (UpH : ulp radix2 (FLT_exp emin prec) pH = H - pH).
  { pose proof (succ_eq_pos radix2 (FLT_exp emin prec) pH ltac:(lra)) as S. rewrite SpH in S. lra. }
  set (ppH := pred radix2 (FLT_exp emin prec) pH).
  assert (PH0 : 0 < pH) by lra.
  assert (Spp : ppH + ulp radix2 (FLT_exp emin prec) ppH = pH)
    by exact (pred_plus_ulp radix2 (FLT_exp emin prec) pH PH0 FpH).
  assert (Upp : ulp radix2 (FLT_exp emin prec) ppH <= ulp radix2 (FLT_exp emin prec) pH).
  { apply ulp_le_pos. all: try exact _.
    - apply pred_ge_0; [exact _ | lra | exact FpH].
    - apply pred_le_id. }
  assert (Upp' : / 2 ^ 53 <= ulp radix2 (FLT_exp emin prec) ppH).
  { pose proof (ulp_ge_0 radix2 (FLT_exp emin prec) ppH).
    destruct (ulp_range ppH ltac:(split; lra)) as [U _].
    change (bpow radix2 (-53)) with (bpow radix2 (- Z.of_nat 53)) in U. rewrite ExpAccurate.bpow_m in U. exact U. }
  (* the four cases *)
  pose proof (up_sign w Nw) as Sg. fold W in Sg.
  destruct (negb (Q128.neg w && negb (Q128.m w =? 0)%Z)); cbn [negb andb].
  - (* [w >= 0]: [h], or the number above it *)
    destruct (half_f (ulp_f h) e Fu Bu ltac:(lia)) as [Fg Bg].
    set (q := ExpAccurate.qf (fmul (ulp_f h) half)).
    assert (Nq : ExpAccurate.NZ q) by apply ExpAccurate.from_f64_nz.
    assert (Vq : Q128.qval q = bpow radix2 e / 2).
    { unfold q, ExpAccurate.qf. rewrite ExpAccurate.from_f64_b64 by exact Fg. rewrite <- E1. exact Bg. }
    pose proof (cmp_lt w q Nw Nq ltac:(rewrite Vq, Rabs_pos_eq; lra)) as C. fold W in C.
    rewrite Vq, (Rabs_pos_eq (bpow radix2 e / 2)), (Rabs_pos_eq W) in C by lra.
    assert (Up : bpow radix2 e / 2 <= W -> finite (b64_of_bits (bits_of_b64 h + 1)) /\
                   B (b64_of_bits (bits_of_b64 h + 1)) = rndF (H + W)).
    { intros L. destruct (bits_up h Fh) as [Fn Bn].
      { change (B h) with H. split; [apply Rle_trans with (bpow radix2 (-1)); [apply bpow_le; lia | change (bpow radix2 (-1)) with (/ 2); lra] | ].
        apply Rlt_le_trans with 2; [lra | ]. change 2 with (bpow radix2 1). apply bpow_le. lia. }
      change (FLT_exp (-1074) 53) with (FLT_exp emin prec) in Bn. fold H in Bn.
      split; [exact Fn | ]. rewrite Bn. apply Rle_antisym.
      - apply round_N_ge_midp; try exact _; [exact FsH | ].
        rewrite pred_succ by (exact _ || exact FH). rewrite Sh.
        pose proof (NoMid H FH ltac:(lra)) as NM. rewrite Sh in NM.
        destruct (Rle_lt_or_eq_dec _ _ L) as [L' | L']; [lra | exfalso; apply NM; lra].
      - apply round_le_generic; [exact _ | exact _ | exact FsH | ].
        rewrite Sh. apply Rabs_le_inv in Wb. lra. }
    destruct (Q128.cmp_abs w q) eqn:Cm.
    + apply Up. apply Rnot_lt_le. intros L. apply C in L. discriminate.
    + split; [exact Fh | ]. change (B h) with H. apply Rle_antisym.
      * apply round_ge_generic; [exact _ | exact _ | exact FH | lra].
      * apply round_N_le_midp; try exact _; [exact FH | ]. rewrite Sh. pose proof (proj1 C eq_refl). lra.
    + apply Up. apply Rnot_lt_le. intros L. apply C in L. discriminate.
  - (* [w < 0]: [h], or the number below it *)
    set (q := ExpAccurate.qf (fmul (if fraction_zero h then fmul (ulp_f h) half else ulp_f h) half)).
    assert (Q : ExpAccurate.NZ q /\ Q128.qval q = (H - pH) / 2).
    { split; [apply ExpAccurate.from_f64_nz | ]. unfold q.
      destruct (fraction_zero h).
      - destruct (half_f (ulp_f h) e Fu Bu ltac:(lia)) as [Fg Bg].
        destruct (half_f _ (e - 1) Fg Bg ltac:(lia)) as [Fg2 Bg2].
        unfold ExpAccurate.qf. rewrite ExpAccurate.from_f64_b64 by exact Fg2.
        now rewrite Bg2, (Gz eq_refl), E1, E2.
      - destruct (half_f (ulp_f h) e Fu Bu ltac:(lia)) as [Fg Bg].
        unfold ExpAccurate.qf. rewrite ExpAccurate.from_f64_b64 by exact Fg.
        rewrite Bg, (Gnz eq_refl), E1. reflexivity. }
    destruct Q as [Nq Vq].
    pose proof (cmp_lt w q Nw Nq ltac:(rewrite Vq, Rabs_pos_eq; lra)) as C. fold W in C.
    rewrite Vq, (Rabs_pos_eq ((H - pH) / 2)), (Rabs_left W) in C by lra.
    assert (Dn : (H - pH) / 2 <= - W -> finite (b64_of_bits (bits_of_b64 h - 1)) /\
                   B (b64_of_bits (bits_of_b64 h - 1)) = rndF (H + W)).
    { intros L. destruct (bits_down h Fh) as [Fn Bn].
      { change (B h) with H. apply Rle_trans with (bpow radix2 (-1)); [apply bpow_le; lia | change (bpow radix2 (-1)) with (/ 2); lra]. }
      change (FLT_exp (-1074) 53) with (FLT_exp emin prec) in Bn. fold H pH in Bn.
      split; [exact Fn | ]. rewrite Bn. apply Rle_antisym.
      - apply round_N_ge_midp; try exact _; [exact FpH | ]. fold ppH.
        apply Rabs_le_inv in Wb. lra.
      - apply round_N_le_midp; try exact _; [exact FpH | ]. rewrite SpH.
        pose proof (NoMid pH FpH ltac:(lra)) as NM. rewrite SpH in NM.
        destruct (Rle_lt_or_eq_dec _ _ L) as [L' | L']; [lra | exfalso; apply NM; lra]. }
    destruct (Q128.cmp_abs w q) eqn:Cm.
    + apply Dn. apply Rnot_lt_le. intros L. apply C in L. discriminate.
    + split; [exact Fh | ]. change (B h) with H. apply Rle_antisym.
      * apply round_N_ge_midp; try exact _; [exact FH | ]. fold pH. pose proof (proj1 C eq_refl). lra.
      * apply round_le_generic; [exact _ | exact _ | exact FH | lra].
    + apply Dn. apply Rnot_lt_le. intros L. apply C in L. discriminate.
Qed.
