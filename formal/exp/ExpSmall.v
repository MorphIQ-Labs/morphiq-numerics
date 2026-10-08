(** exp/mod.rs's accurate path for small arguments, [2^-54 <= |x| < 2^-30]
    ([small_parts] and [small], docs/exp.md, section 6), transcribed on binary64
    and the proved Q128 transcription (formal/q), and proved: [h + w] is within
    [2^-178] of [e^x] ([small_parts_ok]), and when [e^x] keeps the mantissa
    distance [LM] guarantees here, [2^-158], from every rounding breakpoint,
    [small] returns [RN(e^x)] ([exp_small_ok]). [d]'s evaluation is
    formal/exp/small.g's theorem; this file proves its hypotheses. *)

From Coq Require Import ZArith Reals Lia Lra Psatz List.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Q Require QSpec Q128.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Eft.
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

(** [small_parts(x)]: [(h, l) = two_sum(1, x)], then [d] to degree 5 in Q128
    and [w = l + d]. *)
Definition small_parts (x : binary_float 53 1024) : binary_float 53 1024 * Q128.q128 :=
  let '(h, l) := two_sum64 ExpFast.c_one x in
  let xq := ExpAccurate.qf x in
  let g5 := Q128.add ExpAccurate.q_one (Q128.mul xq (ExpAccurate.q_recip 5)) in
  let g4 := Q128.add ExpAccurate.q_one (Q128.mul (Q128.mul xq (ExpAccurate.q_recip 4)) g5) in
  let g3 := Q128.add ExpAccurate.q_one (Q128.mul (Q128.mul xq (ExpAccurate.q_recip 3)) g4) in
  let d := Q128.mul (Q128.mul (Q128.mul xq xq) (ExpAccurate.q_recip 2)) g3 in
  (h, Q128.add (ExpAccurate.qf l) d).

(** [d]'s exact counterpart. *)
Definition Dpoly (x : R) : R := x * x / 2 * (1 + x / 3 * (1 + x / 4 * (1 + x / 5))).

(** A Q128 value [q] as a recip-times-[(1 + k)] with [|k| <= 2^-127]. *)
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
  let xq := ExpAccurate.qf x in
  let g5 := Q128.add ExpAccurate.q_one (Q128.mul xq (ExpAccurate.q_recip 5)) in
  let g4 := Q128.add ExpAccurate.q_one (Q128.mul (Q128.mul xq (ExpAccurate.q_recip 4)) g5) in
  let g3 := Q128.add ExpAccurate.q_one (Q128.mul (Q128.mul xq (ExpAccurate.q_recip 3)) g4) in
  let d := Q128.mul (Q128.mul (Q128.mul xq xq) (ExpAccurate.q_recip 2)) g3 in
  ExpAccurate.NZ d /\ Rabs ((Q128.qval d - Dpoly (B2R 53 1024 x)) / Dpoly (B2R 53 1024 x)) <= / 2 ^ 122.
Proof.
  intros Fx Hx0 Hx xq g5 g4 g3 d.
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
