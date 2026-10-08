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
