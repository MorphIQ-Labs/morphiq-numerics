(** Q128::mul's significand product, transcribed: four 64-bit partial
    products, the middle column and the carry into the high half. *)

From Coq Require Import Bool ZArith Lia Psatz.
Open Scope Z_scope.

Definition B := 2 ^ 64.

Definition prod128 (a b : Z) : Z * Z :=
  let a1 := Z.shiftr a 64 in let a0 := Z.land a (B - 1) in
  let b1 := Z.shiftr b 64 in let b0 := Z.land b (B - 1) in
  let p00 := a0 * b0 in let p01 := a0 * b1 in
  let p10 := a1 * b0 in let p11 := a1 * b1 in
  let mid := Z.shiftr p00 64 + Z.land p01 (B - 1) + Z.land p10 (B - 1) in
  let lo := (Z.lor (Z.land p00 (B - 1)) (Z.shiftl mid 64)) mod 2 ^ 128 in
  let hi := (p11 + Z.shiftr p01 64 + Z.shiftr p10 64 + Z.shiftr mid 64) mod 2 ^ 128 in
  (hi, lo).

Lemma land_mask x : 0 <= x -> Z.land x (B - 1) = x mod B.
Proof. intros. unfold B. change (2 ^ 64 - 1) with (Z.ones 64). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma lor_disjoint_low a h k : 0 <= a < 2 ^ k -> 0 <= h -> 0 <= k ->
  Z.lor a (Z.shiftl h k) = a + h * 2 ^ k.
Proof.
  intros Ha Hh Hk. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite <- Z.lxor_lor.
  - rewrite <- Z.add_nocarry_lxor; [reflexivity | ].
    apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z_lt_le_dec i k) as [L | L].
    + rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
    + rewrite <- (Z.mod_small a (2 ^ k)) by lia. rewrite Z.mod_pow2_bits_high by lia. reflexivity.
  - apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z_lt_le_dec i k) as [L | L].
    + rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
    + rewrite <- (Z.mod_small a (2 ^ k)) by lia. rewrite Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

(** [hi·2^128 + lo] is the exact product of two 128-bit significands. *)
Theorem prod128_ok a b : 0 <= a < 2 ^ 128 -> 0 <= b < 2 ^ 128 ->
  let '(hi, lo) := prod128 a b in hi * 2 ^ 128 + lo = a * b /\ 0 <= lo < 2 ^ 128.
Proof.
  intros Ha Hb. unfold prod128.
  rewrite !Z.shiftr_div_pow2 by lia. rewrite !land_mask by (try lia; apply Z.mul_nonneg_nonneg; lia).
  fold B.
  assert (EB : 2 ^ 128 = B * B) by (unfold B; reflexivity).
  set (a1 := a / B). set (a0 := a mod B). set (b1 := b / B). set (b0 := b mod B).
  assert (A : a = B * a1 + a0) by (apply Z.div_mod; unfold B; lia).
  assert (Bd : b = B * b1 + b0) by (apply Z.div_mod; unfold B; lia).
  assert (A0 : 0 <= a0 < B) by (apply Z.mod_pos_bound; unfold B; lia).
  assert (B0 : 0 <= b0 < B) by (apply Z.mod_pos_bound; unfold B; lia).
  assert (A1 : 0 <= a1 < B) by (split; [apply Z.div_pos; unfold B; lia | apply Z.div_lt_upper_bound; unfold B in *; lia]).
  assert (B1 : 0 <= b1 < B) by (split; [apply Z.div_pos; unfold B; lia | apply Z.div_lt_upper_bound; unfold B in *; lia]).
  assert (PB : 0 < B) by (unfold B; lia).
  (* Each partial product splits into its high and low 64 bits. *)
  assert (Split : forall x, 0 <= x -> x = B * (x / B) + x mod B /\ 0 <= x mod B < B /\ 0 <= x / B)
    by (intros x Hx; repeat split; [apply Z.div_mod; lia | apply Z.mod_pos_bound; lia | apply Z.mod_pos_bound; lia | apply Z.div_pos; lia]).
  set (p00 := a0 * b0). set (p01 := a0 * b1). set (p10 := a1 * b0). set (p11 := a1 * b1).
  assert (P00 : 0 <= p00 < B * B) by (unfold p00; nia).
  assert (P01 : 0 <= p01 < B * B) by (unfold p01; nia).
  assert (P10 : 0 <= p10 < B * B) by (unfold p10; nia).
  assert (P11 : 0 <= p11 < B * B) by (unfold p11; nia).
  destruct (Split p00 ltac:(lia)) as [S00 [M00 D00]].
  destruct (Split p01 ltac:(lia)) as [S01 [M01 D01]].
  destruct (Split p10 ltac:(lia)) as [S10 [M10 D10]].
  assert (Q00 : p00 / B < B) by (apply Z.div_lt_upper_bound; lia).
  assert (Q01 : p01 / B < B) by (apply Z.div_lt_upper_bound; lia).
  assert (Q10 : p10 / B < B) by (apply Z.div_lt_upper_bound; lia).
  set (mid := p00 / B + p01 mod B + p10 mod B).
  assert (Mid : 0 <= mid < 3 * B) by (unfold mid; lia).
  destruct (Split mid ltac:(lia)) as [Sm [Mm Dm]].
  try rewrite !Z.shiftr_div_pow2 by lia. try rewrite !land_mask by lia. fold B.
  fold mid. rewrite (lor_disjoint_low (p00 mod B) mid 64) by (unfold B in *; lia).
  fold B.
  (* lo, before reduction: p00 mod B + mid·B, below B·B + 3B·B; reduced
     modulo B·B it is p00 mod B + (mid mod B)·B. *)
  assert (Lo : (p00 mod B + mid * B) mod 2 ^ 128 = p00 mod B + mid mod B * B).
  { rewrite EB. rewrite Sm at 1.
    replace (p00 mod B + (B * (mid / B) + mid mod B) * B)
      with ((p00 mod B + mid mod B * B) + (mid / B) * (B * B)) by ring.
    rewrite Z.mod_add by lia. apply Z.mod_small. unfold B in *. lia. }
  rewrite Lo.
  set (hi0 := p11 + p01 / B + p10 / B + mid / B).
  assert (AB : a * b = p11 * (B * B) + (p01 + p10) * B + p00)
    by (rewrite A, Bd; unfold p00, p01, p10, p11; ring).
  assert (Total : hi0 * (B * B) + (p00 mod B + mid mod B * B) = a * b).
  { rewrite AB. unfold hi0. unfold mid in Sm |- *. unfold B in *. lia. }
  assert (ABb : a * b < B * B * (B * B)).
  { rewrite <- EB. apply Z.mul_lt_mono_nonneg; lia. }
  assert (Hi : 0 <= hi0 < B * B).
  { split; [unfold hi0; pose proof (Z.div_pos mid B); lia | ]. unfold B in *. lia. }
  rewrite EB, Z.mod_small by lia. split; [lia | ]. unfold B in *. lia.
Qed.
