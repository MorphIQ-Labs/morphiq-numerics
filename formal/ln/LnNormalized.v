(** Reduced::of already chooses the reciprocal stage's fundamental interval.
    The normalized lane specialization therefore has no second exponent. *)
From Coq Require Import ZArith Lia List Bool.
From Flocq Require Import IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import IEEE64 Encodings.
From Q Require Import Q128Mul.
Require Import LnReduction Ln1pReduction Ln1pCheck Ln1pTables.
Open Scope Z_scope.

Lemma clear_low_52 bits :
  Z.land bits (Z.lnot (2^52-1)) = bits / 2^52 * 2^52.
Proof.
  change (2^52-1) with (Z.ones 52).
  rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

(** Independent closed check of every existing generated table word. The
    runtime's constant initializer also rejects an invalid future layout. *)
Definition packed_entry_ok (entry : Z * (Z * Z)) : bool :=
  let '(r, (th, _)) := entry in
  let packed := Z.lor th (Z.land (Z.shiftr r 43) 1023) in
  Z.eqb (Z.land packed (Z.lnot 1023)) th &&
  Z.eqb (Z.lor (1022 * 2^52) (Z.shiftl (Z.land packed 1023) 43)) r.

Theorem packed_tables_lossless :
  forallb packed_entry_ok (combine st_r_bits st_t_bits) = true.
Proof. vm_compute; reflexivity. Qed.

Definition normalized_bits (fraction : Z) :=
  if fraction / 2^45 <? 53 then 1023 * 2^52 + fraction
  else 1022 * 2^52 + fraction.

Lemma normalized_interval fraction : 0 <= fraction < 2^52 ->
  st_off <= normalized_bits fraction < st_off + 2^52.
Proof.
  intros H. unfold normalized_bits, st_off.
  pose proof (Z.mul_div_le fraction (2^45) ltac:(lia)).
  pose proof (Z.mul_succ_div_gt fraction (2^45) ltac:(lia)).
  destruct (Z.ltb_spec (fraction / 2^45) 53); lia.
Qed.

(** Fused lane normalization of a positive normal encoding. All operations
    here are integer operations on the encoding; subnormal scaling stays
    unchanged and its exponent correction is applied after this identity. *)
Definition normalized_exponent biased fraction :=
  if fraction / 2^45 <? 53 then biased - 1023 else biased - 1022.

Lemma normalized_decomposition biased fraction :
  1 <= biased <= 2046 -> 0 <= fraction < 2^52 ->
  let bits := biased * 2^52 + fraction in
  let e := normalized_exponent biased fraction in
  -1022 <= e <= 1024 /\
  bits - st_off = e * 2^52 + (normalized_bits fraction - st_off).
Proof.
  intros Hb Hf. cbv zeta. unfold normalized_exponent, normalized_bits.
  destruct (fraction / 2^45 <? 53); split; [lia | ring | lia | ring].
Qed.

Theorem fused_normalization biased fraction :
  1 <= biased <= 2046 -> 0 <= fraction < 2^52 ->
  let bits := biased * 2^52 + fraction in
  let u := rd_u bits in
  (bits - (u / 2^52) * 2^52) mod 2^64 = normalized_bits fraction /\
  ((u + 1024 * 2^52) mod 2^64) / 2^52 - 1024 =
    normalized_exponent biased fraction.
Proof.
  intros Hb Hf.
  pose proof (normalized_interval fraction Hf) as Hn.
  pose proof (normalized_decomposition biased fraction Hb Hf) as Hd.
  cbv zeta in *. destruct Hd as [He Hd].
  set (bits := biased * 2^52 + fraction) in *.
  set (e := normalized_exponent biased fraction) in *.
  set (r := normalized_bits fraction - st_off) in *.
  assert (Hr : 0 <= r < 2^52) by (unfold r; lia).
  unfold rd_u. change (bits - st_off) with (bits - st_off).
  destruct (Z_le_gt_dec 0 e) as [Pos | Neg].
  - rewrite (Z.mod_small (bits - st_off) (2^64)) by lia.
    assert (D : (bits - st_off) / 2^52 = e).
    { symmetry. apply Z.div_unique with r; [left; exact Hr | lia]. }
    rewrite D. split.
    + replace (bits - e * 2^52) with (normalized_bits fraction) by (unfold r in *; lia).
      apply Z.mod_small. unfold st_off in Hn; lia.
    + rewrite Z.mod_small by lia.
      replace (bits - st_off + 1024 * 2^52) with ((e + 1024) * 2^52 + r) by lia.
      rewrite Z.div_add_l by lia. rewrite Z.div_small by exact Hr. lia.
  - replace ((bits - st_off) mod 2^64) with (bits - st_off + 2^64).
    2: { apply Z.mod_unique with (-1); [left; lia | ring]. }
    assert (D : (bits - st_off + 2^64) / 2^52 = e + 4096).
    { symmetry. apply Z.div_unique with r; [left; exact Hr | lia]. }
    rewrite D. split.
    + replace (bits - (e + 4096) * 2^52) with (normalized_bits fraction - 2^64)
        by (unfold r in *; lia).
      symmetry. apply Z.mod_unique with (-1); [left; unfold st_off in Hn; lia | ring].
    + replace ((bits - st_off + 2^64 + 1024 * 2^52) mod 2^64)
        with (bits - st_off + 1024 * 2^52).
      2: { apply Z.mod_unique with 1; [left; lia | ring]. }
      replace (bits - st_off + 1024 * 2^52) with ((e + 1024) * 2^52 + r) by lia.
      rewrite Z.div_add_l by lia. rewrite Z.div_small by exact Hr. lia.
Qed.

Lemma interval_exponent_zero bits : st_off <= bits < st_off + 2^52 ->
  rd_e bits = 0 /\ rd_u bits < 2^52.
Proof.
  intros H. unfold rd_e, rd_u.
  rewrite Z.mod_small by (unfold st_off in *; lia).
  replace (bits - st_off <? 2^63) with true
    by (symmetry; apply Z.ltb_lt; unfold st_off in *; lia).
  split; [apply Z.div_small | ]; lia.
Qed.

Theorem reduced_stage_exponent_zero x :
  let '(_, _, y, _) := LnReduction.reduce x in
  rd_e (bits_of_b64 y) = 0 /\ rd_u (bits_of_b64 y) < 2^52.
Proof.
  unfold LnReduction.reduce.
  destruct (match Bcompare 53 1024 x LnReduction.c_min_pos with
    | Some Lt => (bits_of_b64 (fmul x LnReduction.c_two_54), 54)
    | _ => (bits_of_b64 x, 0)
    end) as [bits scaled].
  cbv zeta.
  set (fraction := Z.land bits (2^52-1)).
  assert (Hf : 0 <= fraction < 2^52).
  { unfold fraction. change (2^52-1) with (Z.ones 52).
    rewrite Z.land_ones by lia. apply Z.mod_pos_bound; lia. }
  rewrite Z.shiftr_div_pow2 by lia.
  assert (Iq : (Z.to_nat (fraction / 2^45) <? 53)%nat =
    (fraction / 2^45 <? 53)%Z).
  { destruct (Z.ltb_spec (fraction / 2^45) 53);
      [apply Nat.ltb_lt | apply Nat.ltb_ge];
      pose proof (Z.div_pos fraction (2^45) ltac:(lia) ltac:(lia)); lia. }
  rewrite Iq.
  pose proof (normalized_interval fraction Hf) as Bounds.
  unfold normalized_bits in Bounds.
  assert (Round : forall b, 0 <= b < 2^64 -> bits_of_b64 (b64_of_bits b) = b).
  { intros b Hb. apply bits_of_binary_float_of_bits, Hb. }
  destruct (fraction / 2^45 <? 53); cbv beta iota;
    rewrite Z.lor_comm, lor_disjoint_low by lia;
    rewrite Round by (unfold st_off in *; lia);
    apply interval_exponent_zero; lia.
Qed.

(** Scalar signed-shift spelling of the same fused exponent. *)
Theorem fused_signed_exponent biased fraction :
  1 <= biased <= 2046 -> 0 <= fraction < 2^52 ->
  rd_e (biased * 2^52 + fraction) = normalized_exponent biased fraction.
Proof.
  intros Hb Hf.
  pose proof (normalized_interval fraction Hf) as Hn.
  pose proof (normalized_decomposition biased fraction Hb Hf) as Hd.
  cbv zeta in Hd. destruct Hd as [He Hd].
  set (bits := biased * 2^52 + fraction) in *.
  set (r := normalized_bits fraction - st_off) in *.
  assert (Hr : 0 <= r < 2^52) by (unfold r; lia).
  assert (Hs : -2^63 < bits - st_off < 2^63)
    by (unfold bits, st_off; lia).
  unfold rd_e, rd_u.
  destruct (Z_le_gt_dec 0 (bits - st_off)) as [Hp | Hm].
  - rewrite Z.mod_small by lia.
    replace (bits - st_off <? 2^63) with true
      by (symmetry; apply Z.ltb_lt; lia).
    symmetry. apply Z.div_unique with r; [left; exact Hr | lia].
  - replace ((bits - st_off) mod 2^64) with (bits - st_off + 2^64).
    2: { apply Z.mod_unique with (-1); [left; lia | ring]. }
    replace (bits - st_off + 2^64 <? 2^63) with false
      by (symmetry; apply Z.ltb_ge; lia).
    replace (bits - st_off + 2^64 - 2^64) with (bits - st_off) by ring.
    symmetry. apply Z.div_unique with r; [left; exact Hr | lia].
Qed.

(** The flattened pair layout scales the same bounded cell index before
    extraction to scalar registers. Neither word can leave the table. *)
Theorem packed_pair_index i : 0 <= i < 512 ->
  0 <= 2*i < 1024 /\ 0 <= 2*i+1 < 1024 /\ (2*i)/2 = i.
Proof. intros Hi. repeat split; try lia. rewrite Z.mul_comm, Z.div_mul; lia. Qed.

Theorem positive_encoding_screen bits : 0 <= bits < 2^64 ->
  ((bits-1) mod 2^64 < 2047*2^52-1 <-> 0 < bits < 2047*2^52).
Proof.
  intros Hb. destruct (Z.eq_dec bits 0) as [-> | Hn].
  - replace ((0-1) mod 2^64) with (2^64-1).
    2: { apply Z.mod_unique with (-1); [left; lia | ring]. }
    split; lia.
  - rewrite Z.mod_small by lia. split; lia.
Qed.

(** The scalar reduction record retains the cell index before normalization.
    An exponent changes only multiples of 2^52, never these nine bits. *)
Lemma rd_i_low52 bits : rd_i bits =
 Z.to_nat (Z.shiftr ((bits-st_off) mod 2^52) 43).
Proof.
 unfold rd_i.
 replace 511 with (Z.shiftr (Z.ones 52) 43) by (vm_compute; reflexivity).
 rewrite <- Z.shiftr_land, Z.land_ones by lia. unfold rd_u.
 rewrite <- Znumtheory.Zmod_div_mod by (try lia; exists 4096; reflexivity).
 reflexivity.
Qed.

Lemma rd_i_periodic bits k : rd_i (bits+k*2^52) = rd_i bits.
Proof.
 rewrite !rd_i_low52. replace (bits+k*2^52-st_off) with ((bits-st_off)+k*2^52) by ring.
 rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma rd_i_wrap bits : rd_i (bits mod 2^64) = rd_i bits.
Proof.
 rewrite Z.mod_eq by lia.
 replace (bits-2^64*(bits/2^64)) with (bits+(-(bits/2^64)*4096)*2^52) by ring.
 apply rd_i_periodic.
Qed.

Theorem normalized_cell_index bits :
 rd_i ((bits-Z.land (rd_u bits) (Z.lnot (2^52-1))) mod 2^64) = rd_i bits.
Proof.
 rewrite rd_i_wrap, clear_low_52.
 replace (bits-rd_u bits/2^52*2^52) with (bits+(-(rd_u bits/2^52))*2^52) by ring.
 apply rd_i_periodic.
Qed.

Theorem positive_normal_encoding_screen bits : (0<=bits<2^64)%Z ->
 (((bits-2^52) mod 2^64 < 2046*2^52)%Z <-> (2^52<=bits<2047*2^52)%Z).
Proof.
 intros B. destruct (Z_lt_ge_dec bits (2^52)) as [Below|Above].
 - replace ((bits-2^52) mod 2^64)%Z with (bits-2^52+2^64)%Z.
   2: { apply Z.mod_unique with (-1)%Z; [left; lia|ring]. }
   split; lia.
 - rewrite Z.mod_small by lia. split; lia.
Qed.
