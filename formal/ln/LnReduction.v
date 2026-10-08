(** ln/mod.rs's reduction [Reduced::of], the double-word [z] of [ln_y_fast]
    and [Reduced::z_exact] (docs/ln.md, section 3), transcribed on binary64 and
    the proved Q128 transcription (formal/q), and proved: [x = 2^E·y] with [y]
    in table interval [i] ([reduce_ok]), [(z_hi, z_lo)] is [y·R[i] − 1] exactly
    as a double-word, at most [2^-7] and zero or at least [2^-63] ([z_ok]), and
    [z_exact] is the same value in Q128 ([z_exact_ok]). *)

From Coq Require Import ZArith Reals Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Q Require QSpec Q128.
From Q Require Import Q128Mul.
From Binary64 Require Import Binary64Add Binary64Mul IEEE64 IEEE64Add IEEE64Mul IEEE64Eft Grid Encodings.
From Binary64 Require RoundingTest.
Require LnTables.
Import LnTables.

Open Scope R_scope.

(** * The transcription *)

Definition c_one : f64 := b64_of_bits 4607182418800017408.      (* 0x3ff0000000000000 *)
Definition c_two_54 : f64 := b64_of_bits 4850376798678024192.   (* 0x4350000000000000 *)
Definition c_min_pos : f64 := b64_of_bits 4503599627370496.     (* 0x0010000000000000, f64::MIN_POSITIVE *)

(** [Reduced::of(x)]: [(E, i, y, R[i])]. *)
Definition reduce (x : f64) : Z * nat * f64 * f64 :=
  let '(bits, scaled) :=
    match Bcompare 53 1024 x c_min_pos with
    | Some Lt => (bits_of_b64 (fmul x c_two_54), 54%Z)
    | _ => (bits_of_b64 x, 0%Z)
    end in
  let biased := Z.shiftr bits 52 in
  let fraction := Z.land bits (2 ^ 52 - 1) in
  let i := Z.to_nat (Z.shiftr fraction 45) in
  let '(y, e) :=
    if (i <? 53)%nat then (b64_of_bits (Z.lor (Z.shiftl 1023 52) fraction), (biased - 1023 - scaled)%Z)
    else (b64_of_bits (Z.lor (Z.shiftl 1022 52) fraction), (biased - 1022 - scaled)%Z) in
  (e, i, y, ln_r i).

(** [ln_y_fast]'s [z]: [(p, q) = two_prod(y, R[i])], then [DoubleWord::sum(p − 1, q)]. *)
Definition reduce_z (y r : f64) : f64 * f64 :=
  let '(p, q) := two_prod64 y r in two_sum64 (fsub p c_one) q.

(** [significand(v)]: [(m, e)] with [v = m·2^e], for a positive normal [v]. *)
Definition significand (v : f64) : Z * Z :=
  let bits := bits_of_b64 v in
  (Z.lor (Z.land bits (2 ^ 52 - 1)) (Z.shiftl 1 52), (Z.shiftr bits 52 - 1075)%Z).

(** [Reduced::z_exact]: [y·R[i] − 1] from the significands. *)
Definition z_exact (y r : f64) : Q128.q128 :=
  let '(my, ey) := significand y in
  let '(mr, er) := significand r in
  let product := (my * mr)%Z in
  let scale := (ey + er)%Z in
  let one := Z.shiftl 1 (- scale) in
  if (one <=? product)%Z then Q128.new false (product - one)%Z scale
  else Q128.new true (one - product)%Z scale.

(** * The fields of an encoding *)

(** A positive normal number's exponent and fraction fields. *)
Lemma fields x : finite x -> bpow radix2 (-1022) <= B x ->
  exists mx ex, (2 ^ 52 <= mx < 2 ^ 53)%Z /\ (-1074 <= ex <= 971)%Z /\
    B x = IZR mx * bpow radix2 ex /\
    Z.shiftr (bits_of_b64 x) 52 = (ex + 1075)%Z /\
    Z.land (bits_of_b64 x) (2 ^ 52 - 1) = (mx - 2 ^ 52)%Z.
Proof.
  intros Fx Hx. destruct (pos_normal x Fx Hx) as [mx [ex [_ [_ [Mx [Ex [V [_ [_ Bits]]]]]]]]].
  exists (Zpos mx), ex. split; [exact Mx | ]. split; [exact Ex | ]. split; [exact V | ].
  rewrite Bits, join_eq. split.
  - rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. ring.
  - change (2 ^ 52 - 1)%Z with (Z.ones 52). rewrite Z.land_ones by lia.
    rewrite Z.add_comm, Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

(** An encoding with biased exponent [b] and fraction [f]. *)
Lemma build b f : (1 <= b <= 2046)%Z -> (0 <= f < 2 ^ 52)%Z ->
  finite (b64_of_bits (Z.lor (Z.shiftl b 52) f)) /\
  B (b64_of_bits (Z.lor (Z.shiftl b 52) f)) = IZR (f + 2 ^ 52) * bpow radix2 (b - 1075).
Proof.
  intros Hb Hf. rewrite Z.lor_comm, lor_disjoint_low by lia.
  replace (f + b * 2 ^ 52)%Z with (b * 2 ^ 52 + f)%Z by ring. rewrite <- join_eq.
  exact (join_val f b Hf Hb).
Qed.

(** * The reduction *)

(** For a positive normal [v] and a scale [s]: the table index, [y] and [E]
    that [Reduced::of] computes from [v]'s encoding, with [v = 2^(E+s)·y]. *)
Lemma core v s : finite v -> bpow radix2 (-1022) <= B v ->
  let bits := bits_of_b64 v in
  let fraction := Z.land bits (2 ^ 52 - 1) in
  let i := Z.to_nat (Z.shiftr fraction 45) in
  let '(y, e) :=
    if (i <? 53)%nat then (b64_of_bits (Z.lor (Z.shiftl 1023 52) fraction), (Z.shiftr bits 52 - 1023 - s)%Z)
    else (b64_of_bits (Z.lor (Z.shiftl 1022 52) fraction), (Z.shiftr bits 52 - 1022 - s)%Z) in
  (i < 128)%nat /\ finite y /\ ln_lo i <= B y < ln_hi i /\ on_grid (-53) (B y) /\
  B v = bpow radix2 (e + s) * B y /\ (-1022 <= e + s <= 1024)%Z.
Proof.
  intros Fv Hv. destruct (fields v Fv Hv) as [mx [ex [Mx [Ex [V [Sh La]]]]]].
  cbv zeta. rewrite Sh, La.
  set (f := (mx - 2 ^ 52)%Z).
  rewrite Z.shiftr_div_pow2 by lia.
  set (q := (f / 2 ^ 45)%Z).
  assert (Q0 : (0 <= q < 128)%Z) by (unfold q, f; split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  assert (Q1 : (q * 2 ^ 45 <= f < (q + 1) * 2 ^ 45)%Z).
  { unfold q. pose proof (Z.mul_div_le f (2 ^ 45) ltac:(lia)). pose proof (Z.mul_succ_div_gt f (2 ^ 45) ltac:(lia)). lia. }
  assert (Iq : INR (Z.to_nat q) = IZR q) by (rewrite INR_IZR_INZ, Z2Nat.id by lia; reflexivity).
  assert (Iq' : INR (S (Z.to_nat q)) = IZR q + 1) by (rewrite S_INR, Iq; reflexivity).
  assert (Lt : (Z.to_nat q < 128)%nat) by lia.
  pose proof (IZR_le _ _ (proj1 Mx)) as Mx1. pose proof (IZR_lt _ _ (proj2 Mx)) as Mx2.
  pose proof (IZR_le _ _ (proj1 Q1)) as Q1a. pose proof (IZR_lt _ _ (proj2 Q1)) as Q1b.
  rewrite mult_IZR in Q1a, Q1b. rewrite plus_IZR in Q1b. unfold f in Q1a, Q1b. rewrite minus_IZR in Q1a, Q1b.
  change (IZR (2 ^ 45)) with 35184372088832 in Q1a, Q1b.
  change (IZR (2 ^ 52)) with 4503599627370496 in Q1a, Q1b, Mx1.
  change (IZR (2 ^ 53)) with 9007199254740992 in Mx2.
  unfold ln_lo, ln_hi. rewrite Iq, Iq'.
  destruct (Nat.ltb_spec (Z.to_nat q) 53) as [Small | Big].
  - cbv beta iota. destruct (build 1023 f ltac:(lia) ltac:(unfold f; lia)) as [Fy By].
    replace (f + 2 ^ 52)%Z with mx in By by (unfold f; ring).
    change (bpow radix2 (1023 - 1075)) with (/ 4503599627370496) in By.
    split; [exact Lt | ]. split; [exact Fy | ]. rewrite By.
    split; [split; lra | ].
    split; [exists (mx * 2)%Z; rewrite mult_IZR; change (bpow radix2 (-53)) with (/ 9007199254740992); lra | ].
    split.
    + replace (ex + 1075 - 1023 - s + s)%Z with (ex + 52)%Z by ring. rewrite V, bpow_plus.
      change (bpow radix2 52) with 4503599627370496. field.
    + lia.
  - cbv beta iota. destruct (build 1022 f ltac:(lia) ltac:(unfold f; lia)) as [Fy By].
    replace (f + 2 ^ 52)%Z with mx in By by (unfold f; ring).
    change (bpow radix2 (1022 - 1075)) with (/ 9007199254740992) in By.
    assert (Q53 : (53 <= q)%Z) by lia. apply IZR_le in Q53.
    split; [exact Lt | ]. split; [exact Fy | ]. rewrite By.
    split; [split; lra | ].
    split; [exists mx; change (bpow radix2 (-53)) with (/ 9007199254740992); lra | ].
    split.
    + replace (ex + 1075 - 1022 - s + s)%Z with (ex + 53)%Z by ring. rewrite V, bpow_plus.
      change (bpow radix2 53) with 9007199254740992. field.
    + lia.
Qed.

(** The table intervals lie in [[0.70703125, 1.4140625]]. *)
Lemma ln_range i : (i < 128)%nat -> 0.70703125 <= ln_lo i /\ ln_hi i <= 1.4140625 /\ ln_lo i < ln_hi i.
Proof.
  intros H. unfold ln_lo, ln_hi. rewrite S_INR.
  assert (I0 : 0 <= INR i) by apply pos_INR.
  assert (I1 : INR i <= 127) by (replace 127 with (INR 127) by (rewrite INR_IZR_INZ; reflexivity); apply le_INR; lia).
  destruct (Nat.ltb_spec i 53) as [S | S].
  - assert (INR i <= 52) by (replace 52 with (INR 52) by (rewrite INR_IZR_INZ; reflexivity); apply le_INR; lia). lra.
  - assert (53 <= INR i) by (replace 53 with (INR 53) by (rewrite INR_IZR_INZ; reflexivity); apply le_INR; lia). lra.
Qed.

(** A power of two by its encoding. *)
Lemma pow2_bits b : (1 <= b <= 2046)%Z ->
  finite (b64_of_bits (Z.lor (Z.shiftl b 52) 0)) /\ B (b64_of_bits (Z.lor (Z.shiftl b 52) 0)) = bpow radix2 (b - 1023).
Proof.
  intros Hb. destruct (build b 0 Hb ltac:(lia)) as [F V]. split; [exact F | ]. rewrite V.
  change (IZR (0 + 2 ^ 52)) with (bpow radix2 52). rewrite <- bpow_plus. f_equal. ring.
Qed.

Lemma c_one_ok : finite c_one /\ B c_one = 1.
Proof. exact (pow2_bits 1023 ltac:(lia)). Qed.

Lemma c_two_54_ok : finite c_two_54 /\ B c_two_54 = bpow radix2 54.
Proof. exact (pow2_bits 1077 ltac:(lia)). Qed.

Lemma c_min_pos_ok : finite c_min_pos /\ B c_min_pos = bpow radix2 (-1022).
Proof. exact (pow2_bits 1 ltac:(lia)). Qed.

(** [Reduced::of]: [x = 2^E·y] with [y] in table interval [i], for every
    finite [x > 0]. *)
Theorem reduce_ok x : finite x -> 0 < B x ->
  let '(e, i, y, r) := reduce x in
  (i < 128)%nat /\ r = ln_r i /\ finite y /\ ln_lo i <= B y < ln_hi i /\ on_grid (-53) (B y) /\
  B x = bpow radix2 e * B y /\ (-1074 <= e <= 1024)%Z.
Proof.
  intros Fx Px. destruct c_min_pos_ok as [Fm Bm]. destruct c_two_54_ok as [F54 B54].
  unfold reduce. rewrite (Bcompare_correct 53 1024 x c_min_pos Fx Fm), Bm.
  destruct (Rcompare_spec (B x) (bpow radix2 (-1022))) as [L | E | G].
  - (* subnormal: scaled by 2^54, exactly *)
    assert (Gx : on_grid (-1074) (B x)).
    { apply (grid_le (cexp radix2 (FLT_exp emin prec) (B x))).
      - unfold cexp, FLT_exp, emin. lia.
      - apply grid_fmt. apply B_fmt. }
    destruct Gx as [m Hm].
    pose proof (bpow_gt_0 radix2 (-1074)) as P1074.
    assert (M1 : (1 <= m)%Z).
    { cut (0 < m)%Z; [lia | ]. apply lt_IZR. apply Rmult_lt_reg_r with (bpow radix2 (-1074)); [exact P1074 | ].
      rewrite <- Hm, Rmult_0_l. exact Px. }
    assert (M2 : (m < 2 ^ 52)%Z).
    { apply lt_IZR. apply Rmult_lt_reg_r with (bpow radix2 (-1074)); [exact P1074 | ].
      rewrite <- Hm. change (IZR (2 ^ 52)) with (bpow radix2 52). rewrite <- bpow_plus. exact L. }
    assert (Fmt : generic_format radix2 (FLT_exp (-1074) 53) (B x * B c_two_54)).
    { rewrite B54, Hm, Rmult_assoc, <- bpow_plus. apply generic_format_FLT.
      exists (Float radix2 m (-1074 + 54)); [reflexivity | simpl; lia | simpl; lia]. }
    assert (Ov : Rabs (B x * B c_two_54) < bpow radix2 1024).
    { rewrite B54, Rabs_pos_eq by (pose proof (bpow_gt_0 radix2 54); nra).
      apply Rlt_trans with (bpow radix2 (-1022) * bpow radix2 54); [apply Rmult_lt_compat_r; [apply bpow_gt_0 | exact L] | ].
      rewrite <- bpow_plus. apply bpow_lt. lia. }
    destruct (RoundingTest.fmul_exact x c_two_54 Fx F54 Fmt Ov) as [Fv Bv].
    assert (Hv : bpow radix2 (-1022) <= B (fmul x c_two_54)).
    { rewrite Bv, B54, Hm, Rmult_assoc, <- bpow_plus.
      apply Rle_trans with (1 * bpow radix2 (-1074 + 54)).
      - rewrite Rmult_1_l. apply bpow_le. lia.
      - apply Rmult_le_compat_r; [apply bpow_ge_0 | apply IZR_le; exact M1]. }
    pose proof (core (fmul x c_two_54) 54 Fv Hv) as C.
    cbv beta iota zeta in C |- *.
    match goal with |- context [if ?c then ?a else ?b] => destruct (if c then a else b) as [y e] end.
    destruct C as [Li [Fy [[Iy1 Iy2] [Gy [Ev Er]]]]].
    destruct (ln_range _ Li) as [R1 [R2 _]].
    assert (Ex : B x = bpow radix2 e * B y).
    { apply Rmult_eq_reg_r with (bpow radix2 54); [ | apply Rgt_not_eq, bpow_gt_0].
      rewrite <- B54, <- Bv, Ev, bpow_plus, B54. ring. }
    repeat split; try reflexivity; try assumption; try lia.
    (* 2^E·y >= 2^-1074 with y < 2, so E >= -1074 *)
    cut (-1075 < e)%Z; [lia | ]. apply (lt_bpow radix2).
    assert (X : bpow radix2 (-1074) <= B x).
    { rewrite Hm. rewrite <- (Rmult_1_l (bpow radix2 (-1074))) at 1. apply Rmult_le_compat_r; [lra | apply IZR_le; lia]. }
    assert (B2 : bpow radix2 (-1074) = 2 * bpow radix2 (-1075)).
    { change 2 with (bpow radix2 1). rewrite <- bpow_plus. reflexivity. }
    pose proof (bpow_gt_0 radix2 e). pose proof (bpow_gt_0 radix2 (-1075)). nra.
  - (* normal *)
    pose proof (core x 0 Fx (Req_le _ _ (eq_sym E))) as C.
    cbv beta iota zeta in C |- *.
    match goal with |- context [if ?c then ?a else ?b] => destruct (if c then a else b) as [y e] end.
    destruct C as [Li [Fy [[Iy1 Iy2] [Gy [Ev Er]]]]]. rewrite Z.add_0_r in Ev, Er.
    repeat split; try reflexivity; try assumption; lia.
  - pose proof (core x 0 Fx (Rlt_le _ _ G)) as C.
    cbv beta iota zeta in C |- *.
    match goal with |- context [if ?c then ?a else ?b] => destruct (if c then a else b) as [y e] end.
    destruct C as [Li [Fy [[Iy1 Iy2] [Gy [Ev Er]]]]]. rewrite Z.add_0_r in Ev, Er.
    repeat split; try reflexivity; try assumption; lia.
Qed.
