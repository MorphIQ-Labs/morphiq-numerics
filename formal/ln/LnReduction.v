(** ln/mod.rs's reduction [Reduced::of], the double-word [z] of [ln_y_fast]
    and [Reduced::z_exact] (docs/ln.md, section 3), transcribed on binary64 and
    the proved Q128 transcription (formal/q), and proved: [x = 2^E·y] with [y]
    in table interval [i] ([reduce_ok]), [(z_hi, z_lo)] is [y·R[i] − 1] exactly
    as a double-word, at most [2^-7] and zero or at least [2^-63] ([z_ok]), and
    [z_exact] is the same value in Q128 ([z_exact_ok]). *)

From Coq Require Import ZArith Reals Lia Lra Psatz.
From Flocq Require Import Core Sterbenz IEEE754.Binary IEEE754.Bits.
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

(** * The reduced argument [z = y·R[i] − 1] *)

(** [|y·R[i] − 1| <= 2^-7], and [y·R[i] − 1] is on [2^-63]'s grid. *)
Lemma z_range y i : (i < 128)%nat -> ln_lo i <= B y < ln_hi i -> on_grid (-53) (B y) ->
  0 < B (ln_r i) /\ Rabs (B y * B (ln_r i) - 1) <= / 128 /\ on_grid (-63) (B y * B (ln_r i) - 1).
Proof.
  intros Hi Iy Gy. destruct (ln_r_table_ok i Hi) as [_ [Gr [[R1 R2] [Lo Hh]]]].
  split; [lra | ]. split.
  - apply Rabs_le. split; nra.
  - apply grid_minus; [exact (grid_mult _ _ _ _ Gy Gr) | ].
    exists (2 ^ 63)%Z. change (IZR (2 ^ 63)) with (bpow radix2 63). rewrite <- bpow_plus. reflexivity.
Qed.

(** [ln_y_fast]'s [z]: [(z_hi, z_lo)] is [y·R[i] − 1] exactly, a double-word
    with [|z_lo| <= 2^-53·|z_hi|], at most [2^-7], and zero or at least
    [2^-63] in magnitude. *)
Theorem z_ok y i : (i < 128)%nat -> finite y -> ln_lo i <= B y < ln_hi i -> on_grid (-53) (B y) ->
  let '(zh, zl) := reduce_z y (ln_r i) in
  finite zh /\ finite zl /\ B zh + B zl = B y * B (ln_r i) - 1 /\ B zh = rndF (B zh + B zl) /\
  Rabs (B zh + B zl) <= / 128 /\ Rabs (B zl) <= bpow radix2 (-53) * Rabs (B zh) /\
  ((B zh = 0 /\ B zl = 0) \/ bpow radix2 (-63) <= Rabs (B zh)).
Proof.
  intros Hi Fy Iy Gy.
  destruct (ln_r_table_ok i Hi) as [Fr [_ [[R1 R2] _]]].
  destruct (z_range y i Hi Iy Gy) as [Rp [Zb Zg]].
  destruct (ln_range i Hi) as [L1 [L2 _]].
  destruct c_one_ok as [F1 B1].
  set (r := ln_r i) in *.
  pose proof (Rabs_le_inv _ _ Zb) as Zb'.
  assert (Yr : 0.99 <= B y * B r <= 1.01) by lra.
  (* the product, exactly *)
  pose proof (two_prod_ieee 1 1 y r Fy Fr
                ltac:(change (bpow radix2 1) with 2; rewrite Rabs_pos_eq by lra; lra)
                ltac:(change (bpow radix2 1) with 2; rewrite Rabs_pos_eq by lra; lra)
                ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(right; rewrite Rabs_pos_eq by lra; apply Rle_trans with (bpow radix2 (-1));
                      [apply bpow_le; lia | change (bpow radix2 (-1)) with (/ 2); lra])) as TP.
  unfold reduce_z. destruct (two_prod64 y r) as [p q]. destruct TP as [Fp [Fq [Bp Bpq]]].
  (* p − 1, exactly by Sterbenz's lemma *)
  assert (P1 : / 2 <= B p <= 5 / 4).
  { rewrite Bp. split.
    - change (/ 2) with (bpow radix2 (-1)). apply round_ge_generic; [exact _ | exact _ | | change (bpow radix2 (-1)) with (/ 2); lra].
      apply generic_format_FLT_bpow; [reflexivity | unfold emin; lia].
    - apply round_le_generic; [exact _ | exact _ | | lra].
      apply generic_format_FLT. exists (Float radix2 5 (-2)); [unfold F2R; simpl; lra | simpl; lia | simpl; unfold emin; lia]. }
  assert (Fd : fmtF (B p - B c_one)).
  { apply sterbenz; try exact _. all: try apply B_fmt. rewrite B1; lra. }
  destruct (fsub_ok 1 0 p c_one Fp F1 ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)
              ltac:(unfold bnd; rewrite B1, Rmult_1_l; change (bpow radix2 0) with 1; apply Rabs_le; lra)) as [Fs Bs].
  rewrite round_generic in Bs by (exact _ || exact Fd). rewrite B1 in Bs.
  (* (z_hi, z_lo) = two_sum(p − 1, q) *)
  pose proof (two_sum_ieee (fsub p c_one) q Fs Fq) as TS.
  assert (Q : Rabs (B q) <= 1) by (apply Rabs_le; lra).
  specialize (TS ltac:(rewrite Bs; apply Rle_trans with 1; [apply Rabs_le; lra | change 1 with (bpow radix2 0); apply bpow_le; lia])
                 ltac:(apply Rle_trans with 1; [exact Q | change 1 with (bpow radix2 0); apply bpow_le; lia])).
  destruct (two_sum64 (fsub p c_one) q) as [zh zl]. destruct TS as [Fzh [Fzl [Bzh Bz]]].
  rewrite Bs in Bzh, Bz.
  assert (Ez : B zh + B zl = B y * B r - 1) by lra.
  rewrite Ez.
  replace (B p - 1 + B q) with (B y * B r - 1) in Bzh by lra.
  split; [exact Fzh | ]. split; [exact Fzl | ]. split; [reflexivity | ]. split; [exact Bzh | ]. split; [exact Zb | ].
  destruct (Req_dec (B y * B r - 1) 0) as [Z0 | Z1].
  - (* z = 0 *)
    rewrite Z0, round_0 in Bzh by exact _.
    assert (L0 : B zl = 0) by lra. rewrite Bzh, L0, Rabs_R0. split; [lra | left; split; reflexivity].
  - (* |z| >= 2^-63, so |z_hi| >= 2^-63 *)
    pose proof (grid_nonzero _ _ Zg Z1) as Gz.
    assert (H63 : bpow radix2 (-63) <= Rabs (B zh)).
    { rewrite Bzh. apply abs_round_ge_generic; [exact _ | exact _ | | exact Gz].
      apply generic_format_FLT_bpow; [reflexivity | unfold emin; lia]. }
    split; [ | right; exact H63].
    assert (El : B zl = - (rndF (B y * B r - 1) - (B y * B r - 1))) by lra.
    rewrite El, Rabs_Ropp.
    apply Rle_trans with (/ 2 * ulp radix2 (FLT_exp emin prec) (rndF (B y * B r - 1))); [apply error_le_half_ulp_round; exact _ | ].
    rewrite <- Bzh.
    assert (U : ulp radix2 (FLT_exp emin prec) (B zh) <= Rabs (B zh) * bpow radix2 (1 - 53)).
    { apply ulp_FLT_le. unfold emin, prec. apply Rle_trans with (2 := H63). apply bpow_le. lia. }
    replace (bpow radix2 (1 - 53)) with (2 * bpow radix2 (-53)) in U
      by (change 2 with (bpow radix2 1); rewrite <- bpow_plus; reflexivity).
    lra.
Qed.

(** [IZR (2^n)] is [2^n]. *)
Lemma IZR_pow2 n : (0 <= n)%Z -> IZR (2 ^ n) = bpow radix2 n.
Proof.
  intros H. destruct n as [ | p | p]; [reflexivity | | lia].
  change (2 ^ Zpos p)%Z with (Zpower radix2 (Zpos p)). apply IZR_Zpower. lia.
Qed.

(** [significand(v)] for a positive normal [v] below [2]. *)
Lemma significand_ok v : finite v -> / 2 <= B v <= 2 ->
  let '(m, e) := significand v in
  (2 ^ 52 <= m < 2 ^ 53)%Z /\ (-53 <= e <= -51)%Z /\ B v = IZR m * bpow radix2 e.
Proof.
  intros Fv [H1 H2].
  assert (N : bpow radix2 (-1022) <= B v)
    by (apply Rle_trans with (bpow radix2 (-1)); [apply bpow_le; lia | change (bpow radix2 (-1)) with (/ 2); lra]).
  destruct (fields v Fv N) as [mx [ex [Mx [Ex [V [Sh La]]]]]].
  unfold significand. rewrite Sh, La.
  rewrite lor_disjoint_low by lia. replace (mx - 2 ^ 52 + 1 * 2 ^ 52)%Z with mx by ring.
  replace (ex + 1075 - 1075)%Z with ex by ring.
  pose proof (bpow_gt_0 radix2 ex) as Pe.
  split; [exact Mx | ]. split; [ | exact V]. split.
  - cut (-1 < ex + 53)%Z; [lia | ]. apply (lt_bpow radix2).
    apply Rle_lt_trans with (B v); [change (bpow radix2 (-1)) with (/ 2); lra | ].
    rewrite V, bpow_plus, (Rmult_comm (bpow radix2 ex)). apply Rmult_lt_compat_r; [exact Pe | ].
    change (bpow radix2 53) with (IZR (2 ^ 53)). apply IZR_lt. lia.
  - cut (ex + 52 < 2)%Z; [lia | ]. apply (lt_bpow radix2).
    apply Rle_lt_trans with (B v).
    + rewrite V, bpow_plus, (Rmult_comm (bpow radix2 ex)). apply Rmult_le_compat_r; [apply bpow_ge_0 | ].
      change (bpow radix2 52) with (IZR (2 ^ 52)). apply IZR_le. lia.
    + change (bpow radix2 2) with 4. lra.
Qed.

(** [Reduced::z_exact]: [y·R[i] − 1] in Q128, exactly, with its significand
    normalized or zero. *)
Theorem z_exact_ok y i : (i < 128)%nat -> finite y -> ln_lo i <= B y < ln_hi i ->
  (Q128.m (z_exact y (ln_r i)) = 0%Z \/ QSpec.normalized 128 (Q128.m (z_exact y (ln_r i)))) /\
  Q128.qval (z_exact y (ln_r i)) = B y * B (ln_r i) - 1.
Proof.
  intros Hi Fy Iy. destruct (ln_r_table_ok i Hi) as [Fr [_ [[R1 R2] _]]].
  destruct (ln_range i Hi) as [L1 [L2 _]].
  pose proof (significand_ok y Fy ltac:(split; lra)) as Sy.
  pose proof (significand_ok (ln_r i) Fr ltac:(split; lra)) as Sr.
  unfold z_exact. destruct (significand y) as [my ey]. destruct (significand (ln_r i)) as [mr er].
  destruct Sy as [My [Ey Vy]]. destruct Sr as [Mr [Er Vr]].
  assert (P : (0 <= my * mr < 2 ^ 106)%Z).
  { split; [nia | ]. replace (2 ^ 106)%Z with (2 ^ 53 * 2 ^ 53)%Z by reflexivity.
    apply Z.mul_lt_mono_nonneg; lia. }
  rewrite Z.shiftl_1_l.
  assert (Yr : B y * B (ln_r i) = IZR (my * mr) * bpow radix2 (ey + er))
    by (rewrite Vy, Vr, mult_IZR, bpow_plus; ring).
  assert (One : IZR (2 ^ (- (ey + er))) * bpow radix2 (ey + er) = 1)
    by (rewrite IZR_pow2 by lia; rewrite <- bpow_plus; replace (- (ey + er) + (ey + er))%Z with 0%Z by ring; reflexivity).
  assert (Ow : (0 < 2 ^ (- (ey + er)) <= 2 ^ 106)%Z)
    by (split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_le_mono_r; lia]).
  destruct (Z.leb_spec (2 ^ (- (ey + er))) (my * mr)) as [Ge | Lt].
  - assert (W : (0 <= my * mr - 2 ^ (- (ey + er)) < Q128.W)%Z) by (unfold Q128.W; lia).
    split.
    + pose proof (Q128.new_ok false _ (ey + er) W) as No. pose proof (QSpec.norm_ok 128 ltac:(lia) _ (ey + er) W) as V.
      destruct (QSpec.norm 128 (my * mr - 2 ^ (- (ey + er))) (ey + er)) as [m' e']. injection No as N1 N2.
      destruct V as [[[_ Z] | Nm] _]; [left; rewrite N1; exact Z | right; rewrite N1; exact Nm].
    + rewrite Q128.new_val by exact W. unfold QSpec.val, F2R. cbn [Fnum Fexp].
      rewrite Yr, minus_IZR. lra.
  - assert (W : (0 <= 2 ^ (- (ey + er)) - my * mr < Q128.W)%Z) by (unfold Q128.W; lia).
    split.
    + pose proof (Q128.new_ok true _ (ey + er) W) as No. pose proof (QSpec.norm_ok 128 ltac:(lia) _ (ey + er) W) as V.
      destruct (QSpec.norm 128 (2 ^ (- (ey + er)) - my * mr) (ey + er)) as [m' e']. injection No as N1 N2.
      destruct V as [[[_ Z] | Nm] _]; [left; rewrite N1; exact Z | right; rewrite N1; exact Nm].
    + rewrite Q128.new_val by exact W. unfold QSpec.val, F2R. cbn [Fnum Fexp].
      rewrite Yr, opp_IZR, minus_IZR. lra.
Qed.
