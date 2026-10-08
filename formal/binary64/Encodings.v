(** A binary64 encoding's value, for constants given by their bits: when the
    encoding decodes to a finite [±m·2^(−k)] (a computation, closed by
    [eq_refl]), its value is that rational, which CoqInterval can read. *)

From Coq Require Import Reals ZArith Lia Lra.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import IEEE64 Grid.

Open Scope R_scope.

Lemma bits_val (n : Z) (s : bool) (m : positive) (k : nat) :
  binary_float_of_bits_aux 52 11 n = F754_finite s m (- Z.of_nat k) ->
  B (b64_of_bits n) = IZR (cond_Zopp s (Zpos m)) / 2 ^ k.
Proof.
  intros D. unfold b64_of_bits, binary_float_of_bits. rewrite B2R_FF2B, D.
  unfold FF2R, F2R. cbn [Fnum Fexp]. rewrite bpow_opp, bpow_powerRZ, <- pow_powerRZ.
  reflexivity.
Qed.

Lemma bits_zero (n : Z) (s : bool) :
  binary_float_of_bits_aux 52 11 n = F754_zero s -> B (b64_of_bits n) = 0.
Proof.
  intros D. unfold b64_of_bits, binary_float_of_bits. rewrite B2R_FF2B, D. reflexivity.
Qed.

Lemma bits_finite (n : Z) (s : bool) (m : positive) (e : Z) :
  binary_float_of_bits_aux 52 11 n = F754_finite s m e -> finite (b64_of_bits n).
Proof.
  intros D. unfold b64_of_bits, binary_float_of_bits. rewrite is_finite_FF2B, D. reflexivity.
Qed.

(** Such a value is a multiple of [2^(−K)] for any [K >= k]. *)
Lemma val_grid (m : Z) (k K : nat) : (k <= K)%nat -> on_grid (- Z.of_nat K) (IZR m / 2 ^ k).
Proof.
  intros H. exists (m * 2 ^ Z.of_nat (K - k))%Z.
  rewrite mult_IZR, bpow_opp, bpow_powerRZ, <- pow_powerRZ.
  rewrite <- ?pow_IZR. change (IZR radix2) with 2.
  replace (2 ^ K) with (2 ^ (K - k) * 2 ^ k) by (rewrite <- pow_add; f_equal; lia).
  field. split; apply pow_nonzero; lra.
Qed.

Lemma bits_finite_zero (n : Z) (s : bool) :
  binary_float_of_bits_aux 52 11 n = F754_zero s -> finite (b64_of_bits n).
Proof.
  intros D. unfold b64_of_bits, binary_float_of_bits. rewrite is_finite_FF2B, D. reflexivity.
Qed.

(** * Stepping the encoding

    For a positive normal [h], [h.to_bits() + 1] encodes the next binary64
    number up and [h.to_bits() - 1] the next one down: the significand field
    counts within a binade and carries into the exponent field across one. *)

Local Instance prec_53 : Prec_gt_0 53 := eq_refl.

Lemma join_eq m e : join_bits 52 11 false m e = (e * 2 ^ 52 + m)%Z.
Proof. unfold join_bits. rewrite Z.shiftl_mul_pow2 by lia. reflexivity. Qed.

(** A normal encoding's value. *)
Lemma join_val m e : (0 <= m < 2 ^ 52)%Z -> (1 <= e <= 2046)%Z ->
  finite (b64_of_bits (join_bits 52 11 false m e)) /\
  B (b64_of_bits (join_bits 52 11 false m e)) = IZR (m + 2 ^ 52) * bpow radix2 (e - 1075).
Proof.
  intros Hm He. unfold b64_of_bits, binary_float_of_bits. rewrite B2R_FF2B, is_finite_FF2B.
  unfold binary_float_of_bits_aux. rewrite split_join_bits by (change (Zpower 2 52) with (2 ^ 52)%Z; change (Zpower 2 11) with 2048%Z; lia).
  replace (Zeq_bool e 0) with false by (symmetry; apply Zeq_bool_false; lia).
  replace (Zeq_bool e (Zpower 2 11 - 1)) with false by (symmetry; apply Zeq_bool_false; change (Zpower 2 11) with 2048%Z; lia).
  change (Zpower 2 52) with (2 ^ 52)%Z.
  destruct (m + 2 ^ 52)%Z as [ | p | p] eqn:Ep; [lia | | lia].
  split; [reflexivity | ]. unfold FF2R, F2R. cbn [Fnum Fexp cond_Zopp]. rewrite <- Ep.
  f_equal. f_equal. change (2 ^ (11 - 1))%Z with 1024%Z. ring.
Qed.

(** A positive normal number's fields, and its encoding. *)
Lemma pos_normal h : finite h -> bpow radix2 (-1022) <= B h ->
  exists mx ex, (2 ^ 52 <= Zpos mx < 2 ^ 53)%Z /\ (-1074 <= ex <= 971)%Z /\
    B h = IZR (Zpos mx) * bpow radix2 ex /\
    bits_of_b64 h = join_bits 52 11 false (Zpos mx - 2 ^ 52) (ex + 1075).
Proof.
  intros Fh Hh. destruct h as [s | s | s pl Hpl | s mx ex Hx]; try discriminate.
  { exfalso. simpl in Hh. pose proof (bpow_gt_0 radix2 (-1022)). lra. }
  pose proof Hx as Hb. unfold bounded in Hb. apply andb_prop in Hb as [Hc He]. apply Zle_bool_imp_le in He.
  assert (Pos : 0 < B (B754_finite 53 1024 s mx ex Hx)) by (pose proof (bpow_gt_0 radix2 (-1022)); lra).
  destruct s.
  { exfalso. simpl in Pos. pose proof (F2R_lt_0 radix2 (Float radix2 (Zneg mx) ex) ltac:(simpl; lia)). lra. }
  assert (V : B (B754_finite 53 1024 false mx ex Hx) = IZR (Zpos mx) * bpow radix2 ex) by reflexivity.
  pose proof (canonical_canonical_mantissa 53 1024 false mx ex Hc) as Can.
  assert (Ulp : ulp radix2 (FLT_exp (-1074) 53) (B (B754_finite 53 1024 false mx ex Hx)) = bpow radix2 ex).
  { rewrite ulp_neq_0 by lra. unfold canonical in Can. simpl in Can. f_equal. symmetry. exact Can. }
  set (v := B (B754_finite 53 1024 false mx ex Hx)) in *.
  assert (U1 : v * bpow radix2 (-53) < bpow radix2 ex).
  { rewrite <- Ulp. pose proof (ulp_FLT_gt radix2 (-1074) 53 v) as U. rewrite (Rabs_pos_eq v) in U by lra. exact U. }
  assert (U2 : bpow radix2 ex <= v * bpow radix2 (-52)).
  { rewrite <- Ulp. replace (-52)%Z with (1 - 53)%Z by reflexivity. rewrite <- (Rabs_pos_eq v) at 2 by lra.
    apply ulp_FLT_le. rewrite Rabs_pos_eq by lra. exact Hh. }
  pose proof (bpow_gt_0 radix2 ex) as Pe.
  assert (Mx : (2 ^ 52 <= Zpos mx < 2 ^ 53)%Z).
  { split.
    - apply le_IZR. apply Rmult_le_reg_r with (bpow radix2 ex); [exact Pe | ].
      rewrite <- V. replace (IZR (2 ^ 52)) with (bpow radix2 52) by reflexivity.
      apply Rmult_le_reg_r with (bpow radix2 (-52)); [apply bpow_gt_0 | ].
      replace (bpow radix2 52 * bpow radix2 ex * bpow radix2 (-52)) with (bpow radix2 ex)
        by (rewrite Rmult_comm, <- Rmult_assoc, <- bpow_plus; simpl; ring).
      exact U2.
    - apply lt_IZR. apply Rmult_lt_reg_r with (bpow radix2 ex); [exact Pe | ].
      rewrite <- V. replace (IZR (2 ^ 53)) with (bpow radix2 53) by reflexivity.
      apply Rmult_lt_reg_r with (bpow radix2 (-53)); [apply bpow_gt_0 | ].
      replace (bpow radix2 53 * bpow radix2 ex * bpow radix2 (-53)) with (bpow radix2 ex)
        by (rewrite Rmult_comm, <- Rmult_assoc, <- bpow_plus; simpl; ring).
      exact U1. }
  assert (Ex : (-1074 <= ex)%Z).
  { cut (-1075 < ex)%Z; [lia | ]. apply (lt_bpow radix2). apply Rle_lt_trans with (2 := U1).
    replace (-1075)%Z with (-1022 + -53)%Z by reflexivity. rewrite bpow_plus.
    apply Rmult_le_compat_r; [apply bpow_ge_0 | exact Hh]. }
  exists mx, ex. split; [exact Mx | ]. split; [lia | ]. split; [exact V | ].
  unfold bits_of_b64, bits_of_binary_float. change (Zpower 2 52) with (2 ^ 52)%Z.
  replace (Zle_bool 0 (Zpos mx - 2 ^ 52)) with true by (symmetry; apply Zle_imp_le_bool; lia).
  f_equal. replace (3 - 2 ^ (11 - 1) - (52 + 1))%Z with (-1074)%Z by reflexivity. ring.
Qed.

(** [h.to_bits() + 1]: the next number up. *)
Theorem bits_up h : finite h -> bpow radix2 (-1022) <= B h < bpow radix2 1023 ->
  finite (b64_of_bits (bits_of_b64 h + 1)) /\
  B (b64_of_bits (bits_of_b64 h + 1)) = succ radix2 (FLT_exp (-1074) 53) (B h).
Proof.
  intros Fh [H1 H2]. destruct (pos_normal h Fh H1) as [mx [ex [Mx [Ex [V Bits]]]]].
  assert (Pe : 0 < bpow radix2 ex) by apply bpow_gt_0.
  assert (Pos : 0 < B h) by (pose proof (bpow_gt_0 radix2 (-1022)); lra).
  (* succ h = h + ulp h = (mx + 1)·2^ex *)
  assert (S : succ radix2 (FLT_exp (-1074) 53) (B h) = IZR (Zpos mx + 1) * bpow radix2 ex).
  { rewrite succ_eq_pos by lra. rewrite ulp_neq_0 by lra. unfold cexp.
    assert (M : mag radix2 (B h) = (ex + 53)%Z :> Z).
    { apply mag_unique. rewrite Rabs_pos_eq by lra. rewrite V.
      replace (ex + 53 - 1)%Z with (52 + ex)%Z by ring. replace (ex + 53)%Z with (53 + ex)%Z by ring.
      rewrite !bpow_plus.
      split; [apply Rmult_le_compat_r; [lra | ] | apply Rmult_lt_compat_r; [lra | ]].
      - replace (bpow radix2 52) with (IZR (2 ^ 52)) by reflexivity. apply IZR_le. lia.
      - replace (bpow radix2 53) with (IZR (2 ^ 53)) by reflexivity. apply IZR_lt. lia. }
    rewrite M. unfold FLT_exp. replace (Z.max (ex + 53 - 53) (-1074)) with ex by lia.
    rewrite V, plus_IZR. ring. }
  rewrite Bits, join_eq, S.
  destruct (Z.eq_dec (Zpos mx) (2 ^ 53 - 1)) as [Top | Mid].
  - (* the significand field carries into the exponent field *)
    assert (Ex' : (ex <= 970)%Z).
    { cut (52 + ex < 1023)%Z; [lia | ]. apply (lt_bpow radix2). apply Rle_lt_trans with (2 := H2).
      rewrite V, bpow_plus. apply Rmult_le_compat_r; [lra | ].
      replace (bpow radix2 52) with (IZR (2 ^ 52)) by reflexivity. apply IZR_le. lia. }
    replace ((ex + 1075) * 2 ^ 52 + (Zpos mx - 2 ^ 52) + 1)%Z with ((ex + 1076) * 2 ^ 52 + 0)%Z by lia.
    rewrite <- join_eq. destruct (join_val 0 (ex + 1076) ltac:(lia) ltac:(lia)) as [F E].
    split; [exact F | ]. rewrite E, Top.
    replace (ex + 1076 - 1075)%Z with (ex + 1)%Z by ring. rewrite bpow_plus.
    replace (2 ^ 53 - 1 + 1)%Z with (2 * 2 ^ 52)%Z by reflexivity. rewrite mult_IZR.
    rewrite Z.add_0_l. change (bpow radix2 1) with 2. ring.
  - replace ((ex + 1075) * 2 ^ 52 + (Zpos mx - 2 ^ 52) + 1)%Z with ((ex + 1075) * 2 ^ 52 + (Zpos mx - 2 ^ 52 + 1))%Z by ring.
    rewrite <- join_eq. destruct (join_val (Zpos mx - 2 ^ 52 + 1) (ex + 1075) ltac:(lia) ltac:(lia)) as [F E].
    split; [exact F | ]. rewrite E. replace (ex + 1075 - 1075)%Z with ex by ring. do 2 f_equal. ring.
Qed.

(** [h.to_bits() - 1]: the next number down. *)
Theorem bits_down h : finite h -> bpow radix2 (-1021) <= B h ->
  finite (b64_of_bits (bits_of_b64 h - 1)) /\
  B (b64_of_bits (bits_of_b64 h - 1)) = pred radix2 (FLT_exp (-1074) 53) (B h).
Proof.
  intros Fh H1.
  assert (H0 : bpow radix2 (-1022) <= B h) by (apply Rle_trans with (2 := H1); apply bpow_le; lia).
  destruct (pos_normal h Fh H0) as [mx [ex [Mx [Ex [V Bits]]]]].
  assert (Pe : 0 < bpow radix2 ex) by apply bpow_gt_0.
  assert (Pos : 0 < B h) by (pose proof (bpow_gt_0 radix2 (-1022)); lra).
  assert (M : mag radix2 (B h) = (ex + 53)%Z :> Z).
  { apply mag_unique. rewrite Rabs_pos_eq by lra. rewrite V.
    replace (ex + 53 - 1)%Z with (52 + ex)%Z by ring. replace (ex + 53)%Z with (53 + ex)%Z by ring.
    rewrite !bpow_plus.
    split; [apply Rmult_le_compat_r; [lra | ] | apply Rmult_lt_compat_r; [lra | ]].
    - replace (bpow radix2 52) with (IZR (2 ^ 52)) by reflexivity. apply IZR_le. lia.
    - replace (bpow radix2 53) with (IZR (2 ^ 53)) by reflexivity. apply IZR_lt. lia. }
  rewrite Bits, join_eq. rewrite pred_eq_pos by lra. unfold pred_pos. rewrite M.
  replace (ex + 53 - 1)%Z with (52 + ex)%Z by ring.
  destruct (Z.eq_dec (Zpos mx) (2 ^ 52)) as [Bot | Mid].
  - (* the significand field borrows from the exponent field *)
    assert (Ex' : (-1073 <= ex)%Z).
    { apply (le_bpow radix2). apply Rle_trans with (B h * bpow radix2 (-52)).
      - replace (-1073)%Z with (-1021 + -52)%Z by reflexivity. rewrite bpow_plus.
        apply Rmult_le_compat_r; [apply bpow_ge_0 | exact H1].
      - rewrite V, Bot, Rmult_assoc, <- bpow_plus. replace (IZR (2 ^ 52)) with (bpow radix2 52) by reflexivity.
        rewrite <- bpow_plus. apply bpow_le. lia. }
    assert (P2 : B h = bpow radix2 (52 + ex)) by (rewrite V, Bot, bpow_plus; reflexivity).
    rewrite (Req_bool_true _ _ P2).
    replace ((ex + 1075) * 2 ^ 52 + (Zpos mx - 2 ^ 52) - 1)%Z with ((ex + 1074) * 2 ^ 52 + (2 ^ 52 - 1))%Z by lia.
    rewrite <- join_eq. destruct (join_val (2 ^ 52 - 1) (ex + 1074) ltac:(lia) ltac:(lia)) as [F E].
    split; [exact F | ]. rewrite E, P2. unfold FLT_exp. replace (Z.max (52 + ex - 53) (-1074)) with (ex - 1)%Z by lia.
    replace (ex + 1074 - 1075)%Z with (ex - 1)%Z by ring. replace (52 + ex)%Z with (53 + (ex - 1))%Z by ring.
    rewrite bpow_plus. replace (2 ^ 52 - 1 + 2 ^ 52)%Z with (2 ^ 53 - 1)%Z by reflexivity.
    rewrite minus_IZR. replace (IZR (2 ^ 53)) with (bpow radix2 53) by reflexivity. ring.
  - assert (NP : B h <> bpow radix2 (52 + ex)).
    { rewrite V, bpow_plus. intros E. apply Mid. apply eq_IZR. apply Rmult_eq_reg_r with (bpow radix2 ex); [ | lra].
      rewrite E. reflexivity. }
    rewrite (Req_bool_false _ _ NP).
    replace ((ex + 1075) * 2 ^ 52 + (Zpos mx - 2 ^ 52) - 1)%Z with ((ex + 1075) * 2 ^ 52 + (Zpos mx - 2 ^ 52 - 1))%Z by ring.
    rewrite <- join_eq. destruct (join_val (Zpos mx - 2 ^ 52 - 1) (ex + 1075) ltac:(lia) ltac:(lia)) as [F E].
    split; [exact F | ]. rewrite E. replace (ex + 1075 - 1075)%Z with ex by ring.
    rewrite ulp_neq_0 by lra. unfold cexp. rewrite M. unfold FLT_exp.
    replace (Z.max (ex + 53 - 53) (-1074)) with ex by lia.
    rewrite V. replace (Zpos mx - 2 ^ 52 - 1 + 2 ^ 52)%Z with (Zpos mx - 1)%Z by ring. rewrite minus_IZR. ring.
Qed.
