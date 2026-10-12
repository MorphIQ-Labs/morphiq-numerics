(** [ln_1p]'s screens (crates/morphiq-numerics/src/ln/stages.rs,
    [stage_h_screen] and [stage_b_screen]), transcribed on the encoding as the
    code computes them, and what they let through: a finite [x] with
    [2^-46 <= |x|] and [-1 < x < 2^53] (stage H), [2^-54 <= |x|] and
    [-1 < x < 2^1020] (stage B). *)

From Coq Require Import ZArith Reals Lia Lra.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import IEEE64.

Open Scope R_scope.

(** A 64-bit word read as a signed one. *)
Definition sgn64 (b : Z) : Z := if (b <? 2 ^ 63)%Z then b else (b - 2 ^ 64)%Z.

(** [(b << 1) >= floor << 1], [b as i64 < ceil], [b < bits(-1)]. *)
Definition screen (lo hi : Z) (x : f64) : bool :=
  let b := bits_of_b64 x in
  andb (andb (2 * (lo * 2 ^ 52) <=? (2 * b) mod 2 ^ 64)%Z (sgn64 b <? hi * 2 ^ 52)%Z) (b <? 2 ^ 63 + 1023 * 2 ^ 52)%Z.

Definition h_screen : f64 -> bool := screen 977 1076.
Definition b_screen : f64 -> bool := screen 969 2043.

(** A normal encoding's value, either sign. *)
Lemma join_val_s s m e : (0 <= m < 2 ^ 52)%Z -> (1 <= e <= 2046)%Z ->
  finite (b64_of_bits (join_bits 52 11 s m e)) /\
  B (b64_of_bits (join_bits 52 11 s m e)) = (if s then -1 else 1) * (IZR (m + 2 ^ 52) * bpow radix2 (e - 1075)).
Proof.
  intros Hm He. unfold b64_of_bits, binary_float_of_bits. rewrite B2R_FF2B, is_finite_FF2B.
  unfold binary_float_of_bits_aux. rewrite split_join_bits by (change (Zpower 2 52) with (2 ^ 52)%Z; change (Zpower 2 11) with 2048%Z; lia).
  replace (Zeq_bool e 0) with false by (symmetry; apply Zeq_bool_false; lia).
  replace (Zeq_bool e (Zpower 2 11 - 1)) with false by (symmetry; apply Zeq_bool_false; change (Zpower 2 11) with 2048%Z; lia).
  change (Zpower 2 52) with (2 ^ 52)%Z.
  destruct (m + 2 ^ 52)%Z as [ | p | p] eqn:Ep; [lia | | lia].
  split; [reflexivity | ]. unfold FF2R, F2R. cbn [Fnum Fexp]. rewrite <- Ep.
  change (2 ^ (11 - 1))%Z with 1024%Z.
  replace (e + (3 - 1024 - (52 + 1)) - 1)%Z with (e - 1075)%Z by lia.
  destruct s; cbn [SpecFloat.cond_Zopp]; [rewrite opp_IZR; ring | ring].
Qed.

Lemma screen_ok lo hi x : (1 <= lo)%Z -> (lo < hi <= 2047)%Z -> screen lo hi x = true ->
  finite x /\ bpow radix2 (lo - 1023) <= Rabs (B x) /\ -1 < B x < bpow radix2 (hi - 1023).
Proof.
  intros Hlo Hhi Hs. unfold screen in Hs.
  set (b := bits_of_b64 x) in *.
  assert (Hb : (0 <= b < 2 ^ 64)%Z) by (unfold b, bits_of_b64; apply bits_of_binary_float_range; lia).
  apply andb_prop in Hs as [Hs H3]. apply andb_prop in Hs as [H1 H2].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.ltb_lt in H3.
  set (q := (b / 2 ^ 52)%Z). set (m := (b mod 2 ^ 52)%Z). set (e := (q mod 2048)%Z).
  assert (Dm : (b = 2 ^ 52 * q + m)%Z) by (apply Z.div_mod; lia).
  assert (Bm : (0 <= m < 2 ^ 52)%Z) by (apply Z.mod_pos_bound; lia).
  assert (De : (q = 2048 * (q / 2048) + e)%Z) by (apply Z.div_mod; lia).
  assert (Be : (0 <= e < 2048)%Z) by (apply Z.mod_pos_bound; lia).
  set (t := (q / 2048)%Z).
  assert (Ht : (0 <= t <= 1)%Z).
  { unfold t. split; [apply Z.div_pos; [apply Z.div_pos | ]; lia | ].
    apply Z.lt_succ_r. apply Z.div_lt_upper_bound; [lia | ]. unfold q.
    apply Z.div_lt_upper_bound; lia. }
  fold t in De.
  set (s := (t =? 1)%Z).
  assert (J : join_bits 52 11 s m e = b).
  { unfold join_bits. rewrite Z.shiftl_mul_pow2 by lia. change (Zpower 2 11) with 2048%Z.
    unfold s. destruct (Z.eqb_spec t 1); lia. }
  assert (X : x = b64_of_bits (join_bits 52 11 s m e)).
  { rewrite J. unfold b. symmetry. apply (binary_float_of_bits_of_binary_float 52 11). }
  assert (D2 : ((2 * b) mod 2 ^ 64 = 2 * (e * 2 ^ 52 + m))%Z).
  { symmetry. apply (Z.mod_unique _ _ t); lia. }
  rewrite D2 in H1.
  assert (Elo : (lo <= e)%Z) by lia.
  assert (Ehi : (e <= 2046)%Z /\ (t = 0 -> e < hi)%Z /\ (t = 1 -> e <= 1022)%Z).
  { unfold sgn64 in H2. destruct (Z.ltb_spec b (2 ^ 63)); split; try split; intros; lia. }
  destruct Ehi as [E1 [E2 E3]].
  destruct (join_val_s s m e Bm ltac:(lia)) as [F V]. rewrite <- X in F, V.
  assert (Mb : bpow radix2 52 <= IZR (m + 2 ^ 52) < bpow radix2 53).
  { rewrite <- !IZR_Zpower by lia. split; apply IZR_le || apply IZR_lt; cbn; lia. }
  assert (P : 0 < bpow radix2 (e - 1075)) by apply bpow_gt_0.
  pose proof (bpow_gt_0 radix2 52) as P52.
  assert (Lo : bpow radix2 (lo - 1023) <= IZR (m + 2 ^ 52) * bpow radix2 (e - 1075)).
  { replace (lo - 1023)%Z with (52 + (lo - 1075))%Z by ring. rewrite bpow_plus.
    apply Rmult_le_compat; [apply bpow_ge_0 | apply bpow_ge_0 | lra | apply bpow_le; lia]. }
  split; [exact F | ].
  destruct s eqn:Es; rewrite V.
  - assert (T1 : t = 1%Z) by (unfold s in Es; apply Z.eqb_eq, Es).
    assert (Up : IZR (m + 2 ^ 52) * bpow radix2 (e - 1075) < 1).
    { apply Rlt_le_trans with (bpow radix2 53 * bpow radix2 (e - 1075)); [apply Rmult_lt_compat_r; lra | ].
      rewrite <- bpow_plus. change 1 with (bpow radix2 0). apply bpow_le. specialize (E3 T1). lia. }
    replace (-1 * (IZR (m + 2 ^ 52) * bpow radix2 (e - 1075))) with (- (IZR (m + 2 ^ 52) * bpow radix2 (e - 1075))) by ring.
    rewrite Rabs_Ropp, Rabs_pos_eq by (apply Rmult_le_pos; [lra | apply bpow_ge_0]).
    assert (0 <= IZR (m + 2 ^ 52) * bpow radix2 (e - 1075)) by (apply Rmult_le_pos; lra).
    split; [exact Lo | ]. pose proof (bpow_gt_0 radix2 (hi - 1023)). split; lra.
  - assert (T0 : t = 0%Z) by (unfold s in Es; apply Z.eqb_neq in Es; lia).
    assert (Up : IZR (m + 2 ^ 52) * bpow radix2 (e - 1075) < bpow radix2 (hi - 1023)).
    { apply Rlt_le_trans with (bpow radix2 53 * bpow radix2 (e - 1075)); [apply Rmult_lt_compat_r; lra | ].
      rewrite <- bpow_plus. apply bpow_le. specialize (E2 T0). lia. }
    rewrite Rmult_1_l, Rabs_pos_eq by (apply Rmult_le_pos; [lra | apply bpow_ge_0]).
    split; [exact Lo | ]. split; [ | exact Up].
    assert (0 <= IZR (m + 2 ^ 52) * bpow radix2 (e - 1075)) by (apply Rmult_le_pos; lra). lra.
Qed.

Theorem h_screen_ok x : h_screen x = true ->
  finite x /\ bpow radix2 (-46) <= Rabs (B x) /\ -1 < B x < bpow radix2 53.
Proof. intros H. exact (screen_ok 977 1076 x ltac:(lia) ltac:(lia) H). Qed.

Theorem b_screen_ok x : b_screen x = true ->
  finite x /\ bpow radix2 (-54) <= Rabs (B x) /\ -1 < B x < bpow radix2 1020.
Proof. intros H. exact (screen_ok 969 2043 x ltac:(lia) ltac:(lia) H). Qed.
