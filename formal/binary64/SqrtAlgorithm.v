(** crates/morphiq-numerics/src/sqrt.rs transcribed ([sqrt_rs]) and proved to
    be IEEE 754's square root ([sqrt_rs_ieee]: it equals [fsqrt], Flocq's
    correctly rounded [b64_sqrt], for every binary64). The extraction
    cross-check (formal/extraction) compares the transcription with the Rust
    code bit for bit. *)

From Coq Require Import Bool Reals ZArith Lia Lra.
From Flocq Require Import Core Digits IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Sqrt.
From Binary64 Require Import Isqrt SqrtRound.

Open Scope Z_scope.

(** sqrt.rs on a positive finite [x = mx·2^ex], step for step: normalize the
    significand to [2^52 <= m < 2^53] (a subnormal's is shifted up), make the
    exponent even, take the integer root, round, and assemble. *)
Definition normalize (mx ex : Z) : Z * Z :=
  let sh := 53 - Zdigits radix2 mx in
  let m := mx * 2 ^ sh in
  let e := ex - sh in
  if Z.odd e then (2 * m, e - 1) else (m, e).

Definition sqrt_rs (x : f64) : f64 :=
  match x with
  | B754_finite false mx ex _ =>
      let '(m, e) := normalize (Zpos mx) ex in
      let '(s, rem) := isqrt (m * 2 ^ 54) in
      binary_normalize 53 1024 eq_refl eq_refl mode_NE (round_root s rem) ((e - 54) / 2 + 1) false
  | _ => fsqrt x
  end.

Lemma IZR_pow2 k : 0 <= k -> IZR (2 ^ k) = bpow radix2 k.
Proof. intros H. destruct k; [reflexivity | reflexivity | lia]. Qed.

Lemma normalize_ok mx ex : 0 < mx < 2 ^ 53 -> -1074 <= ex ->
  let '(m, e) := normalize mx ex in
  2 ^ 52 <= m < 2 ^ 54 /\ Z.even e = true /\ -1128 <= e /\
  F2R (Float radix2 m e) = F2R (Float radix2 mx ex).
Proof.
  intros Hm He. unfold normalize.
  pose proof (Zdigits_correct radix2 mx) as D. rewrite Z.abs_eq in D by lia.
  set (d := Zdigits radix2 mx) in *.
  assert (Dp : 1 <= d <= 53).
  { split.
    - destruct (Z_lt_le_dec d 1) as [L | L]; [ | lia ]. exfalso.
      assert (d <= 0) by lia. assert (radix2 ^ d <= 1).
      { destruct (Z.eq_dec d 0) as [-> | ]; [reflexivity | rewrite Z.pow_neg_r by lia; lia]. }
      change (Zpower radix2 d) with (radix2 ^ d) in D. lia.
    - destruct (Z_le_gt_dec d 53) as [L | L]; [exact L | ]. exfalso.
      assert (2 ^ 53 <= 2 ^ (d - 1)) by (apply Z.pow_le_mono_r; lia).
      change (Zpower radix2 (d - 1)) with (2 ^ (d - 1)) in D. lia. }
  change (Zpower radix2 (d - 1)) with (2 ^ (d - 1)) in D.
  change (Zpower radix2 d) with (2 ^ d) in D.
  assert (M0 : 2 ^ 52 <= mx * 2 ^ (53 - d) < 2 ^ 53).
  { replace (2 ^ 52) with (2 ^ (d - 1) * 2 ^ (53 - d)) by (rewrite <- Z.pow_add_r by lia; f_equal; ring).
    replace (2 ^ 53) with (2 ^ d * 2 ^ (53 - d)) by (rewrite <- Z.pow_add_r by lia; f_equal; ring).
    pose proof (Z.pow_pos_nonneg 2 (53 - d) ltac:(lia) ltac:(lia)). nia. }
  assert (V0 : F2R (Float radix2 (mx * 2 ^ (53 - d)) (ex - (53 - d))) = F2R (Float radix2 mx ex)).
  { unfold F2R, Fnum, Fexp. rewrite mult_IZR. rewrite (IZR_pow2 (53 - d)) by lia.
    rewrite Rmult_assoc, <- bpow_plus. f_equal. f_equal. ring. }
  destruct (Z.odd (ex - (53 - d))) eqn:O.
  - repeat split; try lia.
    + rewrite <- Z.negb_odd, Z.odd_sub, O. reflexivity.
    + rewrite <- V0. unfold F2R, Fnum, Fexp. rewrite mult_IZR.
      set (e0 := ex - (53 - d)).
      assert (B : (bpow radix2 e0 = 2 * bpow radix2 (e0 - 1))%R).
      { replace e0 with (e0 - 1 + 1)%Z at 1 by ring. rewrite bpow_plus. change (bpow radix2 1) with 2%R. lra. }
      rewrite B. ring_simplify. reflexivity.
  - repeat split; try lia.
    + rewrite <- Z.negb_odd, O. reflexivity.
    + exact V0.
Qed.

(** The transcription of sqrt.rs is IEEE 754's square root: for a positive
    finite [x] by the derivation above; every other input is handled by the
    special-value branches, which the definition takes from [fsqrt]. *)
Theorem sqrt_rs_ieee x : sqrt_rs x = fsqrt x.
Proof.
  destruct x as [s | s | s pl Hpl | s mx ex Hx]; try reflexivity.
  destruct s; [reflexivity | ].
  (* The binary64 field bounds: mx < 2^53 and ex >= -1074. *)
  pose proof Hx as Hb. unfold bounded in Hb. apply andb_prop in Hb as [Hc _].
  unfold canonical_mantissa in Hc. apply Zeq_bool_eq in Hc.
  rewrite Zpos_digits2_pos in Hc. unfold FLT_exp in Hc.
  pose proof (Zdigits_correct radix2 (Zpos mx)) as D.
  assert (Ex : -1074 <= ex) by lia.
  assert (Mx : 0 < Zpos mx < 2 ^ 53).
  { split; [lia | ]. assert (Zdigits radix2 (Zpos mx) <= 53) by lia.
    apply Z.lt_le_trans with (Zpower radix2 (Zdigits radix2 (Zpos mx))); [lia | ].
    change (Zpower radix2 (Zdigits radix2 (Zpos mx))) with (2 ^ Zdigits radix2 (Zpos mx)).
    apply Z.pow_le_mono_r; lia. }
  pose proof (normalize_ok (Zpos mx) ex Mx Ex) as N.
  unfold sqrt_rs. destruct (normalize (Zpos mx) ex) as [m e].
  destruct N as [Hm [He [Hlo Hv]]].
  assert (Rr : 0 < m * 2 ^ 54 < 2 ^ 128) by lia.
  rewrite (isqrt_correct _ Rr).
  set (sig := round_root (Z.sqrt (m * 2 ^ 54)) (m * 2 ^ 54 - Z.sqrt (m * 2 ^ 54) ^ 2)).
  set (y := B754_finite 53 1024 false mx ex Hx).
  destruct (sqrt_ieee y) as [Sv Sf].
  assert (Fy : finite y) by reflexivity.
  assert (Py : (0 <= B y)%R) by (apply F2R_ge_0; simpl; lia).
  assert (Ff : finite (fsqrt y)) by (apply Sf; split; assumption).
  (* The value: round_sqrt. *)
  assert (Val : B (fsqrt y) = F2R (Float radix2 sig ((e - 54) / 2 + 1))).
  { rewrite Sv. unfold y. simpl B2R. rewrite <- Hv. apply round_sqrt; assumption. }
  pose proof (binary_normalize_correct 53 1024 eq_refl eq_refl mode_NE sig ((e - 54) / 2 + 1) false) as C.
  assert (Fmt : generic_format radix2 (FLT_exp (3 - 1024 - 53) 53) (F2R (Float radix2 sig ((e - 54) / 2 + 1)))).
  { rewrite <- Val, Sv. apply generic_format_round; auto with typeclass_instances. }
  rewrite round_generic in C by (auto with typeclass_instances).
  rewrite Rlt_bool_true in C.
  2: { rewrite <- Val. apply abs_B2R_lt_emax. }
  destruct C as [C1 [C2 C3]].
  apply (B2R_Bsign_inj 53 1024); [exact C2 | exact Ff | | ].
  - rewrite C1, Val. reflexivity.
  - rewrite C3.
    assert (Pos : (0 < F2R (Float radix2 sig ((e - 54) / 2 + 1)))%R).
    { apply F2R_gt_0. simpl. unfold sig, round_root.
      assert (2 ^ 53 <= Z.sqrt (m * 2 ^ 54)).
      { rewrite <- (Z.sqrt_square (2 ^ 53)) by lia. apply Z.sqrt_le_mono. lia. }
      assert (2 ^ 52 <= Z.sqrt (m * 2 ^ 54) / 2) by (apply Z.div_le_lower_bound; lia).
      destruct (_ && _)%bool; lia. }
    rewrite Rcompare_Gt by exact Pos.
    destruct (Bsqrt_correct 53 1024 eq_refl eq_refl unop_nan_pl64 mode_NE y) as [_ [_ Sg]].
    unfold fsqrt, b64_sqrt. rewrite Sg; [reflexivity | ].
    destruct (Bsqrt 53 1024 _ _ unop_nan_pl64 mode_NE y) eqn:Q; try reflexivity.
    exfalso. unfold fsqrt, b64_sqrt in Ff. rewrite Q in Ff. discriminate.
Qed.
