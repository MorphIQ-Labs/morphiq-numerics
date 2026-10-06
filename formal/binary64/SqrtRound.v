(** The rounding step of sqrt.rs: [round_root] turns [⌊√R⌋] and the
    remainder into the round-to-nearest-even significand, and [round_sqrt]
    shows that, at exponent [(e − 54)/2 + 1], this is the binary64 rounding of
    [√(m·2^e)] for the normalized [m] and even [e] sqrt.rs produces. *)

From Coq Require Import Bool Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Binary64 Require Import Isqrt.

Open Scope R_scope.

Notation rndNE := (round radix2 (FLT_exp (-1074) 53) (Znearest (fun n => negb (Z.even n)))).

(** The rounding step of sqrt.rs: [s = ⌊√R⌋] with its remainder, kept bits
    [s / 2], the rounding bit [s mod 2] and the sticky remainder. *)
Definition round_root (s rem : Z) : Z :=
  let kept := (s / 2)%Z in
  if (Z.odd s && (negb (rem =? 0)%Z || Z.odd kept))%bool then (kept + 1)%Z else kept.

Lemma sqrt_bounds (R : Z) : (0 <= R)%Z ->
  IZR (Z.sqrt R) <= sqrt (IZR R) < IZR (Z.sqrt R) + 1.
Proof.
  intros HR. pose proof (Z.sqrt_spec R HR) as [S1 S2]. unfold Z.succ in S2.
  pose proof (Z.sqrt_nonneg R) as S0.
  split.
  - rewrite <- (sqrt_square (IZR (Z.sqrt R))) by (apply IZR_le; lia).
    apply sqrt_le_1_alt. rewrite <- mult_IZR. apply IZR_le. lia.
  - rewrite <- (sqrt_square (IZR (Z.sqrt R) + 1)) by (apply Rplus_le_le_0_compat; [apply IZR_le; lia | lra]).
    apply sqrt_lt_1_alt. split; [apply IZR_le; lia | ].
    replace ((IZR (Z.sqrt R) + 1) * (IZR (Z.sqrt R) + 1)) with (IZR ((Z.sqrt R + 1) * (Z.sqrt R + 1)))
      by (rewrite mult_IZR, plus_IZR; ring).
    apply IZR_lt. lia.
Qed.

Lemma sqrt_exact (R : Z) : (0 <= R)%Z -> (R - Z.sqrt R ^ 2 = 0)%Z -> sqrt (IZR R) = IZR (Z.sqrt R).
Proof.
  intros HR E. apply sqrt_lem_1; [apply IZR_le; lia | apply IZR_le, Z.sqrt_nonneg | ].
  rewrite <- mult_IZR. f_equal. lia.
Qed.

(** Rounding to nearest-even of [v / 2], for [v = √R]: [round_root]. *)
Lemma znearest_root (R : Z) : (0 <= R)%Z ->
  Znearest (fun n => negb (Z.even n)) (sqrt (IZR R) / 2)
  = round_root (Z.sqrt R) (R - Z.sqrt R ^ 2).
Proof.
  intros HR. pose proof (sqrt_bounds R HR) as [V1 V2].
  set (s := Z.sqrt R) in *. set (v := sqrt (IZR R)) in *.
  pose proof (Z.sqrt_nonneg R) as S0. fold s in S0.
  pose proof (Z.div_mod s 2 ltac:(lia)) as Dm. pose proof (Z.mod_pos_bound s 2 ltac:(lia)) as Mb.
  set (k := (s / 2)%Z) in *.
  assert (Fl : Zfloor (v / 2) = k).
  { apply Zfloor_imp. rewrite plus_IZR.
    assert (IZR s = 2 * IZR k + IZR (s mod 2)) by (rewrite <- mult_IZR, <- plus_IZR; f_equal; lia).
    assert (0 <= IZR (s mod 2) <= 1) by (split; apply IZR_le; lia). lra. }
  unfold Znearest, round_root. rewrite Fl. fold k.
  pose proof (Zmod_odd s) as Om.
  destruct (Z.eq_dec (s mod 2) 0) as [E0 | E1].
  - (* an even root: below the midpoint *)
    assert (Hs : IZR s = 2 * IZR k) by (rewrite <- mult_IZR; f_equal; lia).
    rewrite Rcompare_Lt by lra.
    destruct (Z.odd s); [lia | reflexivity].
  - assert (E1' : (s mod 2 = 1)%Z) by lia.
    assert (Hs : IZR s = 2 * IZR k + 1) by (rewrite <- mult_IZR, <- plus_IZR; f_equal; lia).
    replace (Z.odd s) with true by (destruct (Z.odd s); [reflexivity | lia]). simpl andb.
    assert (Ceil : Zceil (v / 2) = (k + 1)%Z).
    { (* k < v/2 <= k + 1, since 2k + 1 = s <= v < s + 1 *)
      apply Zceil_imp. rewrite minus_IZR, plus_IZR. split; lra. }
    destruct (Z.eq_dec (R - s ^ 2) 0) as [Z0 | Z1].
    + (* exact: v = s, a midpoint *)
      assert (Ve : v = IZR s) by (apply sqrt_exact; [lia | exact Z0]).
      rewrite Rcompare_Eq by lra. change (Z.pow_pos s 2) with (s ^ 2)%Z. rewrite Z0.
      rewrite Ceil, <- Z.negb_even. destruct (Z.even k); reflexivity.
    + (* above the midpoint *)
      assert (Vgt : IZR s < v).
      { destruct (Rle_lt_or_eq_dec _ _ V1) as [L | Eq]; [exact L | ].
        exfalso. apply Z1. apply eq_IZR.
        assert (Vv : IZR R = v * v) by (unfold v; rewrite sqrt_sqrt; [reflexivity | apply IZR_le; lia]).
        rewrite minus_IZR, Z.pow_2_r, mult_IZR, Eq, Vv. ring. }
      rewrite Rcompare_Gt by lra.
      change (Z.pow_pos s 2) with (s ^ 2)%Z.
      replace (R - s ^ 2 =? 0)%Z with false by (symmetry; apply Z.eqb_neq; exact Z1).
      rewrite Ceil. reflexivity.
Qed.

(** [√(m·2^e)] for an even [e] and [2^52 <= m < 2^54], rounded to nearest-even:
    [√(m·2^54)·2^((e − 54)/2)] has its leading bit at [2^((e − 54)/2 + 53)], so
    the result's exponent is [(e − 54)/2 + 1] and its integer significand is
    [round_root] of [⌊√(m·2^54)⌋] and the remainder. *)
Lemma round_sqrt (m e : Z) : (2 ^ 52 <= m < 2 ^ 54)%Z -> Z.even e = true -> (-1128 <= e)%Z ->
  rndNE (sqrt (F2R (Float radix2 m e))) =
  F2R (Float radix2 (round_root (Z.sqrt (m * 2 ^ 54)) (m * 2 ^ 54 - Z.sqrt (m * 2 ^ 54) ^ 2))
                    ((e - 54) / 2 + 1)).
Proof.
  intros Hm He Hlo.
  set (R := (m * 2 ^ 54)%Z). set (h := ((e - 54) / 2)%Z).
  assert (Eh : e = (54 + 2 * h)%Z).
  { unfold h. apply Z.even_spec in He. destruct He as [q ->].
    replace (2 * q - 54)%Z with ((q - 27) * 2)%Z by ring. rewrite Z.div_mul by lia. ring. }
  assert (HR : (2 ^ 106 <= R < 2 ^ 108)%Z) by (unfold R; lia).
  assert (IR : IZR R = IZR m * bpow radix2 54).
  { unfold R. rewrite mult_IZR. f_equal. }
  set (v := sqrt (IZR R)).
  assert (Hx : sqrt (F2R (Float radix2 m e)) = v * bpow radix2 h).
  { unfold F2R, v; simpl. rewrite Eh, !bpow_plus, IR.
    replace (bpow radix2 (2 * h)) with (bpow radix2 h * bpow radix2 h)
      by (rewrite <- bpow_plus; f_equal; ring).
    rewrite <- Rmult_assoc, sqrt_mult_alt.
    - rewrite sqrt_square by apply bpow_ge_0. reflexivity.
    - apply Rmult_le_pos; [apply IZR_le; lia | apply bpow_ge_0]. }
  assert (Vb : bpow radix2 53 <= v < bpow radix2 54).
  { unfold v. split.
    - rewrite <- (sqrt_square (bpow radix2 53)) by apply bpow_ge_0.
      apply sqrt_le_1_alt. rewrite <- bpow_plus. rewrite <- IZR_Zpower by lia. apply IZR_le. simpl. lia.
    - rewrite <- (sqrt_square (bpow radix2 54)) by apply bpow_ge_0.
      apply sqrt_lt_1_alt. split; [apply IZR_le; lia | ].
      rewrite <- bpow_plus. rewrite <- IZR_Zpower by lia. apply IZR_lt. simpl. lia. }
  assert (Mag : mag radix2 (v * bpow radix2 h) = (h + 54)%Z :> Z).
  { pose proof (bpow_gt_0 radix2 53). apply mag_unique.
    rewrite Rabs_pos_eq by (apply Rmult_le_pos; [lra | apply bpow_ge_0]).
    replace (h + 54 - 1)%Z with (53 + h)%Z by ring. replace (h + 54)%Z with (54 + h)%Z by ring.
    rewrite !bpow_plus. pose proof (bpow_gt_0 radix2 h). split; nra. }
  rewrite Hx. unfold round, scaled_mantissa, cexp. rewrite Mag.
  unfold FLT_exp. rewrite Z.max_l by (unfold h; lia).
  replace (h + 54 - 53)%Z with (h + 1)%Z by ring.
  replace (v * bpow radix2 h * bpow radix2 (- (h + 1))) with (v / 2).
  - unfold v. rewrite znearest_root by lia. reflexivity.
  - rewrite Rmult_assoc, <- bpow_plus. replace (h + - (h + 1))%Z with (-1)%Z by ring.
    simpl. unfold Rdiv. f_equal.
Qed.
