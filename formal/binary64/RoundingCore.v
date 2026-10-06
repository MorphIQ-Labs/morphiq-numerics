(** The rounding test's real-number core: when [|l| + RN(eps·h) < g/2], with
    [g] at most both gaps around a positive [h], every real within [ε₁] of
    [h + l] rounds to [h] (docs/exp.md §5). *)

From Coq Require Import ZArith Reals Lia Lra Psatz.
From Flocq Require Import Core Relative.
From Binary64 Require Import RoundingGaps.

Open Scope R_scope.

Notation RNE := (round radix2 fexp64 (Znearest (fun n => negb (Z.even n)))).

Lemma rnd_rel x : bpow radix2 (-1022) <= Rabs x -> Rabs (RNE x - x) <= bpow radix2 (-53) * Rabs x.
Proof.
  intros H. pose proof (relative_error_N_FLT radix2 (-1074) 53 ltac:(lia) (fun n => negb (Z.even n)) x) as R.
  replace (-1074 + 53 - 1)%Z with (-1022)%Z in R by reflexivity. specialize (R H).
  assert (E : / 2 * bpow radix2 (- (53) + 1) = bpow radix2 (-53)).
  { replace (- (53) + 1)%Z with (-53 + 1)%Z by reflexivity. rewrite bpow_plus. change (bpow radix2 1) with 2%R. field. }
  rewrite E in R. exact R.
Qed.

(** The rounding test's real-number core, for a positive leading word: when
    [|l| + RN(eps·h) < g/2] with [g] at most both gaps around [h], every [Z]
    within [e1] of [h + l] rounds to [h]. *)
Lemma ziv_pos (h l eps e1 Z g : R) :
  F64 h -> bpow radix2 (-900) <= h -> h <= bpow radix2 1000 ->
  h = RNE (h + l) ->
  g <= ulp radix2 fexp64 h -> g <= h - pred radix2 fexp64 h ->
  bpow radix2 (-80) <= e1 <= bpow radix2 (-60) -> e1 * (1 + bpow radix2 (-50)) <= eps <= 1 ->
  Rabs (Z - (h + l)) <= e1 * Rabs Z ->
  Rabs l + RNE (eps * h) < g / 2 ->
  RNE Z = h.
Proof.
  intros Fh Hlo Hhi Hdw G1 G2 [E80 E1] [Ee Ee1] HZ Ht.
  assert (E0 : 0 < e1) by (pose proof (bpow_gt_0 radix2 (-80)); lra).
  assert (P60 : bpow radix2 (-60) = / 1152921504606846976) by reflexivity.
  assert (P50 : bpow radix2 (-50) = / 1125899906842624) by reflexivity.
  assert (P53 : bpow radix2 (-53) = / 9007199254740992) by reflexivity.
  assert (P52 : bpow radix2 (-52) = / 4503599627370496) by reflexivity.
  assert (Hpos : 0 < h) by (pose proof (bpow_gt_0 radix2 (-900)); lra).
  (* |l| <= 2^-52 h: h = RN(h + l) with h + l normal *)
  assert (Hl : Rabs l <= bpow radix2 (-52) * h).
  { destruct (Rle_or_lt (bpow radix2 (-1022)) (Rabs (h + l))) as [N | S].
    - pose proof (rnd_rel (h + l) N) as R. rewrite <- Hdw in R.
      replace (h - (h + l)) with (- l) in R by ring. rewrite Rabs_Ropp in R.
      assert (Tr : Rabs (h + l) <= h + Rabs l) by (pose proof (Rabs_triang h l) as T; rewrite (Rabs_pos_eq h) in T by lra; lra).
      rewrite P53 in R. rewrite P52. nra.
    - (* h + l tiny would round to a tiny h, contradicting h >= 2^-900 *)
      exfalso. assert (RNE (h + l) <= bpow radix2 (-1022)).
      { apply round_le_generic; auto with typeclass_instances.
        - apply generic_format_FLT_bpow; [reflexivity | lia].
        - apply Rabs_lt_inv in S. lra. }
      assert (bpow radix2 (-1022) < bpow radix2 (-900)) by (apply bpow_lt; lia). lra. }
  (* |Z - (h + l)| <= e1 (1 + 2^-51) h *)
  assert (HZ2 : Rabs (Z - (h + l)) <= e1 * (1 + bpow radix2 (-51)) * h).
  { set (D := Rabs (Z - (h + l))). set (Y := Rabs (h + l)).
    assert (Zt : Rabs Z <= Y + D).
    { unfold Y, D. replace Z with ((h + l) + (Z - (h + l))) at 1 by ring. apply Rabs_triang. }
    assert (Tr : Y <= h + Rabs l) by (unfold Y; pose proof (Rabs_triang h l) as T; rewrite (Rabs_pos_eq h) in T by lra; lra).
    assert (P51 : bpow radix2 (-51) = / 2251799813685248) by reflexivity.
    rewrite P51. rewrite P52 in Hl. rewrite P60 in E1.
    assert (D0 : 0 <= D) by apply Rabs_pos.
    (* D <= e1 (Y + D) <= e1 h (1 + 2^-52) + 2^-60 D *)
    assert (S1 : D <= e1 * Y + e1 * D).
    { apply Rle_trans with (1 := HZ). rewrite <- Rmult_plus_distr_l. apply Rmult_le_compat_l; lra. }
    assert (S2 : e1 * Y <= (e1 * h) * (1 + / 4503599627370496)).
    { replace ((e1 * h) * (1 + / 4503599627370496)) with (e1 * (h * (1 + / 4503599627370496))) by ring.
      apply Rmult_le_compat_l; lra. }
    assert (S3 : e1 * D <= / 1152921504606846976 * D) by (apply Rmult_le_compat_r; lra).
    assert (X0 : 0 <= e1 * h) by nra.
    replace (e1 * (1 + / 2251799813685248) * h) with ((e1 * h) * (1 + / 2251799813685248)) by ring.
    lra. }
  (* RN(eps h) >= eps h (1 - 2^-53) >= e1 (1 + 2^-51) h *)
  assert (Hr : e1 * (1 + bpow radix2 (-51)) * h <= RNE (eps * h)).
  { assert (P50' : 0 < bpow radix2 (-50)) by apply bpow_gt_0.
    assert (Le : e1 <= eps) by nra.
    assert (N : bpow radix2 (-1022) <= Rabs (eps * h)).
    { rewrite Rabs_pos_eq by (apply Rmult_le_pos; lra).
      assert (B : bpow radix2 (-1022) <= bpow radix2 (-80) * bpow radix2 (-900))
        by (rewrite <- bpow_plus; apply bpow_le; lia).
      pose proof (bpow_gt_0 radix2 (-80)). pose proof (bpow_gt_0 radix2 (-900)).
      apply Rle_trans with (1 := B). apply Rmult_le_compat; lra. }
    pose proof (rnd_rel (eps * h) N) as R. apply Rabs_le_inv in R.
    rewrite Rabs_pos_eq in R by nra.
    assert (P51 : bpow radix2 (-51) = / 2251799813685248) by reflexivity.
    rewrite P51. rewrite P53 in R. rewrite P50 in Ee. nra. }
  assert (Hclose : Rabs (Z - h) < g / 2).
  { replace (Z - h) with ((Z - (h + l)) + l) by ring.
    apply Rle_lt_trans with (Rabs (Z - (h + l)) + Rabs l); [apply Rabs_triang | lra]. }
  apply round_within with g; assumption || lra.
Qed.
