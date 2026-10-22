(** atan2's tiny ratios: [atan2_tiny_phi] returns the correctly rounded value of [atan (n/d)]
    for a quotient below [2^-900], which is [n/d] itself rounded except where [n/d] is exactly the
    midpoint of two subnormal numbers; there the correct value is the lower neighbor. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 Grid RoundingGaps.
From Interval Require Import Tactic.
Require Import Ln1pLemmas AsinTables AsinKernel AsinSqrtStep AsinSegment AsinWithin AsinFacts AsinPath AsinCorrect AsinSmall AsinEntry
  ExpAccurate Atan2Tables Atan2Kernel Atan2Within Atan2Newton Atan2Odd Atan2Decode Atan2TinyMid.
Open Scope R_scope.

Lemma small_bits k : (0 <= k < 2 ^ 52)%Z -> finite (aw k) /\ B (aw k) = IZR k * bpow radix2 (-1074).
Proof.
  intros Hk. unfold aw, b64_of_bits, binary_float_of_bits.
  rewrite is_finite_FF2B, B2R_FF2B. unfold binary_float_of_bits_aux, split_bits. cbn [fst snd].
  assert (Hs : (2 ^ 52 * 2 ^ 11 <=? k)%Z = false) by (apply Z.leb_gt; lia). rewrite Hs.
  assert (Hm : (k mod 2 ^ 52 = k)%Z) by (apply Z.mod_small; lia). rewrite Hm.
  assert (Hd : (k / 2 ^ 52 mod 2 ^ 11 = 0)%Z) by (rewrite Z.div_small by lia; reflexivity). rewrite Hd.
  cbn [Zeq_bool]. destruct k as [ | p | p]; cbn.
  - split; [reflexivity | ring].
  - split; [reflexivity | ]. unfold F2R. cbn [Fnum Fexp]. reflexivity.
  - lia.
Qed.
