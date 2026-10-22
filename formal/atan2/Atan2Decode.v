(** Decoding a positive finite binary64 from its fraction and biased exponent fields. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 Encodings.
Require Import Ln1pLemmas AsinTables AsinKernel AsinSqrtStep AsinWithin AsinFacts AsinPath AsinCorrect AsinSmall AsinEntry Atan2Kernel Atan2Odd.
Open Scope R_scope.


(** A positive finite binary64 as its fraction and biased exponent fields. *)
Lemma decode_bits n : (0 <= n < 2 ^ 63)%Z -> finite (b64_of_bits n) -> 0 < B (b64_of_bits n) ->
  ((n / 2 ^ 52 = 0)%Z /\ (0 < n mod 2 ^ 52)%Z /\ B (b64_of_bits n) = IZR (n mod 2 ^ 52)%Z * bpow radix2 (-1074)) \/
  (((0 < n / 2 ^ 52)%Z /\ (n / 2 ^ 52 < 2047)%Z) /\ B (b64_of_bits n) = IZR (n mod 2 ^ 52 + 2 ^ 52)%Z * bpow radix2 (n / 2 ^ 52 - 1075)).
Proof.
  intros Hn Fn Pn. unfold b64_of_bits, binary_float_of_bits in *.
  rewrite is_finite_FF2B in Fn. rewrite B2R_FF2B in Pn |- *.
  unfold binary_float_of_bits_aux in Fn, Pn |- *. unfold split_bits in Fn, Pn |- *. cbn [fst snd] in *.
  assert (Hs : (2 ^ 52 * 2 ^ 11 <=? n)%Z = false) by (apply Z.leb_gt; lia).
  rewrite Hs in *.
  set (f := (n mod 2 ^ 52)%Z) in *. set (b := (n / 2 ^ 52 mod 2 ^ 11)%Z) in *.
  assert (Hb : b = (n / 2 ^ 52)%Z).
  { unfold b. apply Z.mod_small. split; [apply Z.div_pos; lia | ]. apply Z.div_lt_upper_bound; lia. }
  assert (Hf : (0 <= f < 2 ^ 52)%Z) by (unfold f; apply Z.mod_pos_bound; lia).
  rewrite Hb in *.
  assert (Hdp : (0 <= n / 2 ^ 52)%Z) by (apply Z.div_pos; lia).
  destruct (Z.eq_dec (n / 2 ^ 52) 0) as [E0 | E0].
  - assert (Hz : Zeq_bool (n / 2 ^ 52) 0 = true) by (apply Zeq_is_eq_bool; exact E0).
    rewrite Hz in *. destruct f as [ | pf | pf] eqn:Ef.
    + cbn in Pn. lra.
    + left. split; [exact E0 | ]. split; [lia | ].
      cbn [FF2R] in Pn |- *. unfold F2R. cbn [Fnum Fexp]. simpl. reflexivity.
    + lia.
  - assert (Hz : Zeq_bool (n / 2 ^ 52) 0 = false) by (destruct (Zeq_bool (n / 2 ^ 52) 0) eqn:Eq0; [exfalso; apply E0; apply Zeq_bool_eq; exact Eq0 | reflexivity]).
    rewrite Hz in *.
    destruct (Zeq_bool (n / 2 ^ 52) (2 ^ 11 - 1)) eqn:Ee.
    + exfalso. destruct f as [ | pf | pf]; cbn in Fn; discriminate Fn.
    + assert (Hl : (n / 2 ^ 52 <> 2047)%Z) by (intros H; apply Zeq_is_eq_bool in H; replace (2 ^ 11 - 1)%Z with 2047%Z in Ee by reflexivity; rewrite H in Ee; discriminate).
      right. split; [split; [lia | ] | ].
      * assert (n / 2 ^ 52 < 2048)%Z by (apply Z.div_lt_upper_bound; lia). lia.
      * destruct (f + 2 ^ 52)%Z as [ | pf | pf] eqn:Em; try (cbn in Pn; lra).
        cbn [FF2R SpecFloat.cond_Zopp]. unfold F2R. cbn [Fnum Fexp].
        replace (n / 2 ^ 52 + (3 - 2 ^ (11 - 1) - (52 + 1)) - 1)%Z with (n / 2 ^ 52 - 1075)%Z by (change (2 ^ (11 - 1))%Z with 1024%Z; ring).
        reflexivity.
Qed.

Lemma lor_frac f : (0 <= f < 2 ^ 52)%Z -> Z.lor f (2 ^ 52) = (f + 2 ^ 52)%Z.
Proof.
  intros H.
  assert (L : Z.land f (2 ^ 52) = 0%Z).
  { apply Z.bits_inj'. intros k Hk. rewrite Z.land_spec, Z.pow2_bits_eqb by lia. rewrite Z.bits_0.
    destruct (52 =? k)%Z eqn:E; [ | rewrite Bool.andb_false_r; reflexivity].
    apply Z.eqb_eq in E. subst k. rewrite Bool.andb_true_r.
    destruct (Z.testbit f 52) eqn:Tb; [ | reflexivity].
    apply Z.testbit_true in Tb; [ | lia]. rewrite Z.div_small in Tb by lia. discriminate Tb. }
  rewrite <- (Z.lxor_lor f (2 ^ 52) L). symmetry. apply Z.add_nocarry_lxor. exact L.
Qed.

Lemma pos_bits x : finite x -> 0 < B x -> (0 < bits_of_b64 x < 2 ^ 63)%Z /\ B x = B (b64_of_bits (bits_of_b64 x)) /\ finite (b64_of_bits (bits_of_b64 x)).
Proof.
  intros Fx Px. destruct (abs_split x Fx) as [n0 [R0 [_ [Fn [Nn [[Hb Bx] | [Hb Bx]]]]]]].
  - rewrite Hb. repeat split; try lia; try exact Bx; try exact Fn.
    destruct (Z.eq_dec n0 0) as [-> | Hn0]; [ | lia].
    exfalso. assert (Hz : B (b64_of_bits 0) = 0) by (apply bits_zero with (s := false); vm_compute; reflexivity). rewrite Hz in Bx. lra.
  - exfalso. lra.
Qed.

Theorem odd_part_ok x : finite x -> 0 < B x ->
  exists m e, atan2_odd_part x = (m, e) /\ Z.odd m = true /\ (0 < m < 2 ^ 53)%Z /\ (-1074 <= e)%Z /\ B x = IZR m * bpow radix2 e.
Proof.
  intros Fx Px. destruct (pos_bits x Fx Px) as [[N0 N1] [Bx Fn]]. set (n := bits_of_b64 x) in *.
  rewrite Bx in Px |- *.
  assert (Hsh : Z.shiftr n 52 = (n / 2 ^ 52)%Z) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (Hfr : Z.land n (2 ^ 52 - 1) = (n mod 2 ^ 52)%Z).
  { replace (2 ^ 52 - 1)%Z with (Z.ones 52) by reflexivity. rewrite Z.land_ones by lia. reflexivity. }
  assert (Hf : (0 <= n mod 2 ^ 52 < 2 ^ 52)%Z) by (apply Z.mod_pos_bound; lia).
  unfold atan2_odd_part. fold n. rewrite Hsh, Hfr.
  destruct (decode_bits n (conj (proj1 (conj (Z.lt_le_incl _ _ N0) N1)) N1) Fn Px) as [[E0 [Pf V]] | [[E1 E2] V]].
  - assert (Hb0 : (n / 2 ^ 52 =? 0)%Z = true) by (apply Z.eqb_eq; exact E0).
    rewrite Hb0. cbv zeta iota.
    destruct (lowbit_spec (n mod 2 ^ 52) Pf) as [v [o [Hv [Ho [Ho0 [Hm Hl]]]]]].
    rewrite Hl, Z.log2_pow2 by lia. rewrite Z.shiftr_div_pow2 by lia.
    assert (Hq : (n mod 2 ^ 52 / 2 ^ v)%Z = o) by (rewrite Hm at 1; apply Z.div_mul; apply Z.pow_nonzero; lia).
    rewrite Hq.
    exists o, (-1074 + v)%Z. refine (conj eq_refl (conj Ho (conj (conj Ho0 _) (conj _ _)))).
    + assert (Ho2 : (o <= n mod 2 ^ 52)%Z).
      { rewrite Hm at 1. assert (0 < 2 ^ v)%Z by (apply Z.pow_pos_nonneg; lia). apply Z.le_mul_diag_r; lia. }
      assert (H53 : (2 ^ 52 < 2 ^ 53)%Z) by reflexivity. lia.
    + lia.
    + rewrite V. rewrite Hm at 1. rewrite mult_IZR. assert (Hp : IZR (2 ^ v) = bpow radix2 v) by (apply (IZR_Zpower radix2); lia). rewrite Hp, bpow_plus. ring.
  - assert (Hb0 : (n / 2 ^ 52 =? 0)%Z = false) by (apply Z.eqb_neq; lia).
    rewrite Hb0. cbv zeta iota. rewrite (lor_frac _ Hf).
    destruct (lowbit_spec (n mod 2 ^ 52 + 2 ^ 52) ltac:(lia)) as [v [o [Hv [Ho [Ho0 [Hm Hl]]]]]].
    rewrite Hl, Z.log2_pow2 by lia. rewrite Z.shiftr_div_pow2 by lia.
    assert (Hq : ((n mod 2 ^ 52 + 2 ^ 52) / 2 ^ v)%Z = o) by (rewrite Hm at 1; apply Z.div_mul; apply Z.pow_nonzero; lia).
    rewrite Hq.
    exists o, (n / 2 ^ 52 - 1075 + v)%Z. refine (conj eq_refl (conj Ho (conj (conj Ho0 _) (conj _ _)))).
    + assert (Ho2 : (o <= n mod 2 ^ 52 + 2 ^ 52)%Z).
      { rewrite Hm at 1. assert (0 < 2 ^ v)%Z by (apply Z.pow_pos_nonneg; lia). apply Z.le_mul_diag_r; lia. }
      assert (H53 : (2 ^ 53 = 2 * 2 ^ 52)%Z) by reflexivity. lia.
    + lia.
    + rewrite V. rewrite Hm at 1. rewrite mult_IZR. assert (Hp : IZR (2 ^ v) = bpow radix2 v) by (apply (IZR_Zpower radix2); lia). rewrite Hp, bpow_plus. ring.
Qed.
