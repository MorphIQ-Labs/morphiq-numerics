(** Decoding a positive finite binary64 from its fraction and biased exponent fields. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64.
Require Import Ln1pLemmas AsinTables AsinKernel Atan2Kernel Atan2Odd.
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
