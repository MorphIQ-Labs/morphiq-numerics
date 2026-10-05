(** [eft::two_prod] is exact on its documented domain.

    The Rust function computes, with round-to-nearest-even binary64 operations,
    Veltkamp's split of each operand (constant 2^27 + 1) and Dekker's sum of the
    four partial products against [p = RN(a*b)]. That is exactly the algorithm of
    Flocq's [Pff2Flocq.Dekker] (Boldo's formalization), instantiated here at
    radix 2, precision 53 and minimum exponent -1074, with the even tie-breaking
    rule. Flocq's FLT model has gradual underflow and no overflow; binary64
    agrees with it whenever no operation overflows, which the documented domain
    ensures separately ([docs/double-word.md]). *)

From Coq Require Import Reals ZArith Lia.
From Flocq Require Import Core.
From Flocq.Pff Require Import Pff2Flocq.

Open Scope R_scope.

Definition prec : Z := 53.
Definition emin : Z := -1074.
Definition even_ties (n : Z) : bool := negb (Z.even n).

#[export] Instance prec_gt_0 : Prec_gt_0 prec.
Proof. unfold Prec_gt_0, prec; lia. Qed.

Notation format := (generic_format radix2 (FLT_exp emin prec)).
Notation rn := (round radix2 (FLT_exp emin prec) (Znearest even_ties)).

(** The split's constant: 2^s + 1 with s = prec - div2 prec = 27. *)
Lemma split_exponent : (prec - Z.div2 prec = 27)%Z.
Proof. reflexivity. Qed.

(** The Rust function's operation sequence, written out. *)
Definition split_head (x : R) : R :=
  let p := rn (x * (bpow radix2 27 + 1)) in
  let q := rn (x - p) in
  rn (q + p).

Definition split_tail (x : R) : R := rn (x - split_head x).

Definition two_prod_p (a b : R) : R := rn (a * b).

Definition two_prod_e (a b : R) : R :=
  let ah := split_head a in let at_ := split_tail a in
  let bh := split_head b in let bt := split_tail b in
  rn (rn (rn (rn (- two_prod_p a b + rn (ah * bh)) + rn (ah * bt)) + rn (at_ * bh))
      + rn (at_ * bt)).

(** Exactness: [p + e = a * b] whenever the product is zero or at least
    2^(emin + 2 prec - 1) = 2^-969 in magnitude. *)
Theorem two_prod_exact :
  forall a b, format a -> format b ->
  (a * b = 0 \/ bpow radix2 (-969) <= Rabs (a * b)) ->
  a * b = two_prod_p a b + two_prod_e a b.
Proof.
  intros a b Fa Fb H.
  assert (Hd := Dekker radix2 emin prec even_ties (ltac:(unfold prec; lia))
                  (ltac:(unfold emin; lia)) a b Fa Fb (or_introl eq_refl)).
  destruct Hd as [Hexact _].
  unfold two_prod_p, two_prod_e, split_tail, split_head.
  exact (Hexact H).
Qed.

