(** Discharges the rewriting hints of the Gappa certificates' Coq proofs.

    Gappa checks a hint [a -> b] only symbolically, and its Coq output (gappa
    -Bcoq, formal/<f>/coq) states each hint as a section hypothesis [a = b],
    preceded by its nonzero conditions where the hint divides ([{ x <> 0 }] in
    the certificate, which Gappa proves from the bounds). scripts/check_formal.sh
    turns every such hypothesis into a lemma proved by [hint], so each
    certificate's final theorem holds with no hypothesis left: [field] proves
    the identity, and [nonzero] proves each denominator [field] needs from a
    stated condition, of which it is a constant multiple once normalized. *)

From Coq Require Import Reals Lra Psatz.
Require Import Gappa.Gappa_library.

Ltac nonzero :=
  match goal with
  | H : ?X <> 0%R |- ?P <> 0%R => let Hp := fresh "Hp" in intro Hp; apply H; nra
  end.

Ltac hint := intros; unfold Float1 in *; field; repeat split; try assumption; try nonzero.
