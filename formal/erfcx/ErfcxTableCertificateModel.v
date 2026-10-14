(** The exact stored polynomial and checked binary64/Gappa constants. *)
From Coq Require Import Reals ZArith Lia Lra List.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import IEEE64.
From Gappa Require Import Gappa_library.
Require Import ErfcxTableCoefficient ErfcxTableEntry ErfcxTableEvaluation.
Import ListNotations.
Open Scope R_scope.
Lemma word_value_ok bits m e : word_range_check bits (m,e) (m,e)=true ->
 B (b64_of_bits bits)=float2R (Float2 m e).
Proof.
 intros C. destruct (word_range_check_ok _ _ _ C) as [_ [L U]].
 apply Rle_antisym;assumption.
Qed.
Fixpoint polynomial_tail h cs : R :=
 match cs with
 | nil => 0
 | a::nil => a
 | a::rest => a+h*polynomial_tail h rest
 end.
Definition table_polynomial_exact i h :=
 B (coef i 0)+B (coef i 1)+(B (coef i 2)+B (coef i 3))*h+
 (B (coef i 4)+B (coef i 5))*h*h+h*h*h*polynomial_tail h (map B (tail_coefs i)).

Definition table_exponent i : Z :=
 if Nat.ltb i 49 then 0%Z else ((Z.of_nat i-49)/32)%Z.

Lemma word_integer_ok bits m : word_range_check bits (m,0%Z) (m,0%Z)=true ->
 B (b64_of_bits bits)=Float1 m.
Proof.
 intros C. destruct (word_range_check_ok _ _ _ C) as [_ [L U]].
 change (IZR m*1<=B (b64_of_bits bits)) in L.
 change (B (b64_of_bits bits)<=IZR m*1) in U.
 unfold Float1;lra.
Qed.
