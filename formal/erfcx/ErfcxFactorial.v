(** Normalize factorial coefficients using binary integers, without expanding
    a factorial as a unary natural or a product in R. *)
From Coq Require Import Reals ZArith.
Open Scope R_scope.

Fixpoint factorial_integer (n : nat) : Z :=
  match n with O => 1%Z | S k => (Z.of_nat (S k)*factorial_integer k)%Z end.

Lemma factorial_real_integer n : INR (fact n)=IZR (factorial_integer n).
Proof.
  induction n as [ | n IH]; [reflexivity | ].
  change (INR (S n*fact n)=IZR (Z.of_nat (S n)*factorial_integer n)).
  rewrite mult_INR, mult_IZR, IH, INR_IZR_INZ. reflexivity.
Qed.

Ltac binary_factorials :=
  repeat rewrite factorial_real_integer;
  repeat match goal with |- context [factorial_integer ?n] =>
    let v := eval vm_compute in (factorial_integer n) in
    change (factorial_integer n) with v
  end.
