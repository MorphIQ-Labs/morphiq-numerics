(** The certificate that docs/bivariate_normal_truncation.md section 5 states
    for each rule of the low-correlation table, collected in one predicate. *)
From Coq Require Import Reals Lra.
From Interval Require Import Tactic.
Require Import BvnEllipse BvnRules.
Open Scope R_scope.

(** [certified N L A rho]: the [N]-node rule, for every angle [a] with
    [sin a <= L] ([a <= A]), has a Bernstein ellipse (parameter [rho], on the
    interval [[0, A]]) that avoids the singularities of [cos t = 0], on which
    [Re sin t] lies in [[-1, 1]], and the Gauss-Legendre bound
    [64 M / (15 (1 - rho^-2) rho^(2N))] with [M = 1], scaled by [A/2], is at most
    [2 pi * 2e-17]. *)
Definition certified (N : nat) (L A rho : R) : Prop :=
  sin A >= L + 2 / 10000 /\ A < 2 /\
  ellipse_inside A rho /\ ellipse_ok A rho /\
  trunc_bound A rho N <= 2 * PI * (2 / 10 ^ 17).

Lemma certified_of N L A rho :
  sin A >= L + 2 / 10000 -> A < 2 -> ellipse_inside A rho -> ellipse_ok A rho ->
  trunc_bound A rho N <= budget -> certified N L A rho.
Proof.
  intros H1 H2 H3 H4 H5. refine (conj H1 (conj H2 (conj H3 (conj H4 _)))).
  eapply Rle_trans; [exact H5 | exact budget_le].
Qed.

Theorem certified_4 : certified 4 (55/1000) A4 R4.
Proof. destruct (asin_cover_4) as [a b]. apply certified_of; auto using inside_4, ellipse_4, bound_4. Qed.
Theorem certified_6 : certified 6 (2/10) A6 R6.
Proof. destruct (asin_cover_6) as [a b]. apply certified_of; auto using inside_6, ellipse_6, bound_6. Qed.
Theorem certified_8 : certified 8 (38/100) A8 R8.
Proof. destruct (asin_cover_8) as [a b]. apply certified_of; auto using inside_8, ellipse_8, bound_8. Qed.
Theorem certified_10 : certified 10 (54/100) A10 R10.
Proof. destruct (asin_cover_10) as [a b]. apply certified_of; auto using inside_10, ellipse_10, bound_10. Qed.
Theorem certified_12 : certified 12 (66/100) A12 R12.
Proof. destruct (asin_cover_12) as [a b]. apply certified_of; auto using inside_12, ellipse_12, bound_12. Qed.
Theorem certified_14 : certified 14 (75/100) A14 R14.
Proof. destruct (asin_cover_14) as [a b]. apply certified_of; auto using inside_14, ellipse_14, bound_14. Qed.
Theorem certified_16 : certified 16 (81/100) A16 R16.
Proof. destruct (asin_cover_16) as [a b]. apply certified_of; auto using inside_16, ellipse_16, bound_16. Qed.
Theorem certified_20 : certified 20 (89/100) A20 R20.
Proof. destruct (asin_cover_20) as [a b]. apply certified_of; auto using inside_20, ellipse_20, bound_20. Qed.
Theorem certified_24 : certified 24 (925/1000) A24 R24.
Proof. destruct (asin_cover_24) as [a b]. apply certified_of; auto using inside_24, ellipse_24, bound_24. Qed.
