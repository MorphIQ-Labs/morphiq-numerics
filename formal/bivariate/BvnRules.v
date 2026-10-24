(** Per-rule instances: for every node count [N] of the low-correlation rule
    table, the ellipse parameter [rho] and the angle bound [A >= asin L + 3e-4]
    ([L] the rule's correlation limit) for which the exponent has a nonnegative
    real part on the whole Bernstein ellipse (so [|f| <= 1] there) and the
    Gauss-Legendre bound is within the budget. *)
From Coq Require Import Reals Lra.
From Interval Require Import Tactic.
Require Import BvnEllipse.
Open Scope R_scope.

(** [N = 6], [|rho| <= 2/10]. *)
Definition A6 : R := 2019/10000.
Definition R6 : R := 202/10.
Lemma asin_cover_6 : sin A6 >= 2/10 + 2 / 10000 /\ A6 < 2.
Proof. unfold A6. split; interval with (i_prec 40). Qed.
Lemma inside_6 : ellipse_inside A6 R6.
Proof. unfold ellipse_inside, A6, R6. split; interval with (i_prec 40). Qed.
Lemma ellipse_6 : ellipse_ok A6 R6.
Proof.
  unfold ellipse_ok, re_sin, cosh', ell_u, ell_v, A6, R6. intros th Hth.
  split; interval with (i_bisect th, i_depth 18).
Qed.
Lemma bound_6 : trunc_bound A6 R6 6 <= budget.
Proof. unfold trunc_bound, budget, A6, R6. interval. Qed.

(** [N = 8], [|rho| <= 38/100]. *)
Definition A8 : R := 3903/10000.
Definition R8 : R := 99/10.
Lemma asin_cover_8 : sin A8 >= 38/100 + 2 / 10000 /\ A8 < 2.
Proof. unfold A8. split; interval with (i_prec 40). Qed.
Lemma inside_8 : ellipse_inside A8 R8.
Proof. unfold ellipse_inside, A8, R8. split; interval with (i_prec 40). Qed.
Lemma ellipse_8 : ellipse_ok A8 R8.
Proof.
  unfold ellipse_ok, re_sin, cosh', ell_u, ell_v, A8, R8. intros th Hth.
  split; interval with (i_bisect th, i_depth 18).
Qed.
Lemma bound_8 : trunc_bound A8 R8 8 <= budget.
Proof. unfold trunc_bound, budget, A8, R8. interval. Qed.

(** [N = 12], [|rho| <= 66/100]. *)
Definition A12 : R := 7214/10000.
Definition R12 : R := 473/100.
Lemma asin_cover_12 : sin A12 >= 66/100 + 2 / 10000 /\ A12 < 2.
Proof. unfold A12. split; interval with (i_prec 40). Qed.
Lemma inside_12 : ellipse_inside A12 R12.
Proof. unfold ellipse_inside, A12, R12. split; interval with (i_prec 40). Qed.
Lemma ellipse_12 : ellipse_ok A12 R12.
Proof.
  unfold ellipse_ok, re_sin, cosh', ell_u, ell_v, A12, R12. intros th Hth.
  split; interval with (i_bisect th, i_depth 18).
Qed.
Lemma bound_12 : trunc_bound A12 R12 12 <= budget.
Proof. unfold trunc_bound, budget, A12, R12. interval. Qed.

(** [N = 14], [|rho| <= 75/100]. *)
Definition A14 : R := 8486/10000.
Definition R14 : R := 382/100.
Lemma asin_cover_14 : sin A14 >= 75/100 + 2 / 10000 /\ A14 < 2.
Proof. unfold A14. split; interval with (i_prec 40). Qed.
Lemma inside_14 : ellipse_inside A14 R14.
Proof. unfold ellipse_inside, A14, R14. split; interval with (i_prec 40). Qed.
Lemma ellipse_14 : ellipse_ok A14 R14.
Proof.
  unfold ellipse_ok, re_sin, cosh', ell_u, ell_v, A14, R14. intros th Hth.
  split; interval with (i_bisect th, i_depth 18).
Qed.
Lemma bound_14 : trunc_bound A14 R14 14 <= budget.
Proof. unfold trunc_bound, budget, A14, R14. interval. Qed.

(** [N = 20], [|rho| <= 89/100]. *)
Definition A20 : R := 10979/10000.
Definition R20 : R := 259/100.
Lemma asin_cover_20 : sin A20 >= 89/100 + 2 / 10000 /\ A20 < 2.
Proof. unfold A20. split; interval with (i_prec 40). Qed.
Lemma inside_20 : ellipse_inside A20 R20.
Proof. unfold ellipse_inside, A20, R20. split; interval with (i_prec 40). Qed.
Lemma ellipse_20 : ellipse_ok A20 R20.
Proof.
  unfold ellipse_ok, re_sin, cosh', ell_u, ell_v, A20, R20. intros th Hth.
  split; interval with (i_bisect th, i_depth 18).
Qed.
Lemma bound_20 : trunc_bound A20 R20 20 <= budget.
Proof. unfold trunc_bound, budget, A20, R20. interval. Qed.

(** [N = 24], [|rho| <= 925/1000]. *)
Definition A24 : R := 11816/10000.
Definition R24 : R := 222/100.
Lemma asin_cover_24 : sin A24 >= 925/1000 + 2 / 10000 /\ A24 < 2.
Proof. unfold A24. split; interval with (i_prec 40). Qed.
Lemma inside_24 : ellipse_inside A24 R24.
Proof. unfold ellipse_inside, A24, R24. split; interval with (i_prec 40). Qed.
Lemma ellipse_24 : ellipse_ok A24 R24.
Proof.
  unfold ellipse_ok, re_sin, cosh', ell_u, ell_v, A24, R24. intros th Hth.
  split; interval with (i_bisect th, i_depth 18).
Qed.
Lemma bound_24 : trunc_bound A24 R24 24 <= budget.
Proof. unfold trunc_bound, budget, A24, R24. interval. Qed.
