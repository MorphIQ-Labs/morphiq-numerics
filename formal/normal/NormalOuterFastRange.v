(** A tighter tail bound at the central/outer boundary keeps both outer
    complementary compositions within their existing relative guard. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Interval Require Import Tactic.
From Flocq Require Import Core.
Require Import NormalCentered NormalTailAnalytic NormalTailRange ErfcxGaussianSeries.
Open Scope R_scope.

Theorem normal_outer_tail_tight x : /2<=x -> 0<normal_tail x<=5/16.
Proof.
  intros X;pose proof(normal_tail_range x ltac:(lra))as Positive.
  pose proof(normal_tail_decreasing (/2)x ltac:(split;lra))as Upper.
  rewrite(normal_tail_complement(/2))in Upper.
  pose proof(normal_center_polynomial_error 1 (/2))as Error.
  assert(Lower : 3/16<=normal_center_polynomial 1 (/2)-
    normal_density_constant*Rabs(/2)*((((/2)*(/2)/2)^2)/INR(fact 2))).
  { unfold normal_center_polynomial,normal_density_constant,gaussian_sum.
    cbn [sum_f_R0 fact Nat.mul Nat.add Nat.sub INR];interval with(i_prec 100). }
  apply Rabs_le_inv in Error;split;lra.
Qed.
