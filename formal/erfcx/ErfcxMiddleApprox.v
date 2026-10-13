(** CoqInterval verification of the stored middle polynomial against the
    exact 32-term asymptotic polynomial. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Gappa Require Import Gappa_library.
From Interval Require Import Tactic.
Require Import StageGappa ErfcxFactorial ErfcxAsymptotic.
Require Import ErfcxEntryTables ErfcxMiddlePolynomial.
Open Scope R_scope.

Lemma middle_polynomial_approx t : /2^18<=t<=/2^8 ->
  Rabs (correction_exact t-asym_polynomial 31 t)<=3/2^76.
Proof.
  intros T.
  unfold correction_exact, poly_exact, pa0_r,pa1_r,pa2_r,pa3_r,pa4_r,pa5_r,pa6_r,pa7_r.
  unfold float2R,F2R; cbn [Fnum Fexp]. bpow_num.
  unfold asym_polynomial, asym_coefficient. cbn [sum_f_R0].
  binary_factorials.
  apply Rabs_le; split;
    interval with (i_taylor t, i_degree 10, i_bisect t, i_prec 180, i_depth 12).
Qed.
