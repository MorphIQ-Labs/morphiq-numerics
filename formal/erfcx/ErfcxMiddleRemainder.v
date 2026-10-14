(** The first omitted term after the middle tail's 32-term series. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
Require Import StageGappa ErfcxFactorial ErfcxAsymptotic ErfcxTailIntegral.
Open Scope R_scope.

Lemma middle_asymptotic_next t : 0<=t<=/2^8 ->
  asym_next_coefficient 31 t*INR(fact(2*S 31))<=/2^140.
Proof.
  intros T. unfold asym_next_coefficient. binary_factorials.
  interval with (i_prec 180).
Qed.

Theorem middle_asymptotic_remainder t : 0<=t<=/2^8 ->
  0<=tail_integral t-asym_polynomial 31 t<=/2^140.
Proof.
  intros T. pose proof (tail_integral_asymptotic 31 t (proj1 T)) as E.
  replace ((-1)^S 31) with 1 in E by (simpl pow; ring).
  rewrite Rmult_1_l in E. pose proof (middle_asymptotic_next t T). lra.
Qed.
