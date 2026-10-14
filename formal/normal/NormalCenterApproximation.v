(** Integrated Gaussian identity, truncation, and argument sensitivity for
    the accurate centered-CDF polynomial. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
Require Import StageGappa NormalCentered NormalCenterConstants NormalCenterHorner
  ErfcxGaussianSeries ErfcxFactorial Expm1Series.
Open Scope R_scope.

Lemma normal_center_horner_polynomial x :
  normal_center_horner (-x*x/2) 40=gaussian_sum 40 (x/sqrt 2).
Proof.
  assert (Square : -(x/sqrt 2)*(x/sqrt 2)= -x*x/2).
  { assert (S : sqrt 2*sqrt 2=2) by (apply sqrt_sqrt;lra).
    assert (P : sqrt 2<>0) by interval with(i_prec 80).
    replace (-(x/sqrt 2)*(x/sqrt 2)) with(-x*x/(sqrt 2*sqrt 2)) by (field;exact P).
    rewrite S;reflexivity. }
  unfold gaussian_sum;rewrite Square.
  cbn [sum_f_R0 normal_center_horner]. unfold normal_center_coefficient.
  binary_factorials. repeat rewrite INR_IZR_INZ. small_numerals. field.
Qed.

Theorem normal_center_horner_truncation x : Rabs x<=/2 ->
  Rabs(normal_center_horner (-x*x/2) 40-normal_shape x)<=bpow radix2 (-280).
Proof.
  intros X. rewrite normal_center_horner_polynomial,Rabs_minus_sym.
  eapply Rle_trans;[apply gaussian_integral_remainder|].
  binary_factorials. apply Rabs_le_inv in X.
  bpow_num. interval with(i_prec 400).
Qed.

Theorem normal_center_horner_lipschitz z t count : Rabs z<=/4 -> Rabs t<=/4 ->
  Rabs(normal_center_horner z count-normal_center_horner t count)<=4*Rabs(z-t).
Proof.
  intros Z T. induction count as [|n IH].
  - cbn [normal_center_horner];rewrite Rminus_diag_eq,Rabs_R0 by reflexivity.
    pose proof(Rabs_pos(z-t));lra.
  - cbn [normal_center_horner].
    replace(normal_center_coefficient (40-S n)+z*normal_center_horner z n-
      (normal_center_coefficient (40-S n)+t*normal_center_horner t n)) with
      (z*(normal_center_horner z n-normal_center_horner t n)+(z-t)*normal_center_horner t n) by ring.
    eapply Rle_trans;[apply Rabs_triang|]. rewrite !Rabs_mult.
    pose proof(normal_center_horner_range t n T) as Range.
    assert (A : Rabs z*Rabs(normal_center_horner z n-normal_center_horner t n)<=
      (/4)*(4*Rabs(z-t))).
    { apply Rmult_le_compat;[apply Rabs_pos|apply Rabs_pos|exact Z|exact IH]. }
    assert (B : Rabs(z-t)*Rabs(normal_center_horner t n)<=Rabs(z-t)*2).
    { apply Rmult_le_compat_l;[apply Rabs_pos|exact Range]. }
    pose proof(Rabs_pos(z-t));lra.
Qed.
