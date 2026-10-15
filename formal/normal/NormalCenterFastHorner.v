(** The four lower-degree Horner stages. Their coefficient dominates the
    incoming product, giving explicit cancellation and magnitude bounds. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
Require Import StageGappa NormalCenterFastConstants NormalCenterFastAnalytic ErfcxFactorial Expm1Series.
Open Scope R_scope.

Fixpoint normal_center_fast_horner z t count : R :=
  match count with
  | O => normal_fast_center_coefficient 3+z*t
  | S n => normal_fast_center_coefficient(3-S n)+z*normal_center_fast_horner z t n
  end.

Definition normal_center_fast_previous z t count :=
  match count with O => t | S n => normal_center_fast_horner z t n end.

Lemma normal_center_fast_horner_unfold z t count :
  normal_center_fast_horner z t count=normal_fast_center_coefficient(3-count)+z*normal_center_fast_previous z t count.
Proof. destruct count;reflexivity. Qed.

Lemma normal_center_fast_horner_shape z t :
  normal_center_fast_horner z t 3=normal_center_mixed_shape z t.
Proof. reflexivity. Qed.

Theorem normal_center_fast_horner_range z t count : 0<=z<=/4 ->
  bpow radix2 (-15)<=t<=bpow radix2 (-10) -> (count<=3)%nat ->
  bpow radix2 (-10)<=Rabs(normal_center_fast_horner z t count)<=2.
Proof.
  intros Z T N;assert(Cases : count=0%nat \/ count=1%nat \/ count=2%nat \/ count=3%nat)by lia.
  destruct Cases as[ -> | [ -> | [ -> | -> ] ] ];cbn [normal_center_fast_horner];
    unfold normal_fast_center_coefficient;binary_factorials;repeat rewrite INR_IZR_INZ;
    small_numerals;cbn [Nat.sub];bpow_num_all;split;interval with(i_prec 180).
Qed.

Theorem normal_center_fast_horner_dominance z t count : 0<=z<=/4 ->
  bpow radix2 (-15)<=t<=bpow radix2 (-10) -> (count<=3)%nat ->
  Rabs(z*normal_center_fast_previous z t count)<=Rabs(normal_fast_center_coefficient(3-count))/4.
Proof.
  intros Z T N;assert(Cases : count=0%nat \/ count=1%nat \/ count=2%nat \/ count=3%nat)by lia.
  destruct Cases as[ -> | [ -> | [ -> | -> ] ] ];cbn [normal_center_fast_previous normal_center_fast_horner];
    unfold normal_fast_center_coefficient;binary_factorials;repeat rewrite INR_IZR_INZ;
    small_numerals;cbn [Nat.sub];bpow_num_all;interval with(i_prec 180).
Qed.

Lemma normal_center_fast_horner_cancellation z t count : 0<=z<=/4 ->
  bpow radix2 (-15)<=t<=bpow radix2 (-10) -> (count<=3)%nat ->
  Rabs(normal_fast_center_coefficient(3-count))+Rabs(z*normal_center_fast_previous z t count)<=
    2*Rabs(normal_center_fast_horner z t count).
Proof.
  intros Z T N;pose proof(normal_center_fast_horner_dominance z t count Z T N)as Dominant.
  rewrite normal_center_fast_horner_unfold.
  pose proof(Rabs_triang_inv (normal_fast_center_coefficient(3-count))
    (normal_fast_center_coefficient(3-count)+z*normal_center_fast_previous z t count))as Difference.
  replace(normal_fast_center_coefficient(3-count)-
    (normal_fast_center_coefficient(3-count)+z*normal_center_fast_previous z t count))with
    (-(z*normal_center_fast_previous z t count))in Difference by ring.
  rewrite Rabs_Ropp in Difference;pose proof(Rabs_pos(normal_fast_center_coefficient(3-count)));lra.
Qed.
