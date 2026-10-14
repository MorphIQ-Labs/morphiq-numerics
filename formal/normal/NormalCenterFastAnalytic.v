(** The mixed polynomial's exact algebra and the attenuation of the
    binary64-only tail error by four powers of the squared argument. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Eft RoundingConstant.
Require Import StageGappa NormalCentered NormalCenterFastConstants NormalCenterFastTail
  ErfcxGaussianSeries ErfcxFactorial Expm1Series.
Open Scope R_scope.

Lemma normal_center_fast_tail_coefficient_range n : (4<=n<13)%nat ->
  Rabs(normal_fast_center_coefficient n)<=bpow radix2 (-10).
Proof.
  intros N;destruct(normal_center_fast_tail_word n N)as[_ [Range Error]].
  pose proof(Rabs_triang_inv (normal_fast_center_coefficient n)
    (B(fst(normal_center_fast_word n))))as Bound.
  rewrite Rabs_minus_sym in Bound;bpow_num_all;lra.
Qed.



Lemma normal_center_tail_polynomial_range z count : Rabs z<=/4 -> (count<=8)%nat ->
  Rabs(normal_center_tail_polynomial z count)<=bpow radix2 (-9).
Proof.
  intros Z;induction count as[|n IH];intros N.
  - cbn [normal_center_tail_polynomial];eapply Rle_trans;
      [apply normal_center_fast_tail_coefficient_range;lia|apply bpow_le;lia].
  - specialize(IH ltac:(lia));pose proof(normal_center_fast_tail_coefficient_range (12-S n)ltac:(lia))as C.
    cbn [normal_center_tail_polynomial];eapply Rle_trans;[apply Rabs_triang|];rewrite Rabs_mult.
    assert(P : Rabs z*Rabs(normal_center_tail_polynomial z n)<=/4*bpow radix2 (-9)).
    { apply Rmult_le_compat;[apply Rabs_pos|apply Rabs_pos|exact Z|exact IH]. }
    bpow_num_all;lra.
Qed.

Theorem normal_center_tail_lipschitz z t count : Rabs z<=/4 -> Rabs t<=/4 -> (count<=8)%nat ->
  Rabs(normal_center_tail_polynomial z count-normal_center_tail_polynomial t count)<=bpow radix2 (-8)*Rabs(z-t).
Proof.
  intros Z T;induction count as[|n IH];intros N.
  - cbn [normal_center_tail_polynomial];rewrite Rminus_diag_eq,Rabs_R0 by reflexivity.
    apply Rmult_le_pos;[apply bpow_ge_0|apply Rabs_pos].
  - specialize(IH ltac:(lia));pose proof(normal_center_tail_polynomial_range t n T ltac:(lia))as Range.
    cbn [normal_center_tail_polynomial].
    replace(normal_fast_center_coefficient(12-S n)+z*normal_center_tail_polynomial z n-
      (normal_fast_center_coefficient(12-S n)+t*normal_center_tail_polynomial t n))with
      (z*(normal_center_tail_polynomial z n-normal_center_tail_polynomial t n)+(z-t)*normal_center_tail_polynomial t n)by ring.
    eapply Rle_trans;[apply Rabs_triang|];rewrite !Rabs_mult.
    assert(A : Rabs z*Rabs(normal_center_tail_polynomial z n-normal_center_tail_polynomial t n)<=
      /4*(bpow radix2 (-8)*Rabs(z-t))).
    { apply Rmult_le_compat;[apply Rabs_pos|apply Rabs_pos|exact Z|exact IH]. }
    assert(D : Rabs(z-t)*Rabs(normal_center_tail_polynomial t n)<=Rabs(z-t)*bpow radix2 (-9)).
    { apply Rmult_le_compat_l;[apply Rabs_pos|exact Range]. }
    pose proof(Rabs_pos(z-t));bpow_num_all;lra.
Qed.

Definition normal_center_mixed_shape z tail := normal_fast_center_coefficient 0+
  z*(normal_fast_center_coefficient 1+z*(normal_fast_center_coefficient 2+
  z*(normal_fast_center_coefficient 3+z*tail))).

Lemma normal_center_mixed_polynomial x :
  normal_center_mixed_shape (x*x)(normal_center_tail_polynomial (x*x) 8)=gaussian_sum 12 (x/sqrt 2).
Proof.
  assert(Square : -(x/sqrt 2)*(x/sqrt 2)= -x*x/2).
  { assert(S : sqrt 2*sqrt 2=2)by(apply sqrt_sqrt;lra).
    assert(P : sqrt 2<>0)by interval with(i_prec 80).
    replace(-(x/sqrt 2)*(x/sqrt 2))with(-x*x/(sqrt 2*sqrt 2))by(field;exact P).
    rewrite S;reflexivity. }
  unfold gaussian_sum;rewrite Square.
  unfold normal_center_mixed_shape;cbn [normal_center_tail_polynomial sum_f_R0].
  unfold normal_fast_center_coefficient;binary_factorials;repeat rewrite INR_IZR_INZ;small_numerals;cbn [Nat.sub];field.
Qed.

Theorem normal_center_mixed_tail_error x tail : Rabs x<=/2 ->
  Rabs(tail-normal_center_tail_polynomial(x*x)8)<=bpow radix2 (-61) ->
  Rabs(normal_density_constant*x*normal_center_mixed_shape(x*x)tail-normal_center x)<=
    normal_density_constant*Rabs x*bpow radix2 (-68).
Proof.
  intros X Tail;pose proof(normal_center_degree12_error x X)as Truncation.
  assert(Cpositive : 0<normal_density_constant)by(unfold normal_density_constant;interval with(i_prec 80)).
  assert(Shape : Rabs(normal_center_mixed_shape(x*x)tail-
      normal_center_mixed_shape(x*x)(normal_center_tail_polynomial(x*x)8))<=bpow radix2 (-69)).
  { unfold normal_center_mixed_shape.
    replace(normal_fast_center_coefficient 0+x*x*(normal_fast_center_coefficient 1+x*x*
      (normal_fast_center_coefficient 2+x*x*(normal_fast_center_coefficient 3+x*x*tail)))-
      (normal_fast_center_coefficient 0+x*x*(normal_fast_center_coefficient 1+x*x*
      (normal_fast_center_coefficient 2+x*x*(normal_fast_center_coefficient 3+x*x*normal_center_tail_polynomial(x*x)8)))))with
      ((x*x)^4*(tail-normal_center_tail_polynomial(x*x)8))by ring.
    rewrite Rabs_mult;apply Rabs_le_inv in X.
    assert(Power : Rabs((x*x)^4)<=bpow radix2 (-8))by(bpow_num;interval with(i_prec 100)).
    eapply Rle_trans with(bpow radix2 (-8)*bpow radix2 (-61));
      [apply Rmult_le_compat;[apply Rabs_pos|apply Rabs_pos|exact Power|exact Tail]|].
    rewrite <-bpow_plus;apply Rle_refl. }
  rewrite normal_center_mixed_polynomial in Shape.
  unfold normal_center_polynomial in Truncation.
  replace(normal_density_constant*x*normal_center_mixed_shape(x*x)tail-normal_center x)with
    (normal_density_constant*x*(normal_center_mixed_shape(x*x)tail-gaussian_sum 12(x/sqrt 2))+
     (normal_density_constant*x*gaussian_sum 12(x/sqrt 2)-normal_center x))by ring.
  eapply Rle_trans;[apply Rabs_triang|];rewrite !Rabs_mult,(Rabs_pos_eq normal_density_constant)by lra.
  rewrite(Rabs_minus_sym(normal_density_constant*x*gaussian_sum 12(x/sqrt 2))(normal_center x)).
  assert(A : normal_density_constant*Rabs x*Rabs(normal_center_mixed_shape(x*x)tail-gaussian_sum 12(x/sqrt 2))<=
    normal_density_constant*Rabs x*bpow radix2 (-69)).
  { apply Rmult_le_compat_l;[apply Rmult_le_pos;[lra|apply Rabs_pos]|exact Shape]. }
  bpow_num_all;pose proof(Rabs_pos x);nra.
Qed.

Theorem normal_center_tail_argument_error z x : finite z -> Rabs(B z)<=/4 -> Rabs x<=/2 ->
  Rabs(B z-x*x)<=bpow radix2 (-56) ->
  finite(normal_center_tail64 z 8) /\
  Rabs(B(normal_center_tail64 z 8)-normal_center_tail_polynomial(x*x)8)<=bpow radix2 (-61).
Proof.
  intros Fz Z X Argument.
  destruct(normal_center_tail_ieee z 8 Fz Z ltac:(lia))as[F [_ Error]].
  assert(Square : Rabs(x*x)<=/4)by(rewrite Rabs_mult;pose proof(Rabs_pos x);nra).
  pose proof(normal_center_tail_lipschitz (B z)(x*x)8 Z Square ltac:(lia))as Sensitivity.
  split;[exact F|].
  replace(B(normal_center_tail64 z 8)-normal_center_tail_polynomial(x*x)8)with
    ((B(normal_center_tail64 z 8)-normal_center_tail_polynomial(B z)8)+
     (normal_center_tail_polynomial(B z)8-normal_center_tail_polynomial(x*x)8))by ring.
  eapply Rle_trans;[apply Rabs_triang|].
  bpow_num_all;lra.
Qed.
