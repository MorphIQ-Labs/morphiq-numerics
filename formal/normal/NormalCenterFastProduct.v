(** IEEE products for the central Horner composition. The fixed grids
    discharge the cross-product underflow conditions of the shared kernels. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add Binary64Mul Binary64Grid IEEE64 IEEE64Mul IEEE64Grid IEEE64NormalizedMul RoundingConstant.
Require Import StageGappa NormalCenterFastTail.
Open Scope R_scope.

Definition normal_center_product_value h l value e :=
  finite h /\ finite l /\ B h=rndF(B h+B l) /\
  Rabs(B h)<=2 /\ Rabs(B l)<=bpow radix2 (-53) /\
  binary_grid e (B h) /\ binary_grid e (B l) /\ Rabs((B h+B l)-value)<=bpow radix2 (-103).

Lemma normal_center_product_bounds h l value e :
  finite h -> finite l -> B h=rndF(B h+B l) ->
  Rabs value<=1 -> value<>0 ->
  Rabs(((B h+B l)-value)/value)<=bpow radix2 (-103) -> binary_grid e (B h) -> binary_grid e (B l) ->
  normal_center_product_value h l value e.
Proof.
  intros Fh Fl Norm V Nonzero Relative GridHigh GridLow.
  assert(Error : Rabs((B h+B l)-value)<=bpow radix2 (-103)).
  { replace((B h+B l)-value)with((((B h+B l)-value)/value)*value)by(field;exact Nonzero).
    rewrite Rabs_mult;pose proof(Rabs_pos value);pose proof(Rabs_pos(((B h+B l)-value)/value)).
    assert(P : 0<=bpow radix2 (-103))by apply bpow_ge_0;nra. }
  assert(SumRange : Rabs(B h+B l)<=2).
  { pose proof(Rabs_triang_inv (B h+B l)value);bpow_num_all;lra. }
  assert(High : Rabs(B h)<=2).
  { rewrite Norm;change 2 with(bpow radix2 1);apply normal_center_round_bound;[exact SumRange|lia]. }
  pose proof(rnd_err_below(B h+B l)1 ltac:(lia)SumRange)as Rounded.
  rewrite <-Norm in Rounded;change(1-54)%Z with(-53)%Z in Rounded.
  assert(Low : Rabs(B l)<=bpow radix2 (-53)).
  { replace(B h-(B h+B l))with(-B l)in Rounded by ring;rewrite Rabs_Ropp in Rounded;exact Rounded. }
  unfold normal_center_product_value;tauto.
Qed.

Lemma normal_center_grid_domain e x y : (-969<=e)%Z -> binary_grid e (x*y) -> in_two_prod_domain x y.
Proof.
  intros E Grid;destruct(binary_grid_nonzero e (x*y)Grid)as[Zero|Lower];[left;exact Zero|right].
  eapply Rle_trans;[|exact Lower];apply bpow_le;exact E.
Qed.

Lemma normal_center_word_bound a e : (2<=e)%Z -> Rabs(B a)<=4 -> Rabs(B a)<=bpow radix2 e.
Proof.
  intros E A;eapply Rle_trans;[exact A|];change 4 with(bpow radix2 2);apply bpow_le;exact E.
Qed.

Theorem normal_center_mul_f64_ieee e xh xl y : (-969<=e)%Z ->
  finite xh -> finite xl -> finite y -> B xh=rndF(B xh+B xl) ->
  Rabs(B xh)<=4 -> Rabs(B xl)<=4 -> Rabs(B y)<=4 ->
  binary_grid e (B xh*B y) -> binary_grid e (B xl*B y) ->
  Rabs((B xh+B xl)*B y)<=1 -> (B xh+B xl)*B y<>0 ->
  let '(h,l):=mul_f64_64 xh xl y in normal_center_product_value h l ((B xh+B xl)*B y)e.
Proof.
  intros E Fxh Fxl Fy X Xh Xl Y Leading Cross Value Nonzero.
  pose proof(normal_center_grid_domain e (B xh)(B y)E Leading)as Domain.
  pose proof(binary_grid_normal e (B xl*B y)ltac:(lia)Cross)as NormalCross.
  pose proof(mul_f64_ieee xh xl y Fxh Fxl Fy X
    (normal_center_word_bound _ 508 ltac:(lia)Xh)(normal_center_word_bound _ 508 ltac:(lia)Xl)
    (normal_center_word_bound _ 508 ltac:(lia)Y)Domain NormalCross)as Product.
  pose proof(mul_f64_normalized_ieee xh xl y Fxh Fxl Fy X
    (normal_center_word_bound _ 508 ltac:(lia)Xh)(normal_center_word_bound _ 508 ltac:(lia)Xl)
    (normal_center_word_bound _ 508 ltac:(lia)Y)Domain NormalCross)as Normalized.
  pose proof(mul_f64_grid_ieee e xh xl y Fxh Fxl Fy
    (normal_center_word_bound _ 100 ltac:(lia)Xh)(normal_center_word_bound _ 100 ltac:(lia)Xl)
    (normal_center_word_bound _ 100 ltac:(lia)Y)Domain Leading Cross)as Grid.
  destruct(mul_f64_64 xh xl y)as[h l];destruct Product as[Fh [Fl Error]];
    destruct Normalized as[_ [_ Norm]];destruct Grid as[Gh Gl].
  apply normal_center_product_bounds;try assumption.
  eapply Rle_trans;[exact Error|];unfold prec;bpow_num;interval with(i_prec 200).
Qed.

Theorem normal_center_mul_ieee e xh xl yh yl : (-969<=e)%Z ->
  finite xh -> finite xl -> finite yh -> finite yl ->
  B xh=rndF(B xh+B xl) -> B yh=rndF(B yh+B yl) ->
  Rabs(B xh)<=4 -> Rabs(B xl)<=4 -> Rabs(B yh)<=4 -> Rabs(B yl)<=4 ->
  binary_grid e (B xh*B yh) -> binary_grid e (B xh*B yl) -> binary_grid e (B xl*B yh) ->
  Rabs((B xh+B xl)*(B yh+B yl))<=1 -> (B xh+B xl)*(B yh+B yl)<>0 ->
  let '(h,l):=mul64 xh xl yh yl in normal_center_product_value h l ((B xh+B xl)*(B yh+B yl))e.
Proof.
  intros E Fxh Fxl Fyh Fyl X Y Xh Xl Yh Yl Leading Cross1 Cross2 Value Nonzero.
  pose proof(normal_center_grid_domain e (B xh)(B yh)E Leading)as Domain.
  pose proof(binary_grid_normal e (B xh*B yl)ltac:(lia)Cross1)as NormalCross1.
  pose proof(binary_grid_normal e (B xl*B yh)ltac:(lia)Cross2)as NormalCross2.
  pose proof(mul_ieee xh xl yh yl Fxh Fxl X Fyh Fyl Y
    (normal_center_word_bound _ 508 ltac:(lia)Xh)(normal_center_word_bound _ 508 ltac:(lia)Xl)
    (normal_center_word_bound _ 508 ltac:(lia)Yh)(normal_center_word_bound _ 508 ltac:(lia)Yl)
    Domain NormalCross1 NormalCross2)as Product.
  pose proof(mul_normalized_ieee xh xl yh yl Fxh Fxl X Fyh Fyl Y
    (normal_center_word_bound _ 508 ltac:(lia)Xh)(normal_center_word_bound _ 508 ltac:(lia)Xl)
    (normal_center_word_bound _ 508 ltac:(lia)Yh)(normal_center_word_bound _ 508 ltac:(lia)Yl)
    Domain NormalCross1 NormalCross2)as Normalized.
  pose proof(mul_grid_ieee e xh xl yh yl Fxh Fxl Fyh Fyl
    (normal_center_word_bound _ 100 ltac:(lia)Xh)(normal_center_word_bound _ 100 ltac:(lia)Xl)
    (normal_center_word_bound _ 100 ltac:(lia)Yh)(normal_center_word_bound _ 100 ltac:(lia)Yl)
    Domain Leading Cross1 Cross2)as Grid.
  destruct(mul64 xh xl yh yl)as[h l];destruct Product as[Fh [Fl Error]];
    destruct Normalized as[_ [_ Norm]];destruct Grid as[Gh Gl].
  apply normal_center_product_bounds;try assumption.
  eapply Rle_trans;[apply Rlt_le;exact Error|];unfold prec;bpow_num;interval with(i_prec 200).
Qed.
