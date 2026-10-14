(** Fixed-grid preservation for the actual IEEE double-word operations.
    The existing finite-operation mappings exclude overflow; the grid
    argument independently controls the least nonzero intermediate. *)
From Coq Require Import Reals ZArith Lia Lra.
From Flocq Require Import Core.
From Binary64 Require Import Binary64Add Binary64Mul Binary64Grid IEEE64 IEEE64Add IEEE64Mul.
Open Scope R_scope.

Lemma grid_word_bound x : Rabs(B x)<=bpow radix2 100 -> bnd 1 100 (B x).
Proof. unfold bnd;rewrite Rmult_1_l;trivial. Qed.

Theorem add_grid_ieee e xh xl yh yl :
  finite xh -> finite xl -> finite yh -> finite yl ->
  Rabs(B xh)<=bpow radix2 100 -> Rabs(B xl)<=bpow radix2 100 ->
  Rabs(B yh)<=bpow radix2 100 -> Rabs(B yl)<=bpow radix2 100 ->
  binary_grid e (B xh) -> binary_grid e (B xl) -> binary_grid e (B yh) -> binary_grid e (B yl) ->
  let '(h,l):=add64 xh xl yh yl in binary_grid e (B h) /\ binary_grid e (B l).
Proof.
  intros Fxh Fxl Fyh Fyl Xh Xl Yh Yl Gxh Gxl Gyh Gyl.
  destruct(add64_ok 1 100 xh xl yh yl Fxh Fxl Fyh Fyl
    (grid_word_bound _ Xh)(grid_word_bound _ Xl)(grid_word_bound _ Yh)(grid_word_bound _ Yl)
    ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia))as[_ [_ Value]].
  pose proof(binary_grid_add_dw e (B xh)(B xl)(B yh)(B yl)Gxh Gxl Gyh Gyl)as Grid.
  rewrite <-Value in Grid;destruct(add64 xh xl yh yl)as[h l];exact Grid.
Qed.

Theorem mul_f64_grid_ieee e xh xl y :
  finite xh -> finite xl -> finite y ->
  Rabs(B xh)<=bpow radix2 100 -> Rabs(B xl)<=bpow radix2 100 -> Rabs(B y)<=bpow radix2 100 ->
  in_two_prod_domain(B xh)(B y) -> binary_grid e (B xh*B y) -> binary_grid e (B xl*B y) ->
  let '(h,l):=mul_f64_64 xh xl y in binary_grid e (B h) /\ binary_grid e (B l).
Proof.
  intros Fxh Fxl Fy Xh Xl Y Domain Leading Cross.
  destruct(mul_f64_64_ok 100 100 xh xl y Fxh Fxl Fy
    (grid_word_bound _ Xh)(grid_word_bound _ Xl)(grid_word_bound _ Y)
    ltac:(lia)ltac:(lia)ltac:(lia))as[_ [_ [Value _]]].
  pose proof(binary_grid_mul_f64 e (B xh)(B xl)(B y)(B_fmt xh)(B_fmt y)Domain Leading Cross)as Grid.
  rewrite <-Value in Grid;destruct(mul_f64_64 xh xl y)as[h l];exact Grid.
Qed.

Theorem mul_grid_ieee e xh xl yh yl :
  finite xh -> finite xl -> finite yh -> finite yl ->
  Rabs(B xh)<=bpow radix2 100 -> Rabs(B xl)<=bpow radix2 100 ->
  Rabs(B yh)<=bpow radix2 100 -> Rabs(B yl)<=bpow radix2 100 ->
  in_two_prod_domain(B xh)(B yh) ->
  binary_grid e (B xh*B yh) -> binary_grid e (B xh*B yl) -> binary_grid e (B xl*B yh) ->
  let '(h,l):=mul64 xh xl yh yl in binary_grid e (B h) /\ binary_grid e (B l).
Proof.
  intros Fxh Fxl Fyh Fyl Xh Xl Yh Yl Domain Leading Cross1 Cross2.
  destruct(mul64_ok 100 xh xl yh yl Fxh Fxl Fyh Fyl
    (grid_word_bound _ Xh)(grid_word_bound _ Xl)(grid_word_bound _ Yh)(grid_word_bound _ Yl)
    ltac:(lia))as[_ [_ Value]].
  pose proof(binary_grid_mul_dw e (B xh)(B xl)(B yh)(B yl)(B_fmt xh)(B_fmt yh)Domain Leading Cross1 Cross2)as Grid.
  rewrite <-Value in Grid;destruct(mul64 xh xl yh yl)as[h l];exact Grid.
Qed.
