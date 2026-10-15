(** The actual mixed-precision central polynomial, through all four
    double-word Horner stages and their shared invariant. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add Binary64Grid IEEE64 IEEE64Mul.
Require Import StageGappa NormalCenterFastTail NormalCenterFastSquare NormalCenterFastHorner
  NormalCenterFastState NormalCenterFastInitial NormalCenterFastStep NormalCentered NormalCenterFastAnalytic.
Open Scope R_scope.

Fixpoint normal_center_polynomial64 zh zl t count :=
  match count with
  | O => normal_center_initial64 zh zl t
  | S n => let '(h,l):=normal_center_polynomial64 zh zl t n in normal_center_step64 (S n)zh zl h l
  end.

Theorem normal_center_polynomial_ieee zh zl t count :
  finite zh -> finite zl -> finite t -> B zh=rndF(B zh+B zl) ->
  Rabs(B zh)<=/4 -> Rabs(B zl)<=bpow radix2 (-56) ->
  bpow radix2 (-66)<=B zh+B zl<=/4 -> bpow radix2 (-15)<=B t<=bpow radix2 (-10) ->
  binary_grid (-118)(B zh) -> binary_grid (-170)(B zl) -> (count<=3)%nat ->
  let '(h,l):=normal_center_polynomial64 zh zl t count in
  normal_center_value h l (normal_center_fast_horner (B zh+B zl)(B t)count)(-237-118*Z.of_nat count).
Proof.
  intros Fzh Fzl Ft Norm Zh Zl Z T Gzh Gzl;induction count as[|n IH];intros N.
  - cbn [normal_center_polynomial64];change(-237-118*Z.of_nat 0)%Z with(-237)%Z.
    apply normal_center_initial_ieee;assumption.
  - specialize(IH ltac:(lia));cbn [normal_center_polynomial64].
    destruct(normal_center_polynomial64 zh zl t n)as[ph pl].
    replace(-237-118*Z.of_nat(S n))%Z with((-237-118*Z.of_nat n)-118)%Z by(rewrite Nat2Z.inj_succ;ring).
    apply(normal_center_step_ieee zh zl (B t)n (-237-118*Z.of_nat n)ph pl);
      try assumption;lia.
Qed.



Definition normal_center_shape64 x :=
  let '(zh,zl,t):=normal_center_square_tail64 x in normal_center_polynomial64 zh zl t 3.

Theorem normal_center_shape_ieee x : finite x -> bpow radix2 (-33)<=Rabs(B x)<=/2 ->
  let '(zh,zl,t):=normal_center_square_tail64 x in
  let '(h,l):=normal_center_shape64 x in
  normal_center_value h l (normal_center_fast_horner (B x*B x)(B t)3)(-591).
Proof.
  intros F X;pose proof(normal_center_square_tail_ieee x F X)as Square.
  pose proof(normal_center_square_grid x F X)as Grid.
  unfold normal_center_shape64,normal_center_square_tail64 in *;destruct(two_prod64 x x)as[zh zl].
  destruct Square as[Fzh [Fzl [Ft [Zh [Zl [Total [Norm Error]]]]]]];destruct Grid as[Gzh Gzl].
  pose proof(normal_center_tail_positive zh Fzh
    ltac:(rewrite Rabs_pos_eq;[exact(proj2 Zh)|pose proof(bpow_gt_0 radix2 (-66));lra]))as T.
  assert(Z : bpow radix2 (-66)<=B zh+B zl<=/4).
  { rewrite Total;pose proof(Rabs_mult(B x)(B x))as Abs;rewrite Rabs_pos_eq in Abs by nra.
    pose proof(Rabs_pos(B x));bpow_num_all;split;nra. }
  pose proof(normal_center_polynomial_ieee zh zl (normal_center_tail64 zh 8)3 Fzh Fzl Ft Norm
    ltac:(rewrite Rabs_pos_eq;[exact(proj2 Zh)|pose proof(bpow_gt_0 radix2 (-66));lra])
    Zl Z T Gzh Gzl ltac:(lia))as Polynomial.
  rewrite Total in Polynomial;exact Polynomial.
Qed.

Local Opaque normal_center_polynomial64 normal_center_square_tail64.

Theorem normal_center_shape_error x : finite x -> bpow radix2 (-33)<=Rabs(B x)<=/2 ->
  let '(h,l):=normal_center_shape64 x in
  Rabs((B h+B l)-normal_shape(B x))<=bpow radix2 (-68)+bpow radix2 (-95).
Proof.
  intros F X;pose proof(normal_center_shape_ieee x F X)as Shape.
  pose proof(normal_center_square_tail_ieee x F X)as Square.
  unfold normal_center_shape64 in *;destruct(normal_center_square_tail64 x)as[[zh zl]t].
  destruct(normal_center_polynomial64 zh zl t 3)as[h l].
  destruct Shape as[_ [_ [_ [_ [_ [_ Evaluation]]]]]];
    destruct Square as[_ [_ [_ [_ [_ [_ [_ Tail]]]]]]].
  rewrite normal_center_fast_horner_shape in Evaluation.
  pose proof(normal_center_mixed_tail_error (B x)(B t)(proj2 X)Tail)as Analytic.
  assert(Cpositive : 0<normal_density_constant)by(unfold normal_density_constant;interval with(i_prec 80)).
  assert(Xpositive : 0<Rabs(B x))by(pose proof(bpow_gt_0 radix2 (-33));lra).
  assert(Approximation : Rabs(normal_center_mixed_shape(B x*B x)(B t)-normal_shape(B x))<=bpow radix2 (-68)).
  { unfold normal_center in Analytic.
    replace(normal_density_constant*B x*normal_center_mixed_shape(B x*B x)(B t)-
      normal_density_constant*B x*normal_shape(B x))with
      (normal_density_constant*B x*(normal_center_mixed_shape(B x*B x)(B t)-normal_shape(B x)))in Analytic by ring.
    rewrite !Rabs_mult,(Rabs_pos_eq normal_density_constant)in Analytic by lra.
    assert(Scale : 0<normal_density_constant*Rabs(B x))by nra;nra. }
  replace((B h+B l)-normal_shape(B x))with
    (((B h+B l)-normal_center_mixed_shape(B x*B x)(B t))+
     (normal_center_mixed_shape(B x*B x)(B t)-normal_shape(B x)))by ring.
  eapply Rle_trans;[apply Rabs_triang|];bpow_num_all;lra.
Qed.
