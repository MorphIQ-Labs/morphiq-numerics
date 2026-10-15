(** The regular central value, including the final density-times-argument
    multiplication and the mixed polynomial's complete analytic remainder. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add Binary64Mul Binary64Grid IEEE64 IEEE64Mul.
Require Import StageGappa NormalCentered NormalCenterSmall NormalCenterFastSquare
  NormalCenterFastState NormalCenterFastProduct NormalCenterFastLinear NormalCenterFastPolynomial.
Open Scope R_scope.

Definition normal_center_regular64 x :=
  let '(ah,al):=normal_center_small64 x in
  let '(bh,bl):=normal_center_shape64 x in mul64 ah al bh bl.

Theorem normal_center_regular_ieee x : finite x -> bpow radix2 (-33)<=Rabs(B x)<=/2 ->
  let '(h,l):=normal_center_regular64 x in
  finite h /\ finite l /\ B h=rndF(B h+B l) /\ binary_grid (-679)(B l) /\
  Rabs((B h+B l)-normal_center(B x))<=normal_density_constant*Rabs(B x)*bpow radix2 (-67).
Proof.
  intros Fx X;pose proof(normal_center_linear_regular_ieee x Fx X)as Linear.
  pose proof(normal_center_shape_ieee x Fx X)as Shape;pose proof(normal_center_shape_error x Fx X)as ShapeError.
  destruct(normal_center_square_tail64 x)as[[zh zl]t].
  unfold normal_center_regular64;destruct(normal_center_small64 x)as[ah al];destruct(normal_center_shape64 x)as[bh bl].
  pose proof(normal_center_value_high_grid bh bl _ (-591)Shape)as Gbh.
  destruct Linear as[Fah [Fal [Anorm [Ah [Al [Gah [Gal LinearError]]]]]]].
  destruct Shape as[Fbh [Fbl [Bnorm [Bh [Bl [Gbl _]]]]]].
  assert(C : 3/8<=normal_density_constant<=/2)by(unfold normal_density_constant;split;interval with(i_prec 100)).
  pose proof(normal_shape_range (B x)(proj2 X))as ShapeRange.
  set(scale:=normal_density_constant*Rabs(B x))in *.
  assert(Scale : 0<scale<=/4).
  { unfold scale;pose proof(bpow_gt_0 radix2 (-33));split;nra. }
  assert(TargetAbs : Rabs(normal_density_constant*B x)=scale).
  { unfold scale;rewrite Rabs_mult,(Rabs_pos_eq normal_density_constant)by lra;reflexivity. }
  assert(ASize : Rabs(B ah+B al)<=2*scale).
  { pose proof(Rabs_triang_inv (B ah+B al)(normal_density_constant*B x))as Bound;
      rewrite TargetAbs in Bound;bpow_num_all;nra. }
  assert(ANonzero : B ah+B al<>0).
  { intros Zero;rewrite Zero,Rminus_0_l,Rabs_Ropp,TargetAbs in LinearError;bpow_num_all;nra. }
  assert(BSize : 0<B bh+B bl<=2).
  { apply Rabs_le_inv in ShapeError;bpow_num_all;split;lra. }
  assert(Leading : binary_grid (-679)(B ah*B bh)).
  { eapply binary_grid_finer;[|exact(binary_grid_mul (-88)(-63)(B ah)(B bh)Gah Gbh)];lia. }
  assert(Cross1 : binary_grid (-679)(B ah*B bl)).
  { exact(binary_grid_mul (-88)(-591)(B ah)(B bl)Gah Gbl). }
  assert(Cross2 : binary_grid (-679)(B al*B bh)).
  { eapply binary_grid_finer;[|exact(binary_grid_mul (-193)(-63)(B al)(B bh)Gal Gbh)];lia. }
  assert(Value : Rabs((B ah+B al)*(B bh+B bl))<=1).
  { rewrite Rabs_mult,(Rabs_pos_eq(B bh+B bl))by lra;pose proof(Rabs_pos(B ah+B al));nra. }
  assert(Nonzero : (B ah+B al)*(B bh+B bl)<>0).
  { apply Rmult_integral_contrapositive_currified;[exact ANonzero|lra]. }
  pose proof(normal_center_mul_ieee (-679)ah al bh bl ltac:(lia)Fah Fal Fbh Fbl Anorm Bnorm
    ltac:(lra)ltac:(eapply Rle_trans;[exact Al|interval with(i_prec 80)])(proj2 Bh)
    ltac:(eapply Rle_trans;[exact Bl|interval with(i_prec 80)])Leading Cross1 Cross2 Value Nonzero)as Product.
  pose proof(normal_center_grid_domain (-679)(B ah)(B bh)ltac:(lia)Leading)as Domain.
  pose proof(mul_ieee ah al bh bl Fah Fal Anorm Fbh Fbl Bnorm
    (normal_center_word_bound ah 508 ltac:(lia)ltac:(lra))
    (normal_center_word_bound al 508 ltac:(lia)ltac:(eapply Rle_trans;[exact Al|interval with(i_prec 80)]))
    (normal_center_word_bound bh 508 ltac:(lia)(proj2 Bh))
    (normal_center_word_bound bl 508 ltac:(lia)ltac:(eapply Rle_trans;[exact Bl|interval with(i_prec 80)]))
    Domain (binary_grid_normal (-679)(B ah*B bl)ltac:(lia)Cross1)(binary_grid_normal (-679)(B al*B bh)ltac:(lia)Cross2))as Relative.
  destruct(mul64 ah al bh bl)as[h l];destruct Product as[Fh [Fl [Norm [_ [_ [_ [Grid _]]]]]]];
    destruct Relative as[_ [_ Relative]].
  assert(Rel : Rabs(((B h+B l)-(B ah+B al)*(B bh+B bl))/((B ah+B al)*(B bh+B bl)))<=bpow radix2 (-103)).
  { eapply Rle_trans;[apply Rlt_le;exact Relative|];unfold prec;bpow_num;interval with(i_prec 200). }
  assert(MultiplyError : Rabs((B h+B l)-(B ah+B al)*(B bh+B bl))<=4*scale*bpow radix2 (-103)).
  { replace((B h+B l)-(B ah+B al)*(B bh+B bl))with
      ((((B h+B l)-(B ah+B al)*(B bh+B bl))/((B ah+B al)*(B bh+B bl)))*((B ah+B al)*(B bh+B bl)))by(field;split;lra).
    rewrite !Rabs_mult,(Rabs_pos_eq(B bh+B bl))by lra.
    assert(P : Rabs(B ah+B al)*(B bh+B bl)<=4*scale)by(pose proof(Rabs_pos(B ah+B al));nra).
    assert(Positive : 0<=Rabs(B ah+B al)*(B bh+B bl))by(apply Rmult_le_pos;[apply Rabs_pos|lra]).
    pose proof(bpow_ge_0 radix2 (-103));nra. }
  split;[exact Fh|];split;[exact Fl|];split;[exact Norm|];split;[exact Grid|].
  unfold normal_center.
  replace((B h+B l)-normal_density_constant*B x*normal_shape(B x))with
    (((B h+B l)-(B ah+B al)*(B bh+B bl))+
     (((B ah+B al)-normal_density_constant*B x)*(B bh+B bl)+
      (normal_density_constant*B x)*((B bh+B bl)-normal_shape(B x))))by ring.
  eapply Rle_trans;[apply Rabs_triang|];eapply Rle_trans;[apply Rplus_le_compat_l,Rabs_triang|].
  rewrite !Rabs_mult,(Rabs_pos_eq normal_density_constant),(Rabs_pos_eq(B bh+B bl))by lra;fold scale.
  assert(LinearPart : Rabs((B ah+B al)-normal_density_constant*B x)*(B bh+B bl)<=2*scale*bpow radix2 (-103)).
  { pose proof(Rabs_pos((B ah+B al)-normal_density_constant*B x));pose proof(bpow_ge_0 radix2 (-103));nra. }
  assert(ShapePart : scale*Rabs((B bh+B bl)-normal_shape(B x))<=scale*(bpow radix2 (-68)+bpow radix2 (-95))).
  { apply Rmult_le_compat_l;lra. }
  assert(Budget : 6*bpow radix2 (-103)+bpow radix2 (-68)+bpow radix2 (-95)<=bpow radix2 (-67))
    by(bpow_num;interval with(i_prec 180)).
  fold scale;nra.
Qed.
