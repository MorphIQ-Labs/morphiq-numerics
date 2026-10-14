(** Preservation of the lower-degree Horner invariant by one actual
    double-word multiplication and normalized coefficient addition. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add Binary64Grid IEEE64 IEEE64Mul.
Require Import StageGappa NormalCenterFastHorner NormalCenterFastState NormalCenterFastProduct NormalCenterFastAdd.
Open Scope R_scope.

Definition normal_center_step64 count zh zl ph pl :=
  let '(h,l):=mul64 zh zl ph pl in normal_center_add_coefficient64 count h l.

Theorem normal_center_step_ieee zh zl t n e ph pl : (n<3)%nat -> (-851<=e<= -237)%Z ->
  finite zh -> finite zl -> B zh=rndF(B zh+B zl) ->
  Rabs(B zh)<=/4 -> Rabs(B zl)<=bpow radix2 (-56) ->
  bpow radix2 (-66)<=B zh+B zl<=/4 -> bpow radix2 (-15)<=t<=bpow radix2 (-10) ->
  binary_grid (-118)(B zh) -> binary_grid (-170)(B zl) ->
  normal_center_value ph pl (normal_center_fast_horner (B zh+B zl)t n)e ->
  let '(h,l):=normal_center_step64 (S n)zh zl ph pl in
  normal_center_value h l (normal_center_fast_horner (B zh+B zl)t(S n))(e-118).
Proof.
  intros N E Fzh Fzl Znorm Zh Zl Z T Gzh Gzl Previous.
  pose proof(normal_center_value_high_grid ph pl _ e Previous)as Gph.
  destruct Previous as[Fph [Fpl [Pnorm [Ph [Pl [Gpl PreviousError]]]]]].
  assert(Zpositive : 0<B zh+B zl)by(pose proof(bpow_gt_0 radix2 (-66));lra).
  assert(Zrange : 0<=B zh+B zl<=/4)by lra.
  pose proof(normal_center_fast_horner_range (B zh+B zl)t n Zrange T ltac:(lia))as PreviousRange.
  assert(PreviousSize : Rabs(B ph+B pl)<=3).
  { pose proof(Rabs_triang_inv (B ph+B pl)(normal_center_fast_horner(B zh+B zl)t n));bpow_num_all;lra. }
  assert(PreviousNonzero : B ph+B pl<>0).
  { intros Zero;rewrite Zero,Rminus_0_l,Rabs_Ropp in PreviousError;bpow_num_all;lra. }
  assert(Leading : binary_grid (e-118)(B zh*B ph)).
  { eapply binary_grid_finer;[|exact(binary_grid_mul (-118)(-63)(B zh)(B ph)Gzh Gph)];lia. }
  assert(Cross1 : binary_grid (e-118)(B zh*B pl)).
  { replace(e-118)%Z with(-118+e)%Z by lia;apply binary_grid_mul;assumption. }
  assert(Cross2 : binary_grid (e-118)(B zl*B ph)).
  { eapply binary_grid_finer;[|exact(binary_grid_mul (-170)(-63)(B zl)(B ph)Gzl Gph)];lia. }
  assert(Value : Rabs((B zh+B zl)*(B ph+B pl))<=1).
  { rewrite Rabs_mult,(Rabs_pos_eq(B zh+B zl))by lra;pose proof(Rabs_pos(B ph+B pl));nra. }
  assert(Nonzero : (B zh+B zl)*(B ph+B pl)<>0)by(apply Rmult_integral_contrapositive_currified;[lra|exact PreviousNonzero]).
  pose proof(normal_center_mul_ieee (e-118)zh zl ph pl ltac:(lia)Fzh Fzl Fph Fpl Znorm Pnorm
    ltac:(lra)ltac:(eapply Rle_trans;[exact Zl|interval with(i_prec 80)])(proj2 Ph)
    ltac:(eapply Rle_trans;[exact Pl|interval with(i_prec 80)])Leading Cross1 Cross2 Value Nonzero)as Product.
  unfold normal_center_step64;destruct(mul64 zh zl ph pl)as[mh ml].
  destruct Product as[Fmh [Fml [Mnorm [Mh [Ml [Gmh [Gml Error]]]]]]].
  apply(normal_center_add_coefficient_ieee (B zh+B zl)t(S n)(e-118)mh ml);
    try assumption;try lia.
  cbn [normal_center_fast_previous].
  replace((B mh+B ml)-(B zh+B zl)*normal_center_fast_horner(B zh+B zl)t n)with
    (((B mh+B ml)-(B zh+B zl)*(B ph+B pl))+
     (B zh+B zl)*((B ph+B pl)-normal_center_fast_horner(B zh+B zl)t n))by ring.
  eapply Rle_trans;[apply Rabs_triang|];rewrite Rabs_mult,(Rabs_pos_eq(B zh+B zl))by lra.
  assert(Propagation : (B zh+B zl)*Rabs((B ph+B pl)-normal_center_fast_horner(B zh+B zl)t n)<=/4*bpow radix2 (-95)).
  { apply Rmult_le_compat;[lra|apply Rabs_pos|exact(proj2 Z)|exact PreviousError]. }
  bpow_num_all;lra.
Qed.
