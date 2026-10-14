(** The first double-word Horner stage: multiply the exact square by the
    binary64 tail, then add coefficient three. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add Binary64Grid IEEE64 IEEE64Mul.
Require Import StageGappa NormalCenterFastHorner NormalCenterFastState NormalCenterFastProduct NormalCenterFastAdd.
Open Scope R_scope.

Definition normal_center_initial64 zh zl t :=
  let '(h,l):=mul_f64_64 zh zl t in normal_center_add_coefficient64 0 h l.

Theorem normal_center_initial_ieee zh zl t :
  finite zh -> finite zl -> finite t -> B zh=rndF(B zh+B zl) ->
  Rabs(B zh)<=/4 -> Rabs(B zl)<=bpow radix2 (-56) ->
  bpow radix2 (-66)<=B zh+B zl<=/4 -> bpow radix2 (-15)<=B t<=bpow radix2 (-10) ->
  binary_grid (-118)(B zh) -> binary_grid (-170)(B zl) ->
  let '(h,l):=normal_center_initial64 zh zl t in
  normal_center_value h l (normal_center_fast_horner (B zh+B zl)(B t)0)(-237).
Proof.
  intros Fzh Fzl Ft Znorm Zh Zl Z T Gzh Gzl.
  assert(Gt : binary_grid (-67)(B t)).
  { apply(binary_grid_binary64 t (-15));rewrite Rabs_pos_eq;[exact(proj1 T)|pose proof(bpow_gt_0 radix2 (-15));lra]. }
  assert(Leading : binary_grid (-237)(B zh*B t)).
  { eapply binary_grid_finer;[|exact(binary_grid_mul (-118)(-67)(B zh)(B t)Gzh Gt)];lia. }
  assert(Cross : binary_grid (-237)(B zl*B t))by(exact(binary_grid_mul (-170)(-67)(B zl)(B t)Gzl Gt)).
  assert(Zpositive : 0<B zh+B zl)by(pose proof(bpow_gt_0 radix2 (-66));lra).
  assert(Tpositive : 0<B t)by(pose proof(bpow_gt_0 radix2 (-15));lra).
  assert(Value : Rabs((B zh+B zl)*B t)<=1).
  { rewrite Rabs_pos_eq by nra;bpow_num_all;nra. }
  assert(Nonzero : (B zh+B zl)*B t<>0)by nra.
  pose proof(normal_center_mul_f64_ieee (-237)zh zl t ltac:(lia)Fzh Fzl Ft Znorm
    ltac:(lra)ltac:(eapply Rle_trans;[exact Zl|interval with(i_prec 80)])
    ltac:(rewrite Rabs_pos_eq by lra;bpow_num_all;lra)
    Leading Cross Value Nonzero)as Product.
  unfold normal_center_initial64;destruct(mul_f64_64 zh zl t)as[ph pl].
  destruct Product as[Fph [Fpl [Pnorm [Ph [Pl [Gph [Gpl Error]]]]]]].
  apply(normal_center_add_coefficient_ieee (B zh+B zl)(B t)0 (-237)ph pl);
    try assumption;try lia.
  - split;lra.
  - cbn [normal_center_fast_previous];eapply Rle_trans;[exact Error|];apply bpow_le;lia.
Qed.
