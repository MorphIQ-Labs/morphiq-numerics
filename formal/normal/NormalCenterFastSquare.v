(** Exact double-word squaring and the tail evaluated at its high word.
    The low word is retained for the lower-degree polynomial stages. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add Binary64Mul Binary64Grid IEEE64 IEEE64Mul IEEE64Eft RoundingConstant.
Require Import StageGappa NormalCenterFastTail NormalCenterFastAnalytic.
Open Scope R_scope.

Definition normal_center_square_tail64 x :=
  let '(h,l):=two_prod64 x x in(h,l,normal_center_tail64 h 8).

Theorem normal_center_square_tail_ieee x : finite x ->
  bpow radix2 (-33)<=Rabs(B x)<=/2 ->
  let '(h,l,t):=normal_center_square_tail64 x in
  finite h /\ finite l /\ finite t /\
  bpow radix2 (-66)<=B h<=/4 /\ Rabs(B l)<=bpow radix2 (-56) /\
  B h+B l=B x*B x /\ B h=rndF(B h+B l) /\
  Rabs(B t-normal_center_tail_polynomial(B x*B x)8)<=bpow radix2 (-61).
Proof.
  intros F X.
  assert(ProductRange : bpow radix2 (-66)<=B x*B x<=/4).
  { pose proof(Rabs_pos(B x));pose proof(Rabs_mult(B x)(B x))as Abs.
    rewrite Rabs_pos_eq in Abs by nra;bpow_num_all;split;nra. }
  assert(Domain : in_two_prod_domain(B x)(B x)).
  { right;rewrite Rabs_pos_eq by nra;eapply Rle_trans with(bpow radix2 (-66));[apply bpow_le;lia|exact(proj1 ProductRange)]. }
  pose proof(two_prod_ieee (-1)(-1)x x F F
    ltac:(change(bpow radix2 (-1))with(/2);exact(proj2 X))
    ltac:(change(bpow radix2 (-1))with(/2);exact(proj2 X))
    ltac:(lia)ltac:(lia)ltac:(lia)Domain)as Product.
  unfold normal_center_square_tail64;destruct(two_prod64 x x)as[h l].
  destruct Product as[Fh [Fl [High Total]]].
  assert(Hrange : bpow radix2 (-66)<=B h<=/4).
  { rewrite High;split.
    - apply round_ge_generic;[exact _|exact _| |exact(proj1 ProductRange)].
      apply generic_format_bpow;unfold FLT_exp,emin,prec;lia.
    - change(/4)with(bpow radix2 (-2));apply round_le_generic;[exact _|exact _| |exact(proj2 ProductRange)].
      apply generic_format_bpow;unfold FLT_exp,emin,prec;lia. }
  assert(Input : Rabs(B x*B x)<=bpow radix2 (-2)).
  { rewrite Rabs_pos_eq by nra;exact(proj2 ProductRange). }
  pose proof(rnd_err_below _ (-2)ltac:(lia)Input)as Error;rewrite <-High in Error.
  change(-2-54)%Z with(-56)%Z in Error.
  assert(Low : Rabs(B l)<=bpow radix2 (-56)).
  { replace(B l)with(-(B h-B x*B x))by lra;rewrite Rabs_Ropp;exact Error. }
  destruct(normal_center_tail_argument_error h (B x) Fh
    ltac:(rewrite Rabs_pos_eq;[exact(proj2 Hrange)|pose proof(bpow_gt_0 radix2 (-66));lra])
    (proj2 X)Error)as[Ft Tail].
  repeat split;try tauto.
  rewrite Total;exact High.
Qed.

Theorem normal_center_square_grid x : finite x ->
  bpow radix2 (-33)<=Rabs(B x)<=/2 ->
  let '(h,l,t):=normal_center_square_tail64 x in
  binary_grid (-118)(B h) /\ binary_grid (-170)(B l).
Proof.
  intros F X;pose proof(normal_center_square_tail_ieee x F X)as Square.
  destruct(normal_center_square_tail64 x)as[[h l]t].
  destruct Square as[_ [_ [_ [High [_ [Total _]]]]]].
  assert(Gx : binary_grid (-85)(B x)).
  { apply(binary_grid_binary64 x (-33));exact(proj1 X). }
  assert(Gh : binary_grid (-118)(B h)).
  { apply(binary_grid_binary64 h (-66));rewrite Rabs_pos_eq;[exact(proj1 High)|pose proof(bpow_gt_0 radix2 (-66));lra]. }
  split;[exact Gh|];replace(B l)with(B x*B x-B h)by lra;apply binary_grid_sub.
  - exact(binary_grid_mul (-85)(-85)(B x)(B x)Gx Gx).
  - eapply binary_grid_finer;[|exact Gh];lia.
Qed.
