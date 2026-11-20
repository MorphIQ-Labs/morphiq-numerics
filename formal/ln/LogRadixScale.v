(** The shared double-word multiplication theorem instantiated with the
    fast logarithm grids. This includes zero logarithms: a relative quotient
    alone would not establish the result when the exact product is zero. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Double Require Import DWPlus DWTimesFP.
From Binary64 Require Import Binary64Add Binary64Mul IEEE64 IEEE64Mul
  IEEE64NormalizedMul Grid Encodings.
From Interval Require Import Tactic.
Require Import LnFastTables LogRadixConstants LogRadixFast LogRadixGrid.
Open Scope R_scope.

Lemma inv_ln2_pair_grid : let '(h,l):=inv_ln2_dw in
  on_grid (-109) (B h) /\ on_grid (-109) (B l).
Proof.
  pose proof inv_ln2_dw_ok as P. destruct inv_ln2_dw as [h l].
  destruct P as [_ [_ [D V]]]. apply radix_normalized_grid; [exact D | rewrite V].
  apply grid_plus.
  - rewrite inv_ln2_hi_val; apply (val_grid 6497320848556798 52 109); lia.
  - rewrite inv_ln2_lo_val; apply (val_grid 6605663993728292 108 109); lia.
Qed.

Lemma inv_ln10_pair_grid : let '(h,l):=inv_ln10_dw in
  on_grid (-109) (B h) /\ on_grid (-109) (B l).
Proof.
  pose proof inv_ln10_dw_ok as P. destruct inv_ln10_dw as [h l].
  destruct P as [_ [_ [D V]]]. apply radix_normalized_grid; [exact D | rewrite V].
  apply grid_plus.
  - rewrite inv_ln10_hi_val; apply (val_grid 7823553867474190 54 109); lia.
  - rewrite inv_ln10_lo_val; apply (val_grid 7128502086859475 109 109); lia.
Qed.

Lemma radix_scale_domain a b : on_grid (-623) a -> on_grid (-109) b ->
  in_two_prod_domain a b.
Proof.
  intros Ga Gb. destruct (Req_dec (a*b) 0) as [Z | N]; [left; exact Z | right].
  apply Rle_trans with (bpow radix2 (-732)); [apply bpow_le; lia | ].
  apply grid_nonzero; [change (-732)%Z with (-623 + -109)%Z; now apply grid_mult | exact N].
Qed.

Lemma radix_mul_zero xh xl yh yl : fmtF xh -> fmtF xl -> fmtF yh -> fmtF yl ->
  xh=rndF(xh+xl) -> yh=rndF(yh+yl) -> (xh+xl)*(yh+yl)=0 ->
  mul xh xl yh yl=(0,0).
Proof.
  intros Fxh Fxl Fyh Fyl Dx Dy Zero.
  assert (Pair : forall h l, h=rndF(h+l) -> h+l=0 -> h=0 /\ l=0).
  { intros h l D Z. rewrite Z,round_0 in D by exact _. split; lra. }
  apply Rmult_integral in Zero. destruct Zero as [X | Y].
  - destruct (Pair xh xl Dx X) as [-> ->].
    unfold mul. rewrite two_prod_eq by (try assumption; try apply generic_format_0; left; ring).
    unfold Fast2Mult,fast_two_sum; cbn [fst snd].
    repeat (rewrite ?Rmult_0_l,?Rmult_0_r,?Rplus_0_l,?Rplus_0_r,?Rminus_0_l,?Rminus_0_r,?Ropp_0,?round_0 by exact _).
    reflexivity.
  - destruct (Pair yh yl Dy Y) as [-> ->].
    unfold mul. rewrite two_prod_eq by (try assumption; try apply generic_format_0; left; ring).
    unfold Fast2Mult,fast_two_sum; cbn [fst snd].
    repeat (rewrite ?Rmult_0_l,?Rmult_0_r,?Rplus_0_l,?Rplus_0_r,?Rminus_0_l,?Rminus_0_r,?Ropp_0,?round_0 by exact _).
    reflexivity.
Qed.

Theorem radix_scale_ieee xh xl ch cl :
  finite xh -> finite xl -> B xh=rndF(B xh+B xl) ->
  finite ch -> finite cl -> B ch=rndF(B ch+B cl) ->
  Rabs(B xh)<=2048 -> Rabs(B xl)<=2048 -> Rabs(B ch)<=4 -> Rabs(B cl)<=4 ->
  on_grid (-623) (B xh) -> on_grid (-623) (B xl) ->
  on_grid (-109) (B ch) -> on_grid (-109) (B cl) ->
  let '(h,l):=mul64 xh xl ch cl in
  finite h /\ finite l /\ B h=rndF(B h+B l) /\
  exists d, Rabs d<=5/2^106 /\ B h+B l=(B xh+B xl)*(B ch+B cl)*(1+d).
Proof.
  intros Fxh Fxl Dx Fch Fcl Dc Xh Xl Ch Cl Gxh Gxl Gch Gcl.
  assert (Big : forall v, Rabs v<=2048 -> Rabs v<=bpow radix2 508).
  { intros v V. apply Rle_trans with 2048; [exact V | interval]. }
  pose proof (radix_scale_domain _ _ Gxh Gch) as Domain.
  pose proof (two_prod_domain_normal _ _ (radix_scale_domain _ _ Gxh Gcl)) as Cross1.
  pose proof (two_prod_domain_normal _ _ (radix_scale_domain _ _ Gxl Gch)) as Cross2.
  pose proof (mul_normalized_ieee xh xl ch cl Fxh Fxl Dx Fch Fcl Dc
    (Big _ Xh) (Big _ Xl) (Big (B ch) ltac:(lra)) (Big (B cl) ltac:(lra)) Domain Cross1 Cross2) as P.
  pose proof (mul_ieee xh xl ch cl Fxh Fxl Dx Fch Fcl Dc
    (Big _ Xh) (Big _ Xl) (Big (B ch) ltac:(lra)) (Big (B cl) ltac:(lra)) Domain Cross1 Cross2) as E.
  assert (Bound : forall v, Rabs v<=2048 -> bnd 1 11 v).
  { intros v V. unfold bnd. change (IZR 1*bpow radix2 11) with (1*2048); lra. }
  destruct (mul64_ok 11 xh xl ch cl Fxh Fxl Fch Fcl
    (Bound _ Xh) (Bound _ Xl) (Bound (B ch) ltac:(lra)) (Bound (B cl) ltac:(lra)) ltac:(lia)) as [_ [_ Value]].
  destruct (mul64 xh xl ch cl) as [h l]; cbn [fst snd] in Value.
  destruct P as [Fh [Fl D]]. destruct E as [_ [_ E]].
  split; [exact Fh | split; [exact Fl | split; [exact D | ]]].
  destruct (Req_dec ((B xh+B xl)*(B ch+B cl)) 0) as [Zero | Nonzero].
  - rewrite (radix_mul_zero _ _ _ _ (B_fmt xh) (B_fmt xl) (B_fmt ch) (B_fmt cl) Dx Dc Zero) in Value.
    injection Value as H L. exists 0. rewrite H,L,Zero,Rabs_R0. split; [interval | ring].
  - exists ((B h+B l-(B xh+B xl)*(B ch+B cl))/((B xh+B xl)*(B ch+B cl))).
    split; [apply Rle_trans with (1:=Rlt_le _ _ E); unfold prec; interval with (i_prec 140) | field; split; intro Z; apply Nonzero; rewrite Z; ring].
Qed.
