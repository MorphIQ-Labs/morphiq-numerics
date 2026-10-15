(** The regular centered-CDF value fits the shared relative guard. The
    bitwise endpoint test is sufficient for correct rounding on acceptance. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64 RoundingConstant.
Require Import StageGappa NormalCentered NormalCenterFastValue NormalRelativeDecision.
Open Scope R_scope.

Theorem normal_center_regular_range x : finite x -> bpow radix2 (-33)<=Rabs(B x)<=/2 ->
  let '(h,l):=normal_center_regular64 x in
  exists k, finite h /\ finite l /\ (-1000<=k<=0)%Z /\
    bpow radix2 k/8<=Rabs(B h)<=4*bpow radix2 k /\ Rabs(B l)<=bpow radix2 (k-52) /\
    Rabs((B h+B l)-normal_center(B x))<=bpow radix2 (k-68).
Proof.
  intros Fx X;pose proof(normal_center_regular_ieee x Fx X)as Fast.
  destruct(normal_center_regular64 x)as[h l];destruct Fast as[Fh [Fl [Norm [_ Error]]]].
  assert(Nonzero : B x<>0).
  { intros Zero;rewrite Zero,Rabs_R0 in X;pose proof(bpow_gt_0 radix2 (-33));lra. }
  set(k:=(mag radix2 (B x):Z)).
  assert(K : (-32<=k<=0)%Z).
  { unfold k;split.
    - apply mag_ge_bpow;change(-32-1)%Z with(-33)%Z;exact(proj1 X).
    - apply mag_le_bpow;[exact Nonzero|];change(bpow radix2 0)with 1;lra. }
  pose proof(bpow_mag_le radix2 (B x)Nonzero)as Lower;pose proof(bpow_mag_gt radix2 (B x))as Upper.
  fold k in Lower,Upper;set(s:=bpow radix2 k).
  assert(Spositive : 0<s<=1).
  { unfold s;split;[apply bpow_gt_0|change 1 with(bpow radix2 0);apply bpow_le;lia]. }
  assert(Xscale : s/2<=Rabs(B x)<=s).
  { unfold s;replace(k-1)%Z with(k+ -1)%Z in Lower by ring;rewrite bpow_plus in Lower.
    change(bpow radix2 (-1))with(/2)in Lower;lra. }
  assert(C : 3/8<=normal_density_constant<=/2)by(unfold normal_density_constant;split;interval with(i_prec 80)).
  pose proof(normal_shape_range(B x)(proj2 X))as Shape.
  assert(Target : Rabs(normal_center(B x))=normal_density_constant*Rabs(B x)*normal_shape(B x)).
  { unfold normal_center;rewrite !Rabs_mult,(Rabs_pos_eq normal_density_constant),(Rabs_pos_eq(normal_shape(B x)))by lra;reflexivity. }
  assert(Scale : 3/16*s<=normal_density_constant*Rabs(B x)<=s/2)by(split;nra).
  assert(Magnitude : 5/32*s<=Rabs(normal_center(B x))<=s).
  { rewrite Target;split;nra. }
  assert(Composition : Rabs((B h+B l)-normal_center(B x))<=bpow radix2 (k-68)).
  { eapply Rle_trans;[exact Error|].
    replace(k-68)%Z with(k+ -68)%Z by ring;rewrite bpow_plus;fold s;bpow_num_all;nra. }
  assert(SumRange : s/7<=Rabs(B h+B l)<=2*s).
  { pose proof(Rabs_triang_inv (B h+B l)(normal_center(B x)))as A.
    pose proof(Rabs_triang_inv (normal_center(B x))(B h+B l))as D;rewrite Rabs_minus_sym in D.
    pose proof Composition as Bound;replace(k-68)%Z with(k+ -68)%Z in Bound by ring;
      rewrite bpow_plus in Bound;fold s in Bound;bpow_num_all;split;nra. }
  assert(SumBound : Rabs(B h+B l)<=bpow radix2 (k+1)).
  { rewrite bpow_plus;change(bpow radix2 1)with 2;fold s;lra. }
  pose proof(rnd_err_below (B h+B l)(k+1)ltac:(lia)SumBound)as Rounded;rewrite <-Norm in Rounded.
  replace(k+1-54)%Z with(k-53)%Z in Rounded by ring.
  assert(Low : Rabs(B l)<=bpow radix2 (k-53)).
  { replace(B h-(B h+B l))with(-B l)in Rounded by ring;rewrite Rabs_Ropp in Rounded;exact Rounded. }
  assert(High : s/8<=Rabs(B h)<=4*s).
  { pose proof(Rabs_triang_inv (B h)(B h+B l))as A.
    pose proof(Rabs_triang_inv (B h+B l)(B h))as D.
    replace(B h-(B h+B l))with(-B l)in A by ring;rewrite Rabs_Ropp in A.
    replace(B h+B l-B h)with(B l)in D by ring.
    pose proof Low as Bound;replace(k-53)%Z with(k+ -53)%Z in Bound by ring;
      rewrite bpow_plus in Bound;fold s in Bound;bpow_num_all;split;nra. }
  exists k;repeat split;try tauto;try lia.
  eapply Rle_trans;[exact Low|];apply bpow_le;lia.
Qed.

Definition normal_center_regular_decide64 x :=
  let '(h,l):=normal_center_regular64 x in normal_relative_decide64 h l.

Local Opaque normal_center_regular64 normal_relative_decide64.

Theorem normal_center_regular_decided x v : finite x -> bpow radix2 (-33)<=Rabs(B x)<=/2 ->
  normal_center_regular_decide64 x=Some v -> finite v /\ B v=rndF(normal_center(B x)).
Proof.
  intros F X Decision;pose proof(normal_center_regular_range x F X)as Fast.
  unfold normal_center_regular_decide64 in Decision;destruct(normal_center_regular64 x)as[h l].
  destruct Fast as[k [Fh [Fl [K [H [L Error]]]]]].
  exact(normal_relative_decide_ok h l k (normal_center(B x))v Fh Fl K H L Error Decision).
Qed.
