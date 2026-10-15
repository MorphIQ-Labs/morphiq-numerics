(** The actual signed linear centered-CDF value and its rounded guard.
    An accepted interval test returns the correctly rounded centered CDF. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64 RoundingConstant.
Require Import StageGappa NormalCentered NormalCenterSmall NormalRelativeDecision.
Open Scope R_scope.

Theorem normal_center_small_range x : finite x ->
  bpow radix2 (-450)<=Rabs(B x)<=bpow radix2 (-33) ->
  let '(h,l):=normal_center_small64 x in
  exists k, finite h /\ finite l /\ (-1000<=k<=0)%Z /\
    bpow radix2 k/8<=Rabs(B h)<=4*bpow radix2 k /\
    Rabs(B l)<=bpow radix2 (k-52) /\
    Rabs((B h+B l)-normal_center(B x))<=bpow radix2 (k-68).
Proof.
  intros Fx X;pose proof(normal_center_small_ieee x Fx X)as Small.
  destruct(normal_center_small64 x)as[h l];destruct Small as[Fh [Fl [Norm [Linear Error]]]].
  assert (Nonzero : B x<>0).
  { intros Zero;rewrite Zero,Rabs_R0 in X;pose proof(bpow_gt_0 radix2 (-450));lra. }
  set(k:=(mag radix2 (B x):Z)).
  assert(K : (-449<=k<=0)%Z).
  { unfold k;split.
    - apply mag_ge_bpow;change(-449-1)%Z with(-450)%Z;exact(proj1 X).
    - apply mag_le_bpow;[exact Nonzero|].
      eapply Rle_lt_trans;[exact(proj2 X)|];apply bpow_lt;lia. }
  pose proof(bpow_mag_le radix2 (B x) Nonzero)as Lower.
  pose proof(bpow_mag_gt radix2 (B x))as Upper.
  fold k in Lower,Upper.
  set(s:=bpow radix2 k).
  assert(Spositive : 0<s<=1).
  { unfold s;split;[apply bpow_gt_0|change 1 with(bpow radix2 0);apply bpow_le;lia]. }
  assert(Xscale : s/2<=Rabs(B x)<=s).
  { unfold s;replace(k-1)%Z with(k+ -1)%Z in Lower by ring;rewrite bpow_plus in Lower.
    change(bpow radix2 (-1))with(/2)in Lower;lra. }
  assert(C : 39/100<=normal_density_constant<=41/100).
  { unfold normal_density_constant;split;interval with(i_prec 80). }
  assert(Target : normal_density_constant*Rabs(B x)=Rabs(normal_density_constant*B x)).
  { rewrite Rabs_mult,(Rabs_pos_eq normal_density_constant)by lra;reflexivity. }
  assert(SumRange : s/6<=Rabs(B h+B l)<=s).
  { pose proof(Rabs_triang_inv (B h+B l)(normal_density_constant*B x))as Reverse.
    pose proof(Rabs_triang_inv (normal_density_constant*B x)(B h+B l))as Reverse2.
    rewrite <-Target in Reverse,Reverse2;rewrite Rabs_minus_sym in Reverse2.
    bpow_num_all;split;nra. }
  pose proof(rnd_err_below(B h+B l)k ltac:(lia)(proj2 SumRange))as Rounded.
  rewrite <-Norm in Rounded.
  assert(Low : Rabs(B l)<=bpow radix2 (k-54)).
  { replace(B h-(B h+B l))with(-B l)in Rounded by ring;rewrite Rabs_Ropp in Rounded;exact Rounded. }
  assert(High : s/8<=Rabs(B h)<=4*s).
  { pose proof(Rabs_triang_inv (B h)(B h+B l))as Reverse.
    pose proof(Rabs_triang_inv (B h+B l)(B h))as Reverse2.
    replace(B h-(B h+B l))with(-B l)in Reverse by ring.
    replace(B h+B l-B h)with(B l)in Reverse2 by ring.
    rewrite Rabs_Ropp in Reverse.
    replace(k-54)%Z with(k+ -54)%Z in Low by ring;rewrite bpow_plus in Low;fold s in Low;bpow_num_all;split;nra. }
  assert(Composition : Rabs((B h+B l)-normal_center(B x))<=bpow radix2 (k-68)).
  { pose proof(normal_center_linear_error (B x)(proj2 X))as Approximation.
    replace((B h+B l)-normal_center(B x))with
      (((B h+B l)-normal_density_constant*B x)+(normal_density_constant*B x-normal_center(B x)))by ring.
    eapply Rle_trans;[apply Rabs_triang|];rewrite(Rabs_minus_sym(normal_density_constant*B x)(normal_center(B x))).
    eapply Rle_trans with(normal_density_constant*Rabs(B x)*(bpow radix2 (-103)+bpow radix2 (-67)));[nra|].
    replace(k-68)%Z with(k+ -68)%Z by ring;rewrite bpow_plus;fold s.
    assert(Budget : 41/100*(bpow radix2 (-103)+bpow radix2 (-67))<=bpow radix2 (-68))by(bpow_num;interval with(i_prec 180)).
    assert(Scale : normal_density_constant*Rabs(B x)<=41/100*s)by nra.
    pose proof(bpow_gt_0 radix2 (-103));pose proof(bpow_gt_0 radix2 (-67));nra. }
  exists k;repeat split;try tauto;try lia.
  eapply Rle_trans;[exact Low|];apply bpow_le;lia.
Qed.

Definition normal_center_small_decide64 x :=
  let '(h,l):=normal_center_small64 x in
  normal_relative_decide64 h l.

Local Opaque normal_center_small64 normal_relative_decide64.

Theorem normal_center_small_decided x v : finite x ->
  bpow radix2 (-450)<=Rabs(B x)<=bpow radix2 (-33) ->
  normal_center_small_decide64 x=Some v -> finite v /\ B v=rndF(normal_center(B x)).
Proof.
  intros F X Decision;pose proof(normal_center_small_range x F X)as Fast.
  unfold normal_center_small_decide64 in Decision;destruct(normal_center_small64 x)as[h l].
  destruct Fast as[k [Fh [Fl [K [H [L Error]]]]]].
  exact(normal_relative_decide_ok h l k (normal_center(B x))v Fh Fl K H L Error Decision).
Qed.
