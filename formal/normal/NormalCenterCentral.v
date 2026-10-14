(** The actual central branch selection and a common absolute error bound
    for centered-CDF values reused by central CDF and log-CDF compositions. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64 RoundingConstant RoundingTest.
Require Import StageGappa ErfcxDecision NormalCentered NormalAccurateCentralCdf
  NormalCenterSmall NormalCenterSmallDecision NormalCenterFastValue NormalCenterFastDecision
  NormalCenterFastTail NormalRelativeDecision.
Open Scope R_scope.

Definition normal_center_small_input x :=
  match Bcompare 53 1024 (b64_abs x)(erfcx_pow2 (-33))with Some Lt=>true | _=>false end.

Lemma normal_center_small_input_spec x : finite x ->
  if normal_center_small_input x then Rabs(B x)<bpow radix2 (-33) else bpow radix2 (-33)<=Rabs(B x).
Proof.
  intros Fx;assert(Fabs : finite(b64_abs x))by(unfold b64_abs;destruct x;simpl in *;congruence).
  destruct(erfcx_pow2_ok (-33)ltac:(lia))as[Fc C].
  unfold normal_center_small_input;rewrite(Bcompare_correct 53 1024 _ _ Fabs Fc),B_abs,C.
  destruct(Rcompare_spec(Rabs(B x))(bpow radix2 (-33)));cbn -[bpow];lra.
Qed.

Definition normal_center_central64 x :=
  if normal_center_small_input x then normal_center_small64 x else normal_center_regular64 x.

Lemma normal_center_words_bound x h l : Rabs x<=/2 ->
  finite h -> finite l -> B h=rndF(B h+B l) -> Rabs((B h+B l)-normal_center x)<=bpow radix2 (-69) ->
  finite h /\ finite l /\ B h=rndF(B h+B l) /\
  Rabs(B h)<=/2 /\ Rabs(B l)<=bpow radix2 (-55) /\
  Rabs((B h+B l)-normal_center x)<=bpow radix2 (-69).
Proof.
  intros X Fh Fl Norm Error;pose proof(normal_center_range x X)as Center.
  assert(SumRange : Rabs(B h+B l)<=/2).
  { pose proof(Rabs_triang_inv (B h+B l)(normal_center x));bpow_num_all;lra. }
  assert(High : Rabs(B h)<=/2).
  { rewrite Norm;change(/2)with(bpow radix2 (-1));apply normal_center_round_bound;[exact SumRange|lia]. }
  pose proof(rnd_err_below(B h+B l)(-1)ltac:(lia)SumRange)as Rounded;rewrite <-Norm in Rounded.
  change(-1-54)%Z with(-55)%Z in Rounded.
  assert(Low : Rabs(B l)<=bpow radix2 (-55)).
  { replace(B h-(B h+B l))with(-B l)in Rounded by ring;rewrite Rabs_Ropp in Rounded;exact Rounded. }
  tauto.
Qed.

Theorem normal_center_central_ieee x : finite x -> bpow radix2 (-450)<=Rabs(B x)<=/2 ->
  let '(h,l):=normal_center_central64 x in
  finite h /\ finite l /\ B h=rndF(B h+B l) /\
  Rabs(B h)<=/2 /\ Rabs(B l)<=bpow radix2 (-55) /\
  Rabs((B h+B l)-normal_center(B x))<=bpow radix2 (-69).
Proof.
  intros Fx X;pose proof(normal_center_small_input_spec x Fx)as Screen.
  assert(C : 0<=normal_density_constant<=/2)by(unfold normal_density_constant;split;interval with(i_prec 80)).
  unfold normal_center_central64;destruct(normal_center_small_input x).
  - pose proof(normal_center_small_ieee x Fx ltac:(split;lra))as Small.
    destruct(normal_center_small64 x)as[h l];destruct Small as[Fh [Fl [Norm [_ Error]]]].
    apply(normal_center_words_bound (B x)h l (proj2 X)Fh Fl Norm).
    eapply Rle_trans;[exact Error|];pose proof(Rabs_pos(B x));bpow_num_all;nra.
  - pose proof(normal_center_regular_ieee x Fx ltac:(split;lra))as Regular.
    destruct(normal_center_regular64 x)as[h l];destruct Regular as[Fh [Fl [Norm [_ Error]]]].
    apply(normal_center_words_bound (B x)h l (proj2 X)Fh Fl Norm).
    eapply Rle_trans;[exact Error|];pose proof(Rabs_pos(B x));bpow_num_all;nra.
Qed.

Definition normal_center_central_decide64 x :=
  let '(h,l):=normal_center_central64 x in normal_relative_decide64 h l.

Local Opaque normal_center_small64 normal_center_regular64 normal_relative_decide64.

Theorem normal_center_central_decided x v : finite x -> bpow radix2 (-450)<=Rabs(B x)<=/2 ->
  normal_center_central_decide64 x=Some v -> finite v /\ B v=rndF(normal_center(B x)).
Proof.
  intros Fx X Decision;pose proof(normal_center_small_input_spec x Fx)as Screen.
  unfold normal_center_central_decide64,normal_center_central64 in Decision;destruct(normal_center_small_input x).
  - apply(normal_center_small_decided x v Fx ltac:(split;lra));exact Decision.
  - apply(normal_center_regular_decided x v Fx ltac:(split;lra));exact Decision.
Qed.
