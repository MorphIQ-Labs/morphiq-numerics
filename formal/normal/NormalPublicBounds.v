(** A uniform public error contract, with an explicit absolute term for
    gradual underflow. Component theorems retain tighter domain bounds. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add.
From Q Require Import Q256 Q256Real.
Require Import StageGappa ErfcxRounding NormalPublicModel NormalPublicSpecial.
Open Scope R_scope.

Definition normal_bounded f y := finite y /\ exists d a,
  Rabs d<=bpow radix2(-53)+bpow radix2(-111) /\ Rabs a<=bpow radix2(-1075) /\
  B y=f*(1+d)+a.

Lemma normal_bound_weaken f y e : (e<= -111)%Z -> finite y ->
  (exists d a,Rabs d<=bpow radix2(-53)+bpow radix2 e /\ Rabs a<=bpow radix2(-1075) /\
    B y=f*(1+d)+a) -> normal_bounded f y.
Proof.
  intros E F [d [a [D [A Value]]]];split;[exact F|];exists d,a;repeat split;try assumption.
  eapply Rle_trans;[exact D|apply Rplus_le_compat_l;apply bpow_le;lia].
Qed.

Lemma normal_exact_bounded f y : finite y -> B y=rndF f -> normal_bounded f y.
Proof.
  intros F Value;destruct(rounding_decomposition f)as[d [a [D [A Rounded]]]].
  split;[exact F|];exists d,a;split.
  - apply Rabs_le in D;pose proof(bpow_ge_0 radix2(-111));lra.
  - split;[apply Rabs_le;exact A|rewrite Value;exact Rounded].
Qed.

Lemma normal_bound_target f g y : f=g -> normal_bounded f y -> normal_bounded g y.
Proof. intros E;rewrite E;tauto. Qed.

Lemma normal_bound_fix_zero op x f y : normal_bounded f y ->
  normal_bounded f (normal_fix_zero64 op x y).
Proof.
  intros [F [d [a [D [A Value]]]]];destruct(normal_fix_zero_ok op x y F)as[Result Eq].
  split;[exact Result|];exists d,a;repeat split;try assumption;rewrite Eq;exact Value.
Qed.

Lemma normal_input_sign x : finite x ->
  if Bsign 53 1024 x then B x<=0 else 0<=B x.
Proof.
  intros Fx;destruct x as[s|s|s p Hp|s m e Hm];try discriminate.
  - destruct s;cbn;lra.
  - destruct s;cbn[Bsign B2R];unfold F2R;cbn.
    all: pose proof(bpow_gt_0 radix2 e);pose proof(IZR_lt 0 (Z.pos m)ltac:(lia));cbn in *.
    all: try nra.
    change(IZR(-Z.pos m)*bpow radix2 e<=0);rewrite opp_IZR;nra.
Qed.
