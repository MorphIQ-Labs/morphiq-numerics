(** The actual high-word comparison selects between the two proved
    log-complement compositions. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64.
Require Import StageGappa ErfcxDecision NormalLogComplementMain NormalLogComplementTiny.
Open Scope R_scope.

Definition normal_log_complement64 h l :=
  match Bcompare 53 1024 h (erfcx_pow2(-54))with
  | Some Lt=>normal_log_complement_tiny64 h l
  | _=>normal_log_complement_main64 h l
  end.

Local Opaque normal_log_complement_tiny64 normal_log_complement_main64.

Theorem normal_log_complement_ieee h l : finite h -> finite l ->
  bpow radix2(-1004)<=B h<=/3 -> Rabs(B l)<=B h*bpow radix2(-51) ->
  let '(a,b):=normal_log_complement64 h l in
  finite a /\ finite b /\ B a=rndF(B a+B b) /\
  Rabs((B a+B b)-ln(1-B h-B l))<=B h*bpow radix2(-66).
Proof.
  intros Fh Fl H L;unfold normal_log_complement64.
  destruct(erfcx_pow2_ok(-54)ltac:(lia))as[Fc C].
  rewrite(Bcompare_correct 53 1024 h (erfcx_pow2(-54))Fh Fc),C.
  destruct(Rcompare_spec(B h)(bpow radix2(-54)))as[Small|Equal|Large];cbv beta iota.
  - pose proof(normal_log_complement_tiny_ieee h l Fh Fl ltac:(split;lra)L)as Tiny.
    destruct(normal_log_complement_tiny64 h l)as[a b].
    destruct Tiny as[Fa [Fb [Norm Error]]];repeat split;try assumption.
    eapply Rle_trans;[exact Error|bpow_num_all;nra].
  - apply normal_log_complement_main_ieee;try assumption;split;lra.
  - apply normal_log_complement_main_ieee;try assumption;split;lra.
Qed.
