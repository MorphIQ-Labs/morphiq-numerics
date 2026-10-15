(** Total scalar entry contracts for the standard-normal family. *)
From Coq Require Import Reals ZArith Lia Lra Bool.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import IEEE64 IEEE64Add RoundingTest.
Require Import ErfcxDecision NormalComparisons NormalFastDispatch NormalPublicModel
  NormalPublicBounds NormalPublicSpecial NormalPublicFinite NormalLogOverflowConstants.
Open Scope R_scope.

Definition normal_finite_contract op x y :=
  match op with
  | NormalLogCdf=>if Rle_dec(B x)(-B normal_log_overflow)then
      y=normal_negative_infinity /\ bpow radix2 1024-bpow radix2 970 < -normal_target op (B x)
      else normal_bounded(normal_target op (B x))y
  | _=>normal_bounded(normal_target op (B x))y
  end.

Theorem normal_finite_entry_contract op x : finite x ->
  normal_finite_contract op x (normal_entry64 op x).
Proof.
  intros Fx;destruct op;cbn[normal_finite_contract].
  all: try(apply normal_entry_bounded;[exact Fx|discriminate]).
  destruct(Rle_dec(B x)(-B normal_log_overflow)).
  - apply normal_entry_log_overflow;assumption.
  - apply normal_entry_bounded;[exact Fx|intros;lra].
Qed.

Definition normal_contract op x y := match x with
  | B754_nan _ _ _=>y=x
  | B754_infinity sign=>y=match op with
      | NormalPdf=>normal_zero
      | NormalCdf=>if sign then normal_zero else erfcx_pow2 0
      | NormalCentered=>if sign then fneg(erfcx_pow2(-1))else erfcx_pow2(-1)
      | NormalLogCdf=>if sign then normal_negative_infinity else normal_negative_zero end
  | _=>normal_finite_contract op x y end.

Theorem normal_public_contract op x : normal_contract op x (normal_entry64 op x).
Proof.
  destruct x as[s|s|s p Hp|s m e Hm];cbn[normal_contract].
  - apply normal_finite_entry_contract;reflexivity.
  - destruct s;[rewrite normal_entry_negative_infinity|rewrite normal_entry_positive_infinity];destruct op;reflexivity.
  - apply normal_entry_nan;reflexivity.
  - apply normal_finite_entry_contract;reflexivity.
Qed.

Theorem normal_ccdf_finite_bounded x : finite x ->
  normal_bounded(normal_target NormalCdf (-B x))(normal_ccdf_entry64 x).
Proof.
  intros Fx;assert(Nan : is_nan 53 1024 x=false)by(destruct x;try discriminate;reflexivity).
  unfold normal_ccdf_entry64;rewrite Nan.
  pose proof(normal_entry_bounded NormalCdf (fneg x)
    ltac:(unfold fneg,b64_opp;rewrite is_finite_Bopp;exact Fx)ltac:(discriminate))as Result.
  unfold fneg,b64_opp in Result;rewrite B2R_Bopp in Result;exact Result.
Qed.

Definition normal_ccdf_contract x y := match x with
  | B754_nan _ _ _=>y=x
  | B754_infinity sign=>y=if sign then erfcx_pow2 0 else normal_zero
  | _=>normal_bounded(normal_target NormalCdf (-B x))y end.

Theorem normal_ccdf_public_contract x : normal_ccdf_contract x (normal_ccdf_entry64 x).
Proof.
  destruct x as[s|s|s p Hp|s m e Hm];cbn[normal_ccdf_contract].
  - apply normal_ccdf_finite_bounded;reflexivity.
  - destruct s;reflexivity.
  - apply normal_ccdf_nan;reflexivity.
  - apply normal_ccdf_finite_bounded;reflexivity.
Qed.
