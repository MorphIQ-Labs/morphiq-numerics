(** Payload NaNs, infinities, signed zeros and the fallback zero-sign
    correction, for the actual scalar entry model. *)
From Coq Require Import Reals ZArith Lia Lra Bool.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import IEEE64 IEEE64Add.
Require Import NormalComparisons NormalFastDispatch NormalPublicModel
  NormalConstants ErfcxDecision.
Open Scope R_scope.
Local Opaque normal_regular64.

Theorem normal_entry_nan op x : is_nan 53 1024 x=true -> normal_entry64 op x=x.
Proof. intros Nan;unfold normal_entry64,normal_special64;rewrite Nan;reflexivity. Qed.
Theorem normal_ccdf_nan x : is_nan 53 1024 x=true -> normal_ccdf_entry64 x=x.
Proof. intros Nan;unfold normal_ccdf_entry64;rewrite Nan;apply normal_entry_nan;exact Nan. Qed.
Theorem normal_entry_zero op sign :
  normal_entry64 op (B754_zero 53 1024 sign)=
  match op with
  | NormalPdf=>normal_density_hi | NormalCdf=>erfcx_pow2(-1)
  | NormalCentered=>B754_zero 53 1024 sign | NormalLogCdf=>fneg normal_ln2_hi end.
Proof. destruct op,sign;reflexivity. Qed.
Theorem normal_entry_positive_infinity op :
  normal_entry64 op (B754_infinity 53 1024 false)=
  match op with
  | NormalPdf=>normal_zero | NormalCdf=>erfcx_pow2 0
  | NormalCentered=>erfcx_pow2(-1) | NormalLogCdf=>normal_negative_zero end.
Proof. destruct op;reflexivity. Qed.
Theorem normal_entry_negative_infinity op :
  normal_entry64 op (B754_infinity 53 1024 true)=
  match op with
  | NormalPdf=>normal_zero | NormalCdf=>normal_zero
  | NormalCentered=>fneg(erfcx_pow2(-1)) | NormalLogCdf=>normal_negative_infinity end.
Proof. destruct op;reflexivity. Qed.

Theorem normal_fix_zero_ok op x y : finite y ->
  finite(normal_fix_zero64 op x y) /\ B(normal_fix_zero64 op x y)=B y.
Proof.
  intros Fy;assert(Fzero : finite normal_zero)by reflexivity.
  assert(Zero : B normal_zero=0)by reflexivity.
  destruct op;cbn[normal_fix_zero64];try(split;[exact Fy|reflexivity]).
  all: destruct(normal_eq y normal_zero)eqn:Eq;try(split;[exact Fy|reflexivity]).
  all: apply normal_eq_true in Eq;try assumption;rewrite Zero in Eq.
  - unfold normal_signed_zero;destruct(Bsign 53 1024 x);split;try reflexivity;rewrite Eq;reflexivity.
  - split;[reflexivity|rewrite Eq;reflexivity].
Qed.
