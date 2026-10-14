(** Scalar normal-family entry points: special values, lazy fast acceptance,
    Q256 fallback and signed-zero restoration. *)
From Coq Require Import Reals ZArith Bool.
From Flocq Require Import IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import IEEE64 IEEE64Add.
From Q Require Q256.
Require Import ErfcxDecision ErfcxAccurateSquare ErfcxAccurateTerms NormalConstants NormalComparisons
  NormalFastDispatch NormalTailThresholdConstants NormalLogOverflowConstants
  NormalAccurateDensity NormalAccurateCenter NormalAccurateCentralCdf NormalAccurateTailFull
  NormalAccurateOuter NormalAccurateLogCentral NormalAccurateLogNegative NormalAccurateLogPositive.
Open Scope R_scope.

Definition normal_negative_zero : f64 := b64_of_bits 9223372036854775808.
Definition normal_negative_infinity : f64 := b64_of_bits 18442240474082181120.
Definition normal_signed_half x := if Bsign 53 1024 x then fneg(erfcx_pow2(-1))else erfcx_pow2(-1).
Definition normal_signed_zero x := if Bsign 53 1024 x then normal_negative_zero else normal_zero.
Definition normal_special64 op x :=
  if is_nan 53 1024 x then Some x else
  if normal_eq x normal_zero then Some(match op with
    | NormalPdf=>normal_density_hi | NormalCdf=>erfcx_pow2(-1)
    | NormalCentered=>x | NormalLogCdf=>fneg normal_ln2_hi end)else
  let a:=b64_abs x in
  match op with
  | NormalPdf=>if normal_lt a (erfcx_pow2(-33))then Some normal_density_hi else
      if normal_le normal_pdf_zero a then Some normal_zero else None
  | NormalCdf=>if normal_le normal_cdf_one x then Some(erfcx_pow2 0)else
      if normal_le x (fneg normal_tail_zero)then Some normal_zero else None
  | NormalCentered=>if normal_le normal_centered_half a then Some(normal_signed_half x)else None
  | NormalLogCdf=>if normal_le normal_tail_zero x then Some normal_negative_zero else
      if normal_le x (fneg normal_log_overflow)then Some normal_negative_infinity else None
  end.

Definition normal_accurate_value64 op x :=
  let a:=b64_abs x in
  match op with
  | NormalPdf=>normal_q_density_regular a
  | NormalCdf=>if normal_le a (erfcx_pow2(-1))then normal_q_central_cdf x else
      if normal_lt x normal_zero then normal_q_tail a else normal_q_outer_complement q_one a
  | NormalCentered=>if normal_le a (erfcx_pow2(-1))then normal_q_center x else
      let q:=normal_q_outer_complement q_half a in
      if Bsign 53 1024 x then Q256.neg_q q else q
  | NormalLogCdf=>if normal_le a (erfcx_pow2(-1))then normal_q_log_cdf_central x else
      if normal_lt normal_zero x then normal_q_log_cdf_positive a else normal_q_log_cdf_negative a
  end.
Definition normal_fix_zero64 op x y :=
  match op with
  | NormalCentered=>if normal_eq y normal_zero then normal_signed_zero x else y
  | NormalLogCdf=>if normal_eq y normal_zero then normal_negative_zero else y
  | _=>y
  end.
Definition normal_accurate64 op x := normal_fix_zero64 op x (Q256.to_f64(normal_accurate_value64 op x)).
Definition normal_regular64 op x := match normal_fast_dispatch64 op x with
  | Some y=>y | None=>normal_accurate64 op x end.
Definition normal_entry64 op x := match normal_special64 op x with
  | Some y=>y | None=>normal_regular64 op x end.
Definition normal_ccdf_entry64 x :=
  normal_entry64 NormalCdf (if is_nan 53 1024 x then x else fneg x).
