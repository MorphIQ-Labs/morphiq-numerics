(** Special-value screens establish every fast and accurate path's domain. *)
From Coq Require Import Reals ZArith Lia Lra Bool.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Interval Require Import Tactic.
From Binary64 Require Import IEEE64 IEEE64Add RoundingTest.
Require Import StageGappa ErfcxDecision NormalConstants NormalTailThresholdConstants
  NormalLogOverflowConstants NormalComparisons NormalFastDispatch NormalPublicModel NormalPublicAccurate.
Open Scope R_scope.

Theorem normal_regular_domain op x : finite x -> normal_special64 op x=None ->
  normal_accurate_domain op (B x) /\ (op=NormalPdf -> bpow radix2(-33)<=Rabs(B x)).
Proof.
  intros Fx Screen.
  assert(Fa : finite(b64_abs x))by(unfold b64_abs;destruct x;exact Fx).
  assert(Nf : forall w,finite w -> finite(fneg w))by(intros w Fw;unfold fneg,b64_opp;rewrite is_finite_Bopp;exact Fw).
  assert(Nb : forall w,B(fneg w)= -B w)by(intros;apply B2R_Bopp).
  destruct(erfcx_pow2_ok(-33)ltac:(lia))as[Fs Small].
  destruct normal_pdf_zero_ok as[Fpdf Pdf].
  destruct normal_tail_zero_ok as[Ftail Tail].
  destruct normal_cdf_one_ok as[Fcdf Cdf].
  destruct normal_centered_half_ok as[Fcenter Center].
  destruct normal_log_overflow_ok as[Foverflow Overflow].
  unfold normal_special64 in Screen.
  destruct(is_nan 53 1024 x);[discriminate|].
  destruct(normal_eq x normal_zero);[discriminate|].
  destruct op;cbn[normal_accurate_domain]in *.
  - destruct(normal_lt(b64_abs x)(erfcx_pow2(-33)))eqn:Tiny;[discriminate|].
    destruct(normal_le normal_pdf_zero(b64_abs x))eqn:Large;[discriminate|].
    apply normal_lt_false in Tiny;try assumption;rewrite B_abs,Small in Tiny.
    apply normal_le_false in Large;try assumption;rewrite B_abs,Pdf in Large.
    split;[split|intros;exact Tiny].
    + eapply Rle_trans;[|exact Tiny];apply bpow_le;lia.
    + lra.
  - destruct(normal_le normal_cdf_one x)eqn:High;[discriminate|].
    destruct(normal_le x (fneg normal_tail_zero))eqn:Low;[discriminate|].
    apply normal_le_false in High;try assumption;rewrite Cdf in High.
    apply(proj1(normal_le_false x (fneg normal_tail_zero)Fx (Nf normal_tail_zero Ftail)))in Low.
    rewrite Nb,Tail in Low;split;[apply Rabs_le;split;lra|discriminate].
  - destruct(normal_le normal_centered_half(b64_abs x))eqn:High;[discriminate|].
    apply normal_le_false in High;try assumption;rewrite B_abs,Center in High.
    split;[lra|discriminate].
  - destruct(normal_le normal_tail_zero x)eqn:High;[discriminate|].
    destruct(normal_le x (fneg normal_log_overflow))eqn:Low;[discriminate|].
    apply normal_le_false in High;try assumption;rewrite Tail in High.
    apply(proj1(normal_le_false x (fneg normal_log_overflow)Fx (Nf normal_log_overflow Foverflow)))in Low.
    rewrite Nb in Low;split;[split;intros;lra|discriminate].
Qed.
