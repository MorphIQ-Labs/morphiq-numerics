(** Finite entry-point contract: the bounded result, or the proved
    negative log-CDF overflow screen. *)
From Coq Require Import Reals ZArith Lia Lra Psatz Bool.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add RoundingTest.
Require Import StageGappa ErfcxDecision NormalConstants NormalComparisons NormalFastDispatch
  NormalPublicModel NormalPublicBounds NormalPublicScreens NormalPublicRegular NormalDensityTiny
  NormalTailThresholdConstants NormalLogOverflowConstants NormalLogOverflow NormalTailAnalytic.
Open Scope R_scope.
Local Opaque normal_lt normal_le normal_eq erfcx_pow2 normal_signed_half
  normal_density_hi normal_pdf_zero normal_cdf_one normal_tail_zero normal_centered_half normal_log_overflow.

Theorem normal_special_bounded op x y : finite x ->
  (op=NormalLogCdf -> -B normal_log_overflow<B x) -> normal_special64 op x=Some y ->
  normal_bounded(normal_target op (B x))y.
Proof.
  intros Fx Nonoverflow Special.
  assert(Nan : is_nan 53 1024 x=false)by(destruct x;try discriminate;reflexivity).
  assert(Fa : finite(b64_abs x))by(unfold b64_abs;destruct x;exact Fx).
  assert(Nf : forall w,finite w -> finite(fneg w))by(intros w Fw;unfold fneg,b64_opp;rewrite is_finite_Bopp;exact Fw).
  assert(Nb : forall w,B(fneg w)= -B w)by(intros;apply B2R_Bopp).
  assert(Fzero : finite normal_zero)by reflexivity.
  assert(Zero : B normal_zero=0)by reflexivity.
  unfold normal_special64 in Special;rewrite Nan in Special.
  destruct(normal_eq x normal_zero)eqn:Iszero.
  - injection Special as <-;apply normal_eq_true in Iszero;try assumption;rewrite Zero in Iszero.
    apply normal_zero_result_bounded;assumption.
  - destruct op;cbn[normal_target]in *.
    + destruct(normal_lt(b64_abs x)(erfcx_pow2(-33)))eqn:Small.
      * injection Special as <-;apply normal_exact_bounded;[exact(proj1 normal_density_hi_ok)|].
        destruct(erfcx_pow2_ok(-33)ltac:(lia))as[Fc C].
        apply normal_lt_true in Small;try assumption;rewrite B_abs,C in Small.
        symmetry;apply normal_density_tiny_correct;lra.
      * destruct(normal_le normal_pdf_zero(b64_abs x))eqn:Large;[|discriminate].
        injection Special as <-;apply normal_pdf_saturated_bounded;[exact Fx|].
        apply(proj1(normal_le_true normal_pdf_zero(b64_abs x)(proj1 normal_pdf_zero_ok)Fa))in Large.
        rewrite B_abs in Large;exact Large.
    + destruct(normal_le normal_cdf_one x)eqn:High.
      * injection Special as <-;apply normal_cdf_saturated_one;[exact Fx|].
        apply(proj1(normal_le_true normal_cdf_one x(proj1 normal_cdf_one_ok)Fx))in High;exact High.
      * destruct(normal_le x (fneg normal_tail_zero))eqn:Low;[|discriminate].
        injection Special as <-;apply normal_cdf_saturated_zero;[exact Fx|].
        apply(proj1(normal_le_true x (fneg normal_tail_zero)Fx(Nf normal_tail_zero(proj1 normal_tail_zero_ok))))in Low.
        rewrite Nb in Low;exact Low.
    + destruct(normal_le normal_centered_half(b64_abs x))eqn:Large;[|discriminate].
      injection Special as <-;apply normal_center_saturated_half;[exact Fx|].
      apply(proj1(normal_le_true normal_centered_half(b64_abs x)(proj1 normal_centered_half_ok)Fa))in Large.
      rewrite B_abs in Large;exact Large.
    + destruct(normal_le normal_tail_zero x)eqn:High.
      * injection Special as <-;apply normal_log_saturated_zero;[exact Fx|].
        apply(proj1(normal_le_true normal_tail_zero x(proj1 normal_tail_zero_ok)Fx))in High;exact High.
      * destruct(normal_le x(fneg normal_log_overflow))eqn:Low;[|discriminate].
        apply(proj1(normal_le_true x (fneg normal_log_overflow)Fx(Nf normal_log_overflow(proj1 normal_log_overflow_ok))))in Low.
        rewrite Nb in Low;specialize(Nonoverflow eq_refl);lra.
Qed.

Theorem normal_entry_bounded op x : finite x ->
  (op=NormalLogCdf -> -B normal_log_overflow<B x) ->
  normal_bounded(normal_target op (B x))(normal_entry64 op x).
Proof.
  intros Fx Nonoverflow;unfold normal_entry64;destruct(normal_special64 op x)as[y|]eqn:Special.
  - apply normal_special_bounded;assumption.
  - apply normal_regular_bounded;assumption.
Qed.

Theorem normal_entry_log_overflow x : finite x -> B x<= -B normal_log_overflow ->
  normal_entry64 NormalLogCdf x=normal_negative_infinity /\
  bpow radix2 1024-bpow radix2 970 < -normal_target NormalLogCdf (B x).
Proof.
  intros Fx X;destruct normal_log_overflow_ok as[Fc C].
  assert(Cutoff : /2<B normal_log_overflow)by(rewrite C;bpow_num_all;nra).
  assert(Fa : finite(b64_abs x))by(unfold b64_abs;destruct x;exact Fx).
  assert(Nan : is_nan 53 1024 x=false)by(destruct x;try discriminate;reflexivity).
  assert(Nb : B(fneg normal_log_overflow)= -B normal_log_overflow)by(apply B2R_Bopp).
  assert(Fneg : finite(fneg normal_log_overflow))by(unfold fneg,b64_opp;rewrite is_finite_Bopp;exact Fc).
  assert(Iszero : normal_eq x normal_zero=false).
  { destruct(normal_eq x normal_zero)eqn:E;[|reflexivity].
    apply(proj1(normal_eq_true x normal_zero Fx ltac:(reflexivity)))in E.
    change(B x=0)in E;lra. }
  assert(High : normal_le normal_tail_zero x=false).
  { apply normal_le_false;[exact(proj1 normal_tail_zero_ok)|exact Fx|].
    rewrite(proj2 normal_tail_zero_ok);lra. }
  assert(Low : normal_le x(fneg normal_log_overflow)=true).
  { apply normal_le_true;[exact Fx|exact Fneg|rewrite Nb;exact X]. }
  split.
  - unfold normal_entry64,normal_special64;rewrite Nan,Iszero,High,Low;reflexivity.
  - pose proof(normal_log_overflow_midpoint(b64_abs x)Fa
      ltac:(rewrite B_abs,Rabs_left1;lra))as[Overflow _].
    specialize(Overflow ltac:(rewrite B_abs,Rabs_left1;lra)).
    rewrite B_abs,normal_negative_cdf in Overflow by lra;exact Overflow.
Qed.
