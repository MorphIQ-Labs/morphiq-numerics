(** The Q256 dispatch, including signed complements and both logarithmic
    tails, satisfies the uniform public bound on its screened domain. *)
From Coq Require Import Reals ZArith Lia Lra Psatz Bool.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64 RoundingTest.
From Q Require Import Q256 Q256Real.
Require Import StageGappa ErfcxDecision ErfcxAccurateSquare ErfcxAccurateTerms
  NormalComparisons NormalFastDispatch NormalPublicModel NormalPublicBounds
  NormalAccurateDensity NormalAccurateCenter NormalAccurateCentralCdf NormalAccurateTailFull
  NormalAccurateOuter NormalAccurateLogCentral NormalAccurateLogPositive NormalAccurateLogNegative NormalLogOverflow
  NormalLogOverflowConstants NormalTailAnalytic NormalAccurateRounding.
Open Scope R_scope.

Definition normal_accurate_domain op x := match op with
  | NormalPdf=>bpow radix2(-400)<=Rabs x<=38.6
  | NormalCdf | NormalCentered=>Rabs x<=38.6
  | NormalLogCdf=>(0<=x -> x<=38.6) /\ (x<0 -> -x<B normal_log_overflow)
  end.

Lemma normal_signed_center_accurate (negative:bool) x : finite x -> /2<=B x<=38.6 ->
  normal_bounded (if negative then -(/2-normal_tail(B x))else /2-normal_tail(B x))
    (Q256.to_f64(if negative then neg_q(normal_q_outer_complement q_half x)else normal_q_outer_complement q_half x)).
Proof.
  intros Fx X;destruct q_half_ok as[Fhalf Half].
  destruct(normal_q_outer_complement_error q_half x (/2)Fhalf Half ltac:(split;lra)Fx X)as[Q [e [E Value]]].
  pose proof(normal_tail_range(B x)ltac:(lra))as Range.
  assert(Target : Rabs(/2-normal_tail(B x))<=1)by(rewrite Rabs_pos_eq;lra).
  assert(Epsilon : 0<=bpow radix2(-112)<=/4)by(split;[apply bpow_ge_0|interval with(i_prec 80)]).
  destruct negative.
  - destruct(neg_any _ Q)as[N Nvalue].
    assert(Error : exists e,Rabs e<=bpow radix2(-112) /\ qval(neg_q(normal_q_outer_complement q_half x))=(-(/2-normal_tail(B x)))*(1+e)).
    { exists e;split;[exact E|rewrite Nvalue,Value;ring]. }
    destruct(normal_q_bounded_rounded _ _ _ N ltac:(rewrite Rabs_Ropp;exact Target)Epsilon Error)as[F Rounded].
    unfold normal_bounded;split;[exact F|].
    replace(2*bpow radix2(-112))with(bpow radix2(-111))in Rounded by(bpow_num;field);exact Rounded.
  - destruct(normal_q_bounded_rounded _ _ _ Q Target Epsilon ltac:(exists e;split;assumption))as[F Rounded].
    unfold normal_bounded;split;[exact F|].
    replace(2*bpow radix2(-112))with(bpow radix2(-111))in Rounded by(bpow_num;field);exact Rounded.
Qed.

Local Opaque normal_q_density_regular normal_q_central_cdf normal_q_center normal_q_tail
  normal_q_outer_complement normal_q_log_cdf_central normal_q_log_cdf_positive normal_q_log_cdf_negative.

Theorem normal_accurate_bounded op x : finite x -> normal_accurate_domain op (B x) ->
  normal_bounded(normal_target op (B x))(normal_accurate64 op x).
Proof.
  intros Fx Domain;unfold normal_accurate64;apply normal_bound_fix_zero.
  assert(Fa : finite(b64_abs x))by(unfold b64_abs;destruct x;exact Fx).
  destruct(erfcx_pow2_ok(-1)ltac:(lia))as[Fhalf Half];change(bpow radix2(-1))with(/2)in Half.
  assert(Fzero : finite normal_zero)by reflexivity.
  assert(Zero : B normal_zero=0)by reflexivity.
  unfold normal_accurate_value64;destruct op;cbn[normal_accurate_domain normal_target]in *.
  - destruct(normal_q_density_regular_rounded(b64_abs x)Fa ltac:(rewrite B_abs;exact Domain))as[F Error].
    rewrite B_abs,normal_density_abs in Error;apply(normal_bound_weaken _ _ (-236));try assumption;lia.
  all: destruct(normal_le(b64_abs x)(erfcx_pow2(-1)))eqn:Central.
  - apply normal_le_true in Central;try assumption;rewrite B_abs,Half in Central.
    destruct(normal_q_central_cdf_rounded x Fx Central)as[F Error].
    apply(normal_bound_weaken _ _ (-245));try assumption;lia.
  - apply normal_le_false in Central;try assumption;rewrite B_abs,Half in Central.
    destruct(normal_lt x normal_zero)eqn:Negative.
    + apply normal_lt_true in Negative;try assumption;rewrite Zero in Negative.
      destruct(normal_q_tail_rounded(b64_abs x)Fa ltac:(rewrite B_abs;split;lra))as[F Error].
      rewrite B_abs,normal_negative_cdf in Error by lra;apply(normal_bound_weaken _ _ (-114));try assumption;lia.
    + apply normal_lt_false in Negative;try assumption;rewrite Zero in Negative.
      destruct q_one_ok as[Fone One].
      destruct(normal_q_outer_complement_rounded q_one (b64_abs x)1 Fone One ltac:(split;lra)Fa ltac:(rewrite B_abs;split;lra))as[F Error].
      rewrite B_abs,Rabs_pos_eq,normal_positive_cdf in Error by lra.
      apply(normal_bound_weaken _ _ (-111));try assumption;lia.
  - apply normal_le_true in Central;try assumption;rewrite B_abs,Half in Central.
    destruct(normal_q_center_rounded x Fx Central)as[F Error].
    apply(normal_bound_weaken _ _ (-246));try assumption;lia.
  - apply normal_le_false in Central;try assumption;rewrite B_abs,Half in Central.
    pose proof(normal_signed_center_accurate(Bsign 53 1024 x)(b64_abs x)Fa ltac:(rewrite B_abs;split;lra))as Result.
    rewrite B_abs in Result;pose proof(normal_input_sign x Fx)as Sign.
    destruct(Bsign 53 1024 x)eqn:Negative.
    + rewrite Rabs_left1,normal_tail_complement,normal_center_odd in Result by lra.
      replace(-(/2-(/2- -NormalCentered.normal_center(B x))))with(NormalCentered.normal_center(B x))in Result by ring;exact Result.
    + rewrite Rabs_pos_eq,normal_tail_complement in Result by lra.
      replace(/2-(/2-NormalCentered.normal_center(B x)))with(NormalCentered.normal_center(B x))in Result by ring;exact Result.
  - apply normal_le_true in Central;try assumption;rewrite B_abs,Half in Central.
    destruct(normal_q_log_cdf_central_rounded x Fx Central)as[F Error].
    apply(normal_bound_weaken _ _ (-228));try assumption;lia.
  - apply normal_le_false in Central;try assumption;rewrite B_abs,Half in Central.
    destruct(normal_lt normal_zero x)eqn:Positive.
    + apply normal_lt_true in Positive;try assumption;rewrite Zero in Positive.
      destruct Domain as[Upper Lower];specialize(Upper ltac:(lra)).
      destruct(normal_q_log_cdf_positive_rounded(b64_abs x)Fa ltac:(rewrite B_abs,Rabs_pos_eq by lra;rewrite Rabs_pos_eq in Central by lra;split;lra))as[F Error].
      rewrite B_abs,Rabs_pos_eq,normal_positive_cdf in Error by lra.
      apply(normal_bound_weaken _ _ (-111));try assumption;lia.
    + apply normal_lt_false in Positive;try assumption;rewrite Zero in Positive.
      destruct Domain as[Upper Lower];rewrite Rabs_left1 in Central by lra.
      specialize(Lower ltac:(lra)).
      destruct(normal_q_log_cdf_negative_finite_rounded(b64_abs x)Fa ltac:(rewrite B_abs,Rabs_left1 by lra;split;lra))as[F Error].
      rewrite B_abs,normal_negative_cdf in Error by lra.
      apply(normal_bound_weaken _ _ (-111));try assumption;lia.
Qed.
