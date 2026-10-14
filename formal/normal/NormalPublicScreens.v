(** The finite constant and saturation results, with rounding proofs. *)
From Coq Require Import Reals ZArith Lia Lra Psatz Bool.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add RoundingGaps RoundingTest.
Require Import StageGappa ErfcxDecision Exp2Thresholds Ln1pLemmas
  NormalCentered NormalAccurateDensity NormalAccurateCentralCdf NormalConstants
  NormalTailAnalytic NormalTailSaturation NormalTailThresholdConstants NormalDensitySaturation
  NormalDensityTiny NormalComparisons NormalFastDispatch NormalPublicModel NormalPublicBounds.
Open Scope R_scope.

Lemma normal_zero_round f : Rabs f<=bpow radix2(-1075) -> rndF f=0.
Proof.
  intros F;apply Rabs_le_inv in F;apply Rle_antisym.
  - rewrite <-round_underflow_tie;apply round_le;try exact _;lra.
  - replace 0 with(rndF(-bpow radix2(-1075)))by(rewrite round_NE_opp_ne,round_underflow_tie;ring).
    apply round_le;try exact _;lra.
Qed.

Lemma normal_round_power_close k f : (-1074<=k<=1023)%Z ->
  Rabs(f-bpow radix2 k)<bpow radix2(k-54) -> rndF f=bpow radix2 k.
Proof.
  intros K Error;apply round_relative_close.
  - apply fmt_pow;lia.
  - pose proof(bpow_gt_0 radix2 k);lra.
  - rewrite(Rabs_pos_eq(bpow radix2 k))by apply bpow_ge_0.
    replace(k-54)%Z with(k+ -54)%Z in Error by ring;rewrite bpow_plus in Error.
    replace(bpow radix2(-54))with(/2^54)in Error by(bpow_num;field);exact Error.
Qed.

Lemma normal_center_zero : normal_center 0=0.
Proof. unfold normal_center;ring. Qed.
Lemma normal_cdf_zero : normal_cdf 0=/2.
Proof. unfold normal_cdf;rewrite normal_center_zero;ring. Qed.
Lemma normal_ln2_high_round : B normal_ln2_hi=rndF(ln 2).
Proof.
  destruct normal_ln2_hi_ok as[F Value];symmetry;apply round_relative_close.
  - apply B_fmt.
  - rewrite Value;interval with(i_prec 80).
  - rewrite Value;interval with(i_prec 200).
Qed.

Theorem normal_zero_result_bounded op x : finite x -> B x=0 ->
  normal_bounded(normal_target op (B x))
    (match op with NormalPdf=>normal_density_hi | NormalCdf=>erfcx_pow2(-1)
      | NormalCentered=>x | NormalLogCdf=>fneg normal_ln2_hi end).
Proof.
  intros Fx X;destruct op;cbn[normal_target];rewrite X.
  - apply normal_exact_bounded;[exact(proj1 normal_density_hi_ok)|].
    symmetry;apply normal_density_tiny_correct;rewrite Rabs_R0;apply bpow_ge_0.
  - destruct(erfcx_pow2_ok(-1)ltac:(lia))as[F Half];apply normal_exact_bounded;[exact F|].
    rewrite normal_cdf_zero;change(/2)with(bpow radix2(-1));rewrite <-Half;symmetry;apply round_generic;try exact _;apply B_fmt.
  - apply normal_exact_bounded;[exact Fx|rewrite X,normal_center_zero,round_0 by exact _;reflexivity].
  - apply normal_exact_bounded.
    + unfold fneg,b64_opp;rewrite is_finite_Bopp;exact(proj1 normal_ln2_hi_ok).
    + unfold fneg,b64_opp;rewrite B2R_Bopp,normal_cdf_zero,ln_Rinv by lra.
      rewrite round_NE_opp_ne,normal_ln2_high_round;reflexivity.
Qed.

Theorem normal_pdf_saturated_bounded x : finite x -> B normal_pdf_zero<=Rabs(B x) ->
  normal_bounded(normal_density(B x))normal_zero.
Proof.
  intros Fx X;assert(Fa : finite(b64_abs x))by(unfold b64_abs;destruct x;exact Fx).
  pose proof(normal_pdf_zero_midpoint(b64_abs x)Fa ltac:(rewrite B_abs;apply Rabs_pos))as[Upper _].
  specialize(Upper ltac:(rewrite B_abs;exact X));rewrite B_abs,normal_density_abs in Upper.
  pose proof(normal_density_range(B x))as Range.
  apply normal_exact_bounded;[reflexivity|].
  change(0=rndF(normal_density(B x)));symmetry;apply normal_zero_round;rewrite Rabs_pos_eq;lra.
Qed.

Theorem normal_cdf_saturated_one x : finite x -> B normal_cdf_one<=B x ->
  normal_bounded(normal_cdf(B x))(erfcx_pow2 0).
Proof.
  intros Fx X;destruct normal_cdf_one_ok as[_ Value].
  assert(Positive : 0<B x)by(rewrite Value in X;lra).
  pose proof(normal_cdf_one_midpoint x Fx Positive)as[Upper _];specialize(Upper X).
  pose proof(normal_tail_range(B x)Positive)as Tail.
  destruct(erfcx_pow2_ok 0 ltac:(lia))as[F One];apply normal_exact_bounded;[exact F|].
  rewrite One;replace(normal_cdf(B x))with(1-normal_tail(B x))by apply normal_positive_cdf.
  symmetry;apply normal_round_power_close;[lia|].
  change(bpow radix2 0)with 1;change(0-54)%Z with(-54)%Z.
  replace(1-normal_tail(B x)-1)with(-normal_tail(B x))by ring;rewrite Rabs_Ropp,Rabs_pos_eq by lra;exact Upper.
Qed.

Theorem normal_cdf_saturated_zero x : finite x -> B x<= -B normal_tail_zero ->
  normal_bounded(normal_cdf(B x))normal_zero.
Proof.
  intros Fx X;destruct normal_tail_zero_ok as[_ Value].
  assert(Negative : B x<0)by(rewrite Value in X;lra).
  assert(Fa : finite(b64_abs x))by(unfold b64_abs;destruct x;exact Fx).
  pose proof(normal_tail_zero_midpoint(b64_abs x)Fa ltac:(rewrite B_abs,Rabs_left1;lra))as[Upper _].
  specialize(Upper ltac:(rewrite B_abs,Rabs_left1;lra)).
  pose proof(normal_tail_range(Rabs(B x))ltac:(rewrite Rabs_left1;lra))as Tail.
  rewrite B_abs,normal_negative_cdf in Upper by lra;rewrite normal_negative_cdf in Tail by lra.
  apply normal_exact_bounded;[reflexivity|].
  change(0=rndF(normal_cdf(B x)));symmetry;apply normal_zero_round;rewrite Rabs_pos_eq;lra.
Qed.

Theorem normal_center_saturated_half x : finite x -> B normal_centered_half<=Rabs(B x) ->
  normal_bounded(normal_center(B x))(normal_signed_half x).
Proof.
  intros Fx X;destruct normal_centered_half_ok as[_ Value].
  assert(Positive : 0<Rabs(B x))by(rewrite Value in X;lra).
  assert(Fa : finite(b64_abs x))by(unfold b64_abs;destruct x;exact Fx).
  pose proof(normal_centered_half_midpoint(b64_abs x)Fa ltac:(rewrite B_abs;exact Positive))as[Upper _].
  specialize(Upper ltac:(rewrite B_abs;exact X));rewrite B_abs in Upper.
  pose proof(normal_tail_range(Rabs(B x))Positive)as Tail.
  assert(Round : rndF(/2-normal_tail(Rabs(B x)))=/2).
  { change(/2)with(bpow radix2(-1))at 2;apply normal_round_power_close;[lia|].
    change(bpow radix2(-1))with(/2);change(-1-54)%Z with(-55)%Z.
    replace(/2-normal_tail(Rabs(B x))-/2)with(-normal_tail(Rabs(B x)))by ring.
    rewrite Rabs_Ropp,Rabs_pos_eq by lra;exact Upper. }
  destruct(erfcx_pow2_ok(-1)ltac:(lia))as[Fhalf Half];change(bpow radix2(-1))with(/2)in Half.
  pose proof(normal_input_sign x Fx)as Sign.
  unfold normal_signed_half;destruct(Bsign 53 1024 x)eqn:Negative.
  - rewrite Rabs_left1,normal_tail_complement,normal_center_odd in Round by lra.
    replace(/2-(/2- -normal_center(B x)))with(-normal_center(B x))in Round by ring.
    rewrite round_NE_opp_ne in Round.
    apply normal_exact_bounded.
    + unfold fneg,b64_opp;rewrite is_finite_Bopp;exact Fhalf.
    + unfold fneg,b64_opp;rewrite B2R_Bopp,Half;lra.
  - rewrite Rabs_pos_eq,normal_tail_complement in Round by lra.
    replace(/2-(/2-normal_center(B x)))with(normal_center(B x))in Round by ring.
    apply normal_exact_bounded;[exact Fhalf|rewrite Half;exact(eq_sym Round)].
Qed.

Theorem normal_log_saturated_zero x : finite x -> B normal_tail_zero<=B x ->
  normal_bounded(ln(normal_cdf(B x)))normal_negative_zero.
Proof.
  intros Fx X;destruct normal_tail_zero_ok as[_ Value].
  assert(Positive : 0<B x)by(rewrite Value in X;lra).
  pose proof(normal_log_positive_zero_midpoint x Fx Positive)as[Upper _];specialize(Upper X).
  rewrite normal_positive_cdf in Upper.
  apply normal_exact_bounded;[reflexivity|].
  change(0=rndF(ln(normal_cdf(B x))));symmetry;apply normal_zero_round.
  rewrite Rabs_left1;lra.
Qed.
