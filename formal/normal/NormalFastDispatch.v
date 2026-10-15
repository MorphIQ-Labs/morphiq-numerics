(** Scalar fast-path dispatch. The four internal operations share the
    standard-normal targets; CCDF uses the CDF at the reflected input. *)
From Coq Require Import Reals ZArith Lia Lra Bool.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add Encodings RoundingTest.
Require Import StageGappa ErfcxDecision NormalComparisons
  NormalAccurateDensity NormalAccurateCentralCdf NormalCentered NormalTailAnalytic
  NormalDensityDecision NormalCenterCentral NormalCdfCentralFast NormalTailDecision
  NormalOuterSigned NormalLogDecision NormalLogNegativeFast NormalLogPositiveFast
  NormalLogTailStages NormalLogTailHuge NormalLogOverflowConstants.
Open Scope R_scope.

Inductive normal_operation := NormalPdf | NormalCdf | NormalCentered | NormalLogCdf.
Definition normal_target op x := match op with
  | NormalPdf=>normal_density x | NormalCdf=>normal_cdf x
  | NormalCentered=>normal_center x | NormalLogCdf=>ln(normal_cdf x) end.
Definition normal_thirty_seven : f64 := b64_of_bits 4630404104378646528.
Definition normal_ordinary_dispatch64 op x :=
  let a:=b64_abs x in
  if normal_lt normal_thirty_seven a ||
    (match op with NormalPdf=>false | _=>normal_lt a (erfcx_pow2(-450))end)
  then None else
  match op with
  | NormalPdf=>normal_density_fast_decide64 a
  | NormalCdf=>if normal_le a (erfcx_pow2(-1))then normal_cdf_central_decide64 x else
      if normal_lt x normal_zero then normal_tail_decide64 a else
      normal_outer_signed_decide64 false (erfcx_pow2 0)a
  | NormalCentered=>if normal_le a (erfcx_pow2(-1))then normal_center_central_decide64 x else
      normal_outer_signed_decide64 (normal_lt x normal_zero)(erfcx_pow2(-1))a
  | NormalLogCdf=>if normal_le a (erfcx_pow2(-1))then normal_log_central_decide64 x else
      if normal_lt x normal_zero then normal_log_negative_decide64 a else normal_log_positive_decide64 a
  end.

Lemma normal_thirty_seven_ok : finite normal_thirty_seven /\ B normal_thirty_seven=37.
Proof.
  split;[exact(bits_finite 4630404104378646528 false 5207287069147136 (-47) eq_refl)|].
  change(5207287069147136*bpow radix2(-47)=37);bpow_num;field.
Qed.

Lemma normal_density_abs x : normal_density(Rabs x)=normal_density x.
Proof.
  unfold normal_density;f_equal;f_equal.
  pose proof(Rabs_mult x x);rewrite Rabs_pos_eq in H by nra;unfold Rdiv;nra.
Qed.

Lemma normal_positive_cdf x : 1-normal_tail x=normal_cdf x.
Proof. rewrite normal_tail_complement;unfold normal_cdf;field. Qed.
Lemma normal_negative_cdf x : x<=0 -> normal_tail(Rabs x)=normal_cdf x.
Proof.
  intros X;rewrite Rabs_left1 by exact X;rewrite normal_tail_negative_cdf.
  replace(- -x)with x by ring;reflexivity.
Qed.
Lemma normal_outer_center_target (negative:bool) x :
  (negative=true -> x<0) -> (negative=false -> 0<=x) ->
  (if negative then -(/2-normal_tail(Rabs x)) else /2-normal_tail(Rabs x))=normal_center x.
Proof.
  intros N P;destruct negative.
  - specialize(N eq_refl);rewrite Rabs_left1,normal_tail_complement,normal_center_odd by lra;ring.
  - specialize(P eq_refl);rewrite Rabs_pos_eq,normal_tail_complement by lra;ring.
Qed.

Local Opaque normal_density_fast_decide64 normal_cdf_central_decide64
  normal_center_central_decide64 normal_log_central_decide64 normal_tail_decide64
  normal_outer_signed_decide64 normal_log_negative_decide64 normal_log_positive_decide64.

Theorem normal_ordinary_dispatch_decided op x v : finite x ->
  (op=NormalPdf -> bpow radix2(-33)<=Rabs(B x)) ->
  normal_ordinary_dispatch64 op x=Some v -> finite v /\ B v=rndF(normal_target op (B x)).
Proof.
  intros Fx Pdf Decision.
  assert(Fa : finite(b64_abs x))by(unfold b64_abs;destruct x;exact Fx).
  destruct normal_thirty_seven_ok as[F37 V37].
  destruct(erfcx_pow2_ok(-450)ltac:(lia))as[Ftiny Tiny].
  destruct(erfcx_pow2_ok(-1)ltac:(lia))as[Fhalf Half];change(bpow radix2(-1))with(/2)in Half.
  destruct(erfcx_pow2_ok 0 ltac:(lia))as[Fone One];change(bpow radix2 0)with 1 in One.
  assert(Fzero : finite normal_zero)by reflexivity.
  assert(Zero : B normal_zero=0)by reflexivity.
  unfold normal_ordinary_dispatch64 in Decision.
  destruct(normal_lt normal_thirty_seven (b64_abs x) ||
    match op with NormalPdf=>false|_=>normal_lt(b64_abs x)(erfcx_pow2(-450))end)eqn:Screen;[discriminate|].
  apply orb_false_iff in Screen as[Range TinyScreen].
  apply normal_lt_false in Range;try assumption;rewrite B_abs,V37 in Range.
  destruct op;cbn[normal_target]in *.
  - pose proof(normal_density_fast_decided(b64_abs x)v Fa
      ltac:(rewrite B_abs;split;[apply Pdf;reflexivity|exact Range])Decision)as Result.
    rewrite B_abs,normal_density_abs in Result;exact Result.
  all: apply normal_lt_false in TinyScreen;try assumption;rewrite B_abs,Tiny in TinyScreen.
  all: destruct(normal_le(b64_abs x)(erfcx_pow2(-1)))eqn:Central.
  - apply normal_le_true in Central;try assumption;rewrite B_abs,Half in Central.
    apply normal_cdf_central_decided;[exact Fx|split;assumption|exact Decision].
  - apply normal_le_false in Central;try assumption;rewrite B_abs,Half in Central.
    destruct(normal_lt x normal_zero)eqn:Negative.
    + apply normal_lt_true in Negative;try assumption;rewrite Zero in Negative.
      pose proof(normal_tail_fast_decided(b64_abs x)v Fa ltac:(rewrite B_abs;split;lra)Decision)as Result.
      rewrite B_abs,normal_negative_cdf in Result by lra;exact Result.
    + apply normal_lt_false in Negative;try assumption;rewrite Zero in Negative.
      pose proof(normal_outer_signed_decided false (erfcx_pow2 0)(b64_abs x)v Fone
        ltac:(rewrite One;split;lra)Fa ltac:(rewrite B_abs;split;lra)Decision)as Result.
      unfold normal_outer_signed_target in Result;rewrite One,B_abs,Rabs_pos_eq in Result by lra.
      rewrite normal_positive_cdf in Result;exact Result.
  - apply normal_le_true in Central;try assumption;rewrite B_abs,Half in Central.
    apply normal_center_central_decided;[exact Fx|split;assumption|exact Decision].
  - apply normal_le_false in Central;try assumption;rewrite B_abs,Half in Central.
    pose proof(normal_outer_signed_decided (normal_lt x normal_zero)(erfcx_pow2(-1))(b64_abs x)v Fhalf
      ltac:(rewrite Half;split;lra)Fa ltac:(rewrite B_abs;split;lra)Decision)as Result.
    unfold normal_outer_signed_target in Result;rewrite Half,B_abs in Result.
    rewrite normal_outer_center_target in Result.
    + exact Result.
    + intros N;apply normal_lt_true in N;try assumption;rewrite Zero in N;exact N.
    + intros P;apply normal_lt_false in P;try assumption;rewrite Zero in P;exact P.
  - apply normal_le_true in Central;try assumption;rewrite B_abs,Half in Central.
    apply normal_log_central_decided;[exact Fx|split;assumption|exact Decision].
  - apply normal_le_false in Central;try assumption;rewrite B_abs,Half in Central.
    destruct(normal_lt x normal_zero)eqn:Negative.
    + apply normal_lt_true in Negative;try assumption;rewrite Zero in Negative.
      pose proof(normal_log_negative_decided(b64_abs x)v Fa ltac:(rewrite B_abs;split;lra)Decision)as Result.
      rewrite B_abs,normal_negative_cdf in Result by lra;exact Result.
    + apply normal_lt_false in Negative;try assumption;rewrite Zero in Negative.
      pose proof(normal_log_positive_decided(b64_abs x)v Fa ltac:(rewrite B_abs;split;lra)Decision)as Result.
      rewrite B_abs,Rabs_pos_eq,normal_positive_cdf in Result by lra;exact Result.
Qed.

(** Only negative log-CDF bypasses the ordinary composition's 37 screen. *)
Definition normal_fast_dispatch64 op x :=
  match op with
  | NormalLogCdf=>if normal_lt x (fneg normal_thirty_seven)then
      let a:=b64_abs x in
      if normal_lt a normal_log_overflow then
        if normal_lt a (erfcx_pow2 45)then normal_log_tail_stages64 a
        else normal_log_tail_huge_decide64 a
      else None
    else normal_ordinary_dispatch64 op x
  | _=>normal_ordinary_dispatch64 op x
  end.

Theorem normal_fast_dispatch_decided op x v : finite x ->
  (op=NormalPdf -> bpow radix2(-33)<=Rabs(B x)) ->
  normal_fast_dispatch64 op x=Some v -> finite v /\ B v=rndF(normal_target op (B x)).
Proof.
  intros Fx Pdf Decision;destruct op;cbn[normal_fast_dispatch64]in Decision.
  1-3: eapply normal_ordinary_dispatch_decided;eauto.
  destruct(normal_lt x (fneg normal_thirty_seven))eqn:Far.
  2: eapply normal_ordinary_dispatch_decided;eauto.
  destruct normal_thirty_seven_ok as[F37 V37].
  assert(Fneg : finite(fneg normal_thirty_seven))by(unfold fneg,b64_opp;rewrite is_finite_Bopp;exact F37).
  assert(N37 : B(fneg normal_thirty_seven)= -B normal_thirty_seven)by(apply B2R_Bopp).
  apply normal_lt_true in Far;try assumption;rewrite N37,V37 in Far.
  assert(Fa : finite(b64_abs x))by(unfold b64_abs;destruct x;exact Fx).
  assert(A : 37<B(b64_abs x))by(rewrite B_abs,Rabs_left1;lra).
  destruct normal_log_overflow_ok as[Fo _].
  destruct(normal_lt(b64_abs x)normal_log_overflow)eqn:Finite;[|discriminate].
  apply normal_lt_true in Finite;try assumption.
  destruct(erfcx_pow2_ok 45 ltac:(lia))as[Fhuge Huge].
  destruct(normal_lt(b64_abs x)(erfcx_pow2 45))eqn:Large.
  - apply normal_lt_true in Large;try assumption;rewrite Huge in Large.
    pose proof(normal_log_tail_stages_decided (b64_abs x) v Fa ltac:(split;lra) Decision)as Result.
    rewrite B_abs,normal_negative_cdf in Result by lra;exact Result.
  - apply normal_lt_false in Large;try assumption;rewrite Huge in Large.
    pose proof(normal_log_tail_huge_decided (b64_abs x) v Fa ltac:(split;lra) Decision)as Result.
    rewrite B_abs,normal_negative_cdf in Result by lra;exact Result.
Qed.
