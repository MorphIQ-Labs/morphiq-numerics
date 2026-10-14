(** Compose the retained argument reduction, high-word erfcx kernel and
    low-word correction into the scaled erfcx factor used by normal tails. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Coquelicot Require Import Coquelicot.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64 RoundingConstant.
Require Import StageGappa ErfcxConstants ErfcxGaussianTarget NormalErfcxSensitivity
  NormalFastScaledArgument NormalErfcxCorrection NormalCenterFastTail.
Open Scope R_scope.

Lemma normal_erfcx_unit_upper x : 0<x -> gaussian_erfcx x<=1.
Proof.
  intros X;destruct(MVT_cor2 gaussian_erfcx normal_erfcx_derivative 0 x X)as[c [Difference C]].
  - intros;apply is_derive_Reals,gaussian_erfcx_derivative.
  - pose proof(normal_erfcx_derivative_bounds c ltac:(lra))as[Bounds _].
    rewrite gaussian_erfcx_at_zero in Difference;nra.
Qed.

Lemma normal_erfcx_compact_lower x : 0<x<=33 -> /256<=gaussian_erfcx x.
Proof.
  intros X;assert(Pi : /2<=inv_sqrt_pi)by(unfold inv_sqrt_pi;interval with(i_prec 80)).
  destruct(Rle_dec 1 x)as[Large|Small].
  - pose proof(normal_erfcx_large_lower x Large)as Lower.
    assert(/256<=inv_sqrt_pi/(2*x))by(interval with(i_prec 80));lra.
  - pose proof(normal_erfcx_small_lower x ltac:(split;lra));lra.
Qed.

Definition normal_erfcx_fast_scaled64 x :=
  let '(h,l):=normal_fast_scaled_argument64 x in normal_erfcx_correction64 h l.

Theorem normal_erfcx_fast_scaled_ieee x : finite x -> /2<=B x<=37 ->
  let '(h,l):=normal_erfcx_fast_scaled64 x in
  finite h /\ finite l /\ B h=rndF(B h+B l) /\
  bpow radix2 (-9)<=B h<=2 /\ Rabs(B l)<=bpow radix2 (-53) /\
  Rabs((B h+B l)-gaussian_erfcx(B x/sqrt 2))<=bpow radix2 (-66)*gaussian_erfcx(B x/sqrt 2).
Proof.
  intros Fx X;pose proof(normal_fast_scaled_argument_ieee x Fx X)as Argument.
  unfold normal_erfcx_fast_scaled64;destruct(normal_fast_scaled_argument64 x)as[a b].
  destruct Argument as[Fa [Fb [Anorm [A [Bl ArgumentError]]]]].
  pose proof(normal_erfcx_correction_ieee a b Fa Fb A Bl)as Corrected.
  destruct(normal_erfcx_correction64 a b)as[h l];destruct Corrected as[Fh [Fl [Norm Correction]]].
  set(z:=B x/sqrt 2)in *.
  assert(Z : /3<=z<=27)by(unfold z;split;interval with(i_prec 80)).
  assert(Target : /256<=gaussian_erfcx z<=1).
  { split;[apply normal_erfcx_compact_lower;split;lra|apply normal_erfcx_unit_upper;lra]. }
  assert(InputError : Rabs(gaussian_erfcx(B a+B b)-gaussian_erfcx z)<=bpow radix2 (-99)*gaussian_erfcx z).
  { pose proof(normal_erfcx_scaled_argument_error z (B a+B b)ltac:(lra)
      ltac:(eapply Rle_trans;[exact ArgumentError|bpow_num_all;nra]))as Sensitivity.
    eapply Rle_trans;[exact Sensitivity|].
    assert(Scaled : Rabs(B a+B b-z)/z<=bpow radix2 (-103)).
    { apply(Rmult_le_reg_r z);[lra|];unfold Rdiv;rewrite Rmult_assoc,Rinv_l,Rmult_1_r by lra;nra. }
    bpow_num_all;nra. }
  assert(HighDifference : Rabs(B a-z)<=bpow radix2 (-48)).
  { replace(B a-z)with(((B a+B b)-z)-B b)by ring.
    eapply Rle_trans;[apply Rabs_triang|];rewrite Rabs_Ropp;bpow_num_all;nra. }
  assert(HighError : Rabs(gaussian_erfcx(B a)-gaussian_erfcx z)<=bpow radix2 (-42)*gaussian_erfcx z).
  { pose proof(normal_erfcx_scaled_argument_error z (B a)ltac:(lra)
      ltac:(eapply Rle_trans;[exact HighDifference|bpow_num_all;lra]))as Sensitivity.
    eapply Rle_trans;[exact Sensitivity|].
    assert(Scaled : Rabs(B a-z)/z<=3*bpow radix2 (-48)).
    { apply(Rmult_le_reg_r z);[lra|];unfold Rdiv;rewrite Rmult_assoc,Rinv_l,Rmult_1_r by lra;bpow_num_all;nra. }
    bpow_num_all;nra. }
  assert(Error : Rabs((B h+B l)-gaussian_erfcx z)<=bpow radix2 (-66)*gaussian_erfcx z).
  { replace((B h+B l)-gaussian_erfcx z)with
      (((B h+B l)-gaussian_erfcx(B a+B b))+(gaussian_erfcx(B a+B b)-gaussian_erfcx z))by ring.
    eapply Rle_trans;[apply Rabs_triang|];apply Rabs_le_inv in HighError;bpow_num_all;nra. }
  assert(Range : bpow radix2 (-9)<=B h+B l<=2).
  { apply Rabs_le_inv in Error;bpow_num_all;split;nra. }
  assert(High : bpow radix2 (-9)<=B h<=2).
  { rewrite Norm;split.
    - apply round_ge_generic;[exact _|exact _| |exact(proj1 Range)].
      apply generic_format_bpow;unfold FLT_exp,emin,prec;lia.
    - change 2 with(bpow radix2 1);apply round_le_generic;[exact _|exact _| |exact(proj2 Range)].
      apply generic_format_bpow;unfold FLT_exp,emin,prec;lia. }
  pose proof(rnd_err_below(B h+B l)1 ltac:(lia)
    ltac:(change(bpow radix2 1)with 2;rewrite Rabs_pos_eq;[exact(proj2 Range)|pose proof(bpow_gt_0 radix2 (-9));lra]))as Rounded.
  rewrite <-Norm in Rounded;change(1-54)%Z with(-53)%Z in Rounded.
  assert(Low : Rabs(B l)<=bpow radix2 (-53)).
  { replace(B h-(B h+B l))with(-B l)in Rounded by ring;rewrite Rabs_Ropp in Rounded;exact Rounded. }
  repeat split;tauto.
Qed.
