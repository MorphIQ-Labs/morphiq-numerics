(** Mantissa and relative low-word bounds for the scaled erfcx factor. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64 RoundingCore.
Require Import StageGappa ErfcxConstants ErfcxGaussianTarget ErfcxGaussianSeries
  NormalErfcxSensitivity NormalErfcxFastScaled.
Open Scope R_scope.

Lemma normal_erfcx_tail_upper z : /3<=z -> gaussian_erfcx z<=7/8.
Proof.
  intros Z;pose proof(normal_erfcx_decreasing (/3)z ltac:(split;lra))as Decreasing.
  pose proof(gaussian_approx_error 2 (/3))as Approx.
  assert(AtThird : gaussian_erfcx(/3)<=7/8).
  { assert(Bound : gaussian_approx 2 (/3)+
      2*inv_sqrt_pi*exp((/3)*(/3))*Rabs(/3)*((((/3)*(/3))^3)/INR(fact 3))<=7/8).
    { unfold gaussian_approx,gaussian_sum,inv_sqrt_pi;cbn [sum_f_R0 fact Nat.mul Nat.add Nat.sub INR];interval with(i_prec 100). }
    apply Rabs_le_inv in Approx;lra. }
  lra.
Qed.

Theorem normal_erfcx_fast_scaled_words_extended x : finite x -> /2<=B x<=39 ->
  let '(h,l):=normal_erfcx_fast_scaled64 x in
  bpow radix2 (-9)<=B h<=1 /\ -/2^51<=B l/B h<=/2^51.
Proof.
  intros Fx X;pose proof(normal_erfcx_fast_scaled_ieee_extended x Fx X)as Scaled.
  destruct(normal_erfcx_fast_scaled64 x)as[h l];destruct Scaled as[Fh [Fl [Norm [H [L Error]]]]].
  assert(Z : /3<=B x/sqrt 2<=28)by(split;interval with(i_prec 80)).
  pose proof(normal_erfcx_tail_upper (B x/sqrt 2)(proj1 Z))as Target.
  pose proof(normal_erfcx_compact_lower (B x/sqrt 2)ltac:(split;lra))as Positive.
  assert(Sum : bpow radix2 (-10)<=B h+B l<=1).
  { apply Rabs_le_inv in Error;bpow_num_all;split;nra. }
  assert(High : B h<=1).
  { rewrite Norm;change 1 with(bpow radix2 0);apply round_le_generic;[exact _|exact _| |exact(proj2 Sum)].
    apply generic_format_bpow;unfold FLT_exp,emin,prec;lia. }
  pose proof(rnd_rel (B h+B l)ltac:(rewrite Rabs_pos_eq;[eapply Rle_trans with(bpow radix2 (-10));[apply bpow_le;lia|exact(proj1 Sum)]|pose proof(bpow_gt_0 radix2 (-10));lra]))as Rounded.
  change(Rabs(rndF(B h+B l)-(B h+B l))<=bpow radix2 (-53)*Rabs(B h+B l))in Rounded.
  rewrite <-Norm in Rounded;replace(B h-(B h+B l))with(-B l)in Rounded by ring.
  rewrite Rabs_Ropp,(Rabs_pos_eq(B h+B l))in Rounded by(pose proof(bpow_gt_0 radix2 (-10));lra).
  assert(Low : Rabs(B l)<=bpow radix2 (-52)*B h).
  { pose proof(Rle_abs(B l));bpow_num_all;nra. }
  split;[split;[exact(proj1 H)|exact High]|].
  assert(Bound : Rabs(B l/B h)<=bpow radix2 (-52)).
  { unfold Rdiv;rewrite Rabs_mult,Rabs_Rinv,(Rabs_pos_eq(B h))by(pose proof(bpow_gt_0 radix2 (-9));lra).
    apply(Rmult_le_reg_r(B h));[pose proof(bpow_gt_0 radix2 (-9));lra|].
    rewrite Rmult_assoc,Rinv_l,Rmult_1_r by(pose proof(bpow_gt_0 radix2 (-9));lra);nra. }
  apply Rabs_le_inv in Bound;bpow_num_all;split;lra.
Qed.

Theorem normal_erfcx_fast_scaled_words x : finite x -> /2<=B x<=37 ->
  let '(h,l):=normal_erfcx_fast_scaled64 x in
  bpow radix2 (-9)<=B h<=1 /\ -/2^51<=B l/B h<=/2^51.
Proof. intros F X;apply (normal_erfcx_fast_scaled_words_extended x F);split;lra. Qed.
