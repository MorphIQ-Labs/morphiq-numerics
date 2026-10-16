(** Complete finite-tail compositions: the density and probability share
    the final grid test, and the positive logarithm spends the same budget. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64.
Require Import StageGappa ErfcxConstants ErfcxGaussianTarget ErfcxScaledAnalytic
  ErfcxTailIntegral NormalErfcxIdentity NormalTailAnalytic NormalGaussianRange NormalDensityMantissa
  ErfcxProduct NormalGaussianKernel NormalErfcxFastScaled
  NormalTailFastMantissa NormalFiniteDensity NormalFiniteRound NormalFiniteLog.
Open Scope R_scope.

Lemma normal_finite_tail_range x : 37<=x -> 0<normal_tail x<=bpow radix2(-980).
Proof.
  intros X;pose proof(normal_tail_range x ltac:(lra))as Positive.
  assert(Z : 1<=x/sqrt 2)by(interval with(i_prec 80)).
  assert(Factor : gaussian_erfcx(x/sqrt 2)<=1).
  { rewrite <-positive_erfcx_gaussian by lra;unfold positive_erfcx.
    destruct(tail_integral_limit ((/(x/sqrt 2))*(/(x/sqrt 2)))ltac:(nra))as[_ Range].
    assert(C : 0<inv_sqrt_pi<=1)by(unfold inv_sqrt_pi;split;interval with(i_prec 80)).
    assert(R : 0</(x/sqrt 2)<=1).
    { split;[apply Rinv_0_lt_compat;lra|rewrite <-Rinv_1;apply Rinv_le_contravar;lra]. }
    assert(P : 0<=inv_sqrt_pi/(x/sqrt 2)<=1).
    { change(0<=inv_sqrt_pi* /(x/sqrt 2)<=1);split;nra. }
    replace 1 with(1*1)by ring;apply Rmult_le_compat;lra. }
  assert(G : exp(-x*x/2)<=bpow radix2(-980)).
  { apply Rle_trans with(exp(-37*37/2));[apply exp_le;nra|interval with(i_prec 160)]. }
  split;[exact(proj1 Positive)|].
  unfold normal_tail;pose proof(exp_pos(-x*x/2));pose proof(bpow_gt_0 radix2(-980));nra.
Qed.

Lemma normal_finite_tail_exponent x : finite x -> 37<=B x<=39 ->
  let '(_,_,k):=normal_tail_fast_mantissa64 x in (-1101<=k<= -981)%Z.
Proof.
  intros F X;pose proof(normal_gaussian_finite_tail_exponent x F X)as K.
  unfold normal_tail_fast_mantissa64;destruct(normal_gaussian64 x)as[[a b]k].
  destruct(normal_erfcx_fast_scaled64 x)as[c d];destruct(product64 a b c d);lia.
Qed.

Definition normal_finite_tail64 x :=
  let '(h,l,k):=normal_tail_fast_mantissa64 x in normal_finite_scaled_fast64 h l (k+600).

Theorem normal_finite_tail_ieee x v : finite x -> 37<=B x<=39 ->
  normal_finite_tail64 x=Some v -> finite v /\ B v=rndF(normal_tail(B x)).
Proof.
  intros F X;pose proof(normal_tail_fast_mantissa_extended_ieee x F ltac:(split;lra))as Tail.
  pose proof(normal_finite_tail_exponent x F X)as Exponent.
  pose proof(normal_finite_tail_range (B x)(proj1 X))as Target.
  unfold normal_finite_tail64;destruct(normal_tail_fast_mantissa64 x)as[[h l]k].
  destruct Tail as[Fh [Fl [K [Norm [H [Ratio Error]]]]]].
  assert(Low : Rabs(B l)<=bpow radix2(-51)*B h).
  { apply normal_finite_low_ratio;[pose proof(bpow_gt_0 radix2(-10));lra|].
    replace(bpow radix2(-51))with(/2^51)by(bpow_num;field);exact Ratio. }
  assert(Z : 0<normal_tail(B x)/bpow radix2 k)by(apply Rdiv_lt_0_compat;[lra|apply bpow_gt_0]).
  rewrite Rabs_minus_sym in Error.
  destruct(normal_finite_tail_budget (B h)(B l)_ ltac:(pose proof(bpow_gt_0 radix2(-10));lra)Z Low Error)as[_ Budget].
  intros Decision;destruct(normal_finite_scaled_fast_ieee h l (k+600)
    (normal_tail(B x)/bpow radix2 k)v Fh Fl H Low Norm ltac:(lia))as[Fv V].
  - eapply Rle_trans;[exact Budget|bpow_num_all;nra].
  - exact Decision.
  - split;[exact Fv|rewrite V;replace(k+600-600)%Z with k by ring].
    f_equal;field;apply Rgt_not_eq,bpow_gt_0.
Qed.

Theorem normal_finite_log_tail_ieee x v : finite x -> 37<=B x<=39 ->
  normal_finite_tail64 x=Some v -> finite v /\ B v=rndF(-ln(1-normal_tail(B x))).
Proof.
  intros F X;pose proof(normal_tail_fast_mantissa_extended_ieee x F ltac:(split;lra))as Tail.
  pose proof(normal_finite_tail_exponent x F X)as Exponent.
  pose proof(normal_finite_tail_range (B x)(proj1 X))as Target.
  unfold normal_finite_tail64;destruct(normal_tail_fast_mantissa64 x)as[[h l]k].
  destruct Tail as[Fh [Fl [K [Norm [H [Ratio Error]]]]]].
  assert(Low : Rabs(B l)<=bpow radix2(-51)*B h).
  { apply normal_finite_low_ratio;[pose proof(bpow_gt_0 radix2(-10));lra|].
    replace(bpow radix2(-51))with(/2^51)by(bpow_num;field);exact Ratio. }
  rewrite Rabs_minus_sym in Error.
  pose proof(normal_finite_log_budget (normal_tail(B x))(B h)(B l)k Target
    ltac:(pose proof(bpow_gt_0 radix2(-10));lra)Low Error)as Budget.
  intros Decision;destruct(normal_finite_scaled_fast_ieee h l (k+600)
    ((-ln(1-normal_tail(B x)))/bpow radix2 k)v Fh Fl H Low Norm ltac:(lia)Budget Decision)as[Fv V].
  split;[exact Fv|rewrite V;replace(k+600-600)%Z with k by ring].
  f_equal;field;apply Rgt_not_eq,bpow_gt_0.
Qed.
