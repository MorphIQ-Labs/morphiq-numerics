(** The logarithm of the scaled erfcx factor stays representable in Q256
    even when the normal probability itself would underflow in binary64. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary.
From Interval Require Import Tactic.
From Binary64 Require Import IEEE64.
From Q Require Import Q256 Q256Real.
Require Import StageGappa ErfcxConstants ErfcxGaussianTarget ErfcxAccurateCenterModel
  ErfcxAccurateCenterBounds NormalErfcxSensitivity NormalAccurateTailFull
  NormalLogReduction NormalLogSeries NormalLogarithm NormalLogSensitivity.
Open Scope R_scope.

Theorem normal_erfcx_log_range z : /4<=z<=bpow radix2 1024 ->
  bpow radix2 (-1026)<=gaussian_erfcx z<=3.
Proof.
  intros Z;assert (C : /2<=inv_sqrt_pi)by(unfold inv_sqrt_pi;interval with(i_prec 80)).
  split.
  - destruct(Rle_dec 1 z)as[Large|Small].
    + eapply Rle_trans;[|apply normal_erfcx_large_lower;exact Large].
      apply(Rmult_le_reg_r(2*z));[lra|].
      unfold Rdiv;rewrite Rmult_assoc,Rinv_l,Rmult_1_r by lra.
      assert (Product : bpow radix2 (-1026)*(2*z)<=bpow radix2 (-1026)*(2*bpow radix2 1024)).
      { apply Rmult_le_compat_l;[apply bpow_ge_0|lra]. }
      replace(bpow radix2 (-1026)*(2*bpow radix2 1024))with(/2)in Product by(bpow_num;field);lra.
    + pose proof(normal_erfcx_small_lower z ltac:(split;lra))as Lower.
      assert(bpow radix2 (-1026)<=/8)by(change(/8)with(bpow radix2 (-3));apply bpow_le;lia);lra.
  - assert (Center : accurate_center 24=/4).
    { unfold accurate_center,center_numerator,center_denominator;cbn;field. }
    destruct(accurate_center_bounds 24 ltac:(lia))as[_ [_ Upper]];rewrite Center in Upper.
    pose proof(normal_erfcx_decreasing (/4)z ltac:(split;lra));lra.
Qed.

Lemma normal_scaled_real_range x : finite x -> /2<=B x ->
  /4<=B x/sqrt 2<=bpow radix2 1024.
Proof.
  intros F X;assert (Scale : /2<=/sqrt 2<=1)by(split;interval with(i_prec 80)).
  pose proof(abs_B2R_lt_emax 53 1024 x)as Upper;change(Rabs(B x)<bpow radix2 1024)in Upper.
  rewrite Rabs_pos_eq in Upper by lra;unfold Rdiv;split;nra.
Qed.

Definition normal_q_log_tail_input x := mul_pow2(normal_q_scaled_erfcx x)(-1).

Theorem normal_q_log_tail_input_error x : finite x -> /2<=B x ->
  valid(normal_q_log_tail_input x) /\ exists e,Rabs e<=bpow radix2 (-116) /\
  qval(normal_q_log_tail_input x)=(gaussian_erfcx(B x/sqrt 2)/2)*(1+e).
Proof.
  intros F X;destruct(normal_q_scaled_erfcx_error x F X)as[Q [e [E Value]]].
  destruct(mul_pow2_any _ (-1) Q)as[Result Product].
  split;[exact Result|];exists e;split;[exact E|].
  unfold normal_q_log_tail_input;rewrite Product,Value;change(bpow radix2 (-1))with(/2);field.
Qed.

Theorem normal_q_log_tail_input_range x : finite x -> /2<=B x ->
  bpow radix2 (-1030)<=qval(normal_q_log_tail_input x)<=2.
Proof.
  intros F X;destruct(normal_q_log_tail_input_error x F X)as[_ [e [E Value]]].
  pose proof(normal_erfcx_log_range _ (normal_scaled_real_range x F X))as Range.
  apply Rabs_le_inv in E;assert(bpow radix2 (-116)<=/4)by(interval with(i_prec 80)).
  rewrite Value;split.
  - replace(bpow radix2 (-1030))with(bpow radix2 (-1026)/16)by(bpow_num;field).
    pose proof(bpow_gt_0 radix2 (-1026));nra.
  - nra.
Qed.

Lemma normal_q_tail_log_exponent x : valid x -> bpow radix2 (-1030)<=qval x<=2 ->
  (Z.abs(top x)<=2048)%Z.
Proof.
  intros X Range;pose proof(bpow_gt_0 radix2 (-1030))as Positive.
  pose proof(normal_q_top_range x X ltac:(lra))as[Lower Upper];rewrite Rabs_pos_eq in Lower,Upper by lra.
  assert (High : (top x<=1)%Z)by(apply(le_bpow radix2);change(bpow radix2 1)with 2;lra).
  assert (Low : (-1030<top x+1)%Z)by(apply(lt_bpow radix2);lra).
  apply Z.abs_le;lia.
Qed.

Definition normal_q_log_tail_factor x := normal_q_logarithm(normal_q_log_tail_input x).

Theorem normal_q_log_tail_factor_error x : finite x -> /2<=B x ->
  valid(normal_q_log_tail_factor x) /\
  Rabs(qval(normal_q_log_tail_factor x)-ln(gaussian_erfcx(B x/sqrt 2)/2))<=bpow radix2 (-114).
Proof.
  intros F X;destruct(normal_q_log_tail_input_error x F X)as[Q [e [E Value]]].
  pose proof(normal_q_log_tail_input_range x F X)as Range.
  pose proof(normal_erfcx_log_range _ (normal_scaled_real_range x F X))as Target.
  pose proof(bpow_gt_0 radix2 (-1030))as Positive.
  destruct(normal_q_logarithm_error _ Q ltac:(lra)(normal_q_tail_log_exponent _ Q Range))as[Result Evaluation].
  pose proof(normal_log_relative_perturbation (gaussian_erfcx(B x/sqrt 2)/2)e (bpow radix2 (-116))
    ltac:(pose proof(bpow_gt_0 radix2 (-1026));lra)
    ltac:(split;[apply bpow_ge_0|interval with(i_prec 80)])E)as Perturbation.
  rewrite <-Value in Perturbation;split;[exact Result|].
  unfold normal_q_log_tail_factor;replace(qval(normal_q_logarithm(normal_q_log_tail_input x))-
    ln(gaussian_erfcx(B x/sqrt 2)/2))with
    ((qval(normal_q_logarithm(normal_q_log_tail_input x))-ln(qval(normal_q_log_tail_input x)))+
     (ln(qval(normal_q_log_tail_input x))-ln(gaussian_erfcx(B x/sqrt 2)/2)))by ring.
  eapply Rle_trans;[apply Rabs_triang|].
  assert(bpow radix2 (-232)+2*bpow radix2 (-116)<=bpow radix2 (-114))by(interval with(i_prec 300));lra.
Qed.
