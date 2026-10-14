(** Adjacent binary64 endpoint checks extend to full saturation ranges by
    the input grid and monotonicity. Log-CDF needs the stronger margin to
    account for the difference between q and -ln(1-q). *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64 Grid Encodings.
Require Import StageGappa NormalTailAnalytic NormalTailRange NormalTailThresholdCheck
  NormalTailThresholdConstants NormalComplementAnalytic.
Open Scope R_scope.

Lemma normal_threshold_previous_input x cutoff exponent : finite x ->
  0<=B x<cutoff -> on_grid exponent cutoff ->
  bpow radix2 (exponent+52)<=cutoff-bpow radix2 exponent ->
  B x<=cutoff-bpow radix2 exponent.
Proof.
  intros F X Grid Lower;destruct(Rle_dec(bpow radix2 (exponent+52))(B x))as[Large|Small].
  - assert (Gx : on_grid exponent (B x)).
    { replace exponent with((exponent+52)-52)%Z by ring.
      apply(grid_fmt_bound (FLT_exp emin prec)(exponent+52)).
      - intros;unfold FLT_exp,emin,prec;lia.
      - apply B_fmt.
      - right;rewrite Rabs_pos_eq;lra. }
    pose proof(grid_nonzero exponent(cutoff-B x)(grid_minus _ _ _ Grid Gx)ltac:(lra))as Gap.
    rewrite Rabs_pos_eq in Gap by lra;lra.
  - lra.
Qed.

Theorem normal_tail_saturation_range x cutoff previous exponent threshold :
  finite x -> 0<B x -> 0<cutoff -> previous=cutoff-bpow radix2 exponent ->
  on_grid exponent cutoff -> bpow radix2 (exponent+52)<=previous ->
  normal_tail cutoff<threshold -> threshold<normal_tail previous ->
  (cutoff<=B x -> normal_tail(B x)<threshold) /\
  (B x<cutoff -> threshold<normal_tail(B x)).
Proof.
  intros F X Cutoff Prev Grid Lower High Low;split;intros Range.
  - eapply Rle_lt_trans;[apply(normal_tail_decreasing cutoff(B x));split;assumption|exact High].
  - assert (Bound : B x<=previous).
    { rewrite Prev;apply(normal_threshold_previous_input x cutoff exponent F);try assumption;lra. }
    eapply Rlt_le_trans;[exact Low|apply(normal_tail_decreasing (B x)previous);split;assumption].
Qed.

Theorem normal_tail_zero_midpoint x : finite x -> 0<B x ->
  (B normal_tail_zero<=B x -> normal_tail(B x)<bpow radix2 (-1075)) /\
  (B x<B normal_tail_zero -> bpow radix2 (-1075)<normal_tail(B x)).
Proof.
  intros F X;destruct normal_tail_zero_ok as[_ Value];destruct normal_tail_zero_previous_ok as[_ Prev].
  destruct normal_tail_zero_tail_bracket as[High Low].
  apply(normal_tail_saturation_range x (B normal_tail_zero)(B normal_tail_zero_previous)(-47));try assumption.
  - rewrite Value;interval with(i_prec 80).
  - rewrite Value,Prev;bpow_num;field.
  - rewrite Value;exact(val_grid 5416339707476952 47 47 ltac:(lia)).
  - rewrite Prev;bpow_num;interval with(i_prec 80).
Qed.

Theorem normal_cdf_one_midpoint x : finite x -> 0<B x ->
  (B normal_cdf_one<=B x -> normal_tail(B x)<bpow radix2 (-54)) /\
  (B x<B normal_cdf_one -> bpow radix2 (-54)<normal_tail(B x)).
Proof.
  intros F X;destruct normal_cdf_one_ok as[_ Value];destruct normal_cdf_one_previous_ok as[_ Prev].
  destruct normal_cdf_one_tail_bracket as[High Low].
  apply(normal_tail_saturation_range x (B normal_cdf_one)(B normal_cdf_one_previous)(-49));try assumption.
  - rewrite Value;interval with(i_prec 80).
  - rewrite Value,Prev;bpow_num;field.
  - rewrite Value;exact(val_grid 4668184281381965 49 49 ltac:(lia)).
  - rewrite Prev;bpow_num;interval with(i_prec 80).
Qed.

Theorem normal_centered_half_midpoint x : finite x -> 0<B x ->
  (B normal_centered_half<=B x -> normal_tail(B x)<bpow radix2 (-55)) /\
  (B x<B normal_centered_half -> bpow radix2 (-55)<normal_tail(B x)).
Proof.
  intros F X;destruct normal_centered_half_ok as[_ Value];destruct normal_centered_half_previous_ok as[_ Prev].
  destruct normal_centered_half_tail_bracket as[High Low].
  apply(normal_tail_saturation_range x (B normal_centered_half)(B normal_centered_half_previous)(-49));try assumption.
  - rewrite Value;interval with(i_prec 80).
  - rewrite Value,Prev;bpow_num;field.
  - rewrite Value;exact(val_grid 4714361854172776 49 49 ltac:(lia)).
  - rewrite Prev;bpow_num;interval with(i_prec 80).
Qed.

Lemma normal_complement_quadratic_bound q : 0<q<=/2 ->
  0< -ln(1-q)<=q+2*q*q.
Proof.
  intros Q;pose proof(normal_complement_target_range q Q)as Positive.
  pose proof(normal_complement_remainder 1 q ltac:(split;lra))as Error.
  replace(normal_complement_series 1 q)with q in Error by(cbn;field).
  assert (Remainder : q^(1+1)/(1-q)<=2*q*q).
  { apply(Rmult_le_reg_r(1-q));[lra|].
    replace(q^(1+1)/(1-q)*(1-q))with(q*q)by(cbn;field;lra);nra. }
  apply Rabs_le_inv in Error;split;lra.
Qed.

Theorem normal_log_positive_zero_midpoint x : finite x -> 0<B x ->
  (B normal_tail_zero<=B x -> 0< -ln(1-normal_tail(B x))<bpow radix2 (-1075)) /\
  (B x<B normal_tail_zero -> bpow radix2 (-1075)< -ln(1-normal_tail(B x))).
Proof.
  intros F X;pose proof(normal_tail_range(B x)ltac:(lra))as Range.
  pose proof(normal_complement_quadratic_bound _ Range)as Log.
  destruct normal_tail_zero_ok as[FC Value].
  pose proof(normal_tail_threshold_margin normal_tail_zero 1075 true FC
    ltac:(rewrite Value;split;interval with(i_prec 80)) normal_tail_zero_checked)as Margin.
  split;intros H.
  - assert (Tail : normal_tail(B x)<bpow radix2 (-1075)*(1-bpow radix2 (-62))).
    { eapply Rle_lt_trans;[apply normal_tail_decreasing|exact Margin];rewrite Value in *;split;[interval with(i_prec 80)|exact H]. }
    assert (Budget : bpow radix2 (-1075)*(1-bpow radix2 (-62))+
      2*bpow radix2 (-1075)*bpow radix2 (-1075)<bpow radix2 (-1075)).
    { bpow_num;interval with(i_prec 1200). }
    assert (Small : normal_tail(B x)<bpow radix2 (-1075)).
    { pose proof(bpow_gt_0 radix2 (-1075));pose proof(bpow_gt_0 radix2 (-62));nra. }
    assert (Square : normal_tail(B x)*normal_tail(B x)<=bpow radix2 (-1075)*bpow radix2 (-1075))by nra.
    split;lra.
  - pose proof(proj2(normal_tail_zero_midpoint x F X)H)as Tail.
    pose proof(normal_complement_target_range _ Range);lra.
Qed.
