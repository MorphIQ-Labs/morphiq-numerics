(** Exact binary64 input cutoff for negative log-CDF overflow. The log-tail
    factor cannot bridge the gap between adjacent half-square values. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64 Grid.
From Q Require Import Q256 Q256Real.
Require Import StageGappa ErfcxGaussianTarget NormalTailAnalytic NormalLogAnalytic
  NormalLogTailRange NormalAccurateLogNegative NormalLogOverflowConstants.
Open Scope R_scope.

Lemma normal_log_tail_square_bounds x : finite x -> /2<=B x ->
  B x*B x/2-1028 <= -ln(normal_tail(B x)) <= B x*B x/2+1028.
Proof.
  intros F X;pose proof(normal_erfcx_log_range _ (normal_scaled_real_range x F X))as Factor.
  assert (Log : -1028<=ln(gaussian_erfcx(B x/sqrt 2)/2)<=1028).
  { bpow_num_all;split;interval with(i_prec 80). }
  pose proof(normal_log_tail_identity(B x)ltac:(lra));lra.
Qed.



Lemma normal_log_overflow_previous_input x : finite x -> 0<=B x<B normal_log_overflow ->
  B x<=B normal_log_overflow-bpow radix2 460.
Proof.
  intros F X;destruct normal_log_overflow_ok as [_ Value].
  destruct(Rle_dec (bpow radix2 512)(B x))as[Large|Small].
  - assert (Gx : on_grid 460 (B x)).
    { change 460%Z with (512-52)%Z.
      apply(grid_fmt_bound (FLT_exp emin prec)512).
      - intros;unfold FLT_exp,emin,prec;lia.
      - apply B_fmt.
      - right;rewrite Rabs_pos_eq;lra. }
    assert (Gc : on_grid 460 (B normal_log_overflow)).
    { rewrite Value;exists 6369051672525773%Z;reflexivity. }
    pose proof(grid_nonzero 460 (B normal_log_overflow-B x)
      (grid_minus _ _ _ Gc Gx)ltac:(lra))as Gap.
    rewrite Rabs_pos_eq in Gap by lra;lra.
  - rewrite Value;bpow_num_all;lra.
Qed.

Theorem normal_log_overflow_midpoint x : finite x -> /2<=B x ->
  (B normal_log_overflow<=B x -> bpow radix2 1024-bpow radix2 970 < -ln(normal_tail(B x))) /\
  (B x<B normal_log_overflow -> -ln(normal_tail(B x)) < bpow radix2 1024-bpow radix2 970).
Proof.
  intros F X;pose proof(normal_log_tail_square_bounds x F X)as Bounds.
  destruct normal_log_overflow_bracket as[High Low].
  destruct normal_log_overflow_ok as[_ Value].
  assert (Cutoff : 0<=B normal_log_overflow)by(rewrite Value;apply Rmult_le_pos;[lra|apply bpow_ge_0]).
  split;intros H.
  - assert (Squares : B normal_log_overflow*B normal_log_overflow<=B x*B x)by nra;lra.
  - pose proof(normal_log_overflow_previous_input x F ltac:(split;lra))as Previous.
    set(p:=B normal_log_overflow-bpow radix2 460)in *.
    assert (Squares : B x*B x<=p*p)by nra.
    assert (Budget : p*p/2+1028<9007199254740991*bpow radix2 971).
    { pose proof(bpow_gt_0 radix2 (-112));nra. }
    assert (Last : 9007199254740991*bpow radix2 971 < bpow radix2 1024-bpow radix2 970)by(bpow_num;lra).
    lra.
Qed.

Theorem normal_q_log_cdf_negative_finite x : finite x -> /2<=B x<B normal_log_overflow ->
  Rabs(rndF(qval(normal_q_log_cdf_negative x)))<bpow radix2 1024.
Proof.
  intros F [X Cutoff];destruct(normal_q_log_cdf_negative_error x F X)as[_ [e [E Value]]].
  pose proof(normal_log_tail_bounds x F X)as[Positive _].
  pose proof(normal_log_tail_square_bounds x F X)as Bounds.
  pose proof(normal_log_overflow_previous_input x F ltac:(split;lra))as Previous.
  pose proof(proj2 normal_log_overflow_bracket)as Bracket.
  set(p:=B normal_log_overflow-bpow radix2 460)in *.
  assert (L : Rabs(ln(normal_tail(B x)))<=p*p/2+1028).
  { rewrite Rabs_left1 by lra;nra. }
  assert (Factor : Rabs(1+e)<=1+bpow radix2 (-112)).
  { apply Rabs_le_inv in E;apply Rabs_le;split;lra. }
  assert (Magnitude : bnd 9007199254740991 971 (qval(normal_q_log_cdf_negative x))).
  { unfold bnd;rewrite Value,Rabs_mult.
    eapply Rle_trans;[apply Rmult_le_compat;[apply Rabs_pos|apply Rabs_pos|exact L|exact Factor]|].
    exact(Rlt_le _ _ Bracket). }
  pose proof(bnd_round 9007199254740991 971 _ ltac:(lia)ltac:(lia)Magnitude)as Rounded.
  eapply Rle_lt_trans;[exact Rounded|apply bnd_lt;lia].
Qed.

Corollary normal_q_log_cdf_negative_finite_rounded x : finite x ->
  /2<=B x<B normal_log_overflow ->
  finite(Q256.to_f64(normal_q_log_cdf_negative x)) /\ exists d a,
  Rabs d<=bpow radix2 (-53)+bpow radix2 (-111) /\ Rabs a<=bpow radix2 (-1075) /\
  B(Q256.to_f64(normal_q_log_cdf_negative x))=ln(normal_tail(B x))*(1+d)+a.
Proof.
  intros F X;apply normal_q_log_cdf_negative_rounded;[exact F|exact(proj1 X)|].
  exact(normal_q_log_cdf_negative_finite x F X).
Qed.
