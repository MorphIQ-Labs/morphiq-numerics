(** The complete extended-precision logarithm, including normalization,
    series evaluation, early termination and reconstruction with ln(2). *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Binary64 Require Import IEEE64.
From Q Require Import Q256 Q256Real.
Require Import StageGappa ErfcxAccurateInputs NormalConstants
  NormalLogReduction NormalLogSeries NormalLogLoop.
Open Scope R_scope.

Lemma normal_log_exponent_product_error k c m : Rabs k<=2048 ->
  Rabs c<=bpow radix2 (-255) -> Rabs m<=bpow radix2 (-255) ->
  Rabs(k*(ln 2)*(1+c)*(1+m)-k*(ln 2))<=bpow radix2 (-242).
Proof.
  intros K C M;apply Rabs_le_inv in K,C,M.
  replace(k*(ln 2)*(1+c)*(1+m)-k*(ln 2))with(k*(ln 2)*(c+m+c*m))by ring.
  bpow_num_all;apply Rabs_le;split;interval with(i_prec 400).
Qed.

Theorem normal_q_log_exponent_error k : (Z.abs k<=2048)%Z ->
  valid(mul(q_float(LnAccurate.fe k))normal_q_ln2) /\
  Rabs(qval(mul(q_float(LnAccurate.fe k))normal_q_ln2)-IZR k*(ln 2))<=bpow radix2 (-242).
Proof.
  intros K;destruct(LnAccurate.fe_ok k ltac:(lia))as[F Value].
  destruct(q_float_ok _ F)as[Q Qvalue];rewrite Value in Qvalue.
  destruct normal_q_ln2_error as[C Cerror].
  set(c:=qval normal_q_ln2/(ln 2)-1)in *.
  assert (Cvalue : qval normal_q_ln2=ln 2*(1+c)).
  { unfold c;field;interval with(i_prec 80). }
  destruct(mul_relative _ _ Q C)as[Result [m [M Mvalue]]].
  split;[exact Result|];rewrite Mvalue,Qvalue,Cvalue.
  replace(IZR k*(ln 2*(1+c))*(1+m)-IZR k*ln 2)with
    (IZR k*(ln 2)*(1+c)*(1+m)-IZR k*ln 2)by ring.
  apply normal_log_exponent_product_error;try assumption.
  rewrite <-abs_IZR;change 2048 with(IZR 2048);apply IZR_le;exact K.
Qed.

Theorem normal_q_logarithm_error x : valid x -> 0<qval x -> (Z.abs(top x)<=2048)%Z ->
  valid(normal_q_logarithm x) /\
  Rabs(qval(normal_q_logarithm x)-ln(qval x))<=bpow radix2 (-232).
Proof.
  intros X Positive Exponent.
  destruct(normal_q_log_normalized_range x X Positive)as[Y [Range _]].
  destruct(normal_q_log_series_error _ Y Range)as[S Serror].
  destruct(mul_pow2_any _ 1 S)as[Double DoubleValue];change(bpow radix2 1)with 2 in DoubleValue.
  destruct(normal_q_log_exponent_error (top x)Exponent)as[E Eerror].
  destruct(add_any _ _ Double E)as[Result AddError].
  assert (SeriesRange : Rabs(qval(mul_pow2(normal_q_log_series(normal_q_log_normalized x))1))<=2).
  { rewrite DoubleValue;assert (LogRange : 0<=ln(qval(normal_q_log_normalized x))<=1)by(split;interval with(i_prec 80)).
    apply Rabs_le_inv in Serror;assert(bpow radix2 (-234)<=1)by(interval with(i_prec 80));apply Rabs_le;split;nra. }
  assert (ExponentRange : Rabs(qval(mul(q_float(LnAccurate.fe(top x)))normal_q_ln2))<=4096).
  { assert (K : Rabs(IZR(top x))<=2048).
    { rewrite <-abs_IZR;change 2048 with(IZR 2048);apply IZR_le;exact Exponent. }
    apply Rabs_le_inv in K,Eerror;assert (L : 0<=ln 2<=1)by(split;interval with(i_prec 80)).
    assert(bpow radix2 (-242)<=1)by(interval with(i_prec 80));apply Rabs_le;split;nra. }
  assert (Addition : Rabs(qval(normal_q_logarithm x)-
    (qval(mul_pow2(normal_q_log_series(normal_q_log_normalized x))1)+
     qval(mul(q_float(LnAccurate.fe(top x)))normal_q_ln2)))<=bpow radix2 (-242)).
  { eapply Rle_trans;[exact AddError|].
    replace(bpow radix2 (-242))with(bpow radix2 (-254)*4096)by(bpow_num;field).
    apply Rmult_le_compat_l;[apply bpow_ge_0|apply Rmax_lub;lra]. }
  split;[exact Result|].
  pose proof(normal_q_log_reduction_identity x X Positive)as Identity.
  rewrite DoubleValue in Addition.
  apply Rabs_le_inv in Serror,Eerror,Addition.
  assert (Budget : bpow radix2 (-234)+2*bpow radix2 (-242)<=bpow radix2 (-232))by(interval with(i_prec 300)).
  apply Rabs_le;split;lra.
Qed.
