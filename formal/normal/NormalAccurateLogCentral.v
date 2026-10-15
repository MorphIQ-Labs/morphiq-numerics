(** Compose the central CDF's Q256 error with the complete logarithm. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64.
From Q Require Import Q256 Q256Real.
Require Import StageGappa NormalAccurateCentralCdf NormalLogReduction
  NormalLogSeries NormalLogarithm NormalLogSensitivity NormalAccurateRounding.
Open Scope R_scope.

Lemma normal_q_small_log_exponent x : valid x -> /8<=qval x<=1 -> (Z.abs(top x)<=2048)%Z.
Proof.
  intros X Range;pose proof(normal_q_top_range x X ltac:(lra))as[Lower Upper].
  rewrite Rabs_pos_eq in Lower,Upper by lra.
  assert (High : (top x<=0)%Z).
  { apply(le_bpow radix2);change(bpow radix2 0)with 1;lra. }
  assert (Low : (-3<top x+1)%Z).
  { apply(lt_bpow radix2);change(bpow radix2 (-3))with(/8);lra. }
  apply Z.abs_le;lia.
Qed.

Definition normal_q_log_cdf_central x := normal_q_logarithm(normal_q_central_cdf x).

Theorem normal_q_log_cdf_central_error x : finite x -> Rabs(B x)<=/2 ->
  valid(normal_q_log_cdf_central x) /\ exists e,Rabs e<=bpow radix2 (-229) /\
  qval(normal_q_log_cdf_central x)=ln(normal_cdf(B x))*(1+e).
Proof.
  intros F X;destruct(normal_q_central_cdf_error x F X)as[C [ec [EC Cvalue]]].
  pose proof(normal_central_cdf_range(B x)X)as CdfRange.
  assert (Epsilon : 0<=bpow radix2 (-246)<=/8)by(split;[apply bpow_ge_0|interval with(i_prec 80)]).
  assert (Input : /8<=qval(normal_q_central_cdf x)<=1).
  { rewrite Cvalue;apply Rabs_le_inv in EC;split;nra. }
  pose proof(normal_q_small_log_exponent _ C Input)as Exponent.
  destruct(normal_q_logarithm_error _ C ltac:(lra)Exponent)as[Result Evaluation].
  pose proof(normal_log_relative_perturbation (normal_cdf(B x))ec (bpow radix2 (-246))
    ltac:(lra)ltac:(split;lra)EC)as Perturbation;rewrite <-Cvalue in Perturbation.
  assert (LogRange : -2<=ln(normal_cdf(B x))<= -/4)by(split;interval with(i_prec 80)).
  assert (Absolute : Rabs(qval(normal_q_log_cdf_central x)-ln(normal_cdf(B x)))<=bpow radix2 (-231)).
  { unfold normal_q_log_cdf_central.
    replace(qval(normal_q_logarithm(normal_q_central_cdf x))-ln(normal_cdf(B x)))with
      ((qval(normal_q_logarithm(normal_q_central_cdf x))-ln(qval(normal_q_central_cdf x)))+
       (ln(qval(normal_q_central_cdf x))-ln(normal_cdf(B x))))by ring.
    eapply Rle_trans;[apply Rabs_triang|].
    assert(bpow radix2 (-232)+2*bpow radix2 (-246)<=bpow radix2 (-231))by(interval with(i_prec 300));lra. }
  split;[exact Result|];exists((qval(normal_q_log_cdf_central x)-ln(normal_cdf(B x)))/ln(normal_cdf(B x)));split.
  - unfold Rdiv;rewrite Rabs_mult,Rabs_Rinv,(Rabs_left1(ln(normal_cdf(B x))))by lra.
    apply(Rmult_le_reg_r(-ln(normal_cdf(B x))));[lra|].
    rewrite Rmult_assoc,Rinv_l,Rmult_1_r by lra.
    replace(bpow radix2 (-231))with((/4)*bpow radix2 (-229))in Absolute by(bpow_num;field).
    pose proof(bpow_gt_0 radix2 (-229));nra.
  - field;lra.
Qed.

Theorem normal_q_log_cdf_central_rounded x : finite x -> Rabs(B x)<=/2 ->
  finite(Q256.to_f64(normal_q_log_cdf_central x)) /\ exists d a,
  Rabs d<=bpow radix2 (-53)+bpow radix2 (-228) /\ Rabs a<=bpow radix2 (-1075) /\
  B(Q256.to_f64(normal_q_log_cdf_central x))=ln(normal_cdf(B x))*(1+d)+a.
Proof.
  intros F X;destruct(normal_q_log_cdf_central_error x F X)as[Result Error].
  pose proof Error as[e [E Value]].
  pose proof(normal_central_cdf_range(B x)X)as Range.
  assert (LogRange : -2<=ln(normal_cdf(B x))<= -/4)by(split;interval with(i_prec 80)).
  assert (Qrange : Rabs(qval(normal_q_log_cdf_central x))<=4).
  { rewrite Value;apply Rabs_le_inv in E;assert(bpow radix2 (-229)<=/4)by(interval with(i_prec 80));apply Rabs_le;split;nra. }
  assert (Rounded : Rabs(rndF(qval(normal_q_log_cdf_central x)))<=4).
  { apply abs_round_le_generic;[exact _|exact _| |exact Qrange].
    change 4 with(bpow radix2 2);apply generic_format_bpow;unfold FLT_exp,emin,prec;lia. }
  replace(bpow radix2 (-228))with(2*bpow radix2 (-229))by(bpow_num;field).
  apply normal_q_finite_rounded;try assumption.
  - eapply Rle_lt_trans;[exact Rounded|change 4 with(bpow radix2 2);apply bpow_lt;lia].
  - split;[apply bpow_ge_0|interval with(i_prec 80)].
Qed.
