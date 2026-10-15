(** Accurate negative-input log-CDF retains the original square in Q256,
    avoiding both an overflowing binary64 square and an underflowed tail. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64.
From Q Require Import Q256 Q256Real.
Require Import StageGappa ErfcxAccurateInputs ErfcxGaussianTarget NormalTailAnalytic
  NormalTailRange NormalLogAnalytic NormalLogTailRange NormalAccurateRounding.
Open Scope R_scope.

Definition normal_q_negative_half_square x := neg_q(mul_pow2(mul(q_float x)(q_float x))(-1)).
Definition normal_q_log_cdf_negative x := add(normal_q_negative_half_square x)(normal_q_log_tail_factor x).

Theorem normal_q_negative_half_square_error x : finite x ->
  valid(normal_q_negative_half_square x) /\ exists e,Rabs e<=bpow radix2 (-255) /\
  qval(normal_q_negative_half_square x)=(-B x*B x/2)*(1+e).
Proof.
  intros F;destruct(q_float_ok x F)as[X Xvalue].
  destruct(mul_relative _ _ X X)as[Square [e [E Value]]].
  destruct(mul_pow2_any _ (-1) Square)as[Half Hvalue];destruct(neg_any _ Half)as[Result Nvalue].
  split;[exact Result|];exists e;split;[exact E|].
  unfold normal_q_negative_half_square;rewrite Nvalue,Hvalue,Value,Xvalue.
  change(bpow radix2 (-1))with(/2);field.
Qed.

Lemma normal_log_tail_bounds x : finite x -> /2<=B x ->
  /2<= -ln(normal_tail(B x)) /\ B x*B x/2<=2*(-ln(normal_tail(B x))) /\
  Rabs(ln(gaussian_erfcx(B x/sqrt 2)/2))<=3*(-ln(normal_tail(B x))).
Proof.
  intros F X;pose proof(normal_tail_outer_range(B x)X)as Tail.
  pose proof(normal_erfcx_log_range _ (normal_scaled_real_range x F X))as Factor.
  assert (LogTail : ln(normal_tail(B x))<=ln(3/8)).
  { destruct(Rle_lt_or_eq_dec _ _ (proj2 Tail))as[Lt|Eq];[left;apply ln_increasing;lra|rewrite Eq;lra]. }
  assert (Half : /2<= -ln(normal_tail(B x))).
  { assert(ln(3/8)<= -/2)by(interval with(i_prec 80));lra. }
  assert (Upper : ln(gaussian_erfcx(B x/sqrt 2)/2)<=/2).
  { bpow_num_all;interval with(i_prec 80). }
  pose proof(normal_log_tail_identity(B x)ltac:(lra))as Identity.
  split;[exact Half|];split;[nra|apply Rabs_le;split;nra].
Qed.

Theorem normal_q_log_cdf_negative_error x : finite x -> /2<=B x ->
  valid(normal_q_log_cdf_negative x) /\ exists e,Rabs e<=bpow radix2 (-112) /\
  qval(normal_q_log_cdf_negative x)=ln(normal_tail(B x))*(1+e).
Proof.
  intros F X;destruct(normal_q_negative_half_square_error x F)as[Square [es [ES Svalue]]].
  destruct(normal_q_log_tail_factor_error x F X)as[Log LogError].
  pose proof(normal_log_tail_bounds x F X)as[Lower [SquareBound LogBound]].
  pose proof(normal_log_tail_identity(B x)ltac:(lra))as Identity.
  set(l:= -ln(normal_tail(B x)))in *;set(s:=B x*B x/2)in *.
  assert (Spositive : 0<=s)by(unfold s;nra).
  assert (SquareValue : qval(normal_q_negative_half_square x)= -s*(1+es)).
  { rewrite Svalue;unfold s;field. }
  assert (SquareRange : Rabs(qval(normal_q_negative_half_square x))<=4*l).
  { rewrite SquareValue,Rabs_mult,Rabs_Ropp,(Rabs_pos_eq s)by lra.
    assert (Factor : Rabs(1+es)<=2).
    { apply Rabs_le_inv in ES;assert(bpow radix2 (-255)<=1)by(interval with(i_prec 80));apply Rabs_le;split;lra. } nra. }
  assert (SquareError : Rabs(qval(normal_q_negative_half_square x)+s)<=2*l*bpow radix2 (-255)).
  { rewrite SquareValue;replace(-s*(1+es)+s)with(-s*es)by ring.
    rewrite Rabs_mult,Rabs_Ropp,(Rabs_pos_eq s)by lra.
    apply Rmult_le_compat;[lra|apply Rabs_pos|exact SquareBound|exact ES]. }
  assert (LogRange : Rabs(qval(normal_q_log_tail_factor x))<=4*l).
  { replace(qval(normal_q_log_tail_factor x))with
      ((qval(normal_q_log_tail_factor x)-ln(gaussian_erfcx(B x/sqrt 2)/2))+
        ln(gaussian_erfcx(B x/sqrt 2)/2))by ring.
    eapply Rle_trans;[apply Rabs_triang|].
    assert(bpow radix2 (-114)<=/2)by(interval with(i_prec 80));lra. }
  destruct(add_any _ _ Square Log)as[Result Addition].
  assert (AddError : Rabs(qval(normal_q_log_cdf_negative x)-
    (qval(normal_q_negative_half_square x)+qval(normal_q_log_tail_factor x)))<=4*l*bpow radix2 (-254)).
  { eapply Rle_trans;[exact Addition|];rewrite(Rmult_comm(4*l)(bpow radix2 (-254))).
    apply Rmult_le_compat_l;[apply bpow_ge_0|apply Rmax_lub;assumption]. }
  assert (Absolute : Rabs(qval(normal_q_log_cdf_negative x)-ln(normal_tail(B x)))<=l*bpow radix2 (-112)).
  { replace(qval(normal_q_log_cdf_negative x)-ln(normal_tail(B x)))with
      ((qval(normal_q_log_cdf_negative x)-
        (qval(normal_q_negative_half_square x)+qval(normal_q_log_tail_factor x)))+
       (qval(normal_q_negative_half_square x)+s)+
       (qval(normal_q_log_tail_factor x)-ln(gaussian_erfcx(B x/sqrt 2)/2)))by(unfold s;lra).
    eapply Rle_trans;[apply Rabs_triang|].
    eapply Rle_trans;[apply Rplus_le_compat_r,Rabs_triang|].
    assert (Budget : 4*bpow radix2 (-254)+2*bpow radix2 (-255)+2*bpow radix2 (-114)<=bpow radix2 (-112))by(interval with(i_prec 300)).
    assert (LogScaled : Rabs(qval(normal_q_log_tail_factor x)-ln(gaussian_erfcx(B x/sqrt 2)/2))<=2*l*bpow radix2 (-114)).
    { eapply Rle_trans;[exact LogError|pose proof(bpow_ge_0 radix2 (-114));nra]. }
    assert (Combined : 4*l*bpow radix2 (-254)+2*l*bpow radix2 (-255)+2*l*bpow radix2 (-114)<=l*bpow radix2 (-112)).
    { replace(4*l*bpow radix2 (-254)+2*l*bpow radix2 (-255)+2*l*bpow radix2 (-114))with
        (l*(4*bpow radix2 (-254)+2*bpow radix2 (-255)+2*bpow radix2 (-114)))by ring.
      apply Rmult_le_compat_l;lra. } lra. }
  split;[exact Result|];exists((qval(normal_q_log_cdf_negative x)-ln(normal_tail(B x)))/ln(normal_tail(B x)));split.
  - unfold Rdiv;rewrite Rabs_mult,Rabs_Rinv,(Rabs_left1(ln(normal_tail(B x))))by(unfold l in *;lra).
    fold l;apply(Rmult_le_reg_r l);[lra|];rewrite Rmult_assoc,Rinv_l,Rmult_1_r by lra;nra.
  - unfold l in *;field;lra.
Qed.

Theorem normal_q_log_cdf_negative_rounded x : finite x -> /2<=B x ->
  Rabs(rndF(qval(normal_q_log_cdf_negative x)))<bpow radix2 1024 ->
  finite(Q256.to_f64(normal_q_log_cdf_negative x)) /\ exists d a,
  Rabs d<=bpow radix2 (-53)+bpow radix2 (-111) /\ Rabs a<=bpow radix2 (-1075) /\
  B(Q256.to_f64(normal_q_log_cdf_negative x))=ln(normal_tail(B x))*(1+d)+a.
Proof.
  intros F X Finite;destruct(normal_q_log_cdf_negative_error x F X)as[Result Error].
  replace(bpow radix2 (-111))with(2*bpow radix2 (-112))by(bpow_num;field).
  apply normal_q_finite_rounded;try assumption;split;[apply bpow_ge_0|interval with(i_prec 80)].
Qed.
