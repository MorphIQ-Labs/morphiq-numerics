(** The reciprocal logarithm stage, used directly on the moderate normal
    tail argument. It avoids the more expensive double-word logarithm. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Bits.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Eft.
Require Import StageGappa Ln1pReduction Ln1pLemmas Ln1pTest LnStageEvaluation NormalCenterFastTail.
Open Scope R_scope.

Definition normal_log_reciprocal_parts64 x := ln_parts (rd_e(bits_of_b64 x)) x.

Theorem normal_log_reciprocal_parts_ieee x : finite x -> 37<=B x<=bpow radix2 45 ->
  let '(h,l,e):=normal_log_reciprocal_parts64 x in
  finite h /\ finite l /\ Rabs(B h)<=34 /\ Rabs(B l)<=1 /\
  Rabs(B h+B l-ln(B x))<=bpow radix2(-65).
Proof.
  intros Fx X;assert(Domain : bpow radix2(-53)<=B x<=bpow radix2 1020).
  { split;[bpow_num_all;lra|apply Rle_trans with(bpow radix2 45);[lra|apply bpow_le;lia]]. }
  pose proof(Ln1pReduction.reduce_ok x Fx Domain)as Reduction;cbv zeta in Reduction.
  destruct Reduction as[E [_ [_ [Y _]]]].
  set(k:=rd_e(bits_of_b64 x))in *;set(y:=B x*bpow radix2(-k))in *.
  assert(Value : B x=bpow radix2 k*y).
  { unfold y;rewrite Rmult_comm,Rmult_assoc,<-bpow_plus;replace(-k+k)%Z with 0%Z by ring;simpl;ring. }
  assert(Ne : k=0%Z -> y<>1).
  { intros K One;rewrite Value,K,One in X;change(37<=1*1<=bpow radix2 45)in X;lra. }
  assert(Log : ln(B x)=IZR k*ln 2+ln y).
  { rewrite Value,ln_mult,ln_bpow;[reflexivity|apply bpow_gt_0|lra]. }
  pose proof(ln_eval_bounded k x Fx Domain ltac:(lia)Ne)as Evaluation.
  cbv zeta in Evaluation;fold k y in Evaluation;rewrite <-Log in Evaluation.
  unfold normal_log_reciprocal_parts64;fold k;destruct(ln_parts k x)as[[h l]e].
  destruct Evaluation as[Fh [Fl [Fe [[E0 Ehigh] [High [Low Main]]]]]].
  specialize(Main(ln(B x))ltac:(rewrite Rminus_diag_eq,Rabs_R0 by reflexivity;apply Rmult_le_pos;[left;apply Rinv_0_lt_compat,pow_lt;lra|apply Rabs_pos])).
  assert(Error : Rabs(B h+B l-ln(B x))<=bpow radix2(-65)).
  { rewrite Rabs_minus_sym;pose proof(Rabs_pos(B l));pose proof(bpow_gt_0 radix2(-53));nra. }
  assert(LogRange : 3<=ln(B x)<=32)by(split;interval with(i_prec 100)).
  assert(H : Rabs(B h)<=34).
  { assert(Lbound : Rabs(B l)<=1)by lra;apply Rabs_le_inv in Error,Lbound;
    apply Rabs_le;bpow_num_all;split;lra. }
  repeat split;try assumption;pose proof(Rabs_pos(B l));lra.
Qed.

Definition normal_log_reciprocal64 x :=
  let '(h,l,_):=normal_log_reciprocal_parts64 x in two_sum64 h l.

Theorem normal_log_reciprocal_ieee x : finite x -> 37<=B x<=bpow radix2 45 ->
  let '(h,l):=normal_log_reciprocal64 x in finite h /\ finite l /\ B h=rndF(B h+B l) /\
  Rabs(B h)<=1024 /\ Rabs(B l)<=2048 /\ Rabs(B h+B l-ln(B x))<=/2^64*Rabs(ln(B x)).
Proof.
  intros Fx X;pose proof(normal_log_reciprocal_parts_ieee x Fx X)as Parts.
  unfold normal_log_reciprocal64;destruct(normal_log_reciprocal_parts64 x)as[[a b]e].
  destruct Parts as[Fa [Fb [A [Bv Error]]]].
  pose proof(two_sum_ieee a b Fa Fb
    ltac:(apply Rle_trans with 34;[exact A|interval with(i_prec 80)])
    ltac:(apply Rle_trans with 1;[exact Bv|interval with(i_prec 80)]))as Sum.
  destruct(two_sum64 a b)as[h l];destruct Sum as[Fh [Fl [High Total]]].
  assert(Norm : B h=rndF(B h+B l))by(rewrite Total;exact High).
  assert(Log : 3<=ln(B x)<=32)by(split;interval with(i_prec 100)).
  assert(Range : 2<=B h+B l<=33)by(rewrite Total;apply Rabs_le_inv in Error;bpow_num_all;split;lra).
  assert(H : Rabs(B h)<=64).
  { rewrite Norm;change 64 with(bpow radix2 6);apply normal_center_round_bound;
      [change(bpow radix2 6)with 64;apply Rabs_le;lra|lia]. }
  assert(L : Rabs(B l)<=128)by(apply Rabs_le_inv in H;apply Rabs_le;lra).
  repeat split;try assumption;try lra.
  rewrite Total;apply Rle_trans with(bpow radix2(-65));[exact Error|].
  rewrite Rabs_pos_eq by lra;bpow_num_all;nra.
Qed.
