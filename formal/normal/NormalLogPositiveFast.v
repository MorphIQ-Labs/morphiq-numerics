(** Positive-tail log-CDF: the fast tail, log-complement composition,
    computed guard and bitwise acceptance test. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Binary64 Require Import Binary64Add IEEE64 RoundingConstant.
Require Import StageGappa Ln1pLemmas NormalTailAnalytic NormalTailFast NormalOuterFastRange
  NormalLogTailWords NormalLogComplementFast NormalLogSensitivity
  NormalComplementAnalytic NormalLogDecision NormalScaledLogDecision.
Open Scope R_scope.

Definition normal_log_positive_fast64 x :=
  let '(h,l,k):=normal_tail_fast64 x in
  let '(a,b):=normal_log_complement64 h l in(a,b,k).

Local Opaque normal_tail_fast64 normal_log_complement64.

Theorem normal_log_positive_fast_ieee x : finite x -> /2<=B x<=37 ->
  let '(a,b,k):=normal_log_positive_fast64 x in
  finite a /\ finite b /\ (-991<=k<= -1)%Z /\ B a=rndF(B a+B b) /\
  Rabs(B a)<=16*bpow radix2 k /\ Rabs(B b)<=bpow radix2(k-50) /\
  bpow radix2 k/4096<=Rabs(ln(1-normal_tail(B x)))<=12*bpow radix2 k /\
  Rabs((B a+B b)-ln(1-normal_tail(B x)))<=7*bpow radix2(-65)*Rabs(ln(1-normal_tail(B x))).
Proof.
  intros Fx X;pose proof(normal_tail_fast_ieee x Fx X)as Tail.
  pose proof(normal_log_tail_words x Fx X)as Words.
  pose proof(normal_outer_tail_tight(B x)ltac:(lra))as Tight.
  pose proof(normal_complement_target_range(normal_tail(B x))ltac:(split;lra))as TargetLog.
  unfold normal_log_positive_fast64;destruct(normal_tail_fast64 x)as[[h l]k].
  destruct Tail as[Fh [Fl [K [Norm [H [L [Target Error]]]]]]].
  destruct Words as[High [Low HighTail]].
  set(q:=normal_tail(B x))in *;set(t:=ln(1-q))in *.
  assert(Abs : Rabs t= -t)by(apply Rabs_left1;lra).
  set(e:=((B h+B l)-q)/q).
  assert(E : Rabs e<=3*bpow radix2(-67)).
  { unfold e,Rdiv;rewrite Rabs_mult,Rabs_Rinv,(Rabs_pos_eq q)by lra.
    apply(Rmult_le_reg_r q);[lra|];rewrite Rmult_assoc,Rinv_l,Rmult_1_r by lra;exact Error. }
  pose proof(normal_log_complement_perturbation q e (3*bpow radix2(-67))
    ltac:(split;lra)ltac:(bpow_num_all;split;lra)E)as Perturbation.
  replace(q*(1+e))with(B h+B l)in Perturbation by(unfold e;field;lra).
  replace(1-(B h+B l))with(1-B h-B l)in Perturbation by ring.
  fold t in Perturbation.
  pose proof(normal_log_complement_ieee h l Fh Fl High Low)as Log.
  destruct(normal_log_complement64 h l)as[a b].
  destruct Log as[Fa [Fb [Normalized LogError]]].
  assert(Composition : Rabs((B a+B b)-t)<=7*bpow radix2(-65)*Rabs t).
  { replace((B a+B b)-t)with(((B a+B b)-ln(1-B h-B l))+(ln(1-B h-B l)-t))by ring.
    eapply Rle_trans;[apply Rabs_triang|].
    rewrite Abs;bpow_num_all;nra. }
  set(s:=bpow radix2 k)in *;assert(S : 0<s)by apply bpow_gt_0.
  assert(LogRange : s/4096<=Rabs t<=12*s)by(rewrite Abs;split;lra).
  assert(Sum : Rabs(B a+B b)<=16*s).
  { pose proof(Rabs_triang_inv(B a+B b)t);bpow_num_all;nra. }
  assert(Scale : 16*s=bpow radix2(k+4)).
  { unfold s;rewrite bpow_plus;change(bpow radix2 4)with 16;ring. }
  assert(ResultHigh : Rabs(B a)<=16*s).
  { rewrite Normalized;apply rnd_bound;[|exact Sum].
    rewrite Scale;apply generic_format_bpow;unfold FLT_exp,emin,prec;lia. }
  pose proof(rnd_err_below(B a+B b)(k+4)ltac:(lia)ltac:(rewrite <-Scale;exact Sum))as Rounded.
  rewrite <-Normalized in Rounded;replace(k+4-54)%Z with(k-50)%Z in Rounded by ring.
  replace(B a-(B a+B b))with(-B b)in Rounded by ring;rewrite Rabs_Ropp in Rounded.
  repeat split;tauto.
Qed.

Definition normal_log_positive_decide64 x :=
  let '(h,l,_):=normal_log_positive_fast64 x in normal_log_decide64 h l.

Local Opaque normal_log_positive_fast64 normal_log_decide64.

Theorem normal_log_positive_decided x v : finite x -> /2<=B x<=37 ->
  normal_log_positive_decide64 x=Some v ->
  finite v /\ B v=rndF(ln(1-normal_tail(B x))).
Proof.
  intros Fx X Decision;pose proof(normal_log_positive_fast_ieee x Fx X)as Log.
  unfold normal_log_positive_decide64 in Decision.
  destruct(normal_log_positive_fast64 x)as[[h l]k].
  destruct Log as[Fh [Fl [K [Norm [H [L [Target Error]]]]]]].
  apply(normal_scaled_log_decide_ok h l k (ln(1-normal_tail(B x)))v);try assumption;lia.
Qed.
