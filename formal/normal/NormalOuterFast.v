(** Fast positive CDF and centered-CDF complements of the normal tail.
    The tighter outer-tail bound controls subtraction's relative error. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add RoundingConstant.
Require Import StageGappa NormalTailFast NormalTailAnalytic NormalOuterFastRange
  NormalTailDecision NormalRelativeDecision.
Open Scope R_scope.

Definition normal_outer_fast64 c x :=
  let '(h,l,k):=normal_tail_fast64 x in add_f64_64 (fneg h)(fneg l)c.

Theorem normal_outer_fast_ieee c x : finite c -> /2<=B c<=1 -> finite x -> /2<=B x<=37 ->
  let '(h,l):=normal_outer_fast64 c x in
  finite h /\ finite l /\ B h=rndF(B h+B l) /\ /8<=B h<=2 /\
  Rabs(B l)<=bpow radix2 (-53) /\
  Rabs((B h+B l)-(B c-normal_tail(B x)))<=3*bpow radix2 (-66)*(B c-normal_tail(B x)).
Proof.
  intros Fc C Fx X;pose proof(normal_tail_fast_ieee x Fx X)as Tail.
  unfold normal_outer_fast64;destruct(normal_tail_fast64 x)as[[a b]k].
  destruct Tail as[Fa [Fb [K [Anorm [A [Bl [_ TailError]]]]]]].
  pose proof(normal_outer_tail_tight(B x)(proj1 X))as Target.
  assert(Power : bpow radix2 k<=1)by(change 1 with(bpow radix2 0);apply bpow_le;lia).
  assert(Ahigh : Rabs(B a)<=8)by(rewrite Rabs_pos_eq by lra;nra).
  assert(Blow : Rabs(B b)<=bpow radix2 (-51))by(eapply Rle_trans;[exact Bl|apply bpow_le;lia]).
  assert(Nb : forall w,B(fneg w)= -B w)by(intros;apply B2R_Bopp).
  assert(Nf : forall w,finite w -> finite(fneg w))by(intros w Fw;unfold fneg,b64_opp;rewrite is_finite_Bopp;exact Fw).
  assert(Norm : B(fneg a)=rndF(B(fneg a)+B(fneg b))).
  { rewrite !Nb;apply dw_opp;exact Anorm. }
  assert(SumRange : /8<=B(fneg a)+B(fneg b)+B c<=2).
  { rewrite !Nb;apply Rabs_le_inv in TailError;bpow_num_all;split;nra. }
  assert(Bound : forall w,Rabs(B w)<=16 -> bnd 1 4 (B w)).
  { intros w W;unfold bnd;rewrite Rmult_1_l;change(bpow radix2 4)with 16;exact W. }
  assert(Nah : Rabs(B(fneg a))<=16)by(rewrite Nb,Rabs_Ropp;lra).
  assert(Nbl : Rabs(B(fneg b))<=16)by(rewrite Nb,Rabs_Ropp;eapply Rle_trans;[exact Blow|interval with(i_prec 80)]).
  assert(Cb : Rabs(B c)<=16)by(rewrite Rabs_pos_eq;lra).
  destruct(add_f64_64_ok 1 4 (fneg a)(fneg b)c (Nf a Fa)(Nf b Fb)Fc
    (Bound _ Nah)(Bound _ Nbl)(Bound c Cb)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia))as[Fh [Fl Value]].
  pose proof(add_f64_dw (B(fneg a))(B(fneg b))(B c)(B_fmt _)(B_fmt _)(B_fmt _)Norm)as Normalized.
  pose proof(add_f64_ieee (fneg a)(fneg b)c (Nf a Fa)(Nf b Fb)Fc Norm
    ltac:(eapply Rle_trans;[exact Nah|interval with(i_prec 80)])
    ltac:(eapply Rle_trans;[exact Nbl|interval with(i_prec 80)])
    ltac:(eapply Rle_trans;[exact Cb|interval with(i_prec 80)]))as Relative.
  rewrite <-Value in Normalized;destruct(add_f64_64 (fneg a)(fneg b)c)as[h l];cbn[fst snd]in *.
  destruct Relative as[_ [_ Relative]].
  assert(Evaluation : Rabs((B h+B l)-(B(fneg a)+B(fneg b)+B c))<=bpow radix2 (-104)).
  { replace((B h+B l)-(B(fneg a)+B(fneg b)+B c))with
      ((((B h+B l)-(B(fneg a)+B(fneg b)+B c))/(B(fneg a)+B(fneg b)+B c))*(B(fneg a)+B(fneg b)+B c))by(field;lra).
    rewrite Rabs_mult,(Rabs_pos_eq(B(fneg a)+B(fneg b)+B c))by lra.
    pose proof(Rabs_pos(((B h+B l)-(B(fneg a)+B(fneg b)+B c))/(B(fneg a)+B(fneg b)+B c))).
    unfold prec in Relative;change(- (53))%Z with(-53)%Z in Relative;bpow_num_all;nra. }
  assert(Error : Rabs((B h+B l)-(B c-normal_tail(B x)))<=3*bpow radix2 (-66)*(B c-normal_tail(B x))).
  { replace((B h+B l)-(B c-normal_tail(B x)))with
      (((B h+B l)-(B(fneg a)+B(fneg b)+B c))-((B a+B b)-normal_tail(B x)))by(rewrite !Nb;ring).
    eapply Rle_trans;[apply Rabs_triang|];rewrite Rabs_Ropp;bpow_num_all;nra. }
  assert(Range : /8<=B h+B l<=2).
  { apply Rabs_le_inv in Error;bpow_num_all;split;nra. }
  assert(High : /8<=B h<=2).
  { rewrite Normalized;split.
    - change(/8)with(bpow radix2 (-3));apply round_ge_generic;[exact _|exact _| |exact(proj1 Range)].
      apply generic_format_bpow;unfold FLT_exp,emin,prec;lia.
    - change 2 with(bpow radix2 1);apply round_le_generic;[exact _|exact _| |exact(proj2 Range)].
      apply generic_format_bpow;unfold FLT_exp,emin,prec;lia. }
  pose proof(rnd_err_below(B h+B l)1 ltac:(lia)
    ltac:(change(bpow radix2 1)with 2;rewrite Rabs_pos_eq;lra))as Rounded.
  rewrite <-Normalized in Rounded;change(1-54)%Z with(-53)%Z in Rounded.
  assert(Low : Rabs(B l)<=bpow radix2 (-53)).
  { replace(B h-(B h+B l))with(-B l)in Rounded by ring;rewrite Rabs_Ropp in Rounded;exact Rounded. }
  repeat split;tauto.
Qed.

Definition normal_outer_decide64 c x :=
  let '(h,l):=normal_outer_fast64 c x in normal_relative_decide64 h l.

Local Opaque normal_outer_fast64 normal_relative_decide64.

Theorem normal_outer_fast_decided c x v : finite c -> /2<=B c<=1 -> finite x -> /2<=B x<=37 ->
  normal_outer_decide64 c x=Some v -> finite v /\ B v=rndF(B c-normal_tail(B x)).
Proof.
  intros Fc C Fx X Decision;pose proof(normal_outer_fast_ieee c x Fc C Fx X)as Outer.
  unfold normal_outer_decide64 in Decision;destruct(normal_outer_fast64 c x)as[h l].
  destruct Outer as[Fh [Fl [_ [H [L Error]]]]].
  pose proof(normal_outer_tail_tight(B x)(proj1 X))as Target.
  apply(normal_tail_relative_decide_ok h l 0 (B c-normal_tail(B x))v);try assumption.
  - lia.
  - change(bpow radix2 0)with 1;split;lra.
  - change(0-51)%Z with(-51)%Z;eapply Rle_trans;[exact L|apply bpow_le;lia].
  - change(bpow radix2 0)with 1;split;lra.
Qed.
