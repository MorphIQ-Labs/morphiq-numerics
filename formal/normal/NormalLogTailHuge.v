(** The scaled exact square in the huge negative log-CDF tail. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core Mult_error IEEE754.Binary.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64 RoundingTest.
Require Import StageGappa ErfcxDecision NormalLogTailSquare NormalLogOverflow
  NormalLogOverflowConstants NormalTailAnalytic NormalLogTailScale.
Open Scope R_scope.

Definition normal_log_tail_down64 x := fmul x (erfcx_pow2 (-480)).
Definition normal_log_tail_huge64 x := normal_log_tail_square64(normal_log_tail_down64 x).

Lemma normal_log_tail_down_exact x : finite x -> bpow radix2 45<=B x<=bpow radix2 513 ->
  finite(normal_log_tail_down64 x) /\
  B(normal_log_tail_down64 x)=B x*bpow radix2 (-480) /\
  bpow radix2 (-435)<=B(normal_log_tail_down64 x)<=bpow radix2 33.
Proof.
  intros Fx X;destruct(erfcx_pow2_ok (-480)ltac:(lia))as[Fc C].
  assert(Xp : 0<B x)by(pose proof(bpow_gt_0 radix2 45);lra).
  assert(M : (46<=mag radix2(B x))%Z).
  { apply mag_ge_bpow;change(46-1)%Z with 45%Z;rewrite Rabs_pos_eq;lra. }
  assert(Range : bpow radix2 (-435)<=B x*bpow radix2 (-480)<=bpow radix2 33).
  { replace(bpow radix2 (-435))with(bpow radix2 45*bpow radix2 (-480))by(rewrite <-bpow_plus;reflexivity).
    replace(bpow radix2 33)with(bpow radix2 513*bpow radix2 (-480))by(rewrite <-bpow_plus;reflexivity).
    split;apply Rmult_le_compat_r;try apply bpow_ge_0;lra. }
  destruct(fmul_exact x (erfcx_pow2 (-480)) Fx Fc)as[Fv V].
  - rewrite C;apply mult_bpow_exact_FLT;[apply B_fmt|unfold emin,prec;lia].
  - rewrite C,Rabs_pos_eq by(pose proof(bpow_gt_0 radix2 (-435));lra).
    eapply Rle_lt_trans;[exact(proj2 Range)|apply bpow_lt;lia].
  - unfold normal_log_tail_down64;rewrite C in V;repeat split;try assumption;rewrite V;tauto.
Qed.

Definition normal_log_tail_huge_decide64 x :=
  let '(h,l):=normal_log_tail_huge64 x in
  match erfcx_decide64 h l with
  | Some v => Some(normal_log_tail_up64 v)
  | None => None
  end.

Theorem normal_log_tail_huge_words x : finite x ->
  bpow radix2 45<=B x<B normal_log_overflow ->
  let '(h,l):=normal_log_tail_huge64 x in
  finite h /\ finite l /\ B h=rndF(B h+B l) /\
  bpow radix2 (-900)<=Rabs(B h)<=bpow radix2 1000 /\
  Rabs(ln(normal_tail(B x))*bpow radix2 (-960)-(B h+B l))<=
    bpow radix2 (-67)*Rabs(ln(normal_tail(B x))*bpow radix2 (-960)).
Proof.
  intros Fx X.
  assert(Xp : 0<B x)by(pose proof(bpow_gt_0 radix2 45);lra).
  assert(Upper : B x<=bpow radix2 513).
  { destruct normal_log_overflow_ok as[_ Cutoff];rewrite Cutoff in X.
    bpow_num_all;lra. }
  destruct(normal_log_tail_down_exact x Fx ltac:(split;lra))as[Fr [R Range]].
  pose proof(normal_log_tail_square_exact (normal_log_tail_down64 x) Fr
    ltac:(split;[exact(proj1 Range)|eapply Rle_trans;[exact(proj2 Range)|apply bpow_le;lia]]))as Square.
  unfold normal_log_tail_huge64;destruct(normal_log_tail_square64(normal_log_tail_down64 x))as[h l].
  destruct Square as[Fh [Fl [Norm [Value H]]]].
  assert(Scale : bpow radix2 (-480)*bpow radix2 (-480)=bpow radix2 (-960))by(rewrite <-bpow_plus;reflexivity).
  assert(ValueScaled : B h+B l=(-B x*B x/2)*bpow radix2 (-960)).
  { rewrite Value,R;replace(-(B x*bpow radix2 (-480))*(B x*bpow radix2 (-480))/2)with
      ((-B x*B x/2)*(bpow radix2 (-480)*bpow radix2 (-480)))by(unfold Rdiv;ring).
    rewrite Scale;reflexivity. }
  pose proof(normal_log_tail_square_bounds x Fx ltac:(bpow_num_all;lra))as Tail.
  assert(Lower : bpow radix2 89-1028<= -ln(normal_tail(B x))).
  { replace(bpow radix2 89)with(bpow radix2 45*bpow radix2 45/2)by(bpow_num;field).
    pose proof(bpow_gt_0 radix2 45);nra. }
  assert(Error : Rabs(ln(normal_tail(B x))+B x*B x/2)<=1028).
  { apply Rabs_le;split;lra. }
  repeat split;try assumption.
  - eapply Rle_trans;[apply(bpow_le radix2 (-900) (-871));lia|exact(proj1 H)].
  - eapply Rle_trans;[exact(proj2 H)|apply bpow_le;lia].
  - rewrite ValueScaled.
    replace(ln(normal_tail(B x))*bpow radix2 (-960)-(-B x*B x/2)*bpow radix2 (-960))with
      ((ln(normal_tail(B x))+B x*B x/2)*bpow radix2 (-960))by(unfold Rdiv;ring).
    rewrite !Rabs_mult,(Rabs_pos_eq(bpow radix2 (-960)))by apply bpow_ge_0.
    rewrite <-Rmult_assoc;apply Rmult_le_compat_r;[apply bpow_ge_0|].
    rewrite(Rabs_left1(ln(normal_tail(B x))))by(bpow_num_all;lra);bpow_num_all;lra.
Qed.

Theorem normal_log_tail_huge_decided x v : finite x ->
  bpow radix2 45<=B x<B normal_log_overflow ->
  normal_log_tail_huge_decide64 x=Some v ->
  finite v /\ B v=rndF(ln(normal_tail(B x))).
Proof.
  intros Fx X;pose proof(normal_log_tail_huge_words x Fx X)as Words.
  unfold normal_log_tail_huge_decide64;destruct(normal_log_tail_huge64 x)as[h l].
  destruct Words as[Fh [Fl [Norm [H Error]]]].
  set(z:=ln(normal_tail(B x))*bpow radix2 (-960))in *.
  destruct(erfcx_decide64 h l)as[r|]eqn:Decision;[|discriminate].
  intros Output;injection Output as <-.
  destruct(erfcx_decide_ieee h l z r Fh Fl H Norm Error Decision)as[Eq Round];subst r.
  assert(Identity : z*bpow radix2 960=ln(normal_tail(B x))).
  { unfold z;rewrite Rmult_assoc,<-bpow_plus;change(bpow radix2 (-960+960))with 1;ring. }
  assert(Z : bpow radix2 (-900)<=Rabs z).
  { pose proof(normal_log_tail_square_bounds x Fx ltac:(bpow_num_all;lra))as Tail.
    assert(Lower : bpow radix2 88<= -ln(normal_tail(B x))).
    { assert(Square : bpow radix2 45*bpow radix2 45<=B x*B x).
      { pose proof(bpow_gt_0 radix2 45);nra. }
      bpow_num_all;lra. }
    unfold z;rewrite Rabs_mult,(Rabs_pos_eq(bpow radix2 (-960)))by apply bpow_ge_0.
    rewrite Rabs_left1 by(bpow_num_all;lra).
    eapply Rle_trans;[apply(bpow_le radix2 (-900) (-872));lia|].
    replace(bpow radix2 (-872))with(bpow radix2 88*bpow radix2 (-960))by(rewrite <-bpow_plus;reflexivity).
    apply Rmult_le_compat_r;[apply bpow_ge_0|exact Lower]. }
  destruct(normal_log_tail_up_exact h z Fh (proj1 H) Z Round
    ltac:(rewrite Identity;apply normal_log_tail_rounded_finite;[exact Fx|bpow_num_all;split;lra]))as[Fv V].
  split;[exact Fv|rewrite Identity in V;exact V].
Qed.
