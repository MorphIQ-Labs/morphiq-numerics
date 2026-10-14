(** Division and Taylor remainder in the low-word correction to log(1-q). *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64 RoundingConstant RoundingCore.
Require Import StageGappa ErfcxDecision Ln1pReduction Ln1pApprox.
Open Scope R_scope.

Lemma normal_log_correction_round h v : bpow radix2 (-54)<=h<=/3 ->
  Rabs v<=h*bpow radix2 (-50) ->
  Rabs(rndF v-v)<=h*bpow radix2 (-102).
Proof.
  intros H V;destruct(Rle_lt_dec(bpow radix2 (-200))(Rabs v))as[Large|Small].
  - pose proof(rnd_rel v ltac:(eapply Rle_trans with(bpow radix2 (-200));[apply bpow_le;lia|exact Large]))as Error.
    change(Rabs(rndF v-v)<=bpow radix2 (-53)*Rabs v)in Error.
    bpow_num_all;nra.
  - pose proof(rnd_err_below v (-200)ltac:(lia)ltac:(lra))as Error.
    change(-200-54)%Z with(-254)%Z in Error;bpow_num_all;nra.
Qed.

Definition normal_log_correction64 h l := fdiv l (fsub(erfcx_pow2 0)h).

Theorem normal_log_correction_ieee h l : finite h -> finite l ->
  bpow radix2 (-54)<=B h<=/3 -> Rabs(B l)<=B h*bpow radix2 (-51) ->
  finite(normal_log_correction64 h l) /\
  Rabs(B(normal_log_correction64 h l))<=B h*bpow radix2 (-49) /\
  Rabs(B(normal_log_correction64 h l)-B l/(1-B h))<=B h*bpow radix2 (-100).
Proof.
  intros Fh Fl H L;destruct(erfcx_pow2_ok 0 ltac:(lia))as[Fo One];change(bpow radix2 0)with 1 in One.
  destruct(fsub_s (erfcx_pow2 0)h Fo Fh)as[Fd D].
  { rewrite One;apply Rabs_le;bpow_num_all;split;lra. }
  rewrite One in D.
  pose proof(rnd_err_below (1-B h)0 ltac:(lia)
    ltac:(change(bpow radix2 0)with 1;rewrite Rabs_pos_eq;bpow_num_all;lra))as DenError.
  rewrite <-D in DenError;change(0-54)%Z with(-54)%Z in DenError.
  assert(Den : /2<=B(fsub(erfcx_pow2 0)h)<=1).
  { split.
    - apply Rabs_le_inv in DenError;bpow_num_all;lra.
    - rewrite D;change 1 with(bpow radix2 0);apply round_le_generic;try exact _.
      + apply generic_format_bpow;unfold FLT_exp,emin,prec;lia.
      + change(bpow radix2 0)with 1;bpow_num_all;lra. }
  set(d:=B(fsub(erfcx_pow2 0)h))in *.
  assert(Inv : 0<=/d<=2)by(split;interval with(i_prec 80)).
  assert(Q : Rabs(B l/d)<=B h*bpow radix2 (-50)).
  { unfold Rdiv;rewrite Rabs_mult,Rabs_Rinv,(Rabs_pos_eq d)by lra.
    pose proof(Rabs_pos(B l));bpow_num_all;nra. }
  destruct(fdiv_bnd 1 0 l (fsub(erfcx_pow2 0)h)Fl ltac:(fold d;lra)
    ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia))as[Fq [Qvalue Qbound]].
  { unfold bnd;rewrite Rmult_1_l;change(bpow radix2 0)with 1;fold d;bpow_num_all;lra. }
  fold(normal_log_correction64 h l)in Fq,Qvalue,Qbound;fold d in Qvalue.
  pose proof(normal_log_correction_round(B h)(B l/d)H Q)as Rounded.
  rewrite <-Qvalue in Rounded.
  assert(Division : Rabs(B l/d-B l/(1-B h))<=B h*bpow radix2 (-103)).
  { replace(B l/d-B l/(1-B h))with(B l*((1-B h)-d)*(/d* /(1-B h)))by(unfold d;field;fold d;split;bpow_num_all;lra).
    rewrite !Rabs_mult,Rabs_Rinv,Rabs_Rinv,(Rabs_pos_eq d),(Rabs_pos_eq(1-B h))by(bpow_num_all;lra).
    rewrite Rabs_minus_sym.
    assert(OtherInv : 0<=/(1-B h)<=2)by(split;interval with(i_prec 80)).
    pose proof(Rabs_pos(B l));pose proof(Rabs_pos(d-(1-B h))).
    assert(A : Rabs(B l)*Rabs(d-(1-B h))<=B h*bpow radix2 (-51)*bpow radix2 (-54)).
    { apply Rmult_le_compat;try apply Rabs_pos;assumption. }
    assert(Bound : 0<=/d* /(1-B h)<=4)by nra.
    bpow_num_all;nra. }
  split;[exact Fq|];split.
  - pose proof(Rabs_triang_inv(B(normal_log_correction64 h l))(B l/d));bpow_num_all. nra.
  - replace(B(normal_log_correction64 h l)-B l/(1-B h))with
      ((B(normal_log_correction64 h l)-B l/d)+(B l/d-B l/(1-B h)))by ring.
    eapply Rle_trans;[apply Rabs_triang|];bpow_num_all;lra.
Qed.

Theorem normal_log_complement_linear h l : bpow radix2 (-54)<=h<=/3 ->
  Rabs l<=h*bpow radix2 (-51) ->
  Rabs(ln(1-h-l)-(ln(1-h)-l/(1-h)))<=h*bpow radix2 (-100).
Proof.
  intros H L;set(q:= -l/(1-h)).
  assert(Q : Rabs q<=h*bpow radix2 (-50)).
  { unfold q,Rdiv;rewrite Rabs_mult,Rabs_Ropp,Rabs_Rinv,(Rabs_pos_eq(1-h))by(bpow_num_all;lra).
    assert(Inv : 0<=/(1-h)<=2)by(split;interval with(i_prec 80)).
    pose proof(Rabs_pos l);bpow_num_all;nra. }
  assert(Small : Rabs q<=/2)by(bpow_num_all;lra).
  pose proof(ln1p_linear q Small)as Error.
  assert(Identity : ln(1-h-l)=ln(1-h)+ln(1+q)).
  { replace(1-h-l)with((1-h)*(1+q))by(unfold q;field;bpow_num_all;lra).
    rewrite ln_mult;[reflexivity|bpow_num_all;lra|apply Rabs_le_inv in Small;lra]. }
  rewrite Identity;replace(ln(1-h)+ln(1+q)-(ln(1-h)-l/(1-h)))with(ln(1+q)-q)by(unfold q;unfold Rdiv;ring).
  eapply Rle_trans;[exact Error|].
  apply(Rmult_le_reg_r(1-Rabs q));[lra|].
  unfold Rdiv;rewrite Rmult_assoc,Rinv_l,Rmult_1_r by lra.
  apply Rabs_le_inv in Q;bpow_num_all;nra.
Qed.
