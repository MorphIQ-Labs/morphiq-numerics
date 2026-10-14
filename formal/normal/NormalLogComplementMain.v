(** The non-tiny binary64 log(1-q) composition, including its low-word
    correction and exact final TwoSum. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Eft RoundingConstant.
Require Import StageGappa Ln1pStageB Ln1pTest Ln1pReduction
  NormalLogComplementStage NormalLogComplementCorrection.
Open Scope R_scope.

Definition normal_log_complement_main64 h l :=
  let '(a,b,_):=stage_b_parts(fneg h)in
  two_sum64 a (fsub b (normal_log_correction64 h l)).

Theorem normal_log_complement_main_ieee h l : finite h -> finite l ->
  bpow radix2 (-54)<=B h<=/3 -> Rabs(B l)<=B h*bpow radix2 (-51) ->
  let '(a,b):=normal_log_complement_main64 h l in
  finite a /\ finite b /\ B a=rndF(B a+B b) /\
  Rabs((B a+B b)-ln(1-B h-B l))<=B h*bpow radix2 (-66).
Proof.
  intros Fh Fl H L.
  assert(Fneg : finite(fneg h))by(unfold fneg,b64_opp;rewrite is_finite_Bopp;exact Fh).
  assert(Neg : B(fneg h)= -B h)by(apply B2R_Bopp).
  pose proof(normal_log_complement_stage_ieee (fneg h)Fneg ltac:(rewrite Neg;split;lra))as Stage.
  pose proof(normal_log_correction_ieee h l Fh Fl H L)as[Fq [Q Qerror]].
  pose proof(normal_log_complement_linear(B h)(B l)H L)as Taylor.
  unfold normal_log_complement_main64;destruct(stage_b_parts(fneg h))as[[u v]e].
  destruct Stage as[Fu [Fv [U [V Error]]]].
  rewrite Neg,Rabs_Ropp,(Rabs_pos_eq(B h))in U,V,Error by(bpow_num_all;lra).
  replace(1+ -B h)with(1-B h)in Error by ring.
  set(q:=normal_log_correction64 h l)in *.
  assert(Sum : Rabs(B v-B q)<=B h*bpow radix2 (-14)).
  { pose proof(Rabs_triang(B v)(-B q));rewrite Rabs_Ropp in *;unfold Rminus;bpow_num_all;nra. }
  destruct(fsub_s v q Fv Fq ltac:(eapply Rle_trans;[exact Sum|bpow_num_all;nra]))as[Fd D].
  pose proof(rnd_sum_err(B v)(-B q)(B_fmt v)(generic_format_opp _ _ _ (B_fmt q)))as Rounded.
  change(Rabs(rndF(B v-B q)-(B v-B q))<=bpow radix2 (-53)*Rabs(B v-B q))in Rounded.
  rewrite <-D in Rounded.
  assert(SubError : Rabs(B(fsub v q)-(B v-B q))<=B h*bpow radix2 (-67)).
  { bpow_num_all;nra. }
  assert(SubRange : Rabs(B(fsub v q))<=1).
  { pose proof(Rabs_triang_inv(B(fsub v q))(B v-B q));bpow_num_all;nra. }
  pose proof(two_sum_ieee u (fsub v q)Fu Fd
    ltac:(eapply Rle_trans;[exact U|bpow_num_all;nra])
    ltac:(eapply Rle_trans;[exact SubRange|interval with(i_prec 80)]))as Words.
  destruct(two_sum64 u (fsub v q))as[a b].
  destruct Words as[Fa [Fb [Norm Value]]].
  repeat split;try assumption.
  - rewrite Value;exact Norm.
  - rewrite Value;replace(B u+B(fsub v q)-ln(1-B h-B l))with
      (((B u+B v)-ln(1-B h))+(B(fsub v q)-(B v-B q))-
       (B q-B l/(1-B h))-(ln(1-B h-B l)-(ln(1-B h)-B l/(1-B h))))by ring.
    eapply Rle_trans;[apply Rabs_triang|].
    eapply Rle_trans;[apply Rplus_le_compat;[apply Rabs_triang|apply Rle_refl]|].
    eapply Rle_trans;[apply Rplus_le_compat;[apply Rplus_le_compat;[apply Rabs_triang|apply Rle_refl]|apply Rle_refl]|].
    rewrite !Rabs_Ropp;bpow_num_all;lra.
Qed.
