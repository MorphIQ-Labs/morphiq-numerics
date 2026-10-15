(** Extend the existing Q256 reciprocal proof to denominators near one,
    needed by the normalized logarithm and both logarithm series. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core Relative IEEE754.Binary.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64 RoundingCore.
From Q Require Import Q256 Q256Real.
Require Import StageGappa ErfcxReciprocal ErfcxAccurateInputs
  ErfcxAccurateNewton ErfcxAccurateSetup NormalTableLookup NormalErfcxReciprocal.
Open Scope R_scope.

Lemma normal_small_reciprocal_seed x : finite x -> 1<=B x ->
  finite(fdiv one x) /\ Rabs(B x*B(fdiv one x)-1)<=bpow radix2 (-51).
Proof.
  intros Fx X;destruct one_ok as[F1 B1].
  assert (Y : 0<1/B x<=1).
  { unfold Rdiv;rewrite Rmult_1_l;split.
    - apply Rinv_0_lt_compat;lra.
    - rewrite <-Rinv_1;apply Rinv_le_contravar;lra. }
  destruct(fdiv_ok 1 0 one x F1 ltac:(lra) ltac:(lia) ltac:(lia)
    ltac:(reflexivity) ltac:(lia)
    ltac:(unfold bnd;rewrite B1,Rmult_1_l;change(bpow radix2 0)with 1;
      apply Rabs_le;lra))as[Fy By].
  rewrite B1 in By;split;[exact Fy|].
  assert (Lower : bpow radix2 (-1024)<=Rabs(1/B x)).
  { rewrite Rabs_pos_eq by lra.
    change(-1024)%Z with(Z.opp 1024);rewrite bpow_opp.
    unfold Rdiv;rewrite Rmult_1_l;apply Rinv_le_contravar;[lra|].
    pose proof(abs_B2R_lt_emax 53 1024 x)as Upper.
    rewrite Rabs_pos_eq in Upper by lra;lra. }
  pose proof(ErfcxAccurateReciprocal.binary64_round_large_reciprocal(1/B x)Lower)as Error.
  rewrite <-By,(Rabs_pos_eq(1/B x))in Error by lra.
  replace(B x*B(fdiv one x)-1)with((B(fdiv one x)-1/B x)*B x)by(field;lra).
  rewrite Rabs_mult,(Rabs_pos_eq(B x))by lra.
  replace(bpow radix2 (-51))with((bpow radix2 (-51)*(1/B x))*B x)by(field;lra).
  apply Rmult_le_compat_r;lra.
Qed.

Theorem normal_q_small_reciprocal_error x : valid x -> 1<=qval x<=16 ->
  valid(q_recip x) /\ exists e,Rabs e<=bpow radix2 (-252) /\
  qval(q_recip x)=(/qval x)*(1+e).
Proof.
  intros X Range.
  destruct(normal_table_input_round x X ltac:(split;lra))as[Fh [_ [Rounded _]]].
  assert (Normal : bpow radix2 (-1022)<=Rabs(qval x)).
  { rewrite Rabs_pos_eq by lra;eapply Rle_trans;[|exact(proj1 Range)].
    change 1 with(bpow radix2 0);apply bpow_le;lia. }
  destruct(relative_error_N_FLT_ex radix2 emin prec ltac:(unfold prec;lia) ne (qval x) Normal)
    as[d [D Dvalue]].
  replace(/2*bpow radix2 (-prec+1))with(bpow radix2 (-53))in D
    by(unfold prec;change(/2)with(bpow radix2 (-1));rewrite <-bpow_plus;reflexivity).
  assert (Hvalue : B(Q256.to_f64 x)=qval x*(1+d))by(rewrite Rounded;exact Dvalue).
  assert (High : 1<=B(Q256.to_f64 x)).
  { rewrite Rounded;change 1 with(bpow radix2 0).
    apply round_ge_generic;[exact _|exact _| |exact(proj1 Range)].
    apply generic_format_bpow;unfold FLT_exp,emin,prec;lia. }
  destruct(normal_small_reciprocal_seed _ Fh High)as[Fy Seed].
  destruct(q_float_ok _ Fy)as[Y Yvalue].
  set(e:=B(Q256.to_f64 x)*B(fdiv one (Q256.to_f64 x))-1)in *.
  assert (Den : 1+d<>0)by(apply Rabs_le_inv in D;bpow_num_all;lra).
  assert (SeedBound : Rabs(qval x*qval(q_float(fdiv one (Q256.to_f64 x)))-1)<=bpow radix2 (-50)).
  { rewrite Yvalue;replace(qval x*B(fdiv one (Q256.to_f64 x))-1)with((e-d)/(1+d)).
    - apply normal_reciprocal_seed_perturbation;assumption.
    - unfold e;rewrite Hvalue;field;exact Den. }
  destruct(q_refine3_error _ _ X Y SeedBound)as[Result Error].
  unfold q_recip;split;[exact Result|].
  exists(qval x*qval(q_refine3 x (q_float(fdiv one (Q256.to_f64 x))))-1).
  split;[exact Error|field;lra].
Qed.

Theorem normal_q_log_reciprocal_error x : valid x -> 1<=qval x<=3*bpow radix2 1022 ->
  valid(q_recip x) /\ exists e,Rabs e<=bpow radix2 (-252) /\
  qval(q_recip x)=(/qval x)*(1+e).
Proof.
  intros X Range;destruct(Rle_dec 16(qval x))as[Large|Small].
  - apply normal_q_reciprocal_error;[exact X|split;lra].
  - apply normal_q_small_reciprocal_error;[exact X|split;lra].
Qed.
