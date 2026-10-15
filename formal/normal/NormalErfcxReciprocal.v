(** The existing three-step Q256 reciprocal also accepts an extended input:
    account for rounding that input before the hardware reciprocal seed. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core Relative.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add RoundingCore.
From Q Require Import Q256 Q256Real.
Require Import StageGappa ErfcxReciprocal ErfcxAccurateReciprocal
  ErfcxAccurateInputs ErfcxAccurateNewton ErfcxAccurateSetup.
Require ExpReduction.
Open Scope R_scope.

Lemma normal_extended_input_round x : valid x -> 16<=qval x<=3*bpow radix2 1022 ->
  finite(Q256.to_f64 x) /\ 16<=B(Q256.to_f64 x) /\ exists d,
  Rabs d<=bpow radix2 (-53) /\ B(Q256.to_f64 x)=qval x*(1+d).
Proof.
  intros X Range.
  assert (Normal : bpow radix2 (-1022)<=Rabs(qval x)).
  { rewrite Rabs_pos_eq by lra. eapply Rle_trans;[|exact(proj1 Range)].
    change 16 with(bpow radix2 4);apply bpow_le;lia. }
  assert (Low : 16<=rndF(qval x)).
  { change 16 with(bpow radix2 4). apply round_ge_generic;[exact _|exact _| |exact(proj1 Range)].
    apply generic_format_bpow;unfold FLT_exp,emin,prec;lia. }
  assert (High : Rabs(rndF(qval x))<=3*bpow radix2 1022).
  { apply abs_round_le_generic;[exact _|exact _| |].
    - change 3 with(IZR 3);apply ExpReduction.fmt_int;lia.
    - rewrite Rabs_pos_eq;lra. }
  assert (Finite : Rabs(rndF(qval x))<bpow radix2 1024).
  { eapply Rle_lt_trans;[exact High|].
    replace(bpow radix2 1024)with(4*bpow radix2 1022).
    - pose proof(bpow_gt_0 radix2 1022);lra.
    - change 4 with(bpow radix2 2);rewrite <-bpow_plus;reflexivity. }
  destruct(q_to_float_round _ X Finite) as [F Value].
  destruct(relative_error_N_FLT_ex radix2 emin prec ltac:(unfold prec;lia) ne (qval x) Normal)
    as [d [D Dvalue]].
  replace(/2*bpow radix2 (-prec+1))with(bpow radix2 (-53))in D
    by(unfold prec;change(/2)with(bpow radix2 (-1));rewrite <-bpow_plus;reflexivity).
  split;[exact F|]. rewrite Value. split;[exact Low|]. exists d;split;assumption.
Qed.

Lemma normal_reciprocal_seed_perturbation d e :
  Rabs d<=bpow radix2 (-53) -> Rabs e<=bpow radix2 (-51) ->
  Rabs((e-d)/(1+d))<=bpow radix2 (-50).
Proof.
  intros D E;apply Rabs_le_inv in D,E;bpow_num_all.
  apply Rabs_le;split;interval with(i_prec 100).
Qed.

Theorem normal_q_reciprocal_error x : valid x -> 16<=qval x<=3*bpow radix2 1022 ->
  valid(q_recip x) /\ exists e,Rabs e<=bpow radix2 (-252) /\
  qval(q_recip x)=(/qval x)*(1+e).
Proof.
  intros X Range.
  destruct(normal_extended_input_round x X Range) as [Fh [H [d [D Hvalue]]]].
  destruct(accurate_reciprocal_seed_ieee _ Fh H) as [Fy Seed].
  destruct(q_float_ok _ Fy) as [Y Yvalue].
  set(e:=B(Q256.to_f64 x)*B(fdiv one (Q256.to_f64 x))-1) in *.
  assert (Den : 1+d<>0) by(apply Rabs_le_inv in D;bpow_num_all;lra).
  assert (SeedBound : Rabs(qval x*qval(q_float(fdiv one (Q256.to_f64 x)))-1)<=bpow radix2 (-50)).
  { rewrite Yvalue.
    replace(qval x*B(fdiv one (Q256.to_f64 x))-1)with((e-d)/(1+d)).
    - apply normal_reciprocal_seed_perturbation;assumption.
    - unfold e;rewrite Hvalue;field;exact Den. }
  destruct(q_refine3_error _ _ X Y SeedBound) as [Result Error].
  unfold q_recip;split;[exact Result|].
  exists(qval x*qval(q_refine3 x (q_float(fdiv one (Q256.to_f64 x))))-1).
  split;[exact Error|field;lra].
Qed.
