(** The table constructor used by the fast path: exact IEEE 754 TwoSum,
    finite normalized double-words, and the certified analytic table errors. *)
From Coq Require Import Reals ZArith Lia Lra.
From Flocq Require Import Core.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Eft.
Require Import TrigTables.
Open Scope R_scope.

Definition trig_table_dw_component_ok (v:R) (p:f64*f64) :=
  let '(h,l):=p in
  finite h /\ finite l /\ B h=rndF(B h+B l) /\
  Rabs(B h+B l-v)<=trig_table_error*Rabs v.

Lemma trig_table_sum_ok v h l : trig_table_component_ok v h l ->
  trig_table_dw_component_ok v (two_sum64 h l).
Proof.
  intros [Fh [Fl [H [L Error]]]].
  assert (Wide:1<=bpow radix2 1020) by (change 1 with (bpow radix2 0); apply bpow_le; lia).
  pose proof (two_sum_ieee h l Fh Fl ltac:(lra) ltac:(lra)) as Sum.
  unfold trig_table_dw_component_ok. destruct (two_sum64 h l) as [sh sl].
  destruct Sum as [Fsh [Fsl [Rounded Value]]].
  repeat split; try assumption.
  - rewrite Value; exact Rounded.
  - rewrite Value; exact Error.
Qed.

Definition trig_table_dw i :=
  let '((sh,sl),(ch,cl)):=trig_table_entry i in
  (two_sum64 sh sl,two_sum64 ch cl).

Theorem trig_table_dw_ok i : (i<51)%nat ->
  trig_table_dw_component_ok (sin(IZR(Z.of_nat i)/64)) (fst(trig_table_dw i)) /\
  trig_table_dw_component_ok (cos(IZR(Z.of_nat i)/64)) (snd(trig_table_dw i)).
Proof.
  intro I. pose proof (trig_table_ok i I) as Row.
  unfold trig_table_dw,trig_table_row_ok in *.
  destruct (trig_table_entry i) as [[sh sl][ch cl]]. cbn [fst snd].
  destruct Row as [S C]. split; apply trig_table_sum_ok; assumption.
Qed.
