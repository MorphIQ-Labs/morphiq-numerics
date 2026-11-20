(** Executable double-word radix logarithms. The input logarithm evaluators
    are shared with ln; the reciprocal scaling and exponent addition follow
    src/log2/mod.rs. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Mul IEEE64Eft
  RoundingTest.
From Interval Require Import Tactic.
Require Import LnReduction LnAccurate LnFastY LnFastValue LnFastTables
  LogRadixConstants.
Open Scope R_scope.

Definition inv_ln2_dw := two_sum64 inv_ln2_hi inv_ln2_lo.
Definition inv_ln10_dw := two_sum64 inv_ln10_hi inv_ln10_lo.

Definition log2_fast_value x :=
  let '(e, i, y, r) := reduce x in
  let '(h, l) := lf_ln_y y i in
  let '(ch, cl) := inv_ln2_dw in
  let '(wh, wl) := mul64 h l ch cl in
  if (e =? 0)%Z then (wh, wl) else add64 (fe e) ExpFast.c_zero wh wl.

Definition log10_fast_value x :=
  let '(h, l) := lf_ln_fast_value x in
  let '(ch, cl) := inv_ln10_dw in mul64 h l ch cl.

Definition log2_fast x := let '(h, l) := log2_fast_value x in decide_with h l lf_eps.
Definition log10_fast x := let '(h, l) := log10_fast_value x in decide_with h l lf_eps.

Lemma inv_ln2_dw_ok :
  let '(h, l) := inv_ln2_dw in
  finite h /\ finite l /\ B h = rndF (B h + B l) /\
  B h + B l = B inv_ln2_hi + B inv_ln2_lo.
Proof.
  pose proof (two_sum_ieee inv_ln2_hi inv_ln2_lo
    inv_ln2_hi_finite inv_ln2_lo_finite
    ltac:(rewrite inv_ln2_hi_val; interval)
    ltac:(rewrite inv_ln2_lo_val; interval)) as S.
  unfold inv_ln2_dw. destruct (two_sum64 inv_ln2_hi inv_ln2_lo) as [h l].
  destruct S as [Fh [Fl [H V]]]. repeat split; try assumption.
  rewrite V; exact H.
Qed.

Lemma inv_ln10_dw_ok :
  let '(h, l) := inv_ln10_dw in
  finite h /\ finite l /\ B h = rndF (B h + B l) /\
  B h + B l = B inv_ln10_hi + B inv_ln10_lo.
Proof.
  pose proof (two_sum_ieee inv_ln10_hi inv_ln10_lo
    inv_ln10_hi_finite inv_ln10_lo_finite
    ltac:(rewrite inv_ln10_hi_val; interval)
    ltac:(rewrite inv_ln10_lo_val; interval)) as S.
  unfold inv_ln10_dw. destruct (two_sum64 inv_ln10_hi inv_ln10_lo) as [h l].
  destruct S as [Fh [Fl [H V]]]. repeat split; try assumption.
  rewrite V; exact H.
Qed.
