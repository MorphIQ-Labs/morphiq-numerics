(** The same staged rounding analysis as [BvnHighPol], for [100 <= hk <= 1400], where the two
    exponential leaves are under [e^-50 < 2e-22] (so are the moments' contribution): the leaf
    bounds for [hk] and the polynomial factors are the larger ones that [hk <= 1400] gives, and
    the closed form's error is under [1e-32], far under the [1.5e-16] of the small-[hk] chain.
    Same calculator, same stages, other constants. *)
From Coq Require Import Reals Lra Psatz ZArith Lia.
From Interval Require Import Tactic.
From Flocq Require Import Core.
Require Import BvnHighAssembly BvnHighRound BvnHighSteps BvnHighErr BvnHighErrTree BvnHighPol.
Open Scope R_scope.

Definition me0b (i : nat) : R :=
  match i with
  | 0 => 1400 | 1 => 36009 / 10 ^ 7 | 2 => 9 / 10 ^ 6 | 3 => 1 | 4 => 4 | 5 => 12
  | 6 => 3 / 1000 | 7 => 2 / 10 ^ 22 | 8 => 2 / 10 ^ 22 | 9 => 2507 / 1000
  | 10 => 1 / 2 | 11 => 601 / 10000 | _ => 0 end.
Definition ee0b (i : nat) : R :=
  match i with
  | 0 => 1400 * u + 1 / 10 ^ 190
  | 1 => 32 / 10 * u * (36009 / 10 ^ 7) + 1 / 10 ^ 190
  | 2 => u * (9 / 10 ^ 6) + eta
  | 3 | 4 | 5 | 6 => 0
  | 7 => 1 / 10 ^ 32
  | 8 => 1 / 10 ^ 32
  | 9 => 2 / 10 ^ 16
  | 10 => 183 / 100 * u
  | 11 => 43 / 10 * u * (601 / 10000) + 3 / 10 ^ 100
  | _ => 0 end.

Definition MEb1 := ext me0b 12 (176).
Definition EEb1 := ext ee0b 12 (527 * u).
Definition MEb2 := ext MEb1 13 (89).
Definition EEb2 := ext EEb1 13 (265 * u).
Definition MEb3 := ext MEb2 14 (1065 / 1000).
Definition EEb3 := ext EEb2 14 (16 / 10 * u).
Definition MEb4 := ext MEb3 15 (226 / 1000).
Definition EEb4 := ext EEb3 15 (27 / 10 * u).
Definition MEb5 := ext MEb4 16 (1230 / 1000).
Definition EEb5 := ext EEb4 16 (52 / 10 * u).
Definition MEb6 := ext MEb5 17 (1230 / 1000).
Definition EEb6 := ext EEb5 17 (37 / 10 * u).

Ltac numb := cbv [ext me0b ee0b c_t d_t w_t X_t P1_t P2_t A1_t A2_t A_t MEb1 MEb2 MEb3 MEb4 MEb5 MEb6 EEb1 EEb2 EEb3 EEb4 EEb5 EEb6]; cbn; rewrite ?u_value; unfold eta; interval with (i_prec 120).

Section ChainB.
Variables xe0 ce0 : nat -> R.
Hypothesis H0 : forall i, ab (xe0 i) (ce0 i) (me0b i) (ee0b i).

Lemma S1b : ab (sem xe0 c_t) (csem ce0 c_t) (176) (527 * u).
Proof.
  apply stage with (me := me0b) (ee := ee0b); [exact H0 | unfold c_t; simpl; repeat split; lra | | ].
  - numb.
  - numb.
Qed.
Lemma H1b : forall i, ab (XE1 xe0 i) (CE1 xe0 ce0 i) (MEb1 i) (EEb1 i).
Proof. exact (henv_ext _ _ _ _ 12 _ _ _ _ H0 S1b). Qed.

Lemma S2b : ab (sem (XE1 xe0) d_t) (csem (CE1 xe0 ce0) d_t) (89) (265 * u).
Proof.
  apply stage with (me := MEb1) (ee := EEb1); [exact H1b | unfold d_t; simpl; repeat split; lra | | ].
  - numb.
  - numb.
Qed.
Lemma H2b : forall i, ab (XE2 xe0 i) (CE2 xe0 ce0 i) (MEb2 i) (EEb2 i).
Proof. exact (henv_ext _ _ _ _ 13 _ _ _ _ H1b S2b). Qed.

Lemma S3b : ab (sem (XE2 xe0) w_t) (csem (CE2 xe0 ce0) w_t) (1065 / 1000) (16 / 10 * u).
Proof.
  apply stage with (me := MEb2) (ee := EEb2); [exact H2b | unfold w_t; simpl; repeat split; lra | | ].
  - numb.
  - numb.
Qed.
Lemma H3b : forall i, ab (XE3 xe0 i) (CE3 xe0 ce0 i) (MEb3 i) (EEb3 i).
Proof. exact (henv_ext _ _ _ _ 14 _ _ _ _ H2b S3b). Qed.

Lemma S4b : ab (sem (XE3 xe0) X_t) (csem (CE3 xe0 ce0) X_t) (226 / 1000) (27 / 10 * u).
Proof.
  apply stage with (me := MEb3) (ee := EEb3); [exact H3b | unfold X_t; simpl; repeat split; lra | | ].
  - numb.
  - numb.
Qed.
Lemma H4b : forall i, ab (XE4 xe0 i) (CE4 xe0 ce0 i) (MEb4 i) (EEb4 i).
Proof. exact (henv_ext _ _ _ _ 15 _ _ _ _ H3b S4b). Qed.

Lemma S5b : ab (sem (XE4 xe0) P1_t) (csem (CE4 xe0 ce0) P1_t) (1230 / 1000) (52 / 10 * u).
Proof.
  apply stage with (me := MEb4) (ee := EEb4); [exact H4b | unfold P1_t; simpl; repeat split; lra | | ].
  - numb.
  - numb.
Qed.
Lemma H5b : forall i, ab (XE5 xe0 i) (CE5 xe0 ce0 i) (MEb5 i) (EEb5 i).
Proof. exact (henv_ext _ _ _ _ 16 _ _ _ _ H4b S5b). Qed.

Lemma S6b : ab (sem (XE5 xe0) P2_t) (csem (CE5 xe0 ce0) P2_t) (1230 / 1000) (37 / 10 * u).
Proof.
  apply stage with (me := MEb5) (ee := EEb5); [exact H5b | unfold P2_t; simpl; repeat split; lra | | ].
  - numb.
  - numb.
Qed.
Lemma H6b : forall i, ab (XE6 xe0 i) (CE6 xe0 ce0 i) (MEb6 i) (EEb6 i).
Proof. exact (henv_ext _ _ _ _ 17 _ _ _ _ H5b S6b). Qed.

Lemma A_final_b : ab (sem (XE6 xe0) A_t) (csem (CE6 xe0 ce0) A_t) (2 / 10 ^ 23) (1 / 10 ^ 32).
Proof.
  apply stage with (me := MEb6) (ee := EEb6); [exact H6b | unfold A_t, A1_t, A2_t; simpl; repeat split; lra | | ].
  - numb.
  - numb.
Qed.
End ChainB.
