(** Rounding of the closed form's two polynomial factors and of its two moment
    terms [A1], [A2] (docs/bivariate_normal_high.md section 4.4), through the
    verified calculator of [BvnHighErrTree], one stage at a time: each stage's
    result becomes a leaf of the next, with the bounds proved for it. *)
From Coq Require Import Reals Lra Psatz ZArith Lia.
From Interval Require Import Tactic.
From Flocq Require Import Core.
Require Import BvnHighAssembly BvnHighRound BvnHighSteps BvnHighErr BvnHighErrTree.
Open Scope R_scope.

(** Leaves: 0 hk, 1 bs, 2 s*s, 3 the constant 1, 4 the constant 4, 5 the constant 12,
    6 s, 7 the exponential factor of A1, 8 exp(-hk/2), 9 sqrt(2 pi), 10 Phi(-b/s),
    11 b; then 12 c, 13 d, 14 the bracket 1 - d bs/5, 15 X, 16 Pol1, 17 Pol2. *)
Definition c_t : E := Dc 8 (Sb (Lf 4) (Lf 0)).
Definition d_t : E := Dc 16 (Sb (Lf 5) (Lf 0)).
Definition w_t : E := Sb (Lf 3) (Dc 5 (Ml (Lf 13) (Lf 1))).
Definition X_t : E := Dc 3 (Ml (Ml (Lf 12) (Sb (Lf 1) (Lf 2))) (Lf 14)).
Definition P1_t : E := Ad (Sb (Lf 3) (Lf 15)) (Dc 5 (Ml (Ml (Ml (Lf 12) (Lf 13)) (Lf 2)) (Lf 2))).
Definition P2_t : E := Sb (Lf 3) (Dc 3 (Ml (Ml (Lf 12) (Lf 1)) (Lf 14))).
Definition A1_t : E := Ml (Ml (Lf 6) (Lf 7)) (Lf 16).
Definition A2_t : E := Ml (Ml (Ml (Ml (Lf 8) (Lf 9)) (Lf 10)) (Lf 11)) (Lf 17).
Definition A_t : E := Sb A1_t A2_t.

Definition ext (f : nat -> R) (k : nat) (v : R) (i : nat) : R :=
  if Nat.eqb i k then v else f i.

Definition me0 (i : nat) : R :=
  match i with
  | 0 => 100 | 1 => 36009 / 10 ^ 7 | 2 => 9 / 10 ^ 6 | 3 => 1 | 4 => 4 | 5 => 12
  | 6 => 3 / 1000 | 7 => 1 | 8 => 10005 / 10000 | 9 => 2507 / 1000
  | 10 => 1 / 2 | 11 => 601 / 10000 | _ => 0 end.
Definition ee0 (i : nat) : R :=
  match i with
  | 0 => 100 * u + 1 / 10 ^ 190
  | 1 => 32 / 10 * u * (36009 / 10 ^ 7) + 1 / 10 ^ 190
  | 2 => u * (9 / 10 ^ 6) + eta
  | 3 | 4 | 5 | 6 => 0
  | 7 => 35 / 10 * u
  | 8 => 15 / 10 * u
  | 9 => 2 / 10 ^ 16
  | 10 => 183 / 100 * u
  | 11 => 43 / 10 * u * (601 / 10000) + 3 / 10 ^ 100
  | _ => 0 end.

Lemma henv_ext xe ce me ee k x x' m e :
  (forall i, ab (xe i) (ce i) (me i) (ee i)) -> ab x x' m e ->
  forall i, ab (ext xe k x i) (ext ce k x' i) (ext me k m i) (ext ee k e i).
Proof. intros H Hx i. unfold ext. destruct (Nat.eqb i k); [exact Hx | apply H]. Qed.

Lemma stage xe ce me ee t m e :
  (forall i, ab (xe i) (ce i) (me i) (ee i)) -> wf t ->
  fst (bnd me ee t) <= m -> snd (bnd me ee t) <= e ->
  ab (sem xe t) (csem ce t) m e.
Proof.
  intros H Hw Hm He. pose proof (sound xe ce me ee H t Hw) as S.
  eapply ab_mono; [exact S | exact Hm | exact He].
Qed.


Definition XE1 (xe0 : nat -> R) := ext xe0 12 (sem xe0 c_t).
Definition CE1 (xe0 ce0 : nat -> R) := ext ce0 12 (csem ce0 c_t).
Definition ME1 := ext me0 12 (13).
Definition EE1 := ext ee0 12 (39 * u).
Definition XE2 (xe0 : nat -> R) := ext (XE1 xe0) 13 (sem (XE1 xe0) d_t).
Definition CE2 (xe0 ce0 : nat -> R) := ext (CE1 xe0 ce0) 13 (csem (CE1 xe0 ce0) d_t).
Definition ME2 := ext ME1 13 (7).
Definition EE2 := ext EE1 13 (21 * u).
Definition XE3 (xe0 : nat -> R) := ext (XE2 xe0) 14 (sem (XE2 xe0) w_t).
Definition CE3 (xe0 ce0 : nat -> R) := ext (CE2 xe0 ce0) 14 (csem (CE2 xe0 ce0) w_t).
Definition ME3 := ext ME2 14 (10051 / 10000).
Definition EE3 := ext EE2 14 (11 / 10 * u).
Definition XE4 (xe0 : nat -> R) := ext (XE3 xe0) 15 (sem (XE3 xe0) X_t).
Definition CE4 (xe0 ce0 : nat -> R) := ext (CE3 xe0 ce0) 15 (csem (CE3 xe0 ce0) X_t).
Definition ME4 := ext ME3 15 (158 / 10000).
Definition EE4 := ext EE3 15 (2 / 10 * u).
Definition XE5 (xe0 : nat -> R) := ext (XE4 xe0) 16 (sem (XE4 xe0) P1_t).
Definition CE5 (xe0 ce0 : nat -> R) := ext (CE4 xe0 ce0) 16 (csem (CE4 xe0 ce0) P1_t).
Definition ME5 := ext ME4 16 (1016 / 1000).
Definition EE5 := ext EE4 16 (23 / 10 * u).
Definition XE6 (xe0 : nat -> R) := ext (XE5 xe0) 17 (sem (XE5 xe0) P2_t).
Definition CE6 (xe0 ce0 : nat -> R) := ext (CE5 xe0 ce0) 17 (csem (CE5 xe0 ce0) P2_t).
Definition ME6 := ext ME5 17 (1016 / 1000).
Definition EE6 := ext EE5 17 (13 / 10 * u).

Ltac num := cbv [ext me0 ee0 c_t d_t w_t X_t P1_t P2_t A1_t A2_t A_t ME1 ME2 ME3 ME4 ME5 ME6 EE1 EE2 EE3 EE4 EE5 EE6]; cbn; rewrite ?u_value; unfold eta; interval with (i_prec 120).

Section Chain.
Variables xe0 ce0 : nat -> R.
Hypothesis H0 : forall i, ab (xe0 i) (ce0 i) (me0 i) (ee0 i).

Lemma S1 : ab (sem xe0 c_t) (csem ce0 c_t) (13) (39 * u).
Proof.
  apply stage with (me := me0) (ee := ee0); [exact H0 | unfold c_t; simpl; repeat split; lra | | ].
  - num.
  - num.
Qed.
Lemma H1 : forall i, ab (XE1 xe0 i) (CE1 xe0 ce0 i) (ME1 i) (EE1 i).
Proof. exact (henv_ext _ _ _ _ 12 _ _ _ _ H0 S1). Qed.

Lemma S2 : ab (sem (XE1 xe0) d_t) (csem (CE1 xe0 ce0) d_t) (7) (21 * u).
Proof.
  apply stage with (me := ME1) (ee := EE1); [exact H1 | unfold d_t; simpl; repeat split; lra | | ].
  - num.
  - num.
Qed.
Lemma H2 : forall i, ab (XE2 xe0 i) (CE2 xe0 ce0 i) (ME2 i) (EE2 i).
Proof. exact (henv_ext _ _ _ _ 13 _ _ _ _ H1 S2). Qed.

Lemma S3 : ab (sem (XE2 xe0) w_t) (csem (CE2 xe0 ce0) w_t) (10051 / 10000) (11 / 10 * u).
Proof.
  apply stage with (me := ME2) (ee := EE2); [exact H2 | unfold w_t; simpl; repeat split; lra | | ].
  - num.
  - num.
Qed.
Lemma H3 : forall i, ab (XE3 xe0 i) (CE3 xe0 ce0 i) (ME3 i) (EE3 i).
Proof. exact (henv_ext _ _ _ _ 14 _ _ _ _ H2 S3). Qed.

Lemma S4 : ab (sem (XE3 xe0) X_t) (csem (CE3 xe0 ce0) X_t) (158 / 10000) (2 / 10 * u).
Proof.
  apply stage with (me := ME3) (ee := EE3); [exact H3 | unfold X_t; simpl; repeat split; lra | | ].
  - num.
  - num.
Qed.
Lemma H4 : forall i, ab (XE4 xe0 i) (CE4 xe0 ce0 i) (ME4 i) (EE4 i).
Proof. exact (henv_ext _ _ _ _ 15 _ _ _ _ H3 S4). Qed.

Lemma S5 : ab (sem (XE4 xe0) P1_t) (csem (CE4 xe0 ce0) P1_t) (1016 / 1000) (23 / 10 * u).
Proof.
  apply stage with (me := ME4) (ee := EE4); [exact H4 | unfold P1_t; simpl; repeat split; lra | | ].
  - num.
  - num.
Qed.
Lemma H5 : forall i, ab (XE5 xe0 i) (CE5 xe0 ce0 i) (ME5 i) (EE5 i).
Proof. exact (henv_ext _ _ _ _ 16 _ _ _ _ H4 S5). Qed.

Lemma S6 : ab (sem (XE5 xe0) P2_t) (csem (CE5 xe0 ce0) P2_t) (1016 / 1000) (13 / 10 * u).
Proof.
  apply stage with (me := ME5) (ee := EE5); [exact H5 | unfold P2_t; simpl; repeat split; lra | | ].
  - num.
  - num.
Qed.
Lemma H6 : forall i, ab (XE6 xe0 i) (CE6 xe0 ce0 i) (ME6 i) (EE6 i).
Proof. exact (henv_ext _ _ _ _ 17 _ _ _ _ H5 S6). Qed.

Lemma A_final : ab (sem (XE6 xe0) A_t) (csem (CE6 xe0 ce0) A_t) (8 / 100) (15 / 10 ^ 17).
Proof.
  apply stage with (me := ME6) (ee := EE6); [exact H6 | unfold A_t, A1_t, A2_t; simpl; repeat split; lra | | ].
  - num.
  - num.
Qed.
End Chain.
