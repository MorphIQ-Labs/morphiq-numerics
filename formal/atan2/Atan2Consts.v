(** The constants of atan2's special values and tiny ratios: each encodes the correctly rounded
    value of its mathematical constant, and stays the correctly rounded value of a form
    [C -+ phi] while [phi] is far below half a unit in the last place. *)
From Coq Require Import Reals ZArith Lia Lra Psatz List.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 RoundingCore RoundingGaps.
From Interval Require Import Tactic.
Require Import Ln1pLemmas AsinTables AsinKernel AsinSqrtStep AsinSegment Atan2Tables Atan2Kernel.
Open Scope R_scope.

Lemma rn_const c Z : finite c -> 0 < B c -> Rabs (Z - B c) < B c * / 18014398509481984 -> rndF Z = B c.
Proof.
  intros Fc Pc H.
  apply round_relative_close; [exact (B_fmt c) | lra | ].
  assert (E : (2:R) ^ 54 = 18014398509481984) by (simpl; ring).
  rewrite (Rabs_pos_eq (B c)) by lra. rewrite E. unfold Rdiv. exact H.
Qed.

Lemma atan2_pi_val : finite atan2_pi /\ B atan2_pi = IZR 7074237752028440 * bpow radix2 (-51).
Proof.
  exact (word_ok_intro (0x400921fb54442d18)%Z false 7074237752028440%positive 51%nat 7074237752028440%Z 0%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl).
Qed.

Lemma atan2_half_pi_val : finite atan2_half_pi_f64 /\ B atan2_half_pi_f64 = IZR 7074237752028440 * bpow radix2 (-52).
Proof.
  exact (word_ok_intro (0x3ff921fb54442d18)%Z false 7074237752028440%positive 52%nat 7074237752028440%Z 0%Z (-52)%Z eq_refl eq_refl ltac:(lia) eq_refl).
Qed.

Lemma atan2_quarter_pi_val : finite atan2_quarter_pi /\ B atan2_quarter_pi = IZR 7074237752028440 * bpow radix2 (-53).
Proof.
  exact (word_ok_intro (0x3fe921fb54442d18)%Z false 7074237752028440%positive 53%nat 7074237752028440%Z 0%Z (-53)%Z eq_refl eq_refl ltac:(lia) eq_refl).
Qed.

Lemma atan2_three_quarter_pi_val : finite atan2_three_quarter_pi /\ B atan2_three_quarter_pi = IZR 5305678314021330 * bpow radix2 (-51).
Proof.
  exact (word_ok_intro (0x4002d97c7f3321d2)%Z false 5305678314021330%positive 51%nat 5305678314021330%Z 0%Z (-51)%Z eq_refl eq_refl ltac:(lia) eq_refl).
Qed.

Lemma pi_rn : finite atan2_pi /\ B atan2_pi = rndF PI.
Proof.
  destruct atan2_pi_val as [F V]. split; [exact F | ]. symmetry. apply rn_const; [exact F | | ].
  - rewrite V. bpow_num. interval with (i_prec 100).
  - rewrite V. bpow_num. interval with (i_prec 200).
Qed.

Lemma half_pi_rn_a : finite atan2_half_pi_f64 /\ B atan2_half_pi_f64 = rndF (PI / 2).
Proof.
  destruct atan2_half_pi_val as [F V]. split; [exact F | ]. symmetry. apply rn_const; [exact F | | ].
  - rewrite V. bpow_num. interval with (i_prec 100).
  - rewrite V. bpow_num. interval with (i_prec 200).
Qed.

Lemma quarter_pi_rn : finite atan2_quarter_pi /\ B atan2_quarter_pi = rndF (PI / 4).
Proof.
  destruct atan2_quarter_pi_val as [F V]. split; [exact F | ]. symmetry. apply rn_const; [exact F | | ].
  - rewrite V. bpow_num. interval with (i_prec 100).
  - rewrite V. bpow_num. interval with (i_prec 200).
Qed.

Lemma three_quarter_pi_rn : finite atan2_three_quarter_pi /\ B atan2_three_quarter_pi = rndF (3 * PI / 4).
Proof.
  destruct atan2_three_quarter_pi_val as [F V]. split; [exact F | ]. symmetry. apply rn_const; [exact F | | ].
  - rewrite V. bpow_num. interval with (i_prec 100).
  - rewrite V. bpow_num. interval with (i_prec 200).
Qed.

(** A constant moved by a tiny amount still rounds to its encoding. *)
Lemma rn_shift c C d : finite c -> 0 < B c -> Rabs (C - B c) + Rabs d < B c * / 18014398509481984 -> rndF (C + d) = B c.
Proof.
  intros Fc Pc H. apply rn_const; [exact Fc | exact Pc | ].
  apply Rle_lt_trans with (Rabs (C - B c) + Rabs d); [ | exact H].
  replace (C + d - B c) with ((C - B c) + d) by ring. apply Rabs_triang.
Qed.

Lemma half_pi_minus_rn phi : 0 <= phi <= / 100000000000000000000 -> rndF (PI / 2 - phi) = B atan2_half_pi_f64.
Proof.
  intros [P0 P1]. destruct atan2_half_pi_val as [F V]. set (c := B atan2_half_pi_f64) in *.
  assert (Pc : 0 < c) by (rewrite V; bpow_num; interval with (i_prec 100)).
  assert (Hc : Rabs (PI / 2 - c) + / 100000000000000000000 < c * / 18014398509481984) by (rewrite V; bpow_num; interval with (i_prec 200)).
  replace (PI / 2 - phi) with (PI / 2 + (- phi)) by ring.
  apply rn_shift; [exact F | exact Pc | ].
  fold c. rewrite Rabs_Ropp, (Rabs_pos_eq phi) by exact P0. lra.
Qed.

Lemma half_pi_plus_rn phi : 0 <= phi <= / 100000000000000000000 -> rndF (PI / 2 + phi) = B atan2_half_pi_f64.
Proof.
  intros [P0 P1]. destruct atan2_half_pi_val as [F V]. set (c := B atan2_half_pi_f64) in *.
  assert (Pc : 0 < c) by (rewrite V; bpow_num; interval with (i_prec 100)).
  assert (Hc : Rabs (PI / 2 - c) + / 100000000000000000000 < c * / 18014398509481984) by (rewrite V; bpow_num; interval with (i_prec 200)).
  apply rn_shift; [exact F | exact Pc | ].
  fold c. rewrite (Rabs_pos_eq phi) by exact P0. lra.
Qed.

Lemma pi_minus_rn phi : 0 <= phi <= / 100000000000000000000 -> rndF (PI - phi) = B atan2_pi.
Proof.
  intros [P0 P1]. destruct atan2_pi_val as [F V]. set (c := B atan2_pi) in *.
  assert (Pc : 0 < c) by (rewrite V; bpow_num; interval with (i_prec 100)).
  assert (Hc : Rabs (PI - c) + / 100000000000000000000 < c * / 18014398509481984) by (rewrite V; bpow_num; interval with (i_prec 200)).
  replace (PI - phi) with (PI + (- phi)) by ring.
  apply rn_shift; [exact F | exact Pc | ].
  fold c. rewrite Rabs_Ropp, (Rabs_pos_eq phi) by exact P0. lra.
Qed.
