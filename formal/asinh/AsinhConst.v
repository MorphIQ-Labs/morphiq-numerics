(** The values of asinh's binary64 constants and its comparisons. *)
From Coq Require Import Reals ZArith Lia Lra Psatz List.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 Encodings.
From Interval Require Import Tactic.
Require Import Ln1pLemmas AsinTables AsinKernel AsinSqrtStep AsinSegment AsinhKernel.
Open Scope R_scope.

Lemma two_m7_val : finite asinh_two_m7 /\ B asinh_two_m7 = bpow radix2 (-7).
Proof.
  destruct (word_ok_intro (0x3f80000000000000)%Z false 4503599627370496%positive 59%nat 1%Z 52%Z (-7)%Z
    eq_refl eq_refl ltac:(lia) eq_refl) as [F V]. split; [exact F | ].
  unfold asinh_two_m7. rewrite V. change (IZR 1) with 1. ring.
Qed.

Lemma two_28_val : finite asinh_two_28 /\ B asinh_two_28 = bpow radix2 28.
Proof.
  destruct (word_ok_intro (0x41b0000000000000)%Z false 4503599627370496%positive 24%nat 1%Z 52%Z 28%Z
    eq_refl eq_refl ltac:(lia) eq_refl) as [F V]. split; [exact F | ].
  unfold asinh_two_28. rewrite V. change (IZR 1) with 1. ring.
Qed.

Lemma quarter_val : finite asinh_quarter /\ B asinh_quarter = bpow radix2 (-2).
Proof.
  destruct (word_ok_intro (0x3fd0000000000000)%Z false 4503599627370496%positive 54%nat 1%Z 52%Z (-2)%Z
    eq_refl eq_refl ltac:(lia) eq_refl) as [F V]. split; [exact F | ].
  unfold asinh_quarter. rewrite V. change (IZR 1) with 1. ring.
Qed.

Lemma eps_val : finite asinh_eps /\ B asinh_eps = bpow radix2 (-63) * (1 + bpow radix2 (-50)).
Proof.
  destruct (word_ok_intro (0x3c00000000000004)%Z false 4503599627370500%positive 115%nat 1125899906842625%Z 2%Z (-113)%Z
    eq_refl eq_refl ltac:(lia) eq_refl) as [F V]. split; [exact F | ].
  unfold asinh_eps. rewrite V. bpow_num. 
  change (IZR 1125899906842625) with 1125899906842625. field.
Qed.

Lemma is_x_val : finite asinh_is_x /\ B asinh_is_x = IZR 3247657313705851 * bpow radix2 (-77).
Proof.
  destruct (word_ok_intro (0x3e57137449123ef6)%Z false 6495314627411702%positive 78%nat (3247657313705851)%Z 1%Z (-77)%Z
    eq_refl eq_refl ltac:(lia) eq_refl) as [F V]. split; [exact F | exact V].
Qed.

(** [asinh_lt x c] for finite binary64 values. *)
Lemma lt_correct x c : finite x -> finite c -> asinh_lt x c = true <-> B x < B c.
Proof.
  intros Fx Fc. unfold asinh_lt, asin_cmp. rewrite (Bcompare_correct 53 1024 x c Fx Fc).
  destruct (Rcompare_spec (B x) (B c)) as [H | H | H]; split; intros; try discriminate; try lra; auto.
Qed.
