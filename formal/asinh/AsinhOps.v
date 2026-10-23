(** Binary64 operations on bounded operands, signs and ranges free: each is
    finite and the correctly rounded exact result, and stays within the bound. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Binary64 Require Import Binary64Add IEEE64.
Require Import AsinNormal.
Open Scope R_scope.

Lemma bnd1 v e : Rabs v <= bpow radix2 e -> bnd 1 e v.
Proof. intros H. unfold bnd. change (IZR 1) with 1. rewrite Rmult_1_l. exact H. Qed.

Lemma unbnd1 v e : bnd 1 e v -> Rabs v <= bpow radix2 e.
Proof. unfold bnd. change (IZR 1) with 1. rewrite Rmult_1_l. intros H; exact H. Qed.

Lemma add_abs2 a b e : finite a -> finite b -> Rabs (B a + B b) <= bpow radix2 e -> (-1074 <= e <= 1000)%Z ->
  finite (fadd a b) /\ B (fadd a b) = rndF (B a + B b) /\ Rabs (B (fadd a b)) <= bpow radix2 e.
Proof.
  intros Fa Fb Hs [He1 He2].
  destruct (fadd_bnd 1 e a b Fa Fb ltac:(lia) He1 ltac:(apply Z.pow_gt_1; lia) ltac:(lia) (bnd1 _ _ Hs)) as [F [E Bd]].
  repeat split; try assumption. exact (unbnd1 _ _ Bd).
Qed.

Lemma sub_abs2 a b e : finite a -> finite b -> Rabs (B a - B b) <= bpow radix2 e -> (-1074 <= e <= 1000)%Z ->
  finite (fsub a b) /\ B (fsub a b) = rndF (B a - B b) /\ Rabs (B (fsub a b)) <= bpow radix2 e.
Proof.
  intros Fa Fb Hs [He1 He2].
  destruct (fsub_bnd 1 e a b Fa Fb ltac:(lia) He1 ltac:(apply Z.pow_gt_1; lia) ltac:(lia) (bnd1 _ _ Hs)) as [F [E Bd]].
  repeat split; try assumption. exact (unbnd1 _ _ Bd).
Qed.

Lemma mul_abs2 a b e : finite a -> finite b -> Rabs (B a * B b) <= bpow radix2 e -> (-1074 <= e <= 1000)%Z ->
  finite (fmul a b) /\ B (fmul a b) = rndF (B a * B b) /\ Rabs (B (fmul a b)) <= bpow radix2 e.
Proof.
  intros Fa Fb Hs [He1 He2].
  destruct (fmul_bnd 1 e a b Fa Fb ltac:(lia) He1 ltac:(apply Z.pow_gt_1; lia) ltac:(lia) (bnd1 _ _ Hs)) as [F [E Bd]].
  repeat split; try assumption. exact (unbnd1 _ _ Bd).
Qed.

Lemma div_abs2 a b e : finite a -> B b <> 0 -> Rabs (B a / B b) <= bpow radix2 e -> (-1074 <= e <= 1000)%Z ->
  finite (fdiv a b) /\ B (fdiv a b) = rndF (B a / B b) /\ Rabs (B (fdiv a b)) <= bpow radix2 e.
Proof.
  intros Fa Hb Hs [He1 He2].
  destruct (fdiv_bnd 1 e a b Fa Hb ltac:(lia) He1 ltac:(apply Z.pow_gt_1; lia) ltac:(lia) (bnd1 _ _ Hs)) as [F [E Bd]].
  repeat split; try assumption. exact (unbnd1 _ _ Bd).
Qed.

(** A rounding's error, in absolute terms of the exact value. *)
Lemma rnd_err a : Rabs (rndF a - a) <= bpow radix2 (-53) * Rabs a + bpow radix2 (-1075).
Proof. exact (rnd_err_abs a). Qed.
