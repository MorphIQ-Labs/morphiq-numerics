(** Q256's scans over limbs: [is_zero], [leading_zeros] (from the top limb
    down) and [cmp] (lexicographic from the top), each against the value. *)

From Coq Require Import Bool ZArith Lia Psatz List.
From Flocq Require Import Core Digits.
Import ListNotations.
Require Import Limbs.
Open Scope Z_scope.

Definition is_zero (m : list Z) : bool := forallb (fun l => l =? 0) m.

Lemma is_zero_ok m : limbs_ok m -> is_zero m = (v m =? 0).
Proof.
  induction 1 as [ | x m Hx Hm IH]; [reflexivity | ]. cbn [is_zero forallb v]. fold (is_zero m). rewrite IH.
  pose proof (v_nonneg m Hm). pose proof B_pos.
  destruct (Z.eqb_spec x 0), (Z.eqb_spec (v m) 0), (Z.eqb_spec (x + B * v m) 0); simpl; nia.
Qed.

(** u64::leading_zeros. *)
Definition lz64 (x : Z) := 64 - Zdigits radix2 x.

Fixpoint lz_scan (top_first : list Z) (acc : Z) : Z :=
  match top_first with
  | [] => acc
  | x :: r => if x =? 0 then lz_scan r (acc + 64) else acc + lz64 x
  end.

Definition leading_zeros (m : list Z) := lz_scan (rev m) 0.

(** The digits of [low + B^k·h], [h ≠ 0], [low < B^k]. *)
Lemma Zdigits_shift low h k : 0 <= low < B ^ k -> 0 < h -> 0 <= k ->
  Zdigits radix2 (low + B ^ k * h) = 64 * k + Zdigits radix2 h.
Proof.
  intros Hl Hh Hk. apply Zdigits_unique.
  pose proof (Zdigits_correct radix2 h) as D. rewrite Z.abs_eq in D by lia.
  change (Zpower radix2 (Zdigits radix2 h - 1)) with (2 ^ (Zdigits radix2 h - 1)) in D.
  change (Zpower radix2 (Zdigits radix2 h)) with (2 ^ Zdigits radix2 h) in D.
  assert (Hd : 1 <= Zdigits radix2 h).
  { destruct (Z_lt_le_dec (Zdigits radix2 h) 1) as [L | L]; [ | lia]. exfalso.
    assert (2 ^ Zdigits radix2 h <= 1) by (destruct (Z.eq_dec (Zdigits radix2 h) 0) as [-> | ]; [reflexivity | rewrite Z.pow_neg_r by lia; lia]). lia. }
  assert (EBk : B ^ k = 2 ^ (64 * k)) by (unfold B; rewrite <- Z.pow_mul_r by lia; reflexivity).
  change (Zpower radix2 (64 * k + Zdigits radix2 h - 1)) with (2 ^ (64 * k + Zdigits radix2 h - 1)).
  change (Zpower radix2 (64 * k + Zdigits radix2 h)) with (2 ^ (64 * k + Zdigits radix2 h)).
  rewrite Z.abs_eq by nia.
  replace (64 * k + Zdigits radix2 h - 1) with (64 * k + (Zdigits radix2 h - 1)) by ring.
  rewrite !Z.pow_add_r by lia. rewrite <- EBk. nia.
Qed.

Theorem leading_zeros_ok m : limbs_ok m -> length m = 4%nat -> v m <> 0 ->
  leading_zeros m = 256 - Zdigits radix2 (v m).
Proof.
  intros Ok L Hz.
  destruct m as [ | l0 [ | l1 [ | l2 [ | l3 [ | ? ?]]]]]; try discriminate.
  inversion Ok as [ | ? ? X0 P1]; subst. inversion P1 as [ | ? ? X1 P2]; subst.
  inversion P2 as [ | ? ? X2 P3]; subst. inversion P3 as [ | ? ? X3 _]; subst.
  unfold leading_zeros, lz64. cbn [rev app lz_scan]. cbn [v] in *. pose proof B_pos.
  assert (V : l0 + B * (l1 + B * (l2 + B * (l3 + B * 0))) = l0 + B * (l1 + B * (l2 + B * l3))) by ring.
  rewrite V in *.
  destruct (Z.eqb_spec l3 0) as [Z3 | Z3]; cbv beta iota.
  - rewrite Z3 in *. destruct (Z.eqb_spec l2 0) as [Z2 | Z2]; cbv beta iota.
    + rewrite Z2 in *. destruct (Z.eqb_spec l1 0) as [Z1 | Z1]; cbv beta iota.
      * rewrite Z1 in *. replace (l0 + B * (0 + B * (0 + B * 0))) with l0 in * by ring.
        destruct (Z.eqb_spec l0 0) as [Z0 | Z0]; cbv beta iota; [lia | ].
        unfold lz64. lia.
      * replace (l0 + B * (l1 + B * (0 + B * 0))) with (l0 + B ^ 1 * l1) by ring.
        rewrite Zdigits_shift by (unfold B in *; lia). unfold lz64. lia.
    + replace (l0 + B * (l1 + B * (l2 + B * 0))) with ((l0 + B * l1) + B ^ 2 * l2) by ring.
      rewrite Zdigits_shift by (unfold B in *; nia). unfold lz64. lia.
  - replace (l0 + B * (l1 + B * (l2 + B * l3))) with ((l0 + B * l1 + B ^ 2 * l2) + B ^ 3 * l3) by ring.
    rewrite Zdigits_shift by (unfold B in *; nia). unfold lz64. lia.
Qed.

Fixpoint cmp_scan (a b : list Z) : comparison :=
  match a, b with
  | x :: a', y :: b' => match Z.compare x y with Eq => cmp_scan a' b' | c => c end
  | _, _ => Eq
  end.

(** [a.iter().rev().cmp(b.iter().rev())] *)
Definition cmp (a b : list Z) := cmp_scan (rev a) (rev b).

Lemma compare_step x y X Y : 0 <= x < B -> 0 <= y < B ->
  Z.compare (x + B * X) (y + B * Y) = match Z.compare X Y with Eq => Z.compare x y | c => c end.
Proof.
  intros Hx Hy. pose proof B_pos.
  destruct (Z.compare_spec X Y) as [E | Lt | Gt].
  - subst. destruct (Z.compare_spec x y); [apply Z.compare_eq_iff | apply Z.compare_lt_iff | apply Z.compare_gt_iff]; lia.
  - apply Z.compare_lt_iff. nia.
  - apply Z.compare_gt_iff. nia.
Qed.

Theorem cmp_ok a b : limbs_ok a -> limbs_ok b -> length a = 4%nat -> length b = 4%nat ->
  cmp a b = Z.compare (v a) (v b).
Proof.
  intros Oa Ob La Lb.
  destruct a as [ | a0 [ | a1 [ | a2 [ | a3 [ | ? ?]]]]]; try discriminate.
  destruct b as [ | b0 [ | b1 [ | b2 [ | b3 [ | ? ?]]]]]; try discriminate.
  inversion Oa as [ | ? ? X0 P1]; subst. inversion P1 as [ | ? ? X1 P2]; subst.
  inversion P2 as [ | ? ? X2 P3]; subst. inversion P3 as [ | ? ? X3 _]; subst.
  inversion Ob as [ | ? ? Y0 Q1]; subst. inversion Q1 as [ | ? ? Y1 Q2]; subst.
  inversion Q2 as [ | ? ? Y2 Q3]; subst. inversion Q3 as [ | ? ? Y3 _]; subst.
  unfold cmp. cbn [rev app cmp_scan v].
  rewrite !compare_step by (assumption || (split; [nia | ]; pose proof B_pos; nia)).
  rewrite ?Z.mul_0_r, ?Z.add_0_r. simpl Z.compare at 1.
  destruct (Z.compare a3 b3), (Z.compare a2 b2), (Z.compare a1 b1), (Z.compare a0 b0); reflexivity.
Qed.
