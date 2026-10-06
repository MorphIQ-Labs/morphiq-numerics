(** The integer square root of crates/morphiq-numerics/src/sqrt.rs, [isqrt],
    transcribed step for step: the binary digit-by-digit method, with the
    starting bit found by the same shifting loop. [isqrt_correct]: for
    [0 < r < 2^128] it returns [⌊√r⌋] and the remainder [r − ⌊√r⌋²]. *)

From Coq Require Import ZArith Lia Psatz.
Open Scope Z_scope.

Fixpoint isqrt_loop (fuel : nat) (bit root rem : Z) : Z * Z :=
  match fuel with
  | O => (root, rem)
  | S f =>
      if bit =? 0 then (root, rem)
      else if root + bit <=? rem then isqrt_loop f (bit / 4) (root / 2 + bit) (rem - (root + bit))
      else isqrt_loop f (bit / 4) (root / 2) rem
  end.

Fixpoint start_bit (fuel : nat) (bit r : Z) : Z :=
  match fuel with
  | O => bit
  | S f => if r <? bit then start_bit f (bit / 4) r else bit
  end.

Definition isqrt (r : Z) : Z * Z := isqrt_loop 64 (start_bit 64 (2 ^ 126) r) 0 r.

Lemma pow4_succ k : 0 <= k -> 4 ^ (k + 1) = 4 * 4 ^ k.
Proof. intros. rewrite Z.pow_add_r by lia. lia. Qed.

Lemma pow4_pos k : 0 <= k -> 0 < 4 ^ k.
Proof. intros. apply Z.pow_pos_nonneg; lia. Qed.

(* One digit: n = r / 4^k, with y the root of n / 4. *)
Lemma digit r k y : 0 <= r -> 0 <= k -> y = Z.sqrt (r / 4 ^ (k + 1)) ->
  Z.sqrt (r / 4 ^ k) = if (2 * y + 1) ^ 2 * 4 ^ k <=? r then 2 * y + 1 else 2 * y.
Proof.
  intros Hr Hk Hy.
  pose proof (pow4_pos k Hk) as P.
  set (n := r / 4 ^ k).
  assert (Hm : r / 4 ^ (k + 1) = n / 4).
  { rewrite pow4_succ by lia. rewrite Z.mul_comm, <- Z.div_div by lia. reflexivity. }
  rewrite Hm in Hy.
  assert (Hn : 0 <= n) by (apply Z.div_pos; lia).
  assert (Hn4 : 0 <= n / 4) by (apply Z.div_pos; lia).
  pose proof (Z.sqrt_spec (n / 4) Hn4) as [S1 S2].
  rewrite <- Hy in S1, S2. unfold Z.succ in S2.
  assert (D1 : 4 * (n / 4) <= n) by (apply Z.mul_div_le; lia).
  assert (D2 : n < 4 * (n / 4) + 4).
  { pose proof (Z.mod_pos_bound n 4 ltac:(lia)). pose proof (Z.div_mod n 4 ltac:(lia)). lia. }
  assert (Lo : 4 * y ^ 2 <= n) by nia.
  assert (Hi : n < 4 * (y + 1) ^ 2) by nia.
  assert (Q : (2 * y + 1) ^ 2 * 4 ^ k <= r <-> (2 * y + 1) ^ 2 <= n).
  { unfold n. split; intros H.
    - apply Z.div_le_lower_bound; lia.
    - pose proof (Z.mul_div_le r (4 ^ k) P). nia. }
  destruct (Z.leb_spec ((2 * y + 1) ^ 2 * 4 ^ k) r) as [H | H].
  - apply Z.sqrt_unique. apply Q in H. unfold Z.succ. split; [nia | ].
    replace ((2 * y + 1 + 1) * (2 * y + 1 + 1)) with (4 * (y + 1) ^ 2) by ring. exact Hi.
  - apply Z.sqrt_unique. assert (N : ~ (2 * y + 1) ^ 2 <= n) by (rewrite <- Q; lia).
    unfold Z.succ. split; [replace (2 * y * (2 * y)) with (4 * y ^ 2) by ring; exact Lo | nia].
Qed.

Lemma loop_zero f a b : isqrt_loop f 0 a b = (a, b).
Proof. destruct f; reflexivity. Qed.

Lemma loop_correct (j : nat) fuel r y : (j < fuel)%nat -> 0 <= r ->
  y = Z.sqrt (r / 4 ^ (Z.of_nat j + 1)) ->
  isqrt_loop fuel (4 ^ Z.of_nat j) (y * 4 ^ (Z.of_nat j + 1)) (r - y ^ 2 * 4 ^ (Z.of_nat j + 1))
  = (Z.sqrt r, r - Z.sqrt r ^ 2).
Proof.
  revert fuel y. induction j as [| j IH]; intros fuel y Hf Hr Hy;
    destruct fuel as [| f]; try lia; cbn [isqrt_loop].
  - (* k = 0: the last digit; the next bit is 0. *)
    pose proof (digit r 0 y Hr ltac:(lia) Hy) as D.
    rewrite Z.pow_0_r, Z.div_1_r, Z.mul_1_r in D.
    replace (4 ^ (Z.of_nat 0 + 1)) with 4 by reflexivity.
    replace (4 ^ Z.of_nat 0) with 1 by reflexivity.
    change (1 =? 0) with false. cbv iota. change (1 / 4) with 0. rewrite !loop_zero.
    replace (y * 4 / 2) with (2 * y)
      by (replace (y * 4) with (2 * y * 2) by ring; rewrite Z.div_mul by lia; reflexivity).
    revert D.
    destruct (Z.leb_spec (y * 4 + 1) (r - y ^ 2 * 4)) as [H | H];
    destruct (Z.leb_spec ((2 * y + 1) ^ 2) r) as [H' | H']; intros D; try nia;
    rewrite D; f_equal; ring.
  - set (k := Z.of_nat (S j)).
    assert (Hk : 0 <= k) by lia.
    assert (Bit : 4 ^ k / 4 = 4 ^ Z.of_nat j).
    { unfold k. rewrite Nat2Z.inj_succ, <- Z.add_1_r, pow4_succ by lia. rewrite Z.mul_comm, Z.div_mul by lia. reflexivity. }
    assert (Root : y * 4 ^ (k + 1) / 2 = 2 * y * 4 ^ k).
    { rewrite pow4_succ by lia. replace (y * (4 * 4 ^ k)) with (2 * y * 4 ^ k * 2) by ring.
      rewrite Z.div_mul by lia. reflexivity. }
    pose proof (pow4_pos k Hk) as P.
    assert (Nz : (4 ^ k =? 0) = false) by (apply Z.eqb_neq; lia).
    rewrite Nz, Bit, Root.
    pose proof (digit r k y Hr Hk Hy) as D.
    assert (Kj : k = Z.of_nat j + 1) by (unfold k; lia).
    revert D.
    destruct (Z.leb_spec (y * 4 ^ (k + 1) + 4 ^ k) (r - y ^ 2 * 4 ^ (k + 1))) as [H | H];
    destruct (Z.leb_spec ((2 * y + 1) ^ 2 * 4 ^ k) r) as [H' | H'];
    intros D; try (rewrite pow4_succ in H by lia; nia).
    + replace (2 * y * 4 ^ k + 4 ^ k) with ((2 * y + 1) * 4 ^ (Z.of_nat j + 1)) by (rewrite <- Kj; ring).
      replace (r - y ^ 2 * 4 ^ (k + 1) - (y * 4 ^ (k + 1) + 4 ^ k))
        with (r - (2 * y + 1) ^ 2 * 4 ^ (Z.of_nat j + 1)) by (rewrite <- Kj, pow4_succ by lia; ring).
      apply IH; [lia | exact Hr | ]. rewrite <- Kj, D. reflexivity.
    + replace (2 * y * 4 ^ k) with ((2 * y) * 4 ^ (Z.of_nat j + 1)) by (rewrite <- Kj; ring).
      replace (r - y ^ 2 * 4 ^ (k + 1))
        with (r - (2 * y) ^ 2 * 4 ^ (Z.of_nat j + 1)) by (rewrite <- Kj, pow4_succ by lia; ring).
      apply IH; [lia | exact Hr | ]. rewrite <- Kj, D. reflexivity.
Qed.

Lemma start_correct (n : nat) fuel r : (n < fuel)%nat -> 0 < r -> r < 4 ^ (Z.of_nat n + 1) ->
  exists K : nat, (K <= n)%nat /\ start_bit fuel (4 ^ Z.of_nat n) r = 4 ^ Z.of_nat K /\
    4 ^ Z.of_nat K <= r < 4 ^ (Z.of_nat K + 1).
Proof.
  revert fuel. induction n as [| j IH]; intros fuel Hf H0 H1; destruct fuel as [| f]; try lia;
    cbn [start_bit].
  - exists O. replace (4 ^ Z.of_nat 0) with 1 by reflexivity.
    destruct (Z.ltb_spec r 1); [lia | ]. repeat split; try reflexivity; lia.
  - destruct (Z.ltb_spec r (4 ^ Z.of_nat (S j))) as [H | H].
    + assert (B : 4 ^ Z.of_nat (S j) / 4 = 4 ^ Z.of_nat j).
      { rewrite Nat2Z.inj_succ, <- Z.add_1_r, pow4_succ by lia.
        rewrite Z.mul_comm, Z.div_mul by lia. reflexivity. }
      rewrite B. destruct (IH f ltac:(lia) H0) as [K [HK E]].
      * rewrite Nat2Z.inj_succ, <- Z.add_1_r in H. exact H.
      * exists K. split; [lia | exact E].
    + exists (S j). repeat split; try reflexivity; lia.
Qed.

(** The Rust [isqrt]: [⌊√r⌋] and the remainder, for [0 < r < 2^128]. *)
Theorem isqrt_correct r : 0 < r < 2 ^ 128 -> isqrt r = (Z.sqrt r, r - Z.sqrt r ^ 2).
Proof.
  intros [H0 H1]. unfold isqrt.
  replace (2 ^ 126) with (4 ^ Z.of_nat 63) by reflexivity.
  destruct (start_correct 63 64 r ltac:(lia) H0 ltac:(exact H1)) as [K [HK [E [L U]]]].
  rewrite E.
  assert (Q : r / 4 ^ (Z.of_nat K + 1) = 0) by (apply Z.div_small; lia).
  pose proof (loop_correct K 64 r 0 ltac:(lia) ltac:(lia)) as C.
  rewrite Q, Z.sqrt_0 in C. specialize (C eq_refl).
  rewrite Z.mul_0_l, Z.pow_0_l, Z.mul_0_l, Z.sub_0_r in C by lia. exact C.
Qed.
