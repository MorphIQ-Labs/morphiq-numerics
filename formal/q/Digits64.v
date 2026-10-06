(** Base-2^64 digits: [dig X i] is limb [i] of [X]. A limb list is its value's
    digits, and a list whose limbs are [X]'s digits has value [X mod B^n];
    shifting by whole limbs or by [b] bits moves digits predictably. *)

From Coq Require Import ZArith Lia Psatz List.
Import ListNotations.
Require Import Limbs.
Open Scope Z_scope.

Definition dig (X i : Z) := (X / B ^ i) mod B.

Lemma PB : 0 < B. Proof. exact B_pos. Qed.
Lemma PBi i : 0 <= i -> 0 < B ^ i. Proof. intros. apply Z.pow_pos_nonneg; [exact B_pos | lia]. Qed.

Lemma dig_succ X i : 0 <= X -> 0 <= i -> dig X (i + 1) = dig (X / B) i.
Proof.
  intros. unfold dig. rewrite Z.pow_add_r, Z.pow_1_r by lia.
  rewrite Z.mul_comm, <- Z.div_div by (pose proof PB; pose proof (PBi i); lia). reflexivity.
Qed.

Lemma mod_mul_r' X b c : 0 <= X -> 0 < b -> 0 < c -> X mod (b * c) = X mod b + b * ((X / b) mod c).
Proof.
  intros HX Hb Hc. symmetry. apply Z.mod_unique with ((X / b) / c).
  - left. pose proof (Z.mod_pos_bound X b Hb). pose proof (Z.mod_pos_bound (X / b) c Hc). nia.
  - pose proof (Z.div_mod X b ltac:(lia)). pose proof (Z.div_mod (X / b) c ltac:(lia)). nia.
Qed.

Lemma digits_v (out : list Z) X : 0 <= X -> limbs_ok out ->
  (forall i, (i < length out)%nat -> nth i out 0 = dig X (Z.of_nat i)) ->
  v out = X mod B ^ Z.of_nat (length out).
Proof.
  revert X. induction out as [ | x out IH]; intros X HX Ok H.
  - simpl. rewrite Z.mod_1_r. reflexivity.
  - inversion Ok; subst. cbn [v length].
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    rewrite mod_mul_r' by (try lia; try exact PB; apply PBi; lia).
    f_equal.
    + specialize (H 0%nat ltac:(cbn [length]; lia)). cbn [nth] in H. rewrite H. unfold dig. rewrite Z.pow_0_r, Z.div_1_r. reflexivity.
    + f_equal. apply IH; [apply Z.div_pos; [lia | exact PB] | assumption | ].
      intros i Hi. specialize (H (S i) ltac:(cbn [length]; lia)). cbn [nth] in H. rewrite H.
      rewrite Nat2Z.inj_succ, <- Z.add_1_r. apply dig_succ; lia.
Qed.

Lemma nth_dig (l : list Z) i : limbs_ok l -> (i < length l)%nat -> nth i l 0 = dig (v l) (Z.of_nat i).
Proof.
  revert i. induction l as [ | x l IH]; intros i Ok Hi; [cbn [length] in Hi; lia | ].
  inversion Ok; subst. destruct i as [ | i].
  - cbn [nth]. unfold dig. change (Z.of_nat 0) with 0. rewrite Z.pow_0_r, Z.div_1_r. cbn [v].
    rewrite Z.mul_comm, Z.mod_add by (pose proof PB; lia). rewrite Z.mod_small; lia.
  - cbn [nth]. rewrite IH by (try assumption; cbn [length] in Hi; lia).
    rewrite Nat2Z.inj_succ, <- Z.add_1_r, dig_succ by (try lia; apply v_nonneg; constructor; assumption).
    f_equal. cbn [v]. rewrite Z.mul_comm, Z.div_add by (pose proof PB; lia).
    rewrite Z.div_small by lia. ring.
Qed.

Lemma dig_bound X i : 0 <= dig X i < B.
Proof. unfold dig. apply Z.mod_pos_bound. exact PB. Qed.

(** Whole-limb shifts. *)
Lemma dig_mul_words X w i : 0 <= X -> 0 <= w -> 0 <= i ->
  dig (X * B ^ w) i = if i <? w then 0 else dig X (i - w).
Proof.
  intros HX Hw Hi. unfold dig. destruct (Z.ltb_spec i w) as [L | L].
  - assert (E : X * B ^ w = (X * B ^ (w - i - 1)) * B * B ^ i).
    { replace w with ((w - i - 1) + 1 + i) at 1 by ring. rewrite !Z.pow_add_r, Z.pow_1_r by lia. ring. }
    rewrite E, Z.div_mul by (pose proof (PBi i); lia).
    rewrite Z.mod_mul by (pose proof PB; lia). reflexivity.
  - replace (B ^ i) with (B ^ (i - w) * B ^ w) by (rewrite <- Z.pow_add_r by lia; f_equal; ring).
    rewrite Z.div_mul_cancel_r by (pose proof (PBi (i - w)); pose proof (PBi w); lia). reflexivity.
Qed.

Lemma dig_div_words X w i : 0 <= X -> 0 <= w -> 0 <= i -> dig (X / B ^ w) i = dig X (i + w).
Proof.
  intros. unfold dig. rewrite Z.div_div by (pose proof (PBi w); pose proof (PBi i); lia).
  rewrite <- Z.pow_add_r by lia. f_equal. f_equal. f_equal. ring.
Qed.

(** Shifts by [0 < b < 64] bits. *)
Lemma dig_mul_bits X b j : 0 <= X -> 0 < b < 64 -> 0 <= j ->
  dig (X * 2 ^ b) j = (dig X j * 2 ^ b) mod B + (if j =? 0 then 0 else dig X (j - 1) / 2 ^ (64 - b)).
Proof.
  intros HX Hb Hj.
  assert (P2 : 0 < 2 ^ b) by (apply Z.pow_pos_nonneg; lia).
  assert (P2' : 0 < 2 ^ (64 - b)) by (apply Z.pow_pos_nonneg; lia).
  assert (EB : B = 2 ^ b * 2 ^ (64 - b)) by (unfold B; rewrite <- Z.pow_add_r by lia; f_equal; ring).
  destruct (Z.eqb_spec j 0) as [-> | Nj].
  - unfold dig. rewrite !Z.pow_0_r, !Z.div_1_r. rewrite Z.add_0_r, Z.mul_mod_idemp_l by (pose proof PB; lia). reflexivity.
  - (* X = H·B^j + m·B^(j−1) + R, R < B^(j−1) *)
    set (k := j - 1). assert (Hk : 0 <= k) by lia. replace j with (k + 1) by (unfold k; ring).
    set (H := X / B ^ (k + 1)). set (Lw := X mod B ^ (k + 1)).
    assert (PBk : 0 < B ^ k) by (apply PBi; lia).
    assert (PBk1 : B ^ (k + 1) = B ^ k * B) by (rewrite Z.pow_add_r, Z.pow_1_r by lia; reflexivity).
    pose proof (Z.div_mod X (B ^ (k + 1)) ltac:(rewrite PBk1; pose proof PB; nia)) as DX.
    pose proof (Z.mod_pos_bound X (B ^ (k + 1)) ltac:(rewrite PBk1; pose proof PB; nia)) as ML.
    fold H Lw in DX, ML.
    (* Lw = m·B^k + R *)
    set (m := Lw / B ^ k). set (R := Lw mod B ^ k).
    pose proof (Z.div_mod Lw (B ^ k) ltac:(lia)) as DL. pose proof (Z.mod_pos_bound Lw (B ^ k) PBk) as MR.
    fold m R in DL, MR.
    assert (Mb : 0 <= m < B).
    { unfold m. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; [lia | ]]. rewrite <- PBk1. lia. }
    assert (Dk1 : dig X (k + 1) = H mod B) by reflexivity.
    assert (Dk : dig X k = m).
    { unfold dig. replace (X / B ^ k) with (H * B + m).
      - rewrite Z.add_comm, Z.mod_add by (pose proof PB; lia). apply Z.mod_small. exact Mb.
      - apply Z.div_unique with R; [left; exact MR | ]. rewrite DX at 1. rewrite DL at 1. rewrite PBk1. ring. }
    replace (k + 1 - 1) with k by ring. rewrite Dk1, Dk.
    replace (k + 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    unfold dig.
    (* X·2^b / B^(k+1) = H·2^b + q, q = m / 2^(64−b) *)
    assert (Q : X * 2 ^ b / B ^ (k + 1) = H * 2 ^ b + m / 2 ^ (64 - b)).
    { symmetry. apply Z.div_unique with ((m mod 2 ^ (64 - b)) * 2 ^ b * B ^ k + R * 2 ^ b).
      - left. pose proof (Z.mod_pos_bound m (2 ^ (64 - b)) P2') as Mm.
        split; [nia | ]. rewrite PBk1.
        assert ((m mod 2 ^ (64 - b)) * 2 ^ b <= B - 2 ^ b) by (rewrite EB; nia).
        assert (R * 2 ^ b < B ^ k * 2 ^ b) by nia. nia.
      - pose proof (Z.div_mod m (2 ^ (64 - b)) ltac:(lia)) as Dm.
        rewrite DX at 1. rewrite DL at 1. rewrite PBk1. rewrite Dm at 1. rewrite EB. ring. }
    rewrite Q.
    (* (H·2^b + q) mod B, with q < 2^b and (H·2^b) mod B a multiple of 2^b *)
    assert (Qb : 0 <= m / 2 ^ (64 - b) < 2 ^ b).
    { split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; [lia | ]]. rewrite Z.mul_comm, <- EB. lia. }
    rewrite Z.add_mod by (pose proof PB; lia). rewrite (Z.mod_small (m / 2 ^ (64 - b)) B) by (rewrite EB; nia).
    rewrite Z.mul_mod_idemp_l by (pose proof PB; lia).
    apply Z.mod_small. split.
    + pose proof (Z.mod_pos_bound (H * 2 ^ b) B PB). lia.
    + (* (H·2^b) mod B = ((H mod 2^(64−b))·2^b) <= B − 2^b *)
      assert (Hm : (H * 2 ^ b) mod B = (H mod 2 ^ (64 - b)) * 2 ^ b).
      { rewrite EB, (Z.mul_comm (2 ^ b) (2 ^ (64 - b))). apply Z.mul_mod_distr_r; lia. }
      rewrite Hm. pose proof (Z.mod_pos_bound H (2 ^ (64 - b)) P2').
      assert ((H mod 2 ^ (64 - b)) * 2 ^ b <= B - 2 ^ b) by (rewrite EB; nia). lia.
Qed.

Lemma dig_div_bits X b j : 0 <= X -> 0 < b < 64 -> 0 <= j ->
  dig (X / 2 ^ b) j = dig X j / 2 ^ b + (dig X (j + 1) * 2 ^ (64 - b)) mod B.
Proof.
  intros HX Hb Hj.
  assert (P2 : 0 < 2 ^ b) by (apply Z.pow_pos_nonneg; lia).
  assert (P2' : 0 < 2 ^ (64 - b)) by (apply Z.pow_pos_nonneg; lia).
  assert (EB : B = 2 ^ b * 2 ^ (64 - b)) by (unfold B; rewrite <- Z.pow_add_r by lia; f_equal; ring).
  pose proof (PBi j Hj) as Pj.
  set (Y := X / B ^ j).
  assert (HY : 0 <= Y) by (apply Z.div_pos; lia).
  set (mj := Y mod B). set (Y' := Y / B).
  pose proof (Z.div_mod Y B ltac:(pose proof PB; lia)) as DY. fold mj Y' in DY.
  assert (Mj : 0 <= mj < B) by (apply Z.mod_pos_bound, PB).
  assert (HY' : 0 <= Y') by (apply Z.div_pos; [lia | exact PB]).
  assert (Dj : dig X j = mj) by reflexivity.
  assert (Dj1 : dig X (j + 1) = Y' mod B).
  { unfold dig, Y', Y. rewrite Z.pow_add_r, Z.pow_1_r by lia. rewrite Z.div_div by (pose proof PB; lia). reflexivity. }
  rewrite Dj, Dj1. unfold dig.
  replace (X / 2 ^ b / B ^ j) with (mj / 2 ^ b + 2 ^ (64 - b) * Y').
  2: { rewrite Z.div_div by lia. rewrite (Z.mul_comm (2 ^ b) (B ^ j)). rewrite <- Z.div_div by lia.
       change (X / B ^ j) with Y. rewrite DY, EB.
       replace (2 ^ b * 2 ^ (64 - b) * Y' + mj) with (mj + (2 ^ (64 - b) * Y') * 2 ^ b) by ring.
       rewrite Z.div_add by lia. reflexivity. }
  assert (Q : 0 <= mj / 2 ^ b < 2 ^ (64 - b)).
  { split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; [lia | ]]. rewrite <- EB. lia. }
  assert (Hm : (2 ^ (64 - b) * Y') mod B = (Y' mod 2 ^ b) * 2 ^ (64 - b)).
  { rewrite EB, Z.mul_comm. apply Z.mul_mod_distr_r; lia. }
  assert (Hm' : (Y' mod B * 2 ^ (64 - b)) mod B = (2 ^ (64 - b) * Y') mod B).
  { rewrite Z.mul_mod_idemp_l by (pose proof PB; lia). f_equal. ring. }
  rewrite Hm'. rewrite Z.add_mod by (pose proof PB; lia). rewrite (Z.mod_small (mj / 2 ^ b)) by (rewrite EB; nia).
  apply Z.mod_small. rewrite Hm. pose proof (Z.mod_pos_bound Y' (2 ^ b) P2).
  assert ((Y' mod 2 ^ b) * 2 ^ (64 - b) <= B - 2 ^ (64 - b)) by (rewrite EB; nia). lia.
Qed.
