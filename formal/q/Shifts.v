(** Q256's limb shifts, transcribed: [shl] and [shr] of q256.rs, limb by limb,
    with u64 semantics ([x << k] wraps modulo [2^64]). *)

From Coq Require Import Bool ZArith Lia Psatz List.
Import ListNotations.
Require Import Q128Mul Limbs Digits64.
Open Scope Z_scope.

Definition u64_shl (x k : Z) := (Z.shiftl x k) mod B.

(** [shl] for [s < 256]: limb [i] is [m[i − w] << b | m[i − w − 1] >> (64 − b)]. *)
Definition shl_limb (m : list Z) (s i : Z) : Z :=
  let w := s / 64 in let b := s mod 64 in
  if i <? w then 0 else
  let lo := nth (Z.to_nat (i - w)) m 0 in
  if b =? 0 then lo
  else Z.lor (u64_shl lo b) (if w <? i then Z.shiftr (nth (Z.to_nat (i - w - 1)) m 0) (64 - b) else 0).

Definition shl (m : list Z) (s : Z) : list Z := map (shl_limb m s) [0; 1; 2; 3].

(** [shr]: zero for [s >= 256]; limb [i] is [m[i + w] >> b | m[i + w + 1] << (64 − b)]. *)
Definition shr_limb (m : list Z) (s i : Z) : Z :=
  let w := s / 64 in let b := s mod 64 in
  if 4 - w <=? i then 0 else
  let hi := nth (Z.to_nat (i + w)) m 0 in
  if b =? 0 then hi
  else Z.lor (Z.shiftr hi b) (if i + w + 1 <? 4 then u64_shl (nth (Z.to_nat (i + w + 1)) m 0) (64 - b) else 0).

Definition shr (m : list Z) (s : Z) : list Z :=
  if 256 <=? s then [0; 0; 0; 0] else map (shr_limb m s) [0; 1; 2; 3].

Lemma u64_shl_mul x k : 0 <= k -> u64_shl x k = (x * 2 ^ k) mod B.
Proof. intros. unfold u64_shl. rewrite Z.shiftl_mul_pow2 by lia. reflexivity. Qed.

Lemma dig_high X n k : 0 <= X < B ^ n -> 0 <= n <= k -> dig X k = 0.
Proof.
  intros [H0 H1] Hk. unfold dig. rewrite Z.div_small; [reflexivity | ].
  split; [lia | ]. apply Z.lt_le_trans with (B ^ n); [lia | apply Z.pow_le_mono_r; [exact B_pos | lia]].
Qed.

Lemma nth_dig4 (m : list Z) k : limbs_ok m -> length m = 4%nat -> 0 <= k ->
  nth (Z.to_nat k) m 0 = dig (v m) k.
Proof.
  intros Ok L Hk. destruct (Z_lt_le_dec k 4) as [Lt | Ge].
  - rewrite nth_dig by (try assumption; lia). rewrite Z2Nat.id by lia. reflexivity.
  - rewrite nth_overflow by lia. symmetry. apply (dig_high _ 4); [ | lia].
    pose proof (v_bounds m Ok) as V. rewrite L in V. exact V.
Qed.

(** OR of a multiple of [2^b] below [B] with a value below [2^b] is their sum. *)
Lemma lor_low_high hi lo b : 0 <= lo < 2 ^ b -> 0 < b < 64 -> 0 <= hi ->
  Z.lor ((hi * 2 ^ b) mod B) lo = (hi * 2 ^ b) mod B + lo.
Proof.
  intros Hlo Hb Hhi.
  assert (EB : B = 2 ^ (64 - b) * 2 ^ b) by (unfold B; rewrite <- Z.pow_add_r by lia; f_equal; ring).
  assert (P1 : 0 < 2 ^ b) by (apply Z.pow_pos_nonneg; lia).
  assert (P2 : 0 < 2 ^ (64 - b)) by (apply Z.pow_pos_nonneg; lia).
  rewrite EB, Z.mul_mod_distr_r by lia.
  rewrite <- Z.shiftl_mul_pow2 by lia. rewrite Z.lor_comm.
  rewrite lor_disjoint_low; [ | lia | apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia | lia].
  rewrite ?Z.shiftl_mul_pow2 by lia. ring.
Qed.

Theorem shl_ok m s : limbs_ok m -> length m = 4%nat -> 0 <= s < 256 ->
  let r := shl m s in v r = (v m * 2 ^ s) mod 2 ^ 256 /\ limbs_ok r /\ length r = 4%nat.
Proof.
  intros Ok L Hs.
  pose proof (v_nonneg m Ok) as Vn.
  set (w := s / 64). set (b := s mod 64).
  assert (Sw : s = 64 * w + b) by (apply Z.div_mod; lia).
  assert (Hw : 0 <= w < 4) by (unfold w; split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  assert (Hb : 0 <= b < 64) by (apply Z.mod_pos_bound; lia).
  assert (EX : v m * 2 ^ s = (v m * 2 ^ b) * B ^ w).
  { rewrite Sw, Z.pow_add_r, Z.pow_mul_r by lia. unfold B. ring. }
  assert (Limb : forall i, 0 <= i < 4 -> shl_limb m s i = dig (v m * 2 ^ s) i).
  { intros i Hi. rewrite EX, dig_mul_words by first [lia | apply Z.mul_nonneg_nonneg; [lia | apply Z.pow_nonneg; lia]].
    unfold shl_limb. fold w b. destruct (Z.ltb_spec i w) as [Lt | Ge]; [reflexivity | ].
    rewrite nth_dig4 by (assumption || lia).
    destruct (Z.eqb_spec b 0) as [B0 | B1].
    - rewrite B0, Z.pow_0_r, Z.mul_1_r. reflexivity.
    - rewrite dig_mul_bits by lia. rewrite u64_shl_mul by lia.
      destruct (Z.eqb_spec (i - w) 0) as [E0 | E0].
      + replace (w <? i) with false by (symmetry; apply Z.ltb_ge; lia). rewrite Z.lor_0_r.
        replace (i - w =? 0) with true by (symmetry; apply Z.eqb_eq; exact E0). ring.
      + replace (w <? i) with true by (symmetry; apply Z.ltb_lt; lia).
        replace (i - w =? 0) with false by (symmetry; apply Z.eqb_neq; exact E0).
        rewrite nth_dig4 by (assumption || lia). rewrite Z.shiftr_div_pow2 by lia.
        replace (i - w - 1) with (i - w - 1) by ring.
        apply lor_low_high; [ | lia | apply dig_bound].
        split; [apply Z.div_pos; [apply dig_bound | apply Z.pow_pos_nonneg; lia] | ].
        apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia | ].
        rewrite <- Z.pow_add_r by lia. replace (64 - b + b) with 64 by ring. apply dig_bound. }
  assert (Ok' : limbs_ok (shl m s)).
  { unfold shl. repeat constructor; rewrite Limb by lia; apply dig_bound. }
  assert (L' : length (shl m s) = 4%nat) by reflexivity.
  split; [ | split; assumption].
  change (2 ^ 256) with (B ^ Z.of_nat 4). rewrite <- L'.
  apply digits_v; [apply Z.mul_nonneg_nonneg; [lia | apply Z.pow_nonneg; lia] | exact Ok' | ].
  intros i Hi. rewrite L' in Hi. unfold shl.
  destruct i as [ | [ | [ | [ | ?]]]]; try lia; simpl; apply Limb; lia.
Qed.

Theorem shr_ok m s : limbs_ok m -> length m = 4%nat -> 0 <= s ->
  let r := shr m s in v r = v m / 2 ^ s /\ limbs_ok r /\ length r = 4%nat.
Proof.
  intros Ok L Hs.
  pose proof (v_nonneg m Ok) as Vn. pose proof (v_bounds m Ok) as Vb. rewrite L in Vb.
  change (B ^ Z.of_nat 4) with (2 ^ 256) in Vb.
  unfold shr. destruct (Z.leb_spec 256 s) as [Big | Small].
  - repeat split; try (repeat constructor; unfold B; lia).
    cbn [v]. symmetry. rewrite Z.div_small; [ring | ].
    split; [lia | ]. apply Z.lt_le_trans with (2 ^ 256); [lia | apply Z.pow_le_mono_r; lia].
  - set (w := s / 64). set (b := s mod 64).
    assert (Sw : s = 64 * w + b) by (apply Z.div_mod; lia).
    assert (Hw : 0 <= w < 4) by (unfold w; split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
    assert (Hb : 0 <= b < 64) by (apply Z.mod_pos_bound; lia).
    assert (EX : v m / 2 ^ s = (v m / B ^ w) / 2 ^ b).
    { rewrite Z.div_div by (pose proof (PBi w ltac:(lia)); pose proof (Z.pow_pos_nonneg 2 b ltac:(lia) ltac:(lia)); lia).
      f_equal. rewrite Sw, Z.pow_add_r, Z.pow_mul_r by lia. reflexivity. }
    set (Y := v m / B ^ w).
    assert (HY : 0 <= Y) by (apply Z.div_pos; [lia | apply PBi; lia]).
    assert (DY : forall k, 0 <= k -> dig Y k = nth (Z.to_nat (k + w)) m 0).
    { intros k Hk. unfold Y. rewrite dig_div_words by lia. symmetry. apply nth_dig4; (assumption || lia). }
    assert (Limb : forall i, 0 <= i < 4 -> shr_limb m s i = dig (v m / 2 ^ s) i).
    { intros i Hi. rewrite EX. fold Y. unfold shr_limb. fold w b.
      destruct (Z.leb_spec (4 - w) i) as [Hi4 | Hi4].
      + (* beyond the value: zero *)
        symmetry. apply (dig_high _ (4 - w)); [ | lia]. split; [apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia] | ].
        apply Z.le_lt_trans with Y; [apply Z.div_le_upper_bound; [apply Z.pow_pos_nonneg; lia | ]; pose proof (Z.pow_pos_nonneg 2 b); nia | ].
        unfold Y. apply Z.div_lt_upper_bound; [apply PBi; lia | ].
        rewrite <- Z.pow_add_r by lia. replace (w + (4 - w)) with 4 by ring. change (B ^ 4) with (2 ^ 256). lia.
      + rewrite <- (DY i) by lia.
        destruct (Z.eqb_spec b 0) as [B0 | B1].
        * rewrite B0, Z.pow_0_r, Z.div_1_r. reflexivity.
        * rewrite dig_div_bits by lia. rewrite Z.shiftr_div_pow2 by lia.
          destruct (Z.ltb_spec (i + w + 1) 4) as [Lt | Ge].
          -- replace (i + w + 1) with (i + 1 + w) by ring.
             rewrite <- (DY (i + 1)) by lia. rewrite u64_shl_mul by lia.
             (* low part below 2^(64 − b), high part a multiple of it *)
             rewrite Z.lor_comm, (lor_low_high (dig Y (i + 1)) (dig Y i / 2 ^ b) (64 - b));
               [ring | | lia | apply dig_bound].
             split; [apply Z.div_pos; [apply dig_bound | apply Z.pow_pos_nonneg; lia] | ].
             apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia | ].
             rewrite <- Z.pow_add_r by lia. replace (b + (64 - b)) with 64 by ring. apply dig_bound.
          -- rewrite Z.lor_0_r. replace (dig Y (i + 1)) with 0.
             ++ rewrite Z.mul_0_l, Z.mod_0_l by (pose proof B_pos; lia). ring.
             ++ rewrite DY by lia. rewrite nth_overflow by lia. reflexivity. }
    assert (Ok' : limbs_ok (map (shr_limb m s) [0; 1; 2; 3])).
    { repeat constructor; rewrite Limb by lia; apply dig_bound. }
    assert (L' : length (map (shr_limb m s) [0; 1; 2; 3]) = 4%nat) by reflexivity.
    split; [ | split; assumption].
    assert (Xb : 0 <= v m / 2 ^ s < B ^ Z.of_nat 4).
    { split; [apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia] | ].
      apply Z.le_lt_trans with (v m); [apply Z.div_le_upper_bound; [apply Z.pow_pos_nonneg; lia | ];
        pose proof (Z.pow_pos_nonneg 2 s); nia | ]. change (B ^ Z.of_nat 4) with (2 ^ 256). lia. }
    rewrite <- (Z.mod_small (v m / 2 ^ s) (B ^ Z.of_nat 4)) by exact Xb. rewrite <- L'.
    apply digits_v; [lia | exact Ok' | ].
    intros i Hi. rewrite L' in Hi.
    destruct i as [ | [ | [ | [ | ?]]]]; try lia; simpl; apply Limb; lia.
Qed.
