(** Little-endian lists of 64-bit limbs, the significand representation of
    Q256 (crates/morphiq-numerics/src/q256.rs), and its limb loops: carries,
    borrows and multiply-accumulate rows, each proved against integer
    arithmetic on the list's value. *)

From Coq Require Import ZArith Lia Psatz List.
Import ListNotations.
Open Scope Z_scope.

Definition B := 2 ^ 64.

Lemma B_pos : 0 < B.
Proof. unfold B. lia. Qed.

Fixpoint v (l : list Z) : Z := match l with [] => 0 | x :: r => x + B * v r end.

Definition limbs_ok (l : list Z) := Forall (fun x => 0 <= x < B) l.

Lemma v_bounds l : limbs_ok l -> 0 <= v l < B ^ Z.of_nat (length l).
Proof.
  induction 1 as [ | x l Hx Hl IH]; cbn [v length]; [lia | ].
  rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. pose proof B_pos. nia.
Qed.

(** [add_limbs]: the sum with a carry chain; the chain's last carry is the
    carry out. *)
Fixpoint add_chain (a b : list Z) (carry : Z) : list Z * Z :=
  match a, b with
  | x :: a', y :: b' =>
      let s := x + y + carry in
      let '(out, c) := add_chain a' b' (s / B) in (s mod B :: out, c)
  | _, _ => ([], carry)
  end.

Lemma add_chain_ok a b c : length a = length b -> limbs_ok a -> limbs_ok b -> 0 <= c <= 1 ->
  let '(out, c') := add_chain a b c in
  v out + c' * B ^ Z.of_nat (length a) = v a + v b + c /\ limbs_ok out /\ 0 <= c' <= 1 /\ length out = length a.
Proof.
  revert b c. induction a as [ | x a IH]; intros [ | y b] c Hl Ha Hb Hc; try discriminate; cbn [add_chain v length].
  - repeat split; try lia; constructor.
  - inversion Ha as [ | ? ? Hx Ha']; subst. inversion Hb as [ | ? ? Hy Hb']; subst.
    injection Hl as Hl. pose proof B_pos as PB.
    assert (Q : 0 <= (x + y + c) / B <= 1).
    { split; [apply Z.div_pos; lia | ].
      assert ((x + y + c) / B < 2) by (apply Z.div_lt_upper_bound; lia). lia. }
    specialize (IH b ((x + y + c) / B) Hl Ha' Hb' Q).
    destruct (add_chain a b ((x + y + c) / B)) as [out c']. destruct IH as [E [Ok [C' L]]].
    cbn [v length]. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    pose proof (Z.div_mod (x + y + c) B ltac:(lia)) as D.
    repeat split; try lia.
    all: try (transitivity ((x + y + c) mod B + B * (v out + c' * B ^ Z.of_nat (length a))); [ring | rewrite E; unfold B in *; lia]).
    all: try (constructor; [apply Z.mod_pos_bound; lia | exact Ok]).
Qed.

(** [sub_limbs]: the difference with a borrow chain, for [a >= b]. *)
Fixpoint sub_chain (a b : list Z) (borrow : Z) : list Z * Z :=
  match a, b with
  | x :: a', y :: b' =>
      let d := x - y - borrow in
      let '(out, br) := sub_chain a' b' (if d <? 0 then 1 else 0) in (d mod B :: out, br)
  | _, _ => ([], borrow)
  end.

Lemma sub_chain_ok a b br : length a = length b -> limbs_ok a -> limbs_ok b -> 0 <= br <= 1 ->
  let '(out, br') := sub_chain a b br in
  v out - br' * B ^ Z.of_nat (length a) = v a - v b - br /\ limbs_ok out /\ 0 <= br' <= 1 /\ length out = length a.
Proof.
  revert b br. induction a as [ | x a IH]; intros [ | y b] br Hl Ha Hb Hbr; try discriminate; cbn [sub_chain v length].
  - repeat split; try lia; constructor.
  - inversion Ha as [ | ? ? Hx Ha']; subst. inversion Hb as [ | ? ? Hy Hb']; subst.
    injection Hl as Hl. pose proof B_pos as PB.
    set (nb := if x - y - br <? 0 then 1 else 0).
    assert (Nb : 0 <= nb <= 1) by (unfold nb; destruct (Z.ltb_spec (x - y - br) 0); lia).
    assert (Dm : x - y - br = (x - y - br) mod B - nb * B).
    { unfold nb. destruct (Z.ltb_spec (x - y - br) 0).
      - rewrite <- (Z.mod_unique (x - y - br) B (-1) (x - y - br + B)); [lia | left; lia | lia].
      - rewrite Z.mod_small; lia. }
    specialize (IH b nb Hl Ha' Hb' Nb).
    destruct (sub_chain a b nb) as [out br']. destruct IH as [E [Ok [C' L]]].
    cbn [v length]. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    repeat split; try lia.
    all: try (transitivity ((x - y - br) mod B + B * (v out - br' * B ^ Z.of_nat (length a))); [ring | rewrite E; unfold B in *; lia]).
    all: try (constructor; [apply Z.mod_pos_bound; lia | exact Ok]).
Qed.

Corollary sub_chain_exact a b : length a = length b -> limbs_ok a -> limbs_ok b -> v b <= v a ->
  let '(out, _) := sub_chain a b 0 in v out = v a - v b /\ limbs_ok out /\ length out = length a.
Proof.
  intros Hl Ha Hb Hle. pose proof (sub_chain_ok a b 0 Hl Ha Hb ltac:(lia)) as S.
  destruct (sub_chain a b 0) as [out br']. destruct S as [E [Ok [C' L]]].
  pose proof (v_bounds out Ok) as Vo. rewrite L in Vo.
  assert (br' = 0) by (destruct (Z.eq_dec br' 0); [assumption | assert (br' = 1) by lia; subst; nia]).
  subst. repeat split; [lia | exact Ok | exact L].
Qed.

(** One row of the schoolbook product: [w + x·b], with the carry out. *)
Fixpoint mac (x : Z) (b w : list Z) (carry : Z) : list Z * Z :=
  match b, w with
  | y :: b', p :: w' =>
      let t := x * y + p + carry in
      let '(out, c) := mac x b' w' (t / B) in (t mod B :: out, c)
  | _, _ => ([], carry)
  end.

Lemma mac_ok x b w c : length b = length w -> 0 <= x < B -> limbs_ok b -> limbs_ok w -> 0 <= c < B ->
  let '(out, c') := mac x b w c in
  v out + c' * B ^ Z.of_nat (length b) = v w + x * v b + c /\ limbs_ok out /\ 0 <= c' < B /\ length out = length b.
Proof.
  revert w c. induction b as [ | y b IH]; intros [ | p w] c Hl Hx Hb Hw Hc; try discriminate; cbn [mac v length].
  - repeat split; try lia; constructor.
  - inversion Hb as [ | ? ? Hy Hb']; subst. inversion Hw as [ | ? ? Hp Hw']; subst.
    injection Hl as Hl. pose proof B_pos as PB.
    (* t < B^2: (B−1)^2 + 2(B−1) = B^2 − 1 *)
    assert (T : 0 <= x * y + p + c < B * B) by nia.
    assert (Q : 0 <= (x * y + p + c) / B < B).
    { split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
    specialize (IH w ((x * y + p + c) / B) Hl Hx Hb' Hw' Q).
    destruct (mac x b w ((x * y + p + c) / B)) as [out c']. destruct IH as [E [Ok [C' L]]].
    cbn [v length]. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    pose proof (Z.div_mod (x * y + p + c) B ltac:(lia)) as D.
    repeat split; try lia.
    all: try (transitivity ((x * y + p + c) mod B + B * (v out + c' * B ^ Z.of_nat (length b))); [ring | rewrite E; unfold B in *; lia]).
    all: try (constructor; [apply Z.mod_pos_bound; lia | exact Ok]).
Qed.

Lemma v_app l1 l2 : v (l1 ++ l2) = v l1 + B ^ Z.of_nat (length l1) * v l2.
Proof.
  induction l1 as [ | x l1 IH]; cbn [v app length]; [rewrite Z.pow_0_r; ring | ].
  rewrite IH, Nat2Z.inj_succ, Z.pow_succ_r by lia. ring.
Qed.

Lemma limbs_ok_app l1 l2 : limbs_ok l1 -> limbs_ok l2 -> limbs_ok (l1 ++ l2).
Proof. intros. apply Forall_app. split; assumption. Qed.

Lemma limbs_ok_firstn n l : limbs_ok l -> limbs_ok (firstn n l).
Proof.
  revert l. induction n as [ | n IH]; intros [ | x l] H; simpl; try (constructor; fail).
  inversion H; subst. constructor; [assumption | apply IH; assumption].
Qed.

Lemma limbs_ok_skipn n l : limbs_ok l -> limbs_ok (skipn n l).
Proof.
  revert l. induction n as [ | n IH]; intros [ | x l] H; simpl; try assumption.
  inversion H; subst. apply IH; assumption.
Qed.

Lemma skipn_skipn' (x y : nat) (l : list Z) : skipn x (skipn y l) = skipn (x + y) l.
Proof.
  revert l. induction y as [ | y IH]; intros l.
  - rewrite Nat.add_0_r. reflexivity.
  - destruct l as [ | z l].
    + rewrite !skipn_nil. reflexivity.
    + replace (x + S y)%nat with (S (x + y)) by lia. simpl. apply IH.
Qed.

Lemma v_nonneg l : limbs_ok l -> 0 <= v l.
Proof. intros H. pose proof (v_bounds l H). lia. Qed.

(** Row [i] of the product: [p[i..i+4] += x·b], the carry into [p[i+4]]. *)
Definition row (i : nat) (x : Z) (b p : list Z) : list Z :=
  let w := firstn 4 (skipn i p) in
  let '(w', c) := mac x b w 0 in
  firstn i p ++ w' ++ c :: skipn (i + 5) p.

Lemma row_ok i x b p : (i <= 3)%nat -> length p = 8%nat -> length b = 4%nat ->
  limbs_ok p -> limbs_ok b -> 0 <= x < B -> v p < B ^ Z.of_nat (i + 4) ->
  let p' := row i x b p in
  v p' = v p + B ^ Z.of_nat i * x * v b /\ limbs_ok p' /\ length p' = 8%nat /\ v p' < B ^ Z.of_nat (i + 5).
Proof.
  intros Hi Hp Hb Op Ob Hx Hv. unfold row.
  set (w := firstn 4 (skipn i p)).
  assert (Lw : length w = 4%nat) by (unfold w; rewrite firstn_length, skipn_length; lia).
  assert (Ow : limbs_ok w) by (apply limbs_ok_firstn, limbs_ok_skipn, Op).
  pose proof (mac_ok x b w 0 ltac:(lia) Hx Ob Ow ltac:(pose proof B_pos; lia)) as M.
  destruct (mac x b w 0) as [w' c]. destruct M as [Mv [Mo [Mc Ml]]].
  rewrite Hb in Mv, Ml.
  (* p = firstn i p ++ w ++ skipn (i + 4) p, whose top part is zero *)
  assert (Sp : p = firstn i p ++ w ++ skipn (i + 4) p).
  { unfold w. rewrite <- (firstn_skipn i p) at 1. f_equal.
    rewrite <- (firstn_skipn 4 (skipn i p)) at 1. f_equal. rewrite skipn_skipn'. f_equal. lia. }
  assert (Lf : length (firstn i p) = i) by (rewrite firstn_length; lia).
  assert (Vs : v p = v (firstn i p) + B ^ Z.of_nat i * (v w + B ^ 4 * v (skipn (i + 4) p))).
  { rewrite Sp at 1. rewrite !v_app, Lf, Lw. reflexivity. }
  pose proof (v_nonneg _ (limbs_ok_firstn i p Op)) as N1.
  pose proof (v_nonneg _ Ow) as N2.
  pose proof (v_bounds _ (limbs_ok_firstn i p Op)) as F1. rewrite Lf in F1.
  pose proof (v_nonneg _ (limbs_ok_skipn (i + 4) p Op)) as N3.
  assert (PBi : 0 < B ^ Z.of_nat i) by (apply Z.pow_pos_nonneg; [apply B_pos | lia]).
  assert (E4 : B ^ Z.of_nat (i + 4) = B ^ Z.of_nat i * B ^ 4)
    by (rewrite Nat2Z.inj_add, Z.pow_add_r by lia; reflexivity).
  assert (Top : v (skipn (i + 4) p) = 0).
  { rewrite E4 in Hv. pose proof B_pos. assert (0 < B ^ 4) by (apply Z.pow_pos_nonneg; lia). nia. }
  (* skipn (i + 4) p = hd :: skipn (i + 5) p, both zero *)
  assert (Ls : length (skipn (i + 4) p) = (4 - i)%nat) by (rewrite skipn_length; lia).
  destruct (skipn (i + 4) p) as [ | hd rest] eqn:Esk; [cbn [length] in Ls; lia | ].
  assert (Er : skipn (i + 5) p = rest).
  { replace (i + 5)%nat with (1 + (i + 4))%nat by lia. rewrite <- skipn_skipn', Esk. reflexivity. }
  cbn [v] in Top. pose proof (v_nonneg _ (limbs_ok_skipn (i + 4) p Op)) as N4. rewrite Esk in N4.
  assert (Orest : limbs_ok rest) by (rewrite <- Er; apply limbs_ok_skipn, Op).
  pose proof (v_nonneg _ Orest) as N5.
  assert (Hd0 : 0 <= hd) by (assert (limbs_ok (hd :: rest)) by (rewrite <- Esk; apply limbs_ok_skipn, Op); inversion H; lia).
  assert (Vr : v rest = 0) by (pose proof B_pos; nia).
  rewrite Er. cbv zeta.
  assert (Vn : v (firstn i p ++ w' ++ c :: rest) = v (firstn i p) + B ^ Z.of_nat i * (v w' + B ^ 4 * c)).
  { rewrite !v_app, Lf, Ml. cbn [v]. rewrite Vr. change (Z.of_nat 4) with 4. ring. }
  pose proof (v_bounds b Ob) as Bb. rewrite Hb in Bb.
  cbn [v] in Vs. rewrite Top, Z.mul_0_r, Z.add_0_r in Vs.
  split; [ | split; [ | split]].
  - rewrite Vn, Vs.
    assert (Wb : v w' + B ^ 4 * c = v w + x * v b) by (change (Z.of_nat 4) with 4 in Mv; lia).
    rewrite Wb. ring.
  - apply limbs_ok_app; [apply limbs_ok_firstn, Op | ]. apply limbs_ok_app; [exact Mo | ].
    constructor; [lia | exact Orest].
  - rewrite !app_length, Lf, Ml. cbn [length] in *. lia.
  - rewrite Vn. rewrite Nat2Z.inj_add, Z.pow_add_r by lia.
    assert (Wb : v w' + B ^ 4 * c = v w + x * v b) by (change (Z.of_nat 4) with 4 in Mv; lia).
    rewrite Wb. pose proof (v_bounds w Ow) as Wv. rewrite Lw in Wv. change (Z.of_nat 4) with 4 in *.
    change (Z.of_nat 5) with 5. pose proof B_pos.
    assert (X : x * v b <= (B - 1) * (B ^ 4 - 1)) by (apply Z.mul_le_mono_nonneg; lia).
    assert (B5 : B ^ 5 = B * B ^ 4) by (rewrite <- Z.pow_succ_r by lia; reflexivity).
    assert (v w + x * v b < B ^ 5) by nia.
    assert (v (firstn i p) < B ^ Z.of_nat i) by lia.
    nia.
Qed.

(** Q256::mul's significand product: four rows into eight zeroed limbs. *)
Definition mul_limbs (a b : list Z) : list Z :=
  match a with
  | [a0; a1; a2; a3] => row 3 a3 b (row 2 a2 b (row 1 a1 b (row 0 a0 b (repeat 0 8))))
  | _ => repeat 0 8
  end.

Theorem mul_limbs_ok a b : length a = 4%nat -> length b = 4%nat -> limbs_ok a -> limbs_ok b ->
  let p := mul_limbs a b in v p = v a * v b /\ limbs_ok p /\ length p = 8%nat.
Proof.
  intros La Lb Oa Ob.
  destruct a as [ | a0 [ | a1 [ | a2 [ | a3 [ | ? ?]]]]]; try discriminate.
  inversion Oa as [ | ? ? X0 P1]; subst. inversion P1 as [ | ? ? X1 P2]; subst.
  inversion P2 as [ | ? ? X2 P3]; subst. inversion P3 as [ | ? ? X3 _]; subst.
  unfold mul_limbs.
  assert (Z8 : limbs_ok (repeat 0 8)) by (repeat constructor; unfold B; lia).
  pose proof (row_ok 0 a0 b (repeat 0 8) ltac:(lia) eq_refl Lb Z8 Ob X0 ltac:(simpl; unfold B; lia)) as [V0 [O0 [L0 B0]]].
  pose proof (row_ok 1 a1 b _ ltac:(lia) L0 Lb O0 Ob X1 B0) as [V1 [O1' [L1 B1]]].
  pose proof (row_ok 2 a2 b _ ltac:(lia) L1 Lb O1' Ob X2 B1) as [V2 [O2' [L2 B2]]].
  pose proof (row_ok 3 a3 b _ ltac:(lia) L2 Lb O2' Ob X3 B2) as [V3 [O3' [L3 B3]]].
  split; [ | split; assumption].
  rewrite V3, V2, V1, V0. cbn [v repeat]. change (Z.of_nat 0) with 0. change (Z.of_nat 1) with 1.
  change (Z.of_nat 2) with 2. change (Z.of_nat 3) with 3. ring.
Qed.
