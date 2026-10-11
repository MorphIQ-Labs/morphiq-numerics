(** A reflective check of a table of double-words [(hi, lo)] against
    [T_j = 2^(j/2^s)] (docs/exp.md, section 4): one boolean computation over
    the whole table, run by [vm_compute], replaces a proof per entry.

    For each entry, given by its binary64 encodings, the check decodes both
    words, requires [hi] in [[1, 2)] and [|lo| <= 2^-53], and bounds
    [|hi + lo − T_j| <= 2^-b] without computing [T_j]: [x ↦ x^(2^s)] is
    increasing on the nonnegative reals and [T_j^(2^s) = 2^j], so it suffices
    that [(hi + lo − 2^-b)^(2^s) <= 2^j <= (hi + lo + 2^-b)^(2^s)]. Each power
    is taken by [s] squarings in integer arithmetic, rounded outward to
    [PREC] bits after each, so the computed bound encloses the exact power
    ([iter_up_ok], [iter_down_ok]). [table_check_ok] is the soundness theorem. *)

From Coq Require Import Reals ZArith List Lia Lra Psatz Bool.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import IEEE64.
Import ListNotations.

Open Scope R_scope.

(** [m·2^e]. *)
Definition dval (x : Z * Z) : R := IZR (fst x) * bpow radix2 (snd x).

(** The working precision of the squarings. *)
Definition PREC : Z := 128.

(** The bits to drop from [p] to keep [PREC]. *)
Definition drop (p : Z) : Z := Z.max 0 (Z.log2 p + 1 - PREC).

Definition sq_down (x : Z * Z) : Z * Z :=
  let '(m, e) := x in let p := (m * m)%Z in let s := drop p in (p / 2 ^ s, 2 * e + s)%Z.
Definition sq_up (x : Z * Z) : Z * Z :=
  let '(m, e) := x in let p := (m * m)%Z in let s := drop p in ((p + 2 ^ s - 1) / 2 ^ s, 2 * e + s)%Z.

Fixpoint iter (f : Z * Z -> Z * Z) (n : nat) (x : Z * Z) : Z * Z :=
  match n with O => x | S n => iter f n (f x) end.

(** [m·2^e <= 2^j] and [2^j <= m·2^e], exactly. *)
Definition le2 (x : Z * Z) (j : Z) : bool :=
  let '(m, e) := x in let t := Z.min e j in (m * 2 ^ (e - t) <=? 2 ^ (j - t))%Z.
Definition ge2 (x : Z * Z) (j : Z) : bool :=
  let '(m, e) := x in let t := Z.min e j in (2 ^ (j - t) <=? m * 2 ^ (e - t))%Z.

(** A finite encoding's value [m·2^e], or [None]. *)
Definition decode (n : Z) : option (Z * Z) :=
  match binary_float_of_bits_aux 52 11 n with
  | F754_finite s m e => Some (cond_Zopp s (Zpos m), e)
  | F754_zero _ => Some (0%Z, 0%Z)
  | _ => None
  end.

(** One entry: [j] its index, [hb] and [lb] its words' encodings. *)
Definition entry_check (s : nat) (b j hb lb : Z) : bool :=
  match decode hb, decode lb with
  | Some (mh, eh), Some (ml, el) =>
      let e := Z.min (Z.min eh el) (- b) in
      let m := (mh * 2 ^ (eh - e) + ml * 2 ^ (el - e))%Z in
      let d := (2 ^ (- b - e))%Z in
      (0 <=? hb)%Z && (hb <? 2 ^ 64)%Z && (0 <=? lb)%Z && (lb <? 2 ^ 64)%Z &&
      (hb =? 1023 * 2 ^ 52 + (mh - 2 ^ 52))%Z && (eh =? -52)%Z &&
      (2 ^ 52 <=? mh)%Z && (mh <? 2 ^ 53)%Z && le2 (Z.abs ml, el) (-53) &&
      (d <? m)%Z && le2 (iter sq_up s (m - d, e)%Z) j && ge2 (iter sq_down s (m + d, e)%Z) j
  | _, _ => false
  end.

Fixpoint check_from (s : nat) (b j : Z) (l : list (Z * Z)) : bool :=
  match l with
  | [] => true
  | (hb, lb) :: t => entry_check s b j hb lb && check_from s b (j + 1) t
  end.

Definition table_check (s : nat) (b : Z) (l : list (Z * Z)) : bool := check_from s b 0 l.

(** What the check establishes for an entry. *)
Definition entry_ok (hb lb : Z) (T : R) (b : Z) : Prop :=
  finite (b64_of_bits hb) /\ finite (b64_of_bits lb) /\
  (0 <= hb < 2 ^ 64)%Z /\ (exists f, hb = 1023 * 2 ^ 52 + f /\ 0 <= f < 2 ^ 52)%Z /\
  B (b64_of_bits hb) = IZR (hb - 1022 * 2 ^ 52) * bpow radix2 (-52) /\
  1 <= B (b64_of_bits hb) < 2 /\ Rabs (B (b64_of_bits lb)) <= / 2 ^ 53 /\
  Rabs (B (b64_of_bits hb) + B (b64_of_bits lb) - T) <= bpow radix2 (- b).

(** * Soundness *)

Lemma pow2_pos (k : Z) : (0 <= k)%Z -> (0 < 2 ^ k)%Z.
Proof. intros H. apply Z.pow_pos_nonneg; lia. Qed.

Lemma IZR_pow2 (k : Z) : (0 <= k)%Z -> IZR (2 ^ k) = bpow radix2 k.
Proof. intros H. rewrite <- IZR_Zpower by exact H. reflexivity. Qed.

Lemma sq_down_ok x : (0 <= fst x)%Z ->
  (0 <= fst (sq_down x))%Z /\ dval (sq_down x) <= dval x ^ 2.
Proof.
  destruct x as [m e]. cbn [fst]. intros Hm. unfold sq_down, dval. cbn [fst snd].
  set (p := (m * m)%Z). set (s := drop p).
  assert (Hs : (0 <= s)%Z) by (unfold s, drop; lia).
  pose proof (pow2_pos s Hs) as Ps.
  assert (Hp : (0 <= p)%Z) by (unfold p; nia).
  split; [apply Z.div_pos; lia | ].
  rewrite bpow_plus, <- (IZR_pow2 s Hs).
  replace (2 * e)%Z with (e + e)%Z by ring. rewrite bpow_plus.
  pose proof (Z.mul_div_le p (2 ^ s) Ps) as D.
  apply IZR_le in D. rewrite mult_IZR in D.
  replace ((IZR m * bpow radix2 e) ^ 2) with (IZR p * (bpow radix2 e * bpow radix2 e))
    by (unfold p; rewrite mult_IZR; ring).
  pose proof (bpow_gt_0 radix2 e) as Pe.
  replace (IZR (p / 2 ^ s) * (bpow radix2 e * bpow radix2 e * IZR (2 ^ s)))
    with (IZR (2 ^ s) * IZR (p / 2 ^ s) * (bpow radix2 e * bpow radix2 e)) by ring.
  apply Rmult_le_compat_r; [nra | exact D].
Qed.

Lemma sq_up_ok x : (0 <= fst x)%Z ->
  (0 <= fst (sq_up x))%Z /\ dval x ^ 2 <= dval (sq_up x).
Proof.
  destruct x as [m e]. cbn [fst]. intros Hm. unfold sq_up, dval. cbn [fst snd].
  set (p := (m * m)%Z). set (s := drop p).
  assert (Hs : (0 <= s)%Z) by (unfold s, drop; lia).
  pose proof (pow2_pos s Hs) as Ps.
  assert (Hp : (0 <= p)%Z) by (unfold p; nia).
  split; [apply Z.div_pos; lia | ].
  rewrite bpow_plus, <- (IZR_pow2 s Hs).
  replace (2 * e)%Z with (e + e)%Z by ring. rewrite bpow_plus.
  (* 2^s · ceil(p / 2^s) >= p *)
  assert (D : (p <= 2 ^ s * ((p + 2 ^ s - 1) / 2 ^ s))%Z).
  { pose proof (Z.div_mod (p + 2 ^ s - 1) (2 ^ s) ltac:(lia)) as M.
    pose proof (Z.mod_pos_bound (p + 2 ^ s - 1) (2 ^ s) Ps) as Bd. lia. }
  apply IZR_le in D. rewrite mult_IZR in D.
  replace ((IZR m * bpow radix2 e) ^ 2) with (IZR p * (bpow radix2 e * bpow radix2 e))
    by (unfold p; rewrite mult_IZR; ring).
  pose proof (bpow_gt_0 radix2 e) as Pe.
  replace (IZR ((p + 2 ^ s - 1) / 2 ^ s) * (bpow radix2 e * bpow radix2 e * IZR (2 ^ s)))
    with (IZR (2 ^ s) * IZR ((p + 2 ^ s - 1) / 2 ^ s) * (bpow radix2 e * bpow radix2 e)) by ring.
  apply Rmult_le_compat_r; [nra | exact D].
Qed.

Lemma dval_nonneg x : (0 <= fst x)%Z -> 0 <= dval x.
Proof. intros H. unfold dval. apply Rmult_le_pos; [apply IZR_le; exact H | apply bpow_ge_0]. Qed.

Lemma pow_pow2 (v : R) (n : nat) : (v ^ 2) ^ (2 ^ n) = v ^ (2 ^ S n).
Proof. rewrite <- pow_mult. reflexivity. Qed.

Lemma iter_up_ok n x : (0 <= fst x)%Z -> dval x ^ (2 ^ n) <= dval (iter sq_up n x).
Proof.
  revert x. induction n as [|n IH]; intros x Hx.
  - simpl. lra.
  - simpl iter. destruct (sq_up_ok x Hx) as [H0 H1].
    apply Rle_trans with (dval (sq_up x) ^ (2 ^ n)); [ | exact (IH _ H0)].
    rewrite <- pow_pow2. apply pow_incr. split; [apply pow_le, dval_nonneg, Hx | exact H1].
Qed.

Lemma iter_down_ok n x : (0 <= fst x)%Z -> dval (iter sq_down n x) <= dval x ^ (2 ^ n).
Proof.
  revert x. induction n as [|n IH]; intros x Hx.
  - simpl. lra.
  - simpl iter. destruct (sq_down_ok x Hx) as [H0 H1].
    apply Rle_trans with (dval (sq_down x) ^ (2 ^ n)); [exact (IH _ H0) | ].
    rewrite <- pow_pow2. apply pow_incr. split; [apply dval_nonneg, H0 | exact H1].
Qed.

Lemma le2_ok x j : le2 x j = true -> dval x <= bpow radix2 j.
Proof.
  destruct x as [m e]. unfold le2, dval. cbn [fst snd]. intros H. apply Z.leb_le in H.
  set (t := Z.min e j) in *.
  apply IZR_le in H. rewrite mult_IZR, !IZR_pow2 in H by lia.
  replace (bpow radix2 e) with (bpow radix2 (e - t) * bpow radix2 t) by (rewrite <- bpow_plus; f_equal; ring).
  replace (bpow radix2 j) with (bpow radix2 (j - t) * bpow radix2 t) by (rewrite <- bpow_plus; f_equal; ring).
  rewrite <- Rmult_assoc. apply Rmult_le_compat_r; [apply bpow_ge_0 | exact H].
Qed.

Lemma ge2_ok x j : ge2 x j = true -> bpow radix2 j <= dval x.
Proof.
  destruct x as [m e]. unfold ge2, dval. cbn [fst snd]. intros H. apply Z.leb_le in H.
  set (t := Z.min e j) in *.
  apply IZR_le in H. rewrite mult_IZR, !IZR_pow2 in H by lia.
  replace (bpow radix2 e) with (bpow radix2 (e - t) * bpow radix2 t) by (rewrite <- bpow_plus; f_equal; ring).
  replace (bpow radix2 j) with (bpow radix2 (j - t) * bpow radix2 t) by (rewrite <- bpow_plus; f_equal; ring).
  rewrite <- Rmult_assoc. apply Rmult_le_compat_r; [apply bpow_ge_0 | exact H].
Qed.

(** [x ↦ x^n] is strictly increasing on the nonnegative reals. *)
Lemma pow_lt_mono (x y : R) (n : nat) : 0 <= x < y -> (0 < n)%nat -> x ^ n < y ^ n.
Proof.
  intros [H0 H1] Hn. induction n as [|n IH]; [lia | ].
  destruct n as [|n]; [simpl; lra | ].
  assert (IH' : x ^ S n < y ^ S n) by (apply IH; lia).
  pose proof (pow_le x (S n) H0). simpl in *. nra.
Qed.

Lemma exp_pow x n : exp x ^ n = exp (INR n * x).
Proof.
  induction n as [|n IH]; [simpl; rewrite Rmult_0_l, exp_0; reflexivity | ].
  rewrite S_INR. simpl pow. rewrite IH, <- exp_plus. f_equal. ring.
Qed.

(** [T^(2^s) = 2^j] for [T = exp(j·ln 2 / 2^s)]. *)
Lemma table_power (s j : nat) :
  exp (INR j * ln 2 / IZR (2 ^ Z.of_nat s)) ^ (2 ^ s) = bpow radix2 (Z.of_nat j).
Proof.
  rewrite exp_pow.
  assert (E : INR (2 ^ s) = IZR (2 ^ Z.of_nat s)).
  { rewrite pow_INR, IZR_pow2 by lia. rewrite bpow_powerRZ, <- pow_powerRZ.
    replace (INR 2) with 2 by (simpl; ring). reflexivity. }
  assert (P : 0 < IZR (2 ^ Z.of_nat s)) by (apply IZR_lt; apply pow2_pos; lia).
  rewrite E. replace (IZR (2 ^ Z.of_nat s) * (INR j * ln 2 / IZR (2 ^ Z.of_nat s))) with (INR j * ln 2)
    by (field; lra).
  rewrite bpow_powerRZ, <- pow_powerRZ. change (IZR radix2) with 2.
  rewrite <- (Rpower_pow j 2) by lra. unfold Rpower. f_equal.
Qed.

(** The encodings' values. *)
Lemma decode_ok n m e : decode n = Some (m, e) ->
  finite (b64_of_bits n) /\ B (b64_of_bits n) = IZR m * bpow radix2 e.
Proof.
  unfold decode, b64_of_bits, binary_float_of_bits. rewrite is_finite_FF2B, B2R_FF2B.
  destruct (binary_float_of_bits_aux 52 11 n) as [s | s | s pl | s mx ex]; intros H;
    try discriminate; injection H as <- <-.
  - split; [reflexivity | simpl; ring].
  - split; reflexivity.
Qed.

Lemma Rabs_dval m e : Rabs (IZR m * bpow radix2 e) = IZR (Z.abs m) * bpow radix2 e.
Proof. rewrite Rabs_mult, Rabs_Zabs, (Rabs_pos_eq (bpow radix2 e)) by apply bpow_ge_0. reflexivity. Qed.

Theorem entry_check_ok s b j hb lb :
  entry_check s b (Z.of_nat j) hb lb = true ->
  entry_ok hb lb (exp (INR j * ln 2 / IZR (2 ^ Z.of_nat s))) b.
Proof.
  unfold entry_check. intros H.
  destruct (decode hb) as [[mh eh] | ] eqn:Dh; [ | discriminate].
  destruct (decode lb) as [[ml el] | ] eqn:Dl; [ | discriminate].
  destruct (decode_ok hb mh eh Dh) as [Fh Bh].
  destruct (decode_ok lb ml el Dl) as [Fl Bl].
  set (e := Z.min (Z.min eh el) (- b)) in H.
  set (m := (mh * 2 ^ (eh - e) + ml * 2 ^ (el - e))%Z) in H.
  set (d := (2 ^ (- b - e))%Z) in H.
  repeat rewrite andb_true_iff in H.
  destruct H as [[[[[[[[[[[H0 H1] H2] H3] Hb] He] Hm0] Hm1] Hl] Hd] Hup] Hdown].
  apply Z.leb_le in H0. apply Z.ltb_lt in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3.
  apply Z.eqb_eq in Hb. apply Z.eqb_eq in He. apply Z.leb_le in Hm0. apply Z.ltb_lt in Hm1.
  apply Z.ltb_lt in Hd.
  subst eh.
  (* the leading word *)
  assert (Th : B (b64_of_bits hb) = IZR (hb - 1022 * 2 ^ 52) * bpow radix2 (-52)).
  { rewrite Bh. f_equal. f_equal. lia. }
  assert (Th1 : 1 <= B (b64_of_bits hb) < 2).
  { rewrite Bh. apply IZR_le in Hm0. apply IZR_lt in Hm1.
    rewrite (IZR_pow2 52) in Hm0 by lia. rewrite (IZR_pow2 53) in Hm1 by lia.
    assert (E : bpow radix2 52 * bpow radix2 (-52) = 1) by (rewrite <- bpow_plus; reflexivity).
    assert (E' : bpow radix2 53 * bpow radix2 (-52) = 2) by (rewrite <- bpow_plus; reflexivity).
    pose proof (bpow_gt_0 radix2 (-52)). split; nra. }
  (* the trailing word *)
  assert (Tl : Rabs (B (b64_of_bits lb)) <= / 2 ^ 53).
  { rewrite Bl, Rabs_dval. apply le2_ok in Hl. unfold dval in Hl. cbn [fst snd] in Hl.
    replace (/ 2 ^ 53) with (bpow radix2 (-53)); [exact Hl | ].
    change (-53)%Z with (- Z.of_nat 53)%Z. rewrite bpow_opp, bpow_powerRZ, <- pow_powerRZ. reflexivity. }
  (* hi + lo and 2^-b on the common grid 2^e *)
  assert (Ee1 : (0 <= -52 - e)%Z) by (unfold e; lia).
  assert (Ee2 : (0 <= el - e)%Z) by (unfold e; lia).
  assert (Ee3 : (0 <= - b - e)%Z) by (unfold e; lia).
  assert (Sum : B (b64_of_bits hb) + B (b64_of_bits lb) = IZR m * bpow radix2 e).
  { rewrite Bh, Bl. unfold m. rewrite plus_IZR, !mult_IZR, !IZR_pow2 by assumption.
    replace (-52)%Z with ((-52 - e) + e)%Z at 1 by ring. replace el with ((el - e) + e)%Z at 1 by ring.
    rewrite !bpow_plus. ring. }
  assert (Del : bpow radix2 (- b) = IZR d * bpow radix2 e).
  { unfold d. rewrite IZR_pow2 by exact Ee3. rewrite <- bpow_plus. f_equal. ring. }
  set (T := exp (INR j * ln 2 / IZR (2 ^ Z.of_nat s))).
  assert (TN := table_power s j). fold T in TN.
  assert (Tp : 0 < T) by apply exp_pos.
  assert (N0 : (0 < 2 ^ s)%nat) by (apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia).
  (* below: (hi + lo − 2^-b)^(2^s) <= 2^j *)
  assert (Lo : B (b64_of_bits hb) + B (b64_of_bits lb) - bpow radix2 (- b) <= T).
  { apply le2_ok in Hup. pose proof (iter_up_ok s (m - d, e)%Z ltac:(simpl; lia)) as U.
    assert (V : dval (m - d, e)%Z = B (b64_of_bits hb) + B (b64_of_bits lb) - bpow radix2 (- b)).
    { unfold dval. cbn [fst snd]. rewrite Sum, Del, minus_IZR. ring. }
    rewrite V in U. apply Rnot_lt_le. intros Lt.
    assert (P : T ^ (2 ^ s) < dval (m - d, e)%Z ^ (2 ^ s)).
    { rewrite V. apply pow_lt_mono; [lra | exact N0]. }
    rewrite TN, V in P. lra. }
  (* above: 2^j <= (hi + lo + 2^-b)^(2^s) *)
  assert (Hi : T <= B (b64_of_bits hb) + B (b64_of_bits lb) + bpow radix2 (- b)).
  { apply ge2_ok in Hdown. pose proof (iter_down_ok s (m + d, e)%Z ltac:(simpl; unfold d; pose proof (pow2_pos _ Ee3); lia)) as U.
    assert (V : dval (m + d, e)%Z = B (b64_of_bits hb) + B (b64_of_bits lb) + bpow radix2 (- b)).
    { unfold dval. cbn [fst snd]. rewrite Sum, Del, plus_IZR. ring. }
    assert (V0 : 0 <= dval (m + d, e)%Z) by (apply dval_nonneg; simpl; unfold d; pose proof (pow2_pos _ Ee3); lia).
    rewrite V in U, V0. apply Rnot_lt_le. intros Lt.
    assert (P : dval (m + d, e)%Z ^ (2 ^ s) < T ^ (2 ^ s)).
    { rewrite V. apply pow_lt_mono; [lra | exact N0]. }
    rewrite TN, V in P. lra. }
  split; [exact Fh | split; [exact Fl | split; [lia | split; [ | split; [exact Th | split; [exact Th1 | split; [exact Tl | ]]]]]]].
  - exists (mh - 2 ^ 52)%Z. split; [exact Hb | lia].
  - apply Rabs_le. lra.
Qed.

Lemma check_from_ok s b l : forall j0 i, check_from s b j0 l = true -> (i < length l)%nat ->
  entry_check s b (j0 + Z.of_nat i) (fst (nth i l (0%Z, 0%Z))) (snd (nth i l (0%Z, 0%Z))) = true.
Proof.
  induction l as [|[hb lb] t IH]; intros j0 i H Hi; [simpl in Hi; lia | ].
  simpl in H. apply andb_true_iff in H as [H1 H2].
  destruct i as [|i].
  - simpl. rewrite Z.add_0_r. exact H1.
  - cbn [nth]. replace (j0 + Z.of_nat (S i))%Z with (j0 + 1 + Z.of_nat i)%Z by lia.
    apply IH; [exact H2 | simpl in Hi; lia].
Qed.

Theorem table_check_ok s b l j : table_check s b l = true -> (j < length l)%nat ->
  entry_ok (fst (nth j l (0%Z, 0%Z))) (snd (nth j l (0%Z, 0%Z)))
    (exp (INR j * ln 2 / IZR (2 ^ Z.of_nat s))) b.
Proof.
  intros H Hj. apply entry_check_ok.
  pose proof (check_from_ok s b l 0 j H Hj) as C. rewrite Z.add_0_l in C. exact C.
Qed.
