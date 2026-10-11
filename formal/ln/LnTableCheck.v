(** The accurate path's constants and the reduction's case ratios
    (docs/ln.md, sections 3 and 6), each table proved by one reflective
    computation ([vm_compute]) with formal/ln/LnCheck.v's enclosure of [ln]:
    - [neg_ln_r_q_ok]: [−ln R[i]] in Q128, relative error at most [2^-127],
      its significand's top bit set, and zero where [R[i] = 1];
    - [ln2_q_ok]: [ln 2] likewise; [recip_q_ok]: [1/k], [k = 1..18];
    - [ratios_ok]: over every table interval, closed and widened by [2^-52]
      for [ln_1p]'s [y'], the ratios the accurate certificates
      (formal/ln/accurate_sum_b.g, _c.g) take as hypotheses, for every
      exponent [E ≠ 0]. *)

From Coq Require Import ZArith Reals Lia Lra Psatz List Bool.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import IEEE64.
Require Import LnCheck LnTables.
Import ListNotations.

Open Scope R_scope.

(** * Decoding and comparing *)

(** A finite encoding's value [m·2^e], or [None]. *)
Definition dec (n : Z) : option (Z * Z) :=
  match binary_float_of_bits_aux 52 11 n with
  | F754_finite s m e => Some (cond_Zopp s (Zpos m), e)
  | F754_zero _ => Some (0%Z, 0%Z)
  | _ => None
  end.

Lemma dec_ok n m e : dec n = Some (m, e) ->
  finite (b64_of_bits n) /\ B (b64_of_bits n) = IZR m * bpow radix2 e.
Proof.
  unfold dec, b64_of_bits, binary_float_of_bits. rewrite is_finite_FF2B, B2R_FF2B.
  destruct (binary_float_of_bits_aux 52 11 n) as [s | s | s pl | s mx ex]; intros H;
    try discriminate; injection H as <- <-.
  - split; [reflexivity | simpl; ring].
  - split; reflexivity.
Qed.

(** [a·2^ea <= b·2^eb], exactly. *)
Definition le_sc (a ea b eb : Z) : bool :=
  let t := Z.min ea eb in (a * 2 ^ (ea - t) <=? b * 2 ^ (eb - t))%Z.

Lemma IZR_pow2 k : (0 <= k)%Z -> IZR (2 ^ k) = bpow radix2 k.
Proof. intros H. change (2 ^ k)%Z with (Zpower radix2 k). apply IZR_Zpower. exact H. Qed.

Lemma le_sc_ok a ea b eb : le_sc a ea b eb = true -> IZR a * bpow radix2 ea <= IZR b * bpow radix2 eb.
Proof.
  unfold le_sc. intros H. apply Z.leb_le in H. set (t := Z.min ea eb) in *.
  apply IZR_le in H. rewrite !mult_IZR, !IZR_pow2 in H by lia.
  replace (bpow radix2 ea) with (bpow radix2 (ea - t) * bpow radix2 t) by (rewrite <- bpow_plus; f_equal; ring).
  replace (bpow radix2 eb) with (bpow radix2 (eb - t) * bpow radix2 t) by (rewrite <- bpow_plus; f_equal; ring).
  rewrite <- !Rmult_assoc. apply Rmult_le_compat_r; [apply bpow_ge_0 | exact H].
Qed.

(** [ln(m·2^e)], [m > 0], enclosed on [2^-M]'s grid. *)
Definition ln_me (m e M : Z) (n : nat) : Z * Z :=
  if (0 <=? e)%Z then ln_bounds (m * 2 ^ e) 1 M n else ln_bounds m (2 ^ (- e)) M n.

Lemma ln_me_ok m e M n : (0 < m)%Z -> (0 <= M)%Z ->
  IZR (fst (ln_me m e M n)) * bpow radix2 (- M) <= ln (IZR m * bpow radix2 e)
    <= IZR (snd (ln_me m e M n)) * bpow radix2 (- M).
Proof.
  intros Hm HM. unfold ln_me. destruct (Z.leb_spec 0 e) as [E | E].
  - replace (IZR m * bpow radix2 e) with (IZR (m * 2 ^ e) / IZR 1)
      by (rewrite mult_IZR, IZR_pow2 by exact E; unfold Rdiv; rewrite Rinv_1; ring).
    apply ln_bounds_ok; [apply Z.mul_pos_pos; [exact Hm | apply Z.pow_pos_nonneg; lia] | lia | exact HM].
  - replace (IZR m * bpow radix2 e) with (IZR m / IZR (2 ^ (- e))).
    + apply ln_bounds_ok; [exact Hm | apply Z.pow_pos_nonneg; lia | exact HM].
    + rewrite IZR_pow2 by lia. rewrite bpow_opp. unfold Rdiv. rewrite Rinv_involutive by (apply Rgt_not_eq, bpow_gt_0). reflexivity.
Qed.

(** An enclosure [[L, U]] of [v] bounds [|v|] by [max(|L|, |U|)]. *)
Definition absup (p : Z * Z) : Z := Z.max (Z.abs (fst p)) (Z.abs (snd p)).

Lemma absup_ok p M v : IZR (fst p) * bpow radix2 (- M) <= v <= IZR (snd p) * bpow radix2 (- M) ->
  Rabs v <= IZR (absup p) * bpow radix2 (- M).
Proof.
  intros [H1 H2]. unfold absup. pose proof (bpow_gt_0 radix2 (- M)) as P.
  assert (A1 : IZR (Z.abs (fst p)) <= IZR (Z.max (Z.abs (fst p)) (Z.abs (snd p)))) by (apply IZR_le; lia).
  assert (A2 : IZR (Z.abs (snd p)) <= IZR (Z.max (Z.abs (fst p)) (Z.abs (snd p)))) by (apply IZR_le; lia).
  rewrite <- !Rabs_Zabs in A1, A2.
  apply Rabs_le. split.
  - pose proof (Rabs_le_inv _ _ (Rle_refl (Rabs (IZR (fst p))))) as [Q _]. nra.
  - pose proof (Rabs_le_inv _ _ (Rle_refl (Rabs (IZR (snd p))))) as [_ Q]. nra.
Qed.

Fixpoint all2 {A C} (f : A -> C -> bool) (l1 : list A) (l2 : list C) : bool :=
  match l1, l2 with
  | a :: t, c :: u => f a c && all2 f t u
  | [], [] => true
  | _, _ => false
  end.

Lemma all2_nth {A C} (f : A -> C -> bool) l1 l2 d1 d2 i :
  all2 f l1 l2 = true -> (i < length l1)%nat -> f (nth i l1 d1) (nth i l2 d2) = true.
Proof.
  revert l2 i. induction l1 as [|a t IH]; intros l2 i H Hi; [simpl in Hi; lia | ].
  destruct l2 as [|c u]; [discriminate | ]. simpl in H. apply andb_true_iff in H as [H1 H2].
  destruct i as [|i]; [exact H1 | ]. cbn [nth]. apply IH; [exact H2 | simpl in Hi; lia].
Qed.

Lemma all2_length {A C} (f : A -> C -> bool) l1 l2 : all2 f l1 l2 = true -> length l1 = length l2.
Proof.
  revert l2. induction l1 as [|a t IH]; intros [|c u] H; try discriminate; [reflexivity | ].
  simpl in H. apply andb_true_iff in H as [_ H]. simpl. f_equal. apply IH, H.
Qed.

(** * Relative errors *)

(** [q·2^qe] within [2^-127] relatively of a [t > 0] enclosed by
    [[A, U]·2^-M]: [q·2^qe <= (1 + 2^-127)·A·2^-M] and
    [(1 − 2^-127)·U·2^-M <= q·2^qe]. *)
Definition rel_mag (A U M q qe : Z) : bool :=
  (0 <? A)%Z && le_sc q (qe + 127) ((2 ^ 127 + 1) * A) (- M) && le_sc ((2 ^ 127 - 1) * U) (- M) q (qe + 127).

Lemma rel_mag_ok A U M q qe t : rel_mag A U M q qe = true ->
  IZR A * bpow radix2 (- M) <= t <= IZR U * bpow radix2 (- M) ->
  0 < t /\ Rabs (IZR q * bpow radix2 qe - t) <= / 2 ^ 127 * t.
Proof.
  unfold rel_mag. intros H [H1 H2]. apply andb_true_iff in H as [H H4]. apply andb_true_iff in H as [H0 H3].
  apply Z.ltb_lt in H0. apply le_sc_ok in H3. apply le_sc_ok in H4.
  assert (U127 : bpow radix2 127 = 2 ^ 127)
    by (change 127%Z with (Z.of_nat 127); rewrite bpow_powerRZ, <- pow_powerRZ; reflexivity).
  assert (Pt : 0 < t) by (pose proof (bpow_gt_0 radix2 (- M)); apply IZR_lt in H0; nra).
  split; [exact Pt | ].
  rewrite bpow_plus, U127 in H3, H4. rewrite mult_IZR, plus_IZR, IZR_pow2 in H3 by lia.
  rewrite mult_IZR, minus_IZR, IZR_pow2 in H4 by lia. rewrite U127 in H3, H4.
  assert (P : 0 < 2 ^ 127) by (apply pow_lt; lra).
  set (v := IZR q * bpow radix2 qe) in *.
  assert (H3' : v * 2 ^ 127 <= (2 ^ 127 + 1) * IZR A * bpow radix2 (- M)) by (unfold v; lra).
  assert (H4' : (2 ^ 127 - 1) * IZR U * bpow radix2 (- M) <= v * 2 ^ 127) by (unfold v; lra).
  pose proof (bpow_gt_0 radix2 (- M)) as PM. apply IZR_lt in H0.
  assert (V1 : v * 2 ^ 127 <= (2 ^ 127 + 1) * t) by nra.
  assert (V2 : (2 ^ 127 - 1) * t <= v * 2 ^ 127) by nra.
  assert (E : / 2 ^ 127 * t * 2 ^ 127 = t) by (field; lra).
  assert (Fin : Rabs (v - t) * 2 ^ 127 <= / 2 ^ 127 * t * 2 ^ 127).
  { rewrite E.
    destruct (Rle_dec v t); [rewrite Rabs_left1 by lra | rewrite Rabs_pos_eq by lra]; nra. }
  apply Rmult_le_reg_r with (2 ^ 127); [exact P | exact Fin].
Qed.

(** * [−ln R[i]] *)

Definition c_M : Z := 150.

Definition q_entry (rb : Z) (x : bool * Z * Z) : bool :=
  let '(ng, qm, qe) := x in
  match dec rb with
  | Some (m, e) =>
      if (m =? 2 ^ 52)%Z && (e =? -52)%Z then (qm =? 0)%Z
      else
        (0 <? m)%Z && (2 ^ 127 <=? qm)%Z && (qm <? 2 ^ 128)%Z &&
        let '(L, U) := ln_me m e c_M 32 in
        if (0 <? L)%Z then ng && rel_mag L U c_M qm qe
        else negb ng && rel_mag (- U) (- L) c_M qm qe
  | None => false
  end.

Lemma q_check : all2 q_entry ln_r_bits ln_neg_ln_r_q = true.
Proof. vm_compute. reflexivity. Qed.

Theorem neg_ln_r_q_ok i : (i < 128)%nat ->
  let '(ng, qm, qe) := nth i ln_neg_ln_r_q (false, 0%Z, 0%Z) in
  (B (ln_r i) = 1 /\ qm = 0%Z) \/
  (B (ln_r i) <> 1 /\ (2 ^ 127 <= qm < 2 ^ 128)%Z /\
   Rabs (F2R (Float radix2 (if ng then - qm else qm) qe) - - ln (B (ln_r i))) <= / 2 ^ 127 * Rabs (ln (B (ln_r i)))).
Proof.
  intros Hi. pose proof (all2_nth _ _ _ 0%Z (false, 0%Z, 0%Z) i q_check ltac:(exact Hi)) as C.
  unfold ln_r. destruct (nth i ln_neg_ln_r_q (false, 0%Z, 0%Z)) as [[ng qm] qe].
  set (rb := nth i ln_r_bits 0%Z) in *. unfold q_entry in C.
  destruct (dec rb) as [[m e] | ] eqn:D; [ | discriminate].
  destruct (dec_ok _ _ _ D) as [_ V]. rewrite V.
  destruct ((m =? 2 ^ 52)%Z && (e =? -52)%Z) eqn:One.
  { left. apply andb_true_iff in One as [O1 O2]. apply Z.eqb_eq in O1. apply Z.eqb_eq in O2. subst.
    split; [rewrite IZR_pow2 by lia; rewrite <- bpow_plus; reflexivity | apply Z.eqb_eq, C]. }
  apply andb_true_iff in C as [C Rest]. apply andb_true_iff in C as [C Q2]. apply andb_true_iff in C as [M0 Q1].
  apply Z.ltb_lt in M0. apply Z.leb_le in Q1. apply Z.ltb_lt in Q2.
  pose proof (ln_me_ok m e c_M 32 M0 ltac:(unfold c_M; lia)) as LB.
  destruct (ln_me m e c_M 32) as [L U]. cbn [fst snd] in LB.
  right.
  assert (F2 : forall t : R, F2R (Float radix2 (if ng then - qm else qm) qe) =
                         (if ng then -1 else 1) * (IZR qm * bpow radix2 qe)).
  { intros _. unfold F2R. cbn [Fnum Fexp]. destruct ng; [rewrite opp_IZR | ]; ring. }
  rewrite (F2 0). revert Rest.
  destruct (Z.ltb_spec 0 L) as [Lp | Ln]; intros Rest.
  - apply andb_true_iff in Rest as [Ng Rm]. subst ng.
    destruct (rel_mag_ok _ _ _ _ _ _ Rm LB) as [Pt Hr].
    split; [let N := fresh in assert (N : ln (IZR m * bpow radix2 e) <> 0) by lra; intros E; apply N; rewrite E; apply ln_1 | ]. split; [lia | ].
    rewrite (Rabs_pos_eq (ln (IZR m * bpow radix2 e))) by lra. replace (-1 * (IZR qm * bpow radix2 qe) - - ln (IZR m * bpow radix2 e))
      with (- (IZR qm * bpow radix2 qe - ln (IZR m * bpow radix2 e))) by ring. rewrite Rabs_Ropp. exact Hr.
  - apply andb_true_iff in Rest as [Ng Rm]. destruct ng; [discriminate | ].
    assert (LB' : IZR (- U) * bpow radix2 (- c_M) <= - ln (IZR m * bpow radix2 e) <= IZR (- L) * bpow radix2 (- c_M))
      by (rewrite !opp_IZR; lra).
    destruct (rel_mag_ok _ _ _ _ _ _ Rm LB') as [Pt Hr].
    split; [let N := fresh in assert (N : ln (IZR m * bpow radix2 e) <> 0) by lra; intros E; apply N; rewrite E; apply ln_1 | ]. split; [lia | ].
    rewrite (Rabs_left (ln (IZR m * bpow radix2 e))) by lra. rewrite Rmult_1_l. exact Hr.
Qed.

(** * [ln 2] *)

Lemma ln2_check : rel_mag (fst (ln_bounds 2 1 c_M 50)) (snd (ln_bounds 2 1 c_M 50)) c_M ln_ln2_q (-128)
  && (2 ^ 127 <=? ln_ln2_q)%Z && (ln_ln2_q <? 2 ^ 128)%Z = true.
Proof. vm_compute. reflexivity. Qed.

Theorem ln2_q_ok : (2 ^ 127 <= ln_ln2_q < 2 ^ 128)%Z /\
  Rabs (IZR ln_ln2_q * bpow radix2 (-128) - ln 2) <= / 2 ^ 127 * ln 2.
Proof.
  pose proof ln2_check as C. apply andb_true_iff in C as [C Q2]. apply andb_true_iff in C as [Rm Q1].
  apply Z.leb_le in Q1. apply Z.ltb_lt in Q2. split; [lia | ].
  pose proof (ln_bounds_ok 2 1 c_M 50 ltac:(lia) ltac:(lia) ltac:(unfold c_M; lia)) as LB.
  replace (IZR 2 / IZR 1) with 2 in LB by (simpl; field).
  exact (proj2 (rel_mag_ok _ _ _ _ _ _ Rm LB)).
Qed.

(** * [1/k] *)

Definition recip_entry (k : Z) (x : Z * Z) : bool :=
  let '(m, e) := x in
  (2 ^ 127 <=? m)%Z && (m <? 2 ^ 128)%Z && (e <=? -127)%Z &&
  (Z.abs (m * k - 2 ^ (- e)) <=? 2 ^ (- e - 127))%Z.

Fixpoint recip_from (k : Z) (l : list (Z * Z)) : bool :=
  match l with [] => true | x :: t => recip_entry k x && recip_from (k + 1) t end.

Lemma recip_check : recip_from 1 ln_recips = true /\ length ln_recips = 18%nat.
Proof. split; [vm_compute; reflexivity | reflexivity]. Qed.

Lemma recip_from_nth k0 l i : recip_from k0 l = true -> (i < length l)%nat ->
  recip_entry (k0 + Z.of_nat i) (nth i l (0%Z, 0%Z)) = true.
Proof.
  revert k0 i. induction l as [|x t IH]; intros k0 i H Hi; [simpl in Hi; lia | ].
  simpl in H. apply andb_true_iff in H as [H1 H2]. destruct i as [|i].
  - rewrite Z.add_0_r. exact H1.
  - cbn [nth]. replace (k0 + Z.of_nat (S i))%Z with (k0 + 1 + Z.of_nat i)%Z by lia. apply IH; [exact H2 | simpl in Hi; lia].
Qed.

Theorem recip_q_ok k : (1 <= k <= 18)%nat ->
  let '(m, e) := nth (k - 1) ln_recips (0%Z, 0%Z) in
  (2 ^ 127 <= m < 2 ^ 128)%Z /\ (e <= -127)%Z /\ Rabs (IZR m * bpow radix2 e * INR k - 1) <= / 2 ^ 127.
Proof.
  intros Hk. destruct recip_check as [C Len].
  pose proof (recip_from_nth 1 _ (k - 1) C ltac:(rewrite Len; lia)) as E.
  replace (1 + Z.of_nat (k - 1))%Z with (Z.of_nat k) in E by lia.
  destruct (nth (k - 1) ln_recips (0%Z, 0%Z)) as [m e]. unfold recip_entry in E.
  repeat rewrite andb_true_iff in E. destruct E as [[[Q1 Q2] Q3] Q4].
  apply Z.leb_le in Q1. apply Z.ltb_lt in Q2. apply Z.leb_le in Q3. apply Z.leb_le in Q4.
  split; [lia | ]. split; [exact Q3 | ].
  apply IZR_le in Q4. rewrite <- Rabs_Zabs, minus_IZR, mult_IZR, !IZR_pow2 in Q4 by lia.
  rewrite INR_IZR_INZ.
  replace (IZR m * bpow radix2 e * IZR (Z.of_nat k) - 1)
    with ((IZR m * IZR (Z.of_nat k) - bpow radix2 (- e)) * bpow radix2 e)
    by (rewrite Rmult_minus_distr_r, <- bpow_plus; replace (- e + e)%Z with 0%Z by ring; simpl; ring).
  rewrite Rabs_mult, (Rabs_pos_eq (bpow radix2 e)) by apply bpow_ge_0.
  replace (/ 2 ^ 127) with (bpow radix2 (- e - 127) * bpow radix2 e)
    by (rewrite <- bpow_plus; replace (- e - 127 + e)%Z with (- Z.of_nat 127)%Z by lia;
        rewrite bpow_opp, bpow_powerRZ, <- pow_powerRZ; reflexivity).
  apply Rmult_le_compat_r; [apply bpow_ge_0 | exact Q4].
Qed.

(** * The case ratios

    Interval [i], widened: [y] in [[lo', hi']] with [lo' = ln_lo i − 2^-52],
    [hi' = ln_hi i + 2^-52], both [a·2^-52]. *)

Definition r_M : Z := 64.
Definition r_n : nat := 14.

Definition lo_num (i : Z) : Z := if (i <? 53)%Z then (128 + i) * 2 ^ 45 - 1 else (128 + i) * 2 ^ 44 - 1.
Definition hi_num (i : Z) : Z := if (i <? 53)%Z then (129 + i) * 2 ^ 45 + 1 else (129 + i) * 2 ^ 44 + 1.

(** The bounds the certificates take ([up] of generators/ln_certificates.py):
    case B's [k3]; case C's [k2] and [k3]; and [|E·ln 2| / |ln x|] for the
    additions' errors, below [2.0225]. *)
Definition k3b : R := 533 / 1024.
Definition k2c : R := 514 / 512.
Definition k3c : R := 752 / 65536.
Definition k1c : R := 2071 / 1024.

Definition ratio_entry (i : Z) (rb : Z) : bool :=
  match dec rb with
  | Some (rm, re) =>
      let ll := ln_me (lo_num i) (-52) r_M r_n in
      let lh := ln_me (hi_num i) (-52) r_M r_n in
      let lr := ln_me rm re r_M r_n in
      let lzl := ln_me (lo_num i * rm) (re - 52) r_M r_n in
      let lzh := ln_me (hi_num i * rm) (re - 52) r_M r_n in
      let l2 := ln_bounds 2 1 r_M r_n in
      let num := Z.max (absup lzl) (absup lzh) in
      let c := Z.max (absup ll) (absup lh) in
      let d := (fst l2 - c)%Z in
      (0 <? rm)%Z && (0 <? d)%Z &&
      (512 * absup lr <=? 514 * d)%Z && (65536 * num <=? 752 * d)%Z && (1024 * snd l2 <=? 2071 * d)%Z &&
      ((rm =? 2 ^ 52)%Z && (re =? -52)%Z ||
       (if (0 <? fst ll)%Z then (1024 * num <=? 533 * fst ll)%Z
        else (snd lh <? 0)%Z && (1024 * num <=? 533 * (- snd lh))%Z))
  | None => false
  end.

Fixpoint ratio_from (i : Z) (l : list Z) : bool :=
  match l with [] => true | rb :: t => ratio_entry i rb && ratio_from (i + 1) t end.

Lemma ratio_check : ratio_from 0 ln_r_bits = true /\ length ln_r_bits = 128%nat.
Proof. split; [vm_compute; reflexivity | reflexivity]. Qed.

Lemma ratio_from_nth i0 l i : ratio_from i0 l = true -> (i < length l)%nat ->
  ratio_entry (i0 + Z.of_nat i) (nth i l 0%Z) = true.
Proof.
  revert i0 i. induction l as [|x t IH]; intros i0 i H Hi; [simpl in Hi; lia | ].
  simpl in H. apply andb_true_iff in H as [H1 H2]. destruct i as [|i].
  - rewrite Z.add_0_r. exact H1.
  - cbn [nth]. replace (i0 + Z.of_nat (S i))%Z with (i0 + 1 + Z.of_nat i)%Z by lia. apply IH; [exact H2 | simpl in Hi; lia].
Qed.

Lemma ln_le_mono a b : 0 < a -> a <= b -> ln a <= ln b.
Proof. intros Ha Hab. destruct (Rle_lt_or_eq_dec _ _ Hab) as [L | E]; [apply Rlt_le, ln_increasing; lra | rewrite E; lra]. Qed.

Lemma lo_num_val i : (i < 128)%nat -> IZR (lo_num (Z.of_nat i)) * bpow radix2 (-52) = ln_lo i - / 2 ^ 52.
Proof.
  intros Hi. unfold lo_num, ln_lo. rewrite INR_IZR_INZ.
  change (bpow radix2 (-52)) with (/ 4503599627370496). replace (/ 2 ^ 52) with (/ 4503599627370496) by (simpl; lra).
  destruct (Nat.ltb_spec i 53) as [S | S].
  - replace (Z.of_nat i <? 53)%Z with true by (symmetry; apply Z.ltb_lt; lia).
    rewrite minus_IZR, mult_IZR, plus_IZR. change (IZR (2 ^ 45)) with 35184372088832. lra.
  - replace (Z.of_nat i <? 53)%Z with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite minus_IZR, mult_IZR, plus_IZR. change (IZR (2 ^ 44)) with 17592186044416. lra.
Qed.

Lemma hi_num_val i : (i < 128)%nat -> IZR (hi_num (Z.of_nat i)) * bpow radix2 (-52) = ln_hi i + / 2 ^ 52.
Proof.
  intros Hi. unfold hi_num, ln_hi. rewrite S_INR, INR_IZR_INZ.
  change (bpow radix2 (-52)) with (/ 4503599627370496). replace (/ 2 ^ 52) with (/ 4503599627370496) by (simpl; lra).
  destruct (Nat.ltb_spec i 53) as [S | S].
  - replace (Z.of_nat i <? 53)%Z with true by (symmetry; apply Z.ltb_lt; lia).
    rewrite plus_IZR, mult_IZR, plus_IZR. change (IZR (2 ^ 45)) with 35184372088832. lra.
  - replace (Z.of_nat i <? 53)%Z with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite plus_IZR, mult_IZR, plus_IZR. change (IZR (2 ^ 44)) with 17592186044416. lra.
Qed.

(** Over interval [i], widened by [2^-52]: case B's ratio (where
    [R[i] ≠ 1]), and for every [E ≠ 0] case C's, with
    [ln x = E·ln 2 + ln y] and [ln(1 + z) = ln(y·R[i])]. *)
Theorem ratios_ok i y : (i < 128)%nat -> ln_lo i - / 2 ^ 52 <= y <= ln_hi i + / 2 ^ 52 ->
  0 < y /\ 0 < B (ln_r i) /\
  (B (ln_r i) <> 1 -> Rabs (ln (y * B (ln_r i))) <= k3b * Rabs (ln y)) /\
  forall E : Z, E <> 0%Z ->
    let lx := IZR E * ln 2 + ln y in
    Rabs (ln (B (ln_r i))) <= k2c * Rabs lx /\ Rabs (ln (y * B (ln_r i))) <= k3c * Rabs lx /\
    Rabs (IZR E * ln 2) <= k1c * Rabs lx.
Proof.
  intros Hi Hy. destruct ratio_check as [C Len].
  pose proof (ratio_from_nth 0 _ i C ltac:(rewrite Len; exact Hi)) as E. rewrite Z.add_0_l in E.
  unfold ln_r. set (rb := nth i ln_r_bits 0%Z) in *. unfold ratio_entry in E.
  destruct (dec rb) as [[rm re] | ] eqn:D; [ | discriminate].
  destruct (dec_ok _ _ _ D) as [_ V]. rewrite V.
  set (ii := Z.of_nat i) in *.
  pose proof (lo_num_val i Hi) as LoV. pose proof (hi_num_val i Hi) as HiV. fold ii in LoV, HiV.
  repeat rewrite andb_true_iff in E. destruct E as [[[[[Rp Dp] K2] K3] K1] KB].
  apply Z.ltb_lt in Rp. apply Z.ltb_lt in Dp. apply Z.leb_le in K2. apply Z.leb_le in K3. apply Z.leb_le in K1.
  assert (HM : (0 <= r_M)%Z) by (unfold r_M; lia).
  assert (Lo0 : (0 < lo_num ii)%Z) by (unfold lo_num; destruct (ii <? 53)%Z; lia).
  assert (Hi0 : (0 < hi_num ii)%Z) by (unfold hi_num; destruct (ii <? 53)%Z; lia).
  pose proof (ln_me_ok _ (-52) r_M r_n Lo0 HM) as Bll. pose proof (ln_me_ok _ (-52) r_M r_n Hi0 HM) as Blh.
  pose proof (ln_me_ok _ re r_M r_n Rp HM) as Blr.
  pose proof (ln_me_ok (lo_num ii * rm) (re - 52) r_M r_n ltac:(nia) HM) as Bzl.
  pose proof (ln_me_ok (hi_num ii * rm) (re - 52) r_M r_n ltac:(nia) HM) as Bzh.
  pose proof (ln_bounds_ok 2 1 r_M r_n ltac:(lia) ltac:(lia) HM) as B2.
  replace (IZR 2 / IZR 1) with 2 in B2 by (simpl; field).
  rewrite LoV in Bll. rewrite HiV in Blh.
  assert (Ezl : IZR (lo_num ii * rm) * bpow radix2 (re - 52) = (ln_lo i - / 2 ^ 52) * (IZR rm * bpow radix2 re))
    by (rewrite <- LoV, mult_IZR; replace (re - 52)%Z with (-52 + re)%Z by ring; rewrite bpow_plus; ring).
  assert (Ezh : IZR (hi_num ii * rm) * bpow radix2 (re - 52) = (ln_hi i + / 2 ^ 52) * (IZR rm * bpow radix2 re))
    by (rewrite <- HiV, mult_IZR; replace (re - 52)%Z with (-52 + re)%Z by ring; rewrite bpow_plus; ring).
  rewrite Ezl in Bzl. rewrite Ezh in Bzh.
  set (R0 := IZR rm * bpow radix2 re) in *.
  set (s := bpow radix2 (- r_M)) in *. assert (Ps : 0 < s) by apply bpow_gt_0.
  assert (Pr : 0 < R0) by (unfold R0; apply Rmult_lt_0_compat; [apply IZR_lt; exact Rp | apply bpow_gt_0]).
  assert (Py : 0 < y) by (rewrite <- LoV in Hy; pose proof (bpow_gt_0 radix2 (-52));
                          assert (0 < IZR (lo_num ii)) by (apply IZR_lt; exact Lo0); nra).
  assert (Plo : 0 < ln_lo i - / 2 ^ 52) by (rewrite <- LoV; pose proof (bpow_gt_0 radix2 (-52));
                          assert (0 < IZR (lo_num ii)) by (apply IZR_lt; exact Lo0); nra).
  (* monotonicity *)
  assert (My : ln (ln_lo i - / 2 ^ 52) <= ln y <= ln (ln_hi i + / 2 ^ 52))
    by (split; apply ln_le_mono; lra).
  assert (Mz : ln ((ln_lo i - / 2 ^ 52) * R0) <= ln (y * R0) <= ln ((ln_hi i + / 2 ^ 52) * R0))
    by (split; apply ln_le_mono; nra).
  set (lzl := ln_me (lo_num ii * rm) (re - 52) r_M r_n) in *.
  set (lzh := ln_me (hi_num ii * rm) (re - 52) r_M r_n) in *.
  set (ll := ln_me (lo_num ii) (-52) r_M r_n) in *. set (lh := ln_me (hi_num ii) (-52) r_M r_n) in *.
  set (lr := ln_me rm re r_M r_n) in *. set (l2 := ln_bounds 2 1 r_M r_n) in *.
  set (num := Z.max (absup lzl) (absup lzh)) in *.
  assert (Num : Rabs (ln (y * R0)) <= IZR num * s).
  { pose proof (absup_ok lzl r_M _ Bzl) as A1. pose proof (absup_ok lzh r_M _ Bzh) as A2. fold s in A1, A2.
    assert (IZR (absup lzl) <= IZR num) by (apply IZR_le; unfold num; lia).
    assert (IZR (absup lzh) <= IZR num) by (apply IZR_le; unfold num; lia).
    apply Rabs_le. apply Rabs_le_inv in A1. apply Rabs_le_inv in A2. split; nra. }
  set (c := Z.max (absup ll) (absup lh)) in *.
  assert (Cy : Rabs (ln y) <= IZR c * s).
  { pose proof (absup_ok ll r_M _ Bll) as A1. pose proof (absup_ok lh r_M _ Blh) as A2. fold s in A1, A2.
    assert (IZR (absup ll) <= IZR c) by (apply IZR_le; unfold c; lia).
    assert (IZR (absup lh) <= IZR c) by (apply IZR_le; unfold c; lia).
    apply Rabs_le. apply Rabs_le_inv in A1. apply Rabs_le_inv in A2. split; nra. }
  assert (Lr : Rabs (ln R0) <= IZR (absup lr) * s) by exact (absup_ok lr r_M _ Blr).
  set (d := (fst l2 - c)%Z) in *.
  assert (Dr : 0 < IZR d) by (apply IZR_lt; exact Dp).
  assert (L2lo : IZR (fst l2) * s <= ln 2) by lra.
  assert (L2hi : ln 2 <= IZR (snd l2) * s) by lra.
  split; [exact Py | ]. split; [exact Pr | ]. split.
  - (* case B *)
    intros R1.
    apply orb_true_iff in KB. destruct KB as [One | KB].
    { exfalso. apply andb_true_iff in One as [O1 O2]. apply Z.eqb_eq in O1. apply Z.eqb_eq in O2.
      apply R1. unfold R0. rewrite O1, O2, IZR_pow2 by lia. rewrite <- bpow_plus. reflexivity. }
    revert KB. destruct (Z.ltb_spec 0 (fst ll)) as [Lp | Ln]; intros KB.
    + apply Z.leb_le in KB. apply IZR_le in KB. rewrite !mult_IZR in KB.
      assert (Ly : IZR (fst ll) * s <= ln y) by lra.
      assert (0 < IZR (fst ll)) by (apply IZR_lt; exact Lp).
      rewrite (Rabs_pos_eq (ln y)) by nra. unfold k3b.
      apply Rle_trans with (IZR num * s); [exact Num | ]. nra.
    + apply andb_true_iff in KB as [Hn KB]. apply Z.ltb_lt in Hn. apply Z.leb_le in KB. apply IZR_le in KB.
      rewrite !mult_IZR, opp_IZR in KB.
      assert (Ly : ln y <= IZR (snd lh) * s) by lra.
      assert (IZR (snd lh) < 0) by (apply IZR_lt; exact Hn).
      rewrite (Rabs_left (ln y)) by nra. unfold k3b.
      apply Rle_trans with (IZR num * s); [exact Num | ]. nra.
  - (* case C *)
    intros Ez Hz0. cbv zeta. set (lx := IZR Ez * ln 2 + ln y).
    assert (Ea : 1 <= Rabs (IZR Ez)) by (rewrite <- abs_IZR; apply IZR_le; lia).
    assert (P2 : 0 < ln 2) by (rewrite <- ln_1; apply ln_increasing; lra).
    assert (Ae : Rabs (IZR Ez * ln 2) = Rabs (IZR Ez) * ln 2) by (rewrite Rabs_mult, (Rabs_pos_eq (ln 2)) by lra; reflexivity).
    assert (Dd : IZR d * s <= ln 2 - IZR c * s) by (unfold d; rewrite minus_IZR; lra).
    assert (Lx : Rabs (IZR Ez) * ln 2 - Rabs (ln y) <= Rabs lx).
    { unfold lx. rewrite <- Ae. pose proof (Rabs_triang_inv (IZR Ez * ln 2) (- ln y)) as T.
      rewrite Rabs_Ropp in T. replace (IZR Ez * ln 2 - - ln y) with (IZR Ez * ln 2 + ln y) in T by ring. lra. }
    assert (Lx1 : IZR d * s <= Rabs lx) by nra.
    apply IZR_le in K2. apply IZR_le in K3. apply IZR_le in K1. rewrite !mult_IZR in K2, K3, K1.
    split; [ | split].
    + unfold k2c. apply Rle_trans with (IZR (absup lr) * s); [exact Lr | ]. nra.
    + unfold k3c. apply Rle_trans with (IZR num * s); [exact Num | ]. nra.
    + unfold k1c. rewrite Ae.
      (* |E| ln 2 <= k1c (|E| ln 2 - |ln y|), as ln 2 <= k1c (ln 2 - c s) and |E| >= 1 *)
      assert (H1 : ln 2 <= 2071 / 1024 * (ln 2 - IZR c * s)) by nra.
      assert (Hc : 0 <= IZR c * s) by (pose proof (Rabs_pos (ln y)); lra).
      assert (Rabs (IZR Ez) * ln 2 <= 2071 / 1024 * (Rabs (IZR Ez) * ln 2 - IZR c * s)) by nra.
      nra.
Qed.

(** * [R[i] = 1] only at [i = 0] and [i = 127] *)

(** [a·2^ea < b·2^eb], exactly. *)
Definition lt_sc (a ea b eb : Z) : bool :=
  let t := Z.min ea eb in (a * 2 ^ (ea - t) <? b * 2 ^ (eb - t))%Z.

Lemma lt_sc_ok a ea b eb : lt_sc a ea b eb = true -> IZR a * bpow radix2 ea < IZR b * bpow radix2 eb.
Proof.
  unfold lt_sc. intros H. apply Z.ltb_lt in H. set (t := Z.min ea eb) in *.
  apply IZR_lt in H. rewrite !mult_IZR, !IZR_pow2 in H by lia.
  replace (bpow radix2 ea) with (bpow radix2 (ea - t) * bpow radix2 t) by (rewrite <- bpow_plus; f_equal; ring).
  replace (bpow radix2 eb) with (bpow radix2 (eb - t) * bpow radix2 t) by (rewrite <- bpow_plus; f_equal; ring).
  rewrite <- !Rmult_assoc. apply Rmult_lt_compat_r; [apply bpow_gt_0 | exact H].
Qed.

Definition one_entry (i : Z) (rb : Z) : bool :=
  (i =? 0)%Z || (i =? 127)%Z ||
  match dec rb with Some (m, e) => lt_sc m e 1 0 || lt_sc 1 0 m e | None => false end.

Fixpoint one_from (i : Z) (l : list Z) : bool :=
  match l with [] => true | rb :: t => one_entry i rb && one_from (i + 1) t end.

Lemma one_check : one_from 0 ln_r_bits = true.
Proof. vm_compute. reflexivity. Qed.

Lemma one_from_nth i0 l i : one_from i0 l = true -> (i < length l)%nat ->
  one_entry (i0 + Z.of_nat i) (nth i l 0%Z) = true.
Proof.
  revert i0 i. induction l as [|x t IH]; intros i0 i H Hi; [simpl in Hi; lia | ].
  simpl in H. apply andb_true_iff in H as [H1 H2]. destruct i as [|i].
  - rewrite Z.add_0_r. exact H1.
  - cbn [nth]. replace (i0 + Z.of_nat (S i))%Z with (i0 + 1 + Z.of_nat i)%Z by lia. apply IH; [exact H2 | simpl in Hi; lia].
Qed.

Theorem ln_r_one i : (i < 128)%nat -> B (ln_r i) = 1 -> i = 0%nat \/ i = 127%nat.
Proof.
  intros Hi R1. pose proof (one_from_nth 0 _ i one_check ltac:(rewrite (proj2 ratio_check); exact Hi)) as E.
  rewrite Z.add_0_l in E. unfold one_entry in E. unfold ln_r in R1.
  apply orb_true_iff in E as [E | E]; [apply orb_true_iff in E as [E | E]; apply Z.eqb_eq in E; lia | ].
  destruct (dec (nth i ln_r_bits 0%Z)) as [[m e] | ] eqn:D; [ | discriminate].
  destruct (dec_ok _ _ _ D) as [_ V]. rewrite V in R1. exfalso.
  apply orb_true_iff in E as [E | E]; apply lt_sc_ok in E; simpl in E; rewrite R1 in E; lra.
Qed.
