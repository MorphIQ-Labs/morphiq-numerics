(** Rounding a Q value to binary64 (Q128::to_f64 and Q256::to_f64): the kept
    bits [m / 2^s] and the round-up rule (remainder above half, or at half
    with an odd kept part) are round-to-nearest-even of [m / 2^s]. *)

From Coq Require Import Bool ZArith Reals Lia Lra Psatz.
From Flocq Require Import Core.

Open Scope Z_scope.

Definition round_up (m s : Z) : bool :=
  let kept := m / 2 ^ s in
  let rem := m mod 2 ^ s in
  let half := 2 ^ (s - 1) in
  (half <? rem) || ((rem =? half) && Z.odd kept).

Lemma IZR_pow2' k : 0 <= k -> IZR (2 ^ k) = bpow radix2 k.
Proof. intros H. destruct k; [reflexivity | reflexivity | lia]. Qed.

Theorem znearest_shift (m s : Z) : 0 <= m -> 1 <= s ->
  Znearest (fun n => negb (Z.even n)) (IZR m * bpow radix2 (- s))
  = m / 2 ^ s + (if round_up m s then 1 else 0).
Proof.
  intros Hm Hs.
  pose proof (Z.pow_pos_nonneg 2 s ltac:(lia) ltac:(lia)) as K.
  pose proof (Z.div_mod m (2 ^ s) ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound m (2 ^ s) K) as M.
  set (k := m / 2 ^ s) in *. set (r := m mod 2 ^ s) in *.
  assert (H2 : 2 ^ s = 2 * 2 ^ (s - 1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
  assert (Hh : 0 < 2 ^ (s - 1)) by (apply Z.pow_pos_nonneg; lia).
  set (h := 2 ^ (s - 1)) in *.
  assert (Hpos : (0 < bpow radix2 s)%R) by apply bpow_gt_0.
  assert (Ex : (IZR m * bpow radix2 (- s) = IZR k + IZR r / IZR (2 ^ s))%R).
  { rewrite bpow_opp, IZR_pow2' by lia. rewrite D, plus_IZR, mult_IZR, IZR_pow2' by lia.
    field. lra. }
  assert (Ps : (0 < IZR (2 ^ s))%R) by (apply IZR_lt; lia).
  assert (Fr : (0 <= IZR r / IZR (2 ^ s) < 1)%R).
  { split; [unfold Rdiv; apply Rmult_le_pos; [apply IZR_le; lia | left; apply Rinv_0_lt_compat; exact Ps] | ].
    apply Rmult_lt_reg_r with (IZR (2 ^ s)); [exact Ps | ].
    unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra. rewrite Rmult_1_l. apply IZR_lt; lia. }
  rewrite Ex.
  assert (Fl : Zfloor (IZR k + IZR r / IZR (2 ^ s)) = k) by (apply Zfloor_imp; rewrite plus_IZR; lra).
  unfold Znearest. rewrite Fl.
  replace (IZR k + IZR r / IZR (2 ^ s) - IZR k)%R with (IZR r / IZR (2 ^ s))%R by ring.
  assert (Half : forall c, Rcompare (IZR r / IZR (2 ^ s)) (/ 2) = c -> Rcompare (IZR r) (IZR h) = c).
  { intros c <-.
    replace (/ 2)%R with (IZR h * / IZR (2 ^ s))%R by (rewrite H2, mult_IZR; field; apply not_0_IZR; lia).
    unfold Rdiv. rewrite Rcompare_mult_r; [reflexivity | apply Rinv_0_lt_compat; exact Ps]. }
  assert (Ceil : r <> 0 -> Zceil (IZR k + IZR r / IZR (2 ^ s)) = k + 1).
  { intros Hr. apply Zceil_imp. rewrite minus_IZR, plus_IZR.
    assert (0 < IZR r / IZR (2 ^ s))%R by (apply Rdiv_lt_0_compat; [apply IZR_lt; lia | exact Ps]). lra. }
  unfold round_up. fold k r h.
  destruct (Rcompare_spec (IZR r / IZR (2 ^ s)) (/ 2)) as [L | E | G].
  - assert (r < h) by (apply lt_IZR; apply Rcompare_Lt_inv; apply Half; reflexivity).
    replace (h <? r) with false by (symmetry; apply Z.ltb_ge; lia).
    replace (r =? h) with false by (symmetry; apply Z.eqb_neq; lia). simpl. ring.
  - assert (r = h) by (apply eq_IZR; apply Rcompare_Eq_inv; apply Half; reflexivity).
    replace (h <? r) with false by (symmetry; apply Z.ltb_ge; lia).
    replace (r =? h) with true by (symmetry; apply Z.eqb_eq; lia). simpl.
    rewrite Ceil by lia.
    rewrite <- Z.negb_even. destruct (Z.even k); simpl; ring.
  - assert (h < r) by (apply lt_IZR; apply Rcompare_Gt_inv; apply Half; reflexivity).
    replace (h <? r) with true by (symmetry; apply Z.ltb_lt; lia). simpl.
    rewrite Ceil by lia. reflexivity.
Qed.

From Flocq Require Import IEEE754.Binary.

Notation fexp64 := (FLT_exp (3 - 1024 - 53) 53).
#[local] Instance prec53 : Prec_gt_0 53 := eq_refl.
Notation rnd64 := (round radix2 fexp64 (round_mode mode_NE)).
Definition bn (m e : Z) (s : bool) := binary_normalize 53 1024 eq_refl eq_refl mode_NE m e s.

Definition signed (n : bool) (m : Z) := if n then - m else m.

(** to_f64 of either Q type, on its fields: zero; infinity above the largest
    binade; otherwise the kept bits and the round-up rule at the result's
    quantum, assembled ([bn] of a representable value is that value). *)
Definition to_f64_spec (p : Z) (n : bool) (m e : Z) : binary_float 53 1024 :=
  if m =? 0 then B754_zero 53 1024 n else
  let top := e + p - 1 in
  if 1023 <? top then B754_infinity 53 1024 n else
  let quantum := if -1022 <=? top then top - 52 else -1074 in
  let shift := quantum - e in
  let sig := m / 2 ^ shift + (if round_up m shift then 1 else 0) in
  bn (signed n sig) quantum n.

Definition sign_of (x : R) (s : bool) :=
  match Rcompare x 0 with Eq => s | Lt => true | Gt => false end.

Lemma sign_of_signed n k e : 0 <= k -> sign_of (F2R (Float radix2 (signed n k) e)) n = n.
Proof.
  intros Hk. unfold sign_of, signed. destruct (Z.eq_dec k 0) as [-> | Hz].
  - destruct n; simpl; rewrite F2R_0, Rcompare_Eq; reflexivity.
  - destruct n.
    + rewrite Rcompare_Lt; [reflexivity | apply F2R_lt_0; simpl; lia].
    + rewrite Rcompare_Gt; [reflexivity | apply F2R_gt_0; simpl; lia].
Qed.

(** [bn] depends only on the rounded value and the sign it gives. *)
Lemma bn_ext m1 e1 m2 e2 s :
  rnd64 (F2R (Float radix2 m1 e1)) = rnd64 (F2R (Float radix2 m2 e2)) ->
  sign_of (F2R (Float radix2 m1 e1)) s = sign_of (F2R (Float radix2 m2 e2)) s ->
  bn m1 e1 s = bn m2 e2 s.
Proof.
  intros Hr Hs. unfold bn.
  pose proof (binary_normalize_correct 53 1024 eq_refl eq_refl mode_NE m1 e1 s) as C1.
  pose proof (binary_normalize_correct 53 1024 eq_refl eq_refl mode_NE m2 e2 s) as C2.
  rewrite Hr in C1.
  destruct (Rlt_bool_spec (Rabs (rnd64 (F2R (Float radix2 m2 e2)))) (bpow radix2 1024)) as [L | L].
  - destruct C1 as [B1 [F1 S1]]. destruct C2 as [B2 [F2 S2]].
    apply B2R_Bsign_inj; [exact F1 | exact F2 | rewrite B1, B2; reflexivity | ].
    rewrite S1, S2. exact Hs.
  - apply B2FF_inj. rewrite C1, C2. f_equal.
    (* Overflow: neither value is zero, so their signs agree. *)
    assert (N : forall m e, rnd64 (F2R (Float radix2 m e)) = rnd64 (F2R (Float radix2 m2 e2)) ->
                F2R (Float radix2 m e) <> 0%R).
    { intros m e E Z. rewrite Z, round_0 in E by auto with typeclass_instances.
      rewrite <- E, Rabs_R0 in L. pose proof (bpow_gt_0 radix2 1024). lra. }
    pose proof (N m1 e1 Hr) as N1. pose proof (N m2 e2 eq_refl) as N2.
    unfold sign_of in Hs.
    destruct (Rcompare_spec (F2R (Float radix2 m1 e1)) 0) as [A | A | A];
    destruct (Rcompare_spec (F2R (Float radix2 m2 e2)) 0) as [B | B | B];
      try contradiction; try discriminate;
      try (rewrite !Rlt_bool_true by assumption; reflexivity);
      try (rewrite !Rlt_bool_false by lra; reflexivity).
Qed.

Theorem to_f64_spec_ok (p : Z) n m e : 54 <= p -> 2 ^ (p - 1) <= m < 2 ^ p ->
  to_f64_spec p n m e = bn (signed n m) e n.
Proof.
  intros Hp [M1 M2]. unfold to_f64_spec.
  replace (m =? 0) with false by (symmetry; apply Z.eqb_neq; pose proof (Z.pow_pos_nonneg 2 (p - 1)); lia).
  set (top := e + p - 1).
  set (x := F2R (Float radix2 m e)).
  assert (Xb : (bpow radix2 top <= x < bpow radix2 (top + 1))%R).
  { unfold x, F2R, top; simpl.
    replace (e + p - 1) with ((p - 1) + e) by ring. replace (p - 1 + e + 1) with (p + e) by ring.
    rewrite !bpow_plus, <- (IZR_pow2' (p - 1)), <- (IZR_pow2' p) by lia. pose proof (bpow_gt_0 radix2 e).
    split; [apply Rmult_le_compat_r | apply Rmult_lt_compat_r]; try lra; [apply IZR_le | apply IZR_lt]; lia. }
  assert (Xs : F2R (Float radix2 (signed n m) e) = if n then (- x)%R else x).
  { unfold signed, x. destruct n; [rewrite F2R_Zopp | ]; reflexivity. }
  assert (Ropp : forall y, rnd64 (- y) = (- rnd64 y)%R) by (intros; apply round_NE_opp).
  destruct (Z.ltb_spec 1023 top) as [O | O].
  - (* overflow *)
    unfold bn. pose proof (binary_normalize_correct 53 1024 eq_refl eq_refl mode_NE (signed n m) e n) as C.
    assert (Big : (bpow radix2 1024 <= Rabs (rnd64 (F2R (Float radix2 (signed n m) e))))%R).
    { rewrite Xs. assert (G : (bpow radix2 1024 <= rnd64 x)%R).
      { apply (round_ge_generic radix2 fexp64 (round_mode mode_NE) (bpow radix2 1024) x).
        - apply generic_format_FLT_bpow; [reflexivity | lia].
        - apply Rle_trans with (2 := proj1 Xb). apply bpow_le. lia. }
      destruct n; [rewrite Ropp, Rabs_Ropp | ]; rewrite Rabs_pos_eq; try lra;
        pose proof (bpow_gt_0 radix2 1024); lra. }
    rewrite Rlt_bool_false in C by lra.
    apply B2FF_inj. rewrite C. simpl. f_equal.
    rewrite Xs. pose proof (bpow_gt_0 radix2 top).
    destruct n; [rewrite Rlt_bool_true | rewrite Rlt_bool_false]; try reflexivity; lra.
  - set (quantum := if -1022 <=? top then top - 52 else -1074).
    set (shift := quantum - e).
    assert (Sh : 1 <= shift).
    { unfold shift, quantum, top. destruct (Z.leb_spec (-1022) (e + p - 1)); lia. }
    assert (Mag : mag radix2 x = top + 1 :> Z).
    { apply mag_unique. rewrite Rabs_pos_eq by (pose proof (bpow_gt_0 radix2 top); lra).
      replace (top + 1 - 1) with top by ring. exact Xb. }
    assert (Cexp : cexp radix2 fexp64 x = quantum).
    { unfold cexp. rewrite Mag. unfold FLT_exp, quantum.
      destruct (Z.leb_spec (-1022) top); lia. }
    set (sig := m / 2 ^ shift + (if round_up m shift then 1 else 0)).
    assert (Rx : rnd64 x = F2R (Float radix2 sig quantum)).
    { unfold round. rewrite Cexp. f_equal. f_equal.
      unfold scaled_mantissa. rewrite Cexp. unfold x, F2R; simpl.
      rewrite Rmult_assoc, <- bpow_plus. replace (e + - quantum) with (- shift) by (unfold shift; ring).
      apply znearest_shift; lia. }
    assert (Sg : 0 <= sig).
    { unfold sig. pose proof (Z.div_pos m (2 ^ shift) ltac:(lia) ltac:(apply Z.pow_pos_nonneg; lia)).
      destruct (round_up m shift); lia. }
    apply bn_ext.
    + rewrite Xs. assert (Fs : F2R (Float radix2 (signed n sig) quantum) = if n then (- rnd64 x)%R else rnd64 x).
      { rewrite Rx. unfold signed. destruct n; [rewrite F2R_Zopp | ]; reflexivity. }
      rewrite Fs. destruct n; rewrite ?Ropp, round_generic; auto with typeclass_instances;
        try apply generic_format_opp; apply generic_format_round; auto with typeclass_instances.
    + rewrite !sign_of_signed; [reflexivity | lia | exact Sg].
Qed.
