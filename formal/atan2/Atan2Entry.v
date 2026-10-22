(** atan2's public entry over every binary64 pair: NaN, the special-value table, the sign and
    quadrant handling, and the contract for finite nonzero operands. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 RoundingCore RoundingTest.
From Interval Require Import Tactic.
Require Import Ln1pLemmas AsinSeries AsinTables AsinKernel AsinSqrtStep AsinWithin AsinFacts AsinPath AsinCorrect AsinSmall AsinEntry
  Atan2Tables Atan2Kernel Atan2Within Atan2Approx Atan2Forms Atan2FastPath Atan2Accurate Atan2Angle Atan2Consts
  Atan2Odd Atan2Decode Atan2TinyMid Atan2Tiny Atan2Spec Atan2Angle2.
Open Scope R_scope.

Notation eq0 := (fun v => atan2_cmp_is v asin_zero Eq).
Notation eqinf := (fun v => atan2_cmp_is v atan2_infinity Eq).

Lemma inf_val : atan2_infinity = B754_infinity 53 1024 false.
Proof. vm_compute. reflexivity. Qed.

Lemma zero_val_a : atan2_cmp_is asin_zero asin_zero Eq = true.
Proof. vm_compute. reflexivity. Qed.

(** A finite positive [a] is neither zero nor infinity. *)
Lemma cls_pos a : finite a -> 0 < B a -> eq0 a = false /\ eqinf a = false.
Proof.
  intros Fa Pa. split.
  - destruct (Bool.bool_dec (eq0 a) true) as [H | H]; [exfalso | destruct (eq0 a); [contradiction | reflexivity]].
    destruct zero_val as [Z0 Fz].
    apply (proj1 (cmp_val a asin_zero Eq Fa Fz)) in H. rewrite Z0 in H. apply Rcompare_Eq_inv in H. lra.
  - unfold atan2_cmp_is, asin_cmp. rewrite inf_val. destruct a; try discriminate Fa; reflexivity.
Qed.

Lemma cls_zero a : finite a -> B a = 0 -> eq0 a = true.
Proof.
  intros Fa Z0. destruct zero_val as [Zz Fz].
  apply (proj2 (cmp_val a asin_zero Eq Fa Fz)). rewrite Zz, Z0. apply Rcompare_Eq. reflexivity.
Qed.

Lemma cls_zero_inf a : finite a -> B a = 0 -> eqinf a = false.
Proof. intros Fa Z0. unfold atan2_cmp_is, asin_cmp. rewrite inf_val. destruct a; try discriminate Fa; reflexivity. Qed.

Lemma cls_inf s : eq0 (B754_infinity 53 1024 s) = false /\ eqinf (B754_infinity 53 1024 false) = true.
Proof. split; [destruct s | ]; vm_compute; reflexivity. Qed.

Lemma land_mask2 n0 : (0 <= n0 < 2 ^ 63)%Z -> Z.land (n0 + 2 ^ 63) (asin_sign_bit - 1) = n0.
Proof.
  intros H. unfold asin_sign_bit. replace (2 ^ 63 - 1)%Z with (Z.ones 63) by reflexivity.
  rewrite Z.land_ones by lia. replace (n0 + 2 ^ 63)%Z with (n0 + 1 * 2 ^ 63)%Z by lia. rewrite Z.mod_add by lia. apply Z.mod_small; lia.
Qed.

Lemma land_sign_any m : (0 <= m < 2 ^ 64)%Z ->
  ((m < 2 ^ 63)%Z /\ Z.land m asin_sign_bit = 0%Z) \/
  ((2 ^ 63 <= m)%Z /\ exists m', m = (m' + 2 ^ 63)%Z /\ (0 <= m' < 2 ^ 63)%Z /\ Z.land m asin_sign_bit = (2 ^ 63)%Z).
Proof.
  intros H. destruct (Z_lt_ge_dec m (2 ^ 63)) as [L | G].
  - left. split; [exact L | ]. unfold asin_sign_bit. exact (proj1 (land_sign m ltac:(lia))).
  - right. split; [lia | ]. exists (m - 2 ^ 63)%Z. split; [lia | ]. split; [lia | ].
    assert (Hm : m = ((m - 2 ^ 63) + 2 ^ 63)%Z) by lia. rewrite Hm. unfold asin_sign_bit. exact (proj2 (land_sign (m - 2 ^ 63) ltac:(lia))).
Qed.

(** Applying [x]'s sign to a finite nonnegative [v]. *)
Lemma ws_nonneg v x : finite v -> 0 <= B v ->
  finite (asin_with_sign v x) /\
  ((bits_of_b64 x < 2 ^ 63)%Z -> B (asin_with_sign v x) = B v) /\
  ((2 ^ 63 <= bits_of_b64 x)%Z -> B (asin_with_sign v x) = - B v).
Proof.
  intros Fv Nv.
  destruct (abs_split v Fv) as [nv [Rv [_ [Fnv [Nnv Hs]]]]].
  assert (Hl : Z.land (bits_of_b64 v) (asin_sign_bit - 1) = nv).
  { destruct Hs as [[Hb _] | [Hb _]]; rewrite Hb; [apply land_mask; exact Rv | apply land_mask2; exact Rv]. }
  assert (Hbv : B v = B (b64_of_bits nv)).
  { destruct Hs as [[_ E] | [_ E]]; [exact E | ]. 
    assert (Hz : B (b64_of_bits nv) = 0) by lra. rewrite E, Hz. ring. }
  assert (W : asin_with_sign v x = aw (Z.lor nv (Z.land (bits_of_b64 x) asin_sign_bit))) by (unfold asin_with_sign; rewrite Hl; reflexivity).
  destruct (land_sign_any (bits_of_b64 x) (bits_range x)) as [[L1 L2] | [G1 [m' [G2 [G3 G4]]]]].
  - rewrite L2, Z.lor_0_r in W. unfold aw in W. rewrite W.
    refine (conj Fnv (conj (fun _ => _) (fun H => _))).
    + rewrite Hbv. reflexivity.
    + exfalso. lia.
  - rewrite G4, (lor_sign nv Rv) in W. unfold aw in W. rewrite W.
    destruct (bits_sign nv Rv) as [Hf Hb]. destruct (Hb Fnv) as [Hneg _].
    refine (conj ((proj2 Hf) Fnv) (conj (fun H => _) (fun _ => _))).
    + exfalso. lia.
    + rewrite Hneg, Hbv. reflexivity.
Qed.
