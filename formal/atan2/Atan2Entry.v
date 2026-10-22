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

Lemma angle_real_pos a b neg : 0 < a -> 0 < b -> 0 < angle_real a b neg.
Proof.
  intros Ha Hb. unfold angle_real. pose proof pi_gt_3 as P3.
  pose proof (atan_bound (a / b)) as [A1 A2]. pose proof (atan_bound (b / a)) as [B1 B2].
  assert (Pab : 0 < a / b) by (apply Rdiv_lt_0_compat; lra). assert (Pba : 0 < b / a) by (apply Rdiv_lt_0_compat; lra).
  pose proof (atan_pos _ Pab) as C1. pose proof (atan_pos _ Pba) as C2.
  destruct (Rle_dec a b); destruct neg; lra.
Qed.

Lemma sign_finish Z yv xv neg a b : 0 < a -> 0 < b -> Z = angle_real a b neg ->
  (yv = a \/ yv = - a) -> ((xv = b /\ neg = false) \/ (xv = - b /\ neg = true)) ->
  exists sgn : R, (sgn = 1 \/ sgn = -1) /\ atan2R yv xv = sgn * Z /\ ((yv = a) -> sgn = 1) /\ ((yv = - a) -> sgn = -1).
Proof.
  intros Ha Hb HZ Hy Hx. subst Z.
  destruct Hy as [-> | ->]; destruct Hx as [[-> ->] | [-> ->]].
  - exists 1. refine (conj (or_introl eq_refl) (conj _ (conj (fun _ => eq_refl) (fun H => _)))); [rewrite atan2R_q1 by assumption; ring | lra].
  - exists 1. refine (conj (or_introl eq_refl) (conj _ (conj (fun _ => eq_refl) (fun H => _)))); [rewrite atan2R_q2 by assumption; ring | lra].
  - exists (-1). refine (conj (or_intror eq_refl) (conj _ (conj (fun H => _) (fun _ => eq_refl)))); [rewrite atan2R_q3 by assumption; ring | lra].
  - exists (-1). refine (conj (or_intror eq_refl) (conj _ (conj (fun H => _) (fun _ => eq_refl)))); [rewrite atan2R_q4 by assumption; ring | lra].
Qed.

Definition atan2_certified_pair (y x : f64) : Prop :=
  angle_certified (aw (Z.land (bits_of_b64 y) (asin_sign_bit - 1))) (aw (Z.land (bits_of_b64 x) (asin_sign_bit - 1)))
    (negb (Z.land (bits_of_b64 x) asin_sign_bit =? 0)%Z).

Theorem atan2_entry_finite y x : finite y -> finite x -> B y <> 0 -> B x <> 0 ->
  finite (atan2_entry y x) /\
  Rabs (B (atan2_entry y x) - atan2R (B y) (B x)) <= (/ 2 + bpow radix2 (-137)) * ulpF (B (atan2_entry y x)) /\
  (atan2_certified_pair y x -> B (atan2_entry y x) = rndF (atan2R (B y) (B x))) /\
  (Stable190 (Rabs (atan2R (B y) (B x))) -> B (atan2_entry y x) = rndF (atan2R (B y) (B x))).
Proof.
  intros Fy Fx Ny Nx.
  assert (Hny : asin_is_nan y = false) by (destruct y; first [reflexivity | discriminate Fy]).
  assert (Hnx : asin_is_nan x = false) by (destruct x; first [reflexivity | discriminate Fx]).
  destruct (abs_split y Fy) as [ny [Ry [Hay [Fay [Nay Hsy]]]]].
  destruct (abs_split x Fx) as [nx [Rx [Hax [Fax [Nax Hsx]]]]].
  set (a := b64_of_bits ny) in *. set (b := b64_of_bits nx) in *.
  assert (Pa : 0 < B a) by (destruct Hsy as [[_ E] | [_ E]]; [lra | lra]).
  assert (Pb : 0 < B b) by (destruct Hsx as [[_ E] | [_ E]]; [lra | lra]).
  assert (Hneg : (negb (Z.land (bits_of_b64 x) asin_sign_bit =? 0)%Z = true) <-> (exists m, bits_of_b64 x = (m + 2 ^ 63)%Z /\ (0 <= m < 2 ^ 63)%Z)).
  { destruct Hsx as [[Hb _] | [Hb _]]; rewrite Hb.
    - unfold asin_sign_bit. rewrite (proj1 (land_sign nx Rx)). simpl. split; [discriminate | intros [m [Hm Hr]]; lia].
    - unfold asin_sign_bit. rewrite (proj2 (land_sign nx Rx)). simpl. split; [intros _; exists nx; split; [reflexivity | exact Rx] | reflexivity]. }
  destruct (cls_pos a Fay Pa) as [E0a Eia]. destruct (cls_pos b Fax Pb) as [E0b Eib].
  unfold atan2_entry. rewrite Hny, Hnx. rewrite Hay, Hax. cbv zeta. rewrite E0a, E0b, Eia, Eib. cbv iota.
  set (neg := negb (Z.land (bits_of_b64 x) asin_sign_bit =? 0)%Z) in *.
  destruct (angle_ok a b neg Fay Fax Pa Pb) as [FM [NM [Ub [Cert St]]]].
  set (M := atan2_angle a b neg) in *.
  destruct (ws_nonneg M y FM NM) as [Fw [Wp Wn]].
  pose proof (angle_real_pos (B a) (B b) neg Pa Pb) as Zpos.
  set (Z := angle_real (B a) (B b) neg) in *.
  assert (Hcp : atan2_certified_pair y x = angle_certified a b neg) by (unfold atan2_certified_pair; rewrite Hay, Hax; reflexivity).
  split; [exact Fw | ].
  assert (Hq : forall sgn : R, (sgn = 1 \/ sgn = -1) -> B (asin_with_sign M y) = sgn * B M -> atan2R (B y) (B x) = sgn * Z ->
    Rabs (B (asin_with_sign M y) - atan2R (B y) (B x)) <= (/ 2 + bpow radix2 (-137)) * ulpF (B (asin_with_sign M y)) /\
    (angle_certified a b neg -> B (asin_with_sign M y) = rndF (atan2R (B y) (B x))) /\
    (Stable190 (Rabs (atan2R (B y) (B x))) -> B (asin_with_sign M y) = rndF (atan2R (B y) (B x)))).
  { intros sgn Hs Hw Hsp. rewrite Hw, Hsp.
    destruct Hs as [-> | ->].
    - rewrite !Rmult_1_l. split; [exact Ub | split; [exact Cert | ]]. rewrite Rabs_pos_eq by lra. exact St.
    - replace (-1 * B M - -1 * Z) with (- (B M - Z)) by ring. rewrite Rabs_Ropp.
      replace (-1 * B M) with (- B M) by ring. rewrite ulp_opp.
      split; [exact Ub | split].
      + intros C. replace (-1 * Z) with (- Z) by ring. rewrite round_NE_opp_ne. rewrite (Cert C). reflexivity.
      + intros S. replace (-1 * Z) with (- Z) by ring. rewrite round_NE_opp_ne. rewrite St; [reflexivity | ].
        replace (-1 * Z) with (- Z) in S by ring. rewrite Rabs_Ropp, Rabs_pos_eq in S by lra. exact S. }
  assert (Hy : B y = B a \/ B y = - B a) by (destruct Hsy as [[_ E] | [_ E]]; [left; exact E | right; exact E]).
  assert (Hx : (B x = B b /\ neg = false) \/ (B x = - B b /\ neg = true)).
  { destruct Hsx as [[Hb' E] | [Hb' E]].
    - left. split; [exact E | ]. destruct neg eqn:En; [exfalso | reflexivity].
      destruct (proj1 Hneg eq_refl) as [m [Hm Hr]]. lia.
    - right. split; [exact E | ]. destruct neg eqn:En; [reflexivity | exfalso].
      assert (Ht : false = true) by (apply (proj2 Hneg); exists nx; split; [exact Hb' | exact Rx]). discriminate Ht. }
  destruct (sign_finish Z (B y) (B x) neg (B a) (B b) Pa Pb eq_refl Hy Hx) as [sgn [Hs [Hsp [Hpos' Hneg']]]].
  destruct Hsy as [[Hby By] | [Hby By]].
  - assert (Hs1 : sgn = 1) by (apply Hpos'; exact By).
    assert (Hw : B (asin_with_sign M y) = sgn * B M) by (rewrite Hs1, Rmult_1_l; apply Wp; lia).
    destruct (Hq sgn Hs Hw Hsp) as [U [C S']]. rewrite Hcp. exact (conj U (conj C S')).
  - assert (Hs1 : sgn = -1) by (apply Hneg'; exact By).
    assert (Hw : B (asin_with_sign M y) = sgn * B M) by (rewrite Hs1; replace (-1 * B M) with (- B M) by ring; apply Wn; lia).
    destruct (Hq sgn Hs Hw Hsp) as [U [C S']]. rewrite Hcp. exact (conj U (conj C S')).
Qed.

(** The magnitude of the public entry, by the classes of the two magnitude words. *)
Definition entry_mag (a b : f64) (neg : bool) : f64 :=
  if eq0 a then (if neg then atan2_pi else asin_zero)
  else if eq0 b then atan2_half_pi_f64
  else if eqinf a then
    (if eqinf b then (if neg then atan2_three_quarter_pi else atan2_quarter_pi) else atan2_half_pi_f64)
  else if eqinf b then (if neg then atan2_pi else asin_zero)
  else atan2_angle a b neg.

Lemma entry_eval y x : asin_is_nan y = false -> asin_is_nan x = false ->
  atan2_entry y x = asin_with_sign (entry_mag (aw (Z.land (bits_of_b64 y) (asin_sign_bit - 1))) (aw (Z.land (bits_of_b64 x) (asin_sign_bit - 1)))
    (negb (Z.land (bits_of_b64 x) asin_sign_bit =? 0)%Z)) y.
Proof. intros Hy Hx. unfold atan2_entry. rewrite Hy, Hx. reflexivity. Qed.

Lemma abs_zero_a sy : aw (Z.land (bits_of_b64 (B754_zero 53 1024 sy)) (asin_sign_bit - 1)) = asin_zero.
Proof. destruct sy; vm_compute; reflexivity. Qed.

Lemma abs_inf_a sy : aw (Z.land (bits_of_b64 (B754_infinity 53 1024 sy)) (asin_sign_bit - 1)) = B754_infinity 53 1024 false.
Proof. destruct sy; vm_compute; reflexivity. Qed.

(** The sign test of [x]: through the sign bit. *)
Lemma neg_of x : (bits_of_b64 x < 2 ^ 63)%Z -> negb (Z.land (bits_of_b64 x) asin_sign_bit =? 0)%Z = false.
Proof.
  intros H. destruct (land_sign_any (bits_of_b64 x) (bits_range x)) as [[_ E] | [G _]]; [rewrite E; reflexivity | lia].
Qed.

Lemma neg_of' x : (2 ^ 63 <= bits_of_b64 x)%Z -> negb (Z.land (bits_of_b64 x) asin_sign_bit =? 0)%Z = true.
Proof.
  intros H. destruct (land_sign_any (bits_of_b64 x) (bits_range x)) as [[L _] | [_ [m' [_ [_ E]]]]]; [lia | rewrite E; reflexivity].
Qed.

(** The classes of the magnitude word. *)
Lemma entry_mag_zero_a b neg : eq0 asin_zero = true -> entry_mag asin_zero b neg = (if neg then atan2_pi else asin_zero).
Proof. intros H. unfold entry_mag. rewrite H. reflexivity. Qed.


Lemma fin_zero_inv x : finite x -> B x = 0 -> exists s, x = B754_zero 53 1024 s.
Proof.
  intros F Z0. destruct x as [s | s | s pl H | s m e H]; try discriminate F.
  - exists s. reflexivity.
  - exfalso. cbn [B2R] in Z0. apply eq_0_F2R in Z0. destruct s; cbn in Z0; lia.
Qed.

(** The result carries its magnitude [c], signed by [y]. *)
Definition Table (y x c : f64) : Prop :=
  finite (atan2_entry y x) /\ ((bits_of_b64 y < 2 ^ 63)%Z -> B (atan2_entry y x) = B c) /\ ((2 ^ 63 <= bits_of_b64 y)%Z -> B (atan2_entry y x) = - B c).

Lemma table_from_mag y x c : asin_is_nan y = false -> asin_is_nan x = false ->
  entry_mag (aw (Z.land (bits_of_b64 y) (asin_sign_bit - 1))) (aw (Z.land (bits_of_b64 x) (asin_sign_bit - 1)))
    (negb (Z.land (bits_of_b64 x) asin_sign_bit =? 0)%Z) = c ->
  finite c -> 0 <= B c -> Table y x c.
Proof.
  intros Hy Hx Hm Fc Nc. unfold Table. rewrite (entry_eval y x Hy Hx), Hm.
  destruct (ws_nonneg c y Fc Nc) as [F [P N]]. exact (conj F (conj P N)).
Qed.

Lemma pi_nn : finite atan2_pi /\ 0 <= B atan2_pi.
Proof. destruct atan2_pi_val as [F V]. split; [exact F | rewrite V; bpow_num; interval with (i_prec 60)]. Qed.

Lemma half_pi_nn : finite atan2_half_pi_f64 /\ 0 <= B atan2_half_pi_f64.
Proof. destruct atan2_half_pi_val as [F V]. split; [exact F | rewrite V; bpow_num; interval with (i_prec 60)]. Qed.

Lemma quarter_pi_nn : finite atan2_quarter_pi /\ 0 <= B atan2_quarter_pi.
Proof. destruct atan2_quarter_pi_val as [F V]. split; [exact F | rewrite V; bpow_num; interval with (i_prec 60)]. Qed.

Lemma three_quarter_pi_nn : finite atan2_three_quarter_pi /\ 0 <= B atan2_three_quarter_pi.
Proof. destruct atan2_three_quarter_pi_val as [F V]. split; [exact F | rewrite V; bpow_num; interval with (i_prec 60)]. Qed.

Lemma zero_nn : finite asin_zero /\ 0 <= B asin_zero.
Proof. destruct zero_val as [Z F]. split; [exact F | rewrite Z; lra]. Qed.

Lemma nan_false_zero sy : asin_is_nan (B754_zero 53 1024 sy) = false.
Proof. reflexivity. Qed.
Lemma nan_false_inf sy : asin_is_nan (B754_infinity 53 1024 sy) = false.
Proof. reflexivity. Qed.
Lemma nan_false_fin x : finite x -> asin_is_nan x = false.
Proof. intros F. destruct x; first [reflexivity | discriminate F]. Qed.

(** y = +-0. *)
Theorem table_y_zero sy x : asin_is_nan x = false ->
  ((bits_of_b64 x < 2 ^ 63)%Z -> Table (B754_zero 53 1024 sy) x asin_zero) /\ ((2 ^ 63 <= bits_of_b64 x)%Z -> Table (B754_zero 53 1024 sy) x atan2_pi).
Proof.
  intros Hx. split; intros H; apply table_from_mag; try apply nan_false_zero; try exact Hx.
  - rewrite abs_zero_a, (neg_of x H). unfold entry_mag. rewrite zero_val_a. reflexivity.
  - exact (proj1 zero_nn).
  - exact (proj2 zero_nn).
  - rewrite abs_zero_a, (neg_of' x H). unfold entry_mag. rewrite zero_val_a. reflexivity.
  - exact (proj1 pi_nn).
  - exact (proj2 pi_nn).
Qed.

Lemma neg_inf sx : negb (Z.land (bits_of_b64 (B754_infinity 53 1024 sx)) asin_sign_bit =? 0)%Z = sx.
Proof. destruct sx; vm_compute; reflexivity. Qed.

(** Finite nonzero [y] against [x = +-0]: [+-pi/2]. *)
Theorem table_x_zero y sx : finite y -> B y <> 0 -> Table y (B754_zero 53 1024 sx) atan2_half_pi_f64.
Proof.
  intros Fy Ny. destruct (abs_split y Fy) as [ny [Ry [Hay [Fay [Nay Hsy]]]]].
  assert (Pa : 0 < B (b64_of_bits ny)) by (destruct Hsy as [[_ E] | [_ E]]; lra).
  destruct (cls_pos _ Fay Pa) as [E0a Eia].
  apply table_from_mag; try apply nan_false_zero; try (apply nan_false_fin; exact Fy).
  - rewrite Hay, abs_zero_a. unfold entry_mag. rewrite E0a, zero_val_a. reflexivity.
  - exact (proj1 half_pi_nn).
  - exact (proj2 half_pi_nn).
Qed.

(** Finite nonzero [y] against [x = +-inf]: [+0] or [+-pi]. *)
Theorem table_x_inf y sx : finite y -> B y <> 0 -> Table y (B754_infinity 53 1024 sx) (if sx then atan2_pi else asin_zero).
Proof.
  intros Fy Ny. destruct (abs_split y Fy) as [ny [Ry [Hay [Fay [Nay Hsy]]]]].
  assert (Pa : 0 < B (b64_of_bits ny)) by (destruct Hsy as [[_ E] | [_ E]]; lra).
  destruct (cls_pos _ Fay Pa) as [E0a Eia].
  apply table_from_mag; try apply nan_false_inf; try (apply nan_false_fin; exact Fy).
  - rewrite Hay, abs_inf_a, neg_inf. unfold entry_mag. rewrite E0a, (proj1 (cls_inf false)), Eia, (proj2 (cls_inf false)).
    destruct sx; reflexivity.
  - destruct sx; [exact (proj1 pi_nn) | exact (proj1 zero_nn)].
  - destruct sx; [exact (proj2 pi_nn) | exact (proj2 zero_nn)].
Qed.

(** [y = +-inf] against a finite [x]: [+-pi/2]. *)
Theorem table_y_inf_x_finite sy x : finite x -> Table (B754_infinity 53 1024 sy) x atan2_half_pi_f64.
Proof.
  intros Fx. destruct (Req_dec (B x) 0) as [Z0 | NZ].
  - destruct (fin_zero_inv x Fx Z0) as [sx ->].
    apply table_from_mag; try apply nan_false_inf; try apply nan_false_zero.
    + rewrite abs_inf_a, abs_zero_a. unfold entry_mag. rewrite (proj1 (cls_inf false)), zero_val_a. reflexivity.
    + exact (proj1 half_pi_nn).
    + exact (proj2 half_pi_nn).
  - destruct (abs_split x Fx) as [nx [Rx [Hax [Fax [Nax Hsx]]]]].
    assert (Pb : 0 < B (b64_of_bits nx)) by (destruct Hsx as [[_ E] | [_ E]]; lra).
    destruct (cls_pos _ Fax Pb) as [E0b Eib].
    apply table_from_mag; try apply nan_false_inf; try (apply nan_false_fin; exact Fx).
    + rewrite abs_inf_a, Hax. unfold entry_mag. rewrite (proj1 (cls_inf false)), E0b, (proj2 (cls_inf false)), Eib. reflexivity.
    + exact (proj1 half_pi_nn).
    + exact (proj2 half_pi_nn).
Qed.

(** [y = +-inf] against [x = +-inf]: [+-pi/4] or [+-3 pi/4]. *)
Theorem table_y_inf_x_inf sy sx : Table (B754_infinity 53 1024 sy) (B754_infinity 53 1024 sx) (if sx then atan2_three_quarter_pi else atan2_quarter_pi).
Proof.
  apply table_from_mag; try apply nan_false_inf.
  - rewrite abs_inf_a, neg_inf. unfold entry_mag. rewrite (proj1 (cls_inf false)), (proj2 (cls_inf false)). destruct sx; reflexivity.
  - destruct sx; [exact (proj1 three_quarter_pi_nn) | exact (proj1 quarter_pi_nn)].
  - destruct sx; [exact (proj2 three_quarter_pi_nn) | exact (proj2 quarter_pi_nn)].
Qed.

Theorem entry_nan y x : (asin_is_nan y = true \/ asin_is_nan x = true) -> asin_is_nan (atan2_entry y x) = true.
Proof. intros [H | H]; unfold atan2_entry; rewrite H; [reflexivity | destruct (asin_is_nan y); reflexivity]. Qed.

(** The zero numerator against a nonnegative-signed [x]: the zero itself. *)
Theorem entry_y_zero_x_pos sy x : asin_is_nan x = false -> (bits_of_b64 x < 2 ^ 63)%Z ->
  atan2_entry (B754_zero 53 1024 sy) x = B754_zero 53 1024 sy.
Proof.
  intros Hx H. rewrite (entry_eval _ x (nan_false_zero sy) Hx), abs_zero_a, (neg_of x H). unfold entry_mag. rewrite zero_val_a.
  destruct sy; vm_compute; reflexivity.
Qed.

Lemma fin_nonzero s m e H : B (B754_finite 53 1024 s m e H) <> 0.
Proof.
  intros Z0. cbn [B2R] in Z0. apply eq_0_F2R in Z0. destruct s; cbn in Z0; lia.
Qed.

(** Every pair of binary64 values falls in one of the cases proved above. *)
Theorem pair_classes y x :
  asin_is_nan y = true \/ asin_is_nan x = true \/
  (exists sy, y = B754_zero 53 1024 sy) \/
  (exists sy sx, y = B754_infinity 53 1024 sy /\ x = B754_infinity 53 1024 sx) \/
  (exists sy, y = B754_infinity 53 1024 sy /\ finite x) \/
  (finite y /\ B y <> 0 /\ exists sx, x = B754_zero 53 1024 sx) \/
  (finite y /\ B y <> 0 /\ exists sx, x = B754_infinity 53 1024 sx) \/
  (finite y /\ B y <> 0 /\ finite x /\ B x <> 0).
Proof.
  destruct y as [sy | sy | sy ply Hy | sy my ey Hy]; destruct x as [sx | sx | sx plx Hx | sx mx ex Hx].
  - right; right; left. exists sy. reflexivity.
  - right; right; left. exists sy. reflexivity.
  - right; left. reflexivity.
  - right; right; left. exists sy. reflexivity.
  - right; right; right; right; left. exists sy. split; reflexivity.
  - right; right; right; left. exists sy, sx. split; reflexivity.
  - right; left. reflexivity.
  - right; right; right; right; left. exists sy. split; reflexivity.
  - left. reflexivity.
  - left. reflexivity.
  - left. reflexivity.
  - left. reflexivity.
  - right; right; right; right; right; left. split; [reflexivity | split; [apply fin_nonzero | exists sx; reflexivity]].
  - right; right; right; right; right; right; left. split; [reflexivity | split; [apply fin_nonzero | exists sx; reflexivity]].
  - right; left. reflexivity.
  - right; right; right; right; right; right; right. split; [reflexivity | split; [apply fin_nonzero | split; [reflexivity | apply fin_nonzero]]].
Qed.

(** The published worst-case search (CORE-MATH's [atan2] list, docs/atan2.md): no binary64 midpoint
    within [2^-190] (relatively) of the angle of a pair the rounding test and the tiny path leave
    to the accurate path. Under it, every finite nonzero pair is correctly rounded. *)
Definition CoreMathAtan2 : Prop :=
  forall y x, finite y -> finite x -> B y <> 0 -> B x <> 0 -> ~ atan2_certified_pair y x ->
    Stable190 (Rabs (atan2R (B y) (B x))).

Corollary atan2_entry_correct y x : CoreMathAtan2 -> finite y -> finite x -> B y <> 0 -> B x <> 0 ->
  finite (atan2_entry y x) /\ B (atan2_entry y x) = rndF (atan2R (B y) (B x)).
Proof.
  intros CM Fy Fx Ny Nx. destruct (atan2_entry_finite y x Fy Fx Ny Nx) as [F [_ [C S]]].
  refine (conj F _). destruct (Classical_Prop.classic (atan2_certified_pair y x)) as [H | H].
  - exact (C H).
  - exact (S (CM y x Fy Fx Ny Nx H)).
Qed.
