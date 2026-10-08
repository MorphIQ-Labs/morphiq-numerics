(** exp/mod.rs's accurate path, general case ([Reduced::accurate_value] and
    [accurate_at], docs/exp.md, section 6), transcribed on the proved Q128
    transcription (formal/q) and proved: the 128-bit result is within
    [2^-123.9] relatively of [e^x] ([accurate_ok]), so when [e^x] keeps the
    mantissa distance [LM] guarantees from every rounding breakpoint, rounding
    it once returns [RN(e^x)] ([exp_accurate_ok]). The series and the product
    with [T_j] are the certificates' theorems (ExpAccurateLevels.v); this file
    proves their hypotheses about the transcription. *)

From Coq Require Import ZArith Reals Lia Lra Psatz List.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Q Require QSpec Q128.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Mul IEEE64Eft Binary64Mul.
From Interval Require Import Tactic.
Require ExpTables ExpAccurateLevels ExpReduction.
Import ListNotations ExpTables.

Open Scope R_scope.

(** * Q128 operations, zeros included

    The contracts (formal/q) take normalized operands; the transcription also
    meets zeros, which [add] passes through and [mul] absorbs. *)

Definition NZ (x : Q128.q128) : Prop := Q128.m x = 0%Z \/ QSpec.normalized 128 (Q128.m x).

Lemma NZ_nonneg x : NZ x -> (0 <= Q128.m x)%Z.
Proof. intros [H | [H _]]; [lia | ]. pose proof (Z.pow_pos_nonneg 2 (128 - 1)). lia. Qed.

Lemma qval_zero x : Q128.m x = 0%Z -> Q128.qval x = 0.
Proof. intros H. unfold Q128.qval. rewrite H. apply Q128.val_zero. Qed.

Lemma mag_abs x : NZ x -> Q128.mag x = Rabs (Q128.qval x).
Proof. intros H. unfold Q128.mag, Q128.qval. rewrite QSpec.val_abs by (apply NZ_nonneg, H). reflexivity. Qed.

Lemma add_any a b : NZ a -> NZ b ->
  NZ (Q128.add a b) /\
  Rabs (Q128.qval (Q128.add a b) - (Q128.qval a + Q128.qval b))
    <= bpow radix2 (-126) * Rmax (Rabs (Q128.qval a)) (Rabs (Q128.qval b)).
Proof.
  intros Ha Hb. pose proof (bpow_ge_0 radix2 (-126)) as P.
  destruct (Z.eq_dec (Q128.m a) 0) as [Za | Za].
  { unfold Q128.add. rewrite Za. cbn [Z.eqb]. rewrite (qval_zero a Za), Rplus_0_l.
    split; [exact Hb | ]. rewrite Rminus_diag_eq, Rabs_R0 by reflexivity.
    apply Rmult_le_pos; [exact P | ]. apply Rle_trans with (Rabs (Q128.qval b)); [apply Rabs_pos | apply Rmax_r]. }
  destruct (Z.eq_dec (Q128.m b) 0) as [Zb | Zb].
  { unfold Q128.add. rewrite Zb. replace (Q128.m a =? 0)%Z with false by (symmetry; apply Z.eqb_neq; exact Za).
    cbn [Z.eqb]. rewrite (qval_zero b Zb), Rplus_0_r.
    split; [exact Ha | ]. rewrite Rminus_diag_eq, Rabs_R0 by reflexivity.
    apply Rmult_le_pos; [exact P | ]. apply Rle_trans with (Rabs (Q128.qval a)); [apply Rabs_pos | apply Rmax_l]. }
  destruct Ha as [Ha | Ha]; [contradiction | ]. destruct Hb as [Hb | Hb]; [contradiction | ].
  destruct (Q128.add_ok a b Ha Hb) as [N E].
  split; [exact N | ]. rewrite <- !mag_abs by (right; assumption). exact E.
Qed.

(** Multiplication truncates: the product times [(1 + t)], [t] in [[-2^-127, 0]]. *)
Lemma mul_any a b : NZ a -> NZ b ->
  NZ (Q128.mul a b) /\
  exists t, - bpow radix2 (-127) <= t <= 0 /\
    Q128.qval (Q128.mul a b) = Q128.qval a * Q128.qval b * (1 + t).
Proof.
  intros Ha Hb. pose proof (bpow_gt_0 radix2 (-127)) as P.
  destruct (Z.eq_dec (Q128.m a) 0) as [Za | Za].
  { assert (M : Q128.mul a b = Q128.zero) by (unfold Q128.mul; rewrite Za; reflexivity).
    rewrite M. split; [left; reflexivity | ]. exists 0. split; [lra | ].
    rewrite (qval_zero a Za), (qval_zero Q128.zero eq_refl). ring. }
  destruct (Z.eq_dec (Q128.m b) 0) as [Zb | Zb].
  { assert (M : Q128.mul a b = Q128.zero)
      by (unfold Q128.mul; rewrite Zb, Bool.orb_true_r; reflexivity).
    rewrite M. split; [left; reflexivity | ]. exists 0. split; [lra | ].
    rewrite (qval_zero b Zb), (qval_zero Q128.zero eq_refl). ring. }
  destruct Ha as [Ha | Ha]; [contradiction | ]. destruct Hb as [Hb | Hb]; [contradiction | ].
  destruct (Q128.mul_value a b Ha Hb) as [N V].
  assert (NZv : forall x, QSpec.normalized 128 (Q128.m x) -> Q128.qval x <> 0).
  { intros x Hx Z. assert (0 < Q128.mag x).
    { unfold Q128.mag. apply F2R_gt_0. simpl. destruct Hx. pose proof (Z.pow_pos_nonneg 2 (128 - 1)). lia. }
    rewrite mag_abs, Z, Rabs_R0 in H by (right; exact Hx). lra. }
  assert (Pab : Q128.qval a * Q128.qval b <> 0)
    by (apply Rmult_integral_contrapositive_currified; [apply NZv, Ha | apply NZv, Hb]).
  split; [right; exact N | ].
  exists ((Q128.qval (Q128.mul a b) - Q128.qval a * Q128.qval b) / (Q128.qval a * Q128.qval b)).
  split; [ | field; repeat split; apply NZv; assumption].
  destruct V as [[V1 V2] | [V1 V2]].
  - assert (0 < Q128.qval a * Q128.qval b).
    { destruct (Rtotal_order 0 (Q128.qval a * Q128.qval b)) as [H | [H | H]]; [exact H | | ].
      - exfalso. apply Pab. auto.
      - exfalso. nra. }
    split.
    + apply (Rmult_le_reg_r (Q128.qval a * Q128.qval b)); [exact H | ].
      unfold Rdiv. rewrite Rmult_assoc, Rinv_l by exact Pab. lra.
    + apply Rmult_le_reg_r with (Q128.qval a * Q128.qval b); [exact H | ].
      unfold Rdiv. rewrite Rmult_assoc, Rinv_l by exact Pab. lra.
  - assert (Q128.qval a * Q128.qval b < 0).
    { destruct (Rtotal_order 0 (Q128.qval a * Q128.qval b)) as [H | [H | H]]; [ | exfalso; apply Pab; auto | exact H].
      exfalso. nra. }
    split.
    + apply (Rmult_le_reg_r (- (Q128.qval a * Q128.qval b))); [lra | ].
      replace ((Q128.qval (Q128.mul a b) - Q128.qval a * Q128.qval b) / (Q128.qval a * Q128.qval b)
               * - (Q128.qval a * Q128.qval b)) with (- (Q128.qval (Q128.mul a b) - Q128.qval a * Q128.qval b))
        by (field; repeat split; apply NZv; assumption). lra.
    + apply (Rmult_le_reg_r (- (Q128.qval a * Q128.qval b))); [lra | ].
      replace ((Q128.qval (Q128.mul a b) - Q128.qval a * Q128.qval b) / (Q128.qval a * Q128.qval b)
               * - (Q128.qval a * Q128.qval b)) with (- (Q128.qval (Q128.mul a b) - Q128.qval a * Q128.qval b))
        by (field; repeat split; apply NZv; assumption). lra.
Qed.

(** [new] and so [from_f64] give a normalized number or zero. *)
Lemma new_nz n m0 e0 : (0 <= m0 < Q128.W)%Z -> NZ (Q128.new n m0 e0).
Proof.
  intros H. pose proof (Q128.new_ok n m0 e0 H) as N. pose proof (QSpec.norm_ok 128 ltac:(lia) m0 e0 H) as V.
  destruct (QSpec.norm 128 m0 e0) as [m' e']. injection N as N1 N2.
  destruct V as [[[_ Z] | Nm] _]; [left; rewrite N1; exact Z | right; rewrite N1; exact Nm].
Qed.

Lemma from_f64_nz bits : NZ (Q128.from_f64 bits).
Proof.
  unfold Q128.from_f64. cbv zeta.
  assert (Fm : Z.land bits (2 ^ 52 - 1) = (bits mod 2 ^ 52)%Z)
    by (rewrite <- Z.land_ones by lia; f_equal).
  assert (F0 : (0 <= Z.land bits (2 ^ 52 - 1))%Z) by (rewrite Fm; apply Z.mod_pos_bound; lia).
  assert (F1 : (Z.land bits (2 ^ 52 - 1) <= 2 ^ 52 - 1)%Z)
    by (rewrite Fm; pose proof (Z.mod_pos_bound bits (2 ^ 52)); lia).
  destruct (Z.land (Z.shiftr bits 52) 2047 =? 0)%Z; apply new_nz; unfold Q128.W.
  - lia.
  - set (f := Z.land bits (2 ^ 52 - 1)) in *.
    assert (L0 : (0 <= Z.lor f (2 ^ 52))%Z) by (apply Z.lor_nonneg; lia).
    split; [exact L0 | ].
    destruct (Z.eq_dec f 0) as [Z0 | Z0].
    + rewrite Z0, Z.lor_0_l. lia.
    + assert (Lg : (Z.log2 (Z.lor f (2 ^ 52)) < 53)%Z).
      { rewrite Z.log2_lor by lia. apply Z.max_lub_lt.
        - apply Z.le_lt_trans with (Z.log2 (2 ^ 52 - 1)); [apply Z.log2_le_mono; lia | ].
          apply Z.log2_lt_pow2; lia.
        - rewrite Z.log2_pow2 by lia. lia. }
      assert (P : (0 < Z.lor f (2 ^ 52))%Z).
      { destruct (Z.eq_dec (Z.lor f (2 ^ 52)) 0) as [E | E]; [ | lia].
        apply Z.lor_eq_0_iff in E. lia. }
      apply Z.log2_lt_pow2 in Lg; [ | exact P]. lia.
Qed.

(** A finite binary64 number's encoding converts to its value. *)
Lemma bits_exp_ok (f : binary_float 53 1024) : is_finite 53 1024 f = true ->
  ((bits_of_b64 f / 2 ^ 52) mod 2 ^ 11 <> 2047)%Z.
Proof.
  intros F. pose proof (split_bits_of_binary_float_correct 52 11 eq_refl eq_refl f) as S.
  unfold split_bits in S. change (bits_of_binary_float 52 11 f) with (bits_of_b64 f) in S.
  destruct f as [s | s | s pl Hpl | s mx ex Hb]; try discriminate F.
  - clear S. destruct s; vm_compute; discriminate.
  - pose proof Hb as Hb'. unfold bounded in Hb'. apply andb_prop in Hb'. destruct Hb' as [_ Hb'].
    apply Zle_bool_imp_le in Hb'.
    (* Project the exponent field without unfolding the encoding. *)
    apply (f_equal snd) in S. unfold split_bits_of_binary_float in S. cbv beta zeta in S.
    destruct (0 <=? Z.pos mx - 2 ^ 52)%Z; cbv beta iota delta [snd] in S; rewrite S.
    all: cbn in Hb' |- *; lia.
Qed.

Lemma from_f64_b64 (f : binary_float 53 1024) : is_finite 53 1024 f = true ->
  Q128.qval (Q128.from_f64 (bits_of_b64 f)) = B2R 53 1024 f.
Proof.
  intros F. rewrite Q128.from_f64_ok.
  - unfold b64_of_bits, bits_of_b64. f_equal. apply binary_float_of_bits_of_binary_float.
  - exact (bits_of_binary_float_range 52 11 eq_refl eq_refl f).
  - exact (bits_exp_ok f F).
Qed.

Lemma bpow_m (k : nat) : bpow radix2 (- Z.of_nat k) = / 2 ^ k.
Proof. rewrite bpow_opp, bpow_powerRZ, <- pow_powerRZ. reflexivity. Qed.

Lemma Rabs_mult_le a b A C : Rabs a <= A -> Rabs b <= C -> Rabs (a * b) <= A * C.
Proof. intros Ha Hb. rewrite Rabs_mult. apply Rmult_le_compat; try apply Rabs_pos; assumption. Qed.

(** * The series

    [Q128::ONE], the reciprocals [1/k] as [reciprocal(k)] builds them, and the
    Horner loop of [accurate_at]: after [c] levels (12, 11, ...), [hq r c] is
    [H_(13-c)], against the exact [xq r c = X_(13-c)] at the same [r]. *)

Definition q_one : Q128.q128 := Q128.Q false (2 ^ 127) (-127).

Lemma q_one_nz : NZ q_one.
Proof. right. unfold QSpec.normalized, q_one. cbn [Q128.m]. lia. Qed.

Lemma q_one_val : Q128.qval q_one = 1.
Proof.
  unfold Q128.qval, QSpec.val, q_one, F2R. cbn [Q128.neg Q128.m Q128.e Fnum Fexp].
  rewrite (QSpec.IZR_pow2 127) by lia. rewrite <- bpow_plus. reflexivity.
Qed.

Definition q_recip (i : nat) : Q128.q128 :=
  Q128.new false (fst (exp_recip i)) (- Z.of_nat (snd (exp_recip i))).

Lemma q_recip_ok i : (1 <= i <= 12)%nat ->
  NZ (q_recip i) /\ Rabs (Q128.qval (q_recip i) * INR i - 1) <= / 2 ^ 127.
Proof.
  intros Hi. destruct (exp_recip_table_ok i Hi) as [Hm Hb].
  assert (W : (0 <= fst (exp_recip i) < Q128.W)%Z) by (unfold Q128.W; lia).
  split; [apply new_nz, W | ].
  unfold q_recip. rewrite Q128.new_val by exact W. unfold QSpec.val, F2R. cbn [Fnum Fexp].
  rewrite bpow_m. exact Hb.
Qed.

Fixpoint hq (r : Q128.q128) (c : nat) : Q128.q128 :=
  match c with
  | O => q_one
  | S c' => Q128.add q_one (Q128.mul (Q128.mul r (q_recip (13 - c))) (hq r c'))
  end.

Fixpoint xq (r : R) (c : nat) : R :=
  match c with
  | O => 1
  | S c' => 1 + r / INR (13 - c) * xq r c'
  end.

(** Every partial series is within [0.003] of 1. *)
Lemma xq_range r c : Rabs r <= 0.0027078 -> (c <= 12)%nat -> Rabs (xq r c - 1) <= 0.003.
Proof.
  intros Hr. induction c as [| c IH]; intros Hc.
  - cbn [xq]. rewrite Rminus_diag_eq, Rabs_R0 by reflexivity. lra.
  - cbn [xq]. specialize (IH ltac:(lia)).
    assert (D : 1 <= INR (13 - S c)) by (replace 1 with (INR 1) by reflexivity; apply le_INR; lia).
    replace (1 + r / INR (13 - S c) * xq r c - 1) with (r * xq r c / INR (13 - S c)) by (field; lra).
    unfold Rdiv. rewrite Rabs_mult, (Rabs_pos_eq (/ INR (13 - S c))) by (apply Rlt_le, Rinv_0_lt_compat; lra).
    rewrite Rabs_mult.
    apply Rabs_le_inv in IH.
    assert (Rabs (xq r c) <= 1.003) by (apply Rabs_le; lra).
    assert (0 < / INR (13 - S c) <= 1) by (split; [apply Rinv_0_lt_compat; lra | ];
                                            rewrite <- Rinv_1; apply Rinv_le_contravar; lra).
    assert (Rabs r * Rabs (xq r c) <= 0.0027078 * 1.003)
      by (apply Rmult_le_compat; try apply Rabs_pos; lra).
    pose proof (Rabs_pos r). pose proof (Rabs_pos (xq r c)). nra.
Qed.

(** One Horner level: from [|H_(i+1) − X_(i+1)| <= Eprev] to [|H_i − X_i| <= Ecur],
    given level [i]'s certificate ([d = i]). *)
Lemma step r c d Eprev Ecur :
  NZ r -> Rabs (Q128.qval r) <= 0.0027078 -> (c < 12)%nat -> INR (13 - S c) = d ->
  (forall rr k ma Xn En mb s, Rabs rr <= 0.0027078 -> 0.99 <= Xn <= 1.01 -> Rabs En <= Eprev ->
     Rabs k <= / 2 ^ 127 -> - / 2 ^ 127 <= ma <= 0 -> - / 2 ^ 127 <= mb <= 0 -> Rabs s <= / 2 ^ 126 ->
     Rabs (1 + (rr * (1 / d * (1 + k))) * (1 + ma) * (Xn + En) * (1 + mb) + s - (1 + rr / d * Xn)) <= Ecur) ->
  NZ (hq r c) -> Rabs (Q128.qval (hq r c) - xq (Q128.qval r) c) <= Eprev -> Eprev <= / 1000 ->
  NZ (hq r (S c)) /\ Rabs (Q128.qval (hq r (S c)) - xq (Q128.qval r) (S c)) <= Ecur.
Proof.
  intros Nr Hr Hc Hd Bridge NH HE Ep.
  set (i := (13 - S c)%nat) in *.
  assert (Hi : (1 <= i <= 12)%nat) by (unfold i; lia).
  assert (D1 : 1 <= d) by (rewrite <- Hd; replace 1 with (INR 1) by reflexivity; apply le_INR; lia).
  destruct (q_recip_ok i Hi) as [Nk Vk]. rewrite Hd in Vk.
  destruct (mul_any r (q_recip i) Nr Nk) as [N1 [ma [Hma E1]]].
  destruct (mul_any _ (hq r c) N1 NH) as [N2 [mb [Hmb E2]]].
  destruct (add_any q_one _ q_one_nz N2) as [N3 E3].
  change (bpow radix2 (-127)) with (bpow radix2 (- Z.of_nat 127)) in Hma, Hmb. rewrite bpow_m in Hma, Hmb.
  assert (U127 : 0 < / 2 ^ 127 < / 1000) by (split; interval with (i_prec 64)).
  cbn [hq xq]. fold i. split; [exact N3 | ].
  set (rv := Q128.qval r) in *. set (X := xq rv c) in *. set (H := Q128.qval (hq r c)) in *.
  set (k := Q128.qval (q_recip i) * d - 1).
  assert (Ek : Q128.qval (q_recip i) = 1 / d * (1 + k)) by (unfold k; field; lra).
  set (b := Q128.qval (Q128.mul (Q128.mul r (q_recip i)) (hq r c))) in *.
  assert (Eb : b = rv * (1 / d * (1 + k)) * (1 + ma) * (X + (H - X)) * (1 + mb)).
  { rewrite E2, E1, Ek. ring. }
  pose proof (xq_range rv c Hr ltac:(lia)) as XR. fold X in XR. apply Rabs_le_inv in XR.
  assert (Hb : Rabs b <= 1).
  { rewrite Eb. apply Rabs_le_inv in HE. apply Rabs_le_inv in Hr. apply Rabs_le_inv in Vk.
    assert (0 < 1 / d <= 1) by (split; [unfold Rdiv; rewrite Rmult_1_l; apply Rinv_0_lt_compat; lra
                                       | unfold Rdiv; rewrite Rmult_1_l; rewrite <- Rinv_1; apply Rinv_le_contravar; lra]).
    assert (Kb : - / 2 ^ 127 <= k <= / 2 ^ 127) by (unfold k; lra).
    assert (A : Rabs (rv * (1 / d * (1 + k))) <= 0.003).
    { rewrite Rabs_mult. apply Rle_trans with (0.0027078 * 1.002); [ | lra].
      apply Rmult_le_compat; try apply Rabs_pos; [apply Rabs_le; lra | ].
      rewrite Rabs_mult, (Rabs_pos_eq (1 / d)) by lra. apply Rle_trans with (1 * Rabs (1 + k));
        [apply Rmult_le_compat_r; [apply Rabs_pos | lra] | rewrite Rabs_pos_eq by lra; lra]. }
    assert (B1 : Rabs (1 + ma) <= 1) by (apply Rabs_le; split; lra).
    assert (B2 : Rabs (1 + mb) <= 1) by (apply Rabs_le; split; lra).
    assert (B3 : Rabs (X + (H - X)) <= 1.005) by (apply Rabs_le; split; lra).
    apply Rle_trans with (0.003 * 1 * 1.005 * 1); [ | lra].
    apply Rabs_mult_le; [apply Rabs_mult_le; [apply Rabs_mult_le; [exact A | exact B1] | exact B3] | exact B2]. }
  set (s := Q128.qval (Q128.add q_one (Q128.mul (Q128.mul r (q_recip i)) (hq r c))) - (1 + b)).
  assert (Hs : Rabs s <= / 2 ^ 126).
  { unfold s. rewrite q_one_val in E3. fold b in E3.
    apply Rle_trans with (1 := E3). rewrite Rabs_R1, Rmax_left by lra.
    change (bpow radix2 (-126)) with (bpow radix2 (- Z.of_nat 126)). rewrite bpow_m. lra. }
  assert (HK : Rabs k <= / 2 ^ 127) by exact Vk.
  pose proof (Bridge rv k ma X (H - X) mb s Hr ltac:(lra) HE HK Hma Hmb Hs) as Br.
  replace (Q128.qval (Q128.add q_one (Q128.mul (Q128.mul r (q_recip i)) (hq r c))) - (1 + rv / INR i * X))
    with (1 + rv * (1 / d * (1 + k)) * (1 + ma) * (X + (H - X)) * (1 + mb) + s - (1 + rv / d * X))
    by (unfold s; rewrite <- Eb, <- Hd; ring).
  exact Br.
Qed.

(** The twelve levels: [H_1 = hq r 12] is within [521·2^-135] of the exact
    partial series [X_1] at the same [r]. *)
Theorem series_ok r : NZ r -> Rabs (Q128.qval r) <= 0.0027078 ->
  NZ (hq r 12) /\ Rabs (Q128.qval (hq r 12) - xq (Q128.qval r) 12) <= 521 * / 2 ^ 135.
Proof.
  intros Nr Hr.
  assert (S0 : NZ (hq r 0) /\ Rabs (Q128.qval (hq r 0) - xq (Q128.qval r) 0) <= 0).
  { cbn [hq xq]. rewrite q_one_val, Rminus_diag_eq, Rabs_R0 by reflexivity. split; [exact q_one_nz | lra]. }
  Ltac lvl Nr Hr c L Sin Sout :=
    let N := fresh "N" in let E := fresh "E" in destruct Sin as [N E];
    pose proof (step _ c _ _ _ Nr Hr ltac:(lia) ltac:(rewrite INR_IZR_INZ; reflexivity) L N E
                     ltac:(interval with (i_prec 64))) as Sout.
  lvl Nr Hr 0%nat ExpAccurateLevels.level_12 S0 S1.
  lvl Nr Hr 1%nat ExpAccurateLevels.level_11 S1 S2.
  lvl Nr Hr 2%nat ExpAccurateLevels.level_10 S2 S3.
  lvl Nr Hr 3%nat ExpAccurateLevels.level_09 S3 S4.
  lvl Nr Hr 4%nat ExpAccurateLevels.level_08 S4 S5.
  lvl Nr Hr 5%nat ExpAccurateLevels.level_07 S5 S6.
  lvl Nr Hr 6%nat ExpAccurateLevels.level_06 S6 S7.
  lvl Nr Hr 7%nat ExpAccurateLevels.level_05 S7 S8.
  lvl Nr Hr 8%nat ExpAccurateLevels.level_04 S8 S9.
  lvl Nr Hr 9%nat ExpAccurateLevels.level_03 S9 S10.
  lvl Nr Hr 10%nat ExpAccurateLevels.level_02 S10 S11.
  lvl Nr Hr 11%nat ExpAccurateLevels.level_01 S11 S12.
  exact S12.
Qed.

(** * The product with [T_j]

    [accurate_at(r, j, k)]: the series, times [T_j] as [Q128::new(false,
    T_Q128[j], -127)], scaled by [2^k]. *)

Definition q_t (j : nat) : Q128.q128 := Q128.new false (exp_tq j) (-127).

Definition accurate_at (r : Q128.q128) (j : nat) (k : Z) : Q128.q128 :=
  Q128.mul_pow2 (Q128.mul (q_t j) (hq r 12)) k.

Lemma tj_range j : (j < 128)%nat -> 1 <= exp (INR j * ln 2 / 128) <= 2.
Proof.
  intros Hj. assert (J : 0 <= INR j <= 127).
  { split; [apply pos_INR | ].
    replace 127 with (INR 127) by (rewrite INR_IZR_INZ; reflexivity). apply le_INR. lia. }
  split.
  - assert (0 <= INR j * ln 2 / 128) by (assert (0 < ln 2) by interval with (i_prec 64); nra).
    pose proof (exp_ineq1_le (INR j * ln 2 / 128)). lra.
  - interval with (i_prec 64).
Qed.

(** [Y = T_j·H_1] is within [2^-124] relatively of [2^(j/128)·X_1]. *)
Lemma y_ok r j : NZ r -> Rabs (Q128.qval r) <= 0.0027078 -> (j < 128)%nat ->
  let T := exp (INR j * ln 2 / 128) in
  let Y := Q128.mul (q_t j) (hq r 12) in
  NZ Y /\ Rabs ((Q128.qval Y - T * xq (Q128.qval r) 12) / (T * xq (Q128.qval r) 12)) <= / 2 ^ 124.
Proof.
  intros Nr Hr Hj T Y.
  destruct (series_ok r Nr Hr) as [NH EH].
  destruct (exp_tq_table_ok j Hj) as [Hm HeT]. change (exp (INR j * ln 2 / 128)) with T in HeT.
  assert (W : (0 <= exp_tq j < Q128.W)%Z) by (unfold Q128.W; lia).
  pose proof (new_nz false (exp_tq j) (-127) W) as NT.
  assert (VT : Q128.qval (q_t j) = IZR (exp_tq j) / 2 ^ 127).
  { unfold q_t. rewrite Q128.new_val by exact W. unfold QSpec.val, F2R. cbn [Fnum Fexp].
    change (-127)%Z with (- Z.of_nat 127)%Z. rewrite bpow_m. reflexivity. }
  pose proof (tj_range j Hj) as HT. fold T in HT.
  set (eT := Q128.qval (q_t j) / T - 1).
  assert (EeT : Q128.qval (q_t j) = T * (1 + eT)) by (unfold eT; field; lra).
  assert (HeT' : Rabs eT <= / 2 ^ 127).
  { replace eT with ((IZR (exp_tq j) / 2 ^ 127 - T) / T) by (unfold eT; rewrite VT; field; lra). exact HeT. }
  destruct (mul_any (q_t j) (hq r 12) NT NH) as [NY [mY [HmY EY]]].
  change (bpow radix2 (-127)) with (bpow radix2 (- Z.of_nat 127)) in HmY. rewrite bpow_m in HmY.
  split; [exact NY | ].
  set (X1 := xq (Q128.qval r) 12) in *.
  set (E1 := Q128.qval (hq r 12) - X1).
  pose proof (xq_range (Q128.qval r) 12 Hr ltac:(lia)) as XR. fold X1 in XR. apply Rabs_le_inv in XR.
  pose proof (ExpAccurateLevels.accurate_y_bound T X1 eT E1 mY HT ltac:(lra) HeT' EH HmY) as YB.
  replace (Q128.qval Y) with (T * (1 + eT) * (X1 + E1) * (1 + mY)) by (unfold Y; rewrite EY, EeT; unfold E1; ring).
  exact YB.
Qed.

(** * The reduced argument in Q128

    [Reduced::accurate_value]'s [r]: [r1 − p2 − e2 − p3 − e3 − RN(n·L4)], each
    binary64 term converted exactly and summed left to right. *)

Definition qf (t : binary_float 53 1024) : Q128.q128 := Q128.from_f64 (bits_of_b64 t).

Definition acc_r (n r1 p2 e2 : binary_float 53 1024) : Q128.q128 :=
  let '(p3, e3) := two_prod64 n exp_l3 in
  Q128.add (Q128.add (Q128.add (Q128.add (Q128.add (qf r1) (qf (fneg p2))) (qf (fneg e2)))
    (qf (fneg p3))) (qf (fneg e3))) (qf (fneg (fmul n exp_l4))).

(** One addition of a small term to a partial sum below [0.003]: the error
    grows by at most [0.003·2^-126]. *)
Lemma add_small a t (A e : R) : NZ a -> Rabs (Q128.qval a - A) <= e -> e <= / 1000000 -> Rabs A <= 0.0029 ->
  finite t -> Rabs (B t) <= / 1000000 ->
  NZ (Q128.add a (qf t)) /\ Rabs (Q128.qval (Q128.add a (qf t)) - (A + B t)) <= e + 3 / 1000 * / 2 ^ 126.
Proof.
  intros Na Ha He HA Ft Ht.
  destruct (add_any a (qf t) Na (from_f64_nz _)) as [N E].
  unfold qf in E |- *. rewrite from_f64_b64 in E by exact Ft.
  split; [exact N | ].
  change (bpow radix2 (-126)) with (bpow radix2 (- Z.of_nat 126)) in E. rewrite bpow_m in E.
  assert (M : Rmax (Rabs (Q128.qval a)) (Rabs (B t)) <= 3 / 1000).
  { apply Rmax_lub; [ | lra].
    assert (Rabs (Q128.qval a) <= Rabs A + Rabs (Q128.qval a - A)).
    { replace (Q128.qval a) with (A + (Q128.qval a - A)) at 1 by ring. apply Rabs_triang. }
    lra. }
  assert (P : 0 < / 2 ^ 126) by interval with (i_prec 64).
  replace (Q128.qval (Q128.add a (Q128.from_f64 (bits_of_b64 t))) - (A + B t))
    with ((Q128.qval (Q128.add a (Q128.from_f64 (bits_of_b64 t))) - (Q128.qval a + B t)) + (Q128.qval a - A))
    by ring.
  apply Rle_trans with (1 := Rabs_triang _ _).
  assert (/ 2 ^ 126 * Rmax (Rabs (Q128.qval a)) (Rabs (B t)) <= 3 / 1000 * / 2 ^ 126)
    by (rewrite Rmult_comm; apply Rmult_le_compat_r; lra).
  lra.
Qed.

Lemma fneg_ok t : finite t -> finite (fneg t) /\ B (fneg t) = - B t.
Proof. intros Ft. split; [unfold fneg, b64_opp; now rewrite is_finite_Bopp | apply B2R_Bopp]. Qed.

(** [r] is within [2^-131] of the exact reduced argument [x − n·L], [L = ln 2 / 128]. *)
Lemma acc_r_ok x n r1 p2 e2 k L :
  finite n -> finite r1 -> finite p2 -> finite e2 ->
  B n = IZR k -> (Z.abs k <= 137601)%Z ->
  B r1 = B x - IZR k * ExpReduction.l1v -> B p2 = rndF (IZR k * ExpReduction.l2v) ->
  B p2 + B e2 = IZR k * ExpReduction.l2v ->
  Rabs (L - (ExpReduction.l1v + ExpReduction.l2v + ExpReduction.l3v + ExpReduction.l4v)) <= / 2 ^ 206 ->
  Rabs (B x - IZR k * L) <= 0.0027076063 ->
  NZ (acc_r n r1 p2 e2) /\ Rabs (Q128.qval (acc_r n r1 p2 e2) - (B x - IZR k * L)) <= / 2 ^ 131.
Proof.
  intros Fn Fr1 Fp2 Fe2 Bn Kb Er1 Bp2 Ep HL HR.
  assert (Kr : Rabs (IZR k) <= 137601) by (rewrite <- abs_IZR; apply IZR_le; lia).
  (* the constants as rationals *)
  assert (V1 : ExpReduction.l1v = 23816355775 / 2 ^ 42).
  { unfold ExpReduction.l1v. change (-42)%Z with (- Z.of_nat 42)%Z. rewrite bpow_m. reflexivity. }
  assert (V2 : ExpReduction.l2v = - 7988006341064857 / 2 ^ 96).
  { unfold ExpReduction.l2v, F2R. cbn [Fnum Fexp]. change (-96)%Z with (- Z.of_nat 96)%Z. rewrite bpow_m.
    unfold Rdiv. ring. }
  assert (V3 : ExpReduction.l3v = 6759741496705267 / 2 ^ 151).
  { unfold ExpReduction.l3v, F2R. cbn [Fnum Fexp]. change (-151)%Z with (- Z.of_nat 151)%Z. rewrite bpow_m. reflexivity. }
  assert (V4 : ExpReduction.l4v = 4725274267454307 / 2 ^ 205).
  { unfold ExpReduction.l4v, F2R. cbn [Fnum Fexp]. change (-205)%Z with (- Z.of_nat 205)%Z. rewrite bpow_m. reflexivity. }
  pose proof exp_l3_finite as F3. pose proof exp_l4_finite as F4.
  assert (B3 : B exp_l3 = ExpReduction.l3v) by (rewrite exp_l3_val, V3; reflexivity).
  assert (B4 : B exp_l4 = ExpReduction.l4v) by (rewrite exp_l4_val, V4; reflexivity).
  (* p3 + e3 = n·L3 exactly *)
  assert (Nb : Rabs (B n) <= bpow radix2 18) by (rewrite Bn; change (bpow radix2 18) with 262144; lra).
  assert (L3b : Rabs (B exp_l3) <= bpow radix2 (-98)).
  { rewrite B3, V3. change (-98)%Z with (- Z.of_nat 98)%Z. rewrite bpow_m. rewrite Rabs_pos_eq by interval with (i_prec 64).
    interval with (i_prec 64). }
  assert (Dom : in_two_prod_domain (B n) (B exp_l3)).
  { destruct (Z.eq_dec k 0) as [K0 | K0]; [left; rewrite Bn, K0; ring | right].
    rewrite Rabs_mult, Bn, B3, V3. assert (K1 : 1 <= Rabs (IZR k)) by (rewrite <- abs_IZR; apply IZR_le; lia).
    apply Rle_trans with (1 * Rabs (6759741496705267 / 2 ^ 151)).
    - rewrite Rmult_1_l, Rabs_pos_eq by interval with (i_prec 64).
      change (-969)%Z with (- Z.of_nat 969)%Z. rewrite bpow_m. interval with (i_prec 64).
    - apply Rmult_le_compat_r; [apply Rabs_pos | exact K1]. }
  pose proof (two_prod_ieee 18 (-98) n exp_l3 Fn F3 Nb L3b ltac:(lia) ltac:(lia) ltac:(lia) Dom) as TP.
  unfold acc_r. destruct (two_prod64 n exp_l3) as [p3 e3]. destruct TP as [Fp3 [Fe3 [Bp3 Be3]]].
  rewrite Bn, B3 in Bp3, Be3.
  (* RN(n·L4) *)
  assert (U4 : Rabs (B n * B exp_l4) <= 1).
  { rewrite Bn, B4, V4, Rabs_mult. apply Rle_trans with (137601 * Rabs (4725274267454307 / 2 ^ 205)).
    - apply Rmult_le_compat_r; [apply Rabs_pos | exact Kr].
    - rewrite Rabs_pos_eq by interval with (i_prec 64). interval with (i_prec 64). }
  destruct (fmul_ok 1 0 n exp_l4 Fn F4 ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)
              ltac:(unfold bnd; change (IZR 1 * bpow radix2 0) with (1 * 1); lra)) as [Fm Bm].
  rewrite Bn, B4 in Bm.
  (* the terms' sizes *)
  (* each term is a product below 10^-7 rounded, or that rounding's error *)
  assert (Er : forall v, Rabs v <= / 10000000 -> Rabs (rndF v - v) <= / 1000000000).
  { intros v Hv. pose proof (ExpReduction.rnd_abs_err v).
    assert (/ 2 * bpow radix2 (-1074) <= / 10000000000)
      by (change (-1074)%Z with (- Z.of_nat 1074)%Z; rewrite bpow_m; interval with (i_prec 64)).
    assert (/ 9007199254740992 * Rabs v <= / 10000000000) by (apply Rle_trans with (/ 9007199254740992 * / 10000000); [apply Rmult_le_compat_l; lra | interval with (i_prec 64)]).
    lra. }
  assert (Tiny : forall v, Rabs v <= / 10000000 -> Rabs (rndF v) <= / 1000000).
  { intros v Hv. pose proof (Er v Hv). pose proof (Rabs_triang_inv (rndF v) v). lra. }
  assert (S2 : Rabs (IZR k * ExpReduction.l2v) <= / 10000000).
  { rewrite Rabs_mult, V2. apply Rle_trans with (137601 * Rabs (- 7988006341064857 / 2 ^ 96)).
    - apply Rmult_le_compat_r; [apply Rabs_pos | exact Kr].
    - rewrite Rabs_left by interval with (i_prec 64). interval with (i_prec 64). }
  assert (S3 : Rabs (IZR k * ExpReduction.l3v) <= / 10000000).
  { rewrite Rabs_mult, V3. apply Rle_trans with (137601 * Rabs (6759741496705267 / 2 ^ 151)).
    - apply Rmult_le_compat_r; [apply Rabs_pos | exact Kr].
    - rewrite Rabs_pos_eq by interval with (i_prec 64). interval with (i_prec 64). }
  assert (S4 : Rabs (IZR k * ExpReduction.l4v) <= / 10000000).
  { rewrite Rabs_mult, V4. apply Rle_trans with (137601 * Rabs (4725274267454307 / 2 ^ 205)).
    - apply Rmult_le_compat_r; [apply Rabs_pos | exact Kr].
    - rewrite Rabs_pos_eq by interval with (i_prec 64). interval with (i_prec 64). }
  assert (Hp2 : Rabs (B p2) <= / 1000000) by (rewrite Bp2; apply Tiny, S2).
  assert (He2 : Rabs (B e2) <= / 1000000).
  { replace (B e2) with (- (rndF (IZR k * ExpReduction.l2v) - IZR k * ExpReduction.l2v)) by (rewrite <- Bp2; lra).
    rewrite Rabs_Ropp. pose proof (Er _ S2). lra. }
  assert (Hp3 : Rabs (B p3) <= / 1000000) by (rewrite Bp3; apply Tiny, S3).
  assert (He3 : Rabs (B e3) <= / 1000000).
  { replace (B e3) with (- (rndF (IZR k * ExpReduction.l3v) - IZR k * ExpReduction.l3v)) by (rewrite <- Bp3; lra).
    rewrite Rabs_Ropp. pose proof (Er _ S3). lra. }
  assert (Hm4 : Rabs (B (fmul n exp_l4)) <= / 1000000) by (rewrite Bm; apply Tiny, S4).
  (* r1 is below 0.00271 *)
  assert (Hr1 : Rabs (B r1) <= 0.00271).
  { rewrite Er1. replace (B x - IZR k * ExpReduction.l1v)
      with ((B x - IZR k * L) + IZR k * (L - ExpReduction.l1v)) by ring.
    apply Rle_trans with (1 := Rabs_triang _ _).
    assert (Rabs (L - ExpReduction.l1v) <= / 10000000000000 * 1.1).
    { replace (L - ExpReduction.l1v)
        with ((L - (ExpReduction.l1v + ExpReduction.l2v + ExpReduction.l3v + ExpReduction.l4v))
              + (ExpReduction.l2v + ExpReduction.l3v + ExpReduction.l4v)) by ring.
      apply Rle_trans with (1 := Rabs_triang _ _). pose proof HL as HL'. rewrite V2, V3, V4 in HL' |- *.
      assert (Rabs (- 7988006341064857 / 2 ^ 96 + 6759741496705267 / 2 ^ 151 + 4725274267454307 / 2 ^ 205)
              <= 1.01 * / 10000000000000) by interval with (i_prec 100).
      assert (/ 2 ^ 206 <= / 100000000000000000) by interval with (i_prec 64). lra. }
    rewrite Rabs_mult. assert (Rabs (IZR k) * Rabs (L - ExpReduction.l1v) <= 137601 * (/ 10000000000000 * 1.1))
      by (apply Rmult_le_compat; try apply Rabs_pos; assumption).
    lra. }
  (* the five additions *)
  destruct (fneg_ok p2 Fp2) as [Fq2 Bq2]. destruct (fneg_ok e2 Fe2) as [Fq3 Bq3].
  destruct (fneg_ok p3 Fp3) as [Fq4 Bq4]. destruct (fneg_ok e3 Fe3) as [Fq5 Bq5].
  destruct (fneg_ok (fmul n exp_l4) Fm) as [Fq6 Bq6].
  assert (A0 : NZ (qf r1) /\ Rabs (Q128.qval (qf r1) - B r1) <= / 2 ^ 130).
  { split; [apply from_f64_nz | ]. unfold qf. rewrite from_f64_b64 by exact Fr1.
    rewrite Rminus_diag_eq, Rabs_R0 by reflexivity. apply Rlt_le, Rinv_0_lt_compat, pow_lt. lra. }
  set (d := 3 / 1000 * / 2 ^ 126).
  assert (Dd : 0 <= d <= / 10000000) by (unfold d; split; interval with (i_prec 64)).
  destruct A0 as [N0 E0].
  assert (E0' : Rabs (Q128.qval (qf r1) - B r1) <= 0)
    by (unfold qf; rewrite from_f64_b64 by exact Fr1; rewrite Rminus_diag_eq, Rabs_R0 by reflexivity; lra).
  apply Rabs_le_inv in Hr1.
  assert (Hq2 : Rabs (B (fneg p2)) <= / 1000000) by (rewrite Bq2, Rabs_Ropp; exact Hp2).
  apply Rabs_le_inv in Hp2. apply Rabs_le_inv in He2. apply Rabs_le_inv in Hp3. apply Rabs_le_inv in He3.
  apply Rabs_le_inv in Hm4.
  destruct (add_small _ (fneg p2) (B r1) 0 N0 E0' ltac:(lra) ltac:(apply Rabs_le; lra) Fq2 Hq2) as [N1 E1].
  fold d in E1. rewrite Bq2 in E1.
  destruct (add_small _ (fneg e2) (B r1 + - B p2) (0 + d) N1 E1 ltac:(lra) ltac:(apply Rabs_le; lra)
             Fq3 ltac:(rewrite Bq3, Rabs_Ropp; apply Rabs_le; lra)) as [N2 E2].
  fold d in E2. rewrite Bq3 in E2.
  destruct (add_small _ (fneg p3) (B r1 + - B p2 + - B e2) (0 + d + d) N2 E2 ltac:(lra) ltac:(apply Rabs_le; lra)
             Fq4 ltac:(rewrite Bq4, Rabs_Ropp; apply Rabs_le; lra)) as [N3 E3].
  fold d in E3. rewrite Bq4 in E3.
  destruct (add_small _ (fneg e3) (B r1 + - B p2 + - B e2 + - B p3) (0 + d + d + d) N3 E3 ltac:(lra)
             ltac:(apply Rabs_le; lra) Fq5 ltac:(rewrite Bq5, Rabs_Ropp; apply Rabs_le; lra)) as [N4 E4].
  fold d in E4. rewrite Bq5 in E4.
  destruct (add_small _ (fneg (fmul n exp_l4)) (B r1 + - B p2 + - B e2 + - B p3 + - B e3) (0 + d + d + d + d)
             N4 E4 ltac:(lra) ltac:(apply Rabs_le; lra) Fq6 ltac:(rewrite Bq6, Rabs_Ropp; apply Rabs_le; lra))
    as [N5 E5].
  fold d in E5. rewrite Bq6 in E5.
  split; [exact N5 | ].
  (* the exact sum is x − n·(L1 + L2 + L3) − RN(n·L4), within 2^-186 of x − n·L *)
  set (S := B r1 + - B p2 + - B e2 + - B p3 + - B e3 + - B (fmul n exp_l4)) in E5.
  assert (Tail : Rabs (S - (B x - IZR k * L)) <= / 2 ^ 186).
  { replace (S - (B x - IZR k * L))
      with ((IZR k * ExpReduction.l4v - B (fmul n exp_l4))
            + IZR k * (L - (ExpReduction.l1v + ExpReduction.l2v + ExpReduction.l3v + ExpReduction.l4v)))
      by (unfold S; rewrite Er1; lra).
    apply Rle_trans with (1 := Rabs_triang _ _).
    pose proof (ExpReduction.rnd_abs_err (IZR k * ExpReduction.l4v)) as R4. rewrite <- Bm in R4.
    rewrite Rabs_minus_sym in R4. rewrite Rabs_mult.
    assert (Rabs (IZR k) * Rabs (L - (ExpReduction.l1v + ExpReduction.l2v + ExpReduction.l3v + ExpReduction.l4v))
            <= 137601 * / 2 ^ 206) by (apply Rmult_le_compat; try apply Rabs_pos; assumption).
    assert (Rabs (IZR k * ExpReduction.l4v) <= 137601 * (4725274267454307 / 2 ^ 205)).
    { rewrite Rabs_mult, V4. apply Rmult_le_compat; try apply Rabs_pos; [exact Kr | ].
      rewrite Rabs_pos_eq by interval with (i_prec 64). lra. }
    assert (/ 9007199254740992 * (137601 * (4725274267454307 / 2 ^ 205)) + / 2 * bpow radix2 (-1074)
            + 137601 * / 2 ^ 206 <= / 2 ^ 186).
    { change (-1074)%Z with (- Z.of_nat 1074)%Z. rewrite bpow_m. interval with (i_prec 100). }
    assert (0 <= / 9007199254740992) by lra. nra. }
  set (Qv := Q128.qval _) in E5 |- *.
  replace (Qv - (B x - IZR k * L)) with ((Qv - S) + (S - (B x - IZR k * L))) by ring.
  apply Rle_trans with (1 := Rabs_triang _ _).
  assert (0 + d + d + d + d + d + / 2 ^ 186 <= / 2 ^ 131) by (unfold d; interval with (i_prec 100)).
  lra.
Qed.
