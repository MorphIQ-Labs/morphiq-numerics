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
From Interval Require Import Tactic.
Import ListNotations.

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
