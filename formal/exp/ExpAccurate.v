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
Require ExpTables ExpAccurateLevels.
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
