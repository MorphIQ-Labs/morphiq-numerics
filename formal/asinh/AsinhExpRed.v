(** asinh's accurate path, the exponential's argument reduction: [k] is the
    nearest integer to [y / ln 2], [r = y - k ln 2] stays within [0.3467], and
    [asinh_exp y] is [m 2^k] with [m] within [2^-237] of [exp r]. *)
From Coq Require Import Reals ZArith Lia Lra Psatz List.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Mul Grid Encodings RoundingCore.
From Interval Require Import Tactic.
From Q Require Import Q256 Q256Real QSpec.
Require Import Ln1pLemmas AsinTables AsinKernel AsinSqrtStep AsinSegment AsinSeriesSmall AsinRecip AsinQSeries
  ExpReduction ErfcxAccurateInputs AsinhTables AsinhKernel AsinhConst AsinhOps AsinhWithin AsinhExp.
Import ListNotations.
Open Scope R_scope.

(** The integer a binary64 integer holds. *)
Lemma asinh_int_val f z : finite f -> B f = IZR z -> asinh_int f = z.
Proof.
  intros Ff Hv. destruct f as [s | s | s pl Hpl | s m e Hb]; try (simpl in Ff; discriminate Ff).
  - simpl in Hv. simpl. assert (IZR z = 0) by (rewrite <- Hv; reflexivity). apply eq_IZR in H. lia.
  - cbn [asinh_int]. cbn in Hv. unfold F2R in Hv. cbn [Fnum Fexp] in Hv.
    destruct (e <? 0)%Z eqn:Ee.
    + apply Z.ltb_lt in Ee.
      assert (Hp : bpow radix2 e = / IZR (2 ^ (- e))).
      { replace e with (- (- e))%Z at 1 by ring. rewrite bpow_opp. f_equal. symmetry. apply (IZR_Zpower radix2). lia. }
      rewrite Hp in Hv.
      assert (Hpos : 0 < IZR (2 ^ (- e))) by (apply IZR_lt; apply Z.pow_pos_nonneg; lia).
      assert (Hz : cond_Zopp s (Zpos m) = (z * 2 ^ (- e))%Z).
      { apply eq_IZR. rewrite mult_IZR. rewrite <- Hv.
        field. apply not_eq_sym. apply Rlt_not_eq. exact Hpos. }
      rewrite (Z.shiftr_div_pow2 (Zpos m) (- e)) by lia.
      destruct s.
      * simpl in Hz. simpl. assert (Zpos m = (- z * 2 ^ (- e))%Z) by lia.
        rewrite H. rewrite Z.div_mul by (apply Z.pow_nonzero; lia). lia.
      * simpl in Hz. simpl. rewrite Hz. rewrite Z.div_mul by (apply Z.pow_nonzero; lia). lia.
    + apply Z.ltb_ge in Ee. rewrite (Z.shiftl_mul_pow2 (Zpos m) e) by lia.
      assert (Hp : bpow radix2 e = IZR (2 ^ e)) by (symmetry; apply (IZR_Zpower radix2); lia).
      rewrite Hp in Hv. rewrite <- mult_IZR in Hv. apply eq_IZR in Hv.
      destruct s; cbn [cond_Zopp] in Hv |- *.
      * change (Z.neg m) with (- Z.pos m)%Z in Hv. rewrite <- Hv. ring.
      * exact Hv.
Qed.

Definition ln2q : q256 := Q256.new false (fst asinh_ln2_q256) (snd asinh_ln2_q256).

Lemma ln2q_limbs : limbs_check (fst asinh_ln2_q256) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma ln2q_v : Limbs.v (fst asinh_ln2_q256) = 80260960185991308862233904206310070533990667611589946606122867505419956976172%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma ln2q_ok : Q256Real.valid ln2q /\ Rabs (qval ln2q - ln 2) <= bpow radix2 (-250) /\ 0.69 <= qval ln2q <= 0.7.
Proof.
  pose proof (limbs_check_ok _ ln2q_limbs) as Ok.
  split; [exact (new_valid false _ _ Ok) | ].
  assert (Hq : qval ln2q = IZR 80260960185991308862233904206310070533990667611589946606122867505419956976172 * bpow radix2 (-256)).
  { unfold ln2q. rewrite new_val by exact Ok. rewrite ln2q_v. unfold val, F2R. cbn [Fnum Fexp]. 
    change (snd asinh_ln2_q256) with (-256)%Z. reflexivity. }
  rewrite Hq. bpow_num. split.
  - apply Rabs_le. split; interval with (i_prec 500).
  - split; interval with (i_prec 500).
Qed.

Lemma inv_ln2_val : finite (aw asinh_inv_ln2) /\ Rabs (B (aw asinh_inv_ln2) - / ln 2) <= / 5000000000000000 /\ 1.44 <= B (aw asinh_inv_ln2) <= 1.45.
Proof.
  destruct (word_ok_intro (0x3ff71547652b82fe)%Z false 6497320848556798%positive 52%nat (3248660424278399)%Z 1%Z (-51)%Z
    eq_refl eq_refl ltac:(lia) eq_refl) as [F V].
  unfold asinh_inv_ln2. split; [exact F | ]. rewrite V. bpow_num.
  split; [ | split]; interval with (i_prec 100).
Qed.

(** [|exp u - 1| <= 2 |u|] for [|u| <= 1/2]. *)
Lemma exp_near1 u : Rabs u <= / 2 -> Rabs (exp u - 1) <= 2 * Rabs u.
Proof.
  intros H. apply Rabs_le_inv in H. destruct H as [H1 H2].
  pose proof (exp_pos u) as P.
  assert (L : 1 + u <= exp u).
  { destruct (Req_dec u 0) as [-> | N]; [rewrite exp_0; lra | pose proof (exp_ineq1 u N); lra]. }
  assert (L' : 1 + - u <= exp (- u)).
  { destruct (Req_dec u 0) as [-> | N]; [rewrite Ropp_0, exp_0; lra | pose proof (exp_ineq1 (- u) ltac:(lra)); lra]. }
  destruct (Rle_lt_dec 0 u) as [Hp | Hn].
  - assert (E : exp u = / exp (- u)) by (rewrite exp_Ropp, Rinv_involutive; [reflexivity | apply Rgt_not_eq, P]).
    assert (U : exp u <= / (1 - u)) by (rewrite E; apply Rinv_le_contravar; lra).
    assert (U2 : / (1 - u) <= 1 + 2 * u).
    { apply (Rmult_le_reg_l (1 - u)); [lra | ]. rewrite Rinv_r by lra. nra. }
    rewrite (Rabs_pos_eq u) by lra. apply Rabs_le. split; lra.
  - assert (U : exp u <= 1) by (rewrite <- exp_0; apply Rlt_le, exp_increasing; lra).
    rewrite (Rabs_left u) by lra. apply Rabs_le. split; lra.
Qed.

(** [exp] is [3]-Lipschitz on [[-0.35, 0.35]]. *)
Lemma exp_lip a b : Rabs a <= 0.35 -> Rabs b <= 0.35 -> Rabs (a - b) <= / 2 -> Rabs (exp a - exp b) <= 3 * Rabs (a - b).
Proof.
  intros Ha Hb Hd.
  pose proof (exp_near1 (a - b) Hd) as N.
  assert (E : exp a - exp b = exp b * (exp (a - b) - 1)).
  { assert (E1 : exp b * exp (a - b) = exp a) by (rewrite <- exp_plus; f_equal; ring).
    rewrite Rmult_minus_distr_l, Rmult_1_r, E1. reflexivity. }
  rewrite E, Rabs_mult, (Rabs_pos_eq (exp b)) by apply Rlt_le, exp_pos.
  assert (Eb : exp b <= 1.5).
  { apply Rabs_le_inv in Hb. destruct Hb as [Hb1 Hb2]. destruct (Rle_lt_or_eq_dec b 0.35 Hb2) as [Hlt | Heq]; [apply Rle_trans with (exp 0.35); [apply Rlt_le, exp_increasing; exact Hlt | interval with (i_prec 60)] | rewrite Heq; interval with (i_prec 60)]. }
  pose proof (Rabs_pos (exp (a - b) - 1)). 
  apply Rle_trans with (1.5 * (2 * Rabs (a - b))); [apply Rmult_le_compat; try apply Rlt_le, exp_pos; try lra; exact N | lra].
Qed.
