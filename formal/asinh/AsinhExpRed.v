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
