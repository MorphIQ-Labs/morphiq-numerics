(** exp2's fallback: exact dyadic reduction, Q128 multiplication by ln 2,
    and the shared exponential series/table/scaling, before binary64 rounding.
    The public entry's screens and the final rounding are separate obligations. *)
From Coq Require Import ZArith Reals Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Interval Require Import Tactic.
From Q Require Q128 QSpec.
From Binary64 Require Import IEEE64.
Require Import Exp2Constants Exp2FallbackReduction ExpAccurate Ln1pLemmas.
Require ExpFast.
Open Scope R_scope.

Definition exp2_qproduct d := Q128.mul (qf d) e2_lq.
Definition exp2_fallback_accurate x :=
 let '(_,j,k,d) := exp2_fallback_reduce x in
 accurate_at (exp2_qproduct d) (Z.to_nat j) k.

Lemma exp2_qproduct_ok d : finite d -> Rabs (B d) <= bpow radix2 (-8) ->
 NZ (exp2_qproduct d) /\
 Rabs (Q128.qval (exp2_qproduct d) - B d * ln 2) <= / 2 ^ 134.
Proof.
 intros Fd D. unfold exp2_qproduct.
 destruct (mul_any (qf d) e2_lq (from_f64_nz _) (or_intror e2_lq_normalized))
   as [N [t [Ht V]]].
 split; [exact N | ].
 unfold qf in V |- *. rewrite from_f64_b64 in V by exact Fd.
 rewrite V.
 replace (B d * Q128.qval e2_lq * (1+t) - B d * ln 2)
   with (B d * ((Q128.qval e2_lq - ln 2) + Q128.qval e2_lq * t)) by ring.
 rewrite Rabs_mult. apply Rle_trans with
   (bpow radix2 (-8) * (/ 2 ^ 129 + 0.7 * bpow radix2 (-127))).
 - apply Rmult_le_compat; try apply Rabs_pos; [exact D | ].
   apply Rle_trans with (1 := Rabs_triang _ _). apply Rplus_le_compat; [exact e2_lq_close | ].
   rewrite Rabs_mult. apply Rmult_le_compat; try apply Rabs_pos.
   + rewrite Rabs_pos_eq by exact (proj1 e2_lq_range). exact (proj2 e2_lq_range).
   + apply Rabs_le; lra.
 - bpow_num. interval with (i_prec 180).
Qed.

Theorem exp2_fallback_accurate_bound x : finite x ->
 bpow radix2 (-55) <= Rabs (B x) -> Rabs (B x) <= 1075 ->
 QSpec.normalized 128 (Q128.m (exp2_fallback_accurate x)) /\
 Rabs (Q128.qval (exp2_fallback_accurate x) - exp (B x * ln 2))
   <= 1097 / 2 ^ 134 * exp (B x * ln 2).
Proof.
 intros Fx Xlo Xhi.
 pose proof (exp2_fallback_reduce_ok x Fx Xlo Xhi) as RD.
 unfold exp2_fallback_accurate. revert RD.
 generalize (exp2_fallback_reduce x).
 intros [[[n j] k] d] [ni [Fn [Bn [Ni [JK [J [K [Fd [Bd [D Dlo]]]]]]]]]].
 destruct (exp2_qproduct_ok d Fd D) as [N E].
 assert (E' : Rabs (Q128.qval (exp2_qproduct d) - B d * ln 2) <= / 2 ^ 131).
 { apply Rle_trans with (1 := E). interval with (i_prec 160). }
 assert (DR : Rabs (B d * ln 2) <= 0.0027076063).
 { rewrite Rabs_mult. apply Rle_trans with (bpow radix2 (-8) * Rabs (ln 2)).
   - apply Rmult_le_compat_r; [apply Rabs_pos | exact D].
   - bpow_num. interval with (i_prec 100). }
 assert (Jnat : (Z.to_nat j < 128)%nat) by lia.
 destruct (accurate_bound (exp2_qproduct d) (Z.to_nat j) k (B d * ln 2) N E' DR Jnat) as [NY EY].
 cbv zeta in EY.
 assert (Split : exp (INR (Z.to_nat j) * ln 2 / 128) * exp (B d * ln 2) * bpow radix2 k
   = exp (B x * ln 2)).
 { rewrite <- ExpFast.exp_split. f_equal. rewrite Z2Nat.id by lia.
   rewrite <- JK, Bd. field. }
 rewrite Split in EY. split; assumption.
Qed.
