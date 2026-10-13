(** The gaps around a positive binary64 number and the reals that round to it,
    for the rounding test (RoundingTest.v). *)

From Coq Require Import ZArith Reals Lia Lra Psatz.
From Flocq Require Import Core.
From Binary64 Require Import Binary64Add.

Open Scope R_scope.

Notation fexp64 := (FLT_exp (-1074) 53).
Notation F64 := (generic_format radix2 fexp64).
#[export] Instance prec53 : Prec_gt_0 53 := eq_refl.

(** The gap above a positive representable u is ulp u. *)
Lemma gap_above u : 0 < u -> succ radix2 fexp64 u - u = ulp radix2 fexp64 u.
Proof. intros Pu. rewrite succ_eq_pos by lra. ring. Qed.

(** The gap below is ulp u, except at a power of two, where it is half. *)
Lemma gap_below u : F64 u -> 0 < u ->
  ulp radix2 fexp64 u / 2 <= u - pred radix2 fexp64 u /\
  (u <> bpow radix2 (mag radix2 u - 1) -> u - pred radix2 fexp64 u = ulp radix2 fexp64 u).
Proof.
  intros Fu Pu.
  pose proof (pred_plus_ulp radix2 fexp64 u Pu Fu) as Pl.
  assert (Eq : u - pred radix2 fexp64 u = ulp radix2 fexp64 (pred radix2 fexp64 u)) by lra.
  rewrite Eq.
  pose proof (ulp_ge_0 radix2 fexp64 u) as U0.
  destruct (ulp_FLT_pred_pos radix2 (-1074) 53 u Fu ltac:(lra)) as [A | [B C]].
  - rewrite A. split; [lra | auto].
  - rewrite C. simpl IZR. split; [lra | intros N; contradiction].
Qed.

(** A real strictly within half the smaller gap of a positive representable
    u rounds to u. *)
Lemma round_within u z g : F64 u -> 0 < u ->
  g <= ulp radix2 fexp64 u -> g <= u - pred radix2 fexp64 u ->
  Rabs (z - u) < g / 2 ->
  round radix2 fexp64 (Znearest (fun n => negb (Z.even n))) z = u.
Proof.
  intros Fu Pu G1 G2 H. apply Rabs_lt_inv in H.
  apply Rle_antisym.
  - apply round_N_le_midp; auto with typeclass_instances.
    rewrite succ_eq_pos by lra. lra.
  - apply round_N_ge_midp; auto with typeclass_instances. lra.
Qed.

(** Relative distances valid for both normal and subnormal values. *)
Lemma relative_gaps u : fmtF u -> 0 < u ->
 u*bpow radix2 (-53) <= ulp radix2 (FLT_exp emin prec) u /\
 u*bpow radix2 (-53) <= u-pred radix2 (FLT_exp emin prec) u.
Proof.
 intros Fu Pu. assert (U0 : u <> 0) by lra.
 pose proof (bpow_mag_gt radix2 u) as M. rewrite Rabs_pos_eq in M by lra.
 assert (Ur : ulp radix2 (FLT_exp emin prec) u = bpow radix2 (Z.max (mag radix2 u-53) (-1074))).
 { rewrite ulp_neq_0 by exact U0. reflexivity. }
 assert (Pow : bpow radix2 (mag radix2 u-53) <= ulp radix2 (FLT_exp emin prec) u).
 { rewrite Ur. apply bpow_le. lia. }
 assert (A : u*bpow radix2 (-53) <= ulp radix2 (FLT_exp emin prec) u).
 { apply Rle_trans with (bpow radix2 (mag radix2 u)*bpow radix2 (-53)).
   - apply Rmult_le_compat_r; [apply bpow_ge_0 | lra].
   - rewrite <-bpow_plus. exact Pow. }
 split; [exact A | ]. destruct (Req_dec u (bpow radix2 (mag radix2 u-1))) as [Eq | Ne].
 - destruct (gap_below u Fu Pu) as [L _]. apply Rle_trans with (1:=Rle_refl (u*bpow radix2 (-53))).
   apply Rle_trans with (ulp radix2 (FLT_exp emin prec) u/2); [ | exact L].
   rewrite Eq at 1. rewrite <-bpow_plus.
   assert (P : bpow radix2 (mag radix2 u-1 + -53) = bpow radix2 (mag radix2 u-53)/2).
   { replace (mag radix2 u-1 + -53)%Z with ((mag radix2 u-53)+(-1))%Z by lia.
     rewrite bpow_plus. change (bpow radix2 (-1)) with (/2). reflexivity. }
   rewrite P. lra.
 - destruct (gap_below u Fu Pu) as [_ E]. specialize (E Ne).
   change (u-pred radix2 (FLT_exp emin prec) u = ulp radix2 (FLT_exp emin prec) u) in E.
   rewrite E. exact A.
Qed.
Lemma round_relative_close x y : fmtF x -> x <> 0 -> Rabs (y-x) < Rabs x/2^54 -> rndF y = x.
Proof.
 intros Fx X0 E. destruct (Rlt_dec 0 x) as [Pos | Neg].
 - rewrite (Rabs_pos_eq x) in E by lra. destruct (relative_gaps x Fx Pos) as [A B].
   apply (round_within x y (x*bpow radix2 (-53)) Fx Pos A B).
   apply Rlt_le_trans with (1:=E). change (bpow radix2 (-53)) with (/9007199254740992). right. field.
 - assert (Px : 0 < -x) by lra.
   destruct (relative_gaps (-x) (generic_format_opp _ _ _ Fx) Px) as [A B].
   assert (R : rndF (-y) = -x).
   { apply (round_within (-x) (-y) ((-x)*bpow radix2 (-53)) (generic_format_opp _ _ _ Fx) Px A B).
     replace (-y - -x) with (-(y-x)) by ring. rewrite Rabs_Ropp.
     rewrite (Rabs_left x) in E by lra. apply Rlt_le_trans with (1:=E). change (bpow radix2 (-53)) with (/9007199254740992). right. field. }
   rewrite round_NE_opp_ne in R. lra.
Qed.
