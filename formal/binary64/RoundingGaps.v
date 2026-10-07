(** The gaps around a positive binary64 number and the reals that round to it,
    for the rounding test (RoundingTest.v). *)

From Coq Require Import ZArith Reals Lia Lra Psatz.
From Flocq Require Import Core.

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
