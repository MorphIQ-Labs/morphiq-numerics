(** Below [ASINH_IS_X] (inclusive) the Rust returns [x], and [x] is [RN (arcsinh x)]:
    [x - arcsinh x <= x^3/6] stays below half the gap to the predecessor. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Binary64 Require Import Binary64Add IEEE64.
From Interval Require Import Tactic.
Require Import Ln1pLemmas AsinhWithin AsinhExpRed.
Open Scope R_scope.

(** The gap below a positive binary64. *)
Lemma gap_below a : fmtF a -> 0 < a ->
  bpow radix2 (mag radix2 a - 1) <= a < bpow radix2 (mag radix2 a) /\
  (a <> bpow radix2 (mag radix2 a - 1) -> bpow radix2 (mag radix2 a - 53) <= a - pred radix2 (FLT_exp emin prec) a) /\
  (a = bpow radix2 (mag radix2 a - 1) -> bpow radix2 (mag radix2 a - 54) <= a - pred radix2 (FLT_exp emin prec) a).
Proof.
  intros Fa Pa.
  pose proof (bpow_mag_le radix2 a (Rgt_not_eq _ _ Pa)) as Hlo. rewrite (Rabs_pos_eq a) in Hlo by lra.
  pose proof (bpow_mag_gt radix2 a) as Hhi. rewrite (Rabs_pos_eq a) in Hhi by lra.
  repeat split; try assumption.
  - intros Hn. rewrite (pred_eq_pos radix2 (FLT_exp emin prec) a (Rlt_le _ _ Pa)). unfold pred_pos.
    destruct (Req_bool_spec a (bpow radix2 (mag radix2 a - 1))) as [E | N]; [exfalso; apply Hn; exact E | ].
    rewrite (ulp_neq_0 radix2 (FLT_exp emin prec) a (Rgt_not_eq _ _ Pa)). unfold cexp, FLT_exp.
    replace (a - (a - bpow radix2 (Z.max (mag radix2 a - prec) emin))) with (bpow radix2 (Z.max (mag radix2 a - prec) emin)) by ring.
    apply bpow_le. unfold prec. apply Z.le_max_l.
  - intros E. rewrite (pred_eq_pos radix2 (FLT_exp emin prec) a (Rlt_le _ _ Pa)). unfold pred_pos.
    destruct (Req_bool_spec a (bpow radix2 (mag radix2 a - 1))) as [E' | N]; [ | exfalso; apply N; exact E].
    unfold FLT_exp. replace (a - (a - bpow radix2 (Z.max (mag radix2 a - 1 - prec) emin))) with (bpow radix2 (Z.max (mag radix2 a - 1 - prec) emin)) by ring.
    apply bpow_le. unfold prec. 
    apply Z.le_trans with (mag radix2 a - 1 - 53)%Z; [lia | apply Z.le_max_l].
Qed.
