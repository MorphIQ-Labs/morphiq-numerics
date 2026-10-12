(** Cancellation ratios for the general expm1 fallback, and applications of
    its generated Gappa certificates to the arithmetic errors. *)
From Coq Require Import ZArith Reals Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Interval Require Import Tactic.
From Gappa Require Import Gappa_definitions Gappa_round_def.
From Binary64 Require Import Binary64Add IEEE64.
Require Import StageGappa ExpAccurate Expm1Scale Ln1pLemmas.
Require expm1_fast_general expm1_accurate_general.
Open Scope R_scope.

Lemma em_ratio_bounds x : /32 <= Rabs x ->
 exp x <= 32.51 * Rabs (exp x - 1) /\
 1 <= 32.51 * Rabs (exp x - 1).
Proof.
 intros X. pose proof (exp_pos x) as P.
 destruct (Rle_dec 0 x) as [Pos | Neg].
 - rewrite Rabs_pos_eq in X by exact Pos.
   assert (L : exp (/32) <= exp x) by (apply exp_le; lra).
   assert (E : 32.51 <= 31.51 * exp (/32)) by interval with (i_prec 100).
   rewrite Rabs_pos_eq by lra. split; lra.
 - rewrite Rabs_left in X by lra.
   assert (L : exp x <= exp (- /32)) by (apply exp_le; lra).
   assert (E : 32.51 * exp (- /32) <= 31.51) by interval with (i_prec 100).
   rewrite Rabs_left by lra. split; lra.
Qed.

Lemma em_ratio_certificate x : /32 <= Rabs x ->
 -526/16 <= exp x / (exp x - 1) <= 526/16.
Proof.
 intros X. destruct (em_ratio_bounds x X) as [E _].
 pose proof (em_nonzero x X) as N.
 assert (A : Rabs (exp x / (exp x - 1)) <= 32.51).
 { apply ratio_bound; [lra | rewrite Rabs_pos_eq by (apply Rlt_le, exp_pos); exact E]. }
 apply Rabs_le_inv in A. lra.
Qed.

Lemma em_fast_certificate kq eY ea :
 -526/16 <= kq <= 526/16 ->
 - /2^69 <= eY <= /2^69 -> - /2^105 <= ea <= /2^105 ->
 - /2^62 <= (1+kq*eY)*(1+ea)-1 <= /2^62.
Proof.
 intros K Y A.
 assert (G : BND ((1+kq*eY)*(1+ea)-1) (makepairF (Float2 (-1) (-62)) (Float2 1 (-62)))).
 { gappa_goal (expm1_fast_general.l1 kq eY ea). }
 apply bnd_to in G. destruct G as [G1 G2].
 bpow_num_all. lra.
Qed.
Lemma em_accurate_certificate kq eV sr :
 -526/16 <= kq <= 526/16 ->
 -1097/2^134 <= eV <= 1097/2^134 ->
 -542/2^130 <= sr <= 542/2^130 ->
 - /2^118 <= kq*eV+sr <= /2^118.
Proof.
 intros K V S. replace (kq*eV+sr) with ((1+kq*eV+sr)-1) by ring.
 assert (G : BND ((1+kq*eV+sr)-1) (makepairF (Float2 (-1) (-118)) (Float2 1 (-118)))).
 { gappa_goal (expm1_accurate_general.l1 kq eV sr). }
 apply bnd_to in G. destruct G as [G1 G2].
 bpow_num_all. lra.
Qed.
