(** Exact normal scaling after the cancellation-aware interval test. *)
From Coq Require Import ZArith Reals Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 Grid RoundingTest.
From Interval Require Import Tactic.
Require Import StageGappa Ln1pLemmas Ln1pReduction Ln1pTest LnReduction Expm1Subtract.
Open Scope R_scope.
Definition em_pow2 k := b64_of_bits (Z.shiftl (1023+k) 52).
Lemma em_pow2_ok k : (-1022 <= k <= 1023)%Z -> finite (em_pow2 k) /\ B (em_pow2 k) = bpow radix2 k.
Proof. intros H. pose proof (pow2_bits (1023+k) ltac:(lia)) as P. rewrite Z.lor_0_r in P. replace (1023+k-1023)%Z with k in P by ring. exact P. Qed.

Lemma em_nonzero x : /32 <= Rabs x -> /64 <= Rabs (exp x - 1).
Proof.
 intros H. destruct (Rle_dec 0 x) as [P | N].
 - rewrite Rabs_pos_eq in H by exact P.
   assert (L : exp (/32) <= exp x) by (apply exp_le; lra).
   assert (E : 1 + /64 <= exp (/32)) by interval with (i_prec 64).
   rewrite Rabs_pos_eq; lra.
 - rewrite Rabs_left in H by lra.
   assert (L : exp x <= exp (- /32)) by (apply exp_le; lra).
   assert (E : exp (- /32) <= 1 - /64) by interval with (i_prec 64).
   rewrite Rabs_left; lra.
Qed.

Lemma em_unscaled_range x z k : (-54 <= k <= 1016)%Z -> /32 <= Rabs x ->
 9/10 <= z <= 21/10 -> exp x = z * bpow radix2 k ->
 bpow radix2 (-8) <= Rabs (z - bpow radix2 (-k)) /\
 Rabs (z - bpow radix2 (-k)) <= bpow radix2 55 /\
 ((0 <= k)%Z -> Rabs (z - bpow radix2 (-k)) <= 4).
Proof.
 intros K X Z E. pose proof (bpow_gt_0 radix2 (-k)) as P.
 assert (C : bpow radix2 (-k) <= bpow radix2 54) by (apply bpow_le; lia).
 assert (Upper : Rabs (z - bpow radix2 (-k)) <= bpow radix2 55).
 { apply Rle_trans with (1 := Rabs_triang _ _). rewrite Rabs_Ropp, !Rabs_pos_eq by lra. bpow_num_all. lra. }
 split; [ | split; [exact Upper | ]].
 - destruct (Z_le_gt_dec 2 k) as [Hi | Hi].
   + assert (C1 : bpow radix2 (-k) <= /4) by (change (/4) with (bpow radix2 (-2)); apply bpow_le; lia).
     rewrite Rabs_pos_eq by lra. bpow_num. lra.
   + destruct (Z_le_gt_dec k (-2)) as [Lo | Lo].
     * assert (C1 : 4 <= bpow radix2 (-k)) by (change 4 with (bpow radix2 2); apply bpow_le; lia).
       rewrite Rabs_left by lra. bpow_num. lra.
     * assert (C1 : /2 <= bpow radix2 (-k)) by (change (/2) with (bpow radix2 (-1)); apply bpow_le; lia).
       pose proof (em_nonzero x X) as N.
       assert (Eq : z - bpow radix2 (-k) = (exp x - 1) * bpow radix2 (-k)).
       { rewrite E. rewrite Rmult_minus_distr_r, Rmult_assoc, <- bpow_plus, Z.add_opp_diag_r. change (bpow radix2 0) with 1. ring. }
       rewrite Eq, Rabs_mult, (Rabs_pos_eq (bpow radix2 _)) by lra.
       apply Rle_trans with ((/64)*(/2)); [bpow_num; lra | apply Rmult_le_compat; lra].
 - intros K0. assert (C1 : bpow radix2 (-k) <= 1) by (change 1 with (bpow radix2 0); apply bpow_le; lia).
   apply Rle_trans with (1 := Rabs_triang _ _). rewrite Rabs_Ropp, !Rabs_pos_eq by lra. lra.
Qed.

Theorem em_scale_ok v w k : finite v -> B v = rndF w ->
 (-54 <= k <= 1016)%Z -> bpow radix2 (-8) <= Rabs w -> Rabs w <= bpow radix2 55 ->
 ((0 <= k)%Z -> Rabs w <= 4) ->
 finite (fmul v (em_pow2 k)) /\ B (fmul v (em_pow2 k)) = rndF (w * bpow radix2 k).
Proof.
 intros Fv Bv K Wl Wh Wp.
 assert (N : w <> 0) by (intros E; rewrite E, Rabs_R0 in Wl; pose proof (bpow_gt_0 radix2 (-8)); lra).
 assert (M : (-7 <= mag radix2 w)%Z) by (apply mag_ge_bpow; exact Wl).
 assert (Sc : rndF (w * bpow radix2 k) = rndF w * bpow radix2 k) by (apply round_scale; [exact N | lia | lia]).
 destruct (em_pow2_ok k ltac:(lia)) as [Fp Bp].
 assert (Fprod : fmtF (B v * B (em_pow2 k))).
 { rewrite Bp, Bv, <- Sc. apply generic_format_round; auto with typeclass_instances. }
 assert (Bound : Rabs (B v * B (em_pow2 k)) < bpow radix2 1024).
 { rewrite Bp, Bv, Rabs_mult, (Rabs_pos_eq (bpow radix2 k)) by apply bpow_ge_0.
   destruct (Z_le_gt_dec 0 k) as [Pos | Neg].
   - assert (V : Rabs (rndF w) <= bpow radix2 2) by (apply round_power; [apply Wp, Pos | lia]).
     apply Rle_lt_trans with (bpow radix2 2 * bpow radix2 k).
     + apply Rmult_le_compat_r; [apply bpow_ge_0 | exact V].
     + rewrite <- bpow_plus. apply bpow_lt; lia.
   - assert (V : Rabs (rndF w) <= bpow radix2 55) by (apply round_power; [exact Wh | lia]).
     apply Rle_lt_trans with (bpow radix2 55 * bpow radix2 k).
     + apply Rmult_le_compat_r; [apply bpow_ge_0 | exact V].
     + rewrite <- bpow_plus. apply bpow_lt; lia. }
 destruct (fmul_exact v (em_pow2 k) Fv Fp Fprod Bound) as [F Bm].
 split; [exact F | rewrite Bm, Bp, Bv; symmetry; exact Sc].
Qed.

Definition em_decide h l base k :=
 let '(s,lo,eps) := subtract_parts h l (em_pow2 (-k)) base in
 match Ln1pTest.decide s lo eps with Some v => Some (fmul v (em_pow2 k)) | None => None end.

Theorem em_decide_ok h l base k x z v :
 finite h -> finite l -> finite base ->
 Rabs (B h) <= 4 -> Rabs (B l) <= bpow radix2 (-9) ->
 bpow radix2 (-68) <= B base <= bpow radix2 (-59) ->
 Rabs (z - (B h + B l)) <= B base / 2 ->
 (-54 <= k <= 1016)%Z -> /32 <= Rabs x -> 9/10 <= z <= 21/10 -> exp x = z * bpow radix2 k ->
 em_decide h l base k = Some v -> finite v /\ B v = rndF (exp x - 1).
Proof.
 intros Fh Fl Fb Ah Al Ab Err K X Z Ex.
 destruct (em_pow2_ok (-k) ltac:(lia)) as [Fc Bc].
 assert (Ac : Rabs (B (em_pow2 (-k))) <= bpow radix2 54).
 { rewrite Bc, Rabs_pos_eq by apply bpow_ge_0. apply bpow_le; lia. }
 pose proof (subtract_parts_ok h l (em_pow2 (-k)) base z Fh Fl Fc Fb Ah Al Ac Ab Err) as P.
 unfold em_decide. revert P. generalize (subtract_parts h l (em_pow2 (-k)) base).
 intros [[s lo] eps] [Fs [Flo [Fe [E0 [As [Alow Error]]]]]].
 destruct (Ln1pTest.decide s lo eps) as [u | ] eqn:D; [ | discriminate].
 intros H. injection H as <-.
 destruct (decide_bounded_ok s lo eps u Fs Flo Fe E0 As Alow D) as [Fu Bu].
 specialize (Bu (z - B (em_pow2 (-k))) Error). rewrite Bc in Bu.
 destruct (em_unscaled_range x z k K X Z Ex) as [Wl [Wh Wp]].
 assert (Eq : exp x - 1 = (z - bpow radix2 (-k)) * bpow radix2 k).
 { rewrite Ex, Rmult_minus_distr_r, <- bpow_plus, Z.add_opp_diag_l. reflexivity. }
 rewrite Eq. apply em_scale_ok; try assumption. symmetry; exact Bu.
Qed.
