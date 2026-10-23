(** Per-rule certificates of the low-correlation branch: the enclosure data
    satisfy the node lemmas' conditions, the per-node suprema, the truncation
    bound and the angle's rounding sum to the bound stated in [low_N]. *)
From Coq Require Import Reals ZArith Lia Lra List.
Import ListNotations.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Double Require Import DWPlus.
From Binary64 Require Import Binary64Add.
From Coquelicot Require Import Coquelicot.
Require Import BvnRound BvnArg BvnNode BvnTrig BvnLow BvnSum BvnChain BvnQuadG BvnRule BvnTail BvnIntegral BvnTop BvnLowRule BvnEllipse BvnRules BvnData.
Open Scope R_scope.

Ltac dat_goals :=
  unfold dat_ok, theta_of, zt_of, ar0, u; cbn [dtaulo dtauhi dwhi dk dbr]; simpl;
  repeat split; try lia; interval with (i_prec 64).
Ltac all_dats := repeat (apply List.Forall_cons; [dat_goals |]); apply List.Forall_nil.
Ltac br_goals :=
  unfold br_ok, theta_of, ar0, B0, u; cbn [dtaulo dtauhi dwhi dk dbr]; simpl;
  split; intros Hbr; first [discriminate Hbr | interval with (i_prec 64)].
Ltac all_brs := repeat (apply List.Forall_cons; [br_goals |]); apply List.Forall_nil.
Ltac sum_goal :=
  unfold gcl, theta_of, ar0, B0, u; cbn [dtaulo dtauhi dwhi dk dbr]; simpl; interval with (i_prec 64).

Lemma dat_ok_4 : List.Forall (dat_ok A4) dats_4.
Proof. unfold dats_4. all_dats. Qed.
Lemma br_ok_4 : List.Forall (br_ok A4 B0) dats_4.
Proof. unfold dats_4. all_brs. Qed.
Lemma sum_4 : A4 / (4 * PI) * sumD (gcl A4 B0) dats_4 <= 681 / 10 ^ 20.
Proof. unfold dats_4. simpl. unfold A4. sum_goal. Qed.
Lemma trunc_4 : trunc_bound A4 R4 4 / (2 * PI) <= 161 / 10 ^ 19.
Proof. unfold trunc_bound, A4, R4. interval with (i_prec 64). Qed.
Lemma shift_4 : bpow radix2 (-4 - 54) / (2 * PI) <= 569 / 10 ^ 21.
Proof. simpl. interval with (i_prec 64). Qed.
Lemma bd_4 : 4 * bpow radix2 (-54) + (681 / 10 ^ 20) + 1000 * z + (161 / 10 ^ 19) + (569 / 10 ^ 21) <= 247 / 10 ^ 18.
Proof. unfold z. simpl. interval with (i_prec 100). Qed.

Theorem low_4 (x y rho asr Phix Phiy : R) (nodes : list NodeS) :
  Rabs rho <= 55/1000 -> bpow radix2 (-52) <= Rabs rho ->
  dom x -> dom y -> 0 <= Phix <= 1 -> 0 <= Phiy <= 1 -> asr = rndF (asin rho) ->
  List.Forall2 node_enc nodes dats_4 -> (length nodes <= 24)%nat ->
  0 <= Phix * Phiy + Iint (x * x + y * y) (x * y) (asin rho) / (2 * PI) <= 1 ->
  Rabs (Iint (x * x + y * y) (x * y) asr - asr / 2 * sumR (map (vn x y asr) nodes)) <= trunc_bound A4 R4 4 ->
  Rabs (Rhat x y asr nodes Phix Phiy - (Phix * Phiy + Iint (x * x + y * y) (x * y) (asin rho) / (2 * PI))) <= 247 / 10 ^ 18.
Proof.
  intros. eapply (low_rule x y rho asr (55/1000) A4 (trunc_bound A4 R4 4)
    (681 / 10 ^ 20) (161 / 10 ^ 19) (569 / 10 ^ 21) (247 / 10 ^ 18) Phix Phiy (-4)%Z nodes dats_4); try assumption.
  - destruct (asin_cover_4) as [Hc _]. lra.
  - unfold A4. lra.
  - unfold A4. lra.
  - lia.
  - lia.
  - unfold A4. simpl. lra.
  - exact dat_ok_4.
  - exact br_ok_4.
  - exact sum_4.
  - exact trunc_4.
  - exact shift_4.
  - exact bd_4.
Qed.

Lemma dat_ok_6 : List.Forall (dat_ok A6) dats_6.
Proof. unfold dats_6. all_dats. Qed.
Lemma br_ok_6 : List.Forall (br_ok A6 B0) dats_6.
Proof. unfold dats_6. all_brs. Qed.
Lemma sum_6 : A6 / (4 * PI) * sumD (gcl A6 B0) dats_6 <= 252 / 10 ^ 19.
Proof. unfold dats_6. simpl. unfold A6. sum_goal. Qed.
Lemma trunc_6 : trunc_bound A6 R6 6 / (2 * PI) <= 154 / 10 ^ 19.
Proof. unfold trunc_bound, A6, R6. interval with (i_prec 64). Qed.
Lemma shift_6 : bpow radix2 (-2 - 54) / (2 * PI) <= 228 / 10 ^ 20.
Proof. simpl. interval with (i_prec 64). Qed.
Lemma bd_6 : 4 * bpow radix2 (-54) + (252 / 10 ^ 19) + 1000 * z + (154 / 10 ^ 19) + (228 / 10 ^ 20) <= 267 / 10 ^ 18.
Proof. unfold z. simpl. interval with (i_prec 100). Qed.

Theorem low_6 (x y rho asr Phix Phiy : R) (nodes : list NodeS) :
  Rabs rho <= 2/10 -> bpow radix2 (-52) <= Rabs rho ->
  dom x -> dom y -> 0 <= Phix <= 1 -> 0 <= Phiy <= 1 -> asr = rndF (asin rho) ->
  List.Forall2 node_enc nodes dats_6 -> (length nodes <= 24)%nat ->
  0 <= Phix * Phiy + Iint (x * x + y * y) (x * y) (asin rho) / (2 * PI) <= 1 ->
  Rabs (Iint (x * x + y * y) (x * y) asr - asr / 2 * sumR (map (vn x y asr) nodes)) <= trunc_bound A6 R6 6 ->
  Rabs (Rhat x y asr nodes Phix Phiy - (Phix * Phiy + Iint (x * x + y * y) (x * y) (asin rho) / (2 * PI))) <= 267 / 10 ^ 18.
Proof.
  intros. eapply (low_rule x y rho asr (2/10) A6 (trunc_bound A6 R6 6)
    (252 / 10 ^ 19) (154 / 10 ^ 19) (228 / 10 ^ 20) (267 / 10 ^ 18) Phix Phiy (-2)%Z nodes dats_6); try assumption.
  - destruct (asin_cover_6) as [Hc _]. lra.
  - unfold A6. lra.
  - unfold A6. lra.
  - lia.
  - lia.
  - unfold A6. simpl. lra.
  - exact dat_ok_6.
  - exact br_ok_6.
  - exact sum_6.
  - exact trunc_6.
  - exact shift_6.
  - exact bd_6.
Qed.

Lemma dat_ok_8 : List.Forall (dat_ok A8) dats_8.
Proof. unfold dats_8. all_dats. Qed.
Lemma br_ok_8 : List.Forall (br_ok A8 B0) dats_8.
Proof. unfold dats_8. all_brs. Qed.
Lemma sum_8 : A8 / (4 * PI) * sumD (gcl A8 B0) dats_8 <= 505 / 10 ^ 19.
Proof. unfold dats_8. simpl. unfold A8. sum_goal. Qed.
Lemma trunc_8 : trunc_bound A8 R8 8 / (2 * PI) <= 162 / 10 ^ 19.
Proof. unfold trunc_bound, A8, R8. interval with (i_prec 64). Qed.
Lemma shift_8 : bpow radix2 (-1 - 54) / (2 * PI) <= 455 / 10 ^ 20.
Proof. simpl. interval with (i_prec 64). Qed.
Lemma bd_8 : 4 * bpow radix2 (-54) + (505 / 10 ^ 19) + 1000 * z + (162 / 10 ^ 19) + (455 / 10 ^ 20) <= 295 / 10 ^ 18.
Proof. unfold z. simpl. interval with (i_prec 100). Qed.

Theorem low_8 (x y rho asr Phix Phiy : R) (nodes : list NodeS) :
  Rabs rho <= 38/100 -> bpow radix2 (-52) <= Rabs rho ->
  dom x -> dom y -> 0 <= Phix <= 1 -> 0 <= Phiy <= 1 -> asr = rndF (asin rho) ->
  List.Forall2 node_enc nodes dats_8 -> (length nodes <= 24)%nat ->
  0 <= Phix * Phiy + Iint (x * x + y * y) (x * y) (asin rho) / (2 * PI) <= 1 ->
  Rabs (Iint (x * x + y * y) (x * y) asr - asr / 2 * sumR (map (vn x y asr) nodes)) <= trunc_bound A8 R8 8 ->
  Rabs (Rhat x y asr nodes Phix Phiy - (Phix * Phiy + Iint (x * x + y * y) (x * y) (asin rho) / (2 * PI))) <= 295 / 10 ^ 18.
Proof.
  intros. eapply (low_rule x y rho asr (38/100) A8 (trunc_bound A8 R8 8)
    (505 / 10 ^ 19) (162 / 10 ^ 19) (455 / 10 ^ 20) (295 / 10 ^ 18) Phix Phiy (-1)%Z nodes dats_8); try assumption.
  - destruct (asin_cover_8) as [Hc _]. lra.
  - unfold A8. lra.
  - unfold A8. lra.
  - lia.
  - lia.
  - unfold A8. simpl. lra.
  - exact dat_ok_8.
  - exact br_ok_8.
  - exact sum_8.
  - exact trunc_8.
  - exact shift_8.
  - exact bd_8.
Qed.

Lemma dat_ok_10 : List.Forall (dat_ok A10) dats_10.
Proof. unfold dats_10. all_dats. Qed.
Lemma br_ok_10 : List.Forall (br_ok A10 B0) dats_10.
Proof. unfold dats_10. all_brs. Qed.
Lemma sum_10 : A10 / (4 * PI) * sumD (gcl A10 B0) dats_10 <= 780 / 10 ^ 19.
Proof. unfold dats_10. simpl. unfold A10. sum_goal. Qed.
Lemma trunc_10 : trunc_bound A10 R10 10 / (2 * PI) <= 164 / 10 ^ 19.
Proof. unfold trunc_bound, A10, R10. interval with (i_prec 64). Qed.
Lemma shift_10 : bpow radix2 (0 - 54) / (2 * PI) <= 910 / 10 ^ 20.
Proof. simpl. interval with (i_prec 64). Qed.
Lemma bd_10 : 4 * bpow radix2 (-54) + (780 / 10 ^ 19) + 1000 * z + (164 / 10 ^ 19) + (910 / 10 ^ 20) <= 328 / 10 ^ 18.
Proof. unfold z. simpl. interval with (i_prec 100). Qed.

Theorem low_10 (x y rho asr Phix Phiy : R) (nodes : list NodeS) :
  Rabs rho <= 54/100 -> bpow radix2 (-52) <= Rabs rho ->
  dom x -> dom y -> 0 <= Phix <= 1 -> 0 <= Phiy <= 1 -> asr = rndF (asin rho) ->
  List.Forall2 node_enc nodes dats_10 -> (length nodes <= 24)%nat ->
  0 <= Phix * Phiy + Iint (x * x + y * y) (x * y) (asin rho) / (2 * PI) <= 1 ->
  Rabs (Iint (x * x + y * y) (x * y) asr - asr / 2 * sumR (map (vn x y asr) nodes)) <= trunc_bound A10 R10 10 ->
  Rabs (Rhat x y asr nodes Phix Phiy - (Phix * Phiy + Iint (x * x + y * y) (x * y) (asin rho) / (2 * PI))) <= 328 / 10 ^ 18.
Proof.
  intros. eapply (low_rule x y rho asr (54/100) A10 (trunc_bound A10 R10 10)
    (780 / 10 ^ 19) (164 / 10 ^ 19) (910 / 10 ^ 20) (328 / 10 ^ 18) Phix Phiy (0)%Z nodes dats_10); try assumption.
  - destruct (asin_cover_10) as [Hc _]. lra.
  - unfold A10. lra.
  - unfold A10. lra.
  - lia.
  - lia.
  - unfold A10. simpl. lra.
  - exact dat_ok_10.
  - exact br_ok_10.
  - exact sum_10.
  - exact trunc_10.
  - exact shift_10.
  - exact bd_10.
Qed.

Lemma dat_ok_12 : List.Forall (dat_ok A12) dats_12.
Proof. unfold dats_12. all_dats. Qed.
Lemma br_ok_12 : List.Forall (br_ok A12 B0) dats_12.
Proof. unfold dats_12. all_brs. Qed.
Lemma sum_12 : A12 / (4 * PI) * sumD (gcl A12 B0) dats_12 <= 106 / 10 ^ 18.
Proof. unfold dats_12. simpl. unfold A12. sum_goal. Qed.
Lemma trunc_12 : trunc_bound A12 R12 12 / (2 * PI) <= 168 / 10 ^ 19.
Proof. unfold trunc_bound, A12, R12. interval with (i_prec 64). Qed.
Lemma shift_12 : bpow radix2 (0 - 54) / (2 * PI) <= 910 / 10 ^ 20.
Proof. simpl. interval with (i_prec 64). Qed.
Lemma bd_12 : 4 * bpow radix2 (-54) + (106 / 10 ^ 18) + 1000 * z + (168 / 10 ^ 19) + (910 / 10 ^ 20) <= 356 / 10 ^ 18.
Proof. unfold z. simpl. interval with (i_prec 100). Qed.

Theorem low_12 (x y rho asr Phix Phiy : R) (nodes : list NodeS) :
  Rabs rho <= 66/100 -> bpow radix2 (-52) <= Rabs rho ->
  dom x -> dom y -> 0 <= Phix <= 1 -> 0 <= Phiy <= 1 -> asr = rndF (asin rho) ->
  List.Forall2 node_enc nodes dats_12 -> (length nodes <= 24)%nat ->
  0 <= Phix * Phiy + Iint (x * x + y * y) (x * y) (asin rho) / (2 * PI) <= 1 ->
  Rabs (Iint (x * x + y * y) (x * y) asr - asr / 2 * sumR (map (vn x y asr) nodes)) <= trunc_bound A12 R12 12 ->
  Rabs (Rhat x y asr nodes Phix Phiy - (Phix * Phiy + Iint (x * x + y * y) (x * y) (asin rho) / (2 * PI))) <= 356 / 10 ^ 18.
Proof.
  intros. eapply (low_rule x y rho asr (66/100) A12 (trunc_bound A12 R12 12)
    (106 / 10 ^ 18) (168 / 10 ^ 19) (910 / 10 ^ 20) (356 / 10 ^ 18) Phix Phiy (0)%Z nodes dats_12); try assumption.
  - destruct (asin_cover_12) as [Hc _]. lra.
  - unfold A12. lra.
  - unfold A12. lra.
  - lia.
  - lia.
  - unfold A12. simpl. lra.
  - exact dat_ok_12.
  - exact br_ok_12.
  - exact sum_12.
  - exact trunc_12.
  - exact shift_12.
  - exact bd_12.
Qed.

Lemma dat_ok_14 : List.Forall (dat_ok A14) dats_14.
Proof. unfold dats_14. all_dats. Qed.
Lemma br_ok_14 : List.Forall (br_ok A14 B0) dats_14.
Proof. unfold dats_14. all_brs. Qed.
Lemma sum_14 : A14 / (4 * PI) * sumD (gcl A14 B0) dats_14 <= 135 / 10 ^ 18.
Proof. unfold dats_14. simpl. unfold A14. sum_goal. Qed.
Lemma trunc_14 : trunc_bound A14 R14 14 / (2 * PI) <= 161 / 10 ^ 19.
Proof. unfold trunc_bound, A14, R14. interval with (i_prec 64). Qed.
Lemma shift_14 : bpow radix2 (0 - 54) / (2 * PI) <= 910 / 10 ^ 20.
Proof. simpl. interval with (i_prec 64). Qed.
Lemma bd_14 : 4 * bpow radix2 (-54) + (135 / 10 ^ 18) + 1000 * z + (161 / 10 ^ 19) + (910 / 10 ^ 20) <= 385 / 10 ^ 18.
Proof. unfold z. simpl. interval with (i_prec 100). Qed.

Theorem low_14 (x y rho asr Phix Phiy : R) (nodes : list NodeS) :
  Rabs rho <= 75/100 -> bpow radix2 (-52) <= Rabs rho ->
  dom x -> dom y -> 0 <= Phix <= 1 -> 0 <= Phiy <= 1 -> asr = rndF (asin rho) ->
  List.Forall2 node_enc nodes dats_14 -> (length nodes <= 24)%nat ->
  0 <= Phix * Phiy + Iint (x * x + y * y) (x * y) (asin rho) / (2 * PI) <= 1 ->
  Rabs (Iint (x * x + y * y) (x * y) asr - asr / 2 * sumR (map (vn x y asr) nodes)) <= trunc_bound A14 R14 14 ->
  Rabs (Rhat x y asr nodes Phix Phiy - (Phix * Phiy + Iint (x * x + y * y) (x * y) (asin rho) / (2 * PI))) <= 385 / 10 ^ 18.
Proof.
  intros. eapply (low_rule x y rho asr (75/100) A14 (trunc_bound A14 R14 14)
    (135 / 10 ^ 18) (161 / 10 ^ 19) (910 / 10 ^ 20) (385 / 10 ^ 18) Phix Phiy (0)%Z nodes dats_14); try assumption.
  - destruct (asin_cover_14) as [Hc _]. lra.
  - unfold A14. lra.
  - unfold A14. lra.
  - lia.
  - lia.
  - unfold A14. simpl. lra.
  - exact dat_ok_14.
  - exact br_ok_14.
  - exact sum_14.
  - exact trunc_14.
  - exact shift_14.
  - exact bd_14.
Qed.

Lemma dat_ok_16 : List.Forall (dat_ok A16) dats_16.
Proof. unfold dats_16. all_dats. Qed.
Lemma br_ok_16 : List.Forall (br_ok A16 B0) dats_16.
Proof. unfold dats_16. all_brs. Qed.
Lemma sum_16 : A16 / (4 * PI) * sumD (gcl A16 B0) dats_16 <= 162 / 10 ^ 18.
Proof. unfold dats_16. simpl. unfold A16. sum_goal. Qed.
Lemma trunc_16 : trunc_bound A16 R16 16 / (2 * PI) <= 153 / 10 ^ 19.
Proof. unfold trunc_bound, A16, R16. interval with (i_prec 64). Qed.
Lemma shift_16 : bpow radix2 (0 - 54) / (2 * PI) <= 910 / 10 ^ 20.
Proof. simpl. interval with (i_prec 64). Qed.
Lemma bd_16 : 4 * bpow radix2 (-54) + (162 / 10 ^ 18) + 1000 * z + (153 / 10 ^ 19) + (910 / 10 ^ 20) <= 411 / 10 ^ 18.
Proof. unfold z. simpl. interval with (i_prec 100). Qed.

Theorem low_16 (x y rho asr Phix Phiy : R) (nodes : list NodeS) :
  Rabs rho <= 81/100 -> bpow radix2 (-52) <= Rabs rho ->
  dom x -> dom y -> 0 <= Phix <= 1 -> 0 <= Phiy <= 1 -> asr = rndF (asin rho) ->
  List.Forall2 node_enc nodes dats_16 -> (length nodes <= 24)%nat ->
  0 <= Phix * Phiy + Iint (x * x + y * y) (x * y) (asin rho) / (2 * PI) <= 1 ->
  Rabs (Iint (x * x + y * y) (x * y) asr - asr / 2 * sumR (map (vn x y asr) nodes)) <= trunc_bound A16 R16 16 ->
  Rabs (Rhat x y asr nodes Phix Phiy - (Phix * Phiy + Iint (x * x + y * y) (x * y) (asin rho) / (2 * PI))) <= 411 / 10 ^ 18.
Proof.
  intros. eapply (low_rule x y rho asr (81/100) A16 (trunc_bound A16 R16 16)
    (162 / 10 ^ 18) (153 / 10 ^ 19) (910 / 10 ^ 20) (411 / 10 ^ 18) Phix Phiy (0)%Z nodes dats_16); try assumption.
  - destruct (asin_cover_16) as [Hc _]. lra.
  - unfold A16. lra.
  - unfold A16. lra.
  - lia.
  - lia.
  - unfold A16. simpl. lra.
  - exact dat_ok_16.
  - exact br_ok_16.
  - exact sum_16.
  - exact trunc_16.
  - exact shift_16.
  - exact bd_16.
Qed.

Lemma dat_ok_20 : List.Forall (dat_ok A20) dats_20.
Proof. unfold dats_20. all_dats. Qed.
Lemma br_ok_20 : List.Forall (br_ok A20 B0) dats_20.
Proof. unfold dats_20. all_brs. Qed.
Lemma sum_20 : A20 / (4 * PI) * sumD (gcl A20 B0) dats_20 <= 222 / 10 ^ 18.
Proof. unfold dats_20. simpl. unfold A20. sum_goal. Qed.
Lemma trunc_20 : trunc_bound A20 R20 20 / (2 * PI) <= 133 / 10 ^ 19.
Proof. unfold trunc_bound, A20, R20. interval with (i_prec 64). Qed.
Lemma shift_20 : bpow radix2 (1 - 54) / (2 * PI) <= 182 / 10 ^ 19.
Proof. simpl. interval with (i_prec 64). Qed.
Lemma bd_20 : 4 * bpow radix2 (-54) + (222 / 10 ^ 18) + 1000 * z + (133 / 10 ^ 19) + (182 / 10 ^ 19) <= 478 / 10 ^ 18.
Proof. unfold z. simpl. interval with (i_prec 100). Qed.

Theorem low_20 (x y rho asr Phix Phiy : R) (nodes : list NodeS) :
  Rabs rho <= 89/100 -> bpow radix2 (-52) <= Rabs rho ->
  dom x -> dom y -> 0 <= Phix <= 1 -> 0 <= Phiy <= 1 -> asr = rndF (asin rho) ->
  List.Forall2 node_enc nodes dats_20 -> (length nodes <= 24)%nat ->
  0 <= Phix * Phiy + Iint (x * x + y * y) (x * y) (asin rho) / (2 * PI) <= 1 ->
  Rabs (Iint (x * x + y * y) (x * y) asr - asr / 2 * sumR (map (vn x y asr) nodes)) <= trunc_bound A20 R20 20 ->
  Rabs (Rhat x y asr nodes Phix Phiy - (Phix * Phiy + Iint (x * x + y * y) (x * y) (asin rho) / (2 * PI))) <= 478 / 10 ^ 18.
Proof.
  intros. eapply (low_rule x y rho asr (89/100) A20 (trunc_bound A20 R20 20)
    (222 / 10 ^ 18) (133 / 10 ^ 19) (182 / 10 ^ 19) (478 / 10 ^ 18) Phix Phiy (1)%Z nodes dats_20); try assumption.
  - destruct (asin_cover_20) as [Hc _]. lra.
  - unfold A20. lra.
  - unfold A20. lra.
  - lia.
  - lia.
  - unfold A20. simpl. lra.
  - exact dat_ok_20.
  - exact br_ok_20.
  - exact sum_20.
  - exact trunc_20.
  - exact shift_20.
  - exact bd_20.
Qed.

Lemma dat_ok_24 : List.Forall (dat_ok A24) dats_24.
Proof. unfold dats_24. all_dats. Qed.
Lemma br_ok_24 : List.Forall (br_ok A24 B0) dats_24.
Proof. unfold dats_24. all_brs. Qed.
Lemma sum_24 : A24 / (4 * PI) * sumD (gcl A24 B0) dats_24 <= 273 / 10 ^ 18.
Proof. unfold dats_24. simpl. unfold A24. sum_goal. Qed.
Lemma trunc_24 : trunc_bound A24 R24 24 / (2 * PI) <= 123 / 10 ^ 19.
Proof. unfold trunc_bound, A24, R24. interval with (i_prec 64). Qed.
Lemma shift_24 : bpow radix2 (1 - 54) / (2 * PI) <= 182 / 10 ^ 19.
Proof. simpl. interval with (i_prec 64). Qed.
Lemma bd_24 : 4 * bpow radix2 (-54) + (273 / 10 ^ 18) + 1000 * z + (123 / 10 ^ 19) + (182 / 10 ^ 19) <= 529 / 10 ^ 18.
Proof. unfold z. simpl. interval with (i_prec 100). Qed.

Theorem low_24 (x y rho asr Phix Phiy : R) (nodes : list NodeS) :
  Rabs rho <= 925/1000 -> bpow radix2 (-52) <= Rabs rho ->
  dom x -> dom y -> 0 <= Phix <= 1 -> 0 <= Phiy <= 1 -> asr = rndF (asin rho) ->
  List.Forall2 node_enc nodes dats_24 -> (length nodes <= 24)%nat ->
  0 <= Phix * Phiy + Iint (x * x + y * y) (x * y) (asin rho) / (2 * PI) <= 1 ->
  Rabs (Iint (x * x + y * y) (x * y) asr - asr / 2 * sumR (map (vn x y asr) nodes)) <= trunc_bound A24 R24 24 ->
  Rabs (Rhat x y asr nodes Phix Phiy - (Phix * Phiy + Iint (x * x + y * y) (x * y) (asin rho) / (2 * PI))) <= 529 / 10 ^ 18.
Proof.
  intros. eapply (low_rule x y rho asr (925/1000) A24 (trunc_bound A24 R24 24)
    (273 / 10 ^ 18) (123 / 10 ^ 19) (182 / 10 ^ 19) (529 / 10 ^ 18) Phix Phiy (1)%Z nodes dats_24); try assumption.
  - destruct (asin_cover_24) as [Hc _]. lra.
  - unfold A24. lra.
  - unfold A24. lra.
  - lia.
  - lia.
  - unfold A24. simpl. lra.
  - exact dat_ok_24.
  - exact br_ok_24.
  - exact sum_24.
  - exact trunc_24.
  - exact shift_24.
  - exact bd_24.
Qed.
