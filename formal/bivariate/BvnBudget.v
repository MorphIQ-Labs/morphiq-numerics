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
Require Import BvnRound BvnQ BvnArg BvnNode BvnTrig BvnLow BvnSum BvnQuadG BvnTail BvnRule BvnIntegral BvnFinal BvnTop BvnLowRule BvnEllipse BvnRules BvnData.
Open Scope R_scope.

Ltac dat_goals :=
  unfold dat_ok, theta_of, sgs_of, u; cbn [dtaulo dtauhi dwhi dk dbr]; simpl;
  repeat split; try lia; interval with (i_prec 64).
Ltac all_dats := repeat (apply List.Forall_cons; [dat_goals |]); apply List.Forall_nil.
Ltac br_goals :=
  unfold br_ok, theta_of, B0, u; cbn [dtaulo dtauhi dwhi dk dbr]; simpl;
  split; intros Hbr; first [discriminate Hbr | interval with (i_prec 64)].
Ltac all_brs := repeat (apply List.Forall_cons; [br_goals |]); apply List.Forall_nil.
Ltac sum_goal :=
  unfold gcl, theta_of, B0, u; cbn [dtaulo dtauhi dwhi dk dbr]; simpl; interval with (i_prec 64).

Lemma dat_ok_6 : List.Forall (dat_ok A6) dats_6.
Proof. unfold dats_6. all_dats. Qed.
Lemma br_ok_6 : List.Forall (br_ok A6 B0) dats_6.
Proof. unfold dats_6. all_brs. Qed.
Lemma sum_6 : A6 / (4 * PI) * sumD (gcl A6 B0) dats_6 <= 214 / 10 ^ 19.
Proof. unfold dats_6. simpl. unfold A6. sum_goal. Qed.
Lemma trunc_6 : trunc_bound A6 R6 6 / (2 * PI) <= 154 / 10 ^ 19.
Proof. unfold trunc_bound, A6, R6. interval with (i_prec 64). Qed.
Lemma shift_6 : (bpow radix2 (-2 - 54) + bpow radix2 (-62) * bpow radix2 (-2)) / (2 * PI) <= 229 / 10 ^ 20.
Proof. simpl. interval with (i_prec 64). Qed.
Lemma bd_6 : bpow radix2 (-54) + bpow radix2 (-900) + bpow radix2 (-90) + 2 * eP + (214 / 10 ^ 19) + 200 * z + (154 / 10 ^ 19) + (229 / 10 ^ 20) <= 207 / 10 ^ 18.
Proof. unfold eP, z. simpl. interval with (i_prec 100). Qed.

Theorem low_6 (expI sinI : R -> R) (x y rho asr Phix Phiy pxI pyI : R) (nodes : list NodeS) :
  exp_contract expI -> sin_contract sinI ->
  Rabs rho <= 2/10 -> bpow radix2 (-52) <= Rabs rho ->
  fmtF x -> fmtF y -> Rabs x <= 64 -> Rabs y <= 64 ->
  0 <= Phix <= 1 -> 0 <= Phiy <= 1 -> fmtF pxI -> fmtF pyI -> 0 <= pxI <= 1 -> 0 <= pyI <= 1 ->
  Rabs (pxI - Phix) <= eP -> Rabs (pyI - Phiy) <= eP ->
  (exists Za, asr = rndF Za /\ Rabs (Za - asin rho) <= bpow radix2 (-62) * Rabs (asin rho)) ->
  List.Forall2 (ok A6 (rndF (asr / (2 * TAU)))) nodes dats_6 -> (length nodes <= 24)%nat ->
  0 <= Phix * Phiy + Iint (x * x + y * y) (x * y) (asin rho) / (2 * PI) <= 1 ->
  Rabs (Iint (x * x + y * y) (x * y) asr - asr / 2 * sumR (map (fun n => nW n * exp (- Qn x y asr n)) nodes)) <= trunc_bound A6 R6 6 ->
  Rabs (Rhat expI sinI x y asr nodes pxI pyI - (Phix * Phiy + Iint (x * x + y * y) (x * y) (asin rho) / (2 * PI))) <= 207 / 10 ^ 18.
Proof.
  intros Hexp Hsin Hrho Hrlow Fx Fy Hx Hy HPx HPy Fpx Fpy Hpx Hpy Epx Epy Hasin Hall Hlen Hprob HT1.
  assert (HAc : sin A6 >= 2/10 + 2 / 10000) by (destruct (asin_cover_6) as [Hc _]; exact Hc).
  exact (low_rule expI sinI x y rho asr (2/10) A6 (trunc_bound A6 R6 6)
    (214 / 10 ^ 19) (154 / 10 ^ 19) (229 / 10 ^ 20) (207 / 10 ^ 18) (-2)%Z pxI pyI Phix Phiy nodes dats_6
    Hexp Hsin ltac:(lra) ltac:(unfold A6; lra) ltac:(unfold A6; lra) ltac:(lia) ltac:(lia) ltac:(unfold A6; simpl; lra)
    dat_ok_6 br_ok_6 sum_6 ltac:(lra) trunc_6 shift_6 bd_6
    Hrho Hrlow Fx Fy Hx Hy HPx HPy Fpx Fpy Hpx Hpy Epx Epy Hasin Hall Hlen Hprob HT1).
Qed.

Lemma dat_ok_8 : List.Forall (dat_ok A8) dats_8.
Proof. unfold dats_8. all_dats. Qed.
Lemma br_ok_8 : List.Forall (br_ok A8 B0) dats_8.
Proof. unfold dats_8. all_brs. Qed.
Lemma sum_8 : A8 / (4 * PI) * sumD (gcl A8 B0) dats_8 <= 420 / 10 ^ 19.
Proof. unfold dats_8. simpl. unfold A8. sum_goal. Qed.
Lemma trunc_8 : trunc_bound A8 R8 8 / (2 * PI) <= 162 / 10 ^ 19.
Proof. unfold trunc_bound, A8, R8. interval with (i_prec 64). Qed.
Lemma shift_8 : (bpow radix2 (-1 - 54) + bpow radix2 (-62) * bpow radix2 (-1)) / (2 * PI) <= 457 / 10 ^ 20.
Proof. simpl. interval with (i_prec 64). Qed.
Lemma bd_8 : bpow radix2 (-54) + bpow radix2 (-900) + bpow radix2 (-90) + 2 * eP + (420 / 10 ^ 19) + 200 * z + (162 / 10 ^ 19) + (457 / 10 ^ 20) <= 231 / 10 ^ 18.
Proof. unfold eP, z. simpl. interval with (i_prec 100). Qed.

Theorem low_8 (expI sinI : R -> R) (x y rho asr Phix Phiy pxI pyI : R) (nodes : list NodeS) :
  exp_contract expI -> sin_contract sinI ->
  Rabs rho <= 38/100 -> bpow radix2 (-52) <= Rabs rho ->
  fmtF x -> fmtF y -> Rabs x <= 64 -> Rabs y <= 64 ->
  0 <= Phix <= 1 -> 0 <= Phiy <= 1 -> fmtF pxI -> fmtF pyI -> 0 <= pxI <= 1 -> 0 <= pyI <= 1 ->
  Rabs (pxI - Phix) <= eP -> Rabs (pyI - Phiy) <= eP ->
  (exists Za, asr = rndF Za /\ Rabs (Za - asin rho) <= bpow radix2 (-62) * Rabs (asin rho)) ->
  List.Forall2 (ok A8 (rndF (asr / (2 * TAU)))) nodes dats_8 -> (length nodes <= 24)%nat ->
  0 <= Phix * Phiy + Iint (x * x + y * y) (x * y) (asin rho) / (2 * PI) <= 1 ->
  Rabs (Iint (x * x + y * y) (x * y) asr - asr / 2 * sumR (map (fun n => nW n * exp (- Qn x y asr n)) nodes)) <= trunc_bound A8 R8 8 ->
  Rabs (Rhat expI sinI x y asr nodes pxI pyI - (Phix * Phiy + Iint (x * x + y * y) (x * y) (asin rho) / (2 * PI))) <= 231 / 10 ^ 18.
Proof.
  intros Hexp Hsin Hrho Hrlow Fx Fy Hx Hy HPx HPy Fpx Fpy Hpx Hpy Epx Epy Hasin Hall Hlen Hprob HT1.
  assert (HAc : sin A8 >= 38/100 + 2 / 10000) by (destruct (asin_cover_8) as [Hc _]; exact Hc).
  exact (low_rule expI sinI x y rho asr (38/100) A8 (trunc_bound A8 R8 8)
    (420 / 10 ^ 19) (162 / 10 ^ 19) (457 / 10 ^ 20) (231 / 10 ^ 18) (-1)%Z pxI pyI Phix Phiy nodes dats_8
    Hexp Hsin ltac:(lra) ltac:(unfold A8; lra) ltac:(unfold A8; lra) ltac:(lia) ltac:(lia) ltac:(unfold A8; simpl; lra)
    dat_ok_8 br_ok_8 sum_8 ltac:(lra) trunc_8 shift_8 bd_8
    Hrho Hrlow Fx Fy Hx Hy HPx HPy Fpx Fpy Hpx Hpy Epx Epy Hasin Hall Hlen Hprob HT1).
Qed.

Lemma dat_ok_12 : List.Forall (dat_ok A12) dats_12.
Proof. unfold dats_12. all_dats. Qed.
Lemma br_ok_12 : List.Forall (br_ok A12 B0) dats_12.
Proof. unfold dats_12. all_brs. Qed.
Lemma sum_12 : A12 / (4 * PI) * sumD (gcl A12 B0) dats_12 <= 820 / 10 ^ 19.
Proof. unfold dats_12. simpl. unfold A12. sum_goal. Qed.
Lemma trunc_12 : trunc_bound A12 R12 12 / (2 * PI) <= 168 / 10 ^ 19.
Proof. unfold trunc_bound, A12, R12. interval with (i_prec 64). Qed.
Lemma shift_12 : (bpow radix2 (0 - 54) + bpow radix2 (-62) * bpow radix2 (0)) / (2 * PI) <= 914 / 10 ^ 20.
Proof. simpl. interval with (i_prec 64). Qed.
Lemma bd_12 : bpow radix2 (-54) + bpow radix2 (-900) + bpow radix2 (-90) + 2 * eP + (820 / 10 ^ 19) + 200 * z + (168 / 10 ^ 19) + (914 / 10 ^ 20) <= 276 / 10 ^ 18.
Proof. unfold eP, z. simpl. interval with (i_prec 100). Qed.

Theorem low_12 (expI sinI : R -> R) (x y rho asr Phix Phiy pxI pyI : R) (nodes : list NodeS) :
  exp_contract expI -> sin_contract sinI ->
  Rabs rho <= 66/100 -> bpow radix2 (-52) <= Rabs rho ->
  fmtF x -> fmtF y -> Rabs x <= 64 -> Rabs y <= 64 ->
  0 <= Phix <= 1 -> 0 <= Phiy <= 1 -> fmtF pxI -> fmtF pyI -> 0 <= pxI <= 1 -> 0 <= pyI <= 1 ->
  Rabs (pxI - Phix) <= eP -> Rabs (pyI - Phiy) <= eP ->
  (exists Za, asr = rndF Za /\ Rabs (Za - asin rho) <= bpow radix2 (-62) * Rabs (asin rho)) ->
  List.Forall2 (ok A12 (rndF (asr / (2 * TAU)))) nodes dats_12 -> (length nodes <= 24)%nat ->
  0 <= Phix * Phiy + Iint (x * x + y * y) (x * y) (asin rho) / (2 * PI) <= 1 ->
  Rabs (Iint (x * x + y * y) (x * y) asr - asr / 2 * sumR (map (fun n => nW n * exp (- Qn x y asr n)) nodes)) <= trunc_bound A12 R12 12 ->
  Rabs (Rhat expI sinI x y asr nodes pxI pyI - (Phix * Phiy + Iint (x * x + y * y) (x * y) (asin rho) / (2 * PI))) <= 276 / 10 ^ 18.
Proof.
  intros Hexp Hsin Hrho Hrlow Fx Fy Hx Hy HPx HPy Fpx Fpy Hpx Hpy Epx Epy Hasin Hall Hlen Hprob HT1.
  assert (HAc : sin A12 >= 66/100 + 2 / 10000) by (destruct (asin_cover_12) as [Hc _]; exact Hc).
  exact (low_rule expI sinI x y rho asr (66/100) A12 (trunc_bound A12 R12 12)
    (820 / 10 ^ 19) (168 / 10 ^ 19) (914 / 10 ^ 20) (276 / 10 ^ 18) (0)%Z pxI pyI Phix Phiy nodes dats_12
    Hexp Hsin ltac:(lra) ltac:(unfold A12; lra) ltac:(unfold A12; lra) ltac:(lia) ltac:(lia) ltac:(unfold A12; simpl; lra)
    dat_ok_12 br_ok_12 sum_12 ltac:(lra) trunc_12 shift_12 bd_12
    Hrho Hrlow Fx Fy Hx Hy HPx HPy Fpx Fpy Hpx Hpy Epx Epy Hasin Hall Hlen Hprob HT1).
Qed.

Lemma dat_ok_14 : List.Forall (dat_ok A14) dats_14.
Proof. unfold dats_14. all_dats. Qed.
Lemma br_ok_14 : List.Forall (br_ok A14 B0) dats_14.
Proof. unfold dats_14. all_brs. Qed.
Lemma sum_14 : A14 / (4 * PI) * sumD (gcl A14 B0) dats_14 <= 101 / 10 ^ 18.
Proof. unfold dats_14. simpl. unfold A14. sum_goal. Qed.
Lemma trunc_14 : trunc_bound A14 R14 14 / (2 * PI) <= 161 / 10 ^ 19.
Proof. unfold trunc_bound, A14, R14. interval with (i_prec 64). Qed.
Lemma shift_14 : (bpow radix2 (0 - 54) + bpow radix2 (-62) * bpow radix2 (0)) / (2 * PI) <= 914 / 10 ^ 20.
Proof. simpl. interval with (i_prec 64). Qed.
Lemma bd_14 : bpow radix2 (-54) + bpow radix2 (-900) + bpow radix2 (-90) + 2 * eP + (101 / 10 ^ 18) + 200 * z + (161 / 10 ^ 19) + (914 / 10 ^ 20) <= 295 / 10 ^ 18.
Proof. unfold eP, z. simpl. interval with (i_prec 100). Qed.

Theorem low_14 (expI sinI : R -> R) (x y rho asr Phix Phiy pxI pyI : R) (nodes : list NodeS) :
  exp_contract expI -> sin_contract sinI ->
  Rabs rho <= 75/100 -> bpow radix2 (-52) <= Rabs rho ->
  fmtF x -> fmtF y -> Rabs x <= 64 -> Rabs y <= 64 ->
  0 <= Phix <= 1 -> 0 <= Phiy <= 1 -> fmtF pxI -> fmtF pyI -> 0 <= pxI <= 1 -> 0 <= pyI <= 1 ->
  Rabs (pxI - Phix) <= eP -> Rabs (pyI - Phiy) <= eP ->
  (exists Za, asr = rndF Za /\ Rabs (Za - asin rho) <= bpow radix2 (-62) * Rabs (asin rho)) ->
  List.Forall2 (ok A14 (rndF (asr / (2 * TAU)))) nodes dats_14 -> (length nodes <= 24)%nat ->
  0 <= Phix * Phiy + Iint (x * x + y * y) (x * y) (asin rho) / (2 * PI) <= 1 ->
  Rabs (Iint (x * x + y * y) (x * y) asr - asr / 2 * sumR (map (fun n => nW n * exp (- Qn x y asr n)) nodes)) <= trunc_bound A14 R14 14 ->
  Rabs (Rhat expI sinI x y asr nodes pxI pyI - (Phix * Phiy + Iint (x * x + y * y) (x * y) (asin rho) / (2 * PI))) <= 295 / 10 ^ 18.
Proof.
  intros Hexp Hsin Hrho Hrlow Fx Fy Hx Hy HPx HPy Fpx Fpy Hpx Hpy Epx Epy Hasin Hall Hlen Hprob HT1.
  assert (HAc : sin A14 >= 75/100 + 2 / 10000) by (destruct (asin_cover_14) as [Hc _]; exact Hc).
  exact (low_rule expI sinI x y rho asr (75/100) A14 (trunc_bound A14 R14 14)
    (101 / 10 ^ 18) (161 / 10 ^ 19) (914 / 10 ^ 20) (295 / 10 ^ 18) (0)%Z pxI pyI Phix Phiy nodes dats_14
    Hexp Hsin ltac:(lra) ltac:(unfold A14; lra) ltac:(unfold A14; lra) ltac:(lia) ltac:(lia) ltac:(unfold A14; simpl; lra)
    dat_ok_14 br_ok_14 sum_14 ltac:(lra) trunc_14 shift_14 bd_14
    Hrho Hrlow Fx Fy Hx Hy HPx HPy Fpx Fpy Hpx Hpy Epx Epy Hasin Hall Hlen Hprob HT1).
Qed.

Lemma dat_ok_20 : List.Forall (dat_ok A20) dats_20.
Proof. unfold dats_20. all_dats. Qed.
Lemma br_ok_20 : List.Forall (br_ok A20 B0) dats_20.
Proof. unfold dats_20. all_brs. Qed.
Lemma sum_20 : A20 / (4 * PI) * sumD (gcl A20 B0) dats_20 <= 148 / 10 ^ 18.
Proof. unfold dats_20. simpl. unfold A20. sum_goal. Qed.
Lemma trunc_20 : trunc_bound A20 R20 20 / (2 * PI) <= 133 / 10 ^ 19.
Proof. unfold trunc_bound, A20, R20. interval with (i_prec 64). Qed.
Lemma shift_20 : (bpow radix2 (1 - 54) + bpow radix2 (-62) * bpow radix2 (1)) / (2 * PI) <= 183 / 10 ^ 19.
Proof. simpl. interval with (i_prec 64). Qed.
Lemma bd_20 : bpow radix2 (-54) + bpow radix2 (-900) + bpow radix2 (-90) + 2 * eP + (148 / 10 ^ 18) + 200 * z + (133 / 10 ^ 19) + (183 / 10 ^ 19) <= 348 / 10 ^ 18.
Proof. unfold eP, z. simpl. interval with (i_prec 100). Qed.

Theorem low_20 (expI sinI : R -> R) (x y rho asr Phix Phiy pxI pyI : R) (nodes : list NodeS) :
  exp_contract expI -> sin_contract sinI ->
  Rabs rho <= 89/100 -> bpow radix2 (-52) <= Rabs rho ->
  fmtF x -> fmtF y -> Rabs x <= 64 -> Rabs y <= 64 ->
  0 <= Phix <= 1 -> 0 <= Phiy <= 1 -> fmtF pxI -> fmtF pyI -> 0 <= pxI <= 1 -> 0 <= pyI <= 1 ->
  Rabs (pxI - Phix) <= eP -> Rabs (pyI - Phiy) <= eP ->
  (exists Za, asr = rndF Za /\ Rabs (Za - asin rho) <= bpow radix2 (-62) * Rabs (asin rho)) ->
  List.Forall2 (ok A20 (rndF (asr / (2 * TAU)))) nodes dats_20 -> (length nodes <= 24)%nat ->
  0 <= Phix * Phiy + Iint (x * x + y * y) (x * y) (asin rho) / (2 * PI) <= 1 ->
  Rabs (Iint (x * x + y * y) (x * y) asr - asr / 2 * sumR (map (fun n => nW n * exp (- Qn x y asr n)) nodes)) <= trunc_bound A20 R20 20 ->
  Rabs (Rhat expI sinI x y asr nodes pxI pyI - (Phix * Phiy + Iint (x * x + y * y) (x * y) (asin rho) / (2 * PI))) <= 348 / 10 ^ 18.
Proof.
  intros Hexp Hsin Hrho Hrlow Fx Fy Hx Hy HPx HPy Fpx Fpy Hpx Hpy Epx Epy Hasin Hall Hlen Hprob HT1.
  assert (HAc : sin A20 >= 89/100 + 2 / 10000) by (destruct (asin_cover_20) as [Hc _]; exact Hc).
  exact (low_rule expI sinI x y rho asr (89/100) A20 (trunc_bound A20 R20 20)
    (148 / 10 ^ 18) (133 / 10 ^ 19) (183 / 10 ^ 19) (348 / 10 ^ 18) (1)%Z pxI pyI Phix Phiy nodes dats_20
    Hexp Hsin ltac:(lra) ltac:(unfold A20; lra) ltac:(unfold A20; lra) ltac:(lia) ltac:(lia) ltac:(unfold A20; simpl; lra)
    dat_ok_20 br_ok_20 sum_20 ltac:(lra) trunc_20 shift_20 bd_20
    Hrho Hrlow Fx Fy Hx Hy HPx HPy Fpx Fpy Hpx Hpy Epx Epy Hasin Hall Hlen Hprob HT1).
Qed.

Lemma dat_ok_24 : List.Forall (dat_ok A24) dats_24.
Proof. unfold dats_24. all_dats. Qed.
Lemma br_ok_24 : List.Forall (br_ok A24 B0) dats_24.
Proof. unfold dats_24. all_brs. Qed.
Lemma sum_24 : A24 / (4 * PI) * sumD (gcl A24 B0) dats_24 <= 173 / 10 ^ 18.
Proof. unfold dats_24. simpl. unfold A24. sum_goal. Qed.
Lemma trunc_24 : trunc_bound A24 R24 24 / (2 * PI) <= 123 / 10 ^ 19.
Proof. unfold trunc_bound, A24, R24. interval with (i_prec 64). Qed.
Lemma shift_24 : (bpow radix2 (1 - 54) + bpow radix2 (-62) * bpow radix2 (1)) / (2 * PI) <= 183 / 10 ^ 19.
Proof. simpl. interval with (i_prec 64). Qed.
Lemma bd_24 : bpow radix2 (-54) + bpow radix2 (-900) + bpow radix2 (-90) + 2 * eP + (173 / 10 ^ 18) + 200 * z + (123 / 10 ^ 19) + (183 / 10 ^ 19) <= 372 / 10 ^ 18.
Proof. unfold eP, z. simpl. interval with (i_prec 100). Qed.

Theorem low_24 (expI sinI : R -> R) (x y rho asr Phix Phiy pxI pyI : R) (nodes : list NodeS) :
  exp_contract expI -> sin_contract sinI ->
  Rabs rho <= 925/1000 -> bpow radix2 (-52) <= Rabs rho ->
  fmtF x -> fmtF y -> Rabs x <= 64 -> Rabs y <= 64 ->
  0 <= Phix <= 1 -> 0 <= Phiy <= 1 -> fmtF pxI -> fmtF pyI -> 0 <= pxI <= 1 -> 0 <= pyI <= 1 ->
  Rabs (pxI - Phix) <= eP -> Rabs (pyI - Phiy) <= eP ->
  (exists Za, asr = rndF Za /\ Rabs (Za - asin rho) <= bpow radix2 (-62) * Rabs (asin rho)) ->
  List.Forall2 (ok A24 (rndF (asr / (2 * TAU)))) nodes dats_24 -> (length nodes <= 24)%nat ->
  0 <= Phix * Phiy + Iint (x * x + y * y) (x * y) (asin rho) / (2 * PI) <= 1 ->
  Rabs (Iint (x * x + y * y) (x * y) asr - asr / 2 * sumR (map (fun n => nW n * exp (- Qn x y asr n)) nodes)) <= trunc_bound A24 R24 24 ->
  Rabs (Rhat expI sinI x y asr nodes pxI pyI - (Phix * Phiy + Iint (x * x + y * y) (x * y) (asin rho) / (2 * PI))) <= 372 / 10 ^ 18.
Proof.
  intros Hexp Hsin Hrho Hrlow Fx Fy Hx Hy HPx HPy Fpx Fpy Hpx Hpy Epx Epy Hasin Hall Hlen Hprob HT1.
  assert (HAc : sin A24 >= 925/1000 + 2 / 10000) by (destruct (asin_cover_24) as [Hc _]; exact Hc).
  exact (low_rule expI sinI x y rho asr (925/1000) A24 (trunc_bound A24 R24 24)
    (173 / 10 ^ 18) (123 / 10 ^ 19) (183 / 10 ^ 19) (372 / 10 ^ 18) (1)%Z pxI pyI Phix Phiy nodes dats_24
    Hexp Hsin ltac:(lra) ltac:(unfold A24; lra) ltac:(unfold A24; lra) ltac:(lia) ltac:(lia) ltac:(unfold A24; simpl; lra)
    dat_ok_24 br_ok_24 sum_24 ltac:(lra) trunc_24 shift_24 bd_24
    Hrho Hrlow Fx Fy Hx Hy HPx HPy Fpx Fpy Hpx Hpy Epx Epy Hasin Hall Hlen Hprob HT1).
Qed.
