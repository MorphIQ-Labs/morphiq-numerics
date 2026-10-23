(** The accurate path's sine and cosine series: the Horner form
    [1 - s c1 (1 - s c2 (...))] with [s = r^2] against the Taylor sums, and
    against [sin r], [cos r] with the truncation the 22 and 23 steps leave. *)
From Coq Require Import Reals ZArith Lia Lra Psatz List.
From Flocq Require Import Core.
From Interval Require Import Tactic.
Open Scope R_scope.
Import ListNotations.

(** The Horner form over a list of coefficients. *)
Fixpoint ser (s : R) (cs : list R) : R :=
  match cs with nil => 1 | c :: cs' => 1 - s * c * ser s cs' end.

(** [m] consecutive coefficients [f j, f (j+1), ...]. *)
Fixpoint cs_gen (f : nat -> R) (j m : nat) : list R :=
  match m with O => nil | S m' => f j :: cs_gen f (S j) m' end.

(** [f j * f (j+1) * ... * f (j+i-1)]. *)
Fixpoint prodf (f : nat -> R) (j i : nat) : R :=
  match i with O => 1 | S i' => f j * prodf f (S j) i' end.

Definition f_sin (l : nat) : R := / (INR (2 * l) * INR (2 * l + 1)).
Definition f_cos (l : nat) : R := / (INR (2 * l - 1) * INR (2 * l)).

Lemma sum_shift (g : nat -> R) m : sum_f_R0 g (S m) = g O + sum_f_R0 (fun i => g (S i)) m.
Proof.
  induction m as [ | m IH].
  - simpl. reflexivity.
  - rewrite tech5. rewrite IH. rewrite (tech5 (fun i => g (S i)) m). ring.
Qed.

Lemma ser_closed s f j m : ser s (cs_gen f j m) = sum_f_R0 (fun i => (-1) ^ i * (s ^ i * prodf f j i)) m.
Proof.
  revert j. induction m as [ | m IH]; intros j.
  - simpl. ring.
  - change (ser s (cs_gen f j (S m))) with (1 - s * f j * ser s (cs_gen f (S j) m)).
    rewrite IH. rewrite sum_shift.
    assert (E : sum_f_R0 (fun i => (-1) ^ S i * (s ^ S i * prodf f j (S i))) m
              = (- (s * f j)) * sum_f_R0 (fun i => (-1) ^ i * (s ^ i * prodf f (S j) i)) m).
    { rewrite scal_sum. apply sum_eq. intros i _. change (prodf f j (S i)) with (f j * prodf f (S j) i).
      simpl pow. ring. }
    simpl (prodf f j 0). rewrite E. simpl pow. ring.
Qed.

Lemma INR_fact_pos n : 0 < INR (fact n).
Proof. apply lt_0_INR. apply lt_O_fact. Qed.

Lemma INR_S_pos n : 0 < INR (S n).
Proof. apply lt_0_INR. lia. Qed.

Lemma prodf_sin i : forall j, prodf f_sin (S j) i = INR (fact (2 * j + 1)) / INR (fact (2 * j + 2 * i + 1)).
Proof.
  induction i as [ | i IH]; intros j.
  - change (prodf f_sin (S j) 0) with 1. replace (2 * j + 2 * 0 + 1)%nat with (2 * j + 1)%nat by lia.
    pose proof (INR_fact_pos (2 * j + 1)). unfold Rdiv. rewrite Rinv_r by lra. reflexivity.
  - change (prodf f_sin (S j) (S i)) with (f_sin (S j) * prodf f_sin (S (S j)) i).
    rewrite IH. unfold f_sin.
    assert (E1 : (2 * S j = S (2 * j + 1))%nat) by lia.
    assert (E2 : (2 * S j + 1 = S (S (2 * j + 1)))%nat) by lia.
    assert (E3 : (2 * S j + 2 * i + 1 = 2 * j + 2 * S i + 1)%nat) by lia.
    rewrite E3. rewrite E2. rewrite E1.
    rewrite (fact_simpl (S (2 * j + 1))). rewrite (fact_simpl (2 * j + 1)).
    rewrite !mult_INR.
    pose proof (INR_fact_pos (2 * j + 1)). pose proof (INR_fact_pos (2 * j + 2 * S i + 1)).
    pose proof (INR_S_pos (2 * j + 1)). pose proof (INR_S_pos (S (2 * j + 1))).
    assert (INR (S (S (2 * j + 1))) > 0) by (apply INR_S_pos). 
    field. repeat split; lra.
Qed.

Lemma prodf_cos i : forall j, prodf f_cos (S j) i = INR (fact (2 * j)) / INR (fact (2 * j + 2 * i)).
Proof.
  induction i as [ | i IH]; intros j.
  - change (prodf f_cos (S j) 0) with 1. replace (2 * j + 2 * 0)%nat with (2 * j)%nat by lia.
    pose proof (INR_fact_pos (2 * j)). unfold Rdiv. rewrite Rinv_r by lra. reflexivity.
  - change (prodf f_cos (S j) (S i)) with (f_cos (S j) * prodf f_cos (S (S j)) i).
    rewrite IH. unfold f_cos.
    assert (E1 : (2 * S j - 1 = S (2 * j))%nat) by lia.
    assert (E2 : (2 * S j = S (S (2 * j)))%nat) by lia.
    assert (E3 : (2 * S j + 2 * i = 2 * j + 2 * S i)%nat) by lia.
    rewrite E3. rewrite E1. rewrite E2.
    rewrite (fact_simpl (S (2 * j))). rewrite (fact_simpl (2 * j)).
    rewrite !mult_INR.
    pose proof (INR_fact_pos (2 * j)). pose proof (INR_fact_pos (2 * j + 2 * S i)).
    pose proof (INR_S_pos (2 * j)). pose proof (INR_S_pos (S (2 * j))).
    field. repeat split; lra.
Qed.

Lemma pow_two_i r i : (r * r) ^ i = r ^ (2 * i).
Proof. rewrite Rpow_mult_distr, <- pow_add. f_equal. lia. Qed.

Lemma sin_approx_ser r m : r * ser (r * r) (cs_gen f_sin 1 m) = sin_approx r m.
Proof.
  rewrite ser_closed. rewrite scal_sum. unfold sin_approx. apply sum_eq. intros i _.
  unfold sin_term. replace (prodf f_sin 1 i) with (INR (fact 1) / INR (fact (2 * 0 + 2 * i + 1))) by (symmetry; exact (prodf_sin i 0)).
  rewrite pow_two_i. replace (2 * 0 + 2 * i + 1)%nat with (2 * i + 1)%nat by lia.
  replace (r ^ (2 * i + 1)) with (r ^ (2 * i) * r) by (rewrite pow_add; ring).
  change (fact 1) with 1%nat. simpl INR.
  assert (Hf : INR (fact (2 * i + 1)) <> 0) by (apply not_eq_sym, Rlt_not_eq, INR_fact_pos). field. exact Hf.
Qed.

Lemma cos_approx_ser r m : ser (r * r) (cs_gen f_cos 1 m) = cos_approx r m.
Proof.
  rewrite ser_closed. unfold cos_approx. apply sum_eq. intros i _.
  unfold cos_term. replace (prodf f_cos 1 i) with (INR (fact (2 * 0)) / INR (fact (2 * 0 + 2 * i))) by (symmetry; exact (prodf_cos i 0)).
  rewrite pow_two_i. replace (2 * 0 + 2 * i)%nat with (2 * i)%nat by lia.
  change (fact (2 * 0)) with 1%nat. simpl INR.
  assert (Hf : INR (fact (2 * i)) <> 0) by (apply not_eq_sym, Rlt_not_eq, INR_fact_pos). field. exact Hf.
Qed.

Lemma prodf_sin_small : prodf f_sin 1 22 <= / 2 ^ 186.
Proof. unfold f_sin. cbn [prodf]. simpl INR. interval with (i_prec 300). Qed.

Lemma prodf_cos_small : prodf f_cos 1 24 <= / 2 ^ 202.
Proof. unfold f_cos. cbn [prodf]. simpl INR. interval with (i_prec 300). Qed.

Lemma pi_gt_3 : 3 < PI.
Proof. interval with (i_prec 30). Qed.

Lemma sin_term_prod r m : sin_term r m = (-1) ^ m * (r * ((r * r) ^ m * prodf f_sin 1 m)).
Proof.
  unfold sin_term. rewrite (prodf_sin m 0). rewrite pow_two_i.
  replace (2 * 0 + 2 * m + 1)%nat with (2 * m + 1)%nat by lia.
  replace (r ^ (2 * m + 1)) with (r ^ (2 * m) * r) by (rewrite pow_add; ring).
  replace (INR (fact (2 * 0 + 1))) with 1 by (simpl; ring).
  assert (Hf : INR (fact (2 * m + 1)) <> 0) by (apply not_eq_sym, Rlt_not_eq, INR_fact_pos).
  field. exact Hf.
Qed.

Lemma cos_term_prod r m : cos_term r m = (-1) ^ m * ((r * r) ^ m * prodf f_cos 1 m).
Proof.
  unfold cos_term. rewrite (prodf_cos m 0). rewrite pow_two_i.
  replace (2 * 0 + 2 * m)%nat with (2 * m)%nat by lia.
  replace (INR (fact (2 * 0))) with 1 by (simpl; ring).
  assert (Hf : INR (fact (2 * m)) <> 0) by (apply not_eq_sym, Rlt_not_eq, INR_fact_pos).
  field. exact Hf.
Qed.

(** The 22-step sine series against [sin r]: it overshoots by at most the next term. *)
Theorem sin_trunc r : 0 <= r <= 0.8 ->
  0 <= r * ser (r * r) (cs_gen f_sin 1 22) - sin r <= r * ((r * r) ^ 22 * prodf f_sin 1 22).
Proof.
  intros [H0 H1]. rewrite sin_approx_ser.
  pose proof pi_gt_3 as Pi.
  pose proof (sin_bound r 10 H0 ltac:(lra)) as [Lo Hi].
  change (2 * 10 + 1)%nat with 21%nat in Lo. change (2 * (10 + 1))%nat with 22%nat in Hi.
  assert (Hs : sin_approx r 22 = sin_approx r 21 + sin_term r 22).
  { unfold sin_approx. change 22%nat with (S 21). rewrite tech5. reflexivity. }
  rewrite sin_term_prod in Hs. replace ((-1) ^ 22) with 1 in Hs by ring.
  split; [lra | lra].
Qed.

(** The 23-step cosine series against [cos r]: it undershoots by at most the next term. *)
Theorem cos_trunc r : 0 <= r <= 0.8 ->
  0 <= cos r - ser (r * r) (cs_gen f_cos 1 23) <= (r * r) ^ 24 * prodf f_cos 1 24.
Proof.
  intros [H0 H1]. rewrite cos_approx_ser.
  pose proof pi_gt_3 as Pi.
  pose proof (cos_bound r 11 ltac:(lra) ltac:(lra)) as [Lo Hi].
  change (2 * 11 + 1)%nat with 23%nat in Lo. change (2 * (11 + 1))%nat with 24%nat in Hi.
  assert (Hs : cos_approx r 24 = cos_approx r 23 + cos_term r 24).
  { unfold cos_approx. change 24%nat with (S 23). rewrite tech5. reflexivity. }
  rewrite cos_term_prod in Hs. replace ((-1) ^ 24) with 1 in Hs by ring.
  split; [lra | lra].
Qed.
