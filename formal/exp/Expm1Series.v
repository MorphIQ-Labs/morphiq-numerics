(** Taylor's theorem for exp on a segment from zero, with either sign of x.
    The remainder includes the exponential factor, not just the first omitted term. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Coquelicot Require Import Coquelicot.
From Flocq Require Import Core.
From Interval Require Import Tactic.
Open Scope R_scope.

Definition esum n x := sum_f_R0 (fun k => x^k / INR (fact k)) n.
Lemma exp_scaled_derive a n t :
 Derive_n (fun z => exp (a*z)) n t = a^n*exp (a*t).
Proof.
 apply is_derive_n_unique. apply is_derive_n_comp_scal.
 - apply filter_forall. intros z [|k] _; [exact I | ]. exists (exp z). exact (is_derive_n_exp (S k) z).
 - apply is_derive_n_exp.
Qed.
Lemma exp_taylor_segment n x : exists t, 0 < t < 1 /\
 exp x = esum n x + x^(S n)/INR(fact(S n))*exp(x*t).
Proof.
 destruct (Taylor_Lagrange (fun z => exp(x*z)) n 0 1 ltac:(lra)) as [t [T E]].
 - intros z _ [|k] _; [exact I | ]. exists (x^(S k)*exp(x*z)). change (is_derive_n (fun z => exp(x*z)) (S k) z (x^(S k)*exp(x*z))). apply is_derive_n_comp_scal.
   + apply filter_forall. intros w [|j] _; [exact I | ]. exists (exp w). exact (is_derive_n_exp (S j) w).
   + apply is_derive_n_exp.
 - exists t. split; [exact T | ]. rewrite Rmult_1_r in E.
   rewrite exp_scaled_derive in E.
   assert (S : sum_f_R0 (fun m => (1-0)^m / INR(fact m)*Derive_n (fun z => exp(x*z)) m 0) n = esum n x).
   { apply sum_eq. intros k _. rewrite exp_scaled_derive, Rmult_0_r, exp_0, Rmult_1_r.
     replace (1-0) with 1 by ring. rewrite pow1. field. apply Rgt_not_eq, lt_0_INR, lt_O_fact. }
   rewrite S in E. replace (1-0) with 1 in E by ring. rewrite pow1 in E.
   rewrite E. f_equal. unfold Rdiv. ring.
Qed.
Theorem exp_taylor_bound n x : Rabs x <= 0.0312501 ->
 Rabs(exp x-esum n x) <= (26/25)*Rabs x^(S n)/INR(fact(S n)).
Proof.
 intros X. destruct (exp_taylor_segment n x) as [t [T E]].
 assert (F : 0 < INR(fact(S n))) by (apply lt_0_INR; apply lt_O_fact).
 assert (B : 0 < exp(x*t) <= 26/25).
 { split; [apply exp_pos | ]. apply Rabs_le_inv in X. interval with (i_prec 80). }
 rewrite E. replace (esum n x + x^S n/INR(fact(S n))*exp(x*t)-esum n x)
   with (x^S n/INR(fact(S n))*exp(x*t)) by ring.
 unfold Rdiv. rewrite !Rabs_mult, Rabs_Rinv, (Rabs_pos_eq (INR (fact (S n)))) by lra.
 rewrite <- RPow_abs, (Rabs_pos_eq (exp (x*t))) by lra.
 assert (P : 0 <= Rabs x^S n / INR(fact(S n))) by (apply Rdiv_le_0_compat; [apply pow_le, Rabs_pos | exact F]).
 unfold Rdiv in P. nra.
Qed.

(** Expand factorials in R, avoiding construction of enormous unary naturals. *)
Lemma INR_fact_succ n : INR (fact (S n)) = INR (S n) * INR (fact n).
Proof. change (INR (S n * fact n) = INR (S n) * INR (fact n)). apply mult_INR. Qed.
Ltac factorial_reals := repeat rewrite INR_fact_succ; change (INR (fact 0)) with 1;
 repeat rewrite INR_IZR_INZ.

Fixpoint small_series (x : R) (c : nat) : R :=
 match c with
 | O => 1
 | S c' => 1 + x / INR (17-c) * small_series x c'
 end.
Ltac small_numerals := repeat match goal with |- context [Z.of_nat ?n] =>
 let v := eval vm_compute in (Z.of_nat n) in change (Z.of_nat n) with v end.

Lemma small_series_polynomial x : esum 16 x = 1 + x * small_series x 15.
Proof.
 unfold esum. cbn [sum_f_R0]. factorial_reals.
 cbn [small_series]. repeat rewrite INR_IZR_INZ. small_numerals. field.
Qed.


Lemma small_series_tail x : Rabs x <= 0.0312501 -> x <> 0 ->
 Rabs (small_series x 15 - (exp x-1)/x) <=
 (26/25)*Rabs x^16 / (17*16*15*14*13*12*11*10*9*8*7*6*5*4*3*2).
Proof.
 intros X X0. pose proof (exp_taylor_bound 16 x X) as E.
 repeat rewrite INR_fact_succ in E. change (INR (fact 0)) with 1 in E.
 repeat rewrite INR_IZR_INZ in E.
 repeat match type of E with context [Z.of_nat ?n] =>
   let v := eval vm_compute in (Z.of_nat n) in change (Z.of_nat n) with v in E end.
 apply (Rmult_le_reg_r (Rabs x)); [apply Rabs_pos_lt; exact X0 | ].
 rewrite <- Rabs_mult.
 replace ((small_series x 15 - (exp x-1)/x)*x) with (esum 16 x-exp x)
   by (rewrite small_series_polynomial; field; exact X0).
 rewrite Rabs_minus_sym.
 apply Rle_trans with (1:=E). right. simpl pow. field.
Qed.

Lemma expm1_ratio_small x : Rabs x <= 0.0312501 -> x <> 0 ->
 0.98 <= (exp x-1)/x <= 1.02.
Proof.
 intros X X0. pose proof (exp_taylor_bound 1 x X) as E.
 assert (S : esum 1 x = 1+x) by (unfold esum; cbn [sum_f_R0]; factorial_reals; small_numerals; field).
 rewrite S in E. change (INR (fact 2)) with 2 in E.
 assert (B : Rabs ((exp x-1)/x-1) <= (26/25)*Rabs x/2).
 { apply (Rmult_le_reg_r (Rabs x)); [apply Rabs_pos_lt; exact X0 | ].
   rewrite <- Rabs_mult. replace (((exp x-1)/x-1)*x) with (exp x-(1+x)) by (field; exact X0).
   apply Rle_trans with (1:=E). right. simpl pow. field. }
 apply Rabs_le_inv in B. lra.
Qed.
