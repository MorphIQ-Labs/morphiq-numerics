(** Analytic error of the shared double-word logarithm polynomial. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
Require Import LnFastTables Ln1pApprox.
Open Scope R_scope.
Ltac lf_coefficients := unfold lf_a3, lf_a4, lf_a5, lf_a6, lf_a7, lf_a8, lf_a9.
Lemma lf_w_range x : Rabs x <= 0.0078126 -> 0.33 <= lf_w x <= 0.34.
Proof. intros X. apply Rabs_le_inv in X. unfold lf_w. lf_coefficients. interval with (i_prec 100). Qed.
Lemma lf_poly_identity x : lser 18 x-x+x*x/2-x*x*x*lf_w x = x*x*x*lf_difference x.
Proof. cbn [lser INR]. unfold lf_w,lf_difference. lf_coefficients. field. Qed.
Lemma lf_difference_bound x : Rabs x <= 0.0078126 ->
 Rabs (lf_difference x) <= (534/2^63)*lf_w x.
Proof.
 intros X. pose proof (lf_w_range x X) as W.
 assert (D : Rabs (lf_difference x/lf_w x) <= 534/2^63).
 { apply Rabs_le_inv in X. unfold lf_difference,lf_w. lf_coefficients.
   apply Rabs_le; split; interval with (i_taylor x, i_degree 16, i_bisect x, i_prec 180, i_depth 12). }
 replace (lf_difference x) with ((lf_difference x/lf_w x)*lf_w x) by (field; lra).
 rewrite Rabs_mult, (Rabs_pos_eq (lf_w x)) by lra. apply Rmult_le_compat_r; lra.
Qed.
Theorem lf_polynomial_bound x : Rabs x <= 0.0078126 ->
 Rabs (ln(1+x)-x+x*x/2-x*x*x*lf_w x) <= (535/2^63)*Rabs (x*x*x*lf_w x).
Proof.
 intros X. pose proof (ln1p_series 18 x ltac:(lra)) as E.
 pose proof (lf_difference_bound x X) as D. pose proof (lf_w_range x X) as W.
 assert (Er : Rabs (ln(1+x)-lser 18 x) <= Rabs (x*x*x)/2^110).
 { apply Rle_trans with (1:=E). rewrite !Rabs_mult.
   replace (Rabs x^(18+1)/(1-Rabs x)) with ((Rabs x*Rabs x*Rabs x)*(Rabs x^16/(1-Rabs x))) by (simpl pow; field; pose proof (Rabs_pos x); lra).
   unfold Rdiv at 2. apply Rmult_le_compat_l; [repeat apply Rmult_le_pos; apply Rabs_pos | ].
   pose proof (Rabs_pos x) as P. generalize P,X. generalize (Rabs x). intros a Pa Xa.
   interval with (i_prec 180). }
 replace (ln(1+x)-x+x*x/2-x*x*x*lf_w x) with
 ((ln(1+x)-lser 18 x)+(lser 18 x-x+x*x/2-x*x*x*lf_w x)) by ring.
 rewrite lf_poly_identity. apply Rle_trans with (1:=Rabs_triang _ _).
 rewrite Rabs_mult, (Rabs_mult (x*x*x)), (Rabs_pos_eq (lf_w x)) by lra.
 pose proof (Rabs_pos (x*x*x)) as P.
 assert (C : /2^110 <= (1/2^63)*lf_w x).
 { apply Rle_trans with ((1/2^63)*0.33); [interval with (i_prec 100) | apply Rmult_le_compat_l; [interval with (i_prec 100) | lra]]. }
 assert (Rabs (x*x*x)/2^110 <= Rabs (x*x*x)*((1/2^63)*lf_w x)) by (apply Rmult_le_compat_l; assumption).
 assert (Rabs (x*x*x)*Rabs (lf_difference x) <= Rabs (x*x*x)*((534/2^63)*lf_w x)) by (apply Rmult_le_compat_l; assumption).
 nra.
Qed.
