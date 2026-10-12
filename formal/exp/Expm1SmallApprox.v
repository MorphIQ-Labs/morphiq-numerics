(** Independent analytic bound for the fast polynomial, with its generated
    binary64 coefficients. The Taylor remainder covers both signs. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Binary64 Require Import IEEE64.
From Interval Require Import Tactic.
Require Import Expm1Tables Expm1Series.
Open Scope R_scope.
Ltac em_coefficients := rewrite em_c3_val, em_c4_val, em_c5_val, em_c6_val,
 em_c7_val, em_c8_val, em_c9_val.
Lemma em_w_range x : Rabs x <= 0.0312501 -> 0.16 <= em_w x <= 0.18.
Proof.
 intros X. apply Rabs_le_inv in X. unfold em_w. em_coefficients.
 interval with (i_prec 120).
Qed.
Lemma em_poly_identity x :
 esum 16 x-1-x-x*x/2-x*x*x*em_w x = x*x*x*em_poly_difference x.
Proof.
 unfold esum. cbn [sum_f_R0]. factorial_reals. small_numerals.
 unfold em_w, em_poly_difference. em_coefficients. field.
Qed.
Lemma em_difference_bound x : Rabs x <= 0.0312501 ->
 Rabs (em_poly_difference x) <= (1035/2^64)*em_w x.
Proof.
 intros X. pose proof (em_w_range x X) as W.
 assert (C : Rabs (em_poly_difference x / em_w x) <= 1035/2^64).
 { apply Rabs_le_inv in X. unfold em_poly_difference, em_w. em_coefficients.
   apply Rabs_le; split; interval with (i_taylor x, i_degree 14, i_bisect x, i_prec 180, i_depth 12). }
 replace (em_poly_difference x) with ((em_poly_difference x/em_w x)*em_w x) by (field; lra).
 rewrite Rabs_mult, (Rabs_pos_eq (em_w x)) by lra.
 apply Rmult_le_compat_r; lra.
Qed.

Theorem em_small_polynomial_bound x : Rabs x <= 0.0312501 ->
 Rabs (exp x-1-x-x*x/2-x*x*x*em_w x) <= (518/2^63)*Rabs (x*x*x*em_w x).
Proof.
 intros X. pose proof (exp_taylor_bound 16 x X) as E.
 pose proof (em_difference_bound x X) as D. pose proof (em_w_range x X) as W.
 assert (F : INR (fact 17) = 355687428096000).
 { factorial_reals. small_numerals. ring. }
 rewrite F in E.
 assert (Er : Rabs (exp x-esum 16 x) <= Rabs (x*x*x)/2^70).
 { apply Rle_trans with (1:=E). rewrite !Rabs_mult.
   replace ((26/25)*Rabs x^17 / 355687428096000)
     with ((Rabs x*Rabs x*Rabs x)*((26/25)*Rabs x^14/(17*16*15*14*13*12*11*10*9*8*7*6*5*4*3*2))) by (simpl pow; field).
   unfold Rdiv at 2. apply Rmult_le_compat_l; [repeat apply Rmult_le_pos; apply Rabs_pos | ].
   pose proof (Rabs_pos x) as P. generalize P,X. generalize (Rabs x). intros a Pa Xa.
   interval with (i_prec 180). }
 replace (exp x-1-x-x*x/2-x*x*x*em_w x) with
   ((exp x-esum 16 x)+(esum 16 x-1-x-x*x/2-x*x*x*em_w x)) by ring.
 rewrite em_poly_identity. apply Rle_trans with (1:=Rabs_triang _ _).
 rewrite Rabs_mult, (Rabs_mult (x*x*x)), (Rabs_pos_eq (em_w x)) by lra.
 pose proof (Rabs_pos (x*x*x)) as P.
 assert (V : Rabs (x*x*x)*Rabs (em_poly_difference x) <= Rabs (x*x*x)*((1035/2^64)*em_w x))
   by (apply Rmult_le_compat_l; assumption).
 assert (C : /2^70 <= (1/2^64)*em_w x).
 { apply Rle_trans with ((1/2^64)*0.16); [interval | apply Rmult_le_compat_l; [interval | lra]]. }
 assert (Cw : Rabs (x*x*x)/2^70 <= Rabs (x*x*x)*((1/2^64)*em_w x)) by (apply Rmult_le_compat_l; assumption).
 nra.
Qed.
