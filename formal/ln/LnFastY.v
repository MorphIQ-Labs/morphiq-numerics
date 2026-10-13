(** Reconstruction of ln(y) from the table and exact residual polynomial. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Eft Grid.
From Interval Require Import Tactic.
Require Import LnTables LnTableCheck LnReduction LnFastTables LnFastTableCheck
 LnFastReduced LnFastCompose Ln1pLemmas.
Open Scope R_scope.
Definition lf_table_pair i := let '(h,l):=lf_neg_ln_r i in two_sum64 h l.
Lemma lf_table_pair_ok i : (i<128)%nat ->
 let '(h,l):=lf_table_pair i in finite h /\ finite l /\ B h=rndF(B h+B l) /\
 Rabs(B h)<=2 /\ Rabs(B l)<=4 /\
 Rabs(B h+B l+ln(B (ln_r i)))<=984/2^117*Rabs(ln(B (ln_r i))).
Proof.
 intros I. pose proof (lf_table_all i I) as T. unfold lf_table_ok in T.
 unfold lf_table_pair. destruct (lf_neg_ln_r i) as [a b]. destruct T as [Fa [Fb [Aa [Ab E]]]].
 assert (Al : Rabs(B b)<=1) by (apply Rle_trans with (1:=Ab); interval with (i_prec 80)).
 pose proof (two_sum_ieee a b Fa Fb
  ltac:(apply Rle_trans with 1; [exact Aa | interval with (i_prec 80)])
  ltac:(apply Rle_trans with 1; [exact Al | interval with (i_prec 80)])) as S.
 destruct (two_sum64 a b) as [h l]. destruct S as [Fh [Fl [Vh Vs]]].
 assert (Dw : B h=rndF(B h+B l)) by (rewrite Vs; exact Vh).
 assert (As : Rabs(B h+B l)<=2) by (rewrite Vs; pose proof (Rabs_triang (B a) (B b)); lra).
 assert (H : Rabs(B h)<=2) by (rewrite Dw; apply rnd_bound; [apply (fmt_pow 1); lia | exact As]).
 assert (L : Rabs(B l)<=4).
 { replace (B l) with ((B h+B l)-B h) by ring. apply Rle_trans with (1:=Rabs_triang _ _); rewrite Rabs_Ropp; lra. }
 rewrite <-Vs in E. repeat split; assumption.
Qed.
Definition lf_ln_y y i := let '(a,b):=lf_table_pair i in let '(c,d):=lf_reduced_poly y i in add64 a b c d.
Theorem lf_ln_y_ok y i : (i<128)%nat -> finite y -> ln_lo i<=B y<ln_hi i -> on_grid (-53) (B y) ->
 let '(h,l):=lf_ln_y y i in finite h /\ finite l /\ B h=rndF(B h+B l) /\
 Rabs(B h)<=1 /\ Rabs(B l)<=2 /\ Rabs(B h+B l-ln(B y))<=7/2^67*Rabs(ln(B y)).
Proof.
 intros I Fy Y Gy. destruct (ratios_ok i (B y) I ltac:(assert (0</2^52) by interval with (i_prec 80); lra)) as [Py [Pr [RB RC]]].
 assert (Log : -ln(B (ln_r i))+ln(B y*B (ln_r i))=ln(B y)) by (rewrite ln_mult by lra; ring).
 assert (P : Rabs(ln(B y*B (ln_r i)))<=Rabs(ln(B y))).
 { destruct (Req_dec (B (ln_r i)) 1) as [R1 | R1].
   - rewrite R1,Rmult_1_r; lra.
   - specialize (RB R1). unfold k3b in RB. pose proof (Rabs_pos (ln(B y))); lra. }
 assert (T : Rabs(ln(B (ln_r i)))<=2*Rabs(ln(B y))).
 { replace (ln(B (ln_r i))) with (ln(B y*B (ln_r i))-ln(B y)) by lra.
   apply Rle_trans with (1:=Rabs_triang _ _). rewrite Rabs_Ropp. lra. }
 pose proof (lf_table_pair_ok i I) as TP. pose proof (lf_reduced_poly_ok y i I Fy Y Gy) as PP.
 unfold lf_ln_y. destruct (lf_table_pair i) as [a b]. destruct (lf_reduced_poly y i) as [c d].
 destruct TP as [Fa [Fb [Da [Aa [Ab Ea]]]]]. destruct PP as [Fc [Fd [Dc [Ac [Ad Ec]]]]].
 set (eps:=2*(984/2^117)+3/2^66).
 assert (Ep : 0<=eps<=/100) by (unfold eps; split; interval with (i_prec 180)).
 assert (Err : Rabs(B a+B b- -ln(B (ln_r i)))+Rabs(B c+B d-ln(B y*B (ln_r i)))<=eps*Rabs(ln(B y))).
 { replace (B a+B b- -ln(B (ln_r i))) with (B a+B b+ln(B (ln_r i))) by ring.
   assert (0<=984/2^117) by interval with (i_prec 180). assert (0<=3/2^66) by interval with (i_prec 100). unfold eps; nra. }
 destruct (lf_perturbed_sum (B a+B b) (B c+B d) (-ln(B (ln_r i))) (ln(B y*B (ln_r i))) (ln(B y)) eps Log Ep
   ltac:(rewrite Rabs_Ropp; pose proof (Rabs_pos (ln(B y))); lra) Err) as [C E].
 assert (Big : forall v, Rabs v<=4 -> Rabs v<=bpow radix2 100).
 { intros v V; apply Rle_trans with 4; [exact V | interval with (i_prec 100)]. }
 pose proof (lf_add_pair a b c d Fa Fb Fc Fd Da Dc (Big (B a) ltac:(lra)) (Big (B b) Ab)
  (Big (B c) ltac:(lra)) (Big (B d) ltac:(lra)) C) as A.
 destruct (add64 a b c d) as [h l]. destruct A as [Fh [Fl [Dw [e [Ee Ve]]]]].
 pose proof (lf_rounded_sum _ _ _ eps e (proj1 Ep) E Ee Ve) as Er.
 assert (Bound : Rabs(B h+B l-ln(B y))<=7/2^67*Rabs(ln(B y))).
 { apply Rle_trans with (1:=Er). apply Rmult_le_compat_r; [apply Rabs_pos | unfold eps; interval with (i_prec 200)]. }
 destruct (ln_range i I) as [Lo [Hi _]]. assert (Yb : 0.7<=B y<=1.42) by lra.
 assert (Ly : Rabs(ln(B y))<=/2) by interval with (i_prec 100).
 assert (Small : Rabs(B h+B l)<=1).
 { pose proof (Rabs_triang_inv (B h+B l) (ln(B y))). assert (7/2^67<=1) by interval with (i_prec 100).
   pose proof (Rabs_pos (ln(B y))); nra. }
 assert (H : Rabs(B h)<=1) by (rewrite Dw; apply rnd_bound; [apply (fmt_pow 0); lia | exact Small]).
 assert (L : Rabs(B l)<=2).
 { replace (B l) with ((B h+B l)-B h) by ring. apply Rle_trans with (1:=Rabs_triang _ _); rewrite Rabs_Ropp; lra. }
 repeat split; assumption.
Qed.
