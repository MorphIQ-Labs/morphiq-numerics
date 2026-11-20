(** The actual double-word sine residual assembly on the regular domain. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add.
From Interval Require Import Tactic.
Require Import StageGappa TrigTables TrigError TrigPolynomial TrigTail
 TrigResidualCertificate AsinNormal.
Open Scope R_scope.

Definition trig_sin_residual th tl :=
 let '(_,_,_,tail,_):=trig_tail_eval th in add_f64_64 th tl tail.

Lemma trig_small_perturbation_nonzero h l tail : h<>0 ->
 Rabs l<=Rabs h/4 -> Rabs tail<=Rabs h/4 -> h+l+tail<>0.
Proof.
 intros H L T Zero.
 assert (Positive:0<Rabs h) by (apply Rabs_pos_lt; exact H).
 pose proof (Rabs_triang l tail) as Triangle.
 replace h with (-(l+tail)) in L,T,Positive by lra.
 rewrite Rabs_Ropp in L,T,Positive. lra.
Qed.

Lemma trig_sin_small_nonzero t : t<>0 -> Rabs t<=0.0078126 -> sin t<>0.
Proof.
 intros Nonzero Range.
 destruct (trig_sin_polynomial_model t Range) as [al [Al Value]].
 assert (Factor:0<1+t*t*trig_ps(t*t)*(1+al)).
 { unfold trig_ps. rewrite trig_s0_val,trig_s1_val,trig_s2_val.
   unfold trig_poly_error in Al. interval. }
 rewrite Value. replace (t+t^3*trig_ps(t*t)*(1+al)) with
   (t*(1+t*t*trig_ps(t*t)*(1+al))) by ring.
 apply Rmult_integral_contrapositive_currified; [exact Nonzero|lra].
Qed.

Theorem trig_sin_residual_regular th tl : finite th -> finite tl ->
 /2^60<=Rabs(B th)<=0.0078126 -> Rabs(B tl)<=/2^53*Rabs(B th) ->
 B th=rndF(B th+B tl) -> Rabs(B th+B tl)<=0.0078126 ->
 let '(h,l):=trig_sin_residual th tl in
 finite h /\ finite l /\ B h=rndF(B h+B l) /\
 Rabs(B h+B l-sin(B th+B tl))<=/2^65*Rabs(sin(B th+B tl)).
Proof.
 intros Th Tl Range Low Normal FullRange.
 pose proof (proj2 Range) as Upper.
 assert (ThNonzero:B th<>0).
 { intro Zero. rewrite Zero,Rabs_R0 in Range.
   assert (Positive:0</2^60) by interval. lra. }
 assert (LowQuarter:Rabs(B tl)<=Rabs(B th)/4).
 { assert (Small:/2^53<=/4) by interval. pose proof (Rabs_pos(B th)); nra. }
 assert (TotalNonzero:B th+B tl<>0).
 { pose proof (trig_small_perturbation_nonzero (B th) (B tl) 0 ThNonzero LowQuarter
     ltac:(rewrite Rabs_R0; pose proof (Rabs_pos(B th)); lra)) as N.
   rewrite Rplus_0_r in N; exact N. }
 assert (SinNonzero:sin(B th+B tl)<>0) by (apply trig_sin_small_nonzero; assumption).
 pose proof (trig_tail_evaluation th Th Upper) as Eval.
 pose proof (trig_tail_regular th Th Range) as TailError.
 unfold trig_sin_residual.
 destruct (trig_tail_eval th) as [[[[u ps]pc]tail]ct] eqn:Parts.
 cbn zeta iota in Eval,TailError |- *.
 destruct Eval as [U [Ps [Pc [Tail [Ct Rest]]]]]. destruct TailError as [TailError _].
 destruct (trig_relative_factor (B tail) ((B th)^3*trig_ps(B th*B th)) (/2^50)
   ltac:(interval) TailError) as [et [Et TailValue]].
 assert (TailQuarter:Rabs(B tail)<=Rabs(B th)/4).
 { rewrite TailValue. replace ((B th)^3*trig_ps(B th*B th)*(1+et)) with
     (B th*(B th*B th*trig_ps(B th*B th)*(1+et))) by ring.
   rewrite Rabs_mult. replace (Rabs(B th)/4) with (Rabs(B th)*(/4)) by field.
   apply Rmult_le_compat_l; [apply Rabs_pos|].
   unfold trig_ps. rewrite trig_s0_val,trig_s1_val,trig_s2_val. interval. }
 assert (SumNonzero:B th+B tl+B tail<>0)
   by (apply trig_small_perturbation_nonzero; assumption).
 assert (Bh:Rabs(B th)<=bpow radix2 1018) by (bpow_num; lra).
 assert (Bl:Rabs(B tl)<=bpow radix2 1018) by (bpow_num; lra).
 assert (Bt:Rabs(B tail)<=bpow radix2 1018) by (bpow_num; lra).
 pose proof (add_f64_ieee th tl tail Th Tl Tail Normal Bh Bl Bt) as Add.
 pose proof (add_f64_normalized_ieee th tl tail Th Tl Tail Normal Bh Bl Bt) as Norm.
 destruct (add_f64_64 th tl tail) as [h l] eqn:Output. cbn zeta iota in Add,Norm |- *.
 destruct Add as [H [L Error]]. destruct Norm as [_ [_ N]].
 split; [exact H|]. split; [exact L|]. split; [exact N|].
 assert (D2:Rabs((B h+B l-(B th+B tl+B tail))/(B th+B tl+B tail))<=/2^105).
 { eapply Rle_trans; [exact Error|]. unfold prec. right. change (bpow radix2 (- (53))) with (/9007199254740992). field. }
 set (d2:=(B h+B l-(B th+B tl+B tail))/(B th+B tl+B tail)) in *.
 assert (AddValue:B h+B l=(B th+B tl+B tail)*(1+d2)).
 { unfold d2. field; exact SumNonzero. }
 assert (LowError:Rabs((B th+B tl)-B th)<=/2^53*Rabs(B th)).
 { replace (B th+B tl-B th) with (B tl) by ring. exact Low. }
 destruct (trig_relative_factor (B th+B tl) (B th) (/2^53) ltac:(interval) LowError)
   as [dl [Dl TotalValue]].
 pose proof (trig_sin_residual_model (B th) dl et d2 Range Dl Et D2
   ltac:(rewrite <-TotalValue; exact FullRange)) as Bound.
 cbn zeta in Bound. rewrite <-TotalValue,<-TailValue,<-AddValue in Bound.
 apply trig_ratio_bound; assumption.
Qed.
