(** Tiny residual assembly, with certified tail factors that include underflow. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add Grid.
From Interval Require Import Tactic.
Require Import StageGappa TrigTables TrigError TrigPolynomial TrigTail
 TrigTinyTail TrigTinyCertificate TrigSinResidual TrigCosSquare TrigCosResidual AsinNormal.
Open Scope R_scope.

Theorem trig_sin_residual_tiny th tl : finite th -> finite tl ->
 /2^320<=Rabs(B th)<=/2^60 -> Rabs(B tl)<=/2^53*Rabs(B th) ->
 B th=rndF(B th+B tl) -> Rabs(B th+B tl)<=0.0078126 ->
 let '(h,l):=trig_sin_residual th tl in
 finite h /\ finite l /\ B h=rndF(B h+B l) /\
 Rabs(B h+B l-sin(B th+B tl))<=/2^65*Rabs(sin(B th+B tl)).
Proof.
 intros Th Tl Range Low Normal FullRange.
 pose proof (proj2 Range) as Upper.
 assert (FullHead:Rabs(B th)<=0.0078126) by interval.
 assert (ThNonzero:B th<>0).
 { intro Zero. rewrite Zero,Rabs_R0 in Range.
   assert (Positive:0</2^320) by interval. lra. }
 assert (LowQuarter:Rabs(B tl)<=Rabs(B th)/4).
 { assert (Small:/2^53<=/4) by interval. pose proof (Rabs_pos(B th)); nra. }
 assert (TotalNonzero:B th+B tl<>0).
 { pose proof (trig_small_perturbation_nonzero (B th) (B tl) 0 ThNonzero LowQuarter
     ltac:(rewrite Rabs_R0; pose proof (Rabs_pos(B th)); lra)) as N.
   rewrite Rplus_0_r in N; exact N. }
 assert (SinNonzero:sin(B th+B tl)<>0) by (apply trig_sin_small_nonzero; assumption).
 pose proof (trig_tail_evaluation th Th FullHead) as Eval.
 pose proof (trig_tail_tiny th Th Range) as Tiny.
 unfold trig_sin_residual.
 destruct (trig_tail_eval th) as [[[[u ps]pc]tail]ct] eqn:Parts.
 cbn zeta iota in Eval,Tiny |- *.
 destruct Eval as [U [Ps [Pc [Tail [Ct Rest]]]]].
 destruct Tiny as [et [ec [Et [Ec [TailValue _]]]]].
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
 pose proof (trig_sin_tiny_model (B th) dl et d2 Range Dl Et D2
   ltac:(rewrite <-TotalValue; exact FullRange)) as Bound.
 cbn zeta in Bound. rewrite <-TotalValue,<-TailValue,<-AddValue in Bound.
 apply trig_ratio_bound; assumption.
Qed.

Theorem trig_cos_residual_tiny th tl : finite th -> finite tl ->
 /2^320<=Rabs(B th)<=/2^60 -> Rabs(B tl)<=/2^53*Rabs(B th) ->
 on_grid (-320) (B tl) -> Rabs(B th+B tl)<=0.0078126 ->
 let '(h,l):=trig_cos_residual th tl in
 finite h /\ finite l /\ B h=rndF(B h+B l) /\
 Rabs(B h+B l-(cos(B th+B tl)-1))<=/2^65*Rabs(cos(B th+B tl)-1).
Proof.
 intros Th Tl Range Low GridLow FullRange. pose proof (proj2 Range) as Upper.
 assert (FullHead:Rabs(B th)<=0.0078126) by interval.
 assert (ThNonzero:B th<>0).
 { intro Zero. rewrite Zero,Rabs_R0 in Range. assert (Positive:0</2^320) by interval. lra. }
 assert (ThSquare:0<B th*B th).
 { apply Rlt_0_sqr; exact ThNonzero. }
 assert (LowQuarter:Rabs(B tl)<=Rabs(B th)/4).
 { assert (Small:/2^53<=/4) by interval. pose proof (Rabs_pos(B th)); nra. }
 assert (LowSmall:Rabs(B tl)<=/4) by lra.
 assert (TotalNonzero:B th+B tl<>0).
 { pose proof (trig_small_perturbation_nonzero (B th) (B tl) 0 ThNonzero LowQuarter
     ltac:(rewrite Rabs_R0; pose proof (Rabs_pos(B th)); lra)) as N.
   rewrite Rplus_0_r in N; exact N. }
 assert (CosNonzero:cos(B th+B tl)-1<>0) by (apply trig_cos_small_nonzero; assumption).
 assert (LowError:Rabs((B th+B tl)-B th)<=/2^53*Rabs(B th)).
 { replace (B th+B tl-B th) with (B tl) by ring; exact Low. }
 destruct (trig_relative_factor (B th+B tl) (B th) (/2^53) ltac:(interval) LowError)
   as [dl [Dl TotalValue]].
 assert (TlValue:B tl=B th*dl) by nra.
 pose proof (trig_cos_square_correct_wide th Th (conj (proj1 Range) FullHead)) as Square.
 pose proof (trig_tail_evaluation th Th FullHead) as Eval.
 pose proof (trig_tail_tiny th Th Range) as Tiny.
 unfold trig_cos_residual.
 destruct (trig_cos_square th) as [qh ql] eqn:SquareParts.
 destruct (trig_tail_eval th) as [[[[u ps]pc]st]ct] eqn:TailParts.
 cbn zeta iota in Square,Eval,Tiny |- *.
 destruct Square as [Qh [Ql [Normal SquareValue]]].
 destruct Eval as [_ [_ [_ [_ [Ct _]]]]].
 destruct Tiny as [es [et [Es [Et [_ TailValue]]]]].
 assert (TailSmall:Rabs(B ct)<=/4).
 { rewrite TailValue. unfold trig_pc. rewrite trig_c0_val,trig_c1_val,trig_c2_val. interval. }
 destruct (trig_cross_model_wide th tl Th Tl (conj (proj1 Range) FullHead) LowSmall GridLow) as [Cross [CrossSmall [ec [Ec CrossValue]]]].
 destruct (trig_sub_model ct (fmul th tl) Ct Cross TailSmall CrossSmall) as [V [eu [Eu Vvalue]]].
 rewrite TailValue,CrossValue,TlValue in Vvalue.
 replace (B th*(B th*dl)) with (B th*B th*dl) in Vvalue by ring.
 assert (VSmall:Rabs(B(fsub ct (fmul th tl)))<=B th*B th/4).
 { rewrite Vvalue. replace (((B th)^4*trig_pc(B th*B th)*(1+et)-B th*B th*dl*(1+ec))*(1+eu)) with
     ((B th*B th)*((B th*B th*trig_pc(B th*B th)*(1+et)-dl*(1+ec))*(1+eu))) by ring.
   rewrite Rabs_mult,(Rabs_pos_eq (B th*B th) ltac:(lra)).
   replace (B th*B th/4) with ((B th*B th)*(/4)) by field.
   apply Rmult_le_compat_l; [lra|].
   unfold trig_pc. rewrite trig_c0_val,trig_c1_val,trig_c2_val. interval. }
 assert (SumNonzero:B qh+B ql+B(fsub ct (fmul th tl))<>0).
 { rewrite SquareValue. apply Rabs_le_inv in VSmall. lra. }
 assert (QhBound:Rabs(B qh)<=1).
 { rewrite Normal,SquareValue. apply trig_round_unit; interval. }
 assert (QlBound:Rabs(B ql)<=2).
 { replace (B ql) with (-(B th*B th/2)-B qh) by lra. interval. }
 assert (VB:Rabs(B(fsub ct (fmul th tl)))<=1).
 { assert (Small:B th*B th/4<=1) by interval. lra. }
 assert (Bh:Rabs(B qh)<=bpow radix2 1018) by (bpow_num; lra).
 assert (Bl:Rabs(B ql)<=bpow radix2 1018) by (bpow_num; lra).
 assert (Bv:Rabs(B(fsub ct (fmul th tl)))<=bpow radix2 1018) by (bpow_num; lra).
 pose proof (add_f64_ieee qh ql (fsub ct (fmul th tl)) Qh Ql V Normal Bh Bl Bv) as Add.
 pose proof (add_f64_normalized_ieee qh ql (fsub ct (fmul th tl)) Qh Ql V Normal Bh Bl Bv) as Norm.
 destruct (add_f64_64 qh ql (fsub ct (fmul th tl))) as [h l].
 cbn zeta iota in Add,Norm |- *. destruct Add as [H [L Error]]. destruct Norm as [_ [_ N]].
 split; [exact H|]. split; [exact L|]. split; [exact N|].
 assert (D2:Rabs((B h+B l-(B qh+B ql+B(fsub ct (fmul th tl))))/(B qh+B ql+B(fsub ct (fmul th tl))))<=/2^105).
 { eapply Rle_trans; [exact Error|]. unfold prec. right.
   change (bpow radix2 (- (53))) with (/9007199254740992). field. }
 set (d2:=(B h+B l-(B qh+B ql+B(fsub ct (fmul th tl))))/(B qh+B ql+B(fsub ct (fmul th tl)))) in *.
 assert (AddValue:B h+B l=(B qh+B ql+B(fsub ct (fmul th tl)))*(1+d2)).
 { unfold d2. field; exact SumNonzero. }
 rewrite SquareValue,Vvalue in AddValue.
 pose proof (trig_cos_tiny_model (B th) dl et ec eu d2 Range Dl Et Ec Eu D2
   ltac:(rewrite <-TotalValue; exact FullRange)) as Bound.
 cbn zeta in Bound. rewrite <-TotalValue,<-AddValue in Bound.
 apply trig_ratio_bound; assumption.
Qed.
