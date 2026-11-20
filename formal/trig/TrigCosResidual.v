(** Executable cosine-minus-one residual assembly on the regular domain. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core Relative.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add Grid RoundingCore.
From Interval Require Import Tactic.
Require Import StageGappa TrigTables TrigError TrigPolynomial TrigTail
 TrigResidualCertificate TrigSinResidual TrigCosSquare AsinNormal.
Open Scope R_scope.

Definition trig_cos_residual th tl :=
 let '(qh,ql):=trig_cos_square th in
 let '(_,_,_,_,ct):=trig_tail_eval th in
 add_f64_64 qh ql (fsub ct (fmul th tl)).

Lemma trig_cos_small_nonzero t : t<>0 -> Rabs t<=0.0078126 -> cos t-1<>0.
Proof.
 intros Nonzero Range.
 destruct (trig_cos_polynomial_model t Range) as [al [Al Value]].
 assert (Factor:-/2+t*t*trig_pc(t*t)*(1+al)<0).
 { unfold trig_pc. rewrite trig_c0_val,trig_c1_val,trig_c2_val.
   unfold trig_poly_error in Al. interval. }
 rewrite Value. replace (1-t*t/2+t^4*trig_pc(t*t)*(1+al)-1) with
   (t*t*(-/2+t*t*trig_pc(t*t)*(1+al))) by field.
 repeat apply Rmult_integral_contrapositive_currified; try exact Nonzero; lra.
Qed.

(** A subtraction rounds identically in FLT and FLX, even when its result is
    subnormal, because its operands are binary64 values. *)
Lemma trig_sub_model a b : finite a -> finite b -> Rabs(B a)<=/4 -> Rabs(B b)<=/4 ->
 finite(fsub a b) /\ exists e, Rabs e<=/2^53 /\ B(fsub a b)=(B a-B b)*(1+e).
Proof.
 intros A B Ab Bb.
 assert (Bound:bnd 1 0 (IEEE64.B a-IEEE64.B b)).
 { unfold bnd. change (IZR 1) with 1. change (bpow radix2 0) with 1. interval. }
 destruct (fsub_bnd 1 0 a b A B ltac:(lia) ltac:(lia)
   ltac:(apply Z.pow_gt_1; lia) ltac:(lia) Bound) as [F [Value _]].
 split; [exact F|]. apply trig_relative_factor; [interval|]. rewrite Value.
 rewrite diff_round by apply B_fmt.
 pose proof (relative_error_N_FLX radix2 prec ltac:(unfold prec; lia) ne (IEEE64.B a-IEEE64.B b)) as E.
 replace (/2*bpow radix2 (-prec+1)) with (/2^53) in E
   by (unfold prec; change (bpow radix2 (- (53)+1)) with (/4503599627370496); field).
 exact E.
Qed.

(** The low word's Q256-derived grid excludes underflow in this multiplication.
    Zero is handled explicitly and does not require a normal-product premise. *)
Lemma trig_cross_model_wide th tl : finite th -> finite tl ->
 /2^320<=Rabs(B th)<=0.0078126 -> Rabs(B tl)<=/4 -> on_grid (-320) (B tl) ->
 finite(fmul th tl) /\ Rabs(B(fmul th tl))<=/4 /\
 exists e, Rabs e<=/2^53 /\ B(fmul th tl)=B th*B tl*(1+e).
Proof.
 intros Th Tl Range Low GridLow. pose proof (proj2 Range) as Upper.
 destruct (trig_mul_bounded (-2) th tl Th Tl ltac:(lia)
   ltac:(bpow_num; interval)) as [F [Value Bound]].
 split; [exact F|]. split; [bpow_num_all; exact Bound|].
 apply trig_relative_factor; [interval|]. rewrite Value.
 destruct (Req_dec (B th*B tl) 0) as [Zero|Nonzero].
 - rewrite Zero,round_0,Rminus_0_r,Rabs_R0,Rmult_0_r; first [lra|exact _].
 - assert (ThGrid:on_grid (-372) (B th)).
   { apply (grid_fmt_bound (FLT_exp emin prec) (-320) (B th));
       [intro e; unfold FLT_exp,emin,prec; lia|apply B_fmt|].
     right. replace (bpow radix2 (-320)) with (/2^320) by (bpow_num; field). exact (proj1 Range). }
   assert (ProductGrid:on_grid (-692) (B th*B tl)).
   { change (-692)%Z with ((-372)+(-320))%Z. apply grid_mult; assumption. }
   assert (Normal:bpow radix2 (-1022)<=Rabs(B th*B tl)).
   { eapply Rle_trans; [apply (bpow_le radix2 (-1022) (-692)); lia|].
     apply grid_nonzero; assumption. }
   pose proof (rnd_rel (B th*B tl) Normal) as Error.
   replace (bpow radix2 (-53)) with (/2^53) in Error by (bpow_num; field).
   exact Error.
Qed.

Lemma trig_cross_model th tl : finite th -> finite tl ->
 /2^60<=Rabs(B th)<=0.0078126 -> Rabs(B tl)<=/4 -> on_grid (-320) (B tl) ->
 finite(fmul th tl) /\ Rabs(B(fmul th tl))<=/4 /\
 exists e, Rabs e<=/2^53 /\ B(fmul th tl)=B th*B tl*(1+e).
Proof.
 intros Th Tl [Lower Upper] Low GridLow.
 apply trig_cross_model_wide; try assumption.
 split; [eapply Rle_trans; [|exact Lower]; interval|exact Upper].
Qed.

Lemma trig_round_unit v : Rabs v<=1 -> Rabs(rndF v)<=1.
Proof.
 intro V. assert (Bd:bnd 1 0 v).
 { unfold bnd. change (IZR 1) with 1. change (bpow radix2 0) with 1; lra. }
 pose proof (bnd_round 1 0 v ltac:(lia) ltac:(lia) Bd) as Out.
 unfold bnd in Out. change (IZR 1) with 1 in Out. change (bpow radix2 0) with 1 in Out. lra.
Qed.

Theorem trig_cos_residual_regular th tl : finite th -> finite tl ->
 /2^60<=Rabs(B th)<=0.0078126 -> Rabs(B tl)<=/2^53*Rabs(B th) ->
 on_grid (-320) (B tl) -> Rabs(B th+B tl)<=0.0078126 ->
 let '(h,l):=trig_cos_residual th tl in
 finite h /\ finite l /\ B h=rndF(B h+B l) /\
 Rabs(B h+B l-(cos(B th+B tl)-1))<=/2^65*Rabs(cos(B th+B tl)-1).
Proof.
 intros Th Tl Range Low GridLow FullRange. pose proof (proj2 Range) as Upper.
 assert (ThNonzero:B th<>0).
 { intro Zero. rewrite Zero,Rabs_R0 in Range. assert (Positive:0</2^60) by interval. lra. }
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
 pose proof (trig_cos_square_correct th Th Range) as Square.
 pose proof (trig_tail_evaluation th Th Upper) as Eval.
 pose proof (trig_tail_regular th Th Range) as TailError.
 unfold trig_cos_residual.
 destruct (trig_cos_square th) as [qh ql] eqn:SquareParts.
 destruct (trig_tail_eval th) as [[[[u ps]pc]st]ct] eqn:TailParts.
 cbn zeta iota in Square,Eval,TailError |- *.
 destruct Square as [Qh [Ql [Normal SquareValue]]].
 destruct Eval as [_ [_ [_ [_ [Ct _]]]]]. destruct TailError as [_ TailError].
 destruct (trig_relative_factor (B ct) ((B th)^4*trig_pc(B th*B th)) (/2^50)
   ltac:(interval) TailError) as [et [Et TailValue]].
 assert (TailSmall:Rabs(B ct)<=/4).
 { rewrite TailValue. unfold trig_pc. rewrite trig_c0_val,trig_c1_val,trig_c2_val. interval. }
 destruct (trig_cross_model th tl Th Tl Range LowSmall GridLow) as [Cross [CrossSmall [ec [Ec CrossValue]]]].
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
 pose proof (trig_cos_residual_model (B th) dl et ec eu d2 Range Dl Et Ec Eu D2
   ltac:(rewrite <-TotalValue; exact FullRange)) as Bound.
 cbn zeta in Bound. rewrite <-TotalValue,<-AddValue in Bound.
 apply trig_ratio_bound; assumption.
Qed.
