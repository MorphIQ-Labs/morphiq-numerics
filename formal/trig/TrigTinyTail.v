(** Tiny residual tails: keep gradual-underflow errors until the final bound. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Binary64 Require Import Binary64Add IEEE64 Grid RoundingCore.
From Interval Require Import Tactic.
Require Import StageGappa TrigTables TrigError TrigPolynomial TrigTail AsinNormal.
Open Scope R_scope.

Lemma trig_round_small_error v : Rabs v<=1 -> Rabs(rn v-v)<=/2^52.
Proof.
 intro V. pose proof (rnd_err_abs v) as Error.
 change (Rabs(rn v-v)<=bpow radix2 (-53)*Rabs v+bpow radix2 (-1075)) in Error.
 assert (Eta:bpow radix2 (-1075)<=bpow radix2 (-53)) by (apply bpow_le; lia).
 pose proof (bpow_gt_0 radix2 (-53)).
 replace (/2^52) with (2*bpow radix2 (-53)) by (bpow_num; field). nra.
Qed.

Lemma trig_horner_near u a b c : finite u -> finite a -> finite b -> finite c ->
 Rabs(B u)<=/8192 -> Rabs(B a)<=/4 -> Rabs(B b)<=/4 -> Rabs(B c)<=/4 ->
 Rabs(B(trig_horner u a b c)-B a)<=/4096.
Proof.
 intros U A B C Ub Ab Bb Cb.
 destruct (trig_mul_bounded (-13) u c U C ltac:(lia)
   ltac:(bpow_num; interval)) as [F1 [V1 B1]].
 destruct (trig_add_bounded b (fmul u c) B F1
   ltac:(bpow_num_all; interval)) as [F2 [V2 B2]].
 destruct (trig_mul_bounded (-13) u (fadd b (fmul u c)) U F2 ltac:(lia)
   ltac:(rewrite Rabs_mult; bpow_num; pose proof (Rabs_pos (IEEE64.B u));
     pose proof (Rabs_pos (IEEE64.B (fadd b (fmul u c)))); nra)) as [F3 [V3 B3]].
 destruct (trig_add_bounded a (fmul u (fadd b (fmul u c))) A F3
   ltac:(bpow_num_all; interval)) as [F4 [V4 B4]].
 pose proof (trig_round_small_error (IEEE64.B a+IEEE64.B(fmul u (fadd b (fmul u c))))
   ltac:(bpow_num_all; interval)) as Error.
 rewrite <-V4 in Error. unfold trig_horner.
 pose proof (Rabs_triang
   (IEEE64.B(fadd a (fmul u (fadd b (fmul u c))))-(IEEE64.B a+IEEE64.B(fmul u (fadd b (fmul u c)))))
   (IEEE64.B(fmul u (fadd b (fmul u c))))) as Triangle.
 replace (IEEE64.B(fadd a (fmul u (fadd b (fmul u c))))-
   (IEEE64.B a+IEEE64.B(fmul u (fadd b (fmul u c))))+IEEE64.B(fmul u (fadd b (fmul u c)))) with
   (IEEE64.B(fadd a (fmul u (fadd b (fmul u c))))-IEEE64.B a) in Triangle by ring.
 bpow_num_all. lra.
Qed.

Lemma trig_evaluated_polynomial_ranges th : finite th -> Rabs(B th)<=0.0078126 ->
 let '(u,ps,pc,_,_):=trig_tail_eval th in
 -0.167<=B ps<=-0.166 /\ 0.041<=B pc<=0.042 /\
 -0.167<=trig_ps(B th*B th)<=-0.166 /\ 0.041<=trig_pc(B th*B th)<=0.042.
Proof.
 intros Th Range. unfold trig_tail_eval.
 destruct (trig_mul_bounded (-13) th th Th Th ltac:(lia)
   ltac:(bpow_num; interval)) as [U [Uv Ub]].
 assert (Ub':Rabs(B(fmul th th))<=/8192) by (bpow_num_all; exact Ub).
 pose proof (trig_horner_near (fmul th th) trig_s0 trig_s1 trig_s2 U
   trig_s0_finite trig_s1_finite trig_s2_finite Ub'
   ltac:(rewrite trig_s0_val; interval) ltac:(rewrite trig_s1_val; interval)
   ltac:(rewrite trig_s2_val; interval)) as S.
 pose proof (trig_horner_near (fmul th th) trig_c0 trig_c1 trig_c2 U
   trig_c0_finite trig_c1_finite trig_c2_finite Ub'
   ltac:(rewrite trig_c0_val; interval) ltac:(rewrite trig_c1_val; interval)
   ltac:(rewrite trig_c2_val; interval)) as C.
 assert (S0:-0.166667<=B trig_s0<=-0.166666) by (rewrite trig_s0_val; interval).
 assert (C0:0.041666<=B trig_c0<=0.041667) by (rewrite trig_c0_val; interval).
 apply Rabs_le_inv in S,C.
 split; [lra|]. split; [lra|]. unfold trig_ps,trig_pc.
 rewrite trig_s0_val,trig_s1_val,trig_s2_val,trig_c0_val,trig_c1_val,trig_c2_val.
 split; interval.
Qed.

Lemma trig_round_nonnegative v : 0<=v -> 0<=rn v.
Proof.
 intro V. apply round_ge_generic; [exact _|exact _|apply generic_format_0|exact V].
Qed.

Lemma trig_positive_float_floor v : fmtF v -> 0<v -> bpow radix2 (-1074)<=v.
Proof.
 intros F V. assert (G:on_grid (-1074) v).
 { apply (grid_le (cexp radix2 (FLT_exp emin prec) v) (-1074) v).
   - unfold cexp,FLT_exp,emin. lia.
   - apply grid_fmt; exact F. }
 pose proof (grid_nonzero (-1074) v G ltac:(lra)) as Bound.
 rewrite (Rabs_pos_eq v ltac:(lra)) in Bound; exact Bound.
Qed.

Lemma trig_normal_round_model v : bpow radix2 (-1022)<=Rabs v ->
 exists e, Rabs e<=/2^53 /\ rn v=v*(1+e).
Proof.
 intro Normal. apply trig_relative_factor; [interval|].
 pose proof (rnd_rel v Normal) as Error.
 replace (bpow radix2 (-53)) with (/2^53) in Error by (bpow_num; field).
 exact Error.
Qed.

(** One joint bound for the two cosine-tail roundings. Bounding each rounding
    by a separate multiplicative factor would unnecessarily spend the budget
    twice at the subnormal boundary. *)
Lemma trig_cos_two_roundings u p exact : 0<=u -> 0.041<=p<=0.042 -> 0<exact ->
 u*u*p<=1.1*exact ->
 0<=rn(rn(u*u)*p)<=3*exact.
Proof.
 intros U P T Comparable.
 set (a:=rn(u*u)). set (y:=rn(a*p)).
 assert (A:0<=a) by (unfold a; apply trig_round_nonnegative; nra).
 assert (Y:0<=y) by (unfold y; apply trig_round_nonnegative; nra).
 split; [exact Y|].
 pose proof (rnd_err_abs (u*u)) as E1.
 change (Rabs(a-u*u)<=bpow radix2 (-53)*Rabs(u*u)+bpow radix2 (-1075)) in E1.
 pose proof (rnd_err_abs (a*p)) as E2.
 change (Rabs(y-a*p)<=bpow radix2 (-53)*Rabs(a*p)+bpow radix2 (-1075)) in E2.
 rewrite (Rabs_pos_eq (u*u) ltac:(nra)) in E1.
 rewrite (Rabs_pos_eq (a*p) ltac:(nra)) in E2.
 apply Rabs_le_inv in E1,E2.
 set (eta:=bpow radix2 (-1075)) in *.
 assert (Eta:0<eta) by apply bpow_gt_0.
 assert (Small:bpow radix2 (-53)<=0.001) by interval.
 assert (Aupper:a<=1.001*(u*u)+eta) by nra.
 assert (Yupper:y<=1.001*(a*p)+eta).
 { assert (Scale:bpow radix2 (-53)*(a*p)<=0.001*(a*p)).
   { apply Rmult_le_compat_r; [nra|exact Small]. } nra. }
 assert (Weighted:a*p<=1.001*(u*u*p)+eta*p).
 { pose proof (Rmult_le_compat_r p _ _ ltac:(lra) Aupper). nra. }
 assert (Joint:y<=1.11*exact+1.05*eta) by nra.
 destruct (Req_dec y 0) as [Zero|Nonzero]; [rewrite Zero; lra|].
 assert (Floor:bpow radix2 (-1074)<=y).
 { apply trig_positive_float_floor; [unfold y; apply fmtF_rnd|lra]. }
 assert (Twice:bpow radix2 (-1074)=2*eta).
 { unfold eta. replace (-1074)%Z with (1+(-1075))%Z by lia.
   rewrite bpow_plus. change (bpow radix2 1) with 2; ring. }
 rewrite Twice in Floor. nra.
Qed.

Lemma trig_nonnegative_tail_factor y exact : 0<exact -> 0<=y<=3*exact ->
 exists e, -1<=e<=2 /\ y=exact*(1+e).
Proof.
 intros T Bound. exists (y/exact-1). split.
 - assert (Ratio:0<=y/exact<=3).
   { split.
     - unfold Rdiv. apply Rmult_le_pos; [lra|left; apply Rinv_0_lt_compat; exact T].
     - apply (Rmult_le_reg_r exact); [exact T|].
       replace (y/exact*exact) with y by (field; lra). lra. }
   lra.
 - field; lra.
Qed.

Theorem trig_tail_tiny th : finite th -> /2^320<=Rabs(B th)<=/2^60 ->
 let '(_,_,_,st,ct):=trig_tail_eval th in
 exists es ec, -1<=es<=2 /\ -1<=ec<=2 /\
 B st=(B th)^3*trig_ps(B th*B th)*(1+es) /\
 B ct=(B th)^4*trig_pc(B th*B th)*(1+ec).
Proof.
 intros Th Range.
 assert (Full:Rabs(B th)<=0.0078126) by (destruct Range; interval).
 pose proof (trig_tail_evaluation th Th Full) as Eval.
 pose proof (trig_evaluated_polynomial_ranges th Th Full) as Polys.
 destruct (trig_tail_eval th) as [[[[u ps]pc]st]ct] eqn:Parts.
 cbn zeta iota in Eval,Polys |- *.
 destruct Eval as [U [Ps [Pc [St [Ct [Uv [Psv [Pcv [Stv Ctv]]]]]]]]].
 destruct Polys as [PS [PC [ExactPS ExactPC]]].
 assert (SquareLower:bpow radix2 (-640)<=B th*B th).
 { destruct Range as [Lower _].
   replace (/2^320) with (bpow radix2 (-320)) in Lower by (bpow_num; field).
   destruct (Rle_lt_dec 0 (B th)) as [Pos|Neg].
   - rewrite (Rabs_pos_eq _ Pos) in Lower. bpow_num_all. nra.
   - rewrite (Rabs_left _ Neg) in Lower. bpow_num_all. nra. }
 assert (SquarePos:0<B th*B th) by (pose proof (bpow_gt_0 radix2 (-640)); lra).
 assert (SquareNormal:bpow radix2 (-1022)<=Rabs(B th*B th)).
 { rewrite (Rabs_pos_eq (B th*B th) ltac:(lra)). eapply Rle_trans; [apply (bpow_le radix2 (-1022) (-640)); lia|exact SquareLower]. }
 destruct (trig_normal_round_model (B th*B th) SquareNormal) as [du [Du Umodel]].
 rewrite <-Uv in Umodel.
 assert (DuSmall:-0.001<=du<=0.001).
 { apply Rabs_le_inv in Du. assert (Small:/2^53<=0.001) by interval; lra. }
 assert (Ulower:bpow radix2 (-641)<=B u).
 { rewrite Umodel. bpow_num_all. nra. }
 assert (Upos:0<B u) by (pose proof (bpow_gt_0 radix2 (-641)); lra).
 assert (CubeLower:bpow radix2 (-961)<=Rabs(B th*B u)).
 { rewrite Rabs_mult,(Rabs_pos_eq (B u) ltac:(lra)).
   destruct Range as [Lower _]. replace (/2^320) with (bpow radix2 (-320)) in Lower by (bpow_num; field).
   bpow_num_all. nra. }
 assert (CubeNormal:bpow radix2 (-1022)<=Rabs(B th*B u)).
 { eapply Rle_trans; [apply (bpow_le radix2 (-1022) (-961)); lia|exact CubeLower]. }
 destruct (trig_normal_round_model (B th*B u) CubeNormal) as [da [Da Amodel]].
 assert (DaSmall:-0.001<=da<=0.001).
 { apply Rabs_le_inv in Da. assert (Small:/2^53<=0.001) by interval; lra. }
 assert (Alower:bpow radix2 (-962)<=Rabs(rn(B th*B u))).
 { rewrite Amodel,Rabs_mult,(Rabs_pos_eq (1+da) ltac:(lra)). bpow_num_all. nra. }
 assert (SinNormal:bpow radix2 (-1022)<=Rabs(rn(B th*B u)*B ps)).
 { rewrite Rabs_mult,(Rabs_left (B ps) ltac:(lra)). bpow_num_all. nra. }
 destruct (trig_normal_round_model (rn(B th*B u)*B ps) SinNormal) as [ds [Ds Smodel]].
 rewrite <-Stv in Smodel.
 set (es:=((1+du)*(1+da)*B ps*(1+ds))/trig_ps(B th*B th)-1).
 assert (Es:-1<=es<=2).
 { unfold es. apply Rabs_le_inv in Du,Da,Ds. split; interval. }
 assert (SinValue:B st=(B th)^3*trig_ps(B th*B th)*(1+es)).
 { rewrite Smodel,Amodel,Umodel. unfold es. field; lra. }
 assert (CosExact:0<(B th)^4*trig_pc(B th*B th)).
 { replace ((B th)^4) with ((B th*B th)*(B th*B th)) by ring.
   apply Rmult_lt_0_compat; [apply Rmult_lt_0_compat; exact SquarePos|lra]. }
 assert (Comparable:B u*B u*B pc<=1.1*((B th)^4*trig_pc(B th*B th))).
 { assert (Ratio:(1+du)^2*B pc<=1.1*trig_pc(B th*B th)).
   { apply Rle_trans with 0.044; [interval|lra]. }
   rewrite Umodel. replace ((B th*B th*(1+du))*(B th*B th*(1+du))*B pc) with
     ((B th)^4*((1+du)^2*B pc)) by ring.
   replace (1.1*((B th)^4*trig_pc(B th*B th))) with
     ((B th)^4*(1.1*trig_pc(B th*B th))) by ring.
   apply Rmult_le_compat_l; [replace ((B th)^4) with ((B th*B th)*(B th*B th)) by ring; nra|exact Ratio]. }
 pose proof (trig_cos_two_roundings (B u) (B pc) ((B th)^4*trig_pc(B th*B th))
   ltac:(lra) PC CosExact Comparable) as CosBound.
 rewrite <-Ctv in CosBound.
 destruct (trig_nonnegative_tail_factor (B ct) ((B th)^4*trig_pc(B th*B th)) CosExact CosBound)
   as [ec [Ec CosValue]].
 exists es,ec. split; [exact Es|]. split; [exact Ec|]. split; assumption.
Qed.
