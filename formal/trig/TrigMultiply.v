(** The actual double-word multiply with gradual underflow in either cross
    product. The high-word product is exact as a double-word; the proof
    retains the absolute half-subnormal allowance for the cross products. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core Relative.
From Binary64 Require Import Binary64Add Binary64Mul IEEE64 IEEE64Mul.
From Interval Require Import Tactic.
Require Import LnFastAdd AsinNormal.
Require TwoProdBinary64.
Open Scope R_scope.

Definition trig_mul_u : R := /9007199254740992.

Lemma trig_dw_low h l : fmtF h -> fmtF l -> h=rndF(h+l) ->
 Rabs l<=trig_mul_u*Rabs h.
Proof.
 intros H L Normal. rewrite sum_round in Normal by assumption.
 pose proof (relative_error_N_FLX_round radix2 prec ltac:(unfold prec;lia) ne (h+l)) as E.
 rewrite <-Normal in E. replace (h-(h+l)) with (-l) in E by ring.
 rewrite Rabs_Ropp in E.
 replace (/2*bpow radix2 (-prec+1)) with trig_mul_u in E by (unfold prec,trig_mul_u;simpl;lra).
 exact E.
Qed.

Lemma trig_mul_eta p : bpow radix2 (-900)<=p ->
 bpow radix2 (-1075)<=trig_mul_u^3*p.
Proof.
 intro P.
 assert (U:trig_mul_u^3=bpow radix2 (-159)).
 { unfold trig_mul_u. change (bpow radix2 (-159)) with (/730750818665451459101842416358141509827966271488);field. }
 rewrite U. apply Rle_trans with (bpow radix2 (-159)*bpow radix2 (-900)).
 - rewrite <-bpow_plus. apply bpow_le;lia.
 - apply Rmult_le_compat_l;[apply bpow_ge_0|exact P].
Qed.

Lemma trig_two_prod_value a b : fmtF a -> fmtF b -> in_two_prod_domain a b ->
 let '(h,l):=two_prod a b in fmtF h /\ fmtF l /\ h=rndF(a*b) /\ h+l=a*b.
Proof.
 intros A B Domain.
 pose proof (two_prod_fmt a b) as [Fh Fl].
 pose proof (TwoProdBinary64.two_prod_exact a b A B Domain) as Exact.
 unfold two_prod in *;cbn [fst snd] in *.
 repeat split;try assumption;try reflexivity. symmetry;exact Exact.
Qed.

Lemma trig_mul_zero xh xl yh yl : fmtF xh -> fmtF xl -> xh=rndF(xh+xl) ->
 fmtF yh -> fmtF yl -> yh=rndF(yh+yl) -> xh*yh=0 ->
 mul xh xl yh yl=(0,0).
Proof.
 intros Xh Xl X Yh Yl Y Zero.
 pose proof (trig_dw_low xh xl Xh Xl X) as Lx.
 pose proof (trig_dw_low yh yl Yh Yl Y) as Ly.
 pose proof (trig_two_prod_value xh yh Xh Yh (or_introl Zero)) as Product.
 unfold mul. destruct (two_prod xh yh) as [ch cl].
 destruct Product as [Fch [Fcl [Ch Sum]]].
 assert (Ch0:ch=0) by (rewrite Ch,Zero;apply round_0;exact _).
 assert (Cl0:cl=0) by lra.
 assert (Cross1:xh*yl=0 /\ xl*yh=0).
 { apply Rmult_integral in Zero;destruct Zero as [X0|Y0].
   - rewrite X0,Rabs_R0,Rmult_0_r in Lx.
     assert (Xl0:xl=0) by (apply Rabs_le_inv in Lx;lra). rewrite X0,Xl0;split;ring.
   - rewrite Y0,Rabs_R0,Rmult_0_r in Ly.
     assert (Yl0:yl=0) by (apply Rabs_le_inv in Ly;lra). rewrite Y0,Yl0;split;ring. }
 destruct Cross1 as [C1 C2]. rewrite C1,C2,Ch0,Cl0.
 unfold fast_two_sum;cbn zeta.
 repeat first [rewrite round_0 by exact _|rewrite Rplus_0_l|rewrite Rminus_0_r]. reflexivity.
Qed.

Lemma trig_mul_cross x p : 0<=p -> Rabs x<=trig_mul_u*p ->
 bpow radix2 (-1075)<=trig_mul_u^3*p ->
 Rabs(rndF x-x)<=1.1*trig_mul_u^2*p /\ Rabs(rndF x)<=1.1*trig_mul_u*p.
Proof.
 intros P X Eta. pose proof (rnd_err_abs x) as Error.
 change (bpow radix2 (-53)) with trig_mul_u in Error.
 pose proof (Rabs_triang (rndF x-x) x) as T.
 replace (rndF x-x+x) with (rndF x) in T by ring.
 unfold trig_mul_u in *;cbn [pow] in *;split;lra.
Qed.

Theorem trig_mul_nonzero xh xl yh yl :
 fmtF xh -> fmtF xl -> xh=rndF(xh+xl) ->
 fmtF yh -> fmtF yl -> yh=rndF(yh+yl) ->
 bpow radix2 (-900)<=Rabs(xh*yh) ->
 let '(zh,zl):=mul xh xl yh yl in
 fmtF zh /\ fmtF zl /\ zh=rndF(zh+zl) /\
 Rabs(zh+zl-(xh+xl)*(yh+yl))<=9*trig_mul_u^2*Rabs((xh+xl)*(yh+yl)).
Proof.
 intros Xh Xl X Yh Yl Y Floor.
 set (p:=Rabs(xh*yh)).
 assert (P:0<=p) by apply Rabs_pos.
 assert (Domain:in_two_prod_domain xh yh).
 { right;eapply Rle_trans;[|exact Floor];apply bpow_le;lia. }
 pose proof (trig_mul_eta p Floor) as Eta.
 pose proof (trig_dw_low xh xl Xh Xl X) as LowX.
 pose proof (trig_dw_low yh yl Yh Yl Y) as LowY.
 assert (Cross1:Rabs(xh*yl)<=trig_mul_u*p).
 { unfold p;rewrite !Rabs_mult.
   replace (trig_mul_u*(Rabs xh*Rabs yh)) with (Rabs xh*(trig_mul_u*Rabs yh)) by ring.
   apply Rmult_le_compat_l;[apply Rabs_pos|exact LowY]. }
 assert (Cross2:Rabs(xl*yh)<=trig_mul_u*p).
 { unfold p;rewrite !Rabs_mult.
   replace (trig_mul_u*(Rabs xh*Rabs yh)) with ((trig_mul_u*Rabs xh)*Rabs yh) by ring.
   apply Rmult_le_compat_r;[apply Rabs_pos|exact LowX]. }
 assert (LowProduct:Rabs(xl*yl)<=trig_mul_u^2*p).
 { unfold p;rewrite !Rabs_mult.
   replace (trig_mul_u^2*(Rabs xh*Rabs yh)) with ((trig_mul_u*Rabs xh)*(trig_mul_u*Rabs yh)) by ring.
   apply Rmult_le_compat;try apply Rabs_pos;assumption. }
 assert (TargetMagnitude:0.99*p<=Rabs((xh+xl)*(yh+yl))).
 { pose proof (Rabs_triang (xh*yl) (xl*yh)) as T1.
   pose proof (Rabs_triang (xh*yl+xl*yh) (xl*yl)) as T2.
   pose proof (Rabs_triang ((xh+xl)*(yh+yl)) (-(xh*yl+xl*yh+xl*yl))) as T3.
   replace ((xh+xl)*(yh+yl)+ -(xh*yl+xl*yh+xl*yl)) with (xh*yh) in T3 by ring.
   rewrite Rabs_Ropp in T3;fold p in T3.
   clear - Cross1 Cross2 LowProduct T1 T2 T3 P.
   unfold trig_mul_u in *;cbn [pow] in *;lra. }
 pose proof (trig_two_prod_value xh yh Xh Yh Domain) as Product.
 unfold mul. destruct (two_prod xh yh) as [ch cl].
 destruct Product as [Fch [Fcl [Ch Exact]]].
 assert (HeadError:Rabs(ch-xh*yh)<=trig_mul_u*p).
 { rewrite Ch. apply rnd_rel_f. eapply Rle_trans;[|exact Floor];apply bpow_le;lia. }
 assert (LowHead:Rabs cl<=trig_mul_u*p).
 { replace cl with (-(ch-xh*yh)) by lra;rewrite Rabs_Ropp;exact HeadError. }
 assert (HeadMagnitude:0.99*p<=Rabs ch).
 { pose proof (Rabs_triang (xh*yh-ch) ch) as T.
   replace (xh*yh-ch+ch) with (xh*yh) in T by ring.
   rewrite Rabs_minus_sym in T;fold p in T.
   clear - T HeadError P. unfold trig_mul_u in *;lra. }
 set (t1:=rndF(xh*yl)). set (t2:=rndF(xl*yh)).
 assert (Ft1:fmtF t1) by apply fmtF_rnd.
 assert (Ft2:fmtF t2) by apply fmtF_rnd.
 destruct (trig_mul_cross (xh*yl) p P Cross1 Eta) as [E1 T1]. fold t1 in E1,T1.
 destruct (trig_mul_cross (xl*yh) p P Cross2 Eta) as [E2 T2]. fold t2 in E2,T2.
 set (c2:=rndF(t1+t2)).
 assert (Fc2:fmtF c2) by apply fmtF_rnd.
 pose proof (lf_sum_error t1 t2 Ft1 Ft2) as E3.
 change (Rabs(c2-(t1+t2))<=trig_mul_u*Rabs(t1+t2)) in E3.
 assert (CrossSum:Rabs(t1+t2)<=2.2*trig_mul_u*p).
 { pose proof (Rabs_triang t1 t2);lra. }
 assert (E3bound:Rabs(c2-(t1+t2))<=2.2*trig_mul_u^2*p).
 { clear - E3 CrossSum;unfold trig_mul_u in *;cbn [pow] in *;lra. }
 assert (C2:Rabs c2<=2.3*trig_mul_u*p).
 { pose proof (Rabs_triang (c2-(t1+t2)) (t1+t2)) as T.
   replace (c2-(t1+t2)+(t1+t2)) with c2 in T by ring.
   clear - T E3bound CrossSum P;unfold trig_mul_u in *;cbn [pow] in *;lra. }
 set (c3:=rndF(cl+c2)).
 assert (Fc3:fmtF c3) by apply fmtF_rnd.
 pose proof (lf_sum_error cl c2 Fcl Fc2) as E4.
 change (Rabs(c3-(cl+c2))<=trig_mul_u*Rabs(cl+c2)) in E4.
 assert (CorrectionSum:Rabs(cl+c2)<=3.3*trig_mul_u*p).
 { pose proof (Rabs_triang cl c2);lra. }
 assert (E4bound:Rabs(c3-(cl+c2))<=3.3*trig_mul_u^2*p).
 { clear - E4 CorrectionSum;unfold trig_mul_u in *;cbn [pow] in *;lra. }
 assert (C3:Rabs c3<=3.4*trig_mul_u*p).
 { pose proof (Rabs_triang (c3-(cl+c2)) (cl+c2)) as T.
   replace (c3-(cl+c2)+(cl+c2)) with c3 in T by ring.
   clear - T E4bound CorrectionSum P;unfold trig_mul_u in *;cbn [pow] in *;lra. }
 assert (Dominant:Rabs c3<=Rabs ch).
 { clear - C3 HeadMagnitude P;unfold trig_mul_u in *;lra. }
 pose proof (lf_fast_sum ch c3 Fch Fc3 Dominant) as Final.
 destruct (fast_two_sum ch c3) as [zh zl].
 destruct Final as [Fzh [Fzl [Rounded Sum]]].
 split;[exact Fzh|]. split;[exact Fzl|]. split;[rewrite Sum;exact Rounded|].
 assert (Total:Rabs(ch+c3-(xh+xl)*(yh+yl))<=8.7*trig_mul_u^2*p).
 { set (e1:=t1-xh*yl) in *;set (e2:=t2-xl*yh) in *.
   set (e3:=c2-(t1+t2)) in *;set (e4:=c3-(cl+c2)) in *.
   pose proof (Rabs_triang e1 e2) as B1.
   pose proof (Rabs_triang (e1+e2) e3) as B2.
   pose proof (Rabs_triang (e1+e2+e3) e4) as B3.
   pose proof (Rabs_triang (e1+e2+e3+e4) (-(xl*yl))) as B4.
   assert (Value:ch+c3-(xh+xl)*(yh+yl)=e1+e2+e3+e4+ -(xl*yl)).
   { unfold e1,e2,e3,e4. clear - Exact. nra. }
   rewrite <-Value,Rabs_Ropp in B4.
   clear - E1 E2 E3bound E4bound LowProduct B1 B2 B3 B4.
   unfold trig_mul_u in *;cbn [pow] in *;lra. }
 rewrite Sum. eapply Rle_trans;[exact Total|].
 clear - TargetMagnitude P. unfold trig_mul_u;cbn [pow];lra.
Qed.

Theorem trig_mul_correct xh xl yh yl :
 fmtF xh -> fmtF xl -> xh=rndF(xh+xl) ->
 fmtF yh -> fmtF yl -> yh=rndF(yh+yl) ->
 (xh*yh=0 \/ bpow radix2 (-900)<=Rabs(xh*yh)) ->
 let '(zh,zl):=mul xh xl yh yl in
 fmtF zh /\ fmtF zl /\ zh=rndF(zh+zl) /\
 Rabs(zh+zl-(xh+xl)*(yh+yl))<=9*trig_mul_u^2*Rabs((xh+xl)*(yh+yl)).
Proof.
 intros Xh Xl X Yh Yl Y [Zero|Floor].
 - rewrite (trig_mul_zero xh xl yh yl Xh Xl X Yh Yl Y Zero).
   pose proof (trig_dw_low xh xl Xh Xl X) as Lx.
   pose proof (trig_dw_low yh yl Yh Yl Y) as Ly.
   assert (Value:(xh+xl)*(yh+yl)=0).
   { apply Rmult_integral in Zero;destruct Zero as [X0|Y0].
     - rewrite X0,Rabs_R0,Rmult_0_r in Lx.
       assert (Xl0:xl=0) by (apply Rabs_le_inv in Lx;lra). rewrite X0,Xl0;ring.
     - rewrite Y0,Rabs_R0,Rmult_0_r in Ly.
       assert (Yl0:yl=0) by (apply Rabs_le_inv in Ly;lra). rewrite Y0,Yl0;ring. }
   split;[apply generic_format_0|]. split;[apply generic_format_0|].
   split;[rewrite Rplus_0_l; symmetry;apply round_0;exact _|].
   rewrite Value;replace (0+0-0) with 0 by ring;rewrite Rabs_R0;lra.
 - apply trig_mul_nonzero;assumption.
Qed.


(** IEEE execution is finite under the existing per-word overflow bound.
    Neither cross product needs to be normal or zero. *)
Theorem trig_mul_ieee xh xl yh yl :
 finite xh -> finite xl -> B xh=rndF(B xh+B xl) ->
 finite yh -> finite yl -> B yh=rndF(B yh+B yl) ->
 Rabs(B xh)<=bpow radix2 508 -> Rabs(B xl)<=bpow radix2 508 ->
 Rabs(B yh)<=bpow radix2 508 -> Rabs(B yl)<=bpow radix2 508 ->
 (B xh*B yh=0 \/ bpow radix2 (-900)<=Rabs(B xh*B yh)) ->
 let '(zh,zl):=mul64 xh xl yh yl in
 finite zh /\ finite zl /\ B zh=rndF(B zh+B zl) /\
 Rabs(B zh+B zl-(B xh+B xl)*(B yh+B yl))<=
   9/2^106*Rabs((B xh+B xl)*(B yh+B yl)).
Proof.
 intros Xh Xl X Yh Yl Y Bxh Bxl Byh Byl Domain.
 assert (U:forall v, Rabs v<=bpow radix2 508 -> bnd 1 508 v)
   by (intros v V;unfold bnd;lra).
 destruct (mul64_ok 508 xh xl yh yl Xh Xl Yh Yl
   (U _ Bxh) (U _ Bxl) (U _ Byh) (U _ Byl) ltac:(lia)) as [Fh [Fl Values]].
 pose proof (trig_mul_correct (B xh) (B xl) (B yh) (B yl)
   (B_fmt xh) (B_fmt xl) X (B_fmt yh) (B_fmt yl) Y Domain) as Bound.
 rewrite <-Values in Bound.
 destruct (mul64 xh xl yh yl) as [h l];cbn [fst snd] in *.
 destruct Bound as [_ [_ [Normal Error]]].
 split;[exact Fh|]. split;[exact Fl|]. split;[exact Normal|].
 replace (9/2^106) with (9*trig_mul_u^2) by (unfold trig_mul_u;field).
 exact Error.
Qed.
