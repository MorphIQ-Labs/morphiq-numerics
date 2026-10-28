(** Constrained cubic: independently certified on the 1024-way reduction. *)
From Coq Require Import Reals ZArith Lia Lra Psatz Classical.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Mul RoundingConstant.
From Gappa Require Import Gappa_library.
From Interval Require Import Tactic.
Require Import StageGappa ExpStageTables ExpStageReduction ExpStageA ErfcxTableEvaluation ErfcxReciprocal.
Require Import FastExpTables FastExpReduction.
Require exp_fast_cubic.
Open Scope R_scope.
Definition fast_c2_g : R := float2R (Float2 2251799831492399 (-52)).
Lemma fast_c2_g_eq : B fx_c2=fast_c2_g.
Proof. rewrite fx_c2_val. unfold fast_c2_g,float2R,F2R. simpl. bpow_num_all;lra. Qed.
Definition fast_cubic64 r :=
 let r2:=fmul r r in
 let p:=fadd fx_c2 (fmul r st_d3) in
 fadd r (fmul r2 p).
Definition fast_cubic_value r :=
 let r2:=rn(r*r) in
 let p:=rn(fast_c2_g+rn(r*d3_g)) in
 rn(r+rn(r2*p)).
Lemma fast_cubic_ieee r : finite r -> Rabs(B r)<=/1024 ->
 finite(fast_cubic64 r) /\ B(fast_cubic64 r)=fast_cubic_value(B r).
Proof.
 intros Fr Rr.
 pose proof st_d3_finite as F3;pose proof fx_c2_finite as Fc.
 assert (C3:Rabs(B st_d3)<=/4) by (rewrite st_d3_val;interval).
 assert (Cc:Rabs(B fx_c2)<=3/4) by (rewrite fx_c2_val;interval).
 pose proof Rr as Rr_copy.
 table_op fmul_bnd 1%Z (-20)%Z r r F2 V2 C2.
 table_op fmul_bnd 1%Z (-12)%Z r st_d3 Fm Vm Cm.
 table_op fadd_bnd 1%Z 0%Z fx_c2 (fmul r st_d3) Fp Vp Cp.
 table_op fmul_bnd 1%Z (-20)%Z (fmul r r) (fadd fx_c2 (fmul r st_d3)) Fv Vv Cv.
 table_op fadd_bnd 1%Z (-9)%Z r
   (fmul (fmul r r) (fadd fx_c2 (fmul r st_d3))) Fu Vu Cu.
 unfold fast_cubic64. split;[exact Fu|].
 rewrite Vu,Vv,Vp,Vm,V2,fast_c2_g_eq,d3_g_eq. reflexivity.
Qed.
Lemma fast_cubic_certificate R dr m a : Rabs R<=0.000338451 ->
 Rabs dr<=bpow radix2(-77) -> Rabs m<=bpow radix2(-74) ->
 Rabs a<=IZR 5174524961095286666344419*bpow radix2(-158) ->
 Rabs(fast_cubic_value(rn(R+dr))-(R+Qs(rn(R+dr))+m+a))<=7*bpow radix2(-56) /\
 Rabs(fast_cubic_value(rn(R+dr)))<=/1024.
Proof.
 intros HR Hd Hm Ha. unfold fast_cubic_value,fast_c2_g,Qs,half_g,d3_g,d4_g,d5_g.
 apply Rabs_le_inv in HR,Hd,Hm,Ha.
 split;apply Rabs_le;erfcx_goal (exp_fast_cubic.l1 R dr m a).
Qed.
Theorem fast_cubic_approx r R dr : finite r -> Rabs R<=0.000338451 ->
 Rabs dr<=bpow radix2(-77) -> B r=rn(R+dr) ->
 finite(fast_cubic64 r) /\ Rabs(B(fast_cubic64 r)-(exp R-1))<=7*bpow radix2(-56) /\
 Rabs(B(fast_cubic64 r))<=/1024.
Proof.
 intros Fr HR Hdr Br.
 assert (Er : Rabs (B r-(R+dr))<=bpow radix2(-64)).
 { rewrite Br. apply (rnd_err_below _ (-10));[lia|].
   eapply Rle_trans;[apply Rabs_triang|]. bpow_num_all;lra. }
 assert (Hr : Rabs(B r)<=0.00068).
 { apply Rabs_le_inv in Er. pose proof(Rabs_le_inv _ _ HR);pose proof(Rabs_le_inv _ _ Hdr).
   apply Rabs_le;bpow_num_all;lra. }
 set (m:=Qs R-Qs(B r)).
 assert (Hm:Rabs m<=bpow radix2(-74)).
 { unfold m. replace R with (B r+(R-B r)) at 1 by ring.
   apply stage_mvt_bound;[exact Hr|].
   apply Rabs_le_inv in Er. pose proof(Rabs_le_inv _ _ Hdr).
   apply Rabs_le;bpow_num_all;lra. }
 set (a:=exp R-1-R-Qs R).
 assert (Ha:Rabs a<=IZR 5174524961095286666344419*bpow radix2(-158)).
 { pose proof (st_poly_approx R ltac:(lra)) as A. unfold st_poly_bound,Rdiv in A.
   rewrite <-(bpow_m 158) in A. rewrite d3_g_eq,d4_g_eq,d5_g_eq in A.
   unfold a,Qs. rewrite half_g_eq. replace (/2) with (1/2) by field. exact A. }
 destruct (fast_cubic_ieee r Fr ltac:(lra)) as [Fu Vu].
 destruct (fast_cubic_certificate R dr m a HR Hdr Hm Ha) as [Error Range].
 rewrite <-Br,<-Vu in Error,Range.
 assert (Id:R+Qs(B r)+m+a=exp R-1) by (unfold m,a;ring).
 rewrite Id in Error. repeat split;assumption.
Qed.
