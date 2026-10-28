(** Bounded exponential's quartic, using the existing reduction and coefficients. *)
From Coq Require Import Reals ZArith Lia Lra Psatz Classical.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Mul RoundingConstant.
From Gappa Require Import Gappa_library.
From Interval Require Import Tactic.
Require Import StageGappa ExpStageTables ExpStageReduction ExpStageA ErfcxTableEvaluation ErfcxReciprocal.
Require exp_fast_quartic.
Open Scope R_scope.
Definition fast_quartic64 r :=
 let r2:=fmul r r in
 let left:=fadd r (fmul c_half r2) in
 let p:=fadd st_d3 (fmul r st_d4) in
 fadd left (fmul (fmul r2 r) p).
Definition fast_quartic_value r :=
 let r2:=rn(r*r) in
 let left:=rn(r+rn(half_g*r2)) in
 let p:=rn(d3_g+rn(r*d4_g)) in
 rn(left+rn(rn(r2*r)*p)).
Lemma fast_quartic_ieee r : finite r -> Rabs(B r)<=/1024 ->
 finite(fast_quartic64 r) /\ B(fast_quartic64 r)=fast_quartic_value(B r).
Proof.
 intros Fr Rr.
 pose proof st_d3_finite as F3;pose proof st_d4_finite as F4;pose proof c_half_finite as Fhalf.
 assert (C3:Rabs(B st_d3)<=/4) by (rewrite st_d3_val;interval).
 assert (C4:Rabs(B st_d4)<=/16) by (rewrite st_d4_val;interval).
 assert (Ch:Rabs(B c_half)<=/2) by (rewrite c_half_g,half_g_eq;rewrite Rabs_pos_eq;lra).
 pose proof Rr as Rr_copy.
 table_op fmul_bnd 1%Z (-20)%Z r r F2 V2 C2.
 table_op fmul_bnd 1%Z (-21)%Z c_half (fmul r r) Fh Vh Chh.
 table_op fadd_bnd 1%Z (-9)%Z r (fmul c_half (fmul r r)) Fl Vl Cl.
 table_op fmul_bnd 1%Z (-14)%Z r st_d4 Fm Vm Cm.
 table_op fadd_bnd 1%Z (-1)%Z st_d3 (fmul r st_d4) Fp Vp Cp.
 table_op fmul_bnd 1%Z (-30)%Z (fmul r r) r Fcube Vcube Ccube.
 table_op fmul_bnd 1%Z (-31)%Z (fmul (fmul r r) r) (fadd st_d3 (fmul r st_d4)) Fv Vv Cv.
 table_op fadd_bnd 1%Z (-8)%Z (fadd r (fmul c_half (fmul r r)))
   (fmul (fmul (fmul r r) r) (fadd st_d3 (fmul r st_d4))) Fu Vu Cu.
 unfold fast_quartic64. split;[exact Fu|].
 rewrite Vu,Vl,Vv,Vcube,Vp,Vm,Vh,V2,c_half_g,d3_g_eq,d4_g_eq. reflexivity.
Qed.
Lemma fast_quartic_certificate R dr m a : Rabs R<=0.000677 ->
 Rabs dr<=bpow radix2(-77) -> Rabs m<=bpow radix2(-74) ->
 Rabs a<=IZR 5174524961095286666344419*bpow radix2(-158) ->
 Rabs(fast_quartic_value(rn(R+dr))-(R+Qs(rn(R+dr))+m+a))<=bpow radix2(-59) /\
 Rabs(fast_quartic_value(rn(R+dr)))<=/1024.
Proof.
 intros HR Hd Hm Ha. unfold fast_quartic_value,Qs,half_g,d3_g,d4_g,d5_g.
 apply Rabs_le_inv in HR,Hd,Hm,Ha.
 split;apply Rabs_le;erfcx_goal (exp_fast_quartic.l1 R dr m a).
Qed.
Theorem fast_quartic_approx r R dr : finite r -> Rabs R<=0.000677 ->
 Rabs dr<=bpow radix2(-77) -> B r=rn(R+dr) ->
 finite(fast_quartic64 r) /\ Rabs(B(fast_quartic64 r)-(exp R-1))<=bpow radix2(-59) /\
 Rabs(B(fast_quartic64 r))<=/1024.
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
 { pose proof (st_poly_approx R HR) as A. unfold st_poly_bound,Rdiv in A.
   rewrite <-(bpow_m 158) in A. rewrite d3_g_eq,d4_g_eq,d5_g_eq in A.
   unfold a,Qs. rewrite half_g_eq. replace (/2) with (1/2) by field. exact A. }
 destruct (fast_quartic_ieee r Fr ltac:(lra)) as [Fu Vu].
 destruct (fast_quartic_certificate R dr m a HR Hdr Hm Ha) as [Error Range].
 rewrite <-Br,<-Vu in Error,Range.
 assert (Id:R+Qs(B r)+m+a=exp R-1) by (unfold m,a;ring).
 rewrite Id in Error. repeat split;assumption.
Qed.
