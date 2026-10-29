(** Paired bounded central CDF: IEEE transcription and arithmetic certificate. *)
From Coq Require Import Reals ZArith Lia Lra Psatz Classical.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Mul RoundingConstant RoundingTest RoundingGaps.
From Gappa Require Import Gappa_library.
From Interval Require Import Tactic.
Require Import StageGappa ErfcxTableEvaluation ErfcxTableCertificateModel NormalConstants NormalCentered Expm1Series ErfcxFactorial NormalCenterFastConstants NormalCenterFastAnalytic NormalCenterFastTail FastNormalCentralAnalytic ExpStageA ErfcxReciprocal.
Require normal_fast_center.
Open Scope R_scope.
Definition fast_normal_center64 x :=
 let z:=fmul x x in let zz:=fmul z z in
 let p0:=fadd normal_center_0_hi (fmul z normal_center_1_hi) in
 let p1:=fadd normal_center_2_hi (fmul z normal_center_3_hi) in
 let p2:=fadd normal_center_4_hi (fmul z normal_center_5_hi) in
 let p3:=fadd normal_center_6_hi (fmul z normal_center_7_hi) in
 let p4:=fadd normal_center_8_hi (fmul z normal_center_9_hi) in
 let p5:=fadd normal_center_10_hi (fmul z normal_center_11_hi) in
 let y6:=normal_center_12_hi in
 let y5:=fadd p5 (fmul zz y6) in
 let y4:=fadd p4 (fmul zz y5) in
 let y3:=fadd p3 (fmul zz y4) in
 let y2:=fadd p2 (fmul zz y3) in
 let y1:=fadd p1 (fmul zz y2) in
 let y0:=fadd p0 (fmul zz y1) in
 fadd c_half (fmul (fmul x normal_density_hi) y0).
Definition fast_normal_center_value x :=
 let z:=rn(x*x) in let zz:=rn(z*z) in
 let p0:=rn(B normal_center_0_hi+rn(z*B normal_center_1_hi)) in
 let p1:=rn(B normal_center_2_hi+rn(z*B normal_center_3_hi)) in
 let p2:=rn(B normal_center_4_hi+rn(z*B normal_center_5_hi)) in
 let p3:=rn(B normal_center_6_hi+rn(z*B normal_center_7_hi)) in
 let p4:=rn(B normal_center_8_hi+rn(z*B normal_center_9_hi)) in
 let p5:=rn(B normal_center_10_hi+rn(z*B normal_center_11_hi)) in
 let y6:=B normal_center_12_hi in
 let y5:=rn(p5+rn(zz*y6)) in
 let y4:=rn(p4+rn(zz*y5)) in
 let y3:=rn(p3+rn(zz*y4)) in
 let y2:=rn(p2+rn(zz*y3)) in
 let y1:=rn(p1+rn(zz*y2)) in
 let y0:=rn(p0+rn(zz*y1)) in
 rn(B c_half+rn(rn(x*B normal_density_hi)*y0)).
Definition fast_normal_center_ideal x :=
 let z:=x*x in let zz:=z*z in
 let p0:=normal_fast_center_coefficient 0+z*normal_fast_center_coefficient 1 in
 let p1:=normal_fast_center_coefficient 2+z*normal_fast_center_coefficient 3 in
 let p2:=normal_fast_center_coefficient 4+z*normal_fast_center_coefficient 5 in
 let p3:=normal_fast_center_coefficient 6+z*normal_fast_center_coefficient 7 in
 let p4:=normal_fast_center_coefficient 8+z*normal_fast_center_coefficient 9 in
 let p5:=normal_fast_center_coefficient 10+z*normal_fast_center_coefficient 11 in
 let y6:=normal_fast_center_coefficient 12 in
 let y5:=p5+zz*y6 in
 let y4:=p4+zz*y5 in
 let y3:=p3+zz*y4 in
 let y2:=p2+zz*y3 in
 let y1:=p1+zz*y2 in
 let y0:=p0+zz*y1 in
 /2+x*normal_density_constant*y0.
Lemma fast_normal_center_ieee x : finite x -> Rabs(B x)<=1 ->
 finite(fast_normal_center64 x) /\ B(fast_normal_center64 x)=fast_normal_center_value(B x).
Proof.
 intros Fx X. pose proof X as Xcopy.
 destruct normal_center_0_hi_ok as [F0 W0].
 assert (C0:Rabs(B normal_center_0_hi)<=1) by (rewrite W0;replace (1/1) with 1 by field;rewrite Rabs_R1;lra).
 destruct normal_center_1_hi_ok as [F1 W1].
 assert (C1:Rabs(B normal_center_1_hi)<=1) by (rewrite W1;interval).
 destruct normal_center_2_hi_ok as [F2 W2].
 assert (C2:Rabs(B normal_center_2_hi)<=1) by (rewrite W2;interval).
 destruct normal_center_3_hi_ok as [F3 W3].
 assert (C3:Rabs(B normal_center_3_hi)<=1) by (rewrite W3;interval).
 destruct normal_center_4_hi_ok as [F4 W4].
 assert (C4:Rabs(B normal_center_4_hi)<=1) by (rewrite W4;interval).
 destruct normal_center_5_hi_ok as [F5 W5].
 assert (C5:Rabs(B normal_center_5_hi)<=1) by (rewrite W5;interval).
 destruct normal_center_6_hi_ok as [F6 W6].
 assert (C6:Rabs(B normal_center_6_hi)<=1) by (rewrite W6;interval).
 destruct normal_center_7_hi_ok as [F7 W7].
 assert (C7:Rabs(B normal_center_7_hi)<=1) by (rewrite W7;interval).
 destruct normal_center_8_hi_ok as [F8 W8].
 assert (C8:Rabs(B normal_center_8_hi)<=1) by (rewrite W8;interval).
 destruct normal_center_9_hi_ok as [F9 W9].
 assert (C9:Rabs(B normal_center_9_hi)<=1) by (rewrite W9;interval).
 destruct normal_center_10_hi_ok as [F10 W10].
 assert (C10:Rabs(B normal_center_10_hi)<=1) by (rewrite W10;interval).
 destruct normal_center_11_hi_ok as [F11 W11].
 assert (C11:Rabs(B normal_center_11_hi)<=1) by (rewrite W11;interval).
 destruct normal_center_12_hi_ok as [F12 W12].
 assert (C12:Rabs(B normal_center_12_hi)<=1) by (rewrite W12;interval).
 destruct normal_density_hi_ok as [Fd Wd].
 assert (Cd:Rabs(B normal_density_hi)<=/2) by (rewrite Wd;interval).
 pose proof c_half_finite as Fh.
 assert (Ch:Rabs(B c_half)<=/2) by (rewrite c_half_g,half_g_eq;rewrite Rabs_pos_eq;lra).
 table_op fmul_bnd 1%Z 0%Z x x Fz Vz Cz.
 set (z:=fmul x x) in *. pose proof Cz as Czcopy.
 table_op fmul_bnd 1%Z 0%Z z z Fzz Vzz Czz.
 set (zz:=fmul z z) in *.
 table_op fmul_bnd 1%Z 0%Z z normal_center_1_hi Fm0 Vm0 Cm0.
 table_op fadd_bnd 2%Z 0%Z normal_center_0_hi (fmul z normal_center_1_hi) Fp0 Vp0 Cp0.
 set (p0:=fadd normal_center_0_hi (fmul z normal_center_1_hi)) in *.
 table_op fmul_bnd 1%Z 0%Z z normal_center_3_hi Fm1 Vm1 Cm1.
 table_op fadd_bnd 2%Z 0%Z normal_center_2_hi (fmul z normal_center_3_hi) Fp1 Vp1 Cp1.
 set (p1:=fadd normal_center_2_hi (fmul z normal_center_3_hi)) in *.
 table_op fmul_bnd 1%Z 0%Z z normal_center_5_hi Fm2 Vm2 Cm2.
 table_op fadd_bnd 2%Z 0%Z normal_center_4_hi (fmul z normal_center_5_hi) Fp2 Vp2 Cp2.
 set (p2:=fadd normal_center_4_hi (fmul z normal_center_5_hi)) in *.
 table_op fmul_bnd 1%Z 0%Z z normal_center_7_hi Fm3 Vm3 Cm3.
 table_op fadd_bnd 2%Z 0%Z normal_center_6_hi (fmul z normal_center_7_hi) Fp3 Vp3 Cp3.
 set (p3:=fadd normal_center_6_hi (fmul z normal_center_7_hi)) in *.
 table_op fmul_bnd 1%Z 0%Z z normal_center_9_hi Fm4 Vm4 Cm4.
 table_op fadd_bnd 2%Z 0%Z normal_center_8_hi (fmul z normal_center_9_hi) Fp4 Vp4 Cp4.
 set (p4:=fadd normal_center_8_hi (fmul z normal_center_9_hi)) in *.
 table_op fmul_bnd 1%Z 0%Z z normal_center_11_hi Fm5 Vm5 Cm5.
 table_op fadd_bnd 2%Z 0%Z normal_center_10_hi (fmul z normal_center_11_hi) Fp5 Vp5 Cp5.
 set (p5:=fadd normal_center_10_hi (fmul z normal_center_11_hi)) in *.
 set (y6:=normal_center_12_hi) in *.
 table_op fmul_bnd 1%Z 0%Z zz y6 Ft5 Vt5 Ct5.
 table_op fadd_bnd 3%Z 0%Z p5 (fmul zz y6) Fy5 Vy5 Cy5.
 set (y5:=fadd p5 (fmul zz y6)) in *.
 table_op fmul_bnd 3%Z 0%Z zz y5 Ft4 Vt4 Ct4.
 table_op fadd_bnd 5%Z 0%Z p4 (fmul zz y5) Fy4 Vy4 Cy4.
 set (y4:=fadd p4 (fmul zz y5)) in *.
 table_op fmul_bnd 5%Z 0%Z zz y4 Ft3 Vt3 Ct3.
 table_op fadd_bnd 7%Z 0%Z p3 (fmul zz y4) Fy3 Vy3 Cy3.
 set (y3:=fadd p3 (fmul zz y4)) in *.
 table_op fmul_bnd 7%Z 0%Z zz y3 Ft2 Vt2 Ct2.
 table_op fadd_bnd 9%Z 0%Z p2 (fmul zz y3) Fy2 Vy2 Cy2.
 set (y2:=fadd p2 (fmul zz y3)) in *.
 table_op fmul_bnd 9%Z 0%Z zz y2 Ft1 Vt1 Ct1.
 table_op fadd_bnd 11%Z 0%Z p1 (fmul zz y2) Fy1 Vy1 Cy1.
 set (y1:=fadd p1 (fmul zz y2)) in *.
 table_op fmul_bnd 11%Z 0%Z zz y1 Ft0 Vt0 Ct0.
 table_op fadd_bnd 13%Z 0%Z p0 (fmul zz y1) Fy0 Vy0 Cy0.
 set (y0:=fadd p0 (fmul zz y1)) in *.
 table_op fmul_bnd 1%Z (-1)%Z x normal_density_hi Fdx Vdx Cdx.
 table_op fmul_bnd 13%Z (-1)%Z (fmul x normal_density_hi) y0 Fv Vv Cv.
 table_op fadd_bnd 7%Z 0%Z c_half (fmul (fmul x normal_density_hi) y0) Fy Vy Cy.
 unfold fast_normal_center64;fold z zz p0 p1 p2 p3 p4 p5 y6 y5 y4 y3 y2 y1 y0.
 split;[exact Fy|].
 rewrite Vy,Vv,Vdx,Vy0,Vt0,Vy1,Vt1,Vy2,Vt2,Vy3,Vt3,Vy4,Vt4,Vy5,Vt5,Vp0,Vm0,Vp1,Vm1,Vp2,Vm2,Vp3,Vm3,Vp4,Vm4,Vp5,Vm5,Vzz,Vz.
 reflexivity.
Qed.
Lemma fast_normal_center_ideal_eq x : fast_normal_center_ideal x=/2+normal_center_polynomial 12 x.
Proof.
 unfold fast_normal_center_ideal,normal_center_polynomial.
 rewrite <-(normal_center_mixed_polynomial x).
 unfold normal_center_mixed_shape;cbn [normal_center_tail_polynomial].
 unfold normal_fast_center_coefficient;binary_factorials;repeat rewrite INR_IZR_INZ;small_numerals;cbn [Nat.sub];field.
Qed.
Lemma fast_center_0_g : B normal_center_0_hi=Float1 (1).
Proof. unfold normal_center_0_hi;apply word_integer_ok;vm_compute;reflexivity. Qed.
Lemma fast_center_1_g : B normal_center_1_hi=float2R (Float2 (-6004799503160661) (-55)).
Proof. unfold normal_center_1_hi;apply word_value_ok;vm_compute;reflexivity. Qed.
Lemma fast_center_2_g : B normal_center_2_hi=float2R (Float2 (3602879701896397) (-57)).
Proof. unfold normal_center_2_hi;apply word_value_ok;vm_compute;reflexivity. Qed.
Lemma fast_center_3_g : B normal_center_3_hi=float2R (Float2 (-857828500451523) (-58)).
Proof. unfold normal_center_3_hi;apply word_value_ok;vm_compute;reflexivity. Qed.
Lemma fast_center_4_g : B normal_center_4_hi=float2R (Float2 (667199944795629) (-61)).
Proof. unfold normal_center_4_hi;apply word_value_ok;vm_compute;reflexivity. Qed.
Lemma fast_center_5_g : B normal_center_5_hi=float2R (Float2 (-6987403058223315) (-68)).
Proof. unfold normal_center_5_hi;apply word_value_ok;vm_compute;reflexivity. Qed.
Lemma fast_center_6_g : B normal_center_6_hi=float2R (Float2 (1970805990780935) (-70)).
Proof. unfold normal_center_6_hi;apply word_value_ok;vm_compute;reflexivity. Qed.
Lemma fast_center_7_g : B normal_center_7_hi=float2R (Float2 (-7808145639665419) (-76)).
Proof. unfold normal_center_7_hi;apply word_value_ok;vm_compute;reflexivity. Qed.
Lemma fast_center_8_g : B normal_center_8_hi=float2R (Float2 (861192533786627) (-77)).
Proof. unfold normal_center_8_hi;apply word_value_ok;vm_compute;reflexivity. Qed.
Lemma fast_center_9_g : B normal_center_9_hi=float2R (Float2 (-5479400448888013) (-84)).
Proof. unfold normal_center_9_hi;apply word_value_ok;vm_compute;reflexivity. Qed.
Lemma fast_center_10_g : B normal_center_10_hi=float2R (Float2 (991510557417831) (-86)).
Proof. unfold normal_center_10_hi;apply word_value_ok;vm_compute;reflexivity. Qed.
Lemma fast_center_11_g : B normal_center_11_hi=float2R (Float2 (-2633577448951709) (-92)).
Proof. unfold normal_center_11_hi;apply word_value_ok;vm_compute;reflexivity. Qed.
Lemma fast_center_12_g : B normal_center_12_hi=float2R (Float2 (6461043341428193) (-98)).
Proof. unfold normal_center_12_hi;apply word_value_ok;vm_compute;reflexivity. Qed.
Lemma fast_center_density_g : B normal_density_hi=float2R (Float2 (7186705221432913) (-54)).
Proof. unfold normal_density_hi;apply word_value_ok;vm_compute;reflexivity. Qed.
Definition fast_normal_center_exact_value x d := half_g+x*d*((1/1+x*x*(-1/6)+x*x*(x*x)*((1/40+x*x*(-1/336)+x*x*(x*x)*((1/3456+x*x*(-1/42240)+x*x*(x*x)*((1/599040+x*x*(-1/9676800)+x*x*(x*x)*((1/175472640+x*x*(-1/3530096640)+x*x*(x*x)*((1/78033715200+x*x*(-1/1880240947200)+x*x*(x*x)*(1/49049763840000))))))))))))).
Lemma fast_normal_center_exact_eq x :
 fast_normal_center_ideal x=fast_normal_center_exact_value x normal_density_constant.
Proof.
 unfold fast_normal_center_ideal,fast_normal_center_exact_value,normal_fast_center_coefficient.
 rewrite half_g_eq. binary_factorials;repeat rewrite INR_IZR_INZ;small_numerals;field.
Qed.
Theorem fast_normal_center_arithmetic x : Rabs x<=1 -> F64 x ->
 Rabs(fast_normal_center_value x-fast_normal_center_ideal x)<=bpow radix2(-51) /\
 /64<=fast_normal_center_value x<=1.
Proof.
 intros X F. assert (Rx:rn x=x) by (apply round_generic;[exact _|exact F]).
 set (delta:=normal_density_constant-B normal_density_hi).
 assert (D:Rabs delta<=bpow radix2(-54)).
 { unfold delta,normal_density_constant;rewrite (proj2 normal_density_hi_ok);bpow_num;interval with(i_prec 100). }
 assert (Density:normal_density_constant=B normal_density_hi+delta) by (unfold delta;ring).
 rewrite fast_normal_center_exact_eq.
 unfold fast_normal_center_value,fast_normal_center_exact_value;rewrite Density.
 rewrite c_half_g,fast_center_0_g,fast_center_1_g,fast_center_2_g,fast_center_3_g,fast_center_4_g,fast_center_5_g,fast_center_6_g,fast_center_7_g,fast_center_8_g,fast_center_9_g,fast_center_10_g,fast_center_11_g,fast_center_12_g,fast_center_density_g.
 unfold half_g.
 apply Rabs_le_inv in X,D.
 rewrite <-Rx.
 split;[apply Rabs_le|];repeat split;erfcx_goal (normal_fast_center.l1 x delta).
Qed.

Theorem fast_normal_center_ok x : finite x -> Rabs(B x)<=1 ->
 finite(fast_normal_center64 x) /\ /64<=B(fast_normal_center64 x)<=1 /\
 Rabs(B(fast_normal_center64 x)-(/2+normal_center(B x)))<=7*bpow radix2(-53).
Proof.
 intros Fx X. destruct (fast_normal_center_ieee x Fx X) as [Fy Vy].
 destruct (fast_normal_center_arithmetic (B x) X (B_fmt x)) as [Arithmetic Range].
 pose proof (fast_normal_center_truncation (B x) X) as Truncation.
 rewrite fast_normal_center_ideal_eq in Arithmetic.
 split;[exact Fy|];rewrite Vy;split;[exact Range|].
 replace (fast_normal_center_value(B x)-(/2+normal_center(B x))) with
   ((fast_normal_center_value(B x)-(/2+normal_center_polynomial 12 (B x)))+
    (normal_center_polynomial 12 (B x)-normal_center(B x))) by ring.
 eapply Rle_trans;[apply Rabs_triang|].
 rewrite Rabs_minus_sym in Truncation. bpow_num_all;lra.
Qed.
