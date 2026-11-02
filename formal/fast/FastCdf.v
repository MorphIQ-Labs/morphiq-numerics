(** Bounded normal CDF: the actual binary64 scalar sequence of
    [fast/cdf.rs], its arithmetic certificates (formal/normal/fast_cdf_*.g),
    and the composed contract: absolute error at most [2^-49] on
    [2^-33 <= |x| <= 8], and relative error at most [2^-48] for [x < 0]. *)
From Coq Require Import Reals ZArith Lia Lra Psatz Bool Classical.
From Coquelicot Require Import Coquelicot.
From Flocq Require Import Core Mult_error IEEE754.Binary IEEE754.Bits.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add Binary64Mul IEEE64 IEEE64Add IEEE64Mul IEEE64Eft Encodings
  RoundingCore RoundingConstant RoundingGaps RoundingTest.
From Gappa Require Import Gappa_library.
Require Import StageGappa ErfcxDecision ErfcxPublicModel ErfcxConstants ErfcxTaylorODE ErfcxGaussianTarget
  ErfcxTableEvaluation ErfcxReciprocal NormalConstants NormalComparisons NormalCentered
  NormalTailAnalytic NormalErfcxSensitivity NormalErfcxFastScaled NormalPublicEntry NormalPublicModel
  NormalAccurateCentralCdf NormalFastDispatch FastExp FastNormalArgument FastCdfConstants FastCdfOde
  FastCdfApprox FastCdfBody.
Require normal_fast_cdf_body normal_fast_cdf_tail.
Open Scope R_scope.

Definition cdf_half : f64 := erfcx_pow2 (-1).
Definition cdf_limit : f64 := b64_of_bits 4602115869219225600.

Lemma cdf_half_ok : finite cdf_half /\ B cdf_half=/2.
Proof. destruct (erfcx_pow2_ok (-1) ltac:(lia)) as [F V]. unfold cdf_half. split;[exact F|rewrite V;reflexivity]. Qed.
Lemma cdf_half_g : B cdf_half=float2R (Float2 1 (-1)).
Proof. rewrite (proj2 cdf_half_ok). change (float2R (Float2 1 (-1))) with (IZR 1*bpow radix2 (-1)). bpow_num. simpl. lra. Qed.
Lemma cdf_limit_ok : finite cdf_limit /\ B cdf_limit=15/32.
Proof.
  split;[exact (bits_finite 4602115869219225600 false 8444249301319680 (-54) eq_refl)|].
  unfold cdf_limit. rewrite (bits_val 4602115869219225600 false 8444249301319680 54 eq_refl).
  simpl. field.
Qed.

(** {1 The body: [y = RN(x/sqrt 2)], [|y| <= 15/32]} *)

Definition fast_cdf_body64 x :=
  let y:=fmul x normal_inv_sqrt2_hi in
  let s:=fmul y y in let s2:=fmul s s in let s4:=fmul s2 s2 in
  let a0:=fadd cdf_body_0 (fmul s cdf_body_1) in
  let a1:=fadd cdf_body_2 (fmul s cdf_body_3) in
  let a2:=fadd cdf_body_4 (fmul s cdf_body_5) in
  let a3:=fadd cdf_body_6 (fmul s cdf_body_7) in
  let b0:=fadd a0 (fmul s2 a1) in
  let b1:=fadd a2 (fmul s2 a3) in
  let p:=fadd (fadd b0 (fmul s4 b1)) (fmul (fmul s4 s4) cdf_body_8) in
  fadd cdf_half (fmul cdf_half (fmul y p)).
Definition fast_cdf_body_value y :=
  let s:=rn(y*y) in let s2:=rn(s*s) in let s4:=rn(s2*s2) in
  let a0:=rn(B cdf_body_0+rn(s*B cdf_body_1)) in
  let a1:=rn(B cdf_body_2+rn(s*B cdf_body_3)) in
  let a2:=rn(B cdf_body_4+rn(s*B cdf_body_5)) in
  let a3:=rn(B cdf_body_6+rn(s*B cdf_body_7)) in
  let b0:=rn(a0+rn(s2*a1)) in
  let b1:=rn(a2+rn(s2*a3)) in
  let p:=rn(rn(b0+rn(s4*b1))+rn(rn(s4*s4)*B cdf_body_8)) in
  rn(B cdf_half+rn(B cdf_half*rn(y*p))).
Definition fast_cdf_body_ideal y :=
  let S:=y*y in let S2:=S*S in let S4:=S2*S2 in
  let A0:=B cdf_body_0+S*B cdf_body_1 in
  let A1:=B cdf_body_2+S*B cdf_body_3 in
  let A2:=B cdf_body_4+S*B cdf_body_5 in
  let A3:=B cdf_body_6+S*B cdf_body_7 in
  let B0:=A0+S2*A1 in let B1:=A2+S2*A3 in
  let P:=(B0+S4*B1)+S4*S4*B cdf_body_8 in
  B cdf_half+B cdf_half*(y*P).

Lemma fast_cdf_body_ieee x : finite x -> Rabs (B (fmul x normal_inv_sqrt2_hi))<=/2 ->
  finite (fmul x normal_inv_sqrt2_hi) ->
  finite (fast_cdf_body64 x) /\
  B (fast_cdf_body64 x)=fast_cdf_body_value (B (fmul x normal_inv_sqrt2_hi)).
Proof.
  intros Fx Y Fy. set (y:=fmul x normal_inv_sqrt2_hi) in *.
  pose proof cdf_body_0_finite as F0. pose proof cdf_body_1_finite as F1.
  pose proof cdf_body_2_finite as F2. pose proof cdf_body_3_finite as F3.
  pose proof cdf_body_4_finite as F4. pose proof cdf_body_5_finite as F5.
  pose proof cdf_body_6_finite as F6. pose proof cdf_body_7_finite as F7.
  pose proof cdf_body_8_finite as F8.
  assert (C0 : Rabs (B cdf_body_0)<=2) by (rewrite cdf_body_0_val;interval).
  assert (C1 : Rabs (B cdf_body_1)<=/2) by (rewrite cdf_body_1_val;interval).
  assert (C2 : Rabs (B cdf_body_2)<=/2) by (rewrite cdf_body_2_val;interval).
  assert (C3 : Rabs (B cdf_body_3)<=/2) by (rewrite cdf_body_3_val;interval).
  assert (C4 : Rabs (B cdf_body_4)<=/2) by (rewrite cdf_body_4_val;interval).
  assert (C5 : Rabs (B cdf_body_5)<=/2) by (rewrite cdf_body_5_val;interval).
  assert (C6 : Rabs (B cdf_body_6)<=/2) by (rewrite cdf_body_6_val;interval).
  assert (C7 : Rabs (B cdf_body_7)<=/2) by (rewrite cdf_body_7_val;interval).
  assert (C8 : Rabs (B cdf_body_8)<=/2) by (rewrite cdf_body_8_val;interval).
  destruct cdf_half_ok as [Fh Hh].
  assert (Ch : Rabs (B cdf_half)<=/2) by (rewrite Hh,Rabs_pos_eq;lra).
  pose proof Y as Ycopy.
  table_op fmul_bnd 1%Z (-2)%Z y y Fs Vs Cs. set (s:=fmul y y) in *. pose proof Cs as Cscopy.
  table_op fmul_bnd 1%Z (-4)%Z s s Fs2 Vs2 Cs2. set (s2:=fmul s s) in *. pose proof Cs2 as Cs2copy.
  table_op fmul_bnd 1%Z (-8)%Z s2 s2 Fs4 Vs4 Cs4. set (s4:=fmul s2 s2) in *. pose proof Cs4 as Cs4copy.
  table_op fmul_bnd 1%Z (-3)%Z s cdf_body_1 Fm0 Vm0 Cm0.
  table_op fadd_bnd 3%Z 0%Z cdf_body_0 (fmul s cdf_body_1) Fa0 Va0 Ca0.
  set (a0:=fadd cdf_body_0 (fmul s cdf_body_1)) in *.
  table_op fmul_bnd 1%Z (-3)%Z s cdf_body_3 Fm1 Vm1 Cm1.
  table_op fadd_bnd 1%Z 0%Z cdf_body_2 (fmul s cdf_body_3) Fa1 Va1 Ca1.
  set (a1:=fadd cdf_body_2 (fmul s cdf_body_3)) in *.
  table_op fmul_bnd 1%Z (-3)%Z s cdf_body_5 Fm2 Vm2 Cm2.
  table_op fadd_bnd 1%Z 0%Z cdf_body_4 (fmul s cdf_body_5) Fa2 Va2 Ca2.
  set (a2:=fadd cdf_body_4 (fmul s cdf_body_5)) in *.
  table_op fmul_bnd 1%Z (-3)%Z s cdf_body_7 Fm3 Vm3 Cm3.
  table_op fadd_bnd 1%Z 0%Z cdf_body_6 (fmul s cdf_body_7) Fa3 Va3 Ca3.
  set (a3:=fadd cdf_body_6 (fmul s cdf_body_7)) in *.
  table_op fmul_bnd 1%Z (-4)%Z s2 a1 Fn0 Vn0 Cn0.
  table_op fadd_bnd 4%Z 0%Z a0 (fmul s2 a1) Fb0 Vb0 Cb0.
  set (b0:=fadd a0 (fmul s2 a1)) in *.
  table_op fmul_bnd 1%Z (-4)%Z s2 a3 Fn1 Vn1 Cn1.
  table_op fadd_bnd 2%Z 0%Z a2 (fmul s2 a3) Fb1 Vb1 Cb1.
  set (b1:=fadd a2 (fmul s2 a3)) in *.
  table_op fmul_bnd 1%Z (-6)%Z s4 b1 Fq0 Vq0 Cq0.
  table_op fadd_bnd 5%Z 0%Z b0 (fmul s4 b1) Fc0 Vc0 Cc0.
  table_op fmul_bnd 1%Z (-16)%Z s4 s4 Fs8 Vs8 Cs8.
  table_op fmul_bnd 1%Z (-17)%Z (fmul s4 s4) cdf_body_8 Fq1 Vq1 Cq1.
  table_op fadd_bnd 6%Z 0%Z (fadd b0 (fmul s4 b1)) (fmul (fmul s4 s4) cdf_body_8) Fp Vp Cp.
  set (p:=fadd (fadd b0 (fmul s4 b1)) (fmul (fmul s4 s4) cdf_body_8)) in *.
  table_op fmul_bnd 3%Z 0%Z y p Fyp Vyp Cyp.
  table_op fmul_bnd 2%Z 0%Z cdf_half (fmul y p) Fhp Vhp Chp.
  table_op fadd_bnd 3%Z 0%Z cdf_half (fmul cdf_half (fmul y p)) Fv Vv Cv.
  unfold fast_cdf_body64. fold y s s2 s4 a0 a1 a2 a3 b0 b1 p.
  split;[exact Fv|].
  rewrite Vv,Vhp,Vyp,Vp,Vq1,Vs8,Vc0,Vq0,Vb1,Vn1,Vb0,Vn0,Va3,Vm3,Va2,Vm2,Va1,Vm1,Va0,Vm0,Vs4,Vs2,Vs.
  reflexivity.
Qed.

Theorem fast_cdf_body_arithmetic y : F64 y -> Rabs y<=15/32 ->
  Rabs (fast_cdf_body_value y-fast_cdf_body_ideal y)<=bpow radix2 (-52) /\
  29/128<=fast_cdf_body_value y<=25/32.
Proof.
  intros F Y. assert (Ry : rn y=y) by (apply round_generic;[exact _|exact F]).
  apply Rabs_le_inv in Y.
  unfold fast_cdf_body_value,fast_cdf_body_ideal. cbv zeta.
  rewrite cdf_half_g,cdf_body_0_g,cdf_body_1_g,cdf_body_2_g,cdf_body_3_g,cdf_body_4_g,
    cdf_body_5_g,cdf_body_6_g,cdf_body_7_g,cdf_body_8_g.
  rewrite <-Ry.
  split;[apply Rabs_le|];repeat split;erfcx_goal (normal_fast_cdf_body.l1 y).
Qed.

Lemma fast_cdf_body_ideal_eq y : fast_cdf_body_ideal y=/2+/2*(y*cdf_body_poly(y*y)).
Proof.
  unfold fast_cdf_body_ideal,cdf_body_poly,cdf_body_words. cbn [cdf_horner].
  rewrite (proj2 cdf_half_ok). ring.
Qed.

(** {1 The tail rational at [y = RN(a/sqrt 2)], [15/32 < y <= RN(8/sqrt 2)]} *)

Definition fast_cdf_num64 y y2 y4 y8 :=
  let a0:=fadd cdf_num_0 (fmul y cdf_num_1) in
  let a1:=fadd cdf_num_2 (fmul y cdf_num_3) in
  let a2:=fadd cdf_num_4 (fmul y cdf_num_5) in
  let a3:=fadd cdf_num_6 (fmul y cdf_num_7) in
  fadd (fadd (fadd a0 (fmul y2 a1)) (fmul y4 (fadd a2 (fmul y2 a3)))) (fmul y8 cdf_num_8).
Definition fast_cdf_den64 y y2 y4 y8 :=
  let a0:=fadd cdf_den_0 (fmul y cdf_den_1) in
  let a1:=fadd cdf_den_2 (fmul y cdf_den_3) in
  let a2:=fadd cdf_den_4 (fmul y cdf_den_5) in
  let a3:=fadd cdf_den_6 (fmul y cdf_den_7) in
  let a4:=fadd cdf_den_8 (fmul y cdf_den_9) in
  fadd (fadd (fadd a0 (fmul y2 a1)) (fmul y4 (fadd a2 (fmul y2 a3)))) (fmul y8 a4).
Definition fast_cdf_ratio64 y :=
  let y2:=fmul y y in let y4:=fmul y2 y2 in let y8:=fmul y4 y4 in
  fdiv (fast_cdf_num64 y y2 y4 y8) (fast_cdf_den64 y y2 y4 y8).

Definition fast_cdf_num_value y :=
  let y2:=rn(y*y) in let y4:=rn(y2*y2) in let y8:=rn(y4*y4) in
  let a0:=rn(B cdf_num_0+rn(y*B cdf_num_1)) in
  let a1:=rn(B cdf_num_2+rn(y*B cdf_num_3)) in
  let a2:=rn(B cdf_num_4+rn(y*B cdf_num_5)) in
  let a3:=rn(B cdf_num_6+rn(y*B cdf_num_7)) in
  rn(rn(rn(a0+rn(y2*a1))+rn(y4*rn(a2+rn(y2*a3))))+rn(y8*B cdf_num_8)).
Definition fast_cdf_den_value y :=
  let y2:=rn(y*y) in let y4:=rn(y2*y2) in let y8:=rn(y4*y4) in
  let a0:=rn(B cdf_den_0+rn(y*B cdf_den_1)) in
  let a1:=rn(B cdf_den_2+rn(y*B cdf_den_3)) in
  let a2:=rn(B cdf_den_4+rn(y*B cdf_den_5)) in
  let a3:=rn(B cdf_den_6+rn(y*B cdf_den_7)) in
  let a4:=rn(B cdf_den_8+rn(y*B cdf_den_9)) in
  rn(rn(rn(a0+rn(y2*a1))+rn(y4*rn(a2+rn(y2*a3))))+rn(y8*a4)).
Definition fast_cdf_num_ideal y :=
  let Y2:=y*y in let Y4:=Y2*Y2 in let Y8:=Y4*Y4 in
  ((B cdf_num_0+y*B cdf_num_1)+Y2*(B cdf_num_2+y*B cdf_num_3))+
    Y4*((B cdf_num_4+y*B cdf_num_5)+Y2*(B cdf_num_6+y*B cdf_num_7))+Y8*B cdf_num_8.
Definition fast_cdf_den_ideal y :=
  let Y2:=y*y in let Y4:=Y2*Y2 in let Y8:=Y4*Y4 in
  ((B cdf_den_0+y*B cdf_den_1)+Y2*(B cdf_den_2+y*B cdf_den_3))+
    Y4*((B cdf_den_4+y*B cdf_den_5)+Y2*(B cdf_den_6+y*B cdf_den_7))+
    Y8*(B cdf_den_8+y*B cdf_den_9).

Ltac cdf_coefficient_bounds :=
  pose proof cdf_num_0_finite; pose proof cdf_num_1_finite; pose proof cdf_num_2_finite;
  pose proof cdf_num_3_finite; pose proof cdf_num_4_finite; pose proof cdf_num_5_finite;
  pose proof cdf_num_6_finite; pose proof cdf_num_7_finite; pose proof cdf_num_8_finite;
  pose proof cdf_den_0_finite; pose proof cdf_den_1_finite; pose proof cdf_den_2_finite;
  pose proof cdf_den_3_finite; pose proof cdf_den_4_finite; pose proof cdf_den_5_finite;
  pose proof cdf_den_6_finite; pose proof cdf_den_7_finite; pose proof cdf_den_8_finite;
  pose proof cdf_den_9_finite;
  assert (Rabs (B cdf_num_0)<=8) by (rewrite cdf_num_0_val;interval);
  assert (Rabs (B cdf_num_1)<=8) by (rewrite cdf_num_1_val;interval);
  assert (Rabs (B cdf_num_2)<=8) by (rewrite cdf_num_2_val;interval);
  assert (Rabs (B cdf_num_3)<=8) by (rewrite cdf_num_3_val;interval);
  assert (Rabs (B cdf_num_4)<=8) by (rewrite cdf_num_4_val;interval);
  assert (Rabs (B cdf_num_5)<=8) by (rewrite cdf_num_5_val;interval);
  assert (Rabs (B cdf_num_6)<=8) by (rewrite cdf_num_6_val;interval);
  assert (Rabs (B cdf_num_7)<=8) by (rewrite cdf_num_7_val;interval);
  assert (Rabs (B cdf_num_8)<=8) by (rewrite cdf_num_8_val;interval);
  assert (Rabs (B cdf_den_0)<=8) by (rewrite cdf_den_0_val;interval);
  assert (Rabs (B cdf_den_1)<=8) by (rewrite cdf_den_1_val;interval);
  assert (Rabs (B cdf_den_2)<=8) by (rewrite cdf_den_2_val;interval);
  assert (Rabs (B cdf_den_3)<=8) by (rewrite cdf_den_3_val;interval);
  assert (Rabs (B cdf_den_4)<=8) by (rewrite cdf_den_4_val;interval);
  assert (Rabs (B cdf_den_5)<=8) by (rewrite cdf_den_5_val;interval);
  assert (Rabs (B cdf_den_6)<=8) by (rewrite cdf_den_6_val;interval);
  assert (Rabs (B cdf_den_7)<=8) by (rewrite cdf_den_7_val;interval);
  assert (Rabs (B cdf_den_8)<=8) by (rewrite cdf_den_8_val;interval);
  assert (Rabs (B cdf_den_9)<=8) by (rewrite cdf_den_9_val;interval).

Lemma fast_cdf_ratio_ieee y : finite y -> Rabs (B y)<=8 ->
  1<=fast_cdf_den_value (B y) ->
  finite (fast_cdf_ratio64 y) /\
  B (fast_cdf_ratio64 y)=rn(fast_cdf_num_value (B y)/fast_cdf_den_value (B y)).
Proof.
  intros Fy Y D. cdf_coefficient_bounds. pose proof Y as Ycopy.
  table_op fmul_bnd 1%Z 6%Z y y Fy2 Vy2 Cy2. set (y2:=fmul y y) in *. pose proof Cy2 as Cy2copy.
  table_op fmul_bnd 1%Z 12%Z y2 y2 Fy4 Vy4 Cy4. set (y4:=fmul y2 y2) in *. pose proof Cy4 as Cy4copy.
  table_op fmul_bnd 1%Z 24%Z y4 y4 Fy8 Vy8 Cy8. set (y8:=fmul y4 y4) in *.
  table_op fmul_bnd 1%Z 6%Z y cdf_num_1 Fn0 Vn0 Cn0.
  table_op fadd_bnd 1%Z 7%Z cdf_num_0 (fmul y cdf_num_1) Fna0 Vna0 Cna0.
  table_op fmul_bnd 1%Z 6%Z y cdf_num_3 Fn1 Vn1 Cn1.
  table_op fadd_bnd 1%Z 7%Z cdf_num_2 (fmul y cdf_num_3) Fna1 Vna1 Cna1.
  table_op fmul_bnd 1%Z 6%Z y cdf_num_5 Fn2 Vn2 Cn2.
  table_op fadd_bnd 1%Z 7%Z cdf_num_4 (fmul y cdf_num_5) Fna2 Vna2 Cna2.
  table_op fmul_bnd 1%Z 6%Z y cdf_num_7 Fn3 Vn3 Cn3.
  table_op fadd_bnd 1%Z 7%Z cdf_num_6 (fmul y cdf_num_7) Fna3 Vna3 Cna3.
  set (na0:=fadd cdf_num_0 (fmul y cdf_num_1)) in *.
  set (na1:=fadd cdf_num_2 (fmul y cdf_num_3)) in *.
  set (na2:=fadd cdf_num_4 (fmul y cdf_num_5)) in *.
  set (na3:=fadd cdf_num_6 (fmul y cdf_num_7)) in *.
  table_op fmul_bnd 1%Z 13%Z y2 na1 Fnq0 Vnq0 Cnq0.
  table_op fadd_bnd 1%Z 14%Z na0 (fmul y2 na1) Fnb0 Vnb0 Cnb0.
  table_op fmul_bnd 1%Z 13%Z y2 na3 Fnq1 Vnq1 Cnq1.
  table_op fadd_bnd 1%Z 14%Z na2 (fmul y2 na3) Fnb1 Vnb1 Cnb1.
  set (nb0:=fadd na0 (fmul y2 na1)) in *. set (nb1:=fadd na2 (fmul y2 na3)) in *.
  table_op fmul_bnd 1%Z 26%Z y4 nb1 Fnq2 Vnq2 Cnq2.
  table_op fadd_bnd 1%Z 27%Z nb0 (fmul y4 nb1) Fnc Vnc Cnc.
  set (nc:=fadd nb0 (fmul y4 nb1)) in *.
  table_op fmul_bnd 1%Z 27%Z y8 cdf_num_8 Fnq3 Vnq3 Cnq3.
  table_op fadd_bnd 1%Z 28%Z nc (fmul y8 cdf_num_8) Fnh Vnh Cnh.
  table_op fmul_bnd 1%Z 6%Z y cdf_den_1 Fd0 Vd0 Cd0.
  table_op fadd_bnd 1%Z 7%Z cdf_den_0 (fmul y cdf_den_1) Fda0 Vda0 Cda0.
  table_op fmul_bnd 1%Z 6%Z y cdf_den_3 Fd1 Vd1 Cd1.
  table_op fadd_bnd 1%Z 7%Z cdf_den_2 (fmul y cdf_den_3) Fda1 Vda1 Cda1.
  table_op fmul_bnd 1%Z 6%Z y cdf_den_5 Fd2 Vd2 Cd2.
  table_op fadd_bnd 1%Z 7%Z cdf_den_4 (fmul y cdf_den_5) Fda2 Vda2 Cda2.
  table_op fmul_bnd 1%Z 6%Z y cdf_den_7 Fd3 Vd3 Cd3.
  table_op fadd_bnd 1%Z 7%Z cdf_den_6 (fmul y cdf_den_7) Fda3 Vda3 Cda3.
  table_op fmul_bnd 1%Z 6%Z y cdf_den_9 Fd4 Vd4 Cd4.
  table_op fadd_bnd 1%Z 7%Z cdf_den_8 (fmul y cdf_den_9) Fda4 Vda4 Cda4.
  set (da0:=fadd cdf_den_0 (fmul y cdf_den_1)) in *.
  set (da1:=fadd cdf_den_2 (fmul y cdf_den_3)) in *.
  set (da2:=fadd cdf_den_4 (fmul y cdf_den_5)) in *.
  set (da3:=fadd cdf_den_6 (fmul y cdf_den_7)) in *.
  set (da4:=fadd cdf_den_8 (fmul y cdf_den_9)) in *.
  table_op fmul_bnd 1%Z 13%Z y2 da1 Fdq0 Vdq0 Cdq0.
  table_op fadd_bnd 1%Z 14%Z da0 (fmul y2 da1) Fdb0 Vdb0 Cdb0.
  table_op fmul_bnd 1%Z 13%Z y2 da3 Fdq1 Vdq1 Cdq1.
  table_op fadd_bnd 1%Z 14%Z da2 (fmul y2 da3) Fdb1 Vdb1 Cdb1.
  set (db0:=fadd da0 (fmul y2 da1)) in *. set (db1:=fadd da2 (fmul y2 da3)) in *.
  table_op fmul_bnd 1%Z 26%Z y4 db1 Fdq2 Vdq2 Cdq2.
  table_op fadd_bnd 1%Z 27%Z db0 (fmul y4 db1) Fdc Vdc Cdc.
  set (dc:=fadd db0 (fmul y4 db1)) in *.
  table_op fmul_bnd 1%Z 31%Z y8 da4 Fdq3 Vdq3 Cdq3.
  table_op fadd_bnd 1%Z 32%Z dc (fmul y8 da4) Fdh Vdh Cdh.
  set (nh:=fadd nc (fmul y8 cdf_num_8)) in *. set (dh:=fadd dc (fmul y8 da4)) in *.
  assert (Nh : B nh=fast_cdf_num_value (B y)).
  { unfold fast_cdf_num_value. cbv zeta.
    rewrite Vnh,Vnq3,Vnc,Vnq2,Vnb1,Vnq1,Vnb0,Vnq0,Vna3,Vn3,Vna2,Vn2,Vna1,Vn1,Vna0,Vn0,Vy8,Vy4,Vy2.
    reflexivity. }
  assert (Dh : B dh=fast_cdf_den_value (B y)).
  { unfold fast_cdf_den_value. cbv zeta.
    rewrite Vdh,Vdq3,Vdc,Vdq2,Vdb1,Vdq1,Vdb0,Vdq0,Vda4,Vd4,Vda3,Vd3,Vda2,Vd2,Vda1,Vd1,Vda0,Vd0,Vy8,Vy4,Vy2.
    reflexivity. }
  rewrite <-Dh in D.
  assert (Q : bnd 1 28 (B nh/B dh)).
  { unfold bnd. rewrite Rmult_1_l. unfold Rdiv. rewrite Rabs_mult,Rabs_Rinv,(Rabs_pos_eq (B dh)) by lra.
    apply (Rmult_le_reg_r (B dh));[lra|]. rewrite Rmult_assoc,Rinv_l,Rmult_1_r by lra.
    revert Cnh. bpow_num. cbn [IZR]. intros. nra. }
  destruct (fdiv_bnd 1 28 nh dh Fnh ltac:(lra) ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) Q)
    as [Fr [Vr _]].
  unfold fast_cdf_ratio64,fast_cdf_num64,fast_cdf_den64. cbv zeta.
  fold y2 y4 y8 na0 na1 na2 na3 nb0 nb1 nc nh da0 da1 da2 da3 da4 db0 db1 dc dh.
  split;[exact Fr|]. rewrite Vr,Nh,<-Dh. reflexivity.
Qed.

Lemma fast_cdf_ratio_certificate y : F64 y -> 15/32<=y<=6369051672525773/1125899906842624 ->
  REL (rn(fast_cdf_num_value y/fast_cdf_den_value y)) (fast_cdf_num_ideal y/fast_cdf_den_ideal y)
    (makepairF (Float2 (-17) (-53)) (Float2 17 (-53))) /\
  1<=fast_cdf_den_value y<=bpow radix2 30.
Proof.
  intros F Yh. assert (Ry : rn y=y) by (apply round_generic;[exact _|exact F]).
  unfold fast_cdf_num_value,fast_cdf_den_value,fast_cdf_num_ideal,fast_cdf_den_ideal. cbv zeta.
  rewrite cdf_num_0_g,cdf_num_1_g,cdf_num_2_g,cdf_num_3_g,cdf_num_4_g,cdf_num_5_g,cdf_num_6_g,
    cdf_num_7_g,cdf_num_8_g,cdf_den_0_g,cdf_den_1_g,cdf_den_2_g,cdf_den_3_g,cdf_den_4_g,
    cdf_den_5_g,cdf_den_6_g,cdf_den_7_g,cdf_den_8_g,cdf_den_9_g.
  rewrite <-Ry. split.
  - apply NNPP. intros Hn. apply (normal_fast_cdf_tail.l1 y). gappa_hyps. left. exact Hn.
  - split;erfcx_goal (normal_fast_cdf_tail.l1 y).
Qed.

Lemma fast_cdf_ideal_pos y : 15/32<=y<=6 -> 1<=fast_cdf_num_ideal y /\ 1<=fast_cdf_den_ideal y.
Proof.
  intros Y. unfold fast_cdf_num_ideal,fast_cdf_den_ideal. cbv zeta. cdf_values.
  split;interval with (i_bisect y).
Qed.

Theorem fast_cdf_ratio_arithmetic y : F64 y -> 15/32<=y<=8*B normal_inv_sqrt2_hi ->
  Rabs ((rn(fast_cdf_num_value y/fast_cdf_den_value y)-fast_cdf_num_ideal y/fast_cdf_den_ideal y)/
        (fast_cdf_num_ideal y/fast_cdf_den_ideal y))<=17*bpow radix2 (-53) /\
  1<=fast_cdf_den_value y<=bpow radix2 30.
Proof.
  intros F Y. rewrite (proj2 normal_inv_sqrt2_hi_ok) in Y.
  assert (Yh : 15/32<=y<=6369051672525773/1125899906842624).
  { split;[lra|]. eapply Rle_trans;[exact (proj2 Y)|]. interval with (i_prec 100). }
  destruct (fast_cdf_ratio_certificate y F Yh) as [[e [Be Ee]] D].
  destruct (fast_cdf_ideal_pos y ltac:(split;[lra|eapply Rle_trans;[exact (proj2 Yh)|lra]])) as [Np Dp].
  split;[|exact D].
  rewrite Ee. set (Q:=fast_cdf_num_ideal y/fast_cdf_den_ideal y).
  assert (Qp : 0<Q) by (unfold Q;apply Rdiv_lt_0_compat;lra).
  replace ((Q*(1+e)-Q)/Q) with e by (field;lra).
  cbn [lower upper] in Be. change (float2R (Float2 (-17) (-53))) with (IZR (-17)*bpow radix2 (-53)) in Be.
  change (float2R (Float2 17 (-53))) with (IZR 17*bpow radix2 (-53)) in Be.
  apply Rabs_le. lra.
Qed.

Lemma fast_cdf_ideal_eq y : fast_cdf_num_ideal y=cdf_tail_num y /\ fast_cdf_den_ideal y=cdf_tail_den y.
Proof.
  unfold fast_cdf_num_ideal,fast_cdf_den_ideal,cdf_tail_num,cdf_tail_den,cdf_num_words,cdf_den_words.
  cbn [cdf_horner]. split;ring.
Qed.

(** {1 Relative-error composition} *)

Lemma cdf_rel_chain a b c d1 d2 : Rabs(a-b)<=d1*b -> Rabs(b-c)<=d2*c ->
  0<=c -> 0<=d1 -> 0<=d2 -> Rabs(a-c)<=(d1+d2+d1*d2)*c.
Proof.
  intros Ab Bc C D1 D2. pose proof (Rabs_le_inv _ _ Bc) as B'.
  assert (Bu : b<=(1+d2)*c) by lra.
  replace (a-c) with ((a-b)+(b-c)) by ring. eapply Rle_trans;[apply Rabs_triang|].
  assert (d1*b<=d1*((1+d2)*c)) by (apply Rmult_le_compat_l;lra). nra.
Qed.

Lemma cdf_rel_weaken a c d d' : 0<=c -> d<=d' -> Rabs(a-c)<=d*c -> Rabs(a-c)<=d'*c.
Proof. intros C D H. assert (d*c<=d'*c) by (apply Rmult_le_compat_r;lra). lra. Qed.

Lemma cdf_rel_mul a A b B' da db : Rabs(a-A)<=da*A -> Rabs(b-B')<=db*B' ->
  0<=A -> 0<=B' -> 0<=da -> 0<=db -> Rabs(a*b-A*B')<=(da+db+da*db)*(A*B').
Proof.
  intros Ea Eb HA HB Da Db. pose proof (Rabs_le_inv _ _ Eb) as Eb'.
  replace (a*b-A*B') with ((a-A)*b+A*(b-B')) by ring.
  eapply Rle_trans;[apply Rabs_triang|]. rewrite !Rabs_mult,(Rabs_pos_eq A) by lra.
  assert (Rabs b<=(1+db)*B') by (apply Rabs_le;lra).
  assert (Rabs(a-A)*Rabs b<=(da*A)*((1+db)*B')) by (apply Rmult_le_compat;try apply Rabs_pos;lra).
  assert (A*Rabs(b-B')<=A*(db*B')) by (apply Rmult_le_compat_l;lra). nra.
Qed.

(** {1 Argument rounding and erfcx sensitivity in the tail} *)

Theorem fast_cdf_argument_tight a : finite a -> bpow radix2(-33)<=B a<=8 ->
  Rabs(B(fast_normal_argument64 a)-B a/sqrt 2)<=2*bpow radix2(-53)*(B a/sqrt 2) /\
  B(fast_normal_argument64 a)<=8*B normal_inv_sqrt2_hi.
Proof.
  intros Fa A. destruct normal_inv_sqrt2_hi_ok as [Fc C].
  assert (Apos : 0<B a) by (pose proof (bpow_gt_0 radix2(-33));lra).
  assert (Cerror : Rabs(B normal_inv_sqrt2_hi-/sqrt 2)<=7/10*bpow radix2(-53)/sqrt 2).
  { rewrite C;bpow_num;interval with(i_prec 160). }
  assert (Crange : /2<=B normal_inv_sqrt2_hi<=1) by (rewrite C;interval with(i_prec 80)).
  assert (Bound : bnd 1 3 (B a*B normal_inv_sqrt2_hi)).
  { unfold bnd;rewrite Rmult_1_l,Rabs_pos_eq by nra. change(bpow radix2 3)with 8;nra. }
  destruct (fmul_bnd 1 3 a normal_inv_sqrt2_hi Fa Fc ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Bound)
    as [Fz [Z _]].
  fold (fast_normal_argument64 a) in Z.
  split.
  - assert (Normal : bpow radix2(-1022)<=Rabs(B a*B normal_inv_sqrt2_hi)).
    { rewrite Rabs_pos_eq by nra. assert (bpow radix2 (-1022)<=bpow radix2 (-34)) by (apply bpow_le;lia).
      bpow_num_all. nra. }
    pose proof (rnd_rel _ Normal) as Round.
    change (Rabs(rndF(B a*B normal_inv_sqrt2_hi)-B a*B normal_inv_sqrt2_hi)<=
      bpow radix2(-53)*Rabs(B a*B normal_inv_sqrt2_hi)) in Round.
    rewrite <-Z,(Rabs_pos_eq (B a*B normal_inv_sqrt2_hi)) in Round by nra.
    replace (B(fast_normal_argument64 a)-B a/sqrt 2) with
      ((B(fast_normal_argument64 a)-B a*B normal_inv_sqrt2_hi)+B a*(B normal_inv_sqrt2_hi-/sqrt 2))
      by (unfold Rdiv;ring).
    eapply Rle_trans;[apply Rabs_triang|]. rewrite Rabs_mult,(Rabs_pos_eq (B a)) by lra.
    pose proof (Rabs_le_inv _ _ Cerror) as Cr.
    assert (Sc : B a*Rabs(B normal_inv_sqrt2_hi-/sqrt 2)<=B a*(7/10*bpow radix2(-53)/sqrt 2))
      by (apply Rmult_le_compat_l;lra).
    assert (S2 : 0</sqrt 2) by (apply Rinv_0_lt_compat;interval).
    assert (High : B a*B normal_inv_sqrt2_hi<=B a*(/sqrt 2+7/10*bpow radix2(-53)/sqrt 2)) by (unfold Rdiv in *;nra).
    bpow_num_all. unfold Rdiv in *. nra.
  - rewrite Z. apply round_le_generic;[exact _|exact _| |nra].
    rewrite C. replace (8*(6369051672525773/2^53)) with (IZR 6369051672525773*bpow radix2 (-50))
      by (bpow_num;simpl;field). apply bnd_fmt;lia.
Qed.

Lemma cdf_erfcx_one_lower : 21/50<=gaussian_erfcx 1.
Proof.
  pose proof (cdf_tail_approx 1 ltac:(lra)) as A.
  assert (R1 : 2137/5000<=cdf_tail_ratio 1).
  { unfold cdf_tail_ratio,cdf_tail_num,cdf_tail_den,cdf_num_words,cdf_den_words. cbn [cdf_horner].
    cdf_values. interval with (i_prec 100). }
  assert (E : /2^56+/2^53*/(2*inv_sqrt_pi)<=/2^50) by (unfold inv_sqrt_pi;interval with (i_prec 100)).
  assert (P : 0<gaussian_erfcx 1) by (apply normal_erfcx_positive;lra).
  apply Rabs_le_inv in A.
  assert ((/2^56+/2^53*/(2*inv_sqrt_pi))*gaussian_erfcx 1<=/2^50*gaussian_erfcx 1)
    by (apply Rmult_le_compat_r;lra).
  assert (/2^50 <= /1000) by interval. nra.
Qed.

Lemma cdf_erfcx_derivative_relative Y c : 2/5<=Y -> 999/1000*Y<=c ->
  Rabs(normal_erfcx_derivative c)*Y<=11/4*gaussian_erfcx Y.
Proof.
  intros HY Hc. destruct (normal_erfcx_derivative_bounds c ltac:(lra)) as [Bounds Tail].
  pose proof inv_sqrt_pi_positive as P.
  assert (Pu : inv_sqrt_pi<=5643/10000) by (unfold inv_sqrt_pi;interval).
  pose proof (Rabs_pos (normal_erfcx_derivative c)) as N.
  destruct (Rle_dec 1 Y) as [L|S].
  - pose proof (normal_erfcx_large_lower Y L) as Lo.
    assert (Y2 : Y*Y<=11/8*(c*c)) by nra.
    assert (D : Rabs(normal_erfcx_derivative c)*(Y*Y)<=11/8*inv_sqrt_pi).
    { assert (Rabs(normal_erfcx_derivative c)*(Y*Y)<=Rabs(normal_erfcx_derivative c)*(11/8*(c*c)))
        by (apply Rmult_le_compat_l;lra). nra. }
    assert (Lo' : inv_sqrt_pi<=2*Y*gaussian_erfcx Y).
    { apply (Rmult_le_compat_r (2*Y)) in Lo;[|lra].
      replace (inv_sqrt_pi/(2*Y)*(2*Y)) with inv_sqrt_pi in Lo by (field;lra). lra. }
    apply (Rmult_le_reg_r Y);[lra|]. nra.
  - assert (Dec : gaussian_erfcx 1<=gaussian_erfcx Y) by (apply normal_erfcx_decreasing;lra).
    pose proof cdf_erfcx_one_lower.
    rewrite Rabs_left1 by lra. nra.
Qed.

Theorem cdf_erfcx_relative_argument y Y : 2/5<=Y -> Rabs(y-Y)<=Y/1000 ->
  Rabs(gaussian_erfcx y-gaussian_erfcx Y)<=11/4*(Rabs(y-Y)/Y)*gaussian_erfcx Y.
Proof.
  intros HY D. pose proof (Rabs_le_inv _ _ D) as D'.
  apply (Rmult_le_reg_r Y);[lra|].
  replace (11/4*(Rabs(y-Y)/Y)*gaussian_erfcx Y*Y) with (11/4*gaussian_erfcx Y*Rabs(y-Y)) by (field;lra).
  destruct (Rtotal_order y Y) as [Lt|[Eq|Gt]].
  - destruct (MVT_cor2 gaussian_erfcx normal_erfcx_derivative y Y Lt) as [c [Diff C]].
    + intros;apply is_derive_Reals,gaussian_erfcx_derivative.
    + rewrite Rabs_minus_sym,Diff,Rabs_mult,(Rabs_minus_sym y),(Rabs_pos_eq (Y-y)) by lra.
      pose proof (cdf_erfcx_derivative_relative Y c HY ltac:(lra)) as K.
      assert (0<=Y-y) by lra. nra.
  - subst. rewrite !Rminus_diag_eq,!Rabs_R0 by reflexivity. lra.
  - destruct (MVT_cor2 gaussian_erfcx normal_erfcx_derivative Y y Gt) as [c [Diff C]].
    + intros;apply is_derive_Reals,gaussian_erfcx_derivative.
    + rewrite Diff,Rabs_mult,(Rabs_pos_eq (y-Y)) by lra.
      pose proof (cdf_erfcx_derivative_relative Y c HY ltac:(lra)) as K.
      assert (0<=y-Y) by lra. nra.
Qed.

Lemma cdf_half_rel w x k : Rabs(w-x)<=k*x -> Rabs(/2*w-x/2)<=k*(x/2).
Proof.
  intros H. replace (/2*w-x/2) with ((w-x)*/2) by field.
  rewrite Rabs_mult,(Rabs_pos_eq (/2)) by lra. unfold Rdiv. nra.
Qed.

Lemma cdf_damped w x c : 0<w -> /2<=x -> Rabs c<=bpow radix2 (-95) ->
  Rabs(w*c)<=bpow radix2 (-94)*(w*x).
Proof.
  intros W X C. rewrite Rabs_mult,(Rabs_pos_eq w) by lra.
  assert (H95 : bpow radix2 (-95)=/2*bpow radix2 (-94)) by (bpow_num;lra).
  assert (H1 : w*Rabs c<=w*bpow radix2 (-95)) by (apply Rmult_le_compat_l;lra).
  rewrite H95 in H1.
  assert (w*(/2*bpow radix2 (-94))<=w*(x*bpow radix2 (-94))).
  { apply Rmult_le_compat_l;[lra|]. apply Rmult_le_compat_r;[apply bpow_ge_0|lra]. }
  lra.
Qed.

Lemma cdf_exp_first_order e : Rabs e<=bpow radix2 (-48) -> Rabs((1+e)-exp e)<=bpow radix2 (-95).
Proof. intros E. apply Rabs_le_inv in E. bpow_num_all. apply Rabs_le. split;interval with (i_taylor e, i_prec 200). Qed.

Lemma cdf_erfcx_floor Y : 0<Y<=6 -> 1/25<=gaussian_erfcx Y.
Proof.
  intros Y'. pose proof inv_sqrt_pi_positive as P.
  assert (Pl : 5641/10000<=inv_sqrt_pi) by (unfold inv_sqrt_pi;interval).
  destruct (Rle_dec 1 Y) as [L|S].
  - pose proof (normal_erfcx_large_lower Y L) as Lo.
    assert (1/25<=inv_sqrt_pi/(2*Y)).
    { apply (Rmult_le_reg_r (2*Y));[lra|]. replace (inv_sqrt_pi/(2*Y)*(2*Y)) with inv_sqrt_pi by (field;lra). lra. }
    lra.
  - pose proof (normal_erfcx_decreasing Y 1 ltac:(lra)). pose proof cdf_erfcx_one_lower. lra.
Qed.

(** {1 The lower tail [Phi(-a)] for [RN(a/sqrt 2) > 15/32]} *)

Definition fast_cdf_lower64 a :=
  let '(p,e):=two_prod64 (fmul erfcx_negative_half a) a in
  let r:=fast_cdf_ratio64 (fast_normal_argument64 a) in
  fmul (fmul cdf_half (fast_exp_entry64 p)) (fadd r (fmul r e)).

(** Algebra for [fast_cdf_lower_ok], kept out of its large context: ring and
    field there cost minutes of kernel time. *)
Lemma cdf_sqrt2_cancel x : x/sqrt 2*sqrt 2=x.
Proof. field. interval. Qed.

Lemma cdf_rel_of_div x R d : 0<R -> Rabs((x-R)/R)<=d -> Rabs(x-R)<=d*R.
Proof.
  intros P H. replace (x-R) with (((x-R)/R)*R) by (field;lra).
  rewrite Rabs_mult,(Rabs_pos_eq R) by lra. apply Rmult_le_compat_r;lra.
Qed.

Lemma cdf_neg_half_sq x : -/2*x*x= -x*x/2.
Proof. field. Qed.

Lemma cdf_tail_correction br bre be EY d : Rabs(br-EY)<=d*EY -> Rabs(bre-br*be)<=bpow radix2(-101) ->
  0<=d -> 0<1+be -> 1/26<=EY*(1+be) ->
  Rabs(br+bre-EY*(1+be))<=(d+bpow radix2(-95))*(EY*(1+be)).
Proof.
  intros A Bv D E X.
  replace (br+bre-EY*(1+be)) with ((br-EY)*(1+be)+(bre-br*be)) by ring.
  eapply Rle_trans;[apply Rabs_triang|]. rewrite Rabs_mult,(Rabs_pos_eq (1+be)) by lra.
  assert (Rabs(br-EY)*(1+be)<=d*(EY*(1+be))).
  { replace (d*(EY*(1+be))) with ((d*EY)*(1+be)) by ring. apply Rmult_le_compat_r;lra. }
  assert (bpow radix2(-101)<=bpow radix2(-95)*(EY*(1+be))) by (bpow_num_all;lra).
  lra.
Qed.

Lemma cdf_exp_correction P EY be : 0<P*EY/2 -> /2<=exp be ->
  Rabs((1+be)-exp be)<=bpow radix2 (-95) ->
  Rabs(P/2*(EY*(1+be))-P*exp be*EY/2)<=bpow radix2(-94)*(P*exp be*EY/2).
Proof.
  intros W X C.
  replace (P/2*(EY*(1+be))-P*exp be*EY/2) with ((P*EY/2)*((1+be)-exp be)) by field.
  replace (P*exp be*EY/2) with ((P*EY/2)*exp be) by field.
  apply cdf_damped;assumption.
Qed.

Theorem fast_cdf_lower_ok a : finite a -> bpow radix2(-33)<=B a<=8 ->
  15/32<B(fast_normal_argument64 a) ->
  finite(fast_cdf_lower64 a) /\
  bpow radix2(-58)<=B(fast_cdf_lower64 a)<=41/100 /\ normal_tail(B a)<=41/100 /\
  Rabs(B(fast_cdf_lower64 a)-normal_tail(B a))<=bpow radix2(-48)*normal_tail(B a).
Proof.
  intros Fa A Body. unfold fast_cdf_lower64. cbv zeta.
  assert (Apos : 0<B a) by (pose proof (bpow_gt_0 radix2(-33));lra).
  pose proof (bpow_gt_0 radix2 (-53)) as U.
  destruct (fast_normal_argument_ok a Fa A) as [Fz [Zr _]].
  destruct (fast_cdf_argument_tight a Fa A) as [Zerr Zhi].
  set (z:=fast_normal_argument64 a) in *. clearbody z.
  set (Y:=B a/sqrt 2) in *.
  assert (Ypos : 0<Y) by (unfold Y;apply Rdiv_lt_0_compat;[lra|interval]).
  assert (U53 : bpow radix2 (-53)<=/2^50) by (bpow_num;lra).
  pose proof (Rabs_le_inv _ _ Zerr) as Zr2.
  assert (Ylo : 2/5<=Y) by nra.
  assert (Yhi : Y<=6) by (unfold Y;apply (Rmult_le_reg_r (sqrt 2));[interval|];
    rewrite cdf_sqrt2_cancel;interval).
  assert (Zclose : Rabs(B z-Y)<=Y/1000) by (eapply Rle_trans;[exact Zerr|nra]).
  destruct normal_inv_sqrt2_hi_ok as [_ Cv].
  assert (Ztop : B z<=91/16) by (rewrite Cv in Zhi;eapply Rle_trans;[exact Zhi|interval]).
  (* The tail rational. *)
  destruct (fast_cdf_ratio_arithmetic (B z) (B_fmt z) ltac:(split;lra)) as [Rrel Dv].
  destruct (fast_cdf_ratio_ieee z Fz ltac:(rewrite Rabs_pos_eq;lra) (proj1 Dv)) as [Fr Vr].
  set (r:=fast_cdf_ratio64 z) in *. clearbody r.
  destruct (fast_cdf_ideal_eq (B z)) as [In Id]. rewrite In,Id,<-Vr in Rrel.
  fold (cdf_tail_ratio (B z)) in Rrel.
  pose proof (cdf_tail_approx (B z) ltac:(split;lra)) as Ap.
  pose proof (cdf_erfcx_relative_argument (B z) Y Ylo Zclose) as Sens.
  set (R:=cdf_tail_ratio (B z)) in *. set (Ez:=gaussian_erfcx (B z)) in *.
  set (EY:=gaussian_erfcx Y) in *.
  assert (EYr : 1/25<=EY<=1).
  { split;[apply cdf_erfcx_floor;lra|apply normal_erfcx_unit_upper;lra]. }
  assert (Ezp : 0<Ez) by (apply normal_erfcx_positive;lra).
  assert (E1 : /2^56+/2^53*/(2*inv_sqrt_pi)<=10113/10000*bpow radix2(-53)).
  { bpow_num. unfold inv_sqrt_pi. interval with (i_prec 100). }
  assert (Ap' : Rabs(R-Ez)<=10113/10000*bpow radix2(-53)*Ez).
  { eapply cdf_rel_weaken;[lra|exact E1|exact Ap]. }
  assert (Rp : 0<R) by (pose proof (Rabs_le_inv _ _ Ap');nra).
  assert (Er : Rabs(B r-R)<=17*bpow radix2(-53)*R).
  { apply cdf_rel_of_div;assumption. }
  assert (Q : Rabs(B z-Y)/Y<=2*bpow radix2(-53)).
  { unfold Rdiv. apply (Rmult_le_reg_r Y);[lra|]. rewrite Rmult_assoc,Rinv_l,Rmult_1_r by lra. lra. }
  assert (Sens' : Rabs(Ez-EY)<=11/2*bpow radix2(-53)*EY).
  { eapply Rle_trans;[exact Sens|]. assert (0<=EY) by lra.
    assert (11/4*(Rabs(B z-Y)/Y)<=11/2*bpow radix2(-53)) by lra.
    apply Rmult_le_compat_r;lra. }
  pose proof (cdf_rel_chain (B r) R Ez _ _ Er Ap' ltac:(lra) ltac:(lra) ltac:(lra)) as CA.
  apply (cdf_rel_weaken _ _ _ (1802/100*bpow radix2(-53))) in CA;[|lra|bpow_num;interval].
  pose proof (cdf_rel_chain (B r) Ez EY _ _ CA Sens' ltac:(lra) ltac:(lra) ltac:(lra)) as CB.
  apply (cdf_rel_weaken _ _ _ (2353/100*bpow radix2(-53))) in CB;[|lra|bpow_num;interval].
  pose proof (Rabs_le_inv _ _ CB) as CBr.
  assert (Rr : 1/50<=B r<=2) by (split;bpow_num_all;nra).
  clear In Id Rrel Ap Ap' Sens Sens' Er E1 Q CA Vr Dv Zclose Zhi Ztop Cv Zerr.
  (* The exponent, exactly: p + e = -a^2/2. *)
  destruct erfcx_negative_half_ok as [Fnh Half].
  assert (Mag : (-32<=mag radix2(B a))%Z).
  { apply mag_ge_bpow;change(bpow radix2(-33)<=Rabs(B a));rewrite Rabs_pos_eq by lra;exact(proj1 A). }
  assert (Fmt : F64(B erfcx_negative_half*B a)).
  { rewrite Half;replace(-/2*B a)with(-(B a*bpow radix2(-1)))by(bpow_num;ring).
    apply generic_format_opp,mult_bpow_exact_FLT;[apply B_fmt|unfold emin,prec;lia]. }
  destruct (fmul_exact erfcx_negative_half a Fnh Fa Fmt) as [Fm Hm].
  { rewrite Half,Rabs_mult,(Rabs_pos_eq(B a))by lra.
    eapply Rle_lt_trans with 4;[rewrite Rabs_Ropp;rewrite Rabs_pos_eq by lra;nra|].
    change 4 with(bpow radix2 2);apply bpow_lt;lia. }
  rewrite Half in Hm. set (m:=fmul erfcx_negative_half a) in *. clearbody m.
  assert (Dom : in_two_prod_domain (B m) (B a)).
  { right. rewrite Hm. rewrite Rabs_mult,Rabs_mult,Rabs_Ropp,!(Rabs_pos_eq (B a)),(Rabs_pos_eq (/2)) by lra.
    assert (bpow radix2(-969)<=bpow radix2(-34)*bpow radix2(-33)) by (rewrite <-bpow_plus;apply bpow_le;lia).
    assert (bpow radix2(-34)*bpow radix2(-33)<=/2*B a*B a).
    { assert (bpow radix2 (-34)=/2*bpow radix2 (-33)) by (bpow_num;lra).
      pose proof (bpow_gt_0 radix2 (-33)). nra. }
    lra. }
  pose proof (two_prod_ieee 2 3 m a Fm Fa
    ltac:(rewrite Hm,Rabs_mult,Rabs_Ropp,Rabs_pos_eq,Rabs_pos_eq by lra;change(bpow radix2 2)with 4;lra)
    ltac:(rewrite Rabs_pos_eq by lra;change(bpow radix2 3)with 8;lra)
    ltac:(lia) ltac:(lia) ltac:(lia) Dom) as TP.
  destruct (fast_normal_exponent_ok a Fa A) as [_ [Trange [Tvalue Terror]]].
  revert TP. destruct (two_prod64 m a) as [p e]. intros [Fp [Fe [Vp Sum]]].
  assert (Pv : B p=B(fast_normal_exponent64 a)).
  { rewrite Vp,Tvalue,Hm. f_equal. apply cdf_neg_half_sq. }
  rewrite <-Pv in Trange,Terror.
  rewrite Hm in Sum.
  assert (Ee : Rabs(B e)<=bpow radix2(-48)).
  { replace (B e) with (-(B p+B a*B a/2)) by lra. rewrite Rabs_Ropp.
    eapply Rle_trans;[exact Terror|]. bpow_num_all. nra. }
  pose proof (Rabs_le_inv _ _ Ee) as Ee'.
  destruct (fast_exp_entry_ok p Fp ltac:(apply Rabs_lt;lra)) as [FE Eerr].
  pose proof (fast_exp_nonpositive_range p Fp Trange) as Erange.
  set (E:=fast_exp_entry64 p) in *. clearbody E.
  (* h = E/2 exactly. *)
  destruct cdf_half_ok as [Fhalf Hhalf].
  assert (MagE : (-46<=mag radix2(B E))%Z).
  { apply mag_ge_bpow;change(bpow radix2(-47)<=Rabs(B E));rewrite Rabs_pos_eq by(pose proof(bpow_gt_0 radix2(-47));lra);exact(proj1 Erange). }
  assert (FmtH : F64(B cdf_half*B E)).
  { rewrite Hhalf,Rmult_comm. change (/2) with (bpow radix2 (-1)). apply mult_bpow_exact_FLT;[apply B_fmt|unfold emin,prec;lia]. }
  destruct (fmul_exact cdf_half E Fhalf FE FmtH) as [Fh Vh].
  { rewrite Hhalf,Rabs_mult,(Rabs_pos_eq(B E)) by(pose proof(bpow_gt_0 radix2(-47));lra).
    rewrite Rabs_pos_eq by lra.
    eapply Rle_lt_trans with 1;[lra|change 1 with(bpow radix2 0);apply bpow_lt;lia]. }
  rewrite Hhalf in Vh. set (h:=fmul cdf_half E) in *. clearbody h.
  (* r e, r + r e, h (r + r e). *)
  assert (BRE : bnd 1 (-47) (B r*B e)).
  { unfold bnd. rewrite Rmult_1_l,Rabs_mult,(Rabs_pos_eq (B r)) by lra.
    assert (B r*Rabs(B e)<=2*bpow radix2(-48)) by (apply Rmult_le_compat;try lra;apply Rabs_pos).
    bpow_num_all. lra. }
  destruct (fmul_bnd 1 (-47) r e Fr Fe ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) BRE) as [Fre [Vre _]].
  assert (Rre : Rabs(B(fmul r e)-B r*B e)<=bpow radix2(-101)).
  { rewrite Vre. apply (rnd_err_below _ (-47));[lia|]. unfold bnd in BRE. rewrite Rmult_1_l in BRE. exact BRE. }
  set (re:=fmul r e) in *. clearbody re.
  pose proof (Rabs_le_inv _ _ Rre) as Rre'.
  assert (BRE' : B r*B e<=bpow radix2 (-47) /\ -bpow radix2 (-47)<=B r*B e).
  { unfold bnd in BRE. rewrite Rmult_1_l in BRE. apply Rabs_le_inv in BRE. lra. }
  assert (Wr : 1/100<=B r+B re<=3).
  { assert (bpow radix2 (-101)<=bpow radix2 (-47)) by (apply bpow_le;lia). bpow_num_all. split;lra. }
  assert (BT : bnd 1 2 (B r+B re)) by (unfold bnd;rewrite Rmult_1_l,Rabs_pos_eq by lra;change (bpow radix2 2) with 4;lra).
  destruct (fadd_bnd 1 2 r re Fr Fre ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) BT) as [Ft [Vt _]].
  assert (Rt : Rabs(B(fadd r re)-(B r+B re))<=bpow radix2(-53)*(B r+B re)).
  { rewrite Vt. assert (N : bpow radix2 (-1022)<=Rabs(B r+B re)).
    { rewrite Rabs_pos_eq by lra. assert (bpow radix2 (-1022)<=1/100) by (bpow_num;lra). lra. }
    pose proof (rnd_rel _ N) as K. rewrite (Rabs_pos_eq (B r+B re)) in K by lra. exact K. }
  set (t:=fadd r re) in *. clearbody t.
  pose proof (Rabs_le_inv _ _ Rt) as Rt'.
  assert (Trng : 1/200<=B t<=4) by (bpow_num_all;split;nra).
  assert (Hrng : bpow radix2(-48)<=B h<=1).
  { rewrite Vh. split;[|lra]. assert (bpow radix2 (-48)=/2*bpow radix2 (-47)) by (bpow_num;lra). lra. }
  assert (BL : bnd 1 2 (B h*B t)).
  { unfold bnd;rewrite Rmult_1_l,Rabs_pos_eq by nra;change (bpow radix2 2) with 4;nra. }
  destruct (fmul_bnd 1 2 h t Fh Ft ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) BL) as [Fl [Vl _]].
  assert (Rl : Rabs(B(fmul h t)-B h*B t)<=bpow radix2(-53)*(B h*B t)).
  { rewrite Vl. assert (N : bpow radix2 (-1022)<=Rabs(B h*B t)).
    { rewrite Rabs_pos_eq by nra. assert (bpow radix2 (-1022)<=bpow radix2 (-48)*(1/200)) by (bpow_num;lra).
      assert (bpow radix2 (-48)*(1/200)<=B h*B t) by (apply Rmult_le_compat;try lra;apply bpow_ge_0). lra. }
    pose proof (rnd_rel _ N) as K. rewrite (Rabs_pos_eq (B h*B t)) in K by nra. exact K. }
  (* The real chain. Every binary64 word above is opaque (clearbody): ring,
     field and the kernel must never unfold a computed word. *)
  clear Vre BRE BRE' Vt BT BL Vl MagE FmtH Fmt Mag Dom Hm Half Hhalf Vp Pv Tvalue
    Fnh Fm Fhalf Fh Fre Ft Fr Fz Fe FE Fp Fa Zr Terror Wr Trng Hrng.
  set (X2:=EY*(1+B e)).
  assert (X2r : 1/26<=X2<=2) by (unfold X2;bpow_num_all;split;nra).
  assert (T2 : Rabs(B r+B re-X2)<=(2353/100*bpow radix2(-53)+bpow radix2(-95))*X2).
  { unfold X2. apply cdf_tail_correction;[exact CB|exact Rre|lra|bpow_num_all;lra|exact (proj1 X2r)]. }
  pose proof (cdf_rel_chain (B t) (B r+B re) X2 _ _ Rt T2 ltac:(lra) ltac:(lra) ltac:(bpow_num_all;lra)) as T3.
  apply (cdf_rel_weaken _ _ _ (2454/100*bpow radix2(-53))) in T3;[|lra|bpow_num;interval].
  set (X1:=exp(B p)/2).
  assert (X1p : 0<X1) by (unfold X1;pose proof (exp_pos (B p));lra).
  assert (H1 : Rabs(B h-X1)<=bpow radix2(-51)*X1).
  { rewrite Vh. unfold X1. exact (cdf_half_rel _ _ _ Eerr). }
  pose proof (cdf_rel_mul (B h) X1 (B t) X2 _ _ H1 T3 ltac:(lra) ltac:(lra) ltac:(apply bpow_ge_0) ltac:(bpow_num_all;lra)) as T4.
  apply (cdf_rel_weaken _ _ _ (2855/100*bpow radix2(-53))) in T4;[|nra|bpow_num;interval].
  pose proof (cdf_rel_chain (B(fmul h t)) (B h*B t) (X1*X2) _ _ Rl T4 ltac:(nra) ltac:(lra) ltac:(lra)) as T5.
  apply (cdf_rel_weaken _ _ _ (2956/100*bpow radix2(-53))) in T5;[|nra|bpow_num;interval].
  set (T:=normal_tail(B a)).
  assert (Tid : T=exp(B p)*exp(B e)*EY/2).
  { unfold T,normal_tail. fold Y EY. rewrite <-exp_plus. f_equal. f_equal. f_equal. lra. }
  assert (Ee2 : /2<=exp(B e)<=2) by (bpow_num_all;split;interval).
  assert (Wp : 0<exp(B p)*EY/2) by (pose proof (exp_pos (B p));apply Rdiv_lt_0_compat;[apply Rmult_lt_0_compat|];lra).
  assert (T6 : Rabs(X1*X2-T)<=bpow radix2(-94)*T).
  { rewrite Tid. unfold X1,X2. apply cdf_exp_correction;[exact Wp|lra|exact (cdf_exp_first_order (B e) Ee)]. }
  assert (Tp : 0<T).
  { rewrite Tid. apply Rdiv_lt_0_compat;[|lra]. apply Rmult_lt_0_compat;[apply Rmult_lt_0_compat;apply exp_pos|lra]. }
  pose proof (cdf_rel_chain (B(fmul h t)) (X1*X2) T _ _ T5 T6 ltac:(lra) ltac:(lra) ltac:(apply bpow_ge_0)) as T7.
  apply (cdf_rel_weaken _ _ _ (bpow radix2(-48))) in T7;[|lra|bpow_num;interval].
  (* Ranges. *)
  assert (Tup : T<=4017/10000).
  { rewrite Tid,<-exp_plus.
    assert (Q2 : B p+B e= -(Y*Y)) by (unfold Y;rewrite normal_sqrt_two_square;lra).
    assert (Ylo' : 4687/10000<=Y) by (bpow_num_all;nra).
    rewrite Q2. assert (exp(-(Y*Y))<=8034/10000) by interval with (i_bisect Y).
    pose proof (exp_pos (-(Y*Y))). nra. }
  assert (Tlo : bpow radix2(-57)<=T).
  { rewrite Tid,<-exp_plus.
    assert (exp(-32)<=exp(B p+B e)) by (apply exp_le;nra).
    assert (bpow radix2(-57)*50<=exp(-32)) by (bpow_num;interval).
    pose proof (exp_pos (B p+B e)). nra. }
  pose proof (Rabs_le_inv _ _ T7) as T7'.
  split;[exact Fl|]. split;[|split;[lra|exact T7]].
  bpow_num_all. split;nra.
Qed.

(** {1 The body's contract} *)

Lemma cdf_gaussian_lipschitz y X : Rabs(RInt gaussian 0 y-RInt gaussian 0 X)<=Rabs(y-X).
Proof.
  assert (Split : RInt gaussian 0 y-RInt gaussian 0 X=RInt gaussian X y).
  { pose proof (@RInt_Chasles R_CompleteNormedModule gaussian 0 X y
      (gaussian_integrable 0 X) (gaussian_integrable X y)) as C.
    change (RInt gaussian 0 X+RInt gaussian X y=RInt gaussian 0 y) in C. lra. }
  rewrite Split.
  assert (Pt : forall t, Rabs (gaussian t)<=1).
  { intros t. unfold gaussian. rewrite Rabs_pos_eq by (apply Rlt_le,exp_pos).
    rewrite <-exp_0. apply exp_le. nra. }
  destruct (Rle_dec X y) as [O|O].
  - pose proof (abs_RInt_le_const gaussian X y 1 O (gaussian_integrable X y) (fun t _ => Pt t)) as K.
    rewrite (Rabs_pos_eq (y-X)) by lra. lra.
  - rewrite <-(@opp_RInt_swap R_CompleteNormedModule) by apply gaussian_integrable.
    change (Rabs (-RInt gaussian y X)<=Rabs (y-X)). rewrite Rabs_Ropp.
    pose proof (abs_RInt_le_const gaussian y X 1 ltac:(lra) (gaussian_integrable y X) (fun t _ => Pt t)) as K.
    rewrite Rabs_minus_sym,(Rabs_pos_eq (X-y)) by lra. lra.
Qed.

Theorem fast_cdf_body_ok x : finite x -> bpow radix2(-33)<=Rabs(B x)<=8 ->
  B(fast_normal_argument64 (b64_abs x))<=15/32 ->
  finite(fast_cdf_body64 x) /\ 29/128<=B(fast_cdf_body64 x)<=25/32 /\
  Rabs(B(fast_cdf_body64 x)-normal_cdf(B x))<=3*bpow radix2(-53).
Proof.
  intros Fx X Lim.
  assert (Fa : finite (b64_abs x)) by (unfold b64_abs;destruct x;exact Fx).
  destruct (fast_normal_argument_ok (b64_abs x) Fa ltac:(rewrite B_abs;exact X)) as [Fz [Zr Zerr]].
  rewrite B_abs in Zerr.
  destruct normal_inv_sqrt2_hi_ok as [Fc Cv].
  assert (Cr : /2<=B normal_inv_sqrt2_hi<=1) by (rewrite Cv;interval).
  assert (Bound : bnd 1 3 (B x*B normal_inv_sqrt2_hi)).
  { unfold bnd. rewrite Rmult_1_l,Rabs_mult,(Rabs_pos_eq (B normal_inv_sqrt2_hi)) by lra.
    change (bpow radix2 3) with 8. pose proof (Rabs_pos (B x)). nra. }
  destruct (fmul_bnd 1 3 x normal_inv_sqrt2_hi Fx Fc ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) Bound)
    as [Fy [Vy _]].
  assert (Bound' : bnd 1 3 (B (b64_abs x)*B normal_inv_sqrt2_hi)) by (rewrite B_abs;unfold bnd in *;rewrite Rabs_mult,Rabs_Rabsolu,<-Rabs_mult;exact Bound).
  destruct (fmul_bnd 1 3 (b64_abs x) normal_inv_sqrt2_hi Fa Fc ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) Bound')
    as [_ [Vz _]].
  set (y:=fmul x normal_inv_sqrt2_hi) in *.
  assert (Sym : Rabs (B y)=B (fast_normal_argument64 (b64_abs x))).
  { unfold fast_normal_argument64. rewrite Vy,Vz,B_abs. rewrite <-round_NE_abs by exact _.
    rewrite Rabs_mult,(Rabs_pos_eq (B normal_inv_sqrt2_hi)) by lra. reflexivity. }
  assert (Yerr : Rabs(B y-B x/sqrt 2)<=3*bpow radix2(-53)*(Rabs(B x)/sqrt 2)).
  { rewrite <-Sym in Zerr. destruct (Rle_dec 0 (B x)) as [P|N].
    - rewrite (Rabs_pos_eq (B x)) in * by lra.
      assert (0<=B y).
      { rewrite Vy. apply round_ge_generic;[exact _|exact _|apply generic_format_0|nra]. }
      rewrite (Rabs_pos_eq (B y)) in Zerr by lra. exact Zerr.
    - rewrite (Rabs_left (B x)) in * by lra.
      assert (B y<=0).
      { rewrite Vy. apply round_le_generic;[exact _|exact _|apply generic_format_0|nra]. }
      rewrite (Rabs_left1 (B y)) in Zerr by lra.
      replace (B y-B x/sqrt 2) with (-(-B y- -B x/sqrt 2)) by (unfold Rdiv;ring).
      rewrite Rabs_Ropp. exact Zerr. }
  assert (Y : Rabs(B y)<=15/32) by lra.
  destruct (fast_cdf_body_ieee x Fx ltac:(change (Rabs (B y)<=/2);lra) Fy) as [Fv Vv]. fold y in Vv.
  destruct (fast_cdf_body_arithmetic (B y) (B_fmt y) Y) as [Ar Range].
  rewrite fast_cdf_body_ideal_eq in Ar.
  pose proof (cdf_body_approx (B y) Y) as Ap.
  pose proof (cdf_gaussian_lipschitz (B y) (B x/sqrt 2)) as Lip.
  assert (I : 0<inv_sqrt_pi<=5643/10000) by (unfold inv_sqrt_pi;split;interval).
  assert (Xs : Rabs(B x)/sqrt 2<=1/2).
  { pose proof (Rabs_le_inv _ _ Yerr). assert (Rabs(B x)/sqrt 2<=15/32+3*bpow radix2(-53)*(Rabs(B x)/sqrt 2)).
    { pose proof (Rabs_le_inv _ _ Y). destruct (Rle_dec 0 (B x)).
      - rewrite Rabs_pos_eq in * by lra. lra.
      - rewrite Rabs_left in * by lra. unfold Rdiv in *. lra. }
    bpow_num_all. lra. }
  split;[exact Fv|]. rewrite Vv. split;[exact Range|].
  unfold normal_cdf. rewrite cdf_center_integral.
  replace (fast_cdf_body_value (B y)-(/2+inv_sqrt_pi*RInt gaussian 0 (B x/sqrt 2))) with
    ((fast_cdf_body_value (B y)-(/2+/2*(B y*cdf_body_poly(B y*B y))))+
     (/2*(B y*cdf_body_poly(B y*B y))-inv_sqrt_pi*RInt gaussian 0 (B y))+
     inv_sqrt_pi*(RInt gaussian 0 (B y)-RInt gaussian 0 (B x/sqrt 2))) by ring.
  eapply Rle_trans;[apply Rabs_triang|]. eapply Rle_trans;[apply Rplus_le_compat_r,Rabs_triang|].
  rewrite Rabs_mult,(Rabs_pos_eq inv_sqrt_pi) by lra.
  assert (inv_sqrt_pi*Rabs(RInt gaussian 0 (B y)-RInt gaussian 0 (B x/sqrt 2))<=
    5643/10000*(3*bpow radix2(-53)*(1/2))).
  { apply Rmult_le_compat;try lra;[apply Rabs_pos|]. eapply Rle_trans;[exact Lip|]. eapply Rle_trans;[exact Yerr|].
    apply Rmult_le_compat_l;[bpow_num_all;lra|exact Xs]. }
  assert (/2^55*Rabs(B y)<=/2^55*(15/32)) by (apply Rmult_le_compat_l;[interval|lra]).
  bpow_num_all. lra.
Qed.

(** {1 The outer region and the entry} *)

Definition fast_cdf_outer64 x :=
  let lower:=fast_cdf_lower64 (b64_abs x) in
  if normal_lt x normal_zero then lower else fsub (erfcx_pow2 0) lower.
Definition fast_cdf64 x :=
  if normal_le (fast_normal_argument64 (b64_abs x)) cdf_limit then fast_cdf_body64 x
  else fast_cdf_outer64 x.
Definition fast_cdf_screen64 x :=
  normal_le(erfcx_pow2(-33))(b64_abs x) && normal_le(b64_abs x)(erfcx_pow2 3).
Definition fast_cdf_entry64 x :=
  if fast_cdf_screen64 x then fast_cdf64 x else normal_entry64 NormalCdf x.

Lemma cdf_complement_ok lower T : finite lower -> bpow radix2(-58)<=B lower<=41/100 ->
  T<=41/100 -> Rabs(B lower-T)<=bpow radix2(-48)*T ->
  finite (fsub (erfcx_pow2 0) lower) /\ bpow radix2(-58)<=B(fsub (erfcx_pow2 0) lower)<=1 /\
  Rabs(B(fsub (erfcx_pow2 0) lower)-(1-T))<=bpow radix2(-49).
Proof.
  intros Fl L Tu Error.
  destruct (erfcx_pow2_ok 0 ltac:(lia)) as [Fone One]. change (bpow radix2 0) with 1 in One.
  assert (Bound : bnd 1 0 (B (erfcx_pow2 0)-B lower)).
  { rewrite One. unfold bnd. rewrite Rmult_1_l. change (bpow radix2 0) with 1.
    rewrite Rabs_pos_eq by lra. pose proof (bpow_gt_0 radix2 (-58)). lra. }
  destruct (fsub_bnd 1 0 (erfcx_pow2 0) lower Fone Fl ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Bound)
    as [Fo [Out _]]. rewrite One in Out.
  assert (Round : Rabs(B(fsub (erfcx_pow2 0) lower)-(1-B lower))<=bpow radix2(-54)).
  { rewrite Out. apply (rnd_err_below _ 0);[lia|]. rewrite Rabs_pos_eq by lra.
    change (bpow radix2 0) with 1. pose proof (bpow_gt_0 radix2 (-58)). lra. }
  split;[exact Fo|]. split.
  - rewrite Out. split.
    + apply round_ge_generic;[exact _|exact _| |bpow_num_all;lra].
      apply generic_format_bpow;unfold FLT_exp,emin,prec;lia.
    + change 1 with (bpow radix2 0). apply round_le_generic;[exact _|exact _| |pose proof (bpow_gt_0 radix2 (-58));lra].
      apply generic_format_bpow;unfold FLT_exp,emin,prec;lia.
  - replace (B(fsub (erfcx_pow2 0) lower)-(1-T)) with
      ((B(fsub (erfcx_pow2 0) lower)-(1-B lower))-(B lower-T)) by ring.
    eapply Rle_trans;[apply Rabs_triang|]. rewrite Rabs_Ropp. bpow_num_all. lra.
Qed.

Theorem fast_cdf_outer_ok x : finite x -> bpow radix2(-33)<=Rabs(B x)<=8 ->
  15/32<B(fast_normal_argument64 (b64_abs x)) ->
  finite(fast_cdf_outer64 x) /\ bpow radix2(-58)<=B(fast_cdf_outer64 x)<=1 /\
  Rabs(B(fast_cdf_outer64 x)-normal_cdf(B x))<=bpow radix2(-49) /\
  (B x<0 -> Rabs(B(fast_cdf_outer64 x)-normal_cdf(B x))<=bpow radix2(-48)*normal_cdf(B x)).
Proof.
  intros Fx X Tail.
  assert (Fa : finite(b64_abs x)) by (unfold b64_abs;destruct x;exact Fx).
  destruct (fast_cdf_lower_ok (b64_abs x) Fa ltac:(rewrite B_abs;exact X) Tail) as [Fl [L [Tu Error]]].
  rewrite B_abs in Tu,Error.
  assert (Fzero : finite normal_zero) by reflexivity.
  assert (Zero : B normal_zero=0) by reflexivity.
  assert (Tp : 0<normal_tail (Rabs (B x))).
  { destruct (normal_tail_range (Rabs (B x))) as [P _];[pose proof (bpow_gt_0 radix2 (-33));lra|exact P]. }
  unfold fast_cdf_outer64. cbv zeta. destruct (normal_lt x normal_zero) eqn:Sign.
  - apply normal_lt_true in Sign;try assumption. rewrite Zero in Sign.
    assert (Target : normal_cdf(B x)=normal_tail (Rabs (B x))).
    { rewrite Rabs_left by lra. rewrite normal_tail_negative_cdf,Ropp_involutive. reflexivity. }
    rewrite Target. split;[exact Fl|]. split;[lra|]. split;[|intros;exact Error].
    eapply Rle_trans;[exact Error|]. bpow_num_all. lra.
  - apply normal_lt_false in Sign;try assumption. rewrite Zero in Sign.
    assert (Target : normal_cdf(B x)=1-normal_tail (Rabs (B x))).
    { rewrite Rabs_pos_eq by lra. rewrite normal_tail_complement. unfold normal_cdf. field. }
    rewrite Target.
    destruct (cdf_complement_ok _ _ Fl L Tu Error) as [Fo [Range E]].
    split;[exact Fo|]. split;[exact Range|]. split;[exact E|lra].
Qed.

Theorem fast_cdf_ok x : finite x -> bpow radix2(-33)<=Rabs(B x)<=8 ->
  finite(fast_cdf64 x) /\ bpow radix2(-58)<=B(fast_cdf64 x)<=1 /\
  Rabs(B(fast_cdf64 x)-normal_cdf(B x))<=bpow radix2(-49) /\
  (B x<0 -> Rabs(B(fast_cdf64 x)-normal_cdf(B x))<=bpow radix2(-48)*normal_cdf(B x)).
Proof.
  intros Fx X. unfold fast_cdf64.
  assert (Fa : finite(b64_abs x)) by (unfold b64_abs;destruct x;exact Fx).
  destruct (fast_normal_argument_ok (b64_abs x) Fa ltac:(rewrite B_abs;exact X)) as [Fz _].
  destruct cdf_limit_ok as [Fl Lv].
  destruct (normal_le (fast_normal_argument64 (b64_abs x)) cdf_limit) eqn:Body.
  - apply (normal_le_true _ _ Fz Fl) in Body. rewrite Lv in Body.
    destruct (fast_cdf_body_ok x Fx X Body) as [Fv [Range Error]].
    split;[exact Fv|]. split;[bpow_num_all;lra|]. split;[bpow_num_all;lra|].
    intros N. assert (Phi : 29/128-3*bpow radix2(-53)<=normal_cdf(B x)).
    { pose proof (Rabs_le_inv _ _ Error). lra. }
    eapply Rle_trans;[exact Error|]. bpow_num_all. lra.
  - apply (normal_le_false _ _ Fz Fl) in Body. rewrite Lv in Body.
    apply fast_cdf_outer_ok;assumption.
Qed.

Theorem fast_cdf_screen_finite x : finite x ->
  (fast_cdf_screen64 x=true <-> bpow radix2(-33)<=Rabs(B x)<=8).
Proof.
  intros Fx;assert(Fa : finite(b64_abs x))by(unfold b64_abs;destruct x;exact Fx).
  destruct(erfcx_pow2_ok(-33)ltac:(lia))as[Fmin Min].
  destruct(erfcx_pow2_ok 3 ltac:(lia))as[Fmax Max].
  unfold fast_cdf_screen64;rewrite andb_true_iff,
    (normal_le_true _ _ Fmin Fa),(normal_le_true _ _ Fa Fmax),Min,Max,B_abs.
  change(bpow radix2 3)with 8;tauto.
Qed.

Theorem fast_cdf_entry_ok x : finite x -> bpow radix2(-33)<=Rabs(B x)<=8 ->
  finite(fast_cdf_entry64 x) /\ bpow radix2(-58)<=B(fast_cdf_entry64 x)<=1 /\
  Rabs(B(fast_cdf_entry64 x)-normal_cdf(B x))<=bpow radix2(-49) /\
  (B x<0 -> Rabs(B(fast_cdf_entry64 x)-normal_cdf(B x))<=bpow radix2(-48)*normal_cdf(B x)).
Proof.
  intros Fx X;unfold fast_cdf_entry64.
  rewrite(proj2(fast_cdf_screen_finite x Fx)X);apply fast_cdf_ok;assumption.
Qed.

Theorem fast_cdf_fallback x : fast_cdf_screen64 x=false ->
  fast_cdf_entry64 x=normal_entry64 NormalCdf x.
Proof. intros Screen;unfold fast_cdf_entry64;rewrite Screen;reflexivity. Qed.

Theorem fast_cdf_fallback_contract x : fast_cdf_screen64 x=false ->
  normal_contract NormalCdf x (fast_cdf_entry64 x).
Proof. intros Screen;rewrite fast_cdf_fallback by exact Screen;apply normal_public_contract. Qed.

Theorem fast_cdf_nonfinite x : is_finite 53 1024 x=false ->
  fast_cdf_entry64 x=normal_entry64 NormalCdf x.
Proof.
  intros Nonfinite;destruct x as[s|s|s p Hp|s m e Hm];try discriminate.
  - destruct s;reflexivity.
  - reflexivity.
Qed.

Theorem fast_cdf_zeros :
  fast_cdf_entry64(B754_zero 53 1024 false)=erfcx_pow2(-1) /\
  fast_cdf_entry64(B754_zero 53 1024 true)=erfcx_pow2(-1).
Proof. split;reflexivity. Qed.
