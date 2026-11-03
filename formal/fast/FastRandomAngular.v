(** Bounded angular Horner sequences for the Box–Muller octant. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add Encodings RoundingConstant RoundingGaps.
From Interval Require Import Tactic.
Require Import StageGappa FastRandomConstants.
Require normal_normal_pair_sin normal_normal_pair_cos.
Open Scope R_scope.
Definition bm_limit : R := 884279719003555 / 1125899906842624.

Ltac table_bound :=
 first [
   match goal with
   | Ha : Rabs ?a <= ?u, Hb : Rabs ?b <= ?v |- Rabs (?a * ?b) <= ?cap =>
       rewrite Rabs_mult;apply Rle_trans with (u*v);
       [apply Rmult_le_compat;[apply Rabs_pos|apply Rabs_pos|exact Ha|exact Hb]|lra]
   end
 | eapply Rle_trans;[apply Rabs_triang|lra] ].
Ltac table_op op k e a b F V C :=
 destruct (op k e a b ltac:(assumption) ltac:(assumption)
   ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)
   ltac:(unfold bnd;bpow_num;cbn [IZR];table_bound)) as [F [V C]];
 unfold bnd in C;revert C;bpow_num;cbn [IZR];intro C.

Definition bm_sin64 x := let z:=fmul x x in fmul x (fadd bm_sin0 (fmul z (fadd bm_sin1 (fmul z (fadd bm_sin2 (fmul z (fadd bm_sin3 (fmul z (fadd bm_sin4 (fmul z (bm_sin5))))))))))).
Definition bm_sin_value x := let z:=rn(x*x) in rn (x * (rn (B bm_sin0 + rn (z * (rn (B bm_sin1 + rn (z * (rn (B bm_sin2 + rn (z * (rn (B bm_sin3 + rn (z * (rn (B bm_sin4 + rn (z * (B bm_sin5))))))))))))))))).
Definition bm_sin_ideal x := let z:=x*x in x * (B bm_sin0 + z * (B bm_sin1 + z * (B bm_sin2 + z * (B bm_sin3 + z * (B bm_sin4 + z * B bm_sin5))))).
Theorem bm_sin_ieee x : finite x -> 0<=B x<=bm_limit ->
 finite (bm_sin64 x) /\ B (bm_sin64 x)=bm_sin_value (B x).
Proof.
 intros Fx X.
 assert (Ax : Rabs (B x)<=1) by (rewrite Rabs_pos_eq by lra;unfold bm_limit in X;lra).
 pose proof bm_sin0_finite as F0.
 assert (C0 : Rabs (B bm_sin0)<=1) by (rewrite bm_sin0_val;interval with (i_prec 100)).
 pose proof bm_sin1_finite as F1.
 assert (C1 : Rabs (B bm_sin1)<=1) by (rewrite bm_sin1_val;interval with (i_prec 100)).
 pose proof bm_sin2_finite as F2.
 assert (C2 : Rabs (B bm_sin2)<=1) by (rewrite bm_sin2_val;interval with (i_prec 100)).
 pose proof bm_sin3_finite as F3.
 assert (C3 : Rabs (B bm_sin3)<=1) by (rewrite bm_sin3_val;interval with (i_prec 100)).
 pose proof bm_sin4_finite as F4.
 assert (C4 : Rabs (B bm_sin4)<=1) by (rewrite bm_sin4_val;interval with (i_prec 100)).
 pose proof bm_sin5_finite as F5.
 assert (C5 : Rabs (B bm_sin5)<=1) by (rewrite bm_sin5_val;interval with (i_prec 100)).
 pose proof Ax as Axcopy.
 table_op fmul_bnd 1%Z 0%Z x x Fz Vz Cz.
 set (z:=fmul x x) in *.
 table_op fmul_bnd 1%Z 0%Z z bm_sin5 Fm4 Vm4 Cm4.
 table_op fadd_bnd 2%Z 0%Z bm_sin4 (fmul z bm_sin5) Fq4 Vq4 Cq4.
 set (q4:=fadd bm_sin4 (fmul z bm_sin5)) in *.
 table_op fmul_bnd 2%Z 0%Z z q4 Fm3 Vm3 Cm3.
 table_op fadd_bnd 4%Z 0%Z bm_sin3 (fmul z q4) Fq3 Vq3 Cq3.
 set (q3:=fadd bm_sin3 (fmul z q4)) in *.
 table_op fmul_bnd 4%Z 0%Z z q3 Fm2 Vm2 Cm2.
 table_op fadd_bnd 8%Z 0%Z bm_sin2 (fmul z q3) Fq2 Vq2 Cq2.
 set (q2:=fadd bm_sin2 (fmul z q3)) in *.
 table_op fmul_bnd 8%Z 0%Z z q2 Fm1 Vm1 Cm1.
 table_op fadd_bnd 16%Z 0%Z bm_sin1 (fmul z q2) Fq1 Vq1 Cq1.
 set (q1:=fadd bm_sin1 (fmul z q2)) in *.
 table_op fmul_bnd 16%Z 0%Z z q1 Fm0 Vm0 Cm0.
 table_op fadd_bnd 32%Z 0%Z bm_sin0 (fmul z q1) Fq0 Vq0 Cq0.
 set (q0:=fadd bm_sin0 (fmul z q1)) in *.
 table_op fmul_bnd 32%Z 0%Z x q0 Fv Vv Cv.
 unfold bm_sin64;fold z q4 q3 q2 q1 q0.
 split;[exact Fv|].
 unfold bm_sin_value.
 rewrite Vv,Vq0,Vm0,Vq1,Vm1,Vq2,Vm2,Vq3,Vm3,Vq4,Vm4,Vz. reflexivity.
Qed.
Theorem bm_sin_arithmetic x : F64 x -> 0<=x<=bm_limit ->
 Rabs (bm_sin_value x-bm_sin_ideal x)<=bpow radix2 (-51).
Proof.
 intros F X. assert (Rx : rn x=x) by (apply round_generic;[exact _|exact F]).
 unfold bm_sin_value,bm_sin_ideal;cbv zeta.
 rewrite bm_sin0_g,bm_sin1_g,bm_sin2_g,bm_sin3_g,bm_sin4_g,bm_sin5_g.
 unfold bm_limit in X.
 rewrite <-Rx;apply Rabs_le;split;gappa_goal (normal_normal_pair_sin.l1 x).
Qed.
Theorem bm_sin_approx x : 0<=x<=bm_limit ->
 Rabs (bm_sin_ideal x-sin x)<=127/2^51.
Proof.
 intros X;unfold bm_limit in X.
 unfold bm_sin_ideal;cbv zeta.
 rewrite bm_sin0_val,bm_sin1_val,bm_sin2_val,bm_sin3_val,bm_sin4_val,bm_sin5_val.
 interval with (i_bisect x, i_taylor x, i_degree 16, i_prec 200).
Qed.

Definition bm_cos64 x := let z:=fmul x x in fadd bm_cos0 (fmul z (fadd bm_cos1 (fmul z (fadd bm_cos2 (fmul z (fadd bm_cos3 (fmul z (fadd bm_cos4 (fmul z (bm_cos5)))))))))).
Definition bm_cos_value x := let z:=rn(x*x) in rn (B bm_cos0 + rn (z * (rn (B bm_cos1 + rn (z * (rn (B bm_cos2 + rn (z * (rn (B bm_cos3 + rn (z * (rn (B bm_cos4 + rn (z * (B bm_cos5))))))))))))))).
Definition bm_cos_ideal x := let z:=x*x in (B bm_cos0 + z * (B bm_cos1 + z * (B bm_cos2 + z * (B bm_cos3 + z * (B bm_cos4 + z * B bm_cos5))))).
Theorem bm_cos_ieee x : finite x -> 0<=B x<=bm_limit ->
 finite (bm_cos64 x) /\ B (bm_cos64 x)=bm_cos_value (B x).
Proof.
 intros Fx X.
 assert (Ax : Rabs (B x)<=1) by (rewrite Rabs_pos_eq by lra;unfold bm_limit in X;lra).
 pose proof bm_cos0_finite as F0.
 assert (C0 : Rabs (B bm_cos0)<=1) by (rewrite bm_cos0_val;interval with (i_prec 100)).
 pose proof bm_cos1_finite as F1.
 assert (C1 : Rabs (B bm_cos1)<=1) by (rewrite bm_cos1_val;interval with (i_prec 100)).
 pose proof bm_cos2_finite as F2.
 assert (C2 : Rabs (B bm_cos2)<=1) by (rewrite bm_cos2_val;interval with (i_prec 100)).
 pose proof bm_cos3_finite as F3.
 assert (C3 : Rabs (B bm_cos3)<=1) by (rewrite bm_cos3_val;interval with (i_prec 100)).
 pose proof bm_cos4_finite as F4.
 assert (C4 : Rabs (B bm_cos4)<=1) by (rewrite bm_cos4_val;interval with (i_prec 100)).
 pose proof bm_cos5_finite as F5.
 assert (C5 : Rabs (B bm_cos5)<=1) by (rewrite bm_cos5_val;interval with (i_prec 100)).
 pose proof Ax as Axcopy.
 table_op fmul_bnd 1%Z 0%Z x x Fz Vz Cz.
 set (z:=fmul x x) in *.
 table_op fmul_bnd 1%Z 0%Z z bm_cos5 Fm4 Vm4 Cm4.
 table_op fadd_bnd 2%Z 0%Z bm_cos4 (fmul z bm_cos5) Fq4 Vq4 Cq4.
 set (q4:=fadd bm_cos4 (fmul z bm_cos5)) in *.
 table_op fmul_bnd 2%Z 0%Z z q4 Fm3 Vm3 Cm3.
 table_op fadd_bnd 4%Z 0%Z bm_cos3 (fmul z q4) Fq3 Vq3 Cq3.
 set (q3:=fadd bm_cos3 (fmul z q4)) in *.
 table_op fmul_bnd 4%Z 0%Z z q3 Fm2 Vm2 Cm2.
 table_op fadd_bnd 8%Z 0%Z bm_cos2 (fmul z q3) Fq2 Vq2 Cq2.
 set (q2:=fadd bm_cos2 (fmul z q3)) in *.
 table_op fmul_bnd 8%Z 0%Z z q2 Fm1 Vm1 Cm1.
 table_op fadd_bnd 16%Z 0%Z bm_cos1 (fmul z q2) Fq1 Vq1 Cq1.
 set (q1:=fadd bm_cos1 (fmul z q2)) in *.
 table_op fmul_bnd 16%Z 0%Z z q1 Fm0 Vm0 Cm0.
 table_op fadd_bnd 32%Z 0%Z bm_cos0 (fmul z q1) Fq0 Vq0 Cq0.
 set (q0:=fadd bm_cos0 (fmul z q1)) in *.
 unfold bm_cos64;fold z q4 q3 q2 q1 q0.
 split;[exact Fq0|].
 unfold bm_cos_value.
 rewrite Vq0,Vm0,Vq1,Vm1,Vq2,Vm2,Vq3,Vm3,Vq4,Vm4,Vz. reflexivity.
Qed.
Theorem bm_cos_arithmetic x : F64 x -> 0<=x<=bm_limit ->
 Rabs (bm_cos_value x-bm_cos_ideal x)<=bpow radix2 (-51).
Proof.
 intros F X. assert (Rx : rn x=x) by (apply round_generic;[exact _|exact F]).
 unfold bm_cos_value,bm_cos_ideal;cbv zeta.
 rewrite bm_cos0_g,bm_cos1_g,bm_cos2_g,bm_cos3_g,bm_cos4_g,bm_cos5_g.
 unfold bm_limit in X.
 rewrite <-Rx;apply Rabs_le;split;gappa_goal (normal_normal_pair_cos.l1 x).
Qed.
Theorem bm_cos_approx x : 0<=x<=bm_limit ->
 Rabs (bm_cos_ideal x-cos x)<=127/2^51.
Proof.
 intros X;unfold bm_limit in X.
 unfold bm_cos_ideal;cbv zeta.
 rewrite bm_cos0_val,bm_cos1_val,bm_cos2_val,bm_cos3_val,bm_cos4_val,bm_cos5_val.
 interval with (i_bisect x, i_taylor x, i_degree 16, i_prec 200).
Qed.

Theorem bm_sin_ok x : finite x -> 0<=B x<=bm_limit ->
 finite (bm_sin64 x) /\ Rabs(B(bm_sin64 x)-sin(B x))<=/2^44.
Proof.
 intros F X. destruct (bm_sin_ieee x F X) as [Fs V].
 pose proof (bm_sin_arithmetic (B x) (B_fmt x) X) as A.
 pose proof (bm_sin_approx (B x) X) as P.
 split;[exact Fs|]. rewrite V.
 replace (bm_sin_value (B x)-sin(B x)) with
   ((bm_sin_value (B x)-bm_sin_ideal (B x))+(bm_sin_ideal (B x)-sin(B x))) by ring.
 eapply Rle_trans;[apply Rabs_triang|]. bpow_num_all;lra.
Qed.

Theorem bm_cos_ok x : finite x -> 0<=B x<=bm_limit ->
 finite (bm_cos64 x) /\ Rabs(B(bm_cos64 x)-cos(B x))<=/2^44.
Proof.
 intros F X. destruct (bm_cos_ieee x F X) as [Fs V].
 pose proof (bm_cos_arithmetic (B x) (B_fmt x) X) as A.
 pose proof (bm_cos_approx (B x) X) as P.
 split;[exact Fs|]. rewrite V.
 replace (bm_cos_value (B x)-cos(B x)) with
   ((bm_cos_value (B x)-bm_cos_ideal (B x))+(bm_cos_ideal (B x)-cos(B x))) by ring.
 eapply Rle_trans;[apply Rabs_triang|]. bpow_num_all;lra.
Qed.

Theorem bm_zero_angle : bm_sin64 (b64_of_bits 0)=b64_of_bits 0.
Proof. vm_compute;reflexivity. Qed.
