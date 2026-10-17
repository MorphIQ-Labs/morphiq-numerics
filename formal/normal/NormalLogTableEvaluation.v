(** Binary64 Horner chain for the near far-tail correction table. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Mul.
Require Import StageGappa ErfcxReciprocal ErfcxTailIntegral.
Require normal_log_table.
Open Scope R_scope.

Lemma log_table_step d a b : finite d -> finite a -> finite b ->
 Rabs(B d)<=/2 -> Rabs(B a)<=8 -> Rabs(B b)<=16 ->
 finite(fadd a(fmul d b)) /\ B(fadd a(fmul d b))=rn(B a+rn(B d*B b)) /\
 Rabs(B(fadd a(fmul d b)))<=16.
Proof.
 intros Fd Fa Fb D A V.
 destruct(fmul_bnd 1 3 d b Fd Fb ltac:(lia)ltac:(lia)ltac:(reflexivity)ltac:(lia)
  ltac:(unfold bnd;rewrite Rmult_1_l;change(bpow radix2 3)with 8;
    rewrite Rabs_mult;pose proof(Rabs_pos(B d));pose proof(Rabs_pos(B b));nra))as[Fm [Bm M]].
 destruct(fadd_bnd 1 4 a (fmul d b) Fa Fm ltac:(lia)ltac:(lia)ltac:(reflexivity)ltac:(lia)
  ltac:(unfold bnd in *;rewrite Rmult_1_l in *;change(bpow radix2 3)with 8 in M;
    change(bpow radix2 4)with 16;eapply Rle_trans;[apply Rabs_triang|lra]))as[Fs [Bs S]].
 rewrite Bm in Bs;unfold bnd in S;rewrite Rmult_1_l in S;
 change(bpow radix2 4)with 16 in S;repeat split;assumption.
Qed.

Definition log_table_horner64 d c0 c1 c2 c3 c4 c5 c6 c7 := fadd c0 (fmul d (fadd c1 (fmul d (fadd c2 (fmul d (fadd c3 (fmul d (fadd c4 (fmul d (fadd c5 (fmul d (fadd c6 (fmul d (c7)))))))))))))).
Definition log_table_horner_r d c0 c1 c2 c3 c4 c5 c6 c7 := rn(c0+rn(d*(rn(c1+rn(d*(rn(c2+rn(d*(rn(c3+rn(d*(rn(c4+rn(d*(rn(c5+rn(d*(rn(c6+rn(d*(c7))))))))))))))))))))).
Definition log_table_exact d c0 c1 c2 c3 c4 c5 c6 c7 := (c0+d*(c1+d*(c2+d*(c3+d*(c4+d*(c5+d*(c6+d*c7))))))).
Lemma log_table_horner_ieee d c0 c1 c2 c3 c4 c5 c6 c7 : finite d -> Rabs(B d)<=/2 ->
 finite c0 -> Rabs(B c0)<=8 ->
 finite c1 -> Rabs(B c1)<=8 ->
 finite c2 -> Rabs(B c2)<=8 ->
 finite c3 -> Rabs(B c3)<=8 ->
 finite c4 -> Rabs(B c4)<=8 ->
 finite c5 -> Rabs(B c5)<=8 ->
 finite c6 -> Rabs(B c6)<=8 ->
 finite c7 -> Rabs(B c7)<=8 ->
 let value:=log_table_horner64 d c0 c1 c2 c3 c4 c5 c6 c7 in
 finite value /\ B value=log_table_horner_r (B d) (B c0) (B c1) (B c2) (B c3) (B c4) (B c5) (B c6) (B c7) /\ Rabs(B value)<=16.
Proof.
 intros Fd D F0 C0 F1 C1 F2 C2 F3 C3 F4 C4 F5 C5 F6 C6 F7 C7.
 destruct(log_table_step d c6 (c7) Fd F6 F7 D C6 ltac:(lra))as[H6 [E6 P6]].
 set(p6:=fadd c6(fmul d (c7)))in *.
 destruct(log_table_step d c5 (p6) Fd F5 H6 D C5 P6)as[H5 [E5 P5]].
 set(p5:=fadd c5(fmul d (p6)))in *.
 destruct(log_table_step d c4 (p5) Fd F4 H5 D C4 P5)as[H4 [E4 P4]].
 set(p4:=fadd c4(fmul d (p5)))in *.
 destruct(log_table_step d c3 (p4) Fd F3 H4 D C3 P4)as[H3 [E3 P3]].
 set(p3:=fadd c3(fmul d (p4)))in *.
 destruct(log_table_step d c2 (p3) Fd F2 H3 D C2 P3)as[H2 [E2 P2]].
 set(p2:=fadd c2(fmul d (p3)))in *.
 destruct(log_table_step d c1 (p2) Fd F1 H2 D C1 P2)as[H1 [E1 P1]].
 set(p1:=fadd c1(fmul d (p2)))in *.
 destruct(log_table_step d c0 (p1) Fd F0 H1 D C0 P1)as[H0 [E0 P0]].
 set(p0:=fadd c0(fmul d (p1)))in *.
 unfold log_table_horner64;fold p6 p5 p4 p3 p2 p1 p0;split;[exact H0|];split;[|exact P0].
 rewrite E0,E1,E2,E3,E4,E5,E6;reflexivity.
Qed.
Lemma log_table_model d c0 c1 c2 c3 c4 c5 c6 c7 : -1/2<=d<=1/2 ->
 4<=c0<=6 -> 0<=c1<=0.03 -> -0.0004<=c2<=0 ->
 0<=c3<=0.000007 -> -0.00000013<=c4<=0 -> 0<=c5<=0.000000003 ->
 -0.00000000007<=c6<=0 -> 0<=c7<=0.000000000002 ->
 Rabs(log_table_horner_r d c0 c1 c2 c3 c4 c5 c6 c7-log_table_exact d c0 c1 c2 c3 c4 c5 c6 c7)<=9*bpow radix2(-54) /\
 3<=log_table_horner_r d c0 c1 c2 c3 c4 c5 c6 c7<=7.
Proof.
 intros D C0 C1 C2 C3 C4 C5 C6 C7;unfold log_table_horner_r,log_table_exact;
 repeat split;try apply Rabs_le;try split;erfcx_goal(normal_log_table.l1 d c0 c1 c2 c3 c4 c5 c6 c7).
Qed.
