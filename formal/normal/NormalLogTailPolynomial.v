(** Rounded reciprocal, square and Horner chain for the logarithmic Mills
    correction. The certificate includes rounded coefficients. *)
From Coq Require Import Reals ZArith Lia Lra Psatz Classical.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Mul.
From Gappa Require Import Gappa_library.
Require Import StageGappa ErfcxReciprocal ErfcxTailIntegral NormalLogTailData NormalLogTailApprox.
Require normal_log_tail_polynomial.
Open Scope R_scope.

Definition normal_log_tail_value_r z :=
  let r:=rn z in let u:=rn(r*r) in rn(u*normal_log_tail_horner_r u).

Lemma normal_log_tail_model z : bpow radix2 (-45)<=z<=1/37 ->
  Rabs(normal_log_tail_value_r z-normal_log_tail_polynomial(z*z))<=bpow radix2 (-61).
Proof.
  intros Z;unfold normal_log_tail_value_r,normal_log_tail_horner_r,
    normal_log_tail_polynomial,normal_log_tail_c0_r,normal_log_tail_c1_r,
    normal_log_tail_c2_r,normal_log_tail_c3_r,normal_log_tail_c4_r,
    normal_log_tail_c5_r,normal_log_tail_c6_r,normal_log_tail_c7_r.
  apply Rabs_le;split;erfcx_goal(normal_log_tail_polynomial.l1 z).
Qed.

Definition normal_log_tail_value64 x :=
  let r:=fdiv one x in let u:=fmul r r in fmul u (normal_log_tail_horner64 u).

Lemma normal_log_tail_horner_step u a b : finite u -> finite a -> finite b ->
  Rabs(B u)<=/1024 -> Rabs(B a)<=4194304 -> Rabs(B b)<=8388608 ->
  finite(fadd a (fmul u b)) /\
  B(fadd a (fmul u b))=rn(B a+rn(B u*B b)) /\
  Rabs(B(fadd a (fmul u b)))<=8388608.
Proof.
  intros Fu Fa Fb U A Bv.
  destruct(fmul_bnd 1 13 u b Fu Fb ltac:(lia)ltac:(lia)ltac:(reflexivity)ltac:(lia)
    ltac:(unfold bnd;rewrite Rmult_1_l;change(bpow radix2 13)with 8192;
      rewrite Rabs_mult;pose proof(Rabs_pos(B u));pose proof(Rabs_pos(B b));nra))as[Fm [Bm M]].
  destruct(fadd_bnd 1 23 a (fmul u b) Fa Fm ltac:(lia)ltac:(lia)ltac:(reflexivity)ltac:(lia)
    ltac:(unfold bnd in *;rewrite Rmult_1_l in *;
      change(bpow radix2 13)with 8192 in M;change(bpow radix2 23)with 8388608;
      eapply Rle_trans;[apply Rabs_triang|lra]))as[Fs [Bs S]].
  rewrite Bm in Bs;unfold bnd in S;rewrite Rmult_1_l in S.
  repeat split;assumption.
Qed.

Lemma normal_log_tail_horner_ieee u : finite u -> Rabs(B u)<=/1024 ->
  finite(normal_log_tail_horner64 u) /\
  B(normal_log_tail_horner64 u)=normal_log_tail_horner_r(B u) /\
  Rabs(B(normal_log_tail_horner64 u))<=8388608.
Proof.
  intros Fu U.
  destruct normal_log_tail_c0_ok as[F0 V0].
  assert(C0 : Rabs(B normal_log_tail_c0)<=4194304)by(rewrite V0;unfold normal_log_tail_c0_r;interval with(i_prec 100)).
  destruct normal_log_tail_c1_ok as[F1 V1].
  assert(C1 : Rabs(B normal_log_tail_c1)<=4194304)by(rewrite V1;unfold normal_log_tail_c1_r;interval with(i_prec 100)).
  destruct normal_log_tail_c2_ok as[F2 V2].
  assert(C2 : Rabs(B normal_log_tail_c2)<=4194304)by(rewrite V2;unfold normal_log_tail_c2_r;interval with(i_prec 100)).
  destruct normal_log_tail_c3_ok as[F3 V3].
  assert(C3 : Rabs(B normal_log_tail_c3)<=4194304)by(rewrite V3;unfold normal_log_tail_c3_r;interval with(i_prec 100)).
  destruct normal_log_tail_c4_ok as[F4 V4].
  assert(C4 : Rabs(B normal_log_tail_c4)<=4194304)by(rewrite V4;unfold normal_log_tail_c4_r;interval with(i_prec 100)).
  destruct normal_log_tail_c5_ok as[F5 V5].
  assert(C5 : Rabs(B normal_log_tail_c5)<=4194304)by(rewrite V5;unfold normal_log_tail_c5_r;interval with(i_prec 100)).
  destruct normal_log_tail_c6_ok as[F6 V6].
  assert(C6 : Rabs(B normal_log_tail_c6)<=4194304)by(rewrite V6;unfold normal_log_tail_c6_r;interval with(i_prec 100)).
  destruct normal_log_tail_c7_ok as[F7 V7].
  assert(C7 : Rabs(B normal_log_tail_c7)<=4194304)by(rewrite V7;unfold normal_log_tail_c7_r;interval with(i_prec 100)).
  destruct(normal_log_tail_horner_step u normal_log_tail_c6 normal_log_tail_c7 Fu F6 F7 U C6 ltac:(lra))as[H6 [E6 P6]].
  set(p6:=fadd normal_log_tail_c6 (fmul u normal_log_tail_c7))in *.
  destruct(normal_log_tail_horner_step u normal_log_tail_c5 p6 Fu F5 H6 U C5 P6)as[H5 [E5 P5]].
  set(p5:=fadd normal_log_tail_c5 (fmul u p6))in *.
  destruct(normal_log_tail_horner_step u normal_log_tail_c4 p5 Fu F4 H5 U C4 P5)as[H4 [E4 P4]].
  set(p4:=fadd normal_log_tail_c4 (fmul u p5))in *.
  destruct(normal_log_tail_horner_step u normal_log_tail_c3 p4 Fu F3 H4 U C3 P4)as[H3 [E3 P3]].
  set(p3:=fadd normal_log_tail_c3 (fmul u p4))in *.
  destruct(normal_log_tail_horner_step u normal_log_tail_c2 p3 Fu F2 H3 U C2 P3)as[H2 [E2 P2]].
  set(p2:=fadd normal_log_tail_c2 (fmul u p3))in *.
  destruct(normal_log_tail_horner_step u normal_log_tail_c1 p2 Fu F1 H2 U C1 P2)as[H1 [E1 P1]].
  set(p1:=fadd normal_log_tail_c1 (fmul u p2))in *.
  destruct(normal_log_tail_horner_step u normal_log_tail_c0 p1 Fu F0 H1 U C0 P1)as[H0 [E0 P0]].
  set(p0:=fadd normal_log_tail_c0 (fmul u p1))in *.
  unfold normal_log_tail_horner64;change(finite p0 /\ B p0=normal_log_tail_horner_r(B u) /\ Rabs(B p0)<=8388608).
  split;[exact H0|];split;[|exact P0].
  rewrite E0,E1,E2,E3,E4,E5,E6,V0,V1,V2,V3,V4,V5,V6,V7. reflexivity.
Qed.

Theorem normal_log_tail_value_ieee x : finite x -> 37<=B x<=bpow radix2 45 ->
  finite(normal_log_tail_value64 x) /\
  Rabs(B(normal_log_tail_value64 x)+ln(tail_integral(2*((1/B x)*(1/B x)))))<=bpow radix2 (-60).
Proof.
  intros Fx X;destruct one_ok as[F1 B1].
  assert(Z : bpow radix2 (-45)<=1/B x<=/32).
  { replace(bpow radix2 (-45))with(/bpow radix2 45)by(bpow_num;field).
    unfold Rdiv;rewrite Rmult_1_l;split;apply Rinv_le_contravar;bpow_num_all;lra. }
  assert(Z37 : bpow radix2 (-45)<=1/B x<=1/37).
  { split;[exact(proj1 Z)|unfold Rdiv;rewrite !Rmult_1_l;apply Rinv_le_contravar;lra]. }
  destruct(fdiv_ok 1 0 one x F1 ltac:(bpow_num_all;lra)ltac:(lia)ltac:(lia)
    ltac:(reflexivity)ltac:(lia)
    ltac:(unfold bnd;rewrite B1,Rmult_1_l;change(bpow radix2 0)with 1;
      apply Rabs_le;pose proof(bpow_gt_0 radix2 (-45));lra))as[Fr Br].
  rewrite B1 in Br;set(r:=fdiv one x)in *.
  assert(R : Rabs(B r)<=/32).
  { rewrite Br;change(/32)with(bpow radix2 (-5));apply abs_round_le_generic;
      [exact _|exact _|apply generic_format_bpow;unfold FLT_exp,emin,prec;lia|].
    change(bpow radix2 (-5))with(/32);apply Rabs_le;pose proof(bpow_gt_0 radix2 (-45));lra. }
  destruct(fmul_bnd 1 (-10) r r Fr Fr ltac:(lia)ltac:(lia)ltac:(reflexivity)ltac:(lia)
    ltac:(unfold bnd;rewrite Rmult_1_l;change(bpow radix2 (-10))with(/1024);
      rewrite Rabs_mult;pose proof(Rabs_pos(B r));nra))as[Fu [Bu U]].
  unfold bnd in U;rewrite Rmult_1_l in U;change(bpow radix2 (-10))with(/1024)in U.
  set(u:=fmul r r)in *.
  destruct(normal_log_tail_horner_ieee u Fu U)as[Fp [Bp P]].
  destruct(fmul_ok 1 13 u (normal_log_tail_horner64 u) Fu Fp ltac:(lia)ltac:(lia)ltac:(reflexivity)ltac:(lia)
    ltac:(unfold bnd;rewrite Rmult_1_l;change(bpow radix2 13)with 8192;
      rewrite Rabs_mult;pose proof(Rabs_pos(B u));pose proof(Rabs_pos(B(normal_log_tail_horner64 u)));nra))as[Fv Bv].
  assert(Value : B(normal_log_tail_value64 x)=normal_log_tail_value_r(1/B x)).
  { unfold normal_log_tail_value64;change(B(fmul u (normal_log_tail_horner64 u))=normal_log_tail_value_r(1/B x)).
    rewrite Bv,Bp,Bu,Br;reflexivity. }
  split;[exact Fv|];rewrite Value.
  pose proof(normal_log_tail_model (1/B x) Z37)as Evaluation.
  assert(T : 0<=(1/B x)*(1/B x)<=/1369).
  { pose proof(bpow_gt_0 radix2 (-45));nra. }
  pose proof(normal_log_mills_approximation _ T)as Approximation.
  replace(normal_log_tail_value_r(1/B x)+ln(tail_integral(2*(1/B x*(1/B x)))))with
    ((normal_log_tail_value_r(1/B x)-normal_log_tail_polynomial(1/B x*(1/B x)))+
     (ln(tail_integral(2*(1/B x*(1/B x))))+normal_log_tail_polynomial(1/B x*(1/B x))))by ring.
  eapply Rle_trans;[apply Rabs_triang|].
  eapply Rle_trans;[apply Rplus_le_compat;[exact Evaluation|exact Approximation]|].
  bpow_num;lra.
Qed.
