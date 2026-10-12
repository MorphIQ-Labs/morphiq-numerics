(** Binary64 evaluation of the small-path polynomial, in scalar order. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64.
From Interval Require Import Tactic.
Require Import ExpFast Expm1Tables Expm1SmallCertificates Ln1pLemmas.
Open Scope R_scope.
Definition em_horner x := fadd em_c3 (fmul x (fadd em_c4 (fmul x (fadd em_c5 (fmul x (fadd em_c6 (fmul x (fadd em_c7 (fmul x (fadd em_c8 (fmul x (em_c9)))))))))))).
Definition em_tail x := fmul (fmul x (fmul x x)) (em_horner x).
Lemma em_horner_ok x : finite x -> Rabs (B x) <= /32 ->
 finite (em_horner x) /\ B (em_horner x) = em_wr (B x) /\ Rabs (B (em_horner x)) <= 1.
Proof.
 intros Fx X.
 assert (Step : forall a c, finite a -> finite c -> Rabs (B a) <= 1 -> Rabs (B c) <= /2 ->
 finite (fadd c (fmul x a)) /\ B (fadd c (fmul x a)) = rndF (B c+rndF (B x*B a)) /\
 Rabs (B (fadd c (fmul x a))) <= 1).
 { intros a c Fa Fc Aa Ac.
   destruct (fmul_p (-5) x a Fx Fa ltac:(lia)) as [Fm [Vm Am]].
   - change (bpow radix2 (-5)) with (/32). rewrite Rabs_mult. pose proof (Rabs_pos (B a)). nra.
   - destruct (fadd_p 0 c (fmul x a) Fc Fm ltac:(lia)) as [Fs [Vs As]].
     + change (bpow radix2 0) with 1. change (bpow radix2 (-5)) with (/32) in Am.
       apply Rle_trans with (1:=Rabs_triang _ _). lra.
     + split; [exact Fs | split; [rewrite Vs,Vm; reflexivity | exact As]]. }
 unfold em_horner.
 destruct (Step em_c9 em_c8 em_c9_finite em_c8_finite ltac:(rewrite em_c9_val; interval with (i_prec 64)) ltac:(rewrite em_c8_val; interval with (i_prec 64))) as [F1 [V1 A1]].
 destruct (Step _ em_c7 F1 em_c7_finite A1 ltac:(rewrite em_c7_val; interval with (i_prec 64))) as [F2 [V2 A2]].
 destruct (Step _ em_c6 F2 em_c6_finite A2 ltac:(rewrite em_c6_val; interval with (i_prec 64))) as [F3 [V3 A3]].
 destruct (Step _ em_c5 F3 em_c5_finite A3 ltac:(rewrite em_c5_val; interval with (i_prec 64))) as [F4 [V4 A4]].
 destruct (Step _ em_c4 F4 em_c4_finite A4 ltac:(rewrite em_c4_val; interval with (i_prec 64))) as [F5 [V5 A5]].
 destruct (Step _ em_c3 F5 em_c3_finite A5 ltac:(rewrite em_c3_val; interval with (i_prec 64))) as [F6 [V6 A6]].
 split; [exact F6 | split; [ | exact A6]].
 rewrite V6,V5,V4,V3,V2,V1. em_real_coefficients. unfold em_wr.
 change (round radix2 (FLT_exp (-1074) 53) Gappa_round_def.rndNE) with (round radix2 (FLT_exp emin prec) (Znearest ne)).
 reflexivity.
Qed.
Lemma em_tail_ok x : finite x -> Rabs (B x) <= /32 ->
 finite (em_tail x) /\ B (em_tail x) = em_tr (B x) /\ Rabs (B (em_tail x)) <= /32768.
Proof.
 intros Fx X. pose proof (Rabs_pos (B x)) as Xp. destruct (em_horner_ok x Fx X) as [Fw [Vw Aw]].
 destruct (fmul_p (-10) x x Fx Fx ltac:(lia)) as [Fs [Vs As]].
 - change (bpow radix2 (-10)) with (/1024). rewrite Rabs_mult. nra.
 - destruct (fmul_p (-15) x (fmul x x) Fx Fs ltac:(lia)) as [Fq [Vq Aq]].
   + change (bpow radix2 (-15)) with (/32768). change (bpow radix2 (-10)) with (/1024) in As.
     rewrite Rabs_mult. pose proof (Rabs_pos (B (fmul x x))). nra.
   + destruct (fmul_p (-15) (fmul x (fmul x x)) (em_horner x) Fq Fw ltac:(lia)) as [Ft [Vt At]].
     * change (bpow radix2 (-15)) with (/32768) in Aq |- *. rewrite Rabs_mult.
       pose proof (Rabs_pos (B (em_horner x))). nra.
     * split; [exact Ft | split; [ | exact At]]. unfold em_tail. rewrite Vt,Vq,Vs,Vw. reflexivity.
Qed.
