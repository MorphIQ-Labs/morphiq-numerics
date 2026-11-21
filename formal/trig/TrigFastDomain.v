(** Domain supplied to the fast kernel by actual binary64 reduction. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Bits.
From Q Require Import Q256 Q256Real.
From Binary64 Require Import IEEE64.
From Interval Require Import Tactic.
Require Import TrigReduction TrigClosest TrigQuadrant TrigWindow.
Open Scope R_scope.

Lemma trig_exact_remainder_floor x n : finite x ->
 bpow radix2 (-63)<=B x ->
 -/2<B x*(2/PI)-IZR n</2 ->
 bpow radix2 (-63)<=Rabs(B x-IZR n*(PI/2)).
Proof.
 intros F X Near. assert (Pi:1<PI/2) by interval.
 assert (Xp:0<=B x) by (pose proof (bpow_gt_0 radix2 (-63));lra).
 destruct (Rle_lt_dec (PI/4) (B x)) as [Large|Small].
 - pose proof (trig_binary64_separation x n F Large) as Gap.
   assert (Id:B x-IZR n*(PI/2)=(B x*(2/PI)-IZR n)*(PI/2)) by (field;lra).
   rewrite Id,Rabs_mult,(Rabs_pos_eq (PI/2)) by lra.
   assert (Pos:0<=Rabs(B x*(2/PI)-IZR n)) by apply Rabs_pos.
   apply Rle_trans with (/2^62);[interval|nra].
 - pose proof (trig_nearest_nonnegative (B x) n Xp Near) as N.
   assert (Half:B x*(2/PI)</2).
   { replace (/2) with ((PI/4)*(2/PI)) by (field;lra).
     apply Rmult_lt_compat_r;[apply Rdiv_lt_0_compat;lra|exact Small]. }
   assert (NI:IZR n<1) by lra.
   assert (NZ:(n<1)%Z) by (apply lt_IZR;exact NI).
   assert (Zero:n=0%Z) by lia. rewrite Zero.
   replace (B x-IZR 0*(PI/2)) with (B x) by ring.
   rewrite Rabs_pos_eq by exact Xp;exact X.
Qed.

Lemma trig_exact_remainder_upper x n :
 -/2<x*(2/PI)-IZR n</2 -> Rabs(x-IZR n*(PI/2))<=0.785399.
Proof.
 intro Near. assert (Pi:0<PI) by exact PI_RGT_0.
 assert (Id:x-IZR n*(PI/2)=(x*(2/PI)-IZR n)*(PI/2)) by (field;lra).
 assert (Half:Rabs(x*(2/PI)-IZR n)<=/2) by (apply Rabs_le;lra).
 rewrite Id,Rabs_mult,(Rabs_pos_eq (PI/2)) by lra.
 assert (Quarter:PI/4<=0.785399) by interval. nra.
Qed.

Theorem trig_reduce_fast_domain x : finite x -> bpow radix2 (-63)<=B x ->
 exists n q, trig_reduce64 (bits_of_b64 x)=((n mod 4)%Z,q) /\ valid q /\
 bpow radix2 (-64)<=Rabs(qval q)<=0.785399 /\
 bpow radix2 (-63)<=Rabs(B x-IZR n*(PI/2))<=0.785399 /\
 -/2<B x*(2/PI)-IZR n</2 /\
 Rabs(qval q-(B x-IZR n*(PI/2)))<=bpow radix2 (-199)*Rabs(B x-IZR n*(PI/2)).
Proof.
 intros F X. assert (Xp:0<=B x) by (pose proof (bpow_gt_0 radix2 (-63));lra).
 destruct (trig_reduce_correct x F Xp) as [n [q [Eq [V [Q [Near Err]]]]]].
 pose proof (trig_exact_remainder_floor x n F X Near) as Lower.
 pose proof (trig_exact_remainder_upper (B x) n Near) as Upper.
 assert (E:Rabs(qval q-(B x-IZR n*(PI/2)))<=bpow radix2 (-199)*Rabs(B x-IZR n*(PI/2))).
 { replace (bpow radix2 (-199)) with (/2^199) by (rewrite pow_IZR;reflexivity). exact Err. }
 assert (QL:bpow radix2 (-64)<=Rabs(qval q)).
 { pose proof (Rabs_triang_inv (B x-IZR n*(PI/2)) (qval q)) as H.
   rewrite (Rabs_minus_sym (B x-IZR n*(PI/2)) (qval q)) in H.
   assert (Small:0<=bpow radix2 (-199)<=/2) by (split;[apply bpow_ge_0|interval]).
   assert (P:0<=Rabs(B x-IZR n*(PI/2))) by apply Rabs_pos.
   assert (Half:bpow radix2 (-64)=(/2)*bpow radix2 (-63)) by (replace (-64)%Z with ((-1)+(-63))%Z by lia;rewrite bpow_plus;reflexivity).
   rewrite Half;nra. }
 exists n,q. split;[exact Eq|]. split;[exact V|]. split.
 - split;[exact QL|]. assert (Quarter:PI/4<=0.785399) by (clear;interval with (i_prec 100)).
   exact (Rle_trans _ _ _ Q Quarter).
 - split;[split;assumption|]. split;assumption.
Qed.
