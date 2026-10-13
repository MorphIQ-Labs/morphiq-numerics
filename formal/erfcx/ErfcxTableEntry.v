(** The actual table polynomial, composed from its IEEE entry lemmas. *)
From Coq Require Import Reals ZArith Lia Lra Psatz List.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Mul IEEE64Eft.
Require Import StageGappa ErfcxTableSplit ErfcxTableCoefficient ErfcxTableData ErfcxTableProducts ErfcxTableEvaluation.
Require Import ErfcxTableReduction.
Import ListNotations.
Local Opaque table_words table_word.
Open Scope R_scope.
Definition coef i k := b64_of_bits (table_word i k).
Definition cut1 i := b64_of_bits (truncated_bits (table_word i 2) 18).
Definition cut2 i := b64_of_bits (truncated_bits (table_word i 4) 36).
Definition tail_coefs i := map (coef i) (seq 6 7).
Definition table_polynomial64 i h e :=
 let '(hh,l) := table_split64 h e in
 let '(a1,b1,a2h,b2,p1,sq,p2) := table_leading64 i hh in
 let q := horner64 h (tail_coefs i) in
 let rest := table_rest64 (coef i 1) a1 b1 a2h b2 h hh l sq q in
 table_sum64 (coef i 0) p1 p2 rest.
Definition table_polynomial_value i h e :=
 let hh := round radix2 (FIX_exp (e-23)) (Znearest ne) h in
 let l := h-hh in
 let a1 := B (cut1 i) in let a2 := B (cut2 i) in
 let b1 := rndF (B (coef i 2)-a1+B (coef i 3)) in
 let b2 := rndF (B (coef i 4)-a2+B (coef i 5)) in
 let sq := hh*hh in
 let q := horner_value h (map B (tail_coefs i)) in
 let rest := table_rest_value (B (coef i 1)) a1 b1 (B (coef i 4)) b2 h hh l sq q in
 table_sum_value (B (coef i 0)) (a1*hh) (a2*sq) rest.

Lemma coef_bound i k : (i<177)%nat -> (k<13)%nat -> bounded64 (coef i k) 4.
Proof.
 intros I K. destruct (word_range_check_ok _ _ _ (table_word_check i k I K)) as [F V].
 change (-4*1<=B (coef i k)<=4*1) in V. split;[exact F|apply Rabs_le;lra].
Qed.
Lemma constant_bounds i : (i<177)%nat ->
 finite (coef i 0) /\ 9/256<=B (coef i 0)<=2 /\ bounded64 (coef i 1) (/2^52).
Proof.
 intros I. destruct (table_constant_check i I) as [C0 C1].
 destruct (word_range_check_ok _ _ _ C0) as [F0 V0].
 destruct (word_range_check_ok _ _ _ C1) as [F1 V1].
 change (9*/256<=B (coef i 0)<=2*1) in V0.
 change (-1*/4503599627370496<=B (coef i 1)<=1*/4503599627370496) in V1.
 split;[exact F0|]. split;[lra|]. split;[exact F1|apply Rabs_le;lra].
Qed.

Theorem table_polynomial_ieee i h e : (i<177)%nat -> finite h -> (0<=e<=3)%Z ->
 Rabs (B h)<=bpow radix2 (e-6) ->
 let '(yh,yl) := table_polynomial64 i h e in
 finite yh /\ finite yl /\ B yh+B yl=table_polynomial_value i (B h) e.
Proof.
 intros I Fh E H.
 assert (Hm : bpow radix2 (e-6)<=/8).
 { change (/8) with (bpow radix2 (-3)). apply bpow_le;lia. }
 assert (Hsmall : Rabs (B h)<=/8) by lra.
 pose proof (table_split_ieee h e Fh E H) as Split.
 unfold table_polynomial64. destruct (table_split64 h e) as [hh l] eqn:SplitDef.
 destruct Split as [FH [Fl [BH [Grid [Hbound [Exact Lbound]]]]]].
 assert (HH : Rabs (B hh)<=/8) by lra.
 assert (L : Rabs (B l)<=/2^21).
 { apply Rle_trans with (1:=Lbound). replace (/2^21) with (bpow radix2 (-21)) by (bpow_num;simpl;field).
   apply bpow_le;lia. }
 pose proof (table_leading_value_ieee i hh e I FH E Grid Hbound) as Leading.
 destruct (table_leading64 i hh) as [[[[[[a1 b1] a2h] b2] p1] sq] p2] eqn:LeadDef.
 destruct Leading as [FA1 [FB1 [FA2 [FB2 [FP1 [FSq [FP2 [VB1 [VB2 [VP1 [VSq VP2]]]]]]]]]]].
 assert (A1id : a1=cut1 i).
 { unfold table_leading64,leading64,coefficient64 in LeadDef. inversion LeadDef;reflexivity. }
 assert (A2id : a2h=coef i 4).
 { unfold table_leading64,leading64,coefficient64 in LeadDef. inversion LeadDef;reflexivity. }
 destruct (constant_bounds i I) as [F0 [C0 CLow]].
 destruct (table_leading_size_check i I) as [Check1 Check2].
 destruct (coefficient_size_check_ok _ _ _ _ _ _ Check1) as [Size1 Low1].
 destruct (coefficient_size_check_ok _ _ _ _ _ _ Check2) as [Size2 Low2].
 change (Rabs (B (cut1 i))<=2*B (coef i 0)) in Size1.
 change (Rabs (B (cut2 i))<=4*B (coef i 0)) in Size2.
 assert (A1 : Rabs (B a1)<=4) by (rewrite A1id; lra).
 assert (A2 : Rabs (B a2h)<=4) by (rewrite A2id;exact (proj2 (coef_bound i 4 I ltac:(lia)))).
 assert (B1 : Rabs (B b1)<=/2^32).
 { rewrite VB1,A1id. replace (/2^32) with (bpow radix2 (-32)) by (bpow_num;simpl;field).
   apply abs_round_le_generic;[exact _|exact _|apply generic_format_bpow;unfold FLT_exp,emin,prec;lia|exact Low1]. }
 assert (B2 : Rabs (B b2)<=/2^14).
 { rewrite VB2,A2id. replace (/2^14) with (bpow radix2 (-14)) by (bpow_num;simpl;field).
   apply abs_round_le_generic;[exact _|exact _|apply generic_format_bpow;unfold FLT_exp,emin,prec;lia|exact Low2]. }
 assert (Sq : Rabs (B sq)<=/64).
 { rewrite VSq,Rabs_mult. pose proof (Rabs_pos (B hh));nra. }
 assert (P1 : Rabs (B p1)<=B (coef i 0)/4).
 { rewrite VP1,A1id,Rabs_mult. pose proof (Rabs_pos (B (cut1 i))). pose proof (Rabs_pos (B hh)).
   clear -Size1 HH C0 H0 H1;nra. }
 assert (P2 : Rabs (B p2)<=B (coef i 0)/16).
 { rewrite VP2. fold (cut2 i). rewrite <-VSq,Rabs_mult.
   pose proof (Rabs_pos (B (cut2 i))). pose proof (Rabs_pos (B sq)). clear -Size2 Sq C0 H0 H1;nra. }
 assert (Tail : Forall (fun a => finite a /\ Rabs (B a)<=4) (tail_coefs i)).
 { unfold tail_coefs. apply Forall_forall. intros a InA. apply in_map_iff in InA as [k [Ak Ink]].
   subst a. apply in_seq in Ink. exact (coef_bound i k I ltac:(lia)). }
 destruct (horner_ieee h (tail_coefs i) Fh Hsmall Tail) as [Fq [Q Vq]].
 pose proof (table_rest_ieee (coef i 1) a1 b1 a2h b2 h hh l sq (horner64 h (tail_coefs i))
   CLow (conj FA1 A1) (conj FB1 B1) (conj FA2 A2) (conj FB2 B2)
   (conj Fh Hsmall) (conj FH HH) (conj Fl L) (conj FSq Sq) (conj Fq Q)) as [R Vr].
 pose proof (table_sum_ieee (coef i 0) p1 p2
   (table_rest64 (coef i 1) a1 b1 a2h b2 h hh l sq (horner64 h (tail_coefs i))) F0 C0 FP1 P1 FP2 P2 R) as Sum.
 destruct (table_sum64 (coef i 0) p1 p2
   (table_rest64 (coef i 1) a1 b1 a2h b2 h hh l sq (horner64 h (tail_coefs i)))) as [yh yl].
 destruct Sum as [Fyh [Fyl Value]]. split;[exact Fyh|]. split;[exact Fyl|].
 rewrite Value,Vr,VP1,VP2,VSq,VB1,VB2,Vq,A1id,A2id.
 assert (Bl : B l=B h-B hh) by lra. rewrite Bl,BH.
 reflexivity.
Qed.


Definition table_eval64 x :=
 let '(i,c,h,e) := table_reduce64 x in table_polynomial64 (Z.to_nat i) h e.
Definition table_value x :=
 let '(i,c,h,e) := table_reduce64 x in table_polynomial_value (Z.to_nat i) (B h) e.
Theorem table_eval_ieee x : finite x -> -/2<=B x<16 ->
 let '(h,l) := table_eval64 x in
 finite h /\ finite l /\ B h+B l=table_value x.
Proof.
 intros Fx X. pose proof (table_reduce_ieee x Fx X) as Reduce.
 unfold table_eval64,table_value. destruct (table_reduce64 x) as [[[i c] h] e].
 destruct Reduce as [I [E [Fc [Fh [Exact H]]]]].
 apply table_polynomial_ieee;try assumption;lia.
Qed.
