(** Rounded evaluation of the short sine/cosine tails, on the regular residual
    domain. The tiny residual branch is handled separately. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Gappa Require Import Gappa_library.
From Binary64 Require Import IEEE64.
From Interval Require Import Tactic.
Require Import StageGappa TrigTables TrigPolynomial.
Require trig_sin_tail trig_cos_tail.
Open Scope R_scope.

(** The operation order in [trig::fast], without contraction. *)
Definition trig_horner u a b c := fadd a (fmul u (fadd b (fmul u c))).
Definition trig_tail_eval t :=
 let u:=fmul t t in
 let ps:=trig_horner u trig_s0 trig_s1 trig_s2 in
 let pc:=trig_horner u trig_c0 trig_c1 trig_c2 in
 (u,ps,pc,fmul (fmul t u) ps,fmul (fmul u u) pc).

Lemma trig_mul_bounded e a b : finite a -> finite b -> (-1074<=e<=0)%Z ->
 Rabs(B a*B b)<=bpow radix2 e ->
 finite(fmul a b) /\ B(fmul a b)=rn(B a*B b) /\
 Rabs(B(fmul a b))<=bpow radix2 e.
Proof.
 intros A B E Bound.
 assert (Bd:bnd 1 e (IEEE64.B a*IEEE64.B b)).
 { unfold bnd. change (IZR 1) with 1. rewrite Rmult_1_l; exact Bound. }
 destruct (fmul_bnd 1 e a b A B ltac:(lia) ltac:(lia)
   ltac:(apply Z.pow_gt_1; lia) ltac:(lia) Bd) as [F [Value Out]].
 unfold bnd in Out. change (IZR 1) with 1 in Out. rewrite Rmult_1_l in Out.
 repeat split; assumption.
Qed.

Lemma trig_add_bounded a b : finite a -> finite b -> Rabs(B a+B b)<=1 ->
 finite(fadd a b) /\ B(fadd a b)=rn(B a+B b) /\ Rabs(B(fadd a b))<=1.
Proof.
 intros A B Bound.
 assert (Bd:bnd 1 0 (IEEE64.B a+IEEE64.B b)).
 { unfold bnd. change (IZR 1) with 1. change (bpow radix2 0) with 1. nra. }
 destruct (fadd_bnd 1 0 a b A B ltac:(lia) ltac:(lia)
   ltac:(apply Z.pow_gt_1; lia) ltac:(lia) Bd) as [F [Value Out]].
 unfold bnd in Out. change (IZR 1) with 1 in Out. change (bpow radix2 0) with 1 in Out.
 repeat split; try assumption; nra.
Qed.

Lemma trig_horner_eval u a b c : finite u -> finite a -> finite b -> finite c ->
 Rabs(B u)<=/8192 -> Rabs(B a)<=/4 -> Rabs(B b)<=/4 -> Rabs(B c)<=/4 ->
 finite(trig_horner u a b c) /\
 B(trig_horner u a b c)=rn(B a+rn(B u*rn(B b+rn(B u*B c)))) /\
 Rabs(B(trig_horner u a b c))<=1.
Proof.
 intros U A B C Ub Ab Bb Cb.
 destruct (trig_mul_bounded (-13) u c U C ltac:(lia)
   ltac:(bpow_num; interval)) as [F1 [V1 B1]].
 destruct (trig_add_bounded b (fmul u c) B F1
   ltac:(bpow_num_all; interval)) as [F2 [V2 B2]].
 destruct (trig_mul_bounded (-13) u (fadd b (fmul u c)) U F2 ltac:(lia)
   ltac:(rewrite Rabs_mult; bpow_num; pose proof (Rabs_pos (IEEE64.B u)); pose proof (Rabs_pos (IEEE64.B (fadd b (fmul u c)))); nra)) as [F3 [V3 B3]].
 destruct (trig_add_bounded a (fmul u (fadd b (fmul u c))) A F3
   ltac:(bpow_num_all; interval)) as [F4 [V4 B4]].
 unfold trig_horner. split; [exact F4|]. split; [rewrite V4,V3,V2,V1; reflexivity|exact B4].
Qed.

Theorem trig_tail_evaluation t : finite t -> Rabs(B t)<=0.0078126 ->
 let '(u,ps,pc,st,ct):=trig_tail_eval t in
 finite u /\ finite ps /\ finite pc /\ finite st /\ finite ct /\
 B u=rn(B t*B t) /\
 B ps=rn(B trig_s0+rn(B u*rn(B trig_s1+rn(B u*B trig_s2)))) /\
 B pc=rn(B trig_c0+rn(B u*rn(B trig_c1+rn(B u*B trig_c2)))) /\
 B st=rn(rn(B t*B u)*B ps) /\ B ct=rn(rn(B u*B u)*B pc).
Proof.
 intros T Range. unfold trig_tail_eval.
 destruct (trig_mul_bounded (-13) t t T T ltac:(lia)
   ltac:(bpow_num; interval)) as [U [Uv Ub]].
 assert (SU:Rabs(B(fmul t t))<=/8192) by (bpow_num_all; exact Ub).
 destruct (trig_horner_eval (fmul t t) trig_s0 trig_s1 trig_s2 U
   trig_s0_finite trig_s1_finite trig_s2_finite SU
   ltac:(rewrite trig_s0_val; interval) ltac:(rewrite trig_s1_val; interval)
   ltac:(rewrite trig_s2_val; interval)) as [S [Sv Sb]].
 destruct (trig_horner_eval (fmul t t) trig_c0 trig_c1 trig_c2 U
   trig_c0_finite trig_c1_finite trig_c2_finite SU
   ltac:(rewrite trig_c0_val; interval) ltac:(rewrite trig_c1_val; interval)
   ltac:(rewrite trig_c2_val; interval)) as [C [Cv Cb]].
 destruct (trig_mul_bounded 0 t (fmul t t) T U ltac:(lia)
   ltac:(change (bpow radix2 0) with 1; interval)) as [A3 [A3v A3b]].
 destruct (trig_mul_bounded 0 (fmul t t) (fmul t t) U U ltac:(lia)
   ltac:(change (bpow radix2 0) with 1; interval)) as [A4 [A4v A4b]].
 destruct (trig_mul_bounded 0 (fmul t (fmul t t))
   (trig_horner (fmul t t) trig_s0 trig_s1 trig_s2) A3 S ltac:(lia)
   ltac:(change (bpow radix2 0) with 1 in *; rewrite Rabs_mult;
     apply Rle_trans with (1*1); [apply Rmult_le_compat; try apply Rabs_pos; assumption|lra])) as [ST [STv STb]].
 destruct (trig_mul_bounded 0 (fmul (fmul t t) (fmul t t))
   (trig_horner (fmul t t) trig_c0 trig_c1 trig_c2) A4 C ltac:(lia)
   ltac:(change (bpow radix2 0) with 1 in *; rewrite Rabs_mult;
     apply Rle_trans with (1*1); [apply Rmult_le_compat; try apply Rabs_pos; assumption|lra])) as [CT [CTv CTb]].
 repeat split; try assumption; [rewrite STv,A3v|rewrite CTv,A4v]; reflexivity.
Qed.

Lemma trig_coefficient_gappa_values :
 B trig_s0=IZR (-6004799503160661)*bpow radix2 (-55) /\
 B trig_s1=IZR 600479950272053*bpow radix2 (-56) /\
 B trig_s2=IZR (-3659917331012787)*bpow radix2 (-64) /\
 B trig_c0=IZR 6004799503160661*bpow radix2 (-57) /\
 B trig_c1=IZR (-6405119469336935)*bpow radix2 (-62) /\
 B trig_c2=IZR 3659771605655355*bpow radix2 (-67).
Proof.
 rewrite trig_s0_val,trig_s1_val,trig_s2_val,trig_c0_val,trig_c1_val,trig_c2_val.
 bpow_num. repeat split; field.
Qed.

Lemma trig_sin_tail_certificate t_ : /2^60<=Rabs(rn t_)<=0.0078126 ->
 let t:=rn t_ in let u:=rn(t*t) in
 let ps:=rn(B trig_s0+rn(u*rn(B trig_s1+rn(u*B trig_s2)))) in
 let tail:=rn(rn(t*u)*ps) in let exact:=t*t*t*trig_ps(t*t) in
 Rabs((tail-exact)/exact)<=/2^50.
Proof.
 intros T t u ps tail exact.
 destruct trig_coefficient_gappa_values as [S0 [S1 [S2 [C0 [C1 C2]]]]].
 assert (G:BND ((tail-exact)/exact) (makepairF (Float2 (-1) (-50)) (Float2 1 (-50)))).
 { subst t u ps tail exact. unfold trig_ps. rewrite S0,S1,S2.
   gappa_goal (trig_sin_tail.l1 t_). }
 apply bnd_to in G. destruct G as [G1 G2]. bpow_num_all. apply Rabs_le; lra.
Qed.

Lemma trig_cos_tail_certificate t_ : /2^60<=Rabs(rn t_)<=0.0078126 ->
 let t:=rn t_ in let u:=rn(t*t) in
 let pc:=rn(B trig_c0+rn(u*rn(B trig_c1+rn(u*B trig_c2)))) in
 let tail:=rn(rn(u*u)*pc) in let exact:=t*t*t*t*trig_pc(t*t) in
 Rabs((tail-exact)/exact)<=/2^50.
Proof.
 intros T t u pc tail exact.
 destruct trig_coefficient_gappa_values as [S0 [S1 [S2 [C0 [C1 C2]]]]].
 assert (G:BND ((tail-exact)/exact) (makepairF (Float2 (-1) (-50)) (Float2 1 (-50)))).
 { subst t u pc tail exact. unfold trig_pc. rewrite C0,C1,C2.
   gappa_goal (trig_cos_tail.l1 t_). }
 apply bnd_to in G. destruct G as [G1 G2]. bpow_num_all. apply Rabs_le; lra.
Qed.

Lemma trig_ratio_bound y v eps : v<>0 -> Rabs((y-v)/v)<=eps ->
 Rabs(y-v)<=eps*Rabs v.
Proof.
 intros Nonzero Error.
 replace (y-v) with (((y-v)/v)*v) by (field; exact Nonzero).
 rewrite Rabs_mult. apply Rmult_le_compat_r; [apply Rabs_pos|exact Error].
Qed.

Theorem trig_tail_regular t : finite t -> /2^60<=Rabs(B t)<=0.0078126 ->
 let '(_,_,_,st,ct):=trig_tail_eval t in
 Rabs(B st-(B t)^3*trig_ps(B t*B t))<=/2^50*Rabs((B t)^3*trig_ps(B t*B t)) /\
 Rabs(B ct-(B t)^4*trig_pc(B t*B t))<=/2^50*Rabs((B t)^4*trig_pc(B t*B t)).
Proof.
 intros T Range. pose proof (proj2 Range) as Upper.
 assert (RN:rn(B t)=B t) by (apply round_generic; [exact _|apply B_fmt]).
 assert (Nonzero:B t<>0).
 { intro Zero. rewrite Zero,Rabs_R0 in Range. assert (Positive:0</2^60) by interval. lra. }
 assert (PS:trig_ps(B t*B t)<0).
 { unfold trig_ps. rewrite trig_s0_val,trig_s1_val,trig_s2_val. interval. }
 assert (PC:0<trig_pc(B t*B t)).
 { unfold trig_pc. rewrite trig_c0_val,trig_c1_val,trig_c2_val. interval. }
 pose proof (trig_tail_evaluation t T (proj2 Range)) as Eval.
 unfold trig_tail_eval in Eval |- *.
 destruct Eval as [U [S [C [ST [CT [Uv [Sv [Cv [STv CTv]]]]]]]]].
 pose proof (trig_sin_tail_certificate (B t) ltac:(rewrite RN; exact Range)) as Sin.
 pose proof (trig_cos_tail_certificate (B t) ltac:(rewrite RN; exact Range)) as Cos.
 cbn zeta in Sin,Cos. rewrite RN in Sin,Cos.
 rewrite <-Uv,<-Sv,<-STv in Sin. rewrite <-Uv,<-Cv,<-CTv in Cos.
 replace (B t*B t*B t) with ((B t)^3) in Sin by ring.
 replace (B t*B t*B t*B t) with ((B t)^4) in Cos by ring.
 split; apply trig_ratio_bound; try assumption;
   apply Rmult_integral_contrapositive_currified;
   [apply pow_nonzero; exact Nonzero|lra|apply pow_nonzero; exact Nonzero|lra].
Qed.
