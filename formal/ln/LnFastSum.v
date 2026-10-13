(** The first double-word addition in the shared logarithm polynomial. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Eft RoundingTest.
From Interval Require Import Tactic.
Require Import ExpFast LnFastSquare LnFastAdd Ln1pLemmas StageGappa.
Open Scope R_scope.
Definition lf_first_sum x l := let '(h,t) := lf_half_square x in add64 x l h t.
Theorem lf_first_sum_ok x l : finite x -> finite l ->
 /2^64 <= Rabs (B x) <= /32 -> B x=rndF(B x+B l) -> Rabs(B l)<=lf_u*Rabs(B x) ->
 let '(h,t) := lf_first_sum x l in
 finite h /\ finite t /\ B h=rndF(B h+B t) /\ Rabs(B h)<=1 /\ Rabs(B t)<=2 /\
 exists d1, Rabs d1<=776/2^114 /\ B h+B t=(B x+B l-B x*B x/2)*(1+d1).
Proof.
 intros Fx Fl X Dx L. pose proof (lf_half_square_ok x Fx X) as S.
 unfold lf_first_sum. destruct (lf_half_square x) as [a b]. destruct S as [Fa [Fb [D [V [Aa Ab]]]]].
 assert (A : Rabs(B a)<=Rabs(B x)/16).
 { pose proof (lf_sum_error (B a) (B b) (B_fmt a) (B_fmt b)) as E. rewrite <-D in E.
   pose proof (Rabs_triang_inv (B a) (B a+B b)) as T. rewrite V in E,T.
   assert (Q : Rabs (-(B x*B x)/2)=Rabs(B x)*Rabs(B x)/2).
   { unfold Rdiv. rewrite Rabs_mult,Rabs_Ropp,Rabs_mult,(Rabs_pos_eq (/2)); lra. }
   rewrite Q in E,T. pose proof (Rabs_pos (B x)). unfold lf_u in E. nra. }
 assert (C : Rabs(B x)+Rabs(B a)<=8*Rabs(B x+B a)).
 { pose proof (Rabs_triang_inv (B x) (B x+B a)). replace (B x-(B x+B a)) with (-B a) in H by ring.
   rewrite Rabs_Ropp in H. pose proof (Rabs_pos (B x)); lra. }
 assert (Big : forall v, Rabs v<=1 -> bnd 1 0 v).
 { intros v H. unfold bnd. change (IZR 1*bpow radix2 0) with (1*1); lra. }
 assert (Al : Rabs(B l)<=1) by (unfold lf_u in L; lra).
 destruct (add64_ok 1 0 x l a b Fx Fl Fa Fb (Big (B x) ltac:(lra)) (Big (B l) Al)
  (Big (B a) ltac:(lra)) (Big (B b) ltac:(lra)) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [Fh [Ft Eq]].
 pose proof (lf_add_normalized (B x) (B l) (B a) (B b) (B_fmt x) (B_fmt l) Dx (B_fmt a) (B_fmt b) D C) as Dh.
 pose proof (add_bound (B x) (B l) (B a) (B b) (B_fmt x) (B_fmt l) Dx (B_fmt a) (B_fmt b) D) as E.
 rewrite <-Eq in Dh,E. destruct (add64 x l a b) as [h t]. cbn [fst snd] in *.
 assert (N : B x+B l-B x*B x/2<>0).
 { intro Z. assert (Ax : Rabs(B x)<=Rabs(B l)+Rabs(B x)*Rabs(B x)/2).
   { replace (B x) with (-B l+B x*B x/2) at 1 by lra.
     apply Rle_trans with (1:=Rabs_triang _ _). rewrite Rabs_Ropp.
     unfold Rdiv; rewrite !Rabs_mult,(Rabs_pos_eq (/2)); lra. }
   assert (P : 0</2^64) by interval with (i_prec 100). unfold lf_u in L. nra. }
 assert (N' : B x+B l+(B a+B b)<>0) by (rewrite V; lra).
 specialize (E N'). rewrite V in E.
 set (d1 := (B h+B t-(B x+B l-B x*B x/2))/(B x+B l-B x*B x/2)).
 assert (Ed : Rabs d1<=776/2^114).
 { unfold d1. replace (B x+B l-B x*B x/2) with (B x+B l+ -(B x*B x)/2) by field.
   apply Rle_trans with (1:=E). unfold prec. interval with (i_prec 140). }
 assert (Id : B h+B t=(B x+B l-B x*B x/2)*(1+d1)) by (unfold d1; field; intros Z; apply N; nra).
 assert (Small : Rabs(B h+B t)<=1).
 { rewrite Id,Rabs_mult.
   assert (U : Rabs(B x+B l-B x*B x/2)<=/8).
   { apply Rle_trans with (1:=Rabs_triang _ _). rewrite Rabs_Ropp.
     pose proof (Rabs_triang (B x) (B l)). unfold Rdiv; rewrite !Rabs_mult,(Rabs_pos_eq (/2)) by lra.
     unfold lf_u in L; nra. }
   assert (Db : Rabs(1+d1)<=2).
   { pose proof (Rabs_triang 1 d1). rewrite Rabs_R1 in H.
     assert (776/2^114<=1) by interval with (i_prec 140). lra. }
   pose proof (Rabs_pos (B x+B l-B x*B x/2)). pose proof (Rabs_pos (1+d1)); nra. }
 assert (H : Rabs(B h)<=1) by (rewrite Dh; apply rnd_bound; [apply (fmt_pow 0); lia | exact Small]).
 assert (T : Rabs(B t)<=2).
 { replace (B t) with ((B h+B t)-B h) by ring. apply Rle_trans with (1:=Rabs_triang _ _). rewrite Rabs_Ropp. lra. }
 repeat split; try assumption. exists d1; split; assumption.
Qed.
