(** Exact zero residuals, including finite zero words of either sign. *)
From Coq Require Import Reals ZArith Lia Lra.
From Flocq Require Import Core.
From Binary64 Require Import Binary64Add Binary64Mul IEEE64 IEEE64Add Grid.
Require Import StageGappa TrigTail TrigSinResidual TrigCosSquare TrigCosResidual.
Open Scope R_scope.

Lemma trig_add_f64_zero xh xl y : finite xh -> finite xl -> finite y ->
 B xh=0 -> B xl=0 -> B y=0 ->
 let '(h,l):=add_f64_64 xh xl y in finite h /\ finite l /\ B h=0 /\ B l=0.
Proof.
 intros H L Y Hz Lz Yz.
 assert (Bound:forall x, B x=0 -> bnd 0 0 (B x)).
 { intros x X. unfold bnd. rewrite X,Rabs_R0. change (IZR 0) with 0; lra. }
 pose proof (add_f64_64_ok 0 0 xh xl y H L Y
   (Bound xh Hz) (Bound xl Lz) (Bound y Yz) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Add.
 assert (Real:add_f64 0 0 0=(0,0)).
 { assert (RZ:rndF 0=0) by (apply round_0; exact _).
   unfold add_f64,two_sum,fast_two_sum.
   repeat first [rewrite Rplus_0_l|rewrite Rminus_0_r|rewrite RZ|progress cbn zeta iota].
   reflexivity. }
 destruct (add_f64_64 xh xl y) as [h l]. cbn [fst snd] in Add |- *.
 destruct Add as [Fh [Fl Value]]. rewrite Hz,Lz,Yz,Real in Value.
 injection Value as H0 L0. repeat split; assumption.
Qed.

Lemma trig_tail_zero th : finite th -> B th=0 ->
 let '(_,_,_,st,ct):=trig_tail_eval th in finite st /\ finite ct /\ B st=0 /\ B ct=0.
Proof.
 intros Th Zero.
 pose proof (trig_tail_evaluation th Th ltac:(rewrite Zero,Rabs_R0; lra)) as Eval.
 destruct (trig_tail_eval th) as [[[[u ps]pc]st]ct]. cbn zeta iota in Eval |- *.
 destruct Eval as [_ [_ [_ [St [Ct [Uv [_ [_ [Stv Ctv]]]]]]]]].
 assert (RZ:rn 0=0) by (apply round_0; exact _).
 assert (Uz:B u=0) by (rewrite Uv,Zero,Rmult_0_l,RZ; reflexivity).
 rewrite Zero,Uz in Stv. rewrite Uz in Ctv.
 repeat rewrite Rmult_0_l,RZ in Stv,Ctv.
 repeat split; assumption.
Qed.

Lemma trig_cos_square_zero th : finite th -> B th=0 ->
 let '(h,l):=trig_cos_square th in finite h /\ finite l /\ B h=0 /\ B l=0.
Proof.
 intros Th Zero.
 pose proof (trig_cos_square_on_grid th Th ltac:(rewrite Zero,Rabs_R0; lra)
   ltac:(rewrite Zero; apply grid_0)
   ltac:(left; rewrite Zero; ring)) as Square.
 destruct (trig_cos_square th) as [h l]. cbn zeta iota in Square |- *.
 destruct Square as [H [L [Normal Value]]].
 assert (Sum:B h+B l=0) by (rewrite Zero in Value; lra).
 assert (Head:B h=0) by (rewrite Normal,Sum; apply round_0; exact _).
 repeat split; try assumption; lra.
Qed.

Theorem trig_sin_residual_zero th tl : finite th -> finite tl -> B th=0 -> B tl=0 ->
 let '(h,l):=trig_sin_residual th tl in finite h /\ finite l /\ B h=0 /\ B l=0.
Proof.
 intros Th Tl Hz Lz. pose proof (trig_tail_zero th Th Hz) as Tail.
 unfold trig_sin_residual. destruct (trig_tail_eval th) as [[[[u ps]pc]st]ct].
 cbn zeta iota in Tail |- *. destruct Tail as [St [_ [Stz _]]].
 apply trig_add_f64_zero; assumption.
Qed.

Theorem trig_cos_residual_zero th tl : finite th -> finite tl -> B th=0 -> B tl=0 ->
 let '(h,l):=trig_cos_residual th tl in finite h /\ finite l /\ B h=0 /\ B l=0.
Proof.
 intros Th Tl Hz Lz. pose proof (trig_tail_zero th Th Hz) as Tail.
 pose proof (trig_cos_square_zero th Th Hz) as Square.
 unfold trig_cos_residual. destruct (trig_cos_square th) as [qh ql].
 destruct (trig_tail_eval th) as [[[[u ps]pc]st]ct].
 cbn zeta iota in Tail,Square |- *.
 destruct Tail as [_ [Ct [_ Ctz]]]. destruct Square as [Qh [Ql [Qhz Qlz]]].
 destruct (trig_mul_bounded 0 th tl Th Tl ltac:(lia)
   ltac:(rewrite Hz,Lz,Rmult_0_l,Rabs_R0; change (bpow radix2 0) with 1; lra)) as [Cross [CrossValue _]].
 assert (Crossz:B(fmul th tl)=0) by (rewrite CrossValue,Hz,Rmult_0_l; apply round_0; exact _).
 destruct (trig_sub_model ct (fmul th tl) Ct Cross
   ltac:(rewrite Ctz,Rabs_R0; lra) ltac:(rewrite Crossz,Rabs_R0; lra)) as [V [e [_ Value]]].
 assert (Vz:B(fsub ct (fmul th tl))=0) by (rewrite Value,Ctz,Crossz; ring).
 apply trig_add_f64_zero; assumption.
Qed.
