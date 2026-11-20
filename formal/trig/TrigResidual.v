(** Complete scalar residual contracts: zero, tiny and regular inputs. *)
From Coq Require Import Reals Lra.
From Flocq Require Import Core.
From Binary64 Require Import Binary64Add IEEE64 Grid.
Require Import TrigSinResidual TrigCosResidual TrigTinyResidual TrigZeroResidual.
Open Scope R_scope.

Theorem trig_sin_residual_correct th tl : finite th -> finite tl ->
 (B th=0 \/ /2^320<=Rabs(B th)) -> Rabs(B th)<=0.0078126 ->
 Rabs(B tl)<=/2^53*Rabs(B th) -> B th=rndF(B th+B tl) ->
 Rabs(B th+B tl)<=0.0078126 ->
 let '(h,l):=trig_sin_residual th tl in
 finite h /\ finite l /\ B h=rndF(B h+B l) /\
 Rabs(B h+B l-sin(B th+B tl))<=/2^65*Rabs(sin(B th+B tl)).
Proof.
 intros Th Tl [Zero|Lower] Upper Low Normal Full.
 - assert (Lz:B tl=0).
   { rewrite Zero,Rabs_R0,Rmult_0_r in Low. apply Rabs_le_inv in Low; lra. }
   pose proof (trig_sin_residual_zero th tl Th Tl Zero Lz) as Value.
   destruct (trig_sin_residual th tl) as [h l]. cbn zeta iota in Value |- *.
   destruct Value as [H [L [Hz Lz']]]. split; [exact H|]. split; [exact L|]. split.
   + rewrite Hz,Lz',Rplus_0_l. symmetry; apply round_0; exact _.
   + rewrite Hz,Lz',Zero,Lz. repeat rewrite Rplus_0_l.
     rewrite sin_0,Rminus_0_r,Rabs_R0,Rmult_0_r; lra.
 - destruct (Rle_dec (Rabs(B th)) (/2^60)) as [Tiny|Regular].
   + apply trig_sin_residual_tiny; try assumption; split; assumption.
   + apply trig_sin_residual_regular; try assumption; split; lra.
Qed.

Theorem trig_cos_residual_correct th tl : finite th -> finite tl ->
 (B th=0 \/ /2^320<=Rabs(B th)) -> Rabs(B th)<=0.0078126 ->
 Rabs(B tl)<=/2^53*Rabs(B th) -> on_grid (-320) (B tl) ->
 Rabs(B th+B tl)<=0.0078126 ->
 let '(h,l):=trig_cos_residual th tl in
 finite h /\ finite l /\ B h=rndF(B h+B l) /\
 Rabs(B h+B l-(cos(B th+B tl)-1))<=/2^65*Rabs(cos(B th+B tl)-1).
Proof.
 intros Th Tl [Zero|Lower] Upper Low Grid Full.
 - assert (Lz:B tl=0).
   { rewrite Zero,Rabs_R0,Rmult_0_r in Low. apply Rabs_le_inv in Low; lra. }
   pose proof (trig_cos_residual_zero th tl Th Tl Zero Lz) as Value.
   destruct (trig_cos_residual th tl) as [h l]. cbn zeta iota in Value |- *.
   destruct Value as [H [L [Hz Lz']]]. split; [exact H|]. split; [exact L|]. split.
   + rewrite Hz,Lz',Rplus_0_l. symmetry; apply round_0; exact _.
   + rewrite Hz,Lz',Zero,Lz. repeat rewrite Rplus_0_l. rewrite cos_0.
     replace (1-1) with 0 by ring. replace (0-0) with 0 by ring.
     rewrite Rabs_R0,Rmult_0_r; lra.
 - destruct (Rle_dec (Rabs(B th)) (/2^60)) as [Tiny|Regular].
   + apply trig_cos_residual_tiny; try assumption; split; assumption.
   + apply trig_cos_residual_regular; try assumption; split; lra.
Qed.
