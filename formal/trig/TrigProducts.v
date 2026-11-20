(** The four actual double-word products in sine/cosine reconstruction,
    with multiplication error factors derived from their operand domains. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Mul.
From Interval Require Import Tactic.
Require Import TrigMultiply TrigOperandBounds TrigError TrigTable TrigResidual TrigSinResidual TrigCosResidual.
Open Scope R_scope.

Definition trig_dw_value (p:f64*f64) := B(fst p)+B(snd p).
Definition trig_mul_dw (x y:f64*f64) := mul64 (fst x) (snd x) (fst y) (snd y).
Definition trig_product_contract x y (p:f64*f64) :=
 let '(h,l):=p in finite h /\ finite l /\ B h=rndF(B h+B l) /\
 exists m, Rabs m<=9/2^106 /\ B h+B l=trig_dw_value x*trig_dw_value y*(1+m).

Theorem trig_ready_product_correct x y :
 trig_operand_ready (bpow radix2 (-8)) x ->
 trig_operand_ready (bpow radix2 (-645)) y ->
 trig_product_contract x y (trig_mul_dw x y).
Proof.
 destruct x as [xh xl];destruct y as [yh yl].
 intros [Xh [Xl [X [Bxh [Bxl Dx]]]]] [Yh [Yl [Y [Byh [Byl Dy]]]]].
 assert (Domain:B xh*B yh=0 \/ bpow radix2 (-900)<=Rabs(B xh*B yh)).
 { destruct Dx as [X0|Xfloor];[left;rewrite X0;ring|].
   destruct Dy as [Y0|Yfloor];[left;rewrite Y0;ring|].
   right;rewrite Rabs_mult.
   eapply Rle_trans with (bpow radix2 (-8)*bpow radix2 (-645)).
   - rewrite <-bpow_plus;apply bpow_le;lia.
   - apply Rmult_le_compat;try apply bpow_ge_0;assumption. }
 assert (Wide:4<=bpow radix2 508).
 { change 4 with (bpow radix2 2);apply bpow_le;lia. }
 pose proof (trig_mul_ieee xh xl yh yl Xh Xl X Yh Yl Y
   ltac:(lra) ltac:(lra) ltac:(lra) ltac:(lra) Domain) as Product.
 unfold trig_mul_dw,trig_product_contract,trig_dw_value;cbn [fst snd].
 destruct (mul64 xh xl yh yl) as [h l].
 destruct Product as [H [L [N Error]]].
 split;[exact H|]. split;[exact L|]. split;[exact N|].
 apply trig_relative_factor;[interval|exact Error].
Qed.

Definition trig_reconstruction_products i th tl :=
 let '(s,c):=trig_table_dw i in
 let sn:=trig_sin_residual th tl in let cm:=trig_cos_residual th tl in
 (trig_mul_dw s cm,trig_mul_dw c sn,trig_mul_dw c cm,trig_mul_dw s sn).

Theorem trig_reconstruction_products_correct i th tl :
 (i<51)%nat -> finite th -> finite tl ->
 (B th=0 \/ /2^320<=Rabs(B th)) -> Rabs(B th)<=0.0078126 ->
 Rabs(B tl)<=/2^53*Rabs(B th) -> B th=rndF(B th+B tl) ->
 Grid.on_grid (-320) (B tl) -> Rabs(B th+B tl)<=0.0078126 ->
 let '(s,c):=trig_table_dw i in
 let sn:=trig_sin_residual th tl in let cm:=trig_cos_residual th tl in
 let '(scm,csn,ccm,ssn):=trig_reconstruction_products i th tl in
 trig_product_contract s cm scm /\ trig_product_contract c sn csn /\
 trig_product_contract c cm ccm /\ trig_product_contract s sn ssn.
Proof.
 intros I Th Tl Domain Upper Low Normal Grid Range.
 destruct (trig_table_operands_ready i I) as [S C].
 destruct (trig_residual_operands_ready th tl Th Tl Domain Upper Low Normal Grid Range) as [Sn Cm].
 unfold trig_reconstruction_products.
 destruct (trig_table_dw i) as [s c];cbn [fst snd] in S,C.
 split;[apply trig_ready_product_correct;assumption|].
 split;[apply trig_ready_product_correct;assumption|].
 split;apply trig_ready_product_correct;assumption.
Qed.
