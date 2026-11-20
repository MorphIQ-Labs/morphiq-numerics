(** Magnitude premises for the actual trig reconstruction operands. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Binary64 Require Import Binary64Add IEEE64.
From Interval Require Import Tactic.
Require Import StageGappa TrigMultiply TrigPolynomial TrigTables TrigTable TrigResidual TrigSinResidual TrigCosResidual.
Open Scope R_scope.

Lemma trig_dw_head_magnitude h l v eps : fmtF h -> fmtF l -> h=rndF(h+l) ->
 0<=eps<=/4 -> Rabs(h+l-v)<=eps*Rabs v ->
 Rabs v/2<=Rabs h /\ Rabs h<=2*Rabs v /\ Rabs l<=trig_mul_u*Rabs h.
Proof.
 intros H L N E Error.
 pose proof (trig_dw_low h l H L N) as Low.
 assert (Err:Rabs(h+l-v)<=Rabs v/4).
 { eapply Rle_trans;[exact Error|]. pose proof (Rabs_pos v);nra. }
 pose proof (Rabs_triang (h+l-v) v) as Full.
 replace (h+l-v+v) with (h+l) in Full by ring.
 pose proof (Rabs_triang (h+l) (-l)) as Head.
 replace (h+l+ -l) with h in Head by ring. rewrite Rabs_Ropp in Head.
 pose proof (Rabs_triang (v-(h+l)) (h+l)) as Ref.
 replace (v-(h+l)+(h+l)) with v in Ref by ring.
 rewrite Rabs_minus_sym in Ref.
 pose proof (Rabs_triang h l) as Sum.
 split;[|split;[|exact Low]];
 clear - Err Low Full Head Ref Sum;unfold trig_mul_u in *;lra.
Qed.

Lemma trig_small_sin_magnitude t : Rabs t<=0.0078126 ->
 Rabs t/2<=Rabs(sin t).
Proof.
 intro T. destruct (trig_sin_polynomial_model t T) as [al [Al Value]].
 assert (Factor:1/2<=1+t*t*trig_ps(t*t)*(1+al)).
 { unfold trig_ps,trig_poly_error in *;rewrite trig_s0_val,trig_s1_val,trig_s2_val;interval. }
 rewrite Value. replace (t+t^3*trig_ps(t*t)*(1+al)) with (t*(1+t*t*trig_ps(t*t)*(1+al))) by ring.
 rewrite Rabs_mult,(Rabs_pos_eq (1+t*t*trig_ps(t*t)*(1+al))) by lra.
 pose proof (Rabs_pos t);nra.
Qed.

Lemma trig_small_cos_magnitude t : Rabs t<=0.0078126 ->
 t*t/4<=Rabs(cos t-1).
Proof.
 intro T. destruct (trig_cos_polynomial_model t T) as [al [Al Value]].
 assert (Factor:1/4<=1/2-t*t*trig_pc(t*t)*(1+al)).
 { unfold trig_pc,trig_poly_error in *;rewrite trig_c0_val,trig_c1_val,trig_c2_val;interval. }
 rewrite Value. replace (1-t*t/2+t^4*trig_pc(t*t)*(1+al)-1) with
   (-(t*t*(1/2-t*t*trig_pc(t*t)*(1+al)))) by field.
 rewrite Rabs_Ropp,Rabs_mult,(Rabs_pos_eq (t*t)),(Rabs_pos_eq (1/2-t*t*trig_pc(t*t)*(1+al)))
   by (pose proof (Rle_0_sqr t);unfold Rsqr in *;nra).
 pose proof (Rle_0_sqr t);unfold Rsqr in *;nra.
Qed.

Definition trig_operand_ready floor (p:f64*f64) :=
 let '(h,l):=p in finite h /\ finite l /\ B h=rndF(B h+B l) /\
 Rabs(B h)<=4 /\ Rabs(B l)<=4 /\ (B h=0 \/ floor<=Rabs(B h)).

Lemma trig_operand_from_reference floor h l v eps :
 finite h -> finite l -> B h=rndF(B h+B l) ->
 0<=eps<=/4 -> Rabs(B h+B l-v)<=eps*Rabs v ->
 Rabs v<=2 -> (v=0 \/ 2*floor<=Rabs v) -> trig_operand_ready floor (h,l).
Proof.
 intros H L N E Error Upper Domain.
 destruct (trig_dw_head_magnitude (B h) (B l) v eps (B_fmt h) (B_fmt l) N E Error)
   as [Lower [Head Low]].
 unfold trig_operand_ready.
 split;[exact H|]. split;[exact L|]. split;[exact N|].
 split;[lra|]. split.
 - unfold trig_mul_u in Low. lra.
 - destruct Domain as [Zero|Floor].
   + left. rewrite Zero,Rabs_R0 in Head. apply Rabs_le_inv in Head;lra.
   + right;lra.
Qed.

Theorem trig_table_operands_ready i : (i<51)%nat ->
 trig_operand_ready (bpow radix2 (-8)) (fst(trig_table_dw i)) /\
 trig_operand_ready (bpow radix2 (-8)) (snd(trig_table_dw i)).
Proof.
 intro I. pose proof (trig_table_dw_ok i I) as [S C].
 assert (A:0<=IZR(Z.of_nat i)/64<=50/64).
 { assert (IZ:0<=IZR(Z.of_nat i)<=50).
   { split;apply IZR_le;lia. } lra. }
 assert (Nonzero:i=0%nat \/ /64<=IZR(Z.of_nat i)/64).
 { destruct i;[left;reflexivity|right].
   assert (L:1<=IZR(Z.of_nat(Datatypes.S i))) by (apply IZR_le;lia). lra. }
 assert (SinDomain:sin(IZR(Z.of_nat i)/64)=0 \/
   2*bpow radix2 (-8)<=Rabs(sin(IZR(Z.of_nat i)/64))).
 { destruct Nonzero as [Zero|Lower].
   - left;rewrite Zero;change (sin(0/64)=0);replace (0/64) with 0 by field;apply sin_0.
   - right;change (bpow radix2 (-8)) with (/256);set (a:=IZR(Z.of_nat i)/64) in *;interval. }
 assert (CosDomain:cos(IZR(Z.of_nat i)/64)=0 \/
   2*bpow radix2 (-8)<=Rabs(cos(IZR(Z.of_nat i)/64))) by (right;change (bpow radix2 (-8)) with (/256);set (a:=IZR(Z.of_nat i)/64) in *;interval).
 destruct (trig_table_dw i) as [[sh sl][ch cl]]. cbn [fst snd] in *.
 unfold trig_table_dw_component_ok in S,C.
 destruct S as [Sh [Sl [Sn Se]]]. destruct C as [Ch [Cl [Cn Ce]]].
 split.
 - apply (trig_operand_from_reference _ sh sl (sin(IZR(Z.of_nat i)/64)) trig_table_error);
     try assumption;unfold trig_table_error;set (a:=IZR(Z.of_nat i)/64) in *;interval.
 - apply (trig_operand_from_reference _ ch cl (cos(IZR(Z.of_nat i)/64)) trig_table_error);
     try assumption;unfold trig_table_error;set (a:=IZR(Z.of_nat i)/64) in *;interval.
Qed.

Lemma trig_residual_reference_floors th tl :
 (th=0 \/ /2^320<=Rabs th) -> Rabs tl<=/2^53*Rabs th ->
 Rabs(th+tl)<=0.0078126 ->
 (sin(th+tl)=0 \/ 2*bpow radix2 (-645)<=Rabs(sin(th+tl))) /\
 (cos(th+tl)-1=0 \/ 2*bpow radix2 (-645)<=Rabs(cos(th+tl)-1)).
Proof.
 intros [Zero|Lower] Low Range.
 - assert (Lz:tl=0).
   { rewrite Zero,Rabs_R0,Rmult_0_r in Low;apply Rabs_le_inv in Low;lra. }
   rewrite Zero,Lz,Rplus_0_l,sin_0,cos_0. split;left;ring.
 - assert (FullFloor:/2^321<=Rabs(th+tl)).
   { pose proof (Rabs_triang (th+tl) (-tl)) as T.
     replace (th+tl+ -tl) with th in T by ring;rewrite Rabs_Ropp in T.
     clear - Lower Low T. lra. }
   pose proof (trig_small_sin_magnitude (th+tl) Range) as Sin.
   pose proof (trig_small_cos_magnitude (th+tl) Range) as Cos.
   assert (Square:Rabs(th+tl)*Rabs(th+tl)=(th+tl)*(th+tl)).
   { rewrite <-Rabs_mult. apply Rabs_pos_eq. apply Rle_0_sqr. }
   assert (Positive:0</2^321) by interval.
   split;right.
   + clear - FullFloor Sin. replace (bpow radix2 (-645)) with (/2^645) by (bpow_num;field). lra.
   + clear - FullFloor Cos Square Positive.
     replace (bpow radix2 (-645)) with (/2^645) by (bpow_num;field). nra.
Qed.

Theorem trig_residual_operands_ready th tl : finite th -> finite tl ->
 (B th=0 \/ /2^320<=Rabs(B th)) -> Rabs(B th)<=0.0078126 ->
 Rabs(B tl)<=/2^53*Rabs(B th) -> B th=rndF(B th+B tl) ->
 Grid.on_grid (-320) (B tl) -> Rabs(B th+B tl)<=0.0078126 ->
 trig_operand_ready (bpow radix2 (-645)) (trig_sin_residual th tl) /\
 trig_operand_ready (bpow radix2 (-645)) (trig_cos_residual th tl).
Proof.
 intros Th Tl Domain Upper Low Normal Grid Range.
 pose proof (trig_sin_residual_correct th tl Th Tl Domain Upper Low Normal Range) as S.
 pose proof (trig_cos_residual_correct th tl Th Tl Domain Upper Low Grid Range) as C.
 destruct (trig_residual_reference_floors (B th) (B tl) Domain Low Range) as [Sf Cf].
 destruct (trig_sin_residual th tl) as [sh sl].
 destruct (trig_cos_residual th tl) as [ch cl].
 destruct S as [Sh [Sl [Sn Se]]]. destruct C as [Ch [Cl [Cn Ce]]].
 split.
 - apply (trig_operand_from_reference _ sh sl (sin(B th+B tl)) (/2^65));
     try assumption;set (t:=B th+B tl) in *;interval.
 - apply (trig_operand_from_reference _ ch cl (cos(B th+B tl)-1) (/2^65));
     try assumption;set (t:=B th+B tl) in *;interval.
Qed.
