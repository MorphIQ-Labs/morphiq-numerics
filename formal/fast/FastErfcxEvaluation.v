(** IEEE transcription of the bounded paired high-word table polynomial. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Mul.
Require Import StageGappa ErfcxTableEntry ErfcxTableEvaluation.
Open Scope R_scope.

Definition fast_pair64 a b h := fadd a (fmul h b).
Definition fast_join64 a h2 b := fadd a (fmul h2 b).
Definition fast_table_polynomial64 i h :=
 let h2 := fmul h h in
 let p0 := fast_pair64 (coef i 0) (coef i 2) h in
 let p1 := fast_pair64 (coef i 4) (coef i 6) h in
 let p2 := fast_pair64 (coef i 7) (coef i 8) h in
 let p3 := fast_pair64 (coef i 9) (coef i 10) h in
 let p4 := fast_pair64 (coef i 11) (coef i 12) h in
 fast_join64 p0 h2 (fast_join64 p1 h2 (fast_join64 p2 h2 (fast_join64 p3 h2 p4))).
Definition fast_table_value i h :=
 let h2 := rn (h*h) in
 let p0 := rn (B (coef i 0)+rn (h*B (coef i 2))) in
 let p1 := rn (B (coef i 4)+rn (h*B (coef i 6))) in
 let p2 := rn (B (coef i 7)+rn (h*B (coef i 8))) in
 let p3 := rn (B (coef i 9)+rn (h*B (coef i 10))) in
 let p4 := rn (B (coef i 11)+rn (h*B (coef i 12))) in
 rn (p0+rn (h2*rn (p1+rn (h2*rn (p2+rn (h2*rn (p3+rn (h2*p4)))))))).

Lemma fast_pair_ieee a b h : bounded64 a 4 -> bounded64 b 4 ->
 bounded64 h (/8) -> bounded64 (fast_pair64 a b h) 5 /\
 B (fast_pair64 a b h)=rndF (B a+rndF (B h*B b)).
Proof.
 intros [Fa A] [Fb Bb] [Fh H].
 destruct (horner_step_ieee a h b Fa A Fh H Fb ltac:(lra)) as [F [C V]].
 split;[split;assumption|exact V].
Qed.
Lemma fast_join_ieee a h2 b : bounded64 a 5 -> bounded64 h2 (/64) ->
 bounded64 b 6 -> bounded64 (fast_join64 a h2 b) 6 /\
 B (fast_join64 a h2 b)=rndF (B a+rndF (B h2*B b)).
Proof.
 intros [Fa A] [Fh H] [Fb Bb].
 table_op fmul_bnd 3%Z (-5)%Z h2 b Fm Vm Cm.
 table_op fadd_bnd 6%Z 0%Z a (fmul h2 b) Fv Vv Cv.
 unfold fast_join64. split;[split;[exact Fv|lra]|]. rewrite Vv,Vm;reflexivity.
Qed.
Theorem fast_table_ieee i h : (i<177)%nat -> bounded64 h (/8) ->
 finite (fast_table_polynomial64 i h) /\
 B (fast_table_polynomial64 i h)=fast_table_value i (B h).
Proof.
 intros I H. destruct H as [Fh Hb].
 destruct (fmul_bnd 1 (-6) h h Fh Fh ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)
   ltac:(unfold bnd;bpow_num;cbn [IZR];rewrite Rabs_mult;pose proof(Rabs_pos(B h));nra)) as [Fh2 [Vh2 Ch2]].
 unfold bnd in Ch2;bpow_num_all;cbn [IZR] in Ch2.
 assert (H2 : bounded64 (fmul h h) (/64)) by (split;[exact Fh2|lra]).
 assert (Pair : forall a b, (a<13)%nat -> (b<13)%nat ->
   bounded64 (fast_pair64 (coef i a) (coef i b) h) 5 /\
   B (fast_pair64 (coef i a) (coef i b) h)=rndF (B (coef i a)+rndF (B h*B (coef i b)))).
 { intros a b A Bb. apply fast_pair_ieee;[apply coef_bound|apply coef_bound|split];assumption. }
 destruct (Pair 0%nat 2%nat ltac:(lia) ltac:(lia)) as [P0 V0].
 destruct (Pair 4%nat 6%nat ltac:(lia) ltac:(lia)) as [P1 V1].
 destruct (Pair 7%nat 8%nat ltac:(lia) ltac:(lia)) as [P2 V2].
 destruct (Pair 9%nat 10%nat ltac:(lia) ltac:(lia)) as [P3 V3].
 destruct (Pair 11%nat 12%nat ltac:(lia) ltac:(lia)) as [[F4 C4] V4].
 assert (P4 : bounded64 (fast_pair64 (coef i 11) (coef i 12) h) 6) by (split;[exact F4|lra]).
 destruct (fast_join_ieee _ _ _ P3 H2 P4) as [Y3 E3].
 destruct (fast_join_ieee _ _ _ P2 H2 Y3) as [Y2 E2].
 destruct (fast_join_ieee _ _ _ P1 H2 Y2) as [Y1 E1].
 destruct (fast_join_ieee _ _ _ P0 H2 Y1) as [[Fy Cy] Ey].
 unfold fast_table_polynomial64. split;[exact Fy|].
 rewrite Ey,E1,E2,E3,V0,V1,V2,V3,V4,Vh2. reflexivity.
Qed.
