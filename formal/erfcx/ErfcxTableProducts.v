(** Leading table products, exact by the checked coefficient and residual grids. *)
From Coq Require Import Reals ZArith Lia Lra Psatz List.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Mul Grid.
Require Import ErfcxTableSplit ErfcxTableCoefficient ErfcxTableData.
Open Scope R_scope.

Lemma small_grid_product a b qa qb ba bb : finite a -> finite b ->
 (-1074<=qa+qb)%Z -> (ba+bb<53)%Z -> on_grid qa (B a) -> on_grid qb (B b) ->
 Rabs (B a)<=bpow radix2 (qa+ba) -> Rabs (B b)<=bpow radix2 (qb+bb) ->
 Rabs (B a)<=4 -> Rabs (B b)<=1 ->
 finite (fmul a b) /\ B (fmul a b)=B a*B b.
Proof.
 intros Fa Fb Emin Bits Ga Gb A Bv A4 B1.
 pose proof (grid_product_format _ _ _ _ _ _ Emin Bits Ga Gb A Bv) as Fmt.
 destruct (fmul_ok 1 4 a b Fa Fb ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)
  ltac:(unfold bnd; rewrite Rmult_1_l; change (bpow radix2 4) with 16;
        rewrite Rabs_mult; pose proof (Rabs_pos (B a)); pose proof (Rabs_pos (B b)); nra)) as [F V].
 rewrite round_generic in V by (exact _ || exact Fmt). split;assumption.
Qed.

Definition leading64 b1 b2 h :=
 let '(a1,d1) := coefficient64 b1 18 in let '(a2,d2) := coefficient64 b2 36 in
 let p1 := fmul a1 h in let sq := fmul h h in let p2 := fmul a2 sq in
 (a1,d1,a2,d2,p1,sq,p2).

Theorem leading_ieee b1 b2 h e : coefficient_check b1 18 35=true ->
 coefficient_check b2 36 17=true -> finite h -> (0<=e<=3)%Z ->
 on_grid (e-23) (B h) -> Rabs (B h)<=bpow radix2 (e-6) ->
 let '(a1,d1,a2,d2,p1,sq,p2) := leading64 b1 b2 h in
 finite a1 /\ finite d1 /\ finite a2 /\ finite d2 /\ finite p1 /\ finite sq /\ finite p2 /\
 B d1=B (b64_of_bits b1)-B a1 /\ B d2=B (b64_of_bits b2)-B a2 /\
 B p1=B a1*B h /\ B sq=B h*B h /\ B p2=B a2*(B h*B h).
Proof.
 intros C1 C2 Fh E Gh H.
 pose proof (coefficient_check_ok b1 18 35 C1) as A1.
 pose proof (coefficient_check_ok b2 36 17 C2) as A2.
 unfold leading64. destruct (coefficient64 b1 18) as [a1 d1].
 destruct (coefficient64 b2 36) as [a2 d2].
 destruct A1 as [_ [Fa1 [Fd1 [D1 [_ [Ab1 [q1 [Q1 [G1 P1]]]]]]]]].
 destruct A2 as [_ [Fa2 [Fd2 [D2 [_ [Ab2 [q2 [Q2 [G2 P2]]]]]]]]].
 assert (H1 : Rabs (B h)<=1).
 { apply Rle_trans with (1:=H). change 1 with (bpow radix2 0). apply bpow_le;lia. }
 destruct (small_grid_product a1 h q1 (e-23) 35 17 Fa1 Fh ltac:(lia) ltac:(lia) G1 Gh P1
  ltac:(replace (e-23+17)%Z with (e-6)%Z by ring;exact H) Ab1 H1) as [Fp1 Bp1].
 destruct (table_square_ieee h e Fh E Gh H) as [Fs [Bs Gs]].
 assert (Sq : Rabs (B (fmul h h))<=bpow radix2 (2*(e-23)+34)).
 { rewrite Bs,Rabs_mult.
   apply Rle_trans with (bpow radix2 (e-6)*bpow radix2 (e-6)).
   - apply Rmult_le_compat;try apply Rabs_pos;exact H.
   - rewrite <-bpow_plus. apply bpow_le;lia. }
 assert (S1 : Rabs (B (fmul h h))<=1).
 { apply Rle_trans with (1:=Sq). change 1 with (bpow radix2 0). apply bpow_le;lia. }
 destruct (small_grid_product a2 (fmul h h) q2 (2*(e-23)) 17 34 Fa2 Fs
  ltac:(lia) ltac:(lia) G2 Gs P2 Sq Ab2 S1) as [Fp2 Bp2].
 rewrite Bs in Bp2. repeat split;assumption.
Qed.

Theorem table_leading_ieee i h e : (i<177)%nat -> finite h -> (0<=e<=3)%Z ->
 on_grid (e-23) (B h) -> Rabs (B h)<=bpow radix2 (e-6) ->
 let '(a1,d1,a2,d2,p1,sq,p2) := leading64 (table_word i 2) (table_word i 4) h in
 finite a1 /\ finite d1 /\ finite a2 /\ finite d2 /\ finite p1 /\ finite sq /\ finite p2 /\
 B d1=B (b64_of_bits (table_word i 2))-B a1 /\ B d2=B (b64_of_bits (table_word i 4))-B a2 /\
 B p1=B a1*B h /\ B sq=B h*B h /\ B p2=B a2*(B h*B h).
Proof.
 intros I Fh E Gh H. apply (leading_ieee (table_word i 2) (table_word i 4) h e);try assumption.
 - apply table_a1_check;exact I.
 - apply table_a2_check;exact I.
Qed.

Lemma coefficient_low_ieee b low shift precision : coefficient_check b shift precision=true ->
 low_word_check low=true ->
 let '(a,d) := coefficient64 b shift in
 finite (fadd d (b64_of_bits low)) /\
 B (fadd d (b64_of_bits low))=rndF (B (b64_of_bits b)-B a+B (b64_of_bits low)).
Proof.
 intros C L. pose proof (coefficient_check_ok b shift precision C) as A.
 destruct (coefficient64 b shift) as [a d].
 destruct A as [Ff [Fa [Fd [D [Full [Cut _]]]]]].
 destruct (low_word_check_ok low L) as [Fl Low].
 assert (Db : Rabs (B d)<=8).
 { rewrite D. apply Rle_trans with (Rabs (B (b64_of_bits b))+Rabs (B a));
   [unfold Rminus;rewrite <-(Rabs_Ropp (B a));apply Rabs_triang|lra]. }
 destruct (fadd_ok 1 4 d (b64_of_bits low) Fd Fl ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)
  ltac:(unfold bnd;rewrite Rmult_1_l;change (bpow radix2 4) with 16;
        apply Rle_trans with (Rabs (B d)+Rabs (B (b64_of_bits low)));[apply Rabs_triang|lra])) as [F V].
 rewrite D in V. split;assumption.
Qed.

Definition table_leading64 i h :=
 let '(a1,d1,a2,d2,p1,sq,p2) := leading64 (table_word i 2) (table_word i 4) h in
 (a1,fadd d1 (b64_of_bits (table_word i 3)),b64_of_bits (table_word i 4),
  fadd d2 (b64_of_bits (table_word i 5)),p1,sq,p2).

Theorem table_leading_value_ieee i h e : (i<177)%nat -> finite h -> (0<=e<=3)%Z ->
 on_grid (e-23) (B h) -> Rabs (B h)<=bpow radix2 (e-6) ->
 let '(a1,b1,a2h,b2,p1,sq,p2) := table_leading64 i h in
 finite a1 /\ finite b1 /\ finite a2h /\ finite b2 /\ finite p1 /\ finite sq /\ finite p2 /\
 B b1=rndF (B (b64_of_bits (table_word i 2))-B a1+B (b64_of_bits (table_word i 3))) /\
 B b2=rndF (B a2h-B (b64_of_bits (truncated_bits (table_word i 4) 36))+B (b64_of_bits (table_word i 5))) /\
 B p1=B a1*B h /\ B sq=B h*B h /\ B p2=B (b64_of_bits (truncated_bits (table_word i 4) 36))*(B h*B h).
Proof.
 intros I Fh E Gh H.
 pose proof (table_leading_ieee i h e I Fh E Gh H) as Core.
 destruct (table_low_check i I) as [Lo1 Lo2].
 pose proof (coefficient_low_ieee (table_word i 2) (table_word i 3) 18 35 (table_a1_check i I) Lo1) as L1.
 pose proof (coefficient_low_ieee (table_word i 4) (table_word i 5) 36 17 (table_a2_check i I) Lo2) as L2.
 pose proof (coefficient_check_ok (table_word i 4) 36 17 (table_a2_check i I)) as A2.
 unfold table_leading64,leading64,coefficient64 in *;cbv zeta in *.
 repeat split;tauto.
Qed.
