Require Import Gappa.Gappa_library.
Section Generated_by_Gappa.
Variable _dP : R.
Definition f1 := Float2 (-3) (-66).
Definition f2 := Float2 (3) (-66).
Definition i1 := makepairF f1 f2.
Notation p1 := (BND _dP i1). (* BND(dP, [-4.06576e-20, 4.06576e-20]) *)
Variable _e1 : R.
Definition f3 := Float2 (-97) (-111).
Definition f4 := Float2 (97) (-111).
Definition i2 := makepairF f3 f4.
Notation p2 := (BND _e1 i2). (* BND(e1, [-3.7363e-32, 3.7363e-32]) *)
Definition s3 := (p1 /\ p2).
Variable _e2 : R.
Notation p3 := (BND _e2 i2). (* BND(e2, [-3.7363e-32, 3.7363e-32]) *)
Definition s2 := (s3 /\ p3).
Notation r8 := (Float1 (1)).
Notation r7 := ((r8 + _dP)%R).
Notation r9 := ((r8 + _e1)%R).
Notation r6 := ((r7 * r9)%R).
Notation r10 := ((r8 + _e2)%R).
Notation _Y := ((r6 * r10)%R).
Notation r4 := ((_Y - r8)%R).
Definition f5 := Float2 (-1) (-64).
Definition f6 := Float2 (1) (-64).
Definition i3 := makepairF f5 f6.
Notation p4 := (BND r4 i3). (* BND(Y - 1, [-5.42101e-20, 5.42101e-20]) *)
Definition s4 := (not p4).
Definition s1 := (s2 /\ s4).
Lemma l2 : s1 -> s4.
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj2 h1).
Qed.
Definition f7 := Float2 (-20219960000400142862866259120078401962250418985506621451976172400195) (-288).
Definition f8 := Float2 (20219960000400142862866259120081423879022087643709746117105147735619) (-288).
Definition i4 := makepairF f7 f8.
Notation p5 := (BND r4 i4). (* BND(Y - 1, [-4.06576e-20, 4.06576e-20]) *)
Definition f9 := Float2 (497323236409786642135162288146420697237589891677269315478213557907652875560557203132861) (-288).
Definition f10 := Float2 (497323236409786642175602208147220982963322409917429141319486064536869243129638523268675) (-288).
Definition i5 := makepairF f9 f10.
Notation p6 := (BND _Y i5). (* BND(Y, [1, 1]) *)
Definition f11 := Float2 (191561942608236107287004933105979249172846046473093411) (-177).
Definition f12 := Float2 (191561942608236107302581823681598046731838734072807715) (-177).
Definition i6 := makepairF f11 f12.
Notation p7 := (BND r6 i6). (* BND((1 + dP) * (1 + e1), [1, 1]) *)
Definition f13 := Float2 (73786976294838206461) (-66).
Definition f14 := Float2 (73786976294838206467) (-66).
Definition i7 := makepairF f13 f14.
Notation p8 := (BND r7 i7). (* BND(1 + dP, [1, 1]) *)
Definition f15 := Float2 (1) (0).
Definition i8 := makepairF f15 f15.
Notation p9 := (BND r8 i8). (* BND(1, [1, 1]) *)
Lemma t1 : p9.
Proof.
 refine (constant1 _ i8 _) ; finalize.
Qed.
Lemma l7 : s1 -> p9 (* BND(1, [1, 1]) *).
Proof.
 intros h0.
 apply t1.
Qed.
Lemma l10 : s1 -> s2.
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj1 h1).
Qed.
Lemma l9 : s1 -> s3.
Proof.
 intros h0.
 assert (h1 := l10 h0).
 exact (proj1 h1).
Qed.
Lemma l8 : s1 -> p1 (* BND(dP, [-4.06576e-20, 4.06576e-20]) *).
Proof.
 intros h0.
 assert (h1 := l9 h0).
 exact (proj1 h1).
Qed.
Lemma t2 : p9 -> p1 -> p8.
Proof.
 intros h0 h1.
 refine (add r8 _dP i8 i1 i7 h0 h1 _) ; finalize.
Qed.
Lemma l6 : s1 -> p8 (* BND(1 + dP, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 assert (h2 := l8 h0).
 apply t2. exact h1. exact h2.
Qed.
Definition f16 := Float2 (2596148429267413814265248164609951) (-111).
Definition f17 := Float2 (2596148429267413814265248164610145) (-111).
Definition i9 := makepairF f16 f17.
Notation p10 := (BND r9 i9). (* BND(1 + e1, [1, 1]) *)
Lemma l12 : s1 -> p2 (* BND(e1, [-3.7363e-32, 3.7363e-32]) *).
Proof.
 intros h0.
 assert (h1 := l9 h0).
 exact (proj2 h1).
Qed.
Lemma t3 : p9 -> p2 -> p10.
Proof.
 intros h0 h1.
 refine (add r8 _e1 i8 i2 i9 h0 h1 _) ; finalize.
Qed.
Lemma l11 : s1 -> p10 (* BND(1 + e1, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 assert (h2 := l12 h0).
 apply t3. exact h1. exact h2.
Qed.
Lemma t4 : p8 -> p10 -> p7.
Proof.
 intros h0 h1.
 refine (mul_pp r7 r9 i7 i9 i6 h0 h1 _) ; finalize.
Qed.
Lemma l5 : s1 -> p7 (* BND((1 + dP) * (1 + e1), [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l6 h0).
 assert (h2 := l11 h0).
 apply t4. exact h1. exact h2.
Qed.
Notation p11 := (BND r10 i9). (* BND(1 + e2, [1, 1]) *)
Lemma l14 : s1 -> p3 (* BND(e2, [-3.7363e-32, 3.7363e-32]) *).
Proof.
 intros h0.
 assert (h1 := l10 h0).
 exact (proj2 h1).
Qed.
Lemma t5 : p9 -> p3 -> p11.
Proof.
 intros h0 h1.
 refine (add r8 _e2 i8 i2 i9 h0 h1 _) ; finalize.
Qed.
Lemma l13 : s1 -> p11 (* BND(1 + e2, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 assert (h2 := l14 h0).
 apply t5. exact h1. exact h2.
Qed.
Lemma t6 : p7 -> p11 -> p6.
Proof.
 intros h0 h1.
 refine (mul_pp r6 r10 i6 i9 i5 h0 h1 _) ; finalize.
Qed.
Lemma l4 : s1 -> p6 (* BND(Y, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l5 h0).
 assert (h2 := l13 h0).
 apply t6. exact h1. exact h2.
Qed.
Lemma t7 : p6 -> p9 -> p5.
Proof.
 intros h0 h1.
 refine (sub _Y r8 i5 i8 i4 h0 h1 _) ; finalize.
Qed.
Lemma l3 : s1 -> p5 (* BND(Y - 1, [-4.06576e-20, 4.06576e-20]) *).
Proof.
 intros h0.
 assert (h1 := l4 h0).
 assert (h2 := l7 h0).
 apply t7. exact h1. exact h2.
Qed.
Lemma l1 : s1 -> False.
Proof.
 intros h0.
 assert (h1 := l2 h0).
 assert (h2 := l3 h0).
 refine (simplify (Tatom false (Abnd 0%nat i3)) Tfalse (Abnd 0%nat i4) (List.cons r4 List.nil) h2 h1 _) ; finalize.
Qed.
End Generated_by_Gappa.
