Require Import Gappa.Gappa_library.
Section Generated_by_Gappa.
Variable _eA : R.
Definition f1 := Float2 (-1) (-123).
Definition f2 := Float2 (1) (-123).
Definition i1 := makepairF f1 f2.
Notation p1 := (BND _eA i1). (* BND(eA, [-9.40395e-38, 9.40395e-38]) *)
Variable _eC : R.
Definition f3 := Float2 (-293) (-138).
Definition f4 := Float2 (293) (-138).
Definition i2 := makepairF f3 f4.
Notation p2 := (BND _eC i2). (* BND(eC, [-8.40869e-40, 8.40869e-40]) *)
Definition s3 := (p1 /\ p2).
Variable _m : R.
Definition f5 := Float2 (-1) (-127).
Definition f6 := Float2 (0) (0).
Definition i3 := makepairF f5 f6.
Notation p3 := (BND _m i3). (* BND(m, [-5.87747e-39, 0]) *)
Definition s2 := (s3 /\ p3).
Notation r8 := (Float1 (1)).
Notation r7 := ((r8 + _eA)%R).
Notation r9 := ((r8 + _eC)%R).
Notation r6 := ((r7 * r9)%R).
Notation r10 := ((r8 + _m)%R).
Notation _Y := ((r6 * r10)%R).
Notation r4 := ((_Y - r8)%R).
Definition f7 := Float2 (-1) (-122).
Definition f8 := Float2 (1) (-122).
Definition i4 := makepairF f7 f8.
Notation p4 := (BND r4 i4). (* BND(Y - 1, [-1.88079e-37, 1.88079e-37]) *)
Definition s4 := (not p4).
Definition s1 := (s2 /\ s4).
Lemma l2 : s1 -> s4.
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj2 h1).
Qed.
Definition f9 := Float2 (-63521007203639598517596151760469121199918207085752774230418100950342788001562917) (-388).
Definition f10 := Float2 (351564854149160829392582121759427776217381) (-261).
Definition i5 := makepairF f9 f10.
Notation p5 := (BND r4 i5). (* BND(Y - 1, [-1.00758e-37, 9.48804e-38]) *)
Definition f11 := Float2 (630432099142311667396464641602297820817754821123807548169576542707462427144037162696875485847740549302563259843346139) (-388).
Definition f12 := Float2 (3705346855594118253554271520278013051656204363449658878655224810012647924695333) (-261).
Definition i6 := makepairF f11 f12.
Notation p6 := (BND _Y i6). (* BND(Y, [1, 1]) *)
Definition f13 := Float2 (3705346855594118253554271520278013050953074655151337219870060566493792372261157) (-261).
Definition i7 := makepairF f13 f12.
Notation p7 := (BND r6 i7). (* BND((1 + eA) * (1 + eC), [1, 1]) *)
Definition f14 := Float2 (10633823966279326983230456482242756607) (-123).
Definition f15 := Float2 (10633823966279326983230456482242756609) (-123).
Definition i8 := makepairF f14 f15.
Notation p8 := (BND r7 i8). (* BND(1 + eA, [1, 1]) *)
Definition f16 := Float2 (1) (0).
Definition i9 := makepairF f16 f16.
Notation p9 := (BND r8 i9). (* BND(1, [1, 1]) *)
Lemma t1 : p9.
Proof.
 refine (constant1 _ i9 _) ; finalize.
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
Lemma l8 : s1 -> p1 (* BND(eA, [-9.40395e-38, 9.40395e-38]) *).
Proof.
 intros h0.
 assert (h1 := l9 h0).
 exact (proj1 h1).
Qed.
Lemma t2 : p9 -> p1 -> p8.
Proof.
 intros h0 h1.
 refine (add r8 _eA i9 i1 i8 h0 h1 _) ; finalize.
Qed.
Lemma l6 : s1 -> p8 (* BND(1 + eA, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 assert (h2 := l8 h0).
 apply t2. exact h1. exact h2.
Qed.
Definition f17 := Float2 (348449143727040986586495598010130648530651) (-138).
Definition f18 := Float2 (348449143727040986586495598010130648531237) (-138).
Definition i10 := makepairF f17 f18.
Notation p10 := (BND r9 i10). (* BND(1 + eC, [1, 1]) *)
Lemma l12 : s1 -> p2 (* BND(eC, [-8.40869e-40, 8.40869e-40]) *).
Proof.
 intros h0.
 assert (h1 := l9 h0).
 exact (proj2 h1).
Qed.
Lemma t3 : p9 -> p2 -> p10.
Proof.
 intros h0 h1.
 refine (add r8 _eC i9 i2 i10 h0 h1 _) ; finalize.
Qed.
Lemma l11 : s1 -> p10 (* BND(1 + eC, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 assert (h2 := l12 h0).
 apply t3. exact h1. exact h2.
Qed.
Lemma t4 : p8 -> p10 -> p7.
Proof.
 intros h0 h1.
 refine (mul_pp r7 r9 i8 i10 i7 h0 h1 _) ; finalize.
Qed.
Lemma l5 : s1 -> p7 (* BND((1 + eA) * (1 + eC), [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l6 h0).
 assert (h2 := l11 h0).
 apply t4. exact h1. exact h2.
Qed.
Definition f19 := Float2 (170141183460469231731687303715884105727) (-127).
Definition i11 := makepairF f19 f16.
Notation p11 := (BND r10 i11). (* BND(1 + m, [1, 1]) *)
Lemma l14 : s1 -> p3 (* BND(m, [-5.87747e-39, 0]) *).
Proof.
 intros h0.
 assert (h1 := l10 h0).
 exact (proj2 h1).
Qed.
Lemma t5 : p9 -> p3 -> p11.
Proof.
 intros h0 h1.
 refine (add r8 _m i9 i3 i11 h0 h1 _) ; finalize.
Qed.
Lemma l13 : s1 -> p11 (* BND(1 + m, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 assert (h2 := l14 h0).
 apply t5. exact h1. exact h2.
Qed.
Lemma t6 : p7 -> p11 -> p6.
Proof.
 intros h0 h1.
 refine (mul_pp r6 r10 i7 i11 i6 h0 h1 _) ; finalize.
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
 refine (sub _Y r8 i6 i9 i5 h0 h1 _) ; finalize.
Qed.
Lemma l3 : s1 -> p5 (* BND(Y - 1, [-1.00758e-37, 9.48804e-38]) *).
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
 refine (simplify (Tatom false (Abnd 0%nat i4)) Tfalse (Abnd 0%nat i5) (List.cons r4 List.nil) h2 h1 _) ; finalize.
Qed.
End Generated_by_Gappa.
