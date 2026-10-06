Require Import Gappa.Gappa_library.
Section Generated_by_Gappa.
Variable _kq : R.
Definition f1 := Float2 (-263) (-3).
Definition f2 := Float2 (263) (-3).
Definition i1 := makepairF f1 f2.
Notation p1 := (BND _kq i1). (* BND(kq, [-32.875, 32.875]) *)
Variable _eV : R.
Definition f3 := Float2 (-1097) (-134).
Definition f4 := Float2 (1097) (-134).
Definition i2 := makepairF f3 f4.
Notation p2 := (BND _eV i2). (* BND(eV, [-5.03718e-38, 5.03718e-38]) *)
Definition s3 := (p1 /\ p2).
Variable _sr : R.
Definition f5 := Float2 (-271) (-129).
Definition f6 := Float2 (271) (-129).
Definition i3 := makepairF f5 f6.
Notation p3 := (BND _sr i3). (* BND(sr, [-3.98199e-37, 3.98199e-37]) *)
Definition s2 := (s3 /\ p3).
Notation r7 := (Float1 (1)).
Notation r8 := ((_kq * _eV)%R).
Notation r6 := ((r7 + r8)%R).
Notation _M := ((r6 + _sr)%R).
Notation r4 := ((_M - r7)%R).
Definition f7 := Float2 (-1) (-118).
Definition f8 := Float2 (1) (-118).
Definition i4 := makepairF f7 f8.
Notation p4 := (BND r4 i4). (* BND(M - 1, [-3.00927e-36, 3.00927e-36]) *)
Definition s4 := (not p4).
Definition s1 := (s2 /\ s4).
Lemma l2 : s1 -> s4.
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj2 h1).
Qed.
Definition f9 := Float2 (-357887) (-137).
Definition f10 := Float2 (357887) (-137).
Definition i5 := makepairF f9 f10.
Notation p5 := (BND r4 i5). (* BND(M - 1, [-2.05417e-36, 2.05417e-36]) *)
Definition f11 := Float2 (174224571863520493293247799005065323907585) (-137).
Definition f12 := Float2 (174224571863520493293247799005065324623359) (-137).
Definition i6 := makepairF f11 f12.
Notation p6 := (BND _M i6). (* BND(M, [1, 1]) *)
Definition f13 := Float2 (174224571863520493293247799005065323976961) (-137).
Definition f14 := Float2 (174224571863520493293247799005065324553983) (-137).
Definition i7 := makepairF f13 f14.
Notation p7 := (BND r6 i7). (* BND(1 + kq * eV, [1, 1]) *)
Definition f15 := Float2 (1) (0).
Definition i8 := makepairF f15 f15.
Notation p8 := (BND r7 i8). (* BND(1, [1, 1]) *)
Lemma t1 : p8.
Proof.
 refine (constant1 _ i8 _) ; finalize.
Qed.
Lemma l6 : s1 -> p8 (* BND(1, [1, 1]) *).
Proof.
 intros h0.
 apply t1.
Qed.
Definition f16 := Float2 (-288511) (-137).
Definition f17 := Float2 (288511) (-137).
Definition i9 := makepairF f16 f17.
Notation p9 := (BND r8 i9). (* BND(kq * eV, [-1.65597e-36, 1.65597e-36]) *)
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
Lemma l8 : s1 -> p1 (* BND(kq, [-32.875, 32.875]) *).
Proof.
 intros h0.
 assert (h1 := l9 h0).
 exact (proj1 h1).
Qed.
Lemma l11 : s1 -> p2 (* BND(eV, [-5.03718e-38, 5.03718e-38]) *).
Proof.
 intros h0.
 assert (h1 := l9 h0).
 exact (proj2 h1).
Qed.
Lemma t2 : p1 -> p2 -> p9.
Proof.
 intros h0 h1.
 refine (mul_oo _kq _eV i1 i2 i9 h0 h1 _) ; finalize.
Qed.
Lemma l7 : s1 -> p9 (* BND(kq * eV, [-1.65597e-36, 1.65597e-36]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 assert (h2 := l11 h0).
 apply t2. exact h1. exact h2.
Qed.
Lemma t3 : p8 -> p9 -> p7.
Proof.
 intros h0 h1.
 refine (add r7 r8 i8 i9 i7 h0 h1 _) ; finalize.
Qed.
Lemma l5 : s1 -> p7 (* BND(1 + kq * eV, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l6 h0).
 assert (h2 := l7 h0).
 apply t3. exact h1. exact h2.
Qed.
Lemma l12 : s1 -> p3 (* BND(sr, [-3.98199e-37, 3.98199e-37]) *).
Proof.
 intros h0.
 assert (h1 := l10 h0).
 exact (proj2 h1).
Qed.
Lemma t4 : p7 -> p3 -> p6.
Proof.
 intros h0 h1.
 refine (add r6 _sr i7 i3 i6 h0 h1 _) ; finalize.
Qed.
Lemma l4 : s1 -> p6 (* BND(M, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l5 h0).
 assert (h2 := l12 h0).
 apply t4. exact h1. exact h2.
Qed.
Lemma t5 : p6 -> p8 -> p5.
Proof.
 intros h0 h1.
 refine (sub _M r7 i6 i8 i5 h0 h1 _) ; finalize.
Qed.
Lemma l3 : s1 -> p5 (* BND(M - 1, [-2.05417e-36, 2.05417e-36]) *).
Proof.
 intros h0.
 assert (h1 := l4 h0).
 assert (h2 := l6 h0).
 apply t5. exact h1. exact h2.
Qed.
Lemma l1 : s1 -> False.
Proof.
 intros h0.
 assert (h1 := l2 h0).
 assert (h2 := l3 h0).
 refine (simplify (Tatom false (Abnd 0%nat i4)) Tfalse (Abnd 0%nat i5) (List.cons r4 List.nil) h2 h1 _) ; finalize.
Qed.
End Generated_by_Gappa.
