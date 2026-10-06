Require Import Gappa.Gappa_library.
Section Generated_by_Gappa.
Variable _d1 : R.
Definition f1 := Float2 (-1) (-53).
Definition f2 := Float2 (1) (-53).
Definition i1 := makepairF f1 f2.
Notation p1 := (BND _d1 i1). (* BND(d1, [-1.11022e-16, 1.11022e-16]) *)
Variable _d2 : R.
Notation p2 := (BND _d2 i1). (* BND(d2, [-1.11022e-16, 1.11022e-16]) *)
Definition s2 := (p1 /\ p2).
Notation r6 := (Float1 (1)).
Notation r5 := ((r6 + _d2)%R).
Notation r7 := ((r6 + _d1)%R).
Notation r4 := ((r5 / r7)%R).
Notation _E := ((r4 - r6)%R).
Definition f3 := Float2 (-259) (-60).
Definition f4 := Float2 (259) (-60).
Definition i2 := makepairF f3 f4.
Notation p3 := (BND _E i2). (* BND(E, [-2.24647e-16, 2.24647e-16]) *)
Definition s3 := (not p3).
Definition s1 := (s2 /\ s3).
Lemma l2 : s1 -> s3.
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj2 h1).
Qed.
Definition f5 := Float2 (-533996758980227461313205737036502553800561090964392240670593031171633870184588190952433324654593) (-370).
Definition f6 := Float2 (286687326998758970780039742139109499238164061811620392349855409381946810473379480718897996578366899093505) (-399).
Definition i3 := makepairF f5 f6.
Notation p4 := (BND _E i3). (* BND(E, [-2.22045e-16, 2.22045e-16]) *)
Definition f7 := Float2 (2404907604760404691362069150884819802826961893579565747043174990456741371124327874472957589757812199471376760831) (-370).
Definition f8 := Float2 (1291124939043454581515286584760476717204595035524110994579391489890716160863829979261633150019549634615948164353272840193) (-399).
Definition i4 := makepairF f7 f8.
Notation p5 := (BND r4 i4). (* BND((1 + d2) / (1 + d1), [1, 1]) *)
Definition f9 := Float2 (9007199254740991) (-53).
Definition f10 := Float2 (9007199254740993) (-53).
Definition i5 := makepairF f9 f10.
Notation p6 := (BND r5 i5). (* BND(1 + d2, [1, 1]) *)
Definition f11 := Float2 (1) (0).
Definition i6 := makepairF f11 f11.
Notation p7 := (BND r6 i6). (* BND(1, [1, 1]) *)
Lemma t1 : p7.
Proof.
 refine (constant1 _ i6 _) ; finalize.
Qed.
Lemma l6 : s1 -> p7 (* BND(1, [1, 1]) *).
Proof.
 intros h0.
 apply t1.
Qed.
Lemma l8 : s1 -> s2.
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj1 h1).
Qed.
Lemma l7 : s1 -> p2 (* BND(d2, [-1.11022e-16, 1.11022e-16]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 exact (proj2 h1).
Qed.
Lemma t2 : p7 -> p2 -> p6.
Proof.
 intros h0 h1.
 refine (add r6 _d2 i6 i1 i5 h0 h1 _) ; finalize.
Qed.
Lemma l5 : s1 -> p6 (* BND(1 + d2, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l6 h0).
 assert (h2 := l7 h0).
 apply t2. exact h1. exact h2.
Qed.
Notation p8 := (BND r7 i5). (* BND(1 + d1, [1, 1]) *)
Lemma l10 : s1 -> p1 (* BND(d1, [-1.11022e-16, 1.11022e-16]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 exact (proj1 h1).
Qed.
Lemma t3 : p7 -> p1 -> p8.
Proof.
 intros h0 h1.
 refine (add r6 _d1 i6 i1 i5 h0 h1 _) ; finalize.
Qed.
Lemma l9 : s1 -> p8 (* BND(1 + d1, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l6 h0).
 assert (h2 := l10 h0).
 apply t3. exact h1. exact h2.
Qed.
Lemma t4 : p6 -> p8 -> p5.
Proof.
 intros h0 h1.
 refine (div_pp r5 r7 i5 i5 i4 h0 h1 _) ; finalize.
Qed.
Lemma l4 : s1 -> p5 (* BND((1 + d2) / (1 + d1), [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l5 h0).
 assert (h2 := l9 h0).
 apply t4. exact h1. exact h2.
Qed.
Lemma t5 : p5 -> p7 -> p4.
Proof.
 intros h0 h1.
 refine (sub r4 r6 i4 i6 i3 h0 h1 _) ; finalize.
Qed.
Lemma l3 : s1 -> p4 (* BND(E, [-2.22045e-16, 2.22045e-16]) *).
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
 refine (simplify (Tatom false (Abnd 0%nat i2)) Tfalse (Abnd 0%nat i3) (List.cons _E List.nil) h2 h1 _) ; finalize.
Qed.
End Generated_by_Gappa.
