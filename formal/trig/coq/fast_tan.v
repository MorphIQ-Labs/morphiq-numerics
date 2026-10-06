Require Import Gappa.Gappa_library.
Section Generated_by_Gappa.
Variable _eN : R.
Definition f1 := Float2 (-1) (-62).
Definition f2 := Float2 (1) (-62).
Definition i1 := makepairF f1 f2.
Notation p1 := (BND _eN i1). (* BND(eN, [-2.1684e-19, 2.1684e-19]) *)
Variable _eD : R.
Notation p2 := (BND _eD i1). (* BND(eD, [-2.1684e-19, 2.1684e-19]) *)
Definition s3 := (p1 /\ p2).
Variable _ed : R.
Definition f3 := Float2 (-485) (-111).
Definition f4 := Float2 (485) (-111).
Definition i2 := makepairF f3 f4.
Notation p3 := (BND _ed i2). (* BND(ed, [-1.86815e-31, 1.86815e-31]) *)
Definition s2 := (s3 /\ p3).
Notation r8 := (Float1 (1)).
Notation r7 := ((r8 + _eN)%R).
Notation r9 := ((r8 + _eD)%R).
Notation r6 := ((r7 / r9)%R).
Notation r10 := ((r8 + _ed)%R).
Notation _Q := ((r6 * r10)%R).
Notation r4 := ((_Q - r8)%R).
Definition f5 := Float2 (-1) (-60).
Definition f6 := Float2 (1) (-60).
Definition i3 := makepairF f5 f6.
Notation p4 := (BND r4 i3). (* BND(Q - 1, [-8.67362e-19, 8.67362e-19]) *)
Definition s4 := (not p4).
Definition s1 := (s2 /\ s4).
Lemma l2 : s1 -> s4.
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj2 h1).
Qed.
Definition f7 := Float2 (-1119872371089384508575205021798687516843111483348799688897255634079027063772478253730750498211058679809) (-400).
Definition f8 := Float2 (279968092772346127265218061213884550736312784496073161913710962898357956150279325870471612140093440001) (-398).
Definition i4 := makepairF f7 f8.
Notation p5 := (BND r4 i4). (* BND(Q - 1, [-4.33681e-19, 4.33681e-19]) *)
Definition f9 := Float2 (2582249878086908588536046800913627365754500771030535995987547873191847933119585560550618289507659577705152673761688813567) (-400).
Definition f10 := Float2 (645562469521727147693947885773099095847644509421190428943977623631235067417921261555769294470313783729447405133280313345) (-398).
Definition i5 := makepairF f9 f10.
Notation p6 := (BND _Q i5). (* BND(Q, [1, 1]) *)
Definition f11 := Float2 (2582249878086908588536046800914109769293818264073217507582113200441984124559606466729079320733076769939578105902240104447) (-400).
Definition f12 := Float2 (1291124939043454295387895771545956989925630272320830892904535494672595423078756797688270812118542285439073115763877347329) (-399).
Definition i6 := makepairF f11 f12.
Notation p7 := (BND r6 i6). (* BND((1 + eN) / (1 + eD), [1, 1]) *)
Definition f13 := Float2 (4611686018427387903) (-62).
Definition f14 := Float2 (4611686018427387905) (-62).
Definition i7 := makepairF f13 f14.
Notation p8 := (BND r7 i7). (* BND(1 + eN, [1, 1]) *)
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
Lemma l8 : s1 -> p1 (* BND(eN, [-2.1684e-19, 2.1684e-19]) *).
Proof.
 intros h0.
 assert (h1 := l9 h0).
 exact (proj1 h1).
Qed.
Lemma t2 : p9 -> p1 -> p8.
Proof.
 intros h0 h1.
 refine (add r8 _eN i8 i1 i7 h0 h1 _) ; finalize.
Qed.
Lemma l6 : s1 -> p8 (* BND(1 + eN, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 assert (h2 := l8 h0).
 apply t2. exact h1. exact h2.
Qed.
Notation p10 := (BND r9 i7). (* BND(1 + eD, [1, 1]) *)
Lemma l12 : s1 -> p2 (* BND(eD, [-2.1684e-19, 2.1684e-19]) *).
Proof.
 intros h0.
 assert (h1 := l9 h0).
 exact (proj2 h1).
Qed.
Lemma t3 : p9 -> p2 -> p10.
Proof.
 intros h0 h1.
 refine (add r8 _eD i8 i1 i7 h0 h1 _) ; finalize.
Qed.
Lemma l11 : s1 -> p10 (* BND(1 + eD, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 assert (h2 := l12 h0).
 apply t3. exact h1. exact h2.
Qed.
Lemma t4 : p8 -> p10 -> p7.
Proof.
 intros h0 h1.
 refine (div_pp r7 r9 i7 i7 i6 h0 h1 _) ; finalize.
Qed.
Lemma l5 : s1 -> p7 (* BND((1 + eN) / (1 + eD), [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l6 h0).
 assert (h2 := l11 h0).
 apply t4. exact h1. exact h2.
Qed.
Definition f16 := Float2 (2596148429267413814265248164609563) (-111).
Definition f17 := Float2 (2596148429267413814265248164610533) (-111).
Definition i9 := makepairF f16 f17.
Notation p11 := (BND r10 i9). (* BND(1 + ed, [1, 1]) *)
Lemma l14 : s1 -> p3 (* BND(ed, [-1.86815e-31, 1.86815e-31]) *).
Proof.
 intros h0.
 assert (h1 := l10 h0).
 exact (proj2 h1).
Qed.
Lemma t5 : p9 -> p3 -> p11.
Proof.
 intros h0 h1.
 refine (add r8 _ed i8 i2 i9 h0 h1 _) ; finalize.
Qed.
Lemma l13 : s1 -> p11 (* BND(1 + ed, [1, 1]) *).
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
Lemma l4 : s1 -> p6 (* BND(Q, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l5 h0).
 assert (h2 := l13 h0).
 apply t6. exact h1. exact h2.
Qed.
Lemma t7 : p6 -> p9 -> p5.
Proof.
 intros h0 h1.
 refine (sub _Q r8 i5 i8 i4 h0 h1 _) ; finalize.
Qed.
Lemma l3 : s1 -> p5 (* BND(Q - 1, [-4.33681e-19, 4.33681e-19]) *).
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
