Require Import Gappa.Gappa_library.
Section Generated_by_Gappa.
Variable _eN : R.
Definition f1 := Float2 (-1) (-198).
Definition f2 := Float2 (1) (-198).
Definition i1 := makepairF f1 f2.
Notation p1 := (BND _eN i1). (* BND(eN, [-2.48921e-60, 2.48921e-60]) *)
Variable _eD : R.
Notation p2 := (BND _eD i1). (* BND(eD, [-2.48921e-60, 2.48921e-60]) *)
Definition s4 := (p1 /\ p2).
Variable _er : R.
Definition f3 := Float2 (-657) (-262).
Definition f4 := Float2 (657) (-262).
Definition i2 := makepairF f3 f4.
Notation p3 := (BND _er i2). (* BND(er, [-8.86557e-77, 8.86557e-77]) *)
Definition s3 := (s4 /\ p3).
Variable _m : R.
Definition f5 := Float2 (-1) (-255).
Definition f6 := Float2 (0) (0).
Definition i3 := makepairF f5 f6.
Notation p4 := (BND _m i3). (* BND(m, [-1.72723e-77, 0]) *)
Definition s2 := (s3 /\ p4).
Notation r10 := (Float1 (1)).
Notation r9 := ((r10 + _eN)%R).
Notation r11 := ((r10 + _eD)%R).
Notation r8 := ((r9 / r11)%R).
Notation r12 := ((r10 + _er)%R).
Notation r7 := ((r8 * r12)%R).
Notation r13 := ((r10 + _m)%R).
Notation _Q := ((r7 * r13)%R).
Notation r5 := ((_Q - r10)%R).
Definition f7 := Float2 (-1) (-196).
Definition f8 := Float2 (1) (-196).
Definition i4 := makepairF f7 f8.
Notation p5 := (BND r5 i4). (* BND(Q - 1, [-9.95682e-60, 9.95682e-60]) *)
Definition s5 := (not p5).
Definition s1 := (s2 /\ s5).
Lemma l2 : s1 -> s5.
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj2 h1).
Qed.
Definition f9 := Float2 (-12855504354071922477868274564456475290576668388214901779202017) (-400).
Definition f10 := Float2 (3213876088517980608316696041848807251876307960729544691810313) (-398).
Definition i5 := makepairF f9 f10.
Notation p6 := (BND r5 i5). (* BND(Q - 1, [-4.97841e-60, 4.97841e-60]) *)
Definition f11 := Float2 (2582249878086908589655919172003011874329705792829223512830646501036293550094363326355080896804847254767514957070968291359) (-400).
Definition f12 := Float2 (645562469521727147413979793000752968582426448207305878207668053011250423484818615353453187127286334166936522537878683657) (-398).
Definition i6 := makepairF f11 f12.
Notation p7 := (BND _Q i6). (* BND(Q, [1, 1]) *)
Definition f13 := Float2 (2582249878086908589655919172003011874329705792829223512830646501036293550094407927845477958051130326204060253793980252191) (-400).
Definition i7 := makepairF f13 f12.
Notation p8 := (BND r7 i7). (* BND((1 + eN) / (1 + eD) * (1 + er), [1, 1]) *)
Definition f14 := Float2 (2582249878086908589655919172003011874329705792829223512830646501036293550094636858932906623979317653811952909630065082399) (-400).
Definition f15 := Float2 (1291124939043454294827959586001505937164852896414611756415336106022500846969522765163192041290479004529926717157714952209) (-399).
Definition i8 := makepairF f14 f15.
Notation p9 := (BND r8 i8). (* BND((1 + eN) / (1 + eD), [1, 1]) *)
Definition f16 := Float2 (401734511064747568885490523085290650630550748445698208825343) (-198).
Definition f17 := Float2 (401734511064747568885490523085290650630550748445698208825345) (-198).
Definition i9 := makepairF f16 f17.
Notation p10 := (BND r9 i9). (* BND(1 + eN, [1, 1]) *)
Definition f18 := Float2 (1) (0).
Definition i10 := makepairF f18 f18.
Notation p11 := (BND r10 i10). (* BND(1, [1, 1]) *)
Lemma t1 : p11.
Proof.
 refine (constant1 _ i10 _) ; finalize.
Qed.
Lemma l8 : s1 -> p11 (* BND(1, [1, 1]) *).
Proof.
 intros h0.
 apply t1.
Qed.
Lemma l12 : s1 -> s2.
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj1 h1).
Qed.
Lemma l11 : s1 -> s3.
Proof.
 intros h0.
 assert (h1 := l12 h0).
 exact (proj1 h1).
Qed.
Lemma l10 : s1 -> s4.
Proof.
 intros h0.
 assert (h1 := l11 h0).
 exact (proj1 h1).
Qed.
Lemma l9 : s1 -> p1 (* BND(eN, [-2.48921e-60, 2.48921e-60]) *).
Proof.
 intros h0.
 assert (h1 := l10 h0).
 exact (proj1 h1).
Qed.
Lemma t2 : p11 -> p1 -> p10.
Proof.
 intros h0 h1.
 refine (add r10 _eN i10 i1 i9 h0 h1 _) ; finalize.
Qed.
Lemma l7 : s1 -> p10 (* BND(1 + eN, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 assert (h2 := l9 h0).
 apply t2. exact h1. exact h2.
Qed.
Notation p12 := (BND r11 i9). (* BND(1 + eD, [1, 1]) *)
Lemma l14 : s1 -> p2 (* BND(eD, [-2.48921e-60, 2.48921e-60]) *).
Proof.
 intros h0.
 assert (h1 := l10 h0).
 exact (proj2 h1).
Qed.
Lemma t3 : p11 -> p2 -> p12.
Proof.
 intros h0 h1.
 refine (add r10 _eD i10 i1 i9 h0 h1 _) ; finalize.
Qed.
Lemma l13 : s1 -> p12 (* BND(1 + eD, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 assert (h2 := l14 h0).
 apply t3. exact h1. exact h2.
Qed.
Lemma t4 : p10 -> p12 -> p9.
Proof.
 intros h0 h1.
 refine (div_pp r9 r11 i9 i9 i8 h0 h1 _) ; finalize.
Qed.
Lemma l6 : s1 -> p9 (* BND((1 + eN) / (1 + eD), [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 assert (h2 := l13 h0).
 apply t4. exact h1. exact h2.
Qed.
Definition f19 := Float2 (7410693711188236507108543040556026102609279018600996098525285376506440296955247) (-262).
Definition f20 := Float2 (7410693711188236507108543040556026102609279018600996098525285376506440296956561) (-262).
Definition i11 := makepairF f19 f20.
Notation p13 := (BND r12 i11). (* BND(1 + er, [1, 1]) *)
Lemma l16 : s1 -> p3 (* BND(er, [-8.86557e-77, 8.86557e-77]) *).
Proof.
 intros h0.
 assert (h1 := l11 h0).
 exact (proj2 h1).
Qed.
Lemma t5 : p11 -> p3 -> p13.
Proof.
 intros h0 h1.
 refine (add r10 _er i10 i2 i11 h0 h1 _) ; finalize.
Qed.
Lemma l15 : s1 -> p13 (* BND(1 + er, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 assert (h2 := l16 h0).
 apply t5. exact h1. exact h2.
Qed.
Lemma t6 : p9 -> p13 -> p8.
Proof.
 intros h0 h1.
 refine (mul_pp r8 r12 i8 i11 i7 h0 h1 _) ; finalize.
Qed.
Lemma l5 : s1 -> p8 (* BND((1 + eN) / (1 + eD) * (1 + er), [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l6 h0).
 assert (h2 := l15 h0).
 apply t6. exact h1. exact h2.
Qed.
Definition f21 := Float2 (57896044618658097711785492504343953926634992332820282019728792003956564819967) (-255).
Definition i12 := makepairF f21 f18.
Notation p14 := (BND r13 i12). (* BND(1 + m, [1, 1]) *)
Lemma l18 : s1 -> p4 (* BND(m, [-1.72723e-77, 0]) *).
Proof.
 intros h0.
 assert (h1 := l12 h0).
 exact (proj2 h1).
Qed.
Lemma t7 : p11 -> p4 -> p14.
Proof.
 intros h0 h1.
 refine (add r10 _m i10 i3 i12 h0 h1 _) ; finalize.
Qed.
Lemma l17 : s1 -> p14 (* BND(1 + m, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 assert (h2 := l18 h0).
 apply t7. exact h1. exact h2.
Qed.
Lemma t8 : p8 -> p14 -> p7.
Proof.
 intros h0 h1.
 refine (mul_pp r7 r13 i7 i12 i6 h0 h1 _) ; finalize.
Qed.
Lemma l4 : s1 -> p7 (* BND(Q, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l5 h0).
 assert (h2 := l17 h0).
 apply t8. exact h1. exact h2.
Qed.
Lemma t9 : p7 -> p11 -> p6.
Proof.
 intros h0 h1.
 refine (sub _Q r10 i6 i10 i5 h0 h1 _) ; finalize.
Qed.
Lemma l3 : s1 -> p6 (* BND(Q - 1, [-4.97841e-60, 4.97841e-60]) *).
Proof.
 intros h0.
 assert (h1 := l4 h0).
 assert (h2 := l8 h0).
 apply t9. exact h1. exact h2.
Qed.
Lemma l1 : s1 -> False.
Proof.
 intros h0.
 assert (h1 := l2 h0).
 assert (h2 := l3 h0).
 refine (simplify (Tatom false (Abnd 0%nat i4)) Tfalse (Abnd 0%nat i5) (List.cons r5 List.nil) h2 h1 _) ; finalize.
Qed.
End Generated_by_Gappa.
