Require Import Gappa.Gappa_library.
Section Generated_by_Gappa.
Variable _X1 : R.
Definition f1 := Float2 (1162012445139108865345163627401355343448367606773150580773796710443291429907578537583340408976062024146156427387736372019) (-399).
Definition f2 := Float2 (1) (0).
Definition i1 := makepairF f1 f2.
Notation p1 := (BND _X1 i1). (* BND(X1, [0.9, 1]) *)
Variable _E1 : R.
Definition f3 := Float2 (-259) (-218).
Definition f4 := Float2 (259) (-218).
Definition i2 := makepairF f3 f4.
Notation p2 := (BND _E1 i2). (* BND(E1, [-6.14838e-64, 6.14838e-64]) *)
Definition s4 := (p1 /\ p2).
Variable _dr : R.
Definition f5 := Float2 (-575) (-208).
Definition f6 := Float2 (575) (-208).
Definition i3 := makepairF f5 f6.
Notation p3 := (BND _dr i3). (* BND(dr, [-1.39775e-60, 1.39775e-60]) *)
Definition s3 := (s4 /\ p3).
Variable _m1 : R.
Definition f7 := Float2 (-1) (-255).
Definition f8 := Float2 (0) (0).
Definition i4 := makepairF f7 f8.
Notation p4 := (BND _m1 i4). (* BND(m1, [-1.72723e-77, 0]) *)
Definition s2 := (s3 /\ p4).
Notation r9 := (Float1 (1)).
Notation r8 := ((r9 + _m1)%R).
Notation r11 := ((_E1 / _X1)%R).
Notation r10 := ((r9 + r11)%R).
Notation r7 := ((r8 * r10)%R).
Notation r12 := ((r9 + _dr)%R).
Notation _Y := ((r7 * r12)%R).
Notation r5 := ((_Y - r9)%R).
Definition f9 := Float2 (-1) (-198).
Definition f10 := Float2 (1) (-198).
Definition i5 := makepairF f9 f10.
Notation p5 := (BND r5 i5). (* BND(Y - 1, [-2.48921e-60, 2.48921e-60]) *)
Definition s5 := (not p5).
Definition s1 := (s2 /\ s5).
Lemma l2 : s1 -> s5.
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj2 h1).
Qed.
Definition f11 := Float2 (-451387196311520055039391893247946770196040395417745942089273) (-397).
Definition f12 := Float2 (1805548785246080197856822374461163939248443309022622262376677) (-399).
Definition i6 := makepairF f11 f12.
Notation p6 := (BND r5 i6). (* BND(Y - 1, [-1.39843e-60, 1.39843e-60]) *)
Definition f13 := Float2 (322781234760863573706989896500376484291213224103652939103831968180384641232050109936812421213247032889092478750651347399) (-397).
Definition f14 := Float2 (1291124939043454294827959586001505937164852896414611756415331483819109057088618454137197137804008164161260608608636123365) (-399).
Definition i7 := makepairF f13 f14.
Notation p7 := (BND _Y i7). (* BND(Y, [1, 1]) *)
Definition f15 := Float2 (322781234760863573706989896500376484291213224103652939103832419347071872149730010634177214264270690245890049603131961799) (-397).
Definition f16 := Float2 (322781234760863573706989896500376484291213224103652939103832419788090033354474712836934491399978383683517581299678416441) (-397).
Definition i8 := makepairF f15 f16.
Notation p8 := (BND r7 i8). (* BND((1 + m1) * (1 + E1 / X1), [1, 1]) *)
Definition f17 := Float2 (57896044618658097711785492504343953926634992332820282019728792003956564819967) (-255).
Definition i9 := makepairF f17 f2.
Notation p9 := (BND r8 i9). (* BND(1 + m1, [1, 1]) *)
Definition i10 := makepairF f2 f2.
Notation p10 := (BND r9 i10). (* BND(1, [1, 1]) *)
Lemma t1 : p10.
Proof.
 refine (constant1 _ i10 _) ; finalize.
Qed.
Lemma l7 : s1 -> p10 (* BND(1, [1, 1]) *).
Proof.
 intros h0.
 apply t1.
Qed.
Lemma l9 : s1 -> s2.
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj1 h1).
Qed.
Lemma l8 : s1 -> p4 (* BND(m1, [-1.72723e-77, 0]) *).
Proof.
 intros h0.
 assert (h1 := l9 h0).
 exact (proj2 h1).
Qed.
Lemma t2 : p10 -> p4 -> p9.
Proof.
 intros h0 h1.
 refine (add r9 _m1 i10 i4 i9 h0 h1 _) ; finalize.
Qed.
Lemma l6 : s1 -> p9 (* BND(1 + m1, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 assert (h2 := l8 h0).
 apply t2. exact h1. exact h2.
Qed.
Definition f18 := Float2 (322781234760863573706989896500376484291213224103652939103832419347071872149735585820476846920056074175458211693508456903) (-397).
Definition i11 := makepairF f18 f16.
Notation p11 := (BND r10 i11). (* BND(1 + E1 / X1, [1, 1]) *)
Definition f19 := Float2 (-220509080602369563508228822239961154754029684803084979769) (-397).
Definition f20 := Float2 (220509080602369563508228822239961154754029684803084979769) (-397).
Definition i12 := makepairF f19 f20.
Notation p12 := (BND r11 i12). (* BND(E1 / X1, [-6.83153e-64, 6.83153e-64]) *)
Lemma l14 : s1 -> s3.
Proof.
 intros h0.
 assert (h1 := l9 h0).
 exact (proj1 h1).
Qed.
Lemma l13 : s1 -> s4.
Proof.
 intros h0.
 assert (h1 := l14 h0).
 exact (proj1 h1).
Qed.
Lemma l12 : s1 -> p2 (* BND(E1, [-6.14838e-64, 6.14838e-64]) *).
Proof.
 intros h0.
 assert (h1 := l13 h0).
 exact (proj2 h1).
Qed.
Lemma l15 : s1 -> p1 (* BND(X1, [0.9, 1]) *).
Proof.
 intros h0.
 assert (h1 := l13 h0).
 exact (proj1 h1).
Qed.
Definition f21 := Float2 (1412347890462003171863052620221724943623029975004407765401) (-190).
Definition i13 := makepairF f21 f2.
Notation p13 := (BND _X1 i13). (* BND(X1, [0.9, 1]) *)
Lemma t3 : p2 -> p13 -> p12.
Proof.
 intros h0 h1.
 refine (div_op _E1 _X1 i2 i13 i12 h0 h1 _) ; finalize.
Qed.
Lemma l11 : s1 -> p12 (* BND(E1 / X1, [-6.83153e-64, 6.83153e-64]) *).
Proof.
 intros h0.
 assert (h1 := l12 h0).
 assert (h2 := l15 h0).
 apply t3. exact h1. refine (subset _X1 i1 i13 h2 _) ; finalize.
Qed.
Lemma t4 : p10 -> p12 -> p11.
Proof.
 intros h0 h1.
 refine (add r9 r11 i10 i12 i11 h0 h1 _) ; finalize.
Qed.
Lemma l10 : s1 -> p11 (* BND(1 + E1 / X1, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 assert (h2 := l11 h0).
 apply t4. exact h1. exact h2.
Qed.
Lemma t5 : p9 -> p11 -> p8.
Proof.
 intros h0 h1.
 refine (mul_pp r8 r10 i9 i11 i8 h0 h1 _) ; finalize.
Qed.
Lemma l5 : s1 -> p8 (* BND((1 + m1) * (1 + E1 / X1), [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l6 h0).
 assert (h2 := l10 h0).
 apply t5. exact h1. exact h2.
Qed.
Definition f22 := Float2 (411376139330301510538742295639337626245683966408394965837151681) (-208).
Definition f23 := Float2 (411376139330301510538742295639337626245683966408394965837152831) (-208).
Definition i14 := makepairF f22 f23.
Notation p14 := (BND r12 i14). (* BND(1 + dr, [1, 1]) *)
Lemma l17 : s1 -> p3 (* BND(dr, [-1.39775e-60, 1.39775e-60]) *).
Proof.
 intros h0.
 assert (h1 := l14 h0).
 exact (proj2 h1).
Qed.
Lemma t6 : p10 -> p3 -> p14.
Proof.
 intros h0 h1.
 refine (add r9 _dr i10 i3 i14 h0 h1 _) ; finalize.
Qed.
Lemma l16 : s1 -> p14 (* BND(1 + dr, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 assert (h2 := l17 h0).
 apply t6. exact h1. exact h2.
Qed.
Lemma t7 : p8 -> p14 -> p7.
Proof.
 intros h0 h1.
 refine (mul_pp r7 r12 i8 i14 i7 h0 h1 _) ; finalize.
Qed.
Lemma l4 : s1 -> p7 (* BND(Y, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l5 h0).
 assert (h2 := l16 h0).
 apply t7. exact h1. exact h2.
Qed.
Lemma t8 : p7 -> p10 -> p6.
Proof.
 intros h0 h1.
 refine (sub _Y r9 i7 i10 i6 h0 h1 _) ; finalize.
Qed.
Lemma l3 : s1 -> p6 (* BND(Y - 1, [-1.39843e-60, 1.39843e-60]) *).
Proof.
 intros h0.
 assert (h1 := l4 h0).
 assert (h2 := l7 h0).
 apply t8. exact h1. exact h2.
Qed.
Lemma l1 : s1 -> False.
Proof.
 intros h0.
 assert (h1 := l2 h0).
 assert (h2 := l3 h0).
 refine (simplify (Tatom false (Abnd 0%nat i5)) Tfalse (Abnd 0%nat i6) (List.cons r5 List.nil) h2 h1 _) ; finalize.
Qed.
End Generated_by_Gappa.
