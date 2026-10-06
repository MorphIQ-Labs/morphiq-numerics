Require Import Gappa.Gappa_library.
Section Generated_by_Gappa.
Notation r4 := (Float1 (1)).
Variable _kq : R.
Variable _eY : R.
Notation r5 := ((_kq * _eY)%R).
Notation r3 := ((r4 + r5)%R).
Variable _ea : R.
Notation r8 := ((r4 + _ea)%R).
Notation _M := ((r3 * r8)%R).
Notation r1 := ((_M - r4)%R).
Notation r11 := ((r5 * r8)%R).
Notation r10 := ((r11 + _ea)%R).
Hypothesis a1 : r1 = r10.
Lemma b1 : r1 = r10.
 apply a1.
Qed.
Definition f1 := Float2 (-263) (-3).
Definition f2 := Float2 (263) (-3).
Definition i1 := makepairF f1 f2.
Notation p1 := (BND _kq i1). (* BND(kq, [-32.875, 32.875]) *)
Definition f3 := Float2 (-1) (-69).
Definition f4 := Float2 (1) (-69).
Definition i2 := makepairF f3 f4.
Notation p2 := (BND _eY i2). (* BND(eY, [-1.69407e-21, 1.69407e-21]) *)
Definition s3 := (p1 /\ p2).
Definition f5 := Float2 (-1) (-105).
Definition f6 := Float2 (1) (-105).
Definition i3 := makepairF f5 f6.
Notation p3 := (BND _ea i3). (* BND(ea, [-2.46519e-32, 2.46519e-32]) *)
Definition s2 := (s3 /\ p3).
Definition f7 := Float2 (-1) (-62).
Definition f8 := Float2 (1) (-62).
Definition i4 := makepairF f7 f8.
Notation p4 := (BND r1 i4). (* BND(M - 1, [-2.1684e-19, 2.1684e-19]) *)
Definition s4 := (not p4).
Definition s1 := (s2 /\ s4).
Lemma l2 : s1 -> s4.
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj2 h1).
Qed.
Definition f9 := Float2 (-10668547451525501009479123821657849) (-177).
Definition f10 := Float2 (10668547451525501009479123821658375) (-177).
Definition i5 := makepairF f9 f10.
Notation p5 := (BND r1 i5). (* BND(M - 1, [-5.56924e-20, 5.56924e-20]) *)
Definition f11 := Float2 (191561942608236107284124830942263146942863266451292423) (-177).
Definition f12 := Float2 (191561942608236107305461925845314148961821514094608647) (-177).
Definition i6 := makepairF f11 f12.
Notation p6 := (BND _M i6). (* BND(M, [1, 1]) *)
Definition f13 := Float2 (4722366482869645213433) (-72).
Definition f14 := Float2 (4722366482869645213959) (-72).
Definition i7 := makepairF f13 f14.
Notation p7 := (BND r3 i7). (* BND(1 + kq * eY, [1, 1]) *)
Definition f15 := Float2 (1) (0).
Definition i8 := makepairF f15 f15.
Notation p8 := (BND r4 i8). (* BND(1, [1, 1]) *)
Lemma t1 : p8.
Proof.
 refine (constant1 _ i8 _) ; finalize.
Qed.
Lemma l6 : s1 -> p8 (* BND(1, [1, 1]) *).
Proof.
 intros h0.
 apply t1.
Qed.
Definition f16 := Float2 (-263) (-72).
Definition f17 := Float2 (263) (-72).
Definition i9 := makepairF f16 f17.
Notation p9 := (BND r5 i9). (* BND(kq * eY, [-5.56924e-20, 5.56924e-20]) *)
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
Lemma l11 : s1 -> p2 (* BND(eY, [-1.69407e-21, 1.69407e-21]) *).
Proof.
 intros h0.
 assert (h1 := l9 h0).
 exact (proj2 h1).
Qed.
Lemma t2 : p1 -> p2 -> p9.
Proof.
 intros h0 h1.
 refine (mul_oo _kq _eY i1 i2 i9 h0 h1 _) ; finalize.
Qed.
Lemma l7 : s1 -> p9 (* BND(kq * eY, [-5.56924e-20, 5.56924e-20]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 assert (h2 := l11 h0).
 apply t2. exact h1. exact h2.
Qed.
Lemma t3 : p8 -> p9 -> p7.
Proof.
 intros h0 h1.
 refine (add r4 r5 i8 i9 i7 h0 h1 _) ; finalize.
Qed.
Lemma l5 : s1 -> p7 (* BND(1 + kq * eY, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l6 h0).
 assert (h2 := l7 h0).
 apply t3. exact h1. exact h2.
Qed.
Definition f18 := Float2 (40564819207303340847894502572031) (-105).
Definition f19 := Float2 (40564819207303340847894502572033) (-105).
Definition i10 := makepairF f18 f19.
Notation p10 := (BND r8 i10). (* BND(1 + ea, [1, 1]) *)
Lemma l13 : s1 -> p3 (* BND(ea, [-2.46519e-32, 2.46519e-32]) *).
Proof.
 intros h0.
 assert (h1 := l10 h0).
 exact (proj2 h1).
Qed.
Lemma t4 : p8 -> p3 -> p10.
Proof.
 intros h0 h1.
 refine (add r4 _ea i8 i3 i10 h0 h1 _) ; finalize.
Qed.
Lemma l12 : s1 -> p10 (* BND(1 + ea, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l6 h0).
 assert (h2 := l13 h0).
 apply t4. exact h1. exact h2.
Qed.
Lemma t5 : p7 -> p10 -> p6.
Proof.
 intros h0 h1.
 refine (mul_pp r3 r8 i7 i10 i6 h0 h1 _) ; finalize.
Qed.
Lemma l4 : s1 -> p6 (* BND(M, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l5 h0).
 assert (h2 := l12 h0).
 apply t5. exact h1. exact h2.
Qed.
Lemma t6 : p6 -> p8 -> p5.
Proof.
 intros h0 h1.
 refine (sub _M r4 i6 i8 i5 h0 h1 _) ; finalize.
Qed.
Lemma l3 : s1 -> p5 (* BND(M - 1, [-5.56924e-20, 5.56924e-20]) *).
Proof.
 intros h0.
 assert (h1 := l4 h0).
 assert (h2 := l6 h0).
 apply t6. exact h1. exact h2.
Qed.
Lemma l1 : s1 -> False.
Proof.
 intros h0.
 assert (h1 := l2 h0).
 assert (h2 := l3 h0).
 refine (simplify (Tatom false (Abnd 0%nat i4)) Tfalse (Abnd 0%nat i5) (List.cons r1 List.nil) h2 h1 _) ; finalize.
Qed.
End Generated_by_Gappa.
