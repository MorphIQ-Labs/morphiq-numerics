Require Import Gappa.Gappa_library.
Section Generated_by_Gappa.
Variable _eL : R.
Definition f1 := Float2 (-1) (-64).
Definition f2 := Float2 (1) (-64).
Definition i1 := makepairF f1 f2.
Notation p1 := (BND _eL i1). (* BND(eL, [-5.42101e-20, 5.42101e-20]) *)
Variable _eC : R.
Definition f3 := Float2 (-575) (-119).
Definition f4 := Float2 (575) (-119).
Definition i2 := makepairF f3 f4.
Notation p2 := (BND _eC i2). (* BND(eC, [-8.65164e-34, 8.65164e-34]) *)
Definition s3 := (p1 /\ p2).
Variable _em : R.
Definition f5 := Float2 (-5) (-106).
Definition f6 := Float2 (5) (-106).
Definition i3 := makepairF f5 f6.
Notation p3 := (BND _em i3). (* BND(em, [-6.16298e-32, 6.16298e-32]) *)
Definition s2 := (s3 /\ p3).
Notation r8 := (Float1 (1)).
Notation r7 := ((r8 + _eL)%R).
Notation r9 := ((r8 + _eC)%R).
Notation r6 := ((r7 * r9)%R).
Notation r10 := ((r8 + _em)%R).
Notation _Y := ((r6 * r10)%R).
Notation r4 := ((_Y - r8)%R).
Definition f7 := Float2 (-1) (-63).
Definition f8 := Float2 (1) (-63).
Definition i4 := makepairF f7 f8.
Notation p4 := (BND r4 i4). (* BND(Y - 1, [-1.0842e-19, 1.0842e-19]) *)
Definition s4 := (not p4).
Definition s1 := (s2 /\ s4).
Lemma l2 : s1 -> s4.
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj2 h1).
Qed.
Definition f9 := Float2 (-53919893334363439943132726164008463838458253818309244131932249262907) (-289).
Definition f10 := Float2 (53919893334363439943132726164015203277521355301426491748419488451387) (-289).
Definition i5 := makepairF f9 f10.
Notation p5 := (BND r4 i5). (* BND(Y - 1, [-5.42101e-20, 5.42101e-20]) *)
Definition f11 := Float2 (994646472819573284256844602959278240257779575430686971042469699968009749893134501803205) (-289).
Definition f12 := Float2 (994646472819573284364684389628005120144045027758710638158449309087745485773486239517499) (-289).
Definition i6 := makepairF f11 f12.
Notation p6 := (BND _Y i6). (* BND(Y, [1, 1]) *)
Definition f13 := Float2 (12259964326927110866202162219310004925620167064336466495) (-183).
Definition f14 := Float2 (12259964326927110867531390215094942012279658890601169471) (-183).
Definition i7 := makepairF f13 f14.
Notation p7 := (BND r6 i7). (* BND((1 + eL) * (1 + eC), [1, 1]) *)
Definition f15 := Float2 (18446744073709551615) (-64).
Definition f16 := Float2 (18446744073709551617) (-64).
Definition i8 := makepairF f15 f16.
Notation p8 := (BND r7 i8). (* BND(1 + eL, [1, 1]) *)
Definition f17 := Float2 (1) (0).
Definition i9 := makepairF f17 f17.
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
Lemma l8 : s1 -> p1 (* BND(eL, [-5.42101e-20, 5.42101e-20]) *).
Proof.
 intros h0.
 assert (h1 := l9 h0).
 exact (proj1 h1).
Qed.
Lemma t2 : p9 -> p1 -> p8.
Proof.
 intros h0 h1.
 refine (add r8 _eL i9 i1 i8 h0 h1 _) ; finalize.
Qed.
Lemma l6 : s1 -> p8 (* BND(1 + eL, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 assert (h2 := l8 h0).
 apply t2. exact h1. exact h2.
Qed.
Definition f18 := Float2 (664613997892457936451903530140171713) (-119).
Definition f19 := Float2 (664613997892457936451903530140172863) (-119).
Definition i10 := makepairF f18 f19.
Notation p10 := (BND r9 i10). (* BND(1 + eC, [1, 1]) *)
Lemma l12 : s1 -> p2 (* BND(eC, [-8.65164e-34, 8.65164e-34]) *).
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
Lemma l5 : s1 -> p7 (* BND((1 + eL) * (1 + eC), [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l6 h0).
 assert (h2 := l11 h0).
 apply t4. exact h1. exact h2.
Qed.
Definition f20 := Float2 (81129638414606681695789005144059) (-106).
Definition f21 := Float2 (81129638414606681695789005144069) (-106).
Definition i11 := makepairF f20 f21.
Notation p11 := (BND r10 i11). (* BND(1 + em, [1, 1]) *)
Lemma l14 : s1 -> p3 (* BND(em, [-6.16298e-32, 6.16298e-32]) *).
Proof.
 intros h0.
 assert (h1 := l10 h0).
 exact (proj2 h1).
Qed.
Lemma t5 : p9 -> p3 -> p11.
Proof.
 intros h0 h1.
 refine (add r8 _em i9 i3 i11 h0 h1 _) ; finalize.
Qed.
Lemma l13 : s1 -> p11 (* BND(1 + em, [1, 1]) *).
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
Lemma l3 : s1 -> p5 (* BND(Y - 1, [-5.42101e-20, 5.42101e-20]) *).
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
