Require Import Gappa.Gappa_library.
Section Generated_by_Gappa.
Notation r4 := (Float1 (1)).
Variable _s : R.
Notation r12 := (Float1 (756)).
Notation r11 := ((r4 / r12)%R).
Notation r9 := ((_s * r11)%R).
Variable _kk : R.
Notation r13 := ((r4 + _kk)%R).
Notation r8 := ((r9 * r13)%R).
Variable _ma : R.
Notation r15 := ((r4 + _ma)%R).
Notation r7 := ((r8 * r15)%R).
Variable _Xn : R.
Variable _En : R.
Notation _Hn := ((_Xn + _En)%R).
Notation r6 := ((r7 * _Hn)%R).
Variable _mb : R.
Notation r20 := ((r4 + _mb)%R).
Notation _b := ((r6 * r20)%R).
Notation r3 := ((r4 - _b)%R).
Variable _sa : R.
Notation _H := ((r3 + _sa)%R).
Notation r24 := ((r9 * _Xn)%R).
Notation _X := ((r4 - r24)%R).
Notation r1 := ((_H - _X)%R).
Notation r32 := ((r13 * r15)%R).
Notation r31 := ((r32 * r20)%R).
Notation r30 := ((r31 - r4)%R).
Notation r29 := ((_Hn * r30)%R).
Notation r28 := ((_En + r29)%R).
Notation r27 := ((r9 * r28)%R).
Notation r26 := ((- r27)%R).
Notation r25 := ((r26 + _sa)%R).
Hypothesis a1 : r1 = r25.
Lemma b1 : r1 = r25.
 apply a1.
Qed.
Definition f1 := Float2 (0) (0).
Definition f2 := Float2 (1592860837297909563529253741250057874680279018306706523889592224082098485641088490907296736170853021321236871631389291289) (-400).
Definition i1 := makepairF f1 f2.
Notation p1 := (BND _s i1). (* BND(s, [0, 0.61685]) *)
Definition f3 := Float2 (2554614812902364325752297031970820165452424861524653282354320999761126499389407635293078928895572466133110842431807671875) (-400).
Definition f4 := Float2 (1) (0).
Definition i2 := makepairF f3 f4.
Notation p2 := (BND _Xn i2). (* BND(Xn, [0.989298, 1]) *)
Definition s7 := (p1 /\ p2).
Definition f5 := Float2 (-519) (-263).
Definition f6 := Float2 (519) (-263).
Definition i3 := makepairF f5 f6.
Notation p3 := (BND _En i3). (* BND(En, [-3.5017e-77, 3.5017e-77]) *)
Definition s6 := (s7 /\ p3).
Definition f7 := Float2 (-1) (-255).
Definition f8 := Float2 (1) (-255).
Definition i4 := makepairF f7 f8.
Notation p4 := (BND _kk i4). (* BND(kk, [-1.72723e-77, 1.72723e-77]) *)
Definition s5 := (s6 /\ p4).
Definition i5 := makepairF f7 f1.
Notation p5 := (BND _ma i5). (* BND(ma, [-1.72723e-77, 0]) *)
Definition s4 := (s5 /\ p5).
Notation p6 := (BND _mb i5). (* BND(mb, [-1.72723e-77, 0]) *)
Definition s3 := (s4 /\ p6).
Definition f9 := Float2 (-1) (-254).
Definition f10 := Float2 (1) (-254).
Definition i6 := makepairF f9 f10.
Notation p7 := (BND _sa i6). (* BND(sa, [-3.45447e-77, 3.45447e-77]) *)
Definition s2 := (s3 /\ p7).
Notation p8 := (BND r1 i3). (* BND(H - X, [-3.5017e-77, 3.5017e-77]) *)
Definition s8 := (not p8).
Definition s1 := (s2 /\ s8).
Lemma l2 : s1 -> s8.
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj2 h1).
Qed.
Definition f11 := Float2 (-1292719561166606938149790113202477326018705947318820401778484897420331595511525779114854696989338123478228061790636919785) (-653).
Definition f12 := Float2 (161721630069544279104332994783680206251237076005651715774880849629929189062422959845380232433581179659491787859256234191) (-650).
Definition i7 := makepairF f11 f12.
Notation p9 := (BND r1 i7). (* BND(H - X, [-3.45873e-77, 3.46155e-77]) *)
Notation p10 := (BND r25 i7). (* BND(-(s * (1 / 756) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1))) + sa, [-3.45873e-77, 3.46155e-77]) *)
Definition f13 := Float2 (-1594622123152643321830527200971388853853050904208645363155219150007784503105181800032020349269207760276475804263173097) (-653).
Definition f14 := Float2 (331012689112492250838046533491964105630463953825246222964639846138712686370385181027397853572565194747839610959515855) (-650).
Definition i8 := makepairF f13 f14.
Notation p11 := (BND r26 i8). (* BND(-(s * (1 / 756) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1))), [-4.26649e-80, 7.08512e-80]) *)
Definition f15 := Float2 (-331012689112492250838046533491964105630463953825246222964639846138712686370385181027397853572565194747839610959515855) (-650).
Definition f16 := Float2 (1594622123152643321830527200971388853853050904208645363155219150007784503105181800032020349269207760276475804263173097) (-653).
Definition i9 := makepairF f15 f16.
Notation p12 := (BND r27 i9). (* BND(s * (1 / 756) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1)), [-7.08512e-80, 4.26649e-80]) *)
Definition f17 := Float2 (4213917558989178739495380267857295964762642905573297682247598476407667951431451034146287661827653495558827702728543099) (-401).
Definition i10 := makepairF f1 f17.
Notation p13 := (BND r9 i10). (* BND(s * (1 / 756), [0, 0.000815939]) *)
Lemma l14 : s1 -> s2.
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj1 h1).
Qed.
Lemma l13 : s1 -> s3.
Proof.
 intros h0.
 assert (h1 := l14 h0).
 exact (proj1 h1).
Qed.
Lemma l12 : s1 -> s4.
Proof.
 intros h0.
 assert (h1 := l13 h0).
 exact (proj1 h1).
Qed.
Lemma l11 : s1 -> s5.
Proof.
 intros h0.
 assert (h1 := l12 h0).
 exact (proj1 h1).
Qed.
Lemma l10 : s1 -> s6.
Proof.
 intros h0.
 assert (h1 := l11 h0).
 exact (proj1 h1).
Qed.
Lemma l9 : s1 -> s7.
Proof.
 intros h0.
 assert (h1 := l10 h0).
 exact (proj1 h1).
Qed.
Lemma l8 : s1 -> p1 (* BND(s, [0, 0.61685]) *).
Proof.
 intros h0.
 assert (h1 := l9 h0).
 exact (proj1 h1).
Qed.
Definition f18 := Float2 (1) (-10).
Definition f19 := Float2 (27325395535311202006940943619079490733647680347399190611964649275562408698590912112483019611430029962284689650505264481) (-403).
Definition i11 := makepairF f18 f19.
Notation p14 := (BND r11 i11). (* BND(1 / 756, [0.000976562, 0.00132275]) *)
Definition i12 := makepairF f4 f4.
Notation p15 := (BND r4 i12). (* BND(1, [1, 1]) *)
Lemma t1 : p15.
Proof.
 refine (constant1 _ i12 _) ; finalize.
Qed.
Lemma l16 : s1 -> p15 (* BND(1, [1, 1]) *).
Proof.
 intros h0.
 apply t1.
Qed.
Definition f20 := Float2 (189) (2).
Definition f21 := Float2 (1) (10).
Definition i13 := makepairF f20 f21.
Notation p16 := (BND r12 i13). (* BND(756, [756, 1024]) *)
Lemma t2 : p16.
Proof.
 refine (constant1 _ i13 _) ; finalize.
Qed.
Lemma l17 : s1 -> p16 (* BND(756, [756, 1024]) *).
Proof.
 intros h0.
 apply t2.
Qed.
Lemma t3 : p15 -> p16 -> p14.
Proof.
 intros h0 h1.
 refine (div_pp r4 r12 i12 i13 i11 h0 h1 _) ; finalize.
Qed.
Lemma l15 : s1 -> p14 (* BND(1 / 756, [0.000976562, 0.00132275]) *).
Proof.
 intros h0.
 assert (h1 := l16 h0).
 assert (h2 := l17 h0).
 apply t3. exact h1. exact h2.
Qed.
Definition f22 := Float2 (24888450582779836930144589707032154291879359661042289435774878501282788838142007670426511502669578458144326119240457677) (-394).
Definition i14 := makepairF f1 f22.
Notation p17 := (BND _s i14). (* BND(s, [0, 0.61685]) *)
Lemma t4 : p17 -> p14 -> p13.
Proof.
 intros h0 h1.
 refine (mul_pp _s r11 i14 i11 i10 h0 h1 _) ; finalize.
Qed.
Lemma l7 : s1 -> p13 (* BND(s * (1 / 756), [0, 0.000815939]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 assert (h2 := l15 h0).
 apply t4. refine (subset _s i1 i14 h1 _) ; finalize. exact h2.
Qed.
Definition f23 := Float2 (-74512209424212971755067928853090668703579235132339702959390955309092098923300373) (-518).
Definition f24 := Float2 (44869434579460025726633756690866564293142119057935718565289813803066337735475719) (-518).
Definition i15 := makepairF f23 f24.
Notation p18 := (BND r28 i15). (* BND(En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1), [-8.6834e-77, 5.22893e-77]) *)
Lemma l19 : s1 -> p3 (* BND(En, [-3.5017e-77, 3.5017e-77]) *).
Proof.
 intros h0.
 assert (h1 := l10 h0).
 exact (proj2 h1).
Qed.
Definition f25 := Float2 (-44464162267129419042651258243336156615655674111605976591151712259038641781736981) (-518).
Definition f26 := Float2 (14821387422376473014217086081112052205218558037201992197050570753012880593912327) (-518).
Definition i16 := makepairF f25 f26.
Notation p19 := (BND r29 i16). (* BND(Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1), [-5.1817e-77, 1.72723e-77]) *)
Definition f27 := Float2 (1) (-1).
Definition f28 := Float2 (14821387422376473014217086081112052205218558037201992197050570753012880593912327) (-263).
Definition i17 := makepairF f27 f28.
Notation p20 := (BND _Hn i17). (* BND(Hn, [0.5, 1]) *)
Lemma l22 : s1 -> p2 (* BND(Xn, [0.989298, 1]) *).
Proof.
 intros h0.
 assert (h1 := l9 h0).
 exact (proj2 h1).
Qed.
Definition f29 := Float2 (3) (-2).
Definition i18 := makepairF f29 f4.
Notation p21 := (BND _Xn i18). (* BND(Xn, [0.75, 1]) *)
Definition f30 := Float2 (-1) (-2).
Definition i19 := makepairF f30 f6.
Notation p22 := (BND _En i19). (* BND(En, [-0.25, 3.5017e-77]) *)
Lemma t5 : p21 -> p22 -> p20.
Proof.
 intros h0 h1.
 refine (add _Xn _En i18 i19 i17 h0 h1 _) ; finalize.
Qed.
Lemma l21 : s1 -> p20 (* BND(Hn, [0.5, 1]) *).
Proof.
 intros h0.
 assert (h1 := l22 h0).
 assert (h2 := l19 h0).
 apply t5. refine (subset _Xn i2 i18 h1 _) ; finalize. refine (subset _En i3 i19 h2 _) ; finalize.
Qed.
Definition f31 := Float2 (-3) (-255).
Definition i20 := makepairF f31 f8.
Notation p23 := (BND r30 i20). (* BND((1 + kk) * (1 + ma) * (1 + mb) - 1, [-5.1817e-77, 1.72723e-77]) *)
Definition f32 := Float2 (57896044618658097711785492504343953926634992332820282019728792003956564819965) (-255).
Definition f33 := Float2 (57896044618658097711785492504343953926634992332820282019728792003956564819969) (-255).
Definition i21 := makepairF f32 f33.
Notation p24 := (BND r31 i21). (* BND((1 + kk) * (1 + ma) * (1 + mb), [1, 1]) *)
Definition f34 := Float2 (28948022309329048855892746252171976963317496166410141009864396001978282409983) (-254).
Definition i22 := makepairF f34 f33.
Notation p25 := (BND r32 i22). (* BND((1 + kk) * (1 + ma), [1, 1]) *)
Definition f35 := Float2 (57896044618658097711785492504343953926634992332820282019728792003956564819967) (-255).
Definition i23 := makepairF f35 f33.
Notation p26 := (BND r13 i23). (* BND(1 + kk, [1, 1]) *)
Lemma l27 : s1 -> p4 (* BND(kk, [-1.72723e-77, 1.72723e-77]) *).
Proof.
 intros h0.
 assert (h1 := l11 h0).
 exact (proj2 h1).
Qed.
Lemma t6 : p15 -> p4 -> p26.
Proof.
 intros h0 h1.
 refine (add r4 _kk i12 i4 i23 h0 h1 _) ; finalize.
Qed.
Lemma l26 : s1 -> p26 (* BND(1 + kk, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l16 h0).
 assert (h2 := l27 h0).
 apply t6. exact h1. exact h2.
Qed.
Definition i24 := makepairF f35 f4.
Notation p27 := (BND r15 i24). (* BND(1 + ma, [1, 1]) *)
Lemma l29 : s1 -> p5 (* BND(ma, [-1.72723e-77, 0]) *).
Proof.
 intros h0.
 assert (h1 := l12 h0).
 exact (proj2 h1).
Qed.
Lemma t7 : p15 -> p5 -> p27.
Proof.
 intros h0 h1.
 refine (add r4 _ma i12 i5 i24 h0 h1 _) ; finalize.
Qed.
Lemma l28 : s1 -> p27 (* BND(1 + ma, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l16 h0).
 assert (h2 := l29 h0).
 apply t7. exact h1. exact h2.
Qed.
Lemma t8 : p26 -> p27 -> p25.
Proof.
 intros h0 h1.
 refine (mul_pp r13 r15 i23 i24 i22 h0 h1 _) ; finalize.
Qed.
Lemma l25 : s1 -> p25 (* BND((1 + kk) * (1 + ma), [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l26 h0).
 assert (h2 := l28 h0).
 apply t8. exact h1. exact h2.
Qed.
Notation p28 := (BND r20 i24). (* BND(1 + mb, [1, 1]) *)
Lemma l31 : s1 -> p6 (* BND(mb, [-1.72723e-77, 0]) *).
Proof.
 intros h0.
 assert (h1 := l13 h0).
 exact (proj2 h1).
Qed.
Lemma t9 : p15 -> p6 -> p28.
Proof.
 intros h0 h1.
 refine (add r4 _mb i12 i5 i24 h0 h1 _) ; finalize.
Qed.
Lemma l30 : s1 -> p28 (* BND(1 + mb, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l16 h0).
 assert (h2 := l31 h0).
 apply t9. exact h1. exact h2.
Qed.
Lemma t10 : p25 -> p28 -> p24.
Proof.
 intros h0 h1.
 refine (mul_pp r32 r20 i22 i24 i21 h0 h1 _) ; finalize.
Qed.
Lemma l24 : s1 -> p24 (* BND((1 + kk) * (1 + ma) * (1 + mb), [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l25 h0).
 assert (h2 := l30 h0).
 apply t10. exact h1. exact h2.
Qed.
Lemma t11 : p24 -> p15 -> p23.
Proof.
 intros h0 h1.
 refine (sub r31 r4 i21 i12 i20 h0 h1 _) ; finalize.
Qed.
Lemma l23 : s1 -> p23 (* BND((1 + kk) * (1 + ma) * (1 + mb) - 1, [-5.1817e-77, 1.72723e-77]) *).
Proof.
 intros h0.
 assert (h1 := l24 h0).
 assert (h2 := l16 h0).
 apply t11. exact h1. exact h2.
Qed.
Lemma t12 : p20 -> p23 -> p19.
Proof.
 intros h0 h1.
 refine (mul_po _Hn r30 i17 i20 i16 h0 h1 _) ; finalize.
Qed.
Lemma l20 : s1 -> p19 (* BND(Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1), [-5.1817e-77, 1.72723e-77]) *).
Proof.
 intros h0.
 assert (h1 := l21 h0).
 assert (h2 := l23 h0).
 apply t12. exact h1. exact h2.
Qed.
Lemma t13 : p3 -> p19 -> p18.
Proof.
 intros h0 h1.
 refine (add _En r29 i3 i16 i15 h0 h1 _) ; finalize.
Qed.
Lemma l18 : s1 -> p18 (* BND(En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1), [-8.6834e-77, 5.22893e-77]) *).
Proof.
 intros h0.
 assert (h1 := l19 h0).
 assert (h2 := l20 h0).
 apply t13. exact h1. exact h2.
Qed.
Lemma t14 : p13 -> p18 -> p12.
Proof.
 intros h0 h1.
 refine (mul_po r9 r28 i10 i15 i9 h0 h1 _) ; finalize.
Qed.
Lemma l6 : s1 -> p12 (* BND(s * (1 / 756) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1)), [-7.08512e-80, 4.26649e-80]) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 assert (h2 := l18 h0).
 apply t14. exact h1. exact h2.
Qed.
Lemma t15 : p12 -> p11.
Proof.
 intros h0.
 refine (neg r27 i9 i8 h0 _) ; finalize.
Qed.
Lemma l5 : s1 -> p11 (* BND(-(s * (1 / 756) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1))), [-4.26649e-80, 7.08512e-80]) *).
Proof.
 intros h0.
 assert (h1 := l6 h0).
 apply t15. exact h1.
Qed.
Lemma l32 : s1 -> p7 (* BND(sa, [-3.45447e-77, 3.45447e-77]) *).
Proof.
 intros h0.
 assert (h1 := l14 h0).
 exact (proj2 h1).
Qed.
Lemma t16 : p11 -> p7 -> p10.
Proof.
 intros h0 h1.
 refine (add r26 _sa i8 i6 i7 h0 h1 _) ; finalize.
Qed.
Lemma l4 : s1 -> p10 (* BND(-(s * (1 / 756) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1))) + sa, [-3.45873e-77, 3.46155e-77]) *).
Proof.
 intros h0.
 assert (h1 := l5 h0).
 assert (h2 := l32 h0).
 apply t16. exact h1. exact h2.
Qed.
Definition i25 := makepairF f1 f1.
Notation p29 := (REL r1 r25 i25). (* REL(H - X, -(s * (1 / 756) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1))) + sa, [0, 0]) *)
Notation p30 := (r1 = r25). (* EQL(H - X, -(s * (1 / 756) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1))) + sa) *)
Lemma t17 : p30.
Proof.
 refine (b1) ; finalize.
Qed.
Lemma l34 : s1 -> p30 (* EQL(H - X, -(s * (1 / 756) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1))) + sa) *).
Proof.
 intros h0.
 apply t17.
Qed.
Notation p31 := (REL r25 r25 i25). (* REL(-(s * (1 / 756) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1))) + sa, -(s * (1 / 756) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1))) + sa, [0, 0]) *)
Lemma t18 : p31.
Proof.
 refine (rel_refl r25 i25 _) ; finalize.
Qed.
Lemma l35 : s1 -> p31 (* REL(-(s * (1 / 756) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1))) + sa, -(s * (1 / 756) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1))) + sa, [0, 0]) *).
Proof.
 intros h0.
 apply t18.
Qed.
Lemma t19 : p30 -> p31 -> p29.
Proof.
 intros h0 h1.
 refine (rel_rewrite_1 r1 r25 r25 i25 h0 h1) ; finalize.
Qed.
Lemma l33 : s1 -> p29 (* REL(H - X, -(s * (1 / 756) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1))) + sa, [0, 0]) *).
Proof.
 intros h0.
 assert (h1 := l34 h0).
 assert (h2 := l35 h0).
 apply t19. exact h1. exact h2.
Qed.
Lemma t20 : p10 -> p29 -> p9.
Proof.
 intros h0 h1.
 refine (bnd_of_bnd_rel_o r1 r25 i7 i25 i7 h0 h1 _) ; finalize.
Qed.
Lemma l3 : s1 -> p9 (* BND(H - X, [-3.45873e-77, 3.46155e-77]) *).
Proof.
 intros h0.
 assert (h1 := l4 h0).
 assert (h2 := l33 h0).
 apply t20. exact h1. exact h2.
Qed.
Lemma l1 : s1 -> False.
Proof.
 intros h0.
 assert (h1 := l2 h0).
 assert (h2 := l3 h0).
 refine (simplify (Tatom false (Abnd 0%nat i3)) Tfalse (Abnd 0%nat i7) (List.cons r1 List.nil) h2 h1 _) ; finalize.
Qed.
End Generated_by_Gappa.
