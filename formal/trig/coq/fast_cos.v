Require Import Gappa.Gappa_library.
Section Generated_by_Gappa.
Notation r8 := (Float1 (1)).
Variable _kca : R.
Notation r7 := ((r8 - _kca)%R).
Variable _ksb : R.
Notation _kc := ((r7 + _ksb)%R).
Variable _eC : R.
Notation r11 := ((r8 + _eC)%R).
Notation r5 := ((_kc * r11)%R).
Variable _eCM : R.
Notation r18 := ((r8 + _eCM)%R).
Notation r17 := ((r11 * r18)%R).
Variable _m1 : R.
Notation r20 := ((r8 + _m1)%R).
Notation _X := ((r17 * r20)%R).
Notation r15 := ((_kca * _X)%R).
Variable _eS : R.
Notation r25 := ((r8 + _eS)%R).
Variable _eSN : R.
Notation r27 := ((r8 + _eSN)%R).
Notation r24 := ((r25 * r27)%R).
Variable _m2 : R.
Notation r29 := ((r8 + _m2)%R).
Notation _Z := ((r24 * r29)%R).
Notation r22 := ((_ksb * _Z)%R).
Notation r14 := ((r15 - r22)%R).
Variable _a1 : R.
Notation r31 := ((r8 + _a1)%R).
Notation r13 := ((r14 * r31)%R).
Notation r4 := ((r5 + r13)%R).
Variable _a2 : R.
Notation r33 := ((r8 + _a2)%R).
Notation r3 := ((r4 * r33)%R).
Variable _er : R.
Notation r35 := ((r8 + _er)%R).
Notation _R := ((r3 * r35)%R).
Notation r1 := ((_R - r8)%R).
Notation r42 := ((_kc * _eC)%R).
Notation r46 := ((_X - r8)%R).
Notation r45 := ((_kca * r46)%R).
Notation r48 := ((_Z - r8)%R).
Notation r47 := ((_ksb * r48)%R).
Notation r44 := ((r45 - r47)%R).
Notation r43 := ((r44 * r31)%R).
Notation r41 := ((r42 + r43)%R).
Notation r50 := ((_kca - _ksb)%R).
Notation r49 := ((r50 * _a1)%R).
Notation r40 := ((r41 + r49)%R).
Notation r51 := ((r4 * _a2)%R).
Notation r39 := ((r40 + r51)%R).
Notation r38 := ((r39 * r35)%R).
Notation r37 := ((r38 + _er)%R).
Hypothesis a1 : r1 = r37.
Lemma b1 : r1 = r37.
 apply a1.
Qed.
Definition f1 := Float2 (-261) (-23).
Definition f2 := Float2 (261) (-23).
Definition i1 := makepairF f1 f2.
Notation p1 := (BND _kca i1). (* BND(kca, [-3.11136e-05, 3.11136e-05]) *)
Definition f3 := Float2 (-515) (-16).
Definition f4 := Float2 (515) (-16).
Definition i2 := makepairF f3 f4.
Notation p2 := (BND _ksb i2). (* BND(ksb, [-0.00785828, 0.00785828]) *)
Definition s11 := (p1 /\ p2).
Definition f5 := Float2 (-953) (-117).
Definition f6 := Float2 (953) (-117).
Definition i3 := makepairF f5 f6.
Notation p3 := (BND _eS i3). (* BND(eS, [-5.73566e-33, 5.73566e-33]) *)
Definition s10 := (s11 /\ p3).
Notation p4 := (BND _eC i3). (* BND(eC, [-5.73566e-33, 5.73566e-33]) *)
Definition s9 := (s10 /\ p4).
Definition f7 := Float2 (-1) (-65).
Definition f8 := Float2 (1) (-65).
Definition i4 := makepairF f7 f8.
Notation p5 := (BND _eSN i4). (* BND(eSN, [-2.71051e-20, 2.71051e-20]) *)
Definition s8 := (s9 /\ p5).
Notation p6 := (BND _eCM i4). (* BND(eCM, [-2.71051e-20, 2.71051e-20]) *)
Definition s7 := (s8 /\ p6).
Definition f9 := Float2 (-5) (-106).
Definition f10 := Float2 (5) (-106).
Definition i5 := makepairF f9 f10.
Notation p7 := (BND _m1 i5). (* BND(m1, [-6.16298e-32, 6.16298e-32]) *)
Definition s6 := (s7 /\ p7).
Notation p8 := (BND _m2 i5). (* BND(m2, [-6.16298e-32, 6.16298e-32]) *)
Definition s5 := (s6 /\ p8).
Definition f11 := Float2 (-97) (-111).
Definition f12 := Float2 (97) (-111).
Definition i6 := makepairF f11 f12.
Notation p9 := (BND _a1 i6). (* BND(a1, [-3.7363e-32, 3.7363e-32]) *)
Definition s4 := (s5 /\ p9).
Notation p10 := (BND _a2 i6). (* BND(a2, [-3.7363e-32, 3.7363e-32]) *)
Definition s3 := (s4 /\ p10).
Definition f13 := Float2 (-1) (-104).
Definition f14 := Float2 (1) (-104).
Definition i7 := makepairF f13 f14.
Notation p11 := (BND _er i7). (* BND(er, [-4.93038e-32, 4.93038e-32]) *)
Definition s2 := (s3 /\ p11).
Definition f15 := Float2 (-1) (-62).
Definition f16 := Float2 (1) (-62).
Definition i8 := makepairF f15 f16.
Notation p12 := (BND r1 i8). (* BND(R - 1, [-2.1684e-19, 2.1684e-19]) *)
Definition s12 := (not p12).
Definition s1 := (s2 /\ s12).
Lemma l2 : s1 -> s12.
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj2 h1).
Qed.
Definition f17 := Float2 (-651916043307046525322797252598488773079722453545291120518780556357518493195129202053653515151928804116788022701754338069) (-470).
Definition f18 := Float2 (651916043307046525322797252598488773079722453545291120518780556357518493195129202053653515151928804116788022701754338069) (-470).
Definition i9 := makepairF f17 f18.
Notation p13 := (BND r1 i9). (* BND(R - 1, [-2.13842e-22, 2.13842e-22]) *)
Notation p14 := (BND r37 i9). (* BND((kc * eC + (kca * (X - 1) - ksb * (Z - 1)) * (1 + a1) + (kca - ksb) * a1 + (kc * (1 + eC) + (kca * X - ksb * Z) * (1 + a1)) * a2) * (1 + er) + er, [-2.13842e-22, 2.13842e-22]) *)
Definition f19 := Float2 (-651916043156739800025271926013562014885204883793247437388648084632251871017067824446318574770252068220162825707710499605) (-470).
Definition f20 := Float2 (651916043156739800025271926013562014885204883793247437388648084632251871017067824446318574770252068220162825707710499605) (-470).
Definition i10 := makepairF f19 f20.
Notation p15 := (BND r38 i10). (* BND((kc * eC + (kca * (X - 1) - ksb * (Z - 1)) * (1 + a1) + (kca - ksb) * a1 + (kc * (1 + eC) + (kca * X - ksb * Z) * (1 + a1)) * a2) * (1 + er), [-2.13842e-22, 2.13842e-22]) *)
Definition f21 := Float2 (-1303832086313479600050543852027059745885418176841848325220711318509547647140447702589664177382468845095418023089671484041) (-471).
Definition f22 := Float2 (1303832086313479600050543852027059745885418176841848325220711318509547647140447702589664177382468845095418023089671484041) (-471).
Definition i11 := makepairF f21 f22.
Notation p16 := (BND r39 i11). (* BND(kc * eC + (kca * (X - 1) - ksb * (Z - 1)) * (1 + a1) + (kca - ksb) * a1 + (kc * (1 + eC) + (kca * X - ksb * Z) * (1 + a1)) * a2, [-2.13842e-22, 2.13842e-22]) *)
Definition f23 := Float2 (-2316071043541392575203760005840797186567823049224057265437563330246597798158999803521460824540706485959665) (-422).
Definition f24 := Float2 (2316071043541392575203760005840797186567823049224057265437563330246597798158999803521460824540706485959665) (-422).
Definition i12 := makepairF f23 f24.
Notation p17 := (BND r40 i12). (* BND(kc * eC + (kca * (X - 1) - ksb * (Z - 1)) * (1 + a1) + (kca - ksb) * a1, [-2.13842e-22, 2.13842e-22]) *)
Definition f25 := Float2 (-2316071043538199980340202905133642107369056388472244501451519161125668845552887483220297536822069627583473) (-422).
Definition f26 := Float2 (2316071043538199980340202905133642107369056388472244501451519161125668845552887483220297536822069627583473) (-422).
Definition i13 := makepairF f25 f26.
Notation p18 := (BND r41 i13). (* BND(kc * eC + (kca * (X - 1) - ksb * (Z - 1)) * (1 + a1), [-2.13842e-22, 2.13842e-22]) *)
Definition f27 := Float2 (-8057413917) (-140).
Definition f28 := Float2 (8057413917) (-140).
Definition i14 := makepairF f27 f28.
Notation p19 := (BND r42 i14). (* BND(kc * eC, [-5.78091e-33, 5.78091e-33]) *)
Definition f29 := Float2 (7) (-3).
Definition f30 := Float2 (8454789) (-23).
Definition i15 := makepairF f29 f30.
Notation p20 := (BND _kc i15). (* BND(kc, [0.875, 1.00789]) *)
Definition f31 := Float2 (15) (-4).
Definition f32 := Float2 (8388869) (-23).
Definition i16 := makepairF f31 f32.
Notation p21 := (BND r7 i16). (* BND(1 - kca, [0.9375, 1.00003]) *)
Definition f33 := Float2 (1) (0).
Definition i17 := makepairF f33 f33.
Notation p22 := (BND r8 i17). (* BND(1, [1, 1]) *)
Lemma t1 : p22.
Proof.
 refine (constant1 _ i17 _) ; finalize.
Qed.
Lemma l12 : s1 -> p22 (* BND(1, [1, 1]) *).
Proof.
 intros h0.
 apply t1.
Qed.
Lemma l23 : s1 -> s2.
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj1 h1).
Qed.
Lemma l22 : s1 -> s3.
Proof.
 intros h0.
 assert (h1 := l23 h0).
 exact (proj1 h1).
Qed.
Lemma l21 : s1 -> s4.
Proof.
 intros h0.
 assert (h1 := l22 h0).
 exact (proj1 h1).
Qed.
Lemma l20 : s1 -> s5.
Proof.
 intros h0.
 assert (h1 := l21 h0).
 exact (proj1 h1).
Qed.
Lemma l19 : s1 -> s6.
Proof.
 intros h0.
 assert (h1 := l20 h0).
 exact (proj1 h1).
Qed.
Lemma l18 : s1 -> s7.
Proof.
 intros h0.
 assert (h1 := l19 h0).
 exact (proj1 h1).
Qed.
Lemma l17 : s1 -> s8.
Proof.
 intros h0.
 assert (h1 := l18 h0).
 exact (proj1 h1).
Qed.
Lemma l16 : s1 -> s9.
Proof.
 intros h0.
 assert (h1 := l17 h0).
 exact (proj1 h1).
Qed.
Lemma l15 : s1 -> s10.
Proof.
 intros h0.
 assert (h1 := l16 h0).
 exact (proj1 h1).
Qed.
Lemma l14 : s1 -> s11.
Proof.
 intros h0.
 assert (h1 := l15 h0).
 exact (proj1 h1).
Qed.
Lemma l13 : s1 -> p1 (* BND(kca, [-3.11136e-05, 3.11136e-05]) *).
Proof.
 intros h0.
 assert (h1 := l14 h0).
 exact (proj1 h1).
Qed.
Definition f34 := Float2 (1) (-4).
Definition i18 := makepairF f1 f34.
Notation p23 := (BND _kca i18). (* BND(kca, [-3.11136e-05, 0.0625]) *)
Lemma t2 : p22 -> p23 -> p21.
Proof.
 intros h0 h1.
 refine (sub r8 _kca i17 i18 i16 h0 h1 _) ; finalize.
Qed.
Lemma l11 : s1 -> p21 (* BND(1 - kca, [0.9375, 1.00003]) *).
Proof.
 intros h0.
 assert (h1 := l12 h0).
 assert (h2 := l13 h0).
 apply t2. exact h1. refine (subset _kca i1 i18 h2 _) ; finalize.
Qed.
Lemma l24 : s1 -> p2 (* BND(ksb, [-0.00785828, 0.00785828]) *).
Proof.
 intros h0.
 assert (h1 := l14 h0).
 exact (proj2 h1).
Qed.
Definition f35 := Float2 (-1) (-4).
Definition i19 := makepairF f35 f4.
Notation p24 := (BND _ksb i19). (* BND(ksb, [-0.0625, 0.00785828]) *)
Lemma t3 : p21 -> p24 -> p20.
Proof.
 intros h0 h1.
 refine (add r7 _ksb i16 i19 i15 h0 h1 _) ; finalize.
Qed.
Lemma l10 : s1 -> p20 (* BND(kc, [0.875, 1.00789]) *).
Proof.
 intros h0.
 assert (h1 := l11 h0).
 assert (h2 := l24 h0).
 apply t3. exact h1. refine (subset _ksb i2 i19 h2 _) ; finalize.
Qed.
Lemma l25 : s1 -> p4 (* BND(eC, [-5.73566e-33, 5.73566e-33]) *).
Proof.
 intros h0.
 assert (h1 := l16 h0).
 exact (proj2 h1).
Qed.
Definition f36 := Float2 (1) (-1).
Definition i20 := makepairF f36 f30.
Notation p25 := (BND _kc i20). (* BND(kc, [0.5, 1.00789]) *)
Lemma t4 : p25 -> p4 -> p19.
Proof.
 intros h0 h1.
 refine (mul_po _kc _eC i20 i3 i14 h0 h1 _) ; finalize.
Qed.
Lemma l9 : s1 -> p19 (* BND(kc * eC, [-5.78091e-33, 5.78091e-33]) *).
Proof.
 intros h0.
 assert (h1 := l10 h0).
 assert (h2 := l25 h0).
 apply t4. refine (subset _kc i15 i20 h1 _) ; finalize. exact h2.
Qed.
Definition f37 := Float2 (-2316071043475588430866832655047650297952291674467071891022100408857028563266073268324524000205709741521905) (-422).
Definition f38 := Float2 (2316071043475588430866832655047650297952291674467071891022100408857028563266073268324524000205709741521905) (-422).
Definition i21 := makepairF f37 f38.
Notation p26 := (BND r43 i21). (* BND((kca * (X - 1) - ksb * (Z - 1)) * (1 + a1), [-2.13842e-22, 2.13842e-22]) *)
Definition f39 := Float2 (-892118115191565467656985069878212891925420750166648694345551712694822289) (-311).
Definition f40 := Float2 (892118115191565467656985069878212891925420750166648694345551712694822289) (-311).
Definition i22 := makepairF f39 f40.
Notation p27 := (BND r44 i22). (* BND(kca * (X - 1) - ksb * (Z - 1), [-2.13842e-22, 2.13842e-22]) *)
Definition f41 := Float2 (-3518273040071902616437846258566863069348224049100124042008869570017809) (-311).
Definition f42 := Float2 (3518273040071902616437846258566863069348224049100124042008869570017809) (-311).
Definition i23 := makepairF f41 f42.
Notation p28 := (BND r45 i23). (* BND(kca * (X - 1), [-8.43336e-25, 8.43336e-25]) *)
Definition f43 := Float2 (-4503599627381689) (-117).
Definition f44 := Float2 (13479973333608822285202476086463076894054498272414268360187239731869) (-288).
Definition i24 := makepairF f43 f44.
Notation p29 := (BND r46 i24). (* BND(X - 1, [-2.71051e-20, 2.71051e-20]) *)
Definition f45 := Float2 (166153499473114484108472282907661383) (-117).
Definition f46 := Float2 (497323236409786642168862221480429662385658626883810794334518475165573765372720615264925) (-288).
Definition i25 := makepairF f45 f46.
Notation p30 := (BND _X i25). (* BND(X, [1, 1]) *)
Definition f47 := Float2 (166153499473114484108472282907671623) (-117).
Definition f48 := Float2 (6129982163463555433599541608074386378082136861674832825) (-182).
Definition i26 := makepairF f47 f48.
Notation p31 := (BND r17 i26). (* BND((1 + eC) * (1 + eCM), [1, 1]) *)
Definition f49 := Float2 (166153499473114484112975882535042119) (-117).
Definition f50 := Float2 (166153499473114484112975882535044025) (-117).
Definition i27 := makepairF f49 f50.
Notation p32 := (BND r11 i27). (* BND(1 + eC, [1, 1]) *)
Lemma t5 : p22 -> p4 -> p32.
Proof.
 intros h0 h1.
 refine (add r8 _eC i17 i3 i27 h0 h1 _) ; finalize.
Qed.
Lemma l32 : s1 -> p32 (* BND(1 + eC, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l12 h0).
 assert (h2 := l25 h0).
 apply t5. exact h1. exact h2.
Qed.
Definition f51 := Float2 (36893488147419103231) (-65).
Definition f52 := Float2 (36893488147419103233) (-65).
Definition i28 := makepairF f51 f52.
Notation p33 := (BND r18 i28). (* BND(1 + eCM, [1, 1]) *)
Lemma l34 : s1 -> p6 (* BND(eCM, [-2.71051e-20, 2.71051e-20]) *).
Proof.
 intros h0.
 assert (h1 := l18 h0).
 exact (proj2 h1).
Qed.
Lemma t6 : p22 -> p6 -> p33.
Proof.
 intros h0 h1.
 refine (add r8 _eCM i17 i4 i28 h0 h1 _) ; finalize.
Qed.
Lemma l33 : s1 -> p33 (* BND(1 + eCM, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l12 h0).
 assert (h2 := l34 h0).
 apply t6. exact h1. exact h2.
Qed.
Lemma t7 : p32 -> p33 -> p31.
Proof.
 intros h0 h1.
 refine (mul_pp r11 r18 i27 i28 i26 h0 h1 _) ; finalize.
Qed.
Lemma l31 : s1 -> p31 (* BND((1 + eC) * (1 + eCM), [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l32 h0).
 assert (h2 := l33 h0).
 apply t7. exact h1. exact h2.
Qed.
Definition f53 := Float2 (81129638414606681695789005144059) (-106).
Definition f54 := Float2 (81129638414606681695789005144069) (-106).
Definition i29 := makepairF f53 f54.
Notation p34 := (BND r20 i29). (* BND(1 + m1, [1, 1]) *)
Lemma l36 : s1 -> p7 (* BND(m1, [-6.16298e-32, 6.16298e-32]) *).
Proof.
 intros h0.
 assert (h1 := l19 h0).
 exact (proj2 h1).
Qed.
Lemma t8 : p22 -> p7 -> p34.
Proof.
 intros h0 h1.
 refine (add r8 _m1 i17 i5 i29 h0 h1 _) ; finalize.
Qed.
Lemma l35 : s1 -> p34 (* BND(1 + m1, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l12 h0).
 assert (h2 := l36 h0).
 apply t8. exact h1. exact h2.
Qed.
Lemma t9 : p31 -> p34 -> p30.
Proof.
 intros h0 h1.
 refine (mul_pp r17 r20 i26 i29 i25 h0 h1 _) ; finalize.
Qed.
Lemma l30 : s1 -> p30 (* BND(X, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l31 h0).
 assert (h2 := l35 h0).
 apply t9. exact h1. exact h2.
Qed.
Lemma t10 : p30 -> p22 -> p29.
Proof.
 intros h0 h1.
 refine (sub _X r8 i25 i17 i24 h0 h1 _) ; finalize.
Qed.
Lemma l29 : s1 -> p29 (* BND(X - 1, [-2.71051e-20, 2.71051e-20]) *).
Proof.
 intros h0.
 assert (h1 := l30 h0).
 assert (h2 := l12 h0).
 apply t10. exact h1. exact h2.
Qed.
Lemma t11 : p1 -> p29 -> p28.
Proof.
 intros h0 h1.
 refine (mul_oo _kca r46 i1 i24 i23 h0 h1 _) ; finalize.
Qed.
Lemma l28 : s1 -> p28 (* BND(kca * (X - 1), [-8.43336e-25, 8.43336e-25]) *).
Proof.
 intros h0.
 assert (h1 := l13 h0).
 assert (h2 := l29 h0).
 apply t11. exact h1. exact h2.
Qed.
Definition f55 := Float2 (-6942186266808543476879275184528484600438066610293348205496428461912535) (-304).
Definition f56 := Float2 (6942186266808543476879275184528484600438066610293348205496428461912535) (-304).
Definition i30 := makepairF f55 f56.
Notation p35 := (BND r47 i30). (* BND(ksb * (Z - 1), [-2.12999e-22, 2.12999e-22]) *)
Notation p36 := (BND r48 i24). (* BND(Z - 1, [-2.71051e-20, 2.71051e-20]) *)
Notation p37 := (BND _Z i25). (* BND(Z, [1, 1]) *)
Notation p38 := (BND r24 i26). (* BND((1 + eS) * (1 + eSN), [1, 1]) *)
Notation p39 := (BND r25 i27). (* BND(1 + eS, [1, 1]) *)
Lemma l42 : s1 -> p3 (* BND(eS, [-5.73566e-33, 5.73566e-33]) *).
Proof.
 intros h0.
 assert (h1 := l15 h0).
 exact (proj2 h1).
Qed.
Lemma t12 : p22 -> p3 -> p39.
Proof.
 intros h0 h1.
 refine (add r8 _eS i17 i3 i27 h0 h1 _) ; finalize.
Qed.
Lemma l41 : s1 -> p39 (* BND(1 + eS, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l12 h0).
 assert (h2 := l42 h0).
 apply t12. exact h1. exact h2.
Qed.
Notation p40 := (BND r27 i28). (* BND(1 + eSN, [1, 1]) *)
Lemma l44 : s1 -> p5 (* BND(eSN, [-2.71051e-20, 2.71051e-20]) *).
Proof.
 intros h0.
 assert (h1 := l17 h0).
 exact (proj2 h1).
Qed.
Lemma t13 : p22 -> p5 -> p40.
Proof.
 intros h0 h1.
 refine (add r8 _eSN i17 i4 i28 h0 h1 _) ; finalize.
Qed.
Lemma l43 : s1 -> p40 (* BND(1 + eSN, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l12 h0).
 assert (h2 := l44 h0).
 apply t13. exact h1. exact h2.
Qed.
Lemma t14 : p39 -> p40 -> p38.
Proof.
 intros h0 h1.
 refine (mul_pp r25 r27 i27 i28 i26 h0 h1 _) ; finalize.
Qed.
Lemma l40 : s1 -> p38 (* BND((1 + eS) * (1 + eSN), [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l41 h0).
 assert (h2 := l43 h0).
 apply t14. exact h1. exact h2.
Qed.
Notation p41 := (BND r29 i29). (* BND(1 + m2, [1, 1]) *)
Lemma l46 : s1 -> p8 (* BND(m2, [-6.16298e-32, 6.16298e-32]) *).
Proof.
 intros h0.
 assert (h1 := l20 h0).
 exact (proj2 h1).
Qed.
Lemma t15 : p22 -> p8 -> p41.
Proof.
 intros h0 h1.
 refine (add r8 _m2 i17 i5 i29 h0 h1 _) ; finalize.
Qed.
Lemma l45 : s1 -> p41 (* BND(1 + m2, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l12 h0).
 assert (h2 := l46 h0).
 apply t15. exact h1. exact h2.
Qed.
Lemma t16 : p38 -> p41 -> p37.
Proof.
 intros h0 h1.
 refine (mul_pp r24 r29 i26 i29 i25 h0 h1 _) ; finalize.
Qed.
Lemma l39 : s1 -> p37 (* BND(Z, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l40 h0).
 assert (h2 := l45 h0).
 apply t16. exact h1. exact h2.
Qed.
Lemma t17 : p37 -> p22 -> p36.
Proof.
 intros h0 h1.
 refine (sub _Z r8 i25 i17 i24 h0 h1 _) ; finalize.
Qed.
Lemma l38 : s1 -> p36 (* BND(Z - 1, [-2.71051e-20, 2.71051e-20]) *).
Proof.
 intros h0.
 assert (h1 := l39 h0).
 assert (h2 := l12 h0).
 apply t17. exact h1. exact h2.
Qed.
Lemma t18 : p2 -> p36 -> p35.
Proof.
 intros h0 h1.
 refine (mul_oo _ksb r48 i2 i24 i30 h0 h1 _) ; finalize.
Qed.
Lemma l37 : s1 -> p35 (* BND(ksb * (Z - 1), [-2.12999e-22, 2.12999e-22]) *).
Proof.
 intros h0.
 assert (h1 := l24 h0).
 assert (h2 := l38 h0).
 apply t18. exact h1. exact h2.
Qed.
Lemma t19 : p28 -> p35 -> p27.
Proof.
 intros h0 h1.
 refine (sub r45 r47 i23 i30 i22 h0 h1 _) ; finalize.
Qed.
Lemma l27 : s1 -> p27 (* BND(kca * (X - 1) - ksb * (Z - 1), [-2.13842e-22, 2.13842e-22]) *).
Proof.
 intros h0.
 assert (h1 := l28 h0).
 assert (h2 := l37 h0).
 apply t19. exact h1. exact h2.
Qed.
Definition f57 := Float2 (2596148429267413814265248164610145) (-111).
Definition i31 := makepairF f36 f57.
Notation p42 := (BND r31 i31). (* BND(1 + a1, [0.5, 1]) *)
Lemma l48 : s1 -> p9 (* BND(a1, [-3.7363e-32, 3.7363e-32]) *).
Proof.
 intros h0.
 assert (h1 := l21 h0).
 exact (proj2 h1).
Qed.
Definition f58 := Float2 (-1) (-1).
Definition i32 := makepairF f58 f12.
Notation p43 := (BND _a1 i32). (* BND(a1, [-0.5, 3.7363e-32]) *)
Lemma t20 : p22 -> p43 -> p42.
Proof.
 intros h0 h1.
 refine (add r8 _a1 i17 i32 i31 h0 h1 _) ; finalize.
Qed.
Lemma l47 : s1 -> p42 (* BND(1 + a1, [0.5, 1]) *).
Proof.
 intros h0.
 assert (h1 := l12 h0).
 assert (h2 := l48 h0).
 apply t20. exact h1. refine (subset _a1 i6 i32 h2 _) ; finalize.
Qed.
Lemma t21 : p27 -> p42 -> p26.
Proof.
 intros h0 h1.
 refine (mul_op r44 r31 i22 i31 i21 h0 h1 _) ; finalize.
Qed.
Lemma l26 : s1 -> p26 (* BND((kca * (X - 1) - ksb * (Z - 1)) * (1 + a1), [-2.13842e-22, 2.13842e-22]) *).
Proof.
 intros h0.
 assert (h1 := l27 h0).
 assert (h2 := l47 h0).
 apply t21. exact h1. exact h2.
Qed.
Lemma t22 : p19 -> p26 -> p18.
Proof.
 intros h0 h1.
 refine (add r42 r43 i14 i21 i13 h0 h1 _) ; finalize.
Qed.
Lemma l8 : s1 -> p18 (* BND(kc * eC + (kca * (X - 1) - ksb * (Z - 1)) * (1 + a1), [-2.13842e-22, 2.13842e-22]) *).
Proof.
 intros h0.
 assert (h1 := l9 h0).
 assert (h2 := l26 h0).
 apply t22. exact h1. exact h2.
Qed.
Definition f59 := Float2 (-6419557) (-134).
Definition f60 := Float2 (6419557) (-134).
Definition i33 := makepairF f59 f60.
Notation p44 := (BND r49 i33). (* BND((kca - ksb) * a1, [-2.94772e-34, 2.94772e-34]) *)
Definition f61 := Float2 (-66181) (-23).
Definition f62 := Float2 (66181) (-23).
Definition i34 := makepairF f61 f62.
Notation p45 := (BND r50 i34). (* BND(kca - ksb, [-0.00788939, 0.00788939]) *)
Lemma t23 : p1 -> p2 -> p45.
Proof.
 intros h0 h1.
 refine (sub _kca _ksb i1 i2 i34 h0 h1 _) ; finalize.
Qed.
Lemma l50 : s1 -> p45 (* BND(kca - ksb, [-0.00788939, 0.00788939]) *).
Proof.
 intros h0.
 assert (h1 := l13 h0).
 assert (h2 := l24 h0).
 apply t23. exact h1. exact h2.
Qed.
Lemma t24 : p45 -> p9 -> p44.
Proof.
 intros h0 h1.
 refine (mul_oo r50 _a1 i34 i6 i33 h0 h1 _) ; finalize.
Qed.
Lemma l49 : s1 -> p44 (* BND((kca - ksb) * a1, [-2.94772e-34, 2.94772e-34]) *).
Proof.
 intros h0.
 assert (h1 := l50 h0).
 assert (h2 := l48 h0).
 apply t24. exact h1. exact h2.
Qed.
Lemma t25 : p18 -> p44 -> p17.
Proof.
 intros h0 h1.
 refine (add r41 r49 i13 i33 i12 h0 h1 _) ; finalize.
Qed.
Lemma l7 : s1 -> p17 (* BND(kc * eC + (kca * (X - 1) - ksb * (Z - 1)) * (1 + a1) + (kca - ksb) * a1, [-2.13842e-22, 2.13842e-22]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 assert (h2 := l49 h0).
 apply t25. exact h1. exact h2.
Qed.
Definition f63 := Float2 (-231403172788527002671456708643732015701585936658640502696671256464080665132284046494703179328735320431288103561) (-471).
Definition f64 := Float2 (231403172788527002671456708643732015701585936658640502696671256464080665132284046494703179328735320431288103561) (-471).
Definition i35 := makepairF f63 f64.
Notation p46 := (BND r51 i35). (* BND((kc * (1 + eC) + (kca * X - ksb * Z) * (1 + a1)) * a2, [-3.79526e-32, 3.79526e-32]) *)
Definition f65 := Float2 (305356764092076869504602667076264927936113400951608086032720833272188918937446989188886669629671350672215229441) (-367).
Definition i36 := makepairF f36 f65.
Notation p47 := (BND r4 i36). (* BND(kc * (1 + eC) + (kca * X - ksb * Z) * (1 + a1), [0.5, 1.01578]) *)
Definition f66 := Float2 (3) (-2).
Definition f67 := Float2 (1404792779656794136019063248922582337085725) (-140).
Definition i37 := makepairF f66 f67.
Notation p48 := (BND r5 i37). (* BND(kc * (1 + eC), [0.75, 1.00789]) *)
Definition i38 := makepairF f29 f50.
Notation p49 := (BND r11 i38). (* BND(1 + eC, [0.875, 1]) *)
Lemma t26 : p20 -> p49 -> p48.
Proof.
 intros h0 h1.
 refine (mul_pp _kc r11 i15 i38 i37 h0 h1 _) ; finalize.
Qed.
Lemma l53 : s1 -> p48 (* BND(kc * (1 + eC), [0.75, 1.00789]) *).
Proof.
 intros h0.
 assert (h1 := l10 h0).
 assert (h2 := l32 h0).
 apply t26. exact h1. refine (subset r11 i27 i38 h2 _) ; finalize.
Qed.
Definition f68 := Float2 (-1) (-2).
Definition f69 := Float2 (2371656748513108167406717286103247240104316942248825096042186049506072653452094182415517050715697180966896641) (-367).
Definition i39 := makepairF f68 f69.
Notation p50 := (BND r13 i39). (* BND((kca * X - ksb * Z) * (1 + a1), [-0.25, 0.00788939]) *)
Definition f70 := Float2 (-1) (-3).
Definition f71 := Float2 (32913349108836089765377470679796315486345273585797482179852767204932837366132023038848001425) (-311).
Definition i40 := makepairF f70 f71.
Notation p51 := (BND r14 i40). (* BND(kca * X - ksb * Z, [-0.125, 0.00788939]) *)
Definition f72 := Float2 (129801364702954313606073039806392141882656901616674617321309322018214752762280080584145425) (-311).
Definition i41 := makepairF f35 f72.
Notation p52 := (BND r15 i41). (* BND(kca * X, [-0.0625, 3.11136e-05]) *)
Definition f73 := Float2 (-1) (-5).
Definition i42 := makepairF f73 f2.
Notation p53 := (BND _kca i42). (* BND(kca, [-0.03125, 3.11136e-05]) *)
Definition i43 := makepairF f36 f46.
Notation p54 := (BND _X i43). (* BND(X, [0.5, 1]) *)
Lemma t27 : p53 -> p54 -> p52.
Proof.
 intros h0 h1.
 refine (mul_op _kca _X i42 i43 i41 h0 h1 _) ; finalize.
Qed.
Lemma l56 : s1 -> p52 (* BND(kca * X, [-0.0625, 3.11136e-05]) *).
Proof.
 intros h0.
 assert (h1 := l13 h0).
 assert (h2 := l30 h0).
 apply t27. refine (subset _kca i1 i42 h1 _) ; finalize. refine (subset _X i25 i43 h2 _) ; finalize.
Qed.
Definition f74 := Float2 (-256121466751040120716964044062421276128614192845162559082277014710270489166951116861436375) (-304).
Definition i44 := makepairF f74 f34.
Notation p55 := (BND r22 i44). (* BND(ksb * Z, [-0.00785828, 0.0625]) *)
Definition f75 := Float2 (1) (-5).
Definition i45 := makepairF f3 f75.
Notation p56 := (BND _ksb i45). (* BND(ksb, [-0.00785828, 0.03125]) *)
Notation p57 := (BND _Z i43). (* BND(Z, [0.5, 1]) *)
Lemma t28 : p56 -> p57 -> p55.
Proof.
 intros h0 h1.
 refine (mul_op _ksb _Z i45 i43 i44 h0 h1 _) ; finalize.
Qed.
Lemma l57 : s1 -> p55 (* BND(ksb * Z, [-0.00785828, 0.0625]) *).
Proof.
 intros h0.
 assert (h1 := l24 h0).
 assert (h2 := l39 h0).
 apply t28. refine (subset _ksb i2 i45 h1 _) ; finalize. refine (subset _Z i25 i43 h2 _) ; finalize.
Qed.
Lemma t29 : p52 -> p55 -> p51.
Proof.
 intros h0 h1.
 refine (sub r15 r22 i41 i44 i40 h0 h1 _) ; finalize.
Qed.
Lemma l55 : s1 -> p51 (* BND(kca * X - ksb * Z, [-0.125, 0.00788939]) *).
Proof.
 intros h0.
 assert (h1 := l56 h0).
 assert (h2 := l57 h0).
 apply t29. exact h1. exact h2.
Qed.
Lemma t30 : p51 -> p42 -> p50.
Proof.
 intros h0 h1.
 refine (mul_op r14 r31 i40 i31 i39 h0 h1 _) ; finalize.
Qed.
Lemma l54 : s1 -> p50 (* BND((kca * X - ksb * Z) * (1 + a1), [-0.25, 0.00788939]) *).
Proof.
 intros h0.
 assert (h1 := l55 h0).
 assert (h2 := l47 h0).
 apply t30. exact h1. exact h2.
Qed.
Lemma t31 : p48 -> p50 -> p47.
Proof.
 intros h0 h1.
 refine (add r5 r13 i37 i39 i36 h0 h1 _) ; finalize.
Qed.
Lemma l52 : s1 -> p47 (* BND(kc * (1 + eC) + (kca * X - ksb * Z) * (1 + a1), [0.5, 1.01578]) *).
Proof.
 intros h0.
 assert (h1 := l53 h0).
 assert (h2 := l54 h0).
 apply t31. exact h1. exact h2.
Qed.
Lemma l58 : s1 -> p10 (* BND(a2, [-3.7363e-32, 3.7363e-32]) *).
Proof.
 intros h0.
 assert (h1 := l22 h0).
 exact (proj2 h1).
Qed.
Lemma t32 : p47 -> p10 -> p46.
Proof.
 intros h0 h1.
 refine (mul_po r4 _a2 i36 i6 i35 h0 h1 _) ; finalize.
Qed.
Lemma l51 : s1 -> p46 (* BND((kc * (1 + eC) + (kca * X - ksb * Z) * (1 + a1)) * a2, [-3.79526e-32, 3.79526e-32]) *).
Proof.
 intros h0.
 assert (h1 := l52 h0).
 assert (h2 := l58 h0).
 apply t32. exact h1. exact h2.
Qed.
Lemma t33 : p17 -> p46 -> p16.
Proof.
 intros h0 h1.
 refine (add r40 r51 i12 i35 i11 h0 h1 _) ; finalize.
Qed.
Lemma l6 : s1 -> p16 (* BND(kc * eC + (kca * (X - 1) - ksb * (Z - 1)) * (1 + a1) + (kca - ksb) * a1 + (kc * (1 + eC) + (kca * X - ksb * Z) * (1 + a1)) * a2, [-2.13842e-22, 2.13842e-22]) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 assert (h2 := l51 h0).
 apply t33. exact h1. exact h2.
Qed.
Definition f76 := Float2 (20282409603651670423947251286017) (-104).
Definition i46 := makepairF f36 f76.
Notation p58 := (BND r35 i46). (* BND(1 + er, [0.5, 1]) *)
Lemma l60 : s1 -> p11 (* BND(er, [-4.93038e-32, 4.93038e-32]) *).
Proof.
 intros h0.
 assert (h1 := l23 h0).
 exact (proj2 h1).
Qed.
Definition i47 := makepairF f58 f14.
Notation p59 := (BND _er i47). (* BND(er, [-0.5, 4.93038e-32]) *)
Lemma t34 : p22 -> p59 -> p58.
Proof.
 intros h0 h1.
 refine (add r8 _er i17 i47 i46 h0 h1 _) ; finalize.
Qed.
Lemma l59 : s1 -> p58 (* BND(1 + er, [0.5, 1]) *).
Proof.
 intros h0.
 assert (h1 := l12 h0).
 assert (h2 := l60 h0).
 apply t34. exact h1. refine (subset _er i7 i47 h2 _) ; finalize.
Qed.
Lemma t35 : p16 -> p58 -> p15.
Proof.
 intros h0 h1.
 refine (mul_op r39 r35 i11 i46 i10 h0 h1 _) ; finalize.
Qed.
Lemma l5 : s1 -> p15 (* BND((kc * eC + (kca * (X - 1) - ksb * (Z - 1)) * (1 + a1) + (kca - ksb) * a1 + (kc * (1 + eC) + (kca * X - ksb * Z) * (1 + a1)) * a2) * (1 + er), [-2.13842e-22, 2.13842e-22]) *).
Proof.
 intros h0.
 assert (h1 := l6 h0).
 assert (h2 := l59 h0).
 apply t35. exact h1. exact h2.
Qed.
Lemma t36 : p15 -> p11 -> p14.
Proof.
 intros h0 h1.
 refine (add r38 _er i10 i7 i9 h0 h1 _) ; finalize.
Qed.
Lemma l4 : s1 -> p14 (* BND((kc * eC + (kca * (X - 1) - ksb * (Z - 1)) * (1 + a1) + (kca - ksb) * a1 + (kc * (1 + eC) + (kca * X - ksb * Z) * (1 + a1)) * a2) * (1 + er) + er, [-2.13842e-22, 2.13842e-22]) *).
Proof.
 intros h0.
 assert (h1 := l5 h0).
 assert (h2 := l60 h0).
 apply t36. exact h1. exact h2.
Qed.
Definition f77 := Float2 (0) (0).
Definition i48 := makepairF f77 f77.
Notation p60 := (REL r1 r37 i48). (* REL(R - 1, (kc * eC + (kca * (X - 1) - ksb * (Z - 1)) * (1 + a1) + (kca - ksb) * a1 + (kc * (1 + eC) + (kca * X - ksb * Z) * (1 + a1)) * a2) * (1 + er) + er, [0, 0]) *)
Notation p61 := (r1 = r37). (* EQL(R - 1, (kc * eC + (kca * (X - 1) - ksb * (Z - 1)) * (1 + a1) + (kca - ksb) * a1 + (kc * (1 + eC) + (kca * X - ksb * Z) * (1 + a1)) * a2) * (1 + er) + er) *)
Lemma t37 : p61.
Proof.
 refine (b1) ; finalize.
Qed.
Lemma l62 : s1 -> p61 (* EQL(R - 1, (kc * eC + (kca * (X - 1) - ksb * (Z - 1)) * (1 + a1) + (kca - ksb) * a1 + (kc * (1 + eC) + (kca * X - ksb * Z) * (1 + a1)) * a2) * (1 + er) + er) *).
Proof.
 intros h0.
 apply t37.
Qed.
Notation p62 := (REL r37 r37 i48). (* REL((kc * eC + (kca * (X - 1) - ksb * (Z - 1)) * (1 + a1) + (kca - ksb) * a1 + (kc * (1 + eC) + (kca * X - ksb * Z) * (1 + a1)) * a2) * (1 + er) + er, (kc * eC + (kca * (X - 1) - ksb * (Z - 1)) * (1 + a1) + (kca - ksb) * a1 + (kc * (1 + eC) + (kca * X - ksb * Z) * (1 + a1)) * a2) * (1 + er) + er, [0, 0]) *)
Lemma t38 : p62.
Proof.
 refine (rel_refl r37 i48 _) ; finalize.
Qed.
Lemma l63 : s1 -> p62 (* REL((kc * eC + (kca * (X - 1) - ksb * (Z - 1)) * (1 + a1) + (kca - ksb) * a1 + (kc * (1 + eC) + (kca * X - ksb * Z) * (1 + a1)) * a2) * (1 + er) + er, (kc * eC + (kca * (X - 1) - ksb * (Z - 1)) * (1 + a1) + (kca - ksb) * a1 + (kc * (1 + eC) + (kca * X - ksb * Z) * (1 + a1)) * a2) * (1 + er) + er, [0, 0]) *).
Proof.
 intros h0.
 apply t38.
Qed.
Lemma t39 : p61 -> p62 -> p60.
Proof.
 intros h0 h1.
 refine (rel_rewrite_1 r1 r37 r37 i48 h0 h1) ; finalize.
Qed.
Lemma l61 : s1 -> p60 (* REL(R - 1, (kc * eC + (kca * (X - 1) - ksb * (Z - 1)) * (1 + a1) + (kca - ksb) * a1 + (kc * (1 + eC) + (kca * X - ksb * Z) * (1 + a1)) * a2) * (1 + er) + er, [0, 0]) *).
Proof.
 intros h0.
 assert (h1 := l62 h0).
 assert (h2 := l63 h0).
 apply t39. exact h1. exact h2.
Qed.
Lemma t40 : p14 -> p60 -> p13.
Proof.
 intros h0 h1.
 refine (bnd_of_bnd_rel_o r1 r37 i9 i48 i9 h0 h1 _) ; finalize.
Qed.
Lemma l3 : s1 -> p13 (* BND(R - 1, [-2.13842e-22, 2.13842e-22]) *).
Proof.
 intros h0.
 assert (h1 := l4 h0).
 assert (h2 := l61 h0).
 apply t40. exact h1. exact h2.
Qed.
Lemma l1 : s1 -> False.
Proof.
 intros h0.
 assert (h1 := l2 h0).
 assert (h2 := l3 h0).
 refine (simplify (Tatom false (Abnd 0%nat i8)) Tfalse (Abnd 0%nat i9) (List.cons r1 List.nil) h2 h1 _) ; finalize.
Qed.
End Generated_by_Gappa.
