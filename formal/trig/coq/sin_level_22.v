Require Import Gappa.Gappa_library.
Section Generated_by_Gappa.
Notation r4 := (Float1 (1)).
Variable _s : R.
Notation r12 := (Float1 (1980)).
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
Definition f3 := Float2 (638924498605806299368054294924434653212343422968245735599923775525683329482177570925668153872800898027384730901790356053) (-398).
Definition f4 := Float2 (1) (0).
Definition i2 := makepairF f3 f4.
Notation p2 := (BND _Xn i2). (* BND(Xn, [0.989718, 1]) *)
Definition s7 := (p1 /\ p2).
Definition i3 := makepairF f1 f1.
Notation p3 := (BND _En i3). (* BND(En, [0, 0]) *)
Definition s6 := (s7 /\ p3).
Definition f5 := Float2 (-1) (-255).
Definition f6 := Float2 (1) (-255).
Definition i4 := makepairF f5 f6.
Notation p4 := (BND _kk i4). (* BND(kk, [-1.72723e-77, 1.72723e-77]) *)
Definition s5 := (s6 /\ p4).
Definition i5 := makepairF f5 f1.
Notation p5 := (BND _ma i5). (* BND(ma, [-1.72723e-77, 0]) *)
Definition s4 := (s5 /\ p5).
Notation p6 := (BND _mb i5). (* BND(mb, [-1.72723e-77, 0]) *)
Definition s3 := (s4 /\ p6).
Definition f7 := Float2 (-1) (-254).
Definition f8 := Float2 (1) (-254).
Definition i6 := makepairF f7 f8.
Notation p7 := (BND _sa i6). (* BND(sa, [-3.45447e-77, 3.45447e-77]) *)
Definition s2 := (s3 /\ p7).
Definition f9 := Float2 (-259) (-262).
Definition f10 := Float2 (259) (-262).
Definition i7 := makepairF f9 f10.
Notation p8 := (BND r1 i7). (* BND(H - X, [-3.49495e-77, 3.49495e-77]) *)
Definition s8 := (not p8).
Definition s1 := (s2 /\ s8).
Lemma l2 : s1 -> s8.
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj2 h1).
Qed.
Definition f11 := Float2 (-1291326057836042414722344592787017308108625658916923209259255131833970540615193462023270567642110690089330530035822154427) (-653).
Definition f12 := Float2 (1291728295421218654511114606358040049996171183921546114947106038961263999828739191440166349646194238832088418134718969905) (-653).
Definition i8 := makepairF f11 f12.
Notation p9 := (BND r1 i8). (* BND(H - X, [-3.45501e-77, 3.45608e-77]) *)
Notation p10 := (BND r25 i8). (* BND(-(s * (1 / 1980) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1))) + sa, [-3.45501e-77, 3.45608e-77]) *)
Definition f13 := Float2 (-201118792588119894385006785511370943772762502311452843925453563646729606772864708447891002041774371378944049448407739) (-653).
Definition f14 := Float2 (603356377764359683155020356534112831318287506934358531776360690940188820318594125343673006125323114136832148345223217) (-653).
Definition i9 := makepairF f13 f14.
Notation p11 := (BND r26 i9). (* BND(-(s * (1 / 1980) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1))), [-5.38103e-81, 1.61431e-80]) *)
Definition f15 := Float2 (-603356377764359683155020356534112831318287506934358531776360690940188820318594125343673006125323114136832148345223217) (-653).
Definition f16 := Float2 (201118792588119894385006785511370943772762502311452843925453563646729606772864708447891002041774371378944049448407739) (-653).
Definition i10 := makepairF f15 f16.
Notation p12 := (BND r27 i10). (* BND(s * (1 / 1980) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1)), [-1.61431e-80, 5.38103e-81]) *)
Definition f17 := Float2 (201118792588119894385006785511370943772762502311452843925453563646729606772864708447891002041774371378944049448407739) (-398).
Definition i11 := makepairF f1 f17.
Notation p13 := (BND r9 i11). (* BND(s * (1 / 1980), [0, 0.00031154]) *)
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
Definition f18 := Float2 (1) (-11).
Definition f19 := Float2 (163020825636799784700499947727462870854148092981642898537289100791707551895002600671063469272735974206812068937673453) (-397).
Definition i12 := makepairF f18 f19.
Notation p14 := (BND r11 i12). (* BND(1 / 1980, [0.000488281, 0.000505051]) *)
Definition i13 := makepairF f4 f4.
Notation p15 := (BND r4 i13). (* BND(1, [1, 1]) *)
Lemma t1 : p15.
Proof.
 refine (constant1 _ i13 _) ; finalize.
Qed.
Lemma l16 : s1 -> p15 (* BND(1, [1, 1]) *).
Proof.
 intros h0.
 apply t1.
Qed.
Definition f20 := Float2 (495) (2).
Definition f21 := Float2 (1) (11).
Definition i14 := makepairF f20 f21.
Notation p16 := (BND r12 i14). (* BND(1980, [1980, 2048]) *)
Lemma t2 : p16.
Proof.
 refine (constant1 _ i14 _) ; finalize.
Qed.
Lemma l17 : s1 -> p16 (* BND(1980, [1980, 2048]) *).
Proof.
 intros h0.
 apply t2.
Qed.
Lemma t3 : p15 -> p16 -> p14.
Proof.
 intros h0 h1.
 refine (div_pp r4 r12 i13 i14 i12 h0 h1 _) ; finalize.
Qed.
Lemma l15 : s1 -> p14 (* BND(1 / 1980, [0.000488281, 0.000505051]) *).
Proof.
 intros h0.
 assert (h1 := l16 h0).
 assert (h2 := l17 h0).
 apply t3. exact h1. exact h2.
Qed.
Definition f22 := Float2 (1555528161423739808134036856689509643242459978815143089735929906330174302383875479401656968916848653634020382452528605) (-390).
Definition i15 := makepairF f1 f22.
Notation p17 := (BND _s i15). (* BND(s, [0, 0.61685]) *)
Lemma t4 : p17 -> p14 -> p13.
Proof.
 intros h0 h1.
 refine (mul_pp _s r11 i15 i12 i11 h0 h1 _) ; finalize.
Qed.
Lemma l7 : s1 -> p13 (* BND(s * (1 / 1980), [0, 0.00031154]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 assert (h2 := l15 h0).
 apply t4. refine (subset _s i1 i15 h1 _) ; finalize. exact h2.
Qed.
Definition f23 := Float2 (-3) (-255).
Definition i16 := makepairF f23 f6.
Notation p18 := (BND r28 i16). (* BND(En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1), [-5.1817e-77, 1.72723e-77]) *)
Lemma l19 : s1 -> p3 (* BND(En, [0, 0]) *).
Proof.
 intros h0.
 assert (h1 := l10 h0).
 exact (proj2 h1).
Qed.
Notation p19 := (BND r29 i16). (* BND(Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1), [-5.1817e-77, 1.72723e-77]) *)
Definition f24 := Float2 (1) (-1).
Definition i17 := makepairF f24 f4.
Notation p20 := (BND _Hn i17). (* BND(Hn, [0.5, 1]) *)
Lemma l22 : s1 -> p2 (* BND(Xn, [0.989718, 1]) *).
Proof.
 intros h0.
 assert (h1 := l9 h0).
 exact (proj2 h1).
Qed.
Notation p21 := (BND _Xn i17). (* BND(Xn, [0.5, 1]) *)
Lemma t5 : p21 -> p3 -> p20.
Proof.
 intros h0 h1.
 refine (add _Xn _En i17 i3 i17 h0 h1 _) ; finalize.
Qed.
Lemma l21 : s1 -> p20 (* BND(Hn, [0.5, 1]) *).
Proof.
 intros h0.
 assert (h1 := l22 h0).
 assert (h2 := l19 h0).
 apply t5. refine (subset _Xn i2 i17 h1 _) ; finalize. exact h2.
Qed.
Notation p22 := (BND r30 i16). (* BND((1 + kk) * (1 + ma) * (1 + mb) - 1, [-5.1817e-77, 1.72723e-77]) *)
Definition f25 := Float2 (57896044618658097711785492504343953926634992332820282019728792003956564819965) (-255).
Definition f26 := Float2 (57896044618658097711785492504343953926634992332820282019728792003956564819969) (-255).
Definition i18 := makepairF f25 f26.
Notation p23 := (BND r31 i18). (* BND((1 + kk) * (1 + ma) * (1 + mb), [1, 1]) *)
Definition f27 := Float2 (28948022309329048855892746252171976963317496166410141009864396001978282409983) (-254).
Definition i19 := makepairF f27 f26.
Notation p24 := (BND r32 i19). (* BND((1 + kk) * (1 + ma), [1, 1]) *)
Definition f28 := Float2 (57896044618658097711785492504343953926634992332820282019728792003956564819967) (-255).
Definition i20 := makepairF f28 f26.
Notation p25 := (BND r13 i20). (* BND(1 + kk, [1, 1]) *)
Lemma l27 : s1 -> p4 (* BND(kk, [-1.72723e-77, 1.72723e-77]) *).
Proof.
 intros h0.
 assert (h1 := l11 h0).
 exact (proj2 h1).
Qed.
Lemma t6 : p15 -> p4 -> p25.
Proof.
 intros h0 h1.
 refine (add r4 _kk i13 i4 i20 h0 h1 _) ; finalize.
Qed.
Lemma l26 : s1 -> p25 (* BND(1 + kk, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l16 h0).
 assert (h2 := l27 h0).
 apply t6. exact h1. exact h2.
Qed.
Definition i21 := makepairF f28 f4.
Notation p26 := (BND r15 i21). (* BND(1 + ma, [1, 1]) *)
Lemma l29 : s1 -> p5 (* BND(ma, [-1.72723e-77, 0]) *).
Proof.
 intros h0.
 assert (h1 := l12 h0).
 exact (proj2 h1).
Qed.
Lemma t7 : p15 -> p5 -> p26.
Proof.
 intros h0 h1.
 refine (add r4 _ma i13 i5 i21 h0 h1 _) ; finalize.
Qed.
Lemma l28 : s1 -> p26 (* BND(1 + ma, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l16 h0).
 assert (h2 := l29 h0).
 apply t7. exact h1. exact h2.
Qed.
Lemma t8 : p25 -> p26 -> p24.
Proof.
 intros h0 h1.
 refine (mul_pp r13 r15 i20 i21 i19 h0 h1 _) ; finalize.
Qed.
Lemma l25 : s1 -> p24 (* BND((1 + kk) * (1 + ma), [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l26 h0).
 assert (h2 := l28 h0).
 apply t8. exact h1. exact h2.
Qed.
Notation p27 := (BND r20 i21). (* BND(1 + mb, [1, 1]) *)
Lemma l31 : s1 -> p6 (* BND(mb, [-1.72723e-77, 0]) *).
Proof.
 intros h0.
 assert (h1 := l13 h0).
 exact (proj2 h1).
Qed.
Lemma t9 : p15 -> p6 -> p27.
Proof.
 intros h0 h1.
 refine (add r4 _mb i13 i5 i21 h0 h1 _) ; finalize.
Qed.
Lemma l30 : s1 -> p27 (* BND(1 + mb, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l16 h0).
 assert (h2 := l31 h0).
 apply t9. exact h1. exact h2.
Qed.
Lemma t10 : p24 -> p27 -> p23.
Proof.
 intros h0 h1.
 refine (mul_pp r32 r20 i19 i21 i18 h0 h1 _) ; finalize.
Qed.
Lemma l24 : s1 -> p23 (* BND((1 + kk) * (1 + ma) * (1 + mb), [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l25 h0).
 assert (h2 := l30 h0).
 apply t10. exact h1. exact h2.
Qed.
Lemma t11 : p23 -> p15 -> p22.
Proof.
 intros h0 h1.
 refine (sub r31 r4 i18 i13 i16 h0 h1 _) ; finalize.
Qed.
Lemma l23 : s1 -> p22 (* BND((1 + kk) * (1 + ma) * (1 + mb) - 1, [-5.1817e-77, 1.72723e-77]) *).
Proof.
 intros h0.
 assert (h1 := l24 h0).
 assert (h2 := l16 h0).
 apply t11. exact h1. exact h2.
Qed.
Lemma t12 : p20 -> p22 -> p19.
Proof.
 intros h0 h1.
 refine (mul_po _Hn r30 i17 i16 i16 h0 h1 _) ; finalize.
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
 refine (add _En r29 i3 i16 i16 h0 h1 _) ; finalize.
Qed.
Lemma l18 : s1 -> p18 (* BND(En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1), [-5.1817e-77, 1.72723e-77]) *).
Proof.
 intros h0.
 assert (h1 := l19 h0).
 assert (h2 := l20 h0).
 apply t13. exact h1. exact h2.
Qed.
Lemma t14 : p13 -> p18 -> p12.
Proof.
 intros h0 h1.
 refine (mul_po r9 r28 i11 i16 i10 h0 h1 _) ; finalize.
Qed.
Lemma l6 : s1 -> p12 (* BND(s * (1 / 1980) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1)), [-1.61431e-80, 5.38103e-81]) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 assert (h2 := l18 h0).
 apply t14. exact h1. exact h2.
Qed.
Lemma t15 : p12 -> p11.
Proof.
 intros h0.
 refine (neg r27 i10 i9 h0 _) ; finalize.
Qed.
Lemma l5 : s1 -> p11 (* BND(-(s * (1 / 1980) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1))), [-5.38103e-81, 1.61431e-80]) *).
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
 refine (add r26 _sa i9 i6 i8 h0 h1 _) ; finalize.
Qed.
Lemma l4 : s1 -> p10 (* BND(-(s * (1 / 1980) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1))) + sa, [-3.45501e-77, 3.45608e-77]) *).
Proof.
 intros h0.
 assert (h1 := l5 h0).
 assert (h2 := l32 h0).
 apply t16. exact h1. exact h2.
Qed.
Notation p28 := (REL r1 r25 i3). (* REL(H - X, -(s * (1 / 1980) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1))) + sa, [0, 0]) *)
Notation p29 := (r1 = r25). (* EQL(H - X, -(s * (1 / 1980) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1))) + sa) *)
Lemma t17 : p29.
Proof.
 refine (b1) ; finalize.
Qed.
Lemma l34 : s1 -> p29 (* EQL(H - X, -(s * (1 / 1980) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1))) + sa) *).
Proof.
 intros h0.
 apply t17.
Qed.
Notation p30 := (REL r25 r25 i3). (* REL(-(s * (1 / 1980) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1))) + sa, -(s * (1 / 1980) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1))) + sa, [0, 0]) *)
Lemma t18 : p30.
Proof.
 refine (rel_refl r25 i3 _) ; finalize.
Qed.
Lemma l35 : s1 -> p30 (* REL(-(s * (1 / 1980) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1))) + sa, -(s * (1 / 1980) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1))) + sa, [0, 0]) *).
Proof.
 intros h0.
 apply t18.
Qed.
Lemma t19 : p29 -> p30 -> p28.
Proof.
 intros h0 h1.
 refine (rel_rewrite_1 r1 r25 r25 i3 h0 h1) ; finalize.
Qed.
Lemma l33 : s1 -> p28 (* REL(H - X, -(s * (1 / 1980) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1))) + sa, [0, 0]) *).
Proof.
 intros h0.
 assert (h1 := l34 h0).
 assert (h2 := l35 h0).
 apply t19. exact h1. exact h2.
Qed.
Lemma t20 : p10 -> p28 -> p9.
Proof.
 intros h0 h1.
 refine (bnd_of_bnd_rel_o r1 r25 i8 i3 i8 h0 h1 _) ; finalize.
Qed.
Lemma l3 : s1 -> p9 (* BND(H - X, [-3.45501e-77, 3.45608e-77]) *).
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
 refine (simplify (Tatom false (Abnd 0%nat i7)) Tfalse (Abnd 0%nat i8) (List.cons r1 List.nil) h2 h1 _) ; finalize.
Qed.
End Generated_by_Gappa.
