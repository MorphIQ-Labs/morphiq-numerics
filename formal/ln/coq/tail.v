Require Import Gappa.Gappa_library.
Section Generated_by_Gappa.
Variable _zh_ : R.
Notation _zh := ((rounding_float rndNE (53)%positive (-1074)%Z) _zh_).
Notation r3 := ((_zh * _zh)%R).
Notation r2 := ((r3 * _zh)%R).
Notation _c3 := (float2R (Float2 (6004799503160661) (-54))).
Notation _c4 := (float2R (Float2 (-4503599627370541) (-54))).
Notation _c5 := (float2R (Float2 (7205759403880275) (-55))).
Notation _c6 := (float2R (Float2 (-750599936424355) (-52))).
Notation _c7 := (float2R (Float2 (643371015971573) (-52))).
Notation _c8 := (float2R (Float2 (-4503984727172023) (-55))).
Notation _c9 := (float2R (Float2 (8060734871950603) (-56))).
Notation r23 := ((_zh * _c9)%R).
Notation r21 := ((_c8 + r23)%R).
Notation r20 := ((_zh * r21)%R).
Notation r18 := ((_c7 + r20)%R).
Notation r17 := ((_zh * r18)%R).
Notation r15 := ((_c6 + r17)%R).
Notation r14 := ((_zh * r15)%R).
Notation r12 := ((_c5 + r14)%R).
Notation r11 := ((_zh * r12)%R).
Notation r9 := ((_c4 + r11)%R).
Notation r8 := ((_zh * r9)%R).
Notation _W := ((_c3 + r8)%R).
Notation _T := ((r2 * _W)%R).
Notation _sh := ((rounding_float rndNE (53)%positive (-1074)%Z) r3).
Notation r26 := ((_zh * _sh)%R).
Notation _z3 := ((rounding_float rndNE (53)%positive (-1074)%Z) r26).
Notation r50 := ((rounding_float rndNE (53)%positive (-1074)%Z) r23).
Notation r49 := ((_c8 + r50)%R).
Notation _w8 := ((rounding_float rndNE (53)%positive (-1074)%Z) r49).
Notation r47 := ((_zh * _w8)%R).
Notation r46 := ((rounding_float rndNE (53)%positive (-1074)%Z) r47).
Notation r45 := ((_c7 + r46)%R).
Notation _w7 := ((rounding_float rndNE (53)%positive (-1074)%Z) r45).
Notation r43 := ((_zh * _w7)%R).
Notation r42 := ((rounding_float rndNE (53)%positive (-1074)%Z) r43).
Notation r41 := ((_c6 + r42)%R).
Notation _w6 := ((rounding_float rndNE (53)%positive (-1074)%Z) r41).
Notation r39 := ((_zh * _w6)%R).
Notation r38 := ((rounding_float rndNE (53)%positive (-1074)%Z) r39).
Notation r37 := ((_c5 + r38)%R).
Notation _w5 := ((rounding_float rndNE (53)%positive (-1074)%Z) r37).
Notation r35 := ((_zh * _w5)%R).
Notation r34 := ((rounding_float rndNE (53)%positive (-1074)%Z) r35).
Notation r33 := ((_c4 + r34)%R).
Notation _w4 := ((rounding_float rndNE (53)%positive (-1074)%Z) r33).
Notation r31 := ((_zh * _w4)%R).
Notation r30 := ((rounding_float rndNE (53)%positive (-1074)%Z) r31).
Notation r29 := ((_c3 + r30)%R).
Notation _w := ((rounding_float rndNE (53)%positive (-1074)%Z) r29).
Notation r54 := ((_z3 * _w)%R).
Notation _t := ((rounding_float rndNE (53)%positive (-1074)%Z) r54).
Notation r52 := ((_t - _T)%R).
Notation r51 := ((r52 / _T)%R).
Notation r59 := (Float1 (1)).
Notation r61 := ((_z3 - r2)%R).
Notation r60 := ((r61 / r2)%R).
Notation r58 := ((r59 + r60)%R).
Notation r64 := ((_w - _W)%R).
Notation r63 := ((r64 / _W)%R).
Notation r62 := ((r59 + r63)%R).
Notation r57 := ((r58 * r62)%R).
Notation r67 := ((_t - r54)%R).
Notation r66 := ((r67 / r54)%R).
Notation r65 := ((r59 + r66)%R).
Notation r56 := ((r57 * r65)%R).
Notation r55 := ((r56 - r59)%R).
Hypothesis a1 : (_T <> 0)%R -> (_zh <> 0)%R -> (_W <> 0)%R -> (_z3 <> 0)%R -> (_w <> 0)%R -> r51 = r55.
Lemma b1 : NZR _T -> NZR _zh -> NZR _W -> NZR _z3 -> NZR _w -> r51 = r55.
 intros h0 h1 h2 h3 h4.
 apply a1.
 exact h0.
 exact h1.
 exact h2.
 exact h3.
 exact h4.
Qed.
Notation r72 := ((_sh - r3)%R).
Notation r71 := ((r72 / r3)%R).
Notation r70 := ((r59 + r71)%R).
Notation r75 := ((_z3 - r26)%R).
Notation r74 := ((r75 / r26)%R).
Notation r73 := ((r59 + r74)%R).
Notation r69 := ((r70 * r73)%R).
Notation r68 := ((r69 - r59)%R).
Hypothesis a2 : (_zh <> 0)%R -> (_sh <> 0)%R -> r60 = r68.
Lemma b2 : NZR _zh -> NZR _sh -> r60 = r68.
 intros h0 h1.
 apply a2.
 exact h0.
 exact h1.
Qed.
Notation r76 := ((Rabs _zh)%R).
Definition f1 := Float2 (1) (-64).
Definition f2 := Float2 (80696341590167128190183336492762922277553037908230366465363237155637854447075094068654269148145619287504548485417148267) (-402).
Definition i1 := makepairF f1 f2.
Notation p1 := (BND r76 i1). (* BND(|zh|, [5.42101e-20, 0.0078126]) *)
Definition f3 := Float2 (-1) (-50).
Definition f4 := Float2 (1) (-50).
Definition i2 := makepairF f3 f4.
Notation p2 := (BND r51 i2). (* BND((t - T) / T, [-8.88178e-16, 8.88178e-16]) *)
Definition s2 := (not p2).
Definition s1 := (p1 /\ s2).
Lemma l2 : s1 -> s2.
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj2 h1).
Qed.
Definition f5 := Float2 (-2431428783295503358271786188438544725031851777157645714720011656461329883571719862164370241523697258668117029398338578937) (-451).
Definition f6 := Float2 (2431428783295504118291890936329482462007222118830552992668365259720458589847987060943692613745868602042768296523457921447) (-451).
Definition i3 := makepairF f5 f6.
Notation p3 := (BND r51 i3). (* BND((t - T) / T, [-4.18151e-16, 4.18151e-16]) *)
Notation p4 := (NZR _T). (* NZR(T) *)
Notation p5 := (NZR r2). (* NZR(zh * zh * zh) *)
Notation p6 := (NZR r3). (* NZR(zh * zh) *)
Definition f7 := Float2 (1) (-128).
Definition f8 := Float2 (1) (0).
Definition i4 := makepairF f7 f8.
Notation p7 := (ABS r3 i4). (* ABS(zh * zh, [2.93874e-39, 1]) *)
Definition f9 := Float2 (5043521349385445511886458530797682642347064869264397904085202322227365902942193379290891821759101205469034280338571767) (-398).
Definition i5 := makepairF f1 f9.
Notation p8 := (ABS _zh i5). (* ABS(zh, [5.42101e-20, 0.0078126]) *)
Lemma l9 : s1 -> p1 (* BND(|zh|, [5.42101e-20, 0.0078126]) *).
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj1 h1).
Qed.
Notation p9 := (BND r76 i5). (* BND(|zh|, [5.42101e-20, 0.0078126]) *)
Lemma t1 : p9 -> p8.
Proof.
 intros h0.
 refine (abs_of_uabs _zh i5 h0 _) ; finalize.
Qed.
Lemma l8 : s1 -> p8 (* ABS(zh, [5.42101e-20, 0.0078126]) *).
Proof.
 intros h0.
 assert (h1 := l9 h0).
 apply t1. refine (subset r76 i1 i5 h1 _) ; finalize.
Qed.
Definition i6 := makepairF f1 f8.
Notation p10 := (ABS _zh i6). (* ABS(zh, [5.42101e-20, 1]) *)
Lemma t2 : p10 -> p10 -> p7.
Proof.
 intros h0 h1.
 refine (mul_aa _zh _zh i6 i6 i4 h0 h1 _) ; finalize.
Qed.
Lemma l7 : s1 -> p7 (* ABS(zh * zh, [2.93874e-39, 1]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 apply t2. refine (abs_subset _zh i5 i6 h1 _) ; finalize. refine (abs_subset _zh i5 i6 h1 _) ; finalize.
Qed.
Lemma t3 : p7 -> p6.
Proof.
 intros h0.
 refine (nzr_of_abs r3 i4 h0 _) ; finalize.
Qed.
Lemma l6 : s1 -> p6 (* NZR(zh * zh) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 apply t3. exact h1.
Qed.
Notation p11 := (NZR _zh). (* NZR(zh) *)
Lemma t4 : p10 -> p11.
Proof.
 intros h0.
 refine (nzr_of_abs _zh i6 h0 _) ; finalize.
Qed.
Lemma l10 : s1 -> p11 (* NZR(zh) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 apply t4. refine (abs_subset _zh i5 i6 h1 _) ; finalize.
Qed.
Lemma t5 : p6 -> p11 -> p5.
Proof.
 intros h0 h1.
 refine (mul_nzr r3 _zh h0 h1) ; finalize.
Qed.
Lemma l5 : s1 -> p5 (* NZR(zh * zh * zh) *).
Proof.
 intros h0.
 assert (h1 := l6 h0).
 assert (h2 := l10 h0).
 apply t5. exact h1. exact h2.
Qed.
Notation p12 := (NZR _W). (* NZR(W) *)
Definition f10 := Float2 (1) (-2).
Definition i7 := makepairF f10 f8.
Notation p13 := (ABS _W i7). (* ABS(W, [0.25, 1]) *)
Definition f11 := Float2 (6004799503160661) (-54).
Definition i8 := makepairF f11 f11.
Notation p14 := (ABS _c3 i8). (* ABS(c3, [0.333333, 0.333333]) *)
Notation p15 := (BND _c3 i8). (* BND(c3, [0.333333, 0.333333]) *)
Lemma t6 : p15.
Proof.
 refine (constant2 _ i8 _) ; finalize.
Qed.
Lemma l14 : s1 -> p15 (* BND(c3, [0.333333, 0.333333]) *).
Proof.
 intros h0.
 apply t6.
Qed.
Lemma t7 : p15 -> p14.
Proof.
 intros h0.
 refine (abs_of_bnd_p _c3 i8 i8 h0 _) ; finalize.
Qed.
Lemma l13 : s1 -> p14 (* ABS(c3, [0.333333, 0.333333]) *).
Proof.
 intros h0.
 assert (h1 := l14 h0).
 apply t7. exact h1.
Qed.
Definition f12 := Float2 (1) (-67).
Definition f13 := Float2 (1) (-4).
Definition i9 := makepairF f12 f13.
Notation p16 := (ABS r8 i9). (* ABS(zh * (c4 + zh * (c5 + zh * (c6 + zh * (c7 + zh * (c8 + zh * c9))))), [6.77626e-21, 0.0625]) *)
Definition f14 := Float2 (1) (-3).
Definition i10 := makepairF f14 f8.
Notation p17 := (ABS r9 i10). (* ABS(c4 + zh * (c5 + zh * (c6 + zh * (c7 + zh * (c8 + zh * c9)))), [0.125, 1]) *)
Definition f15 := Float2 (4503599627370541) (-54).
Definition i11 := makepairF f15 f15.
Notation p18 := (ABS _c4 i11). (* ABS(c4, [0.25, 0.25]) *)
Definition f16 := Float2 (-4503599627370541) (-54).
Definition i12 := makepairF f16 f16.
Notation p19 := (BND _c4 i12). (* BND(c4, [-0.25, -0.25]) *)
Lemma t8 : p19.
Proof.
 refine (constant2 _ i12 _) ; finalize.
Qed.
Lemma l18 : s1 -> p19 (* BND(c4, [-0.25, -0.25]) *).
Proof.
 intros h0.
 apply t8.
Qed.
Lemma t9 : p19 -> p18.
Proof.
 intros h0.
 refine (abs_of_bnd_n _c4 i12 i11 h0 _) ; finalize.
Qed.
Lemma l17 : s1 -> p18 (* ABS(c4, [0.25, 0.25]) *).
Proof.
 intros h0.
 assert (h1 := l18 h0).
 apply t9. exact h1.
Qed.
Definition i13 := makepairF f12 f14.
Notation p20 := (ABS r11 i13). (* ABS(zh * (c5 + zh * (c6 + zh * (c7 + zh * (c8 + zh * c9)))), [6.77626e-21, 0.125]) *)
Notation p21 := (ABS r12 i10). (* ABS(c5 + zh * (c6 + zh * (c7 + zh * (c8 + zh * c9))), [0.125, 1]) *)
Definition f17 := Float2 (7205759403880275) (-55).
Definition i14 := makepairF f17 f17.
Notation p22 := (ABS _c5 i14). (* ABS(c5, [0.2, 0.2]) *)
Notation p23 := (BND _c5 i14). (* BND(c5, [0.2, 0.2]) *)
Lemma t10 : p23.
Proof.
 refine (constant2 _ i14 _) ; finalize.
Qed.
Lemma l22 : s1 -> p23 (* BND(c5, [0.2, 0.2]) *).
Proof.
 intros h0.
 apply t10.
Qed.
Lemma t11 : p23 -> p22.
Proof.
 intros h0.
 refine (abs_of_bnd_p _c5 i14 i14 h0 _) ; finalize.
Qed.
Lemma l21 : s1 -> p22 (* ABS(c5, [0.2, 0.2]) *).
Proof.
 intros h0.
 assert (h1 := l22 h0).
 apply t11. exact h1.
Qed.
Notation p24 := (ABS r14 i9). (* ABS(zh * (c6 + zh * (c7 + zh * (c8 + zh * c9))), [6.77626e-21, 0.0625]) *)
Notation p25 := (ABS r15 i10). (* ABS(c6 + zh * (c7 + zh * (c8 + zh * c9)), [0.125, 1]) *)
Definition f18 := Float2 (750599936424355) (-52).
Definition i15 := makepairF f18 f18.
Notation p26 := (ABS _c6 i15). (* ABS(c6, [0.166667, 0.166667]) *)
Definition f19 := Float2 (-750599936424355) (-52).
Definition i16 := makepairF f19 f19.
Notation p27 := (BND _c6 i16). (* BND(c6, [-0.166667, -0.166667]) *)
Lemma t12 : p27.
Proof.
 refine (constant2 _ i16 _) ; finalize.
Qed.
Lemma l26 : s1 -> p27 (* BND(c6, [-0.166667, -0.166667]) *).
Proof.
 intros h0.
 apply t12.
Qed.
Lemma t13 : p27 -> p26.
Proof.
 intros h0.
 refine (abs_of_bnd_n _c6 i16 i15 h0 _) ; finalize.
Qed.
Lemma l25 : s1 -> p26 (* ABS(c6, [0.166667, 0.166667]) *).
Proof.
 intros h0.
 assert (h1 := l26 h0).
 apply t13. exact h1.
Qed.
Definition f20 := Float2 (1) (-5).
Definition i17 := makepairF f12 f20.
Notation p28 := (ABS r17 i17). (* ABS(zh * (c7 + zh * (c8 + zh * c9)), [6.77626e-21, 0.03125]) *)
Notation p29 := (ABS r18 i10). (* ABS(c7 + zh * (c8 + zh * c9), [0.125, 1]) *)
Definition f21 := Float2 (9) (-6).
Definition f22 := Float2 (3) (-4).
Definition i18 := makepairF f21 f22.
Notation p30 := (ABS _c7 i18). (* ABS(c7, [0.140625, 0.1875]) *)
Definition f23 := Float2 (643371015971573) (-52).
Definition i19 := makepairF f21 f23.
Notation p31 := (BND _c7 i19). (* BND(c7, [0.140625, 0.142857]) *)
Lemma t14 : p31.
Proof.
 refine (constant2 _ i19 _) ; finalize.
Qed.
Lemma l30 : s1 -> p31 (* BND(c7, [0.140625, 0.142857]) *).
Proof.
 intros h0.
 apply t14.
Qed.
Notation p32 := (BND _c7 i18). (* BND(c7, [0.140625, 0.1875]) *)
Lemma t15 : p32 -> p30.
Proof.
 intros h0.
 refine (abs_of_bnd_p _c7 i18 i18 h0 _) ; finalize.
Qed.
Lemma l29 : s1 -> p30 (* ABS(c7, [0.140625, 0.1875]) *).
Proof.
 intros h0.
 assert (h1 := l30 h0).
 apply t15. refine (subset _c7 i19 i18 h1 _) ; finalize.
Qed.
Definition f24 := Float2 (1) (-68).
Definition f25 := Float2 (1) (-6).
Definition i20 := makepairF f24 f25.
Notation p33 := (ABS r20 i20). (* ABS(zh * (c8 + zh * c9), [3.38813e-21, 0.015625]) *)
Definition i21 := makepairF f13 f8.
Notation p34 := (ABS r21 i21). (* ABS(c8 + zh * c9, [0.0625, 1]) *)
Definition f26 := Float2 (4503984727172023) (-55).
Definition i22 := makepairF f26 f26.
Notation p35 := (ABS _c8 i22). (* ABS(c8, [0.125011, 0.125011]) *)
Definition f27 := Float2 (-4503984727172023) (-55).
Definition i23 := makepairF f27 f27.
Notation p36 := (BND _c8 i23). (* BND(c8, [-0.125011, -0.125011]) *)
Lemma t16 : p36.
Proof.
 refine (constant2 _ i23 _) ; finalize.
Qed.
Lemma l34 : s1 -> p36 (* BND(c8, [-0.125011, -0.125011]) *).
Proof.
 intros h0.
 apply t16.
Qed.
Lemma t17 : p36 -> p35.
Proof.
 intros h0.
 refine (abs_of_bnd_n _c8 i23 i22 h0 _) ; finalize.
Qed.
Lemma l33 : s1 -> p35 (* ABS(c8, [0.125011, 0.125011]) *).
Proof.
 intros h0.
 assert (h1 := l34 h0).
 apply t17. exact h1.
Qed.
Definition f28 := Float2 (1) (-10).
Definition i24 := makepairF f24 f28.
Notation p37 := (ABS r23 i24). (* ABS(zh * c9, [3.38813e-21, 0.000976562]) *)
Definition f29 := Float2 (8060734871950603) (-56).
Definition i25 := makepairF f29 f29.
Notation p38 := (ABS _c9 i25). (* ABS(c9, [0.111865, 0.111865]) *)
Notation p39 := (BND _c9 i25). (* BND(c9, [0.111865, 0.111865]) *)
Lemma t18 : p39.
Proof.
 refine (constant2 _ i25 _) ; finalize.
Qed.
Lemma l37 : s1 -> p39 (* BND(c9, [0.111865, 0.111865]) *).
Proof.
 intros h0.
 apply t18.
Qed.
Lemma t19 : p39 -> p38.
Proof.
 intros h0.
 refine (abs_of_bnd_p _c9 i25 i25 h0 _) ; finalize.
Qed.
Lemma l36 : s1 -> p38 (* ABS(c9, [0.111865, 0.111865]) *).
Proof.
 intros h0.
 assert (h1 := l37 h0).
 apply t19. exact h1.
Qed.
Definition f30 := Float2 (17) (-11).
Definition i26 := makepairF f1 f30.
Notation p40 := (ABS _zh i26). (* ABS(zh, [5.42101e-20, 0.00830078]) *)
Definition f31 := Float2 (15) (-7).
Definition i27 := makepairF f13 f31.
Notation p41 := (ABS _c9 i27). (* ABS(c9, [0.0625, 0.117188]) *)
Lemma t20 : p40 -> p41 -> p37.
Proof.
 intros h0 h1.
 refine (mul_aa _zh _c9 i26 i27 i24 h0 h1 _) ; finalize.
Qed.
Lemma l35 : s1 -> p37 (* ABS(zh * c9, [3.38813e-21, 0.000976562]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 assert (h2 := l36 h0).
 apply t20. refine (abs_subset _zh i5 i26 h1 _) ; finalize. refine (abs_subset _c9 i25 i27 h2 _) ; finalize.
Qed.
Definition f32 := Float2 (1) (-1).
Definition i28 := makepairF f14 f32.
Notation p42 := (ABS _c8 i28). (* ABS(c8, [0.125, 0.5]) *)
Definition i29 := makepairF f24 f13.
Notation p43 := (ABS r23 i29). (* ABS(zh * c9, [3.38813e-21, 0.0625]) *)
Lemma t21 : p42 -> p43 -> p34.
Proof.
 intros h0 h1.
 refine (add_aa_p _c8 r23 i28 i29 i21 h0 h1 _) ; finalize.
Qed.
Lemma l32 : s1 -> p34 (* ABS(c8 + zh * c9, [0.0625, 1]) *).
Proof.
 intros h0.
 assert (h1 := l33 h0).
 assert (h2 := l35 h0).
 apply t21. refine (abs_subset _c8 i22 i28 h1 _) ; finalize. refine (abs_subset r23 i24 i29 h2 _) ; finalize.
Qed.
Definition i30 := makepairF f1 f25.
Notation p44 := (ABS _zh i30). (* ABS(zh, [5.42101e-20, 0.015625]) *)
Lemma t22 : p44 -> p34 -> p33.
Proof.
 intros h0 h1.
 refine (mul_aa _zh r21 i30 i21 i20 h0 h1 _) ; finalize.
Qed.
Lemma l31 : s1 -> p33 (* ABS(zh * (c8 + zh * c9), [3.38813e-21, 0.015625]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 assert (h2 := l32 h0).
 apply t22. refine (abs_subset _zh i5 i30 h1 _) ; finalize. exact h2.
Qed.
Definition i31 := makepairF f21 f32.
Notation p45 := (ABS _c7 i31). (* ABS(c7, [0.140625, 0.5]) *)
Lemma t23 : p45 -> p33 -> p29.
Proof.
 intros h0 h1.
 refine (add_aa_p _c7 r20 i31 i20 i10 h0 h1 _) ; finalize.
Qed.
Lemma l28 : s1 -> p29 (* ABS(c7 + zh * (c8 + zh * c9), [0.125, 1]) *).
Proof.
 intros h0.
 assert (h1 := l29 h0).
 assert (h2 := l31 h0).
 apply t23. refine (abs_subset _c7 i18 i31 h1 _) ; finalize. exact h2.
Qed.
Definition i32 := makepairF f1 f20.
Notation p46 := (ABS _zh i32). (* ABS(zh, [5.42101e-20, 0.03125]) *)
Lemma t24 : p46 -> p29 -> p28.
Proof.
 intros h0 h1.
 refine (mul_aa _zh r18 i32 i10 i17 h0 h1 _) ; finalize.
Qed.
Lemma l27 : s1 -> p28 (* ABS(zh * (c7 + zh * (c8 + zh * c9)), [6.77626e-21, 0.03125]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 assert (h2 := l28 h0).
 apply t24. refine (abs_subset _zh i5 i32 h1 _) ; finalize. exact h2.
Qed.
Definition f33 := Float2 (5) (-5).
Definition i33 := makepairF f33 f32.
Notation p47 := (ABS _c6 i33). (* ABS(c6, [0.15625, 0.5]) *)
Lemma t25 : p47 -> p28 -> p25.
Proof.
 intros h0 h1.
 refine (add_aa_p _c6 r17 i33 i17 i10 h0 h1 _) ; finalize.
Qed.
Lemma l24 : s1 -> p25 (* ABS(c6 + zh * (c7 + zh * (c8 + zh * c9)), [0.125, 1]) *).
Proof.
 intros h0.
 assert (h1 := l25 h0).
 assert (h2 := l27 h0).
 apply t25. refine (abs_subset _c6 i15 i33 h1 _) ; finalize. exact h2.
Qed.
Definition i34 := makepairF f1 f13.
Notation p48 := (ABS _zh i34). (* ABS(zh, [5.42101e-20, 0.0625]) *)
Lemma t26 : p48 -> p25 -> p24.
Proof.
 intros h0 h1.
 refine (mul_aa _zh r15 i34 i10 i9 h0 h1 _) ; finalize.
Qed.
Lemma l23 : s1 -> p24 (* ABS(zh * (c6 + zh * (c7 + zh * (c8 + zh * c9))), [6.77626e-21, 0.0625]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 assert (h2 := l24 h0).
 apply t26. refine (abs_subset _zh i5 i34 h1 _) ; finalize. exact h2.
Qed.
Definition i35 := makepairF f22 f32.
Notation p49 := (ABS _c5 i35). (* ABS(c5, [0.1875, 0.5]) *)
Lemma t27 : p49 -> p24 -> p21.
Proof.
 intros h0 h1.
 refine (add_aa_p _c5 r14 i35 i9 i10 h0 h1 _) ; finalize.
Qed.
Lemma l20 : s1 -> p21 (* ABS(c5 + zh * (c6 + zh * (c7 + zh * (c8 + zh * c9))), [0.125, 1]) *).
Proof.
 intros h0.
 assert (h1 := l21 h0).
 assert (h2 := l23 h0).
 apply t27. refine (abs_subset _c5 i14 i35 h1 _) ; finalize. exact h2.
Qed.
Definition i36 := makepairF f1 f14.
Notation p50 := (ABS _zh i36). (* ABS(zh, [5.42101e-20, 0.125]) *)
Lemma t28 : p50 -> p21 -> p20.
Proof.
 intros h0 h1.
 refine (mul_aa _zh r12 i36 i10 i13 h0 h1 _) ; finalize.
Qed.
Lemma l19 : s1 -> p20 (* ABS(zh * (c5 + zh * (c6 + zh * (c7 + zh * (c8 + zh * c9)))), [6.77626e-21, 0.125]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 assert (h2 := l20 h0).
 apply t28. refine (abs_subset _zh i5 i36 h1 _) ; finalize. exact h2.
Qed.
Definition i37 := makepairF f10 f32.
Notation p51 := (ABS _c4 i37). (* ABS(c4, [0.25, 0.5]) *)
Lemma t29 : p51 -> p20 -> p17.
Proof.
 intros h0 h1.
 refine (add_aa_p _c4 r11 i37 i13 i10 h0 h1 _) ; finalize.
Qed.
Lemma l16 : s1 -> p17 (* ABS(c4 + zh * (c5 + zh * (c6 + zh * (c7 + zh * (c8 + zh * c9)))), [0.125, 1]) *).
Proof.
 intros h0.
 assert (h1 := l17 h0).
 assert (h2 := l19 h0).
 apply t29. refine (abs_subset _c4 i11 i37 h1 _) ; finalize. exact h2.
Qed.
Lemma t30 : p48 -> p17 -> p16.
Proof.
 intros h0 h1.
 refine (mul_aa _zh r9 i34 i10 i9 h0 h1 _) ; finalize.
Qed.
Lemma l15 : s1 -> p16 (* ABS(zh * (c4 + zh * (c5 + zh * (c6 + zh * (c7 + zh * (c8 + zh * c9))))), [6.77626e-21, 0.0625]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 assert (h2 := l16 h0).
 apply t30. refine (abs_subset _zh i5 i34 h1 _) ; finalize. exact h2.
Qed.
Definition f34 := Float2 (5) (-4).
Definition i38 := makepairF f34 f32.
Notation p52 := (ABS _c3 i38). (* ABS(c3, [0.3125, 0.5]) *)
Lemma t31 : p52 -> p16 -> p13.
Proof.
 intros h0 h1.
 refine (add_aa_p _c3 r8 i38 i9 i7 h0 h1 _) ; finalize.
Qed.
Lemma l12 : s1 -> p13 (* ABS(W, [0.25, 1]) *).
Proof.
 intros h0.
 assert (h1 := l13 h0).
 assert (h2 := l15 h0).
 apply t31. refine (abs_subset _c3 i8 i38 h1 _) ; finalize. exact h2.
Qed.
Lemma t32 : p13 -> p12.
Proof.
 intros h0.
 refine (nzr_of_abs _W i7 h0 _) ; finalize.
Qed.
Lemma l11 : s1 -> p12 (* NZR(W) *).
Proof.
 intros h0.
 assert (h1 := l12 h0).
 apply t32. exact h1.
Qed.
Lemma t33 : p5 -> p12 -> p4.
Proof.
 intros h0 h1.
 refine (mul_nzr r2 _W h0 h1) ; finalize.
Qed.
Lemma l4 : s1 -> p4 (* NZR(T) *).
Proof.
 intros h0.
 assert (h1 := l5 h0).
 assert (h2 := l11 h0).
 apply t33. exact h1. exact h2.
Qed.
Notation p53 := (REL _t _T i3). (* REL(t, T, [-4.18151e-16, 4.18151e-16]) *)
Definition f35 := Float2 (-1) (-53).
Definition f36 := Float2 (1) (-53).
Definition i39 := makepairF f35 f36.
Notation p54 := (REL _t r54 i39). (* REL(t, z3 * w, [-1.11022e-16, 1.11022e-16]) *)
Notation p55 := (FIX r54 (-699)). (* FIX(z3 * w, -699) *)
Notation p56 := (FIX _z3 (-296)). (* FIX(z3, -296) *)
Notation p57 := (FIX r26 (-296)). (* FIX(zh * sh, -296) *)
Notation p58 := (FIX _zh (-116)). (* FIX(zh, -116) *)
Notation p59 := (FLT _zh (53)). (* FLT(zh, 53) *)
Lemma t34 : p59.
Proof.
 refine (flt_of_float _ _ _ (53) _ _) ; finalize.
Qed.
Lemma l44 : s1 -> p59 (* FLT(zh, 53) *).
Proof.
 intros h0.
 apply t34.
Qed.
Lemma t35 : p59 -> p10 -> p58.
Proof.
 intros h0 h1.
 refine (fix_of_flt_bnd _zh i6 (-116) (53) h0 h1 _) ; finalize.
Qed.
Lemma l43 : s1 -> p58 (* FIX(zh, -116) *).
Proof.
 intros h0.
 assert (h1 := l44 h0).
 assert (h2 := l8 h0).
 apply t35. exact h1. refine (abs_subset _zh i5 i6 h2 _) ; finalize.
Qed.
Notation p60 := (FIX _sh (-180)). (* FIX(sh, -180) *)
Notation p61 := (FLT _sh (53)). (* FLT(sh, 53) *)
Lemma t36 : p61.
Proof.
 refine (flt_of_float _ _ _ (53) _ _) ; finalize.
Qed.
Lemma l46 : s1 -> p61 (* FLT(sh, 53) *).
Proof.
 intros h0.
 apply t36.
Qed.
Notation p62 := (ABS _sh i4). (* ABS(sh, [2.93874e-39, 1]) *)
Notation p63 := (BND _sh i4). (* BND(sh, [2.93874e-39, 1]) *)
Notation p64 := (BND r3 i4). (* BND(zh * zh, [2.93874e-39, 1]) *)
Lemma t37 : p10 -> p64.
Proof.
 intros h0.
 refine (square _zh i6 i4 h0 _) ; finalize.
Qed.
Lemma l49 : s1 -> p64 (* BND(zh * zh, [2.93874e-39, 1]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 apply t37. refine (abs_subset _zh i5 i6 h1 _) ; finalize.
Qed.
Lemma t38 : p64 -> p63.
Proof.
 intros h0.
 refine (float_round_ne _ _ r3 i4 i4 h0 _) ; finalize.
Qed.
Lemma l48 : s1 -> p63 (* BND(sh, [2.93874e-39, 1]) *).
Proof.
 intros h0.
 assert (h1 := l49 h0).
 apply t38. exact h1.
Qed.
Lemma t39 : p63 -> p62.
Proof.
 intros h0.
 refine (abs_of_bnd_p _sh i4 i4 h0 _) ; finalize.
Qed.
Lemma l47 : s1 -> p62 (* ABS(sh, [2.93874e-39, 1]) *).
Proof.
 intros h0.
 assert (h1 := l48 h0).
 apply t39. exact h1.
Qed.
Lemma t40 : p61 -> p62 -> p60.
Proof.
 intros h0 h1.
 refine (fix_of_flt_bnd _sh i4 (-180) (53) h0 h1 _) ; finalize.
Qed.
Lemma l45 : s1 -> p60 (* FIX(sh, -180) *).
Proof.
 intros h0.
 assert (h1 := l46 h0).
 assert (h2 := l47 h0).
 apply t40. exact h1. exact h2.
Qed.
Lemma t41 : p58 -> p60 -> p57.
Proof.
 intros h0 h1.
 refine (mul_fix _zh _sh (-116) (-180) (-296) h0 h1 _) ; finalize.
Qed.
Lemma l42 : s1 -> p57 (* FIX(zh * sh, -296) *).
Proof.
 intros h0.
 assert (h1 := l43 h0).
 assert (h2 := l45 h0).
 apply t41. exact h1. exact h2.
Qed.
Lemma t42 : p57 -> p56.
Proof.
 intros h0.
 refine (fix_float_of_fix _ _ _ (-296) (-296) r26 h0 _) ; finalize.
Qed.
Lemma l41 : s1 -> p56 (* FIX(z3, -296) *).
Proof.
 intros h0.
 assert (h1 := l42 h0).
 apply t42. exact h1.
Qed.
Notation p65 := (FIX _w (-403)). (* FIX(w, -403) *)
Notation p66 := (FIX r29 (-403)). (* FIX(c3 + float<53,-1074,ne>(zh * w4), -403) *)
Notation p67 := (FIX _c3 (-54)). (* FIX(c3, -54) *)
Lemma t43 : p14 -> p67.
Proof.
 intros h0.
 refine (fix_of_singleton_bnd _c3 i8 (-54) h0 _) ; finalize.
Qed.
Lemma l52 : s1 -> p67 (* FIX(c3, -54) *).
Proof.
 intros h0.
 assert (h1 := l13 h0).
 apply t43. exact h1.
Qed.
Notation p68 := (FIX r30 (-403)). (* FIX(float<53,-1074,ne>(zh * w4), -403) *)
Notation p69 := (FIX r31 (-403)). (* FIX(zh * w4, -403) *)
Notation p70 := (FIX _w4 (-287)). (* FIX(w4, -287) *)
Notation p71 := (FIX r33 (-287)). (* FIX(c4 + float<53,-1074,ne>(zh * w5), -287) *)
Notation p72 := (FIX _c4 (-54)). (* FIX(c4, -54) *)
Lemma t44 : p18 -> p72.
Proof.
 intros h0.
 refine (fix_of_singleton_bnd _c4 i11 (-54) h0 _) ; finalize.
Qed.
Lemma l57 : s1 -> p72 (* FIX(c4, -54) *).
Proof.
 intros h0.
 assert (h1 := l17 h0).
 apply t44. exact h1.
Qed.
Notation p73 := (FIX r34 (-287)). (* FIX(float<53,-1074,ne>(zh * w5), -287) *)
Notation p74 := (FIX r35 (-287)). (* FIX(zh * w5, -287) *)
Notation p75 := (FIX _w5 (-171)). (* FIX(w5, -171) *)
Notation p76 := (FIX r37 (-171)). (* FIX(c5 + float<53,-1074,ne>(zh * w6), -171) *)
Notation p77 := (FIX _c5 (-55)). (* FIX(c5, -55) *)
Lemma t45 : p22 -> p77.
Proof.
 intros h0.
 refine (fix_of_singleton_bnd _c5 i14 (-55) h0 _) ; finalize.
Qed.
Lemma l62 : s1 -> p77 (* FIX(c5, -55) *).
Proof.
 intros h0.
 assert (h1 := l21 h0).
 apply t45. exact h1.
Qed.
Notation p78 := (FIX r38 (-171)). (* FIX(float<53,-1074,ne>(zh * w6), -171) *)
Notation p79 := (FIX r39 (-171)). (* FIX(zh * w6, -171) *)
Notation p80 := (FIX _w6 (-55)). (* FIX(w6, -55) *)
Notation p81 := (FLT _w6 (53)). (* FLT(w6, 53) *)
Lemma t46 : p81.
Proof.
 refine (flt_of_float _ _ _ (53) _ _) ; finalize.
Qed.
Lemma l66 : s1 -> p81 (* FLT(w6, 53) *).
Proof.
 intros h0.
 apply t46.
Qed.
Definition i40 := makepairF f14 f22.
Notation p82 := (ABS _w6 i40). (* ABS(w6, [0.125, 0.1875]) *)
Definition f37 := Float2 (-3022643762470861) (-54).
Definition f38 := Float2 (-1) (-3).
Definition i41 := makepairF f37 f38.
Notation p83 := (BND _w6 i41). (* BND(w6, [-0.16779, -0.125]) *)
Notation p84 := (BND r41 i41). (* BND(c6 + float<53,-1074,ne>(zh * w7), [-0.16779, -0.125]) *)
Definition f39 := Float2 (-20244016773441) (-54).
Definition i42 := makepairF f39 f20.
Notation p85 := (BND r42 i42). (* BND(float<53,-1074,ne>(zh * w7), [-0.00112377, 0.03125]) *)
Notation p86 := (BND r43 i42). (* BND(zh * w7, [-0.00112377, 0.03125]) *)
Definition f40 := Float2 (-5043521349385445511886458530797682642347064869264397904085202322227365902942193379290891821759101205469034280338571767) (-398).
Definition i43 := makepairF f40 f9.
Notation p87 := (BND _zh i43). (* BND(zh, [-0.0078126, 0.0078126]) *)
Lemma t47 : p8 -> p87.
Proof.
 intros h0.
 refine (bnd_of_abs _zh i5 i43 h0 _) ; finalize.
Qed.
Lemma l72 : s1 -> p87 (* BND(zh, [-0.0078126, 0.0078126]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 apply t47. exact h1.
Qed.
Definition f41 := Float2 (20243757653343) (-47).
Definition i44 := makepairF f14 f41.
Notation p88 := (BND _w7 i44). (* BND(w7, [0.125, 0.143841]) *)
Notation p89 := (BND r45 i44). (* BND(c7 + float<53,-1074,ne>(zh * w8), [0.125, 0.143841]) *)
Definition f42 := Float2 (-1) (-6).
Definition f43 := Float2 (553653616925) (-49).
Definition i45 := makepairF f42 f43.
Notation p90 := (BND r46 i45). (* BND(float<53,-1074,ne>(zh * w8), [-0.015625, 0.000983486]) *)
Notation p91 := (BND r47 i45). (* BND(zh * w8, [-0.015625, 0.000983486]) *)
Definition f44 := Float2 (-4429172241995) (-45).
Definition f45 := Float2 (-1) (-4).
Definition i46 := makepairF f44 f45.
Notation p92 := (BND _w8 i46). (* BND(w8, [-0.125885, -0.0625]) *)
Notation p93 := (BND r49 i46). (* BND(c8 + float<53,-1074,ne>(zh * c9), [-0.125885, -0.0625]) *)
Definition f46 := Float2 (-15374828433) (-44).
Definition i47 := makepairF f46 f13.
Notation p94 := (BND r50 i47). (* BND(float<53,-1074,ne>(zh * c9), [-0.000873958, 0.0625]) *)
Definition f47 := Float2 (-34435691144168944308429817330280058686311728846541808141260421195564676990766332096674345775201736658720398019225) (-384).
Definition f48 := Float2 (33628604632977484676200993486601619810851297701700984512949630073793629873795246188158540796095445955781638691) (-374).
Definition i48 := makepairF f47 f48.
Notation p95 := (BND r23 i48). (* BND(zh * c9, [-0.000873958, 0.000873958]) *)
Definition f49 := Float2 (-19239507100621969268365701792898874825847873189027396789875802315625632869499944226420943533932118245960366364817) (-380).
Definition f50 := Float2 (75154324611804567454553522628511229788468254644638268710452352795412628396484157134456810679422336898282681113) (-372).
Definition i49 := makepairF f49 f50.
Notation p96 := (BND _zh i49). (* BND(zh, [-0.0078126, 0.0078126]) *)
Definition i50 := makepairF f13 f29.
Notation p97 := (BND _c9 i50). (* BND(c9, [0.0625, 0.111865]) *)
Lemma t48 : p96 -> p97 -> p95.
Proof.
 intros h0 h1.
 refine (mul_op _zh _c9 i49 i50 i48 h0 h1 _) ; finalize.
Qed.
Lemma l80 : s1 -> p95 (* BND(zh * c9, [-0.000873958, 0.000873958]) *).
Proof.
 intros h0.
 assert (h1 := l72 h0).
 assert (h2 := l37 h0).
 apply t48. refine (subset _zh i43 i49 h1 _) ; finalize. refine (subset _c9 i25 i50 h2 _) ; finalize.
Qed.
Notation p98 := (BND r23 i47). (* BND(zh * c9, [-0.000873958, 0.0625]) *)
Lemma t49 : p98 -> p94.
Proof.
 intros h0.
 refine (float_round_ne _ _ r23 i47 i47 h0 _) ; finalize.
Qed.
Lemma l79 : s1 -> p94 (* BND(float<53,-1074,ne>(zh * c9), [-0.000873958, 0.0625]) *).
Proof.
 intros h0.
 assert (h1 := l80 h0).
 apply t49. refine (subset r23 i48 i47 h1 _) ; finalize.
Qed.
Definition f51 := Float2 (-4398422585129) (-45).
Definition i51 := makepairF f51 f38.
Notation p99 := (BND _c8 i51). (* BND(c8, [-0.125011, -0.125]) *)
Lemma t50 : p99 -> p94 -> p93.
Proof.
 intros h0 h1.
 refine (add _c8 r50 i51 i47 i46 h0 h1 _) ; finalize.
Qed.
Lemma l78 : s1 -> p93 (* BND(c8 + float<53,-1074,ne>(zh * c9), [-0.125885, -0.0625]) *).
Proof.
 intros h0.
 assert (h1 := l34 h0).
 assert (h2 := l79 h0).
 apply t50. refine (subset _c8 i23 i51 h1 _) ; finalize. exact h2.
Qed.
Lemma t51 : p93 -> p92.
Proof.
 intros h0.
 refine (float_round_ne _ _ r49 i46 i46 h0 _) ; finalize.
Qed.
Lemma l77 : s1 -> p92 (* BND(w8, [-0.125885, -0.0625]) *).
Proof.
 intros h0.
 assert (h1 := l78 h0).
 apply t51. exact h1.
Qed.
Definition f52 := Float2 (-8796205612199) (-50).
Definition i52 := makepairF f52 f13.
Notation p100 := (BND _zh i52). (* BND(zh, [-0.0078126, 0.0625]) *)
Lemma t52 : p100 -> p92 -> p91.
Proof.
 intros h0 h1.
 refine (mul_on _zh _w8 i52 i46 i45 h0 h1 _) ; finalize.
Qed.
Lemma l76 : s1 -> p91 (* BND(zh * w8, [-0.015625, 0.000983486]) *).
Proof.
 intros h0.
 assert (h1 := l72 h0).
 assert (h2 := l77 h0).
 apply t52. refine (subset _zh i43 i52 h1 _) ; finalize. exact h2.
Qed.
Lemma t53 : p91 -> p90.
Proof.
 intros h0.
 refine (float_round_ne _ _ r47 i45 i45 h0 _) ; finalize.
Qed.
Lemma l75 : s1 -> p90 (* BND(float<53,-1074,ne>(zh * w8), [-0.015625, 0.000983486]) *).
Proof.
 intros h0.
 assert (h1 := l76 h0).
 apply t53. exact h1.
Qed.
Definition f53 := Float2 (80421376996447) (-49).
Definition i53 := makepairF f21 f53.
Notation p101 := (BND _c7 i53). (* BND(c7, [0.140625, 0.142857]) *)
Lemma t54 : p101 -> p90 -> p89.
Proof.
 intros h0 h1.
 refine (add _c7 r46 i53 i45 i44 h0 h1 _) ; finalize.
Qed.
Lemma l74 : s1 -> p89 (* BND(c7 + float<53,-1074,ne>(zh * w8), [0.125, 0.143841]) *).
Proof.
 intros h0.
 assert (h1 := l30 h0).
 assert (h2 := l75 h0).
 apply t54. refine (subset _c7 i19 i53 h1 _) ; finalize. exact h2.
Qed.
Lemma t55 : p89 -> p88.
Proof.
 intros h0.
 refine (float_round_ne _ _ r45 i44 i44 h0 _) ; finalize.
Qed.
Lemma l73 : s1 -> p88 (* BND(w7, [0.125, 0.143841]) *).
Proof.
 intros h0.
 assert (h1 := l74 h0).
 apply t55. exact h1.
Qed.
Definition f54 := Float2 (-140739289795179) (-54).
Definition i54 := makepairF f54 f14.
Notation p102 := (BND _zh i54). (* BND(zh, [-0.0078126, 0.125]) *)
Lemma t56 : p102 -> p88 -> p86.
Proof.
 intros h0 h1.
 refine (mul_op _zh _w7 i54 i44 i42 h0 h1 _) ; finalize.
Qed.
Lemma l71 : s1 -> p86 (* BND(zh * w7, [-0.00112377, 0.03125]) *).
Proof.
 intros h0.
 assert (h1 := l72 h0).
 assert (h2 := l73 h0).
 apply t56. refine (subset _zh i43 i54 h1 _) ; finalize. exact h2.
Qed.
Lemma t57 : p86 -> p85.
Proof.
 intros h0.
 refine (float_round_ne _ _ r43 i42 i42 h0 _) ; finalize.
Qed.
Lemma l70 : s1 -> p85 (* BND(float<53,-1074,ne>(zh * w7), [-0.00112377, 0.03125]) *).
Proof.
 intros h0.
 assert (h1 := l71 h0).
 apply t57. exact h1.
Qed.
Definition f55 := Float2 (-5) (-5).
Definition i55 := makepairF f19 f55.
Notation p103 := (BND _c6 i55). (* BND(c6, [-0.166667, -0.15625]) *)
Lemma t58 : p103 -> p85 -> p84.
Proof.
 intros h0 h1.
 refine (add _c6 r42 i55 i42 i41 h0 h1 _) ; finalize.
Qed.
Lemma l69 : s1 -> p84 (* BND(c6 + float<53,-1074,ne>(zh * w7), [-0.16779, -0.125]) *).
Proof.
 intros h0.
 assert (h1 := l26 h0).
 assert (h2 := l70 h0).
 apply t58. refine (subset _c6 i16 i55 h1 _) ; finalize. exact h2.
Qed.
Lemma t59 : p84 -> p83.
Proof.
 intros h0.
 refine (float_round_ne _ _ r41 i41 i41 h0 _) ; finalize.
Qed.
Lemma l68 : s1 -> p83 (* BND(w6, [-0.16779, -0.125]) *).
Proof.
 intros h0.
 assert (h1 := l69 h0).
 apply t59. exact h1.
Qed.
Definition f56 := Float2 (-3) (-4).
Definition i56 := makepairF f56 f38.
Notation p104 := (BND _w6 i56). (* BND(w6, [-0.1875, -0.125]) *)
Lemma t60 : p104 -> p82.
Proof.
 intros h0.
 refine (abs_of_bnd_n _w6 i56 i40 h0 _) ; finalize.
Qed.
Lemma l67 : s1 -> p82 (* ABS(w6, [0.125, 0.1875]) *).
Proof.
 intros h0.
 assert (h1 := l68 h0).
 apply t60. refine (subset _w6 i41 i56 h1 _) ; finalize.
Qed.
Notation p105 := (ABS _w6 i10). (* ABS(w6, [0.125, 1]) *)
Lemma t61 : p81 -> p105 -> p80.
Proof.
 intros h0 h1.
 refine (fix_of_flt_bnd _w6 i10 (-55) (53) h0 h1 _) ; finalize.
Qed.
Lemma l65 : s1 -> p80 (* FIX(w6, -55) *).
Proof.
 intros h0.
 assert (h1 := l66 h0).
 assert (h2 := l67 h0).
 apply t61. exact h1. refine (abs_subset _w6 i40 i10 h2 _) ; finalize.
Qed.
Lemma t62 : p58 -> p80 -> p79.
Proof.
 intros h0 h1.
 refine (mul_fix _zh _w6 (-116) (-55) (-171) h0 h1 _) ; finalize.
Qed.
Lemma l64 : s1 -> p79 (* FIX(zh * w6, -171) *).
Proof.
 intros h0.
 assert (h1 := l43 h0).
 assert (h2 := l65 h0).
 apply t62. exact h1. exact h2.
Qed.
Lemma t63 : p79 -> p78.
Proof.
 intros h0.
 refine (fix_float_of_fix _ _ _ (-171) (-171) r39 h0 _) ; finalize.
Qed.
Lemma l63 : s1 -> p78 (* FIX(float<53,-1074,ne>(zh * w6), -171) *).
Proof.
 intros h0.
 assert (h1 := l64 h0).
 apply t63. exact h1.
Qed.
Lemma t64 : p77 -> p78 -> p76.
Proof.
 intros h0 h1.
 refine (add_fix _c5 r38 (-55) (-171) (-171) h0 h1 _) ; finalize.
Qed.
Lemma l61 : s1 -> p76 (* FIX(c5 + float<53,-1074,ne>(zh * w6), -171) *).
Proof.
 intros h0.
 assert (h1 := l62 h0).
 assert (h2 := l63 h0).
 apply t64. exact h1. exact h2.
Qed.
Lemma t65 : p76 -> p75.
Proof.
 intros h0.
 refine (fix_float_of_fix _ _ _ (-171) (-171) r37 h0 _) ; finalize.
Qed.
Lemma l60 : s1 -> p75 (* FIX(w5, -171) *).
Proof.
 intros h0.
 assert (h1 := l61 h0).
 apply t65. exact h1.
Qed.
Lemma t66 : p58 -> p75 -> p74.
Proof.
 intros h0 h1.
 refine (mul_fix _zh _w5 (-116) (-171) (-287) h0 h1 _) ; finalize.
Qed.
Lemma l59 : s1 -> p74 (* FIX(zh * w5, -287) *).
Proof.
 intros h0.
 assert (h1 := l43 h0).
 assert (h2 := l60 h0).
 apply t66. exact h1. exact h2.
Qed.
Lemma t67 : p74 -> p73.
Proof.
 intros h0.
 refine (fix_float_of_fix _ _ _ (-287) (-287) r35 h0 _) ; finalize.
Qed.
Lemma l58 : s1 -> p73 (* FIX(float<53,-1074,ne>(zh * w5), -287) *).
Proof.
 intros h0.
 assert (h1 := l59 h0).
 apply t67. exact h1.
Qed.
Lemma t68 : p72 -> p73 -> p71.
Proof.
 intros h0 h1.
 refine (add_fix _c4 r34 (-54) (-287) (-287) h0 h1 _) ; finalize.
Qed.
Lemma l56 : s1 -> p71 (* FIX(c4 + float<53,-1074,ne>(zh * w5), -287) *).
Proof.
 intros h0.
 assert (h1 := l57 h0).
 assert (h2 := l58 h0).
 apply t68. exact h1. exact h2.
Qed.
Lemma t69 : p71 -> p70.
Proof.
 intros h0.
 refine (fix_float_of_fix _ _ _ (-287) (-287) r33 h0 _) ; finalize.
Qed.
Lemma l55 : s1 -> p70 (* FIX(w4, -287) *).
Proof.
 intros h0.
 assert (h1 := l56 h0).
 apply t69. exact h1.
Qed.
Lemma t70 : p58 -> p70 -> p69.
Proof.
 intros h0 h1.
 refine (mul_fix _zh _w4 (-116) (-287) (-403) h0 h1 _) ; finalize.
Qed.
Lemma l54 : s1 -> p69 (* FIX(zh * w4, -403) *).
Proof.
 intros h0.
 assert (h1 := l43 h0).
 assert (h2 := l55 h0).
 apply t70. exact h1. exact h2.
Qed.
Lemma t71 : p69 -> p68.
Proof.
 intros h0.
 refine (fix_float_of_fix _ _ _ (-403) (-403) r31 h0 _) ; finalize.
Qed.
Lemma l53 : s1 -> p68 (* FIX(float<53,-1074,ne>(zh * w4), -403) *).
Proof.
 intros h0.
 assert (h1 := l54 h0).
 apply t71. exact h1.
Qed.
Lemma t72 : p67 -> p68 -> p66.
Proof.
 intros h0 h1.
 refine (add_fix _c3 r30 (-54) (-403) (-403) h0 h1 _) ; finalize.
Qed.
Lemma l51 : s1 -> p66 (* FIX(c3 + float<53,-1074,ne>(zh * w4), -403) *).
Proof.
 intros h0.
 assert (h1 := l52 h0).
 assert (h2 := l53 h0).
 apply t72. exact h1. exact h2.
Qed.
Lemma t73 : p66 -> p65.
Proof.
 intros h0.
 refine (fix_float_of_fix _ _ _ (-403) (-403) r29 h0 _) ; finalize.
Qed.
Lemma l50 : s1 -> p65 (* FIX(w, -403) *).
Proof.
 intros h0.
 assert (h1 := l51 h0).
 apply t73. exact h1.
Qed.
Lemma t74 : p56 -> p65 -> p55.
Proof.
 intros h0 h1.
 refine (mul_fix _z3 _w (-296) (-403) (-699) h0 h1 _) ; finalize.
Qed.
Lemma l40 : s1 -> p55 (* FIX(z3 * w, -699) *).
Proof.
 intros h0.
 assert (h1 := l41 h0).
 assert (h2 := l50 h0).
 apply t74. exact h1. exact h2.
Qed.
Lemma t75 : p55 -> p54.
Proof.
 intros h0.
 refine (rel_of_fix_float_ne _ _ (-699) r54 i39 h0 _) ; finalize.
Qed.
Lemma l39 : s1 -> p54 (* REL(t, z3 * w, [-1.11022e-16, 1.11022e-16]) *).
Proof.
 intros h0.
 assert (h1 := l40 h0).
 apply t75. exact h1.
Qed.
Definition f57 := Float2 (-892933156886888204564398220423941039262288574192408623165074278191995921768523911035907971737982677547755790025776476855) (-450).
Definition f58 := Float2 (892933156886888386303460548959299408585674832957332366736572995635062865521185872153379127586949252298857348906068294611) (-450).
Definition i57 := makepairF f57 f58.
Notation p106 := (REL r54 _T i57). (* REL(z3 * w, T, [-3.07129e-16, 3.07129e-16]) *)
Definition f59 := Float2 (-18014398509481983) (-106).
Definition f60 := Float2 (18014398509481985) (-106).
Definition i58 := makepairF f59 f60.
Notation p107 := (REL _z3 r2 i58). (* REL(z3, zh * zh * zh, [-2.22045e-16, 2.22045e-16]) *)
Notation p108 := (BND r60 i58). (* BND((z3 - zh * zh * zh) / (zh * zh * zh), [-2.22045e-16, 2.22045e-16]) *)
Notation p109 := (BND r68 i58). (* BND((1 + (sh - zh * zh) / (zh * zh)) * (1 + (z3 - zh * sh) / (zh * sh)) - 1, [-2.22045e-16, 2.22045e-16]) *)
Definition f61 := Float2 (81129638414606663681390495662081) (-106).
Definition f62 := Float2 (81129638414606699710187514626049) (-106).
Definition i59 := makepairF f61 f62.
Notation p110 := (BND r69 i59). (* BND((1 + (sh - zh * zh) / (zh * zh)) * (1 + (z3 - zh * sh) / (zh * sh)), [1, 1]) *)
Definition f63 := Float2 (9007199254740991) (-53).
Definition f64 := Float2 (9007199254740993) (-53).
Definition i60 := makepairF f63 f64.
Notation p111 := (BND r70 i60). (* BND(1 + (sh - zh * zh) / (zh * zh), [1, 1]) *)
Definition i61 := makepairF f8 f8.
Notation p112 := (BND r59 i61). (* BND(1, [1, 1]) *)
Lemma t76 : p112.
Proof.
 refine (constant1 _ i61 _) ; finalize.
Qed.
Lemma l87 : s1 -> p112 (* BND(1, [1, 1]) *).
Proof.
 intros h0.
 apply t76.
Qed.
Notation p113 := (BND r71 i39). (* BND((sh - zh * zh) / (zh * zh), [-1.11022e-16, 1.11022e-16]) *)
Notation p114 := (REL _sh r3 i39). (* REL(sh, zh * zh, [-1.11022e-16, 1.11022e-16]) *)
Notation p115 := (FIX r3 (-232)). (* FIX(zh * zh, -232) *)
Lemma t77 : p58 -> p58 -> p115.
Proof.
 intros h0 h1.
 refine (mul_fix _zh _zh (-116) (-116) (-232) h0 h1 _) ; finalize.
Qed.
Lemma l90 : s1 -> p115 (* FIX(zh * zh, -232) *).
Proof.
 intros h0.
 assert (h1 := l43 h0).
 apply t77. exact h1. exact h1.
Qed.
Lemma t78 : p115 -> p114.
Proof.
 intros h0.
 refine (rel_of_fix_float_ne _ _ (-232) r3 i39 h0 _) ; finalize.
Qed.
Lemma l89 : s1 -> p114 (* REL(sh, zh * zh, [-1.11022e-16, 1.11022e-16]) *).
Proof.
 intros h0.
 assert (h1 := l90 h0).
 apply t78. exact h1.
Qed.
Lemma t79 : p6 -> p114 -> p113.
Proof.
 intros h0 h1.
 refine (bnd_of_nzr_rel _sh r3 i39 h0 h1) ; finalize.
Qed.
Lemma l88 : s1 -> p113 (* BND((sh - zh * zh) / (zh * zh), [-1.11022e-16, 1.11022e-16]) *).
Proof.
 intros h0.
 assert (h1 := l6 h0).
 assert (h2 := l89 h0).
 apply t79. exact h1. exact h2.
Qed.
Lemma t80 : p112 -> p113 -> p111.
Proof.
 intros h0 h1.
 refine (add r59 r71 i61 i39 i60 h0 h1 _) ; finalize.
Qed.
Lemma l86 : s1 -> p111 (* BND(1 + (sh - zh * zh) / (zh * zh), [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l87 h0).
 assert (h2 := l88 h0).
 apply t80. exact h1. exact h2.
Qed.
Notation p116 := (BND r73 i60). (* BND(1 + (z3 - zh * sh) / (zh * sh), [1, 1]) *)
Notation p117 := (BND r74 i39). (* BND((z3 - zh * sh) / (zh * sh), [-1.11022e-16, 1.11022e-16]) *)
Notation p118 := (NZR r26). (* NZR(zh * sh) *)
Notation p119 := (NZR _sh). (* NZR(sh) *)
Definition f65 := Float2 (-1) (-1).
Definition i62 := makepairF f65 f8.
Notation p120 := (REL _sh r3 i62). (* REL(sh, zh * zh, [-0.5, 1]) *)
Lemma t81 : p6 -> p120 -> p119.
Proof.
 intros h0 h1.
 refine (nzr_of_nzr_rel _sh r3 i62 h0 h1 _) ; finalize.
Qed.
Lemma l94 : s1 -> p119 (* NZR(sh) *).
Proof.
 intros h0.
 assert (h1 := l6 h0).
 assert (h2 := l89 h0).
 apply t81. exact h1. refine (rel_subset _sh r3 i39 i62 h2 _) ; finalize.
Qed.
Lemma t82 : p11 -> p119 -> p118.
Proof.
 intros h0 h1.
 refine (mul_nzr _zh _sh h0 h1) ; finalize.
Qed.
Lemma l93 : s1 -> p118 (* NZR(zh * sh) *).
Proof.
 intros h0.
 assert (h1 := l10 h0).
 assert (h2 := l94 h0).
 apply t82. exact h1. exact h2.
Qed.
Notation p121 := (REL _z3 r26 i39). (* REL(z3, zh * sh, [-1.11022e-16, 1.11022e-16]) *)
Notation p122 := (FIX r26 (-348)). (* FIX(zh * sh, -348) *)
Notation p123 := (FIX _sh (-232)). (* FIX(sh, -232) *)
Lemma t83 : p115 -> p123.
Proof.
 intros h0.
 refine (fix_float_of_fix _ _ _ (-232) (-232) r3 h0 _) ; finalize.
Qed.
Lemma l97 : s1 -> p123 (* FIX(sh, -232) *).
Proof.
 intros h0.
 assert (h1 := l90 h0).
 apply t83. exact h1.
Qed.
Lemma t84 : p58 -> p123 -> p122.
Proof.
 intros h0 h1.
 refine (mul_fix _zh _sh (-116) (-232) (-348) h0 h1 _) ; finalize.
Qed.
Lemma l96 : s1 -> p122 (* FIX(zh * sh, -348) *).
Proof.
 intros h0.
 assert (h1 := l43 h0).
 assert (h2 := l97 h0).
 apply t84. exact h1. exact h2.
Qed.
Lemma t85 : p122 -> p121.
Proof.
 intros h0.
 refine (rel_of_fix_float_ne _ _ (-348) r26 i39 h0 _) ; finalize.
Qed.
Lemma l95 : s1 -> p121 (* REL(z3, zh * sh, [-1.11022e-16, 1.11022e-16]) *).
Proof.
 intros h0.
 assert (h1 := l96 h0).
 apply t85. exact h1.
Qed.
Lemma t86 : p118 -> p121 -> p117.
Proof.
 intros h0 h1.
 refine (bnd_of_nzr_rel _z3 r26 i39 h0 h1) ; finalize.
Qed.
Lemma l92 : s1 -> p117 (* BND((z3 - zh * sh) / (zh * sh), [-1.11022e-16, 1.11022e-16]) *).
Proof.
 intros h0.
 assert (h1 := l93 h0).
 assert (h2 := l95 h0).
 apply t86. exact h1. exact h2.
Qed.
Lemma t87 : p112 -> p117 -> p116.
Proof.
 intros h0 h1.
 refine (add r59 r74 i61 i39 i60 h0 h1 _) ; finalize.
Qed.
Lemma l91 : s1 -> p116 (* BND(1 + (z3 - zh * sh) / (zh * sh), [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l87 h0).
 assert (h2 := l92 h0).
 apply t87. exact h1. exact h2.
Qed.
Lemma t88 : p111 -> p116 -> p110.
Proof.
 intros h0 h1.
 refine (mul_pp r70 r73 i60 i60 i59 h0 h1 _) ; finalize.
Qed.
Lemma l85 : s1 -> p110 (* BND((1 + (sh - zh * zh) / (zh * zh)) * (1 + (z3 - zh * sh) / (zh * sh)), [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l86 h0).
 assert (h2 := l91 h0).
 apply t88. exact h1. exact h2.
Qed.
Lemma t89 : p110 -> p112 -> p109.
Proof.
 intros h0 h1.
 refine (sub r69 r59 i59 i61 i58 h0 h1 _) ; finalize.
Qed.
Lemma l84 : s1 -> p109 (* BND((1 + (sh - zh * zh) / (zh * zh)) * (1 + (z3 - zh * sh) / (zh * sh)) - 1, [-2.22045e-16, 2.22045e-16]) *).
Proof.
 intros h0.
 assert (h1 := l85 h0).
 assert (h2 := l87 h0).
 apply t89. exact h1. exact h2.
Qed.
Definition f66 := Float2 (0) (0).
Definition i63 := makepairF f66 f66.
Notation p124 := (REL r60 r68 i63). (* REL((z3 - zh * zh * zh) / (zh * zh * zh), (1 + (sh - zh * zh) / (zh * zh)) * (1 + (z3 - zh * sh) / (zh * sh)) - 1, [0, 0]) *)
Notation p125 := (r60 = r68). (* EQL((z3 - zh * zh * zh) / (zh * zh * zh), (1 + (sh - zh * zh) / (zh * zh)) * (1 + (z3 - zh * sh) / (zh * sh)) - 1) *)
Lemma t90 : p11 -> p119 -> p125.
Proof.
 intros h0 h1.
 refine (b2 h0 h1) ; finalize.
Qed.
Lemma l99 : s1 -> p125 (* EQL((z3 - zh * zh * zh) / (zh * zh * zh), (1 + (sh - zh * zh) / (zh * zh)) * (1 + (z3 - zh * sh) / (zh * sh)) - 1) *).
Proof.
 intros h0.
 assert (h1 := l10 h0).
 assert (h2 := l94 h0).
 apply t90. exact h1. exact h2.
Qed.
Notation p126 := (REL r68 r68 i63). (* REL((1 + (sh - zh * zh) / (zh * zh)) * (1 + (z3 - zh * sh) / (zh * sh)) - 1, (1 + (sh - zh * zh) / (zh * zh)) * (1 + (z3 - zh * sh) / (zh * sh)) - 1, [0, 0]) *)
Lemma t91 : p126.
Proof.
 refine (rel_refl r68 i63 _) ; finalize.
Qed.
Lemma l100 : s1 -> p126 (* REL((1 + (sh - zh * zh) / (zh * zh)) * (1 + (z3 - zh * sh) / (zh * sh)) - 1, (1 + (sh - zh * zh) / (zh * zh)) * (1 + (z3 - zh * sh) / (zh * sh)) - 1, [0, 0]) *).
Proof.
 intros h0.
 apply t91.
Qed.
Lemma t92 : p125 -> p126 -> p124.
Proof.
 intros h0 h1.
 refine (rel_rewrite_1 r60 r68 r68 i63 h0 h1) ; finalize.
Qed.
Lemma l98 : s1 -> p124 (* REL((z3 - zh * zh * zh) / (zh * zh * zh), (1 + (sh - zh * zh) / (zh * zh)) * (1 + (z3 - zh * sh) / (zh * sh)) - 1, [0, 0]) *).
Proof.
 intros h0.
 assert (h1 := l99 h0).
 assert (h2 := l100 h0).
 apply t92. exact h1. exact h2.
Qed.
Lemma t93 : p109 -> p124 -> p108.
Proof.
 intros h0 h1.
 refine (bnd_of_bnd_rel_o r60 r68 i58 i63 i58 h0 h1 _) ; finalize.
Qed.
Lemma l83 : s1 -> p108 (* BND((z3 - zh * zh * zh) / (zh * zh * zh), [-2.22045e-16, 2.22045e-16]) *).
Proof.
 intros h0.
 assert (h1 := l84 h0).
 assert (h2 := l98 h0).
 apply t93. exact h1. exact h2.
Qed.
Lemma t94 : p5 -> p108 -> p107.
Proof.
 intros h0 h1.
 refine (rel_of_nzr_bnd _z3 r2 i58 h0 h1) ; finalize.
Qed.
Lemma l82 : s1 -> p107 (* REL(z3, zh * zh * zh, [-2.22045e-16, 2.22045e-16]) *).
Proof.
 intros h0.
 assert (h1 := l5 h0).
 assert (h2 := l83 h0).
 apply t94. exact h1. exact h2.
Qed.
Definition f67 := Float2 (-247370687365161147913660848298693390406958910888485127788890449290852621262507725375736075299175468823531736257133886077) (-450).
Definition f68 := Float2 (30921335920645143515779791885379371864525785010295213004294831057419349785032051256503745850662738997433828895443966847) (-447).
Definition i64 := makepairF f67 f68.
Notation p127 := (REL _w _W i64). (* REL(w, W, [-8.50844e-17, 8.50844e-17]) *)
Definition f69 := Float2 (-487043613275218434434594877708075242595788009498842619556963002639866009148620876219938470695136084696449183589587045561) (-451).
Definition f70 := Float2 (487043613275218434434594877708075242595788009498842619556963002639866009148620876219938470695136084696449183589587045561) (-451).
Definition i65 := makepairF f69 f70.
Notation p128 := (REL _w r29 i65). (* REL(w, c3 + float<53,-1074,ne>(zh * w4), [-8.37606e-17, 8.37606e-17]) *)
Notation p129 := (NZR r29). (* NZR(c3 + float<53,-1074,ne>(zh * w4)) *)
Notation p130 := (ABS r29 i37). (* ABS(c3 + float<53,-1074,ne>(zh * w4), [0.25, 0.5]) *)
Definition i66 := makepairF f66 f13.
Notation p131 := (ABS r30 i66). (* ABS(float<53,-1074,ne>(zh * w4), [0, 0.0625]) *)
Definition f71 := Float2 (-4531989986316473) (-61).
Definition i67 := makepairF f71 f13.
Notation p132 := (BND r30 i67). (* BND(float<53,-1074,ne>(zh * w4), [-0.00196544, 0.0625]) *)
Definition f72 := Float2 (-18127959945265893) (-63).
Definition i68 := makepairF f72 f13.
Notation p133 := (BND r31 i68). (* BND(zh * w4, [-0.00196544, 0.0625]) *)
Definition f73 := Float2 (-566491497198395) (-51).
Definition i69 := makepairF f73 f38.
Notation p134 := (BND _w4 i69). (* BND(w4, [-0.251573, -0.125]) *)
Definition f74 := Float2 (-9063863955174321) (-55).
Definition i70 := makepairF f74 f38.
Notation p135 := (BND r33 i70). (* BND(c4 + float<53,-1074,ne>(zh * w5), [-0.251573, -0.125]) *)
Definition f75 := Float2 (-56664700433239) (-55).
Definition i71 := makepairF f75 f14.
Notation p136 := (BND r34 i71). (* BND(float<53,-1074,ne>(zh * w5), [-0.00157276, 0.125]) *)
Notation p137 := (BND r35 i71). (* BND(zh * w5, [-0.00157276, 0.125]) *)
Definition f76 := Float2 (56663975134357) (-48).
Definition i72 := makepairF f14 f76.
Notation p138 := (BND _w5 i72). (* BND(w5, [0.125, 0.201311]) *)
Definition f77 := Float2 (916291838792053159) (-62).
Definition i73 := makepairF f77 f76.
Notation p139 := (BND r37 i73). (* BND(c5 + float<53,-1074,ne>(zh * w6), [0.198689, 0.201311]) *)
Definition f78 := Float2 (-6045364904622041) (-62).
Definition f79 := Float2 (184489895771) (-47).
Definition i74 := makepairF f78 f79.
Notation p140 := (BND r38 i74). (* BND(float<53,-1074,ne>(zh * w6), [-0.00131088, 0.00131088]) *)
Definition f80 := Float2 (-48362919236976331) (-65).
Definition i75 := makepairF f80 f79.
Notation p141 := (BND r39 i75). (* BND(zh * w6, [-0.00131088, 0.00131088]) *)
Definition f81 := Float2 (-1099525701525) (-47).
Definition f82 := Float2 (36029258187565811) (-62).
Definition i76 := makepairF f81 f82.
Notation p142 := (BND _zh i76). (* BND(zh, [-0.0078126, 0.0078126]) *)
Lemma t95 : p142 -> p83 -> p141.
Proof.
 intros h0 h1.
 refine (mul_on _zh _w6 i76 i41 i75 h0 h1 _) ; finalize.
Qed.
Lemma l115 : s1 -> p141 (* BND(zh * w6, [-0.00131088, 0.00131088]) *).
Proof.
 intros h0.
 assert (h1 := l72 h0).
 assert (h2 := l68 h0).
 apply t95. refine (subset _zh i43 i76 h1 _) ; finalize. exact h2.
Qed.
Lemma t96 : p141 -> p140.
Proof.
 intros h0.
 refine (float_round_ne _ _ r39 i75 i74 h0 _) ; finalize.
Qed.
Lemma l114 : s1 -> p140 (* BND(float<53,-1074,ne>(zh * w6), [-0.00131088, 0.00131088]) *).
Proof.
 intros h0.
 assert (h1 := l115 h0).
 apply t96. exact h1.
Qed.
Definition f83 := Float2 (56294995342815) (-48).
Definition i77 := makepairF f17 f83.
Notation p143 := (BND _c5 i77). (* BND(c5, [0.2, 0.2]) *)
Lemma t97 : p143 -> p140 -> p139.
Proof.
 intros h0 h1.
 refine (add _c5 r38 i77 i74 i73 h0 h1 _) ; finalize.
Qed.
Lemma l113 : s1 -> p139 (* BND(c5 + float<53,-1074,ne>(zh * w6), [0.198689, 0.201311]) *).
Proof.
 intros h0.
 assert (h1 := l22 h0).
 assert (h2 := l114 h0).
 apply t97. refine (subset _c5 i14 i77 h1 _) ; finalize. exact h2.
Qed.
Notation p144 := (BND r37 i72). (* BND(c5 + float<53,-1074,ne>(zh * w6), [0.125, 0.201311]) *)
Lemma t98 : p144 -> p138.
Proof.
 intros h0.
 refine (float_round_ne _ _ r37 i72 i72 h0 _) ; finalize.
Qed.
Lemma l112 : s1 -> p138 (* BND(w5, [0.125, 0.201311]) *).
Proof.
 intros h0.
 assert (h1 := l113 h0).
 apply t98. refine (subset r37 i73 i72 h1 _) ; finalize.
Qed.
Definition i78 := makepairF f54 f32.
Notation p145 := (BND _zh i78). (* BND(zh, [-0.0078126, 0.5]) *)
Lemma t99 : p145 -> p138 -> p137.
Proof.
 intros h0 h1.
 refine (mul_op _zh _w5 i78 i72 i71 h0 h1 _) ; finalize.
Qed.
Lemma l111 : s1 -> p137 (* BND(zh * w5, [-0.00157276, 0.125]) *).
Proof.
 intros h0.
 assert (h1 := l72 h0).
 assert (h2 := l112 h0).
 apply t99. refine (subset _zh i43 i78 h1 _) ; finalize. exact h2.
Qed.
Lemma t100 : p137 -> p136.
Proof.
 intros h0.
 refine (float_round_ne _ _ r35 i71 i71 h0 _) ; finalize.
Qed.
Lemma l110 : s1 -> p136 (* BND(float<53,-1074,ne>(zh * w5), [-0.00157276, 0.125]) *).
Proof.
 intros h0.
 assert (h1 := l111 h0).
 apply t100. exact h1.
Qed.
Definition f84 := Float2 (-1) (-2).
Definition i79 := makepairF f16 f84.
Notation p146 := (BND _c4 i79). (* BND(c4, [-0.25, -0.25]) *)
Lemma t101 : p146 -> p136 -> p135.
Proof.
 intros h0 h1.
 refine (add _c4 r34 i79 i71 i70 h0 h1 _) ; finalize.
Qed.
Lemma l109 : s1 -> p135 (* BND(c4 + float<53,-1074,ne>(zh * w5), [-0.251573, -0.125]) *).
Proof.
 intros h0.
 assert (h1 := l18 h0).
 assert (h2 := l110 h0).
 apply t101. refine (subset _c4 i12 i79 h1 _) ; finalize. exact h2.
Qed.
Lemma t102 : p135 -> p134.
Proof.
 intros h0.
 refine (float_round_ne _ _ r33 i70 i69 h0 _) ; finalize.
Qed.
Lemma l108 : s1 -> p134 (* BND(w4, [-0.251573, -0.125]) *).
Proof.
 intros h0.
 assert (h1 := l109 h0).
 apply t102. exact h1.
Qed.
Definition i80 := makepairF f38 f82.
Notation p147 := (BND _zh i80). (* BND(zh, [-0.125, 0.0078126]) *)
Lemma t103 : p147 -> p134 -> p133.
Proof.
 intros h0 h1.
 refine (mul_on _zh _w4 i80 i69 i68 h0 h1 _) ; finalize.
Qed.
Lemma l107 : s1 -> p133 (* BND(zh * w4, [-0.00196544, 0.0625]) *).
Proof.
 intros h0.
 assert (h1 := l72 h0).
 assert (h2 := l108 h0).
 apply t103. refine (subset _zh i43 i80 h1 _) ; finalize. exact h2.
Qed.
Lemma t104 : p133 -> p132.
Proof.
 intros h0.
 refine (float_round_ne _ _ r31 i68 i67 h0 _) ; finalize.
Qed.
Lemma l106 : s1 -> p132 (* BND(float<53,-1074,ne>(zh * w4), [-0.00196544, 0.0625]) *).
Proof.
 intros h0.
 assert (h1 := l107 h0).
 apply t104. exact h1.
Qed.
Definition i81 := makepairF f45 f13.
Notation p148 := (BND r30 i81). (* BND(float<53,-1074,ne>(zh * w4), [-0.0625, 0.0625]) *)
Lemma t105 : p148 -> p131.
Proof.
 intros h0.
 refine (abs_of_bnd_o r30 i81 i66 h0 _) ; finalize.
Qed.
Lemma l105 : s1 -> p131 (* ABS(float<53,-1074,ne>(zh * w4), [0, 0.0625]) *).
Proof.
 intros h0.
 assert (h1 := l106 h0).
 apply t105. refine (subset r30 i67 i81 h1 _) ; finalize.
Qed.
Definition f85 := Float2 (3) (-3).
Definition i82 := makepairF f34 f85.
Notation p149 := (ABS _c3 i82). (* ABS(c3, [0.3125, 0.375]) *)
Lemma t106 : p149 -> p131 -> p130.
Proof.
 intros h0 h1.
 refine (add_aa_p _c3 r30 i82 i66 i37 h0 h1 _) ; finalize.
Qed.
Lemma l104 : s1 -> p130 (* ABS(c3 + float<53,-1074,ne>(zh * w4), [0.25, 0.5]) *).
Proof.
 intros h0.
 assert (h1 := l13 h0).
 assert (h2 := l105 h0).
 apply t106. refine (abs_subset _c3 i8 i82 h1 _) ; finalize. exact h2.
Qed.
Notation p150 := (ABS r29 i7). (* ABS(c3 + float<53,-1074,ne>(zh * w4), [0.25, 1]) *)
Lemma t107 : p150 -> p129.
Proof.
 intros h0.
 refine (nzr_of_abs r29 i7 h0 _) ; finalize.
Qed.
Lemma l103 : s1 -> p129 (* NZR(c3 + float<53,-1074,ne>(zh * w4)) *).
Proof.
 intros h0.
 assert (h1 := l104 h0).
 apply t107. refine (abs_subset r29 i37 i7 h1 _) ; finalize.
Qed.
Notation r78 := ((_w - r29)%R).
Notation r77 := ((r78 / r29)%R).
Notation p151 := (BND r77 i65). (* BND((w - (c3 + float<53,-1074,ne>(zh * w4))) / (c3 + float<53,-1074,ne>(zh * w4)), [-8.37606e-17, 8.37606e-17]) *)
Definition f86 := Float2 (-1) (-55).
Definition f87 := Float2 (1) (-55).
Definition i83 := makepairF f86 f87.
Notation p152 := (BND r78 i83). (* BND(w - (c3 + float<53,-1074,ne>(zh * w4)), [-2.77556e-17, 2.77556e-17]) *)
Lemma t108 : p130 -> p152.
Proof.
 intros h0.
 refine (float_absolute_wide_ne _ _ r29 i37 i83 h0 _) ; finalize.
Qed.
Lemma l117 : s1 -> p152 (* BND(w - (c3 + float<53,-1074,ne>(zh * w4)), [-2.77556e-17, 2.77556e-17]) *).
Proof.
 intros h0.
 assert (h1 := l104 h0).
 apply t108. exact h1.
Qed.
Definition f88 := Float2 (764082346418248135) (-61).
Definition i84 := makepairF f88 f8.
Notation p153 := (BND r29 i84). (* BND(c3 + float<53,-1074,ne>(zh * w4), [0.331368, 1]) *)
Definition i85 := makepairF f11 f32.
Notation p154 := (BND _c3 i85). (* BND(c3, [0.333333, 0.5]) *)
Definition i86 := makepairF f71 f32.
Notation p155 := (BND r30 i86). (* BND(float<53,-1074,ne>(zh * w4), [-0.00196544, 0.5]) *)
Lemma t109 : p154 -> p155 -> p153.
Proof.
 intros h0 h1.
 refine (add _c3 r30 i85 i86 i84 h0 h1 _) ; finalize.
Qed.
Lemma l118 : s1 -> p153 (* BND(c3 + float<53,-1074,ne>(zh * w4), [0.331368, 1]) *).
Proof.
 intros h0.
 assert (h1 := l14 h0).
 assert (h2 := l106 h0).
 apply t109. refine (subset _c3 i8 i85 h1 _) ; finalize. refine (subset r30 i67 i86 h2 _) ; finalize.
Qed.
Lemma t110 : p152 -> p153 -> p151.
Proof.
 intros h0 h1.
 refine (div_op r78 r29 i83 i84 i65 h0 h1 _) ; finalize.
Qed.
Lemma l116 : s1 -> p151 (* BND((w - (c3 + float<53,-1074,ne>(zh * w4))) / (c3 + float<53,-1074,ne>(zh * w4)), [-8.37606e-17, 8.37606e-17]) *).
Proof.
 intros h0.
 assert (h1 := l117 h0).
 assert (h2 := l118 h0).
 apply t110. exact h1. exact h2.
Qed.
Lemma t111 : p129 -> p151 -> p128.
Proof.
 intros h0 h1.
 refine (rel_of_nzr_bnd _w r29 i65 h0 h1) ; finalize.
Qed.
Lemma l102 : s1 -> p128 (* REL(w, c3 + float<53,-1074,ne>(zh * w4), [-8.37606e-17, 8.37606e-17]) *).
Proof.
 intros h0.
 assert (h1 := l103 h0).
 assert (h2 := l116 h0).
 apply t111. exact h1. exact h2.
Qed.
Definition f89 := Float2 (-15395522910207724074991958971490085759280643841766070523030468532606510127066745834457673161942978664740462553036432107) (-452).
Definition f90 := Float2 (1924440363775965293278157965390318744096658970757648897394625974084896987445725457454280966055140124025693678674629003) (-449).
Definition i87 := makepairF f89 f90.
Notation p156 := (REL r29 _W i87). (* REL(c3 + float<53,-1074,ne>(zh * w4), W, [-1.32384e-18, 1.32384e-18]) *)
Notation p157 := (REL _c3 _c3 i63). (* REL(c3, c3, [0, 0]) *)
Lemma t112 : p157.
Proof.
 refine (rel_refl _c3 i63 _) ; finalize.
Qed.
Lemma l120 : s1 -> p157 (* REL(c3, c3, [0, 0]) *).
Proof.
 intros h0.
 apply t112.
Qed.
Definition f91 := Float2 (-2534811751321624890387052175366857805922756020718978447446825216296841938461900083984353049704086282868898530942160323) (-442).
Definition f92 := Float2 (40556988021146002800346049313229207906040209780449423554619364992925236275942381145214154440176487387177807683182235263) (-446).
Definition i88 := makepairF f91 f92.
Notation p158 := (REL r30 r8 i88). (* REL(float<53,-1074,ne>(zh * w4), zh * (c4 + zh * (c5 + zh * (c6 + zh * (c7 + zh * (c8 + zh * c9))))), [-2.23197e-16, 2.23197e-16]) *)
Notation p159 := (REL r30 r31 i39). (* REL(float<53,-1074,ne>(zh * w4), zh * w4, [-1.11022e-16, 1.11022e-16]) *)
Notation p160 := (FIX r31 (-519)). (* FIX(zh * w4, -519) *)
Notation p161 := (FIX _w4 (-403)). (* FIX(w4, -403) *)
Notation p162 := (FIX r33 (-403)). (* FIX(c4 + float<53,-1074,ne>(zh * w5), -403) *)
Notation p163 := (FIX r34 (-403)). (* FIX(float<53,-1074,ne>(zh * w5), -403) *)
Notation p164 := (FIX r35 (-403)). (* FIX(zh * w5, -403) *)
Notation p165 := (FIX _w5 (-287)). (* FIX(w5, -287) *)
Notation p166 := (FIX r37 (-287)). (* FIX(c5 + float<53,-1074,ne>(zh * w6), -287) *)
Notation p167 := (FIX r38 (-287)). (* FIX(float<53,-1074,ne>(zh * w6), -287) *)
Notation p168 := (FIX r39 (-287)). (* FIX(zh * w6, -287) *)
Notation p169 := (FIX _w6 (-171)). (* FIX(w6, -171) *)
Notation p170 := (FIX r41 (-171)). (* FIX(c6 + float<53,-1074,ne>(zh * w7), -171) *)
Notation p171 := (FIX _c6 (-52)). (* FIX(c6, -52) *)
Lemma t113 : p26 -> p171.
Proof.
 intros h0.
 refine (fix_of_singleton_bnd _c6 i15 (-52) h0 _) ; finalize.
Qed.
Lemma l134 : s1 -> p171 (* FIX(c6, -52) *).
Proof.
 intros h0.
 assert (h1 := l25 h0).
 apply t113. exact h1.
Qed.
Notation p172 := (FIX r42 (-171)). (* FIX(float<53,-1074,ne>(zh * w7), -171) *)
Notation p173 := (FIX r43 (-171)). (* FIX(zh * w7, -171) *)
Notation p174 := (FIX _w7 (-55)). (* FIX(w7, -55) *)
Notation p175 := (FLT _w7 (53)). (* FLT(w7, 53) *)
Lemma t114 : p175.
Proof.
 refine (flt_of_float _ _ _ (53) _ _) ; finalize.
Qed.
Lemma l138 : s1 -> p175 (* FLT(w7, 53) *).
Proof.
 intros h0.
 apply t114.
Qed.
Notation p176 := (ABS _w7 i40). (* ABS(w7, [0.125, 0.1875]) *)
Notation p177 := (BND _w7 i40). (* BND(w7, [0.125, 0.1875]) *)
Lemma t115 : p177 -> p176.
Proof.
 intros h0.
 refine (abs_of_bnd_p _w7 i40 i40 h0 _) ; finalize.
Qed.
Lemma l139 : s1 -> p176 (* ABS(w7, [0.125, 0.1875]) *).
Proof.
 intros h0.
 assert (h1 := l73 h0).
 apply t115. refine (subset _w7 i44 i40 h1 _) ; finalize.
Qed.
Notation p178 := (ABS _w7 i10). (* ABS(w7, [0.125, 1]) *)
Lemma t116 : p175 -> p178 -> p174.
Proof.
 intros h0 h1.
 refine (fix_of_flt_bnd _w7 i10 (-55) (53) h0 h1 _) ; finalize.
Qed.
Lemma l137 : s1 -> p174 (* FIX(w7, -55) *).
Proof.
 intros h0.
 assert (h1 := l138 h0).
 assert (h2 := l139 h0).
 apply t116. exact h1. refine (abs_subset _w7 i40 i10 h2 _) ; finalize.
Qed.
Lemma t117 : p58 -> p174 -> p173.
Proof.
 intros h0 h1.
 refine (mul_fix _zh _w7 (-116) (-55) (-171) h0 h1 _) ; finalize.
Qed.
Lemma l136 : s1 -> p173 (* FIX(zh * w7, -171) *).
Proof.
 intros h0.
 assert (h1 := l43 h0).
 assert (h2 := l137 h0).
 apply t117. exact h1. exact h2.
Qed.
Lemma t118 : p173 -> p172.
Proof.
 intros h0.
 refine (fix_float_of_fix _ _ _ (-171) (-171) r43 h0 _) ; finalize.
Qed.
Lemma l135 : s1 -> p172 (* FIX(float<53,-1074,ne>(zh * w7), -171) *).
Proof.
 intros h0.
 assert (h1 := l136 h0).
 apply t118. exact h1.
Qed.
Lemma t119 : p171 -> p172 -> p170.
Proof.
 intros h0 h1.
 refine (add_fix _c6 r42 (-52) (-171) (-171) h0 h1 _) ; finalize.
Qed.
Lemma l133 : s1 -> p170 (* FIX(c6 + float<53,-1074,ne>(zh * w7), -171) *).
Proof.
 intros h0.
 assert (h1 := l134 h0).
 assert (h2 := l135 h0).
 apply t119. exact h1. exact h2.
Qed.
Lemma t120 : p170 -> p169.
Proof.
 intros h0.
 refine (fix_float_of_fix _ _ _ (-171) (-171) r41 h0 _) ; finalize.
Qed.
Lemma l132 : s1 -> p169 (* FIX(w6, -171) *).
Proof.
 intros h0.
 assert (h1 := l133 h0).
 apply t120. exact h1.
Qed.
Lemma t121 : p58 -> p169 -> p168.
Proof.
 intros h0 h1.
 refine (mul_fix _zh _w6 (-116) (-171) (-287) h0 h1 _) ; finalize.
Qed.
Lemma l131 : s1 -> p168 (* FIX(zh * w6, -287) *).
Proof.
 intros h0.
 assert (h1 := l43 h0).
 assert (h2 := l132 h0).
 apply t121. exact h1. exact h2.
Qed.
Lemma t122 : p168 -> p167.
Proof.
 intros h0.
 refine (fix_float_of_fix _ _ _ (-287) (-287) r39 h0 _) ; finalize.
Qed.
Lemma l130 : s1 -> p167 (* FIX(float<53,-1074,ne>(zh * w6), -287) *).
Proof.
 intros h0.
 assert (h1 := l131 h0).
 apply t122. exact h1.
Qed.
Lemma t123 : p77 -> p167 -> p166.
Proof.
 intros h0 h1.
 refine (add_fix _c5 r38 (-55) (-287) (-287) h0 h1 _) ; finalize.
Qed.
Lemma l129 : s1 -> p166 (* FIX(c5 + float<53,-1074,ne>(zh * w6), -287) *).
Proof.
 intros h0.
 assert (h1 := l62 h0).
 assert (h2 := l130 h0).
 apply t123. exact h1. exact h2.
Qed.
Lemma t124 : p166 -> p165.
Proof.
 intros h0.
 refine (fix_float_of_fix _ _ _ (-287) (-287) r37 h0 _) ; finalize.
Qed.
Lemma l128 : s1 -> p165 (* FIX(w5, -287) *).
Proof.
 intros h0.
 assert (h1 := l129 h0).
 apply t124. exact h1.
Qed.
Lemma t125 : p58 -> p165 -> p164.
Proof.
 intros h0 h1.
 refine (mul_fix _zh _w5 (-116) (-287) (-403) h0 h1 _) ; finalize.
Qed.
Lemma l127 : s1 -> p164 (* FIX(zh * w5, -403) *).
Proof.
 intros h0.
 assert (h1 := l43 h0).
 assert (h2 := l128 h0).
 apply t125. exact h1. exact h2.
Qed.
Lemma t126 : p164 -> p163.
Proof.
 intros h0.
 refine (fix_float_of_fix _ _ _ (-403) (-403) r35 h0 _) ; finalize.
Qed.
Lemma l126 : s1 -> p163 (* FIX(float<53,-1074,ne>(zh * w5), -403) *).
Proof.
 intros h0.
 assert (h1 := l127 h0).
 apply t126. exact h1.
Qed.
Lemma t127 : p72 -> p163 -> p162.
Proof.
 intros h0 h1.
 refine (add_fix _c4 r34 (-54) (-403) (-403) h0 h1 _) ; finalize.
Qed.
Lemma l125 : s1 -> p162 (* FIX(c4 + float<53,-1074,ne>(zh * w5), -403) *).
Proof.
 intros h0.
 assert (h1 := l57 h0).
 assert (h2 := l126 h0).
 apply t127. exact h1. exact h2.
Qed.
Lemma t128 : p162 -> p161.
Proof.
 intros h0.
 refine (fix_float_of_fix _ _ _ (-403) (-403) r33 h0 _) ; finalize.
Qed.
Lemma l124 : s1 -> p161 (* FIX(w4, -403) *).
Proof.
 intros h0.
 assert (h1 := l125 h0).
 apply t128. exact h1.
Qed.
Lemma t129 : p58 -> p161 -> p160.
Proof.
 intros h0 h1.
 refine (mul_fix _zh _w4 (-116) (-403) (-519) h0 h1 _) ; finalize.
Qed.
Lemma l123 : s1 -> p160 (* FIX(zh * w4, -519) *).
Proof.
 intros h0.
 assert (h1 := l43 h0).
 assert (h2 := l124 h0).
 apply t129. exact h1. exact h2.
Qed.
Lemma t130 : p160 -> p159.
Proof.
 intros h0.
 refine (rel_of_fix_float_ne _ _ (-519) r31 i39 h0 _) ; finalize.
Qed.
Lemma l122 : s1 -> p159 (* REL(float<53,-1074,ne>(zh * w4), zh * w4, [-1.11022e-16, 1.11022e-16]) *).
Proof.
 intros h0.
 assert (h1 := l123 h0).
 apply t130. exact h1.
Qed.
Definition f93 := Float2 (-636973776518500848515356723408983727496777364374037430441508831152907691852126914577581547941014132102104806229518253) (-441).
Definition f94 := Float2 (20383160848592027180673731907464389855640082196082199854756123569227670342707998709377469231597653862731317738987007877) (-446).
Definition i89 := makepairF f93 f94.
Notation p179 := (REL r31 r8 i89). (* REL(zh * w4, zh * (c4 + zh * (c5 + zh * (c6 + zh * (c7 + zh * (c8 + zh * c9))))), [-1.12174e-16, 1.12174e-16]) *)
Notation p180 := (REL _w4 r9 i89). (* REL(w4, c4 + zh * (c5 + zh * (c6 + zh * (c7 + zh * (c8 + zh * c9)))), [-1.12174e-16, 1.12174e-16]) *)
Notation p181 := (REL _w4 r33 i39). (* REL(w4, c4 + float<53,-1074,ne>(zh * w5), [-1.11022e-16, 1.11022e-16]) *)
Notation p182 := (FIX r33 (-1074)). (* FIX(c4 + float<53,-1074,ne>(zh * w5), -1074) *)
Notation p183 := (FIX r34 (-1074)). (* FIX(float<53,-1074,ne>(zh * w5), -1074) *)
Lemma t131 : p183.
Proof.
 refine (fix_of_float _ _ _ _ (-1074) _) ; finalize.
Qed.
Lemma l144 : s1 -> p183 (* FIX(float<53,-1074,ne>(zh * w5), -1074) *).
Proof.
 intros h0.
 apply t131.
Qed.
Lemma t132 : p72 -> p183 -> p182.
Proof.
 intros h0 h1.
 refine (add_fix _c4 r34 (-54) (-1074) (-1074) h0 h1 _) ; finalize.
Qed.
Lemma l143 : s1 -> p182 (* FIX(c4 + float<53,-1074,ne>(zh * w5), -1074) *).
Proof.
 intros h0.
 assert (h1 := l57 h0).
 assert (h2 := l144 h0).
 apply t132. exact h1. exact h2.
Qed.
Lemma t133 : p182 -> p181.
Proof.
 intros h0.
 refine (rel_of_fix_float_ne _ _ (-1074) r33 i39 h0 _) ; finalize.
Qed.
Lemma l142 : s1 -> p181 (* REL(w4, c4 + float<53,-1074,ne>(zh * w5), [-1.11022e-16, 1.11022e-16]) *).
Proof.
 intros h0.
 assert (h1 := l143 h0).
 apply t133. exact h1.
Qed.
Definition f95 := Float2 (-52333419009513454761313328625256421956035685549036681666024587030461215830487466966038803603917404544920316947247637) (-444).
Definition f96 := Float2 (418667352076107601492313359007569885838007004729426363920719875629069582711392698879179222254649495399083823521925501) (-447).
Definition i90 := makepairF f95 f96.
Notation p184 := (REL r33 r9 i90). (* REL(c4 + float<53,-1074,ne>(zh * w5), c4 + zh * (c5 + zh * (c6 + zh * (c7 + zh * (c8 + zh * c9)))), [-1.15202e-18, 1.15202e-18]) *)
Notation p185 := (REL _c4 _c4 i63). (* REL(c4, c4, [0, 0]) *)
Lemma t134 : p185.
Proof.
 refine (rel_refl _c4 i63 _) ; finalize.
Qed.
Lemma l146 : s1 -> p185 (* REL(c4, c4, [0, 0]) *).
Proof.
 intros h0.
 apply t134.
Qed.
Definition f97 := Float2 (-516648892088469753884144522622052686353892672804464582102375996148775619884296469547028056766222624009993074535711673) (-440).
Definition f98 := Float2 (516648892088469799047484610208020864684507502281250688877994047166778556149450805741229544498817259925234581533258615) (-440).
Definition i91 := makepairF f97 f98.
Notation p186 := (REL r34 r11 i91). (* REL(float<53,-1074,ne>(zh * w5), zh * (c5 + zh * (c6 + zh * (c7 + zh * (c8 + zh * c9)))), [-1.81969e-16, 1.81969e-16]) *)
Notation p187 := (REL r34 r35 i39). (* REL(float<53,-1074,ne>(zh * w5), zh * w5, [-1.11022e-16, 1.11022e-16]) *)
Lemma t135 : p164 -> p187.
Proof.
 intros h0.
 refine (rel_of_fix_float_ne _ _ (-403) r35 i39 h0 _) ; finalize.
Qed.
Lemma l148 : s1 -> p187 (* REL(float<53,-1074,ne>(zh * w5), zh * w5, [-1.11022e-16, 1.11022e-16]) *).
Proof.
 intros h0.
 assert (h1 := l127 h0).
 apply t135. exact h1.
Qed.
Definition f99 := Float2 (-805731370069255770197800678649661747827035995274240274254527514839211999048102771484900679581391459859625143485674791) (-442).
Definition f100 := Float2 (100716421258656971492857160782680122382657360909047680624370229044728259992631372777335360379320900318973211971052589) (-439).
Definition i92 := makepairF f99 f100.
Notation p188 := (REL r35 r11 i92). (* REL(zh * w5, zh * (c5 + zh * (c6 + zh * (c7 + zh * (c8 + zh * c9)))), [-7.09467e-17, 7.09467e-17]) *)
Notation p189 := (REL _w5 r12 i92). (* REL(w5, c5 + zh * (c6 + zh * (c7 + zh * (c8 + zh * c9))), [-7.09467e-17, 7.09467e-17]) *)
Definition f101 := Float2 (-396619665004218434047154466665586970876610955331458844399807073044082918985456835884991658559365644954906072927965251) (-441).
Definition f102 := Float2 (396619665004218434047154466665586970876610955331458844399807073044082918985456835884991658559365644954906072927965251) (-441).
Definition i93 := makepairF f101 f102.
Notation p190 := (REL _w5 r37 i93). (* REL(w5, c5 + float<53,-1074,ne>(zh * w6), [-6.98467e-17, 6.98467e-17]) *)
Notation p191 := (NZR r37). (* NZR(c5 + float<53,-1074,ne>(zh * w6)) *)
Definition i94 := makepairF f14 f10.
Notation p192 := (ABS r37 i94). (* ABS(c5 + float<53,-1074,ne>(zh * w6), [0.125, 0.25]) *)
Definition i95 := makepairF f66 f20.
Notation p193 := (ABS r38 i95). (* ABS(float<53,-1074,ne>(zh * w6), [0, 0.03125]) *)
Definition f103 := Float2 (-1) (-5).
Definition i96 := makepairF f103 f20.
Notation p194 := (BND r38 i96). (* BND(float<53,-1074,ne>(zh * w6), [-0.03125, 0.03125]) *)
Lemma t136 : p194 -> p193.
Proof.
 intros h0.
 refine (abs_of_bnd_o r38 i96 i95 h0 _) ; finalize.
Qed.
Lemma l154 : s1 -> p193 (* ABS(float<53,-1074,ne>(zh * w6), [0, 0.03125]) *).
Proof.
 intros h0.
 assert (h1 := l114 h0).
 apply t136. refine (subset r38 i74 i96 h1 _) ; finalize.
Qed.
Definition f104 := Float2 (7) (-5).
Definition i97 := makepairF f22 f104.
Notation p195 := (ABS _c5 i97). (* ABS(c5, [0.1875, 0.21875]) *)
Lemma t137 : p195 -> p193 -> p192.
Proof.
 intros h0 h1.
 refine (add_aa_p _c5 r38 i97 i95 i94 h0 h1 _) ; finalize.
Qed.
Lemma l153 : s1 -> p192 (* ABS(c5 + float<53,-1074,ne>(zh * w6), [0.125, 0.25]) *).
Proof.
 intros h0.
 assert (h1 := l21 h0).
 assert (h2 := l154 h0).
 apply t137. refine (abs_subset _c5 i14 i97 h1 _) ; finalize. exact h2.
Qed.
Notation p196 := (ABS r37 i10). (* ABS(c5 + float<53,-1074,ne>(zh * w6), [0.125, 1]) *)
Lemma t138 : p196 -> p191.
Proof.
 intros h0.
 refine (nzr_of_abs r37 i10 h0 _) ; finalize.
Qed.
Lemma l152 : s1 -> p191 (* NZR(c5 + float<53,-1074,ne>(zh * w6)) *).
Proof.
 intros h0.
 assert (h1 := l153 h0).
 apply t138. refine (abs_subset r37 i94 i10 h1 _) ; finalize.
Qed.
Notation r80 := ((_w5 - r37)%R).
Notation r79 := ((r80 / r37)%R).
Notation p197 := (BND r79 i93). (* BND((w5 - (c5 + float<53,-1074,ne>(zh * w6))) / (c5 + float<53,-1074,ne>(zh * w6)), [-6.98467e-17, 6.98467e-17]) *)
Definition f105 := Float2 (-1) (-56).
Definition f106 := Float2 (1) (-56).
Definition i98 := makepairF f105 f106.
Notation p198 := (BND r80 i98). (* BND(w5 - (c5 + float<53,-1074,ne>(zh * w6)), [-1.38778e-17, 1.38778e-17]) *)
Lemma t139 : p192 -> p198.
Proof.
 intros h0.
 refine (float_absolute_wide_ne _ _ r37 i94 i98 h0 _) ; finalize.
Qed.
Lemma l156 : s1 -> p198 (* BND(w5 - (c5 + float<53,-1074,ne>(zh * w6)), [-1.38778e-17, 1.38778e-17]) *).
Proof.
 intros h0.
 assert (h1 := l153 h0).
 apply t139. exact h1.
Qed.
Definition i99 := makepairF f77 f8.
Notation p199 := (BND r37 i99). (* BND(c5 + float<53,-1074,ne>(zh * w6), [0.198689, 1]) *)
Lemma t140 : p198 -> p199 -> p197.
Proof.
 intros h0 h1.
 refine (div_op r80 r37 i98 i99 i93 h0 h1 _) ; finalize.
Qed.
Lemma l155 : s1 -> p197 (* BND((w5 - (c5 + float<53,-1074,ne>(zh * w6))) / (c5 + float<53,-1074,ne>(zh * w6)), [-6.98467e-17, 6.98467e-17]) *).
Proof.
 intros h0.
 assert (h1 := l156 h0).
 assert (h2 := l113 h0).
 apply t140. exact h1. refine (subset r37 i73 i99 h2 _) ; finalize.
Qed.
Lemma t141 : p191 -> p197 -> p190.
Proof.
 intros h0 h1.
 refine (rel_of_nzr_bnd _w5 r37 i93 h0 h1) ; finalize.
Qed.
Lemma l151 : s1 -> p190 (* REL(w5, c5 + float<53,-1074,ne>(zh * w6), [-6.98467e-17, 6.98467e-17]) *).
Proof.
 intros h0.
 assert (h1 := l152 h0).
 assert (h2 := l155 h0).
 apply t141. exact h1. exact h2.
Qed.
Definition f107 := Float2 (-12492040060818902976020049124377421690925530610393170825130527510353201523663205081808464189248041295893273771117249) (-442).
Definition f108 := Float2 (12492040060818902976020049124377421690925530610393170825130527510353201523663205081808464189248041295893273771117249) (-442).
Definition i100 := makepairF f107 f108.
Notation p200 := (REL r37 r12 i100). (* REL(c5 + float<53,-1074,ne>(zh * w6), c5 + zh * (c6 + zh * (c7 + zh * (c8 + zh * c9))), [-1.09996e-18, 1.09996e-18]) *)
Notation p201 := (NZR r12). (* NZR(c5 + zh * (c6 + zh * (c7 + zh * (c8 + zh * c9)))) *)
Lemma t142 : p21 -> p201.
Proof.
 intros h0.
 refine (nzr_of_abs r12 i10 h0 _) ; finalize.
Qed.
Lemma l158 : s1 -> p201 (* NZR(c5 + zh * (c6 + zh * (c7 + zh * (c8 + zh * c9)))) *).
Proof.
 intros h0.
 assert (h1 := l20 h0).
 apply t142. exact h1.
Qed.
Notation r82 := ((r37 - r12)%R).
Notation r81 := ((r82 / r12)%R).
Notation p202 := (BND r81 i100). (* BND((c5 + float<53,-1074,ne>(zh * w6) - (c5 + zh * (c6 + zh * (c7 + zh * (c8 + zh * c9))))) / (c5 + zh * (c6 + zh * (c7 + zh * (c8 + zh * c9)))), [-1.09996e-18, 1.09996e-18]) *)
Definition f109 := Float2 (-158850076947710585982904894729433492349816328802797120937912667324297964678008681412743679212061206204406265726633129) (-448).
Definition f110 := Float2 (158850076947710585982904894729433492349816328802797120937912667324297964678008681412743679212061206204406265726633129) (-448).
Definition i101 := makepairF f109 f110.
Notation p203 := (BND r82 i101). (* BND(c5 + float<53,-1074,ne>(zh * w6) - (c5 + zh * (c6 + zh * (c7 + zh * (c8 + zh * c9)))), [-2.18549e-19, 2.18549e-19]) *)
Notation r83 := ((r38 - r14)%R).
Notation p204 := (BND r83 i101). (* BND(float<53,-1074,ne>(zh * w6) - zh * (c6 + zh * (c7 + zh * (c8 + zh * c9))), [-2.18549e-19, 2.18549e-19]) *)
Notation r85 := ((r38 - r39)%R).
Notation r86 := ((r39 - r14)%R).
Notation r84 := ((r85 + r86)%R).
Notation p205 := (BND r84 i101). (* BND(float<53,-1074,ne>(zh * w6) - zh * w6 + (zh * w6 - zh * (c6 + zh * (c7 + zh * (c8 + zh * c9)))), [-2.18549e-19, 2.18549e-19]) *)
Definition f111 := Float2 (-1) (-63).
Definition f112 := Float2 (1) (-63).
Definition i102 := makepairF f111 f112.
Notation p206 := (BND r85 i102). (* BND(float<53,-1074,ne>(zh * w6) - zh * w6, [-1.0842e-19, 1.0842e-19]) *)
Definition f113 := Float2 (1) (-9).
Definition i103 := makepairF f12 f113.
Notation p207 := (ABS r39 i103). (* ABS(zh * w6, [6.77626e-21, 0.00195312]) *)
Definition f114 := Float2 (5) (-9).
Definition i104 := makepairF f1 f114.
Notation p208 := (ABS _zh i104). (* ABS(zh, [5.42101e-20, 0.00976562]) *)
Lemma t143 : p208 -> p82 -> p207.
Proof.
 intros h0 h1.
 refine (mul_aa _zh _w6 i104 i40 i103 h0 h1 _) ; finalize.
Qed.
Lemma l164 : s1 -> p207 (* ABS(zh * w6, [6.77626e-21, 0.00195312]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 assert (h2 := l67 h0).
 apply t143. refine (abs_subset _zh i5 i104 h1 _) ; finalize. exact h2.
Qed.
Lemma t144 : p207 -> p206.
Proof.
 intros h0.
 refine (float_absolute_wide_ne _ _ r39 i103 i102 h0 _) ; finalize.
Qed.
Lemma l163 : s1 -> p206 (* BND(float<53,-1074,ne>(zh * w6) - zh * w6, [-1.0842e-19, 1.0842e-19]) *).
Proof.
 intros h0.
 assert (h1 := l164 h0).
 apply t144. exact h1.
Qed.
Definition f115 := Float2 (-80046064554921627558346814529146264739656850261866227602016080515806521135014260189915146702291374922793009746019497) (-448).
Definition f116 := Float2 (80046064554921627558346814529146264739656850261866227602016080515806521135014260189915146702291374922793009746019497) (-448).
Definition i105 := makepairF f115 f116.
Notation p209 := (BND r86 i105). (* BND(zh * w6 - zh * (c6 + zh * (c7 + zh * (c8 + zh * c9))), [-1.10129e-19, 1.10129e-19]) *)
Notation r88 := ((_w6 - r15)%R).
Notation r87 := ((_zh * r88)%R).
Notation p210 := (BND r87 i105). (* BND(zh * (w6 - (c6 + zh * (c7 + zh * (c8 + zh * c9)))), [-1.10129e-19, 1.10129e-19]) *)
Definition f117 := Float2 (-10005629997301237988947093293349128223615843999930079345236391038670520159218744523809488576332644807495590274696921) (-438).
Definition f118 := Float2 (10005629997301237988947093293349128223615843999930079345236391038670520159218744523809488576332644807495590274696921) (-438).
Definition i106 := makepairF f117 f118.
Notation p211 := (BND r88 i106). (* BND(w6 - (c6 + zh * (c7 + zh * (c8 + zh * c9))), [-1.40963e-17, 1.40963e-17]) *)
Notation r90 := ((_w6 - r41)%R).
Notation r91 := ((r41 - r15)%R).
Notation r89 := ((r90 + r91)%R).
Notation p212 := (BND r89 i106). (* BND(w6 - (c6 + float<53,-1074,ne>(zh * w7)) + (c6 + float<53,-1074,ne>(zh * w7) - (c6 + zh * (c7 + zh * (c8 + zh * c9)))), [-1.40963e-17, 1.40963e-17]) *)
Notation p213 := (BND r90 i98). (* BND(w6 - (c6 + float<53,-1074,ne>(zh * w7)), [-1.38778e-17, 1.38778e-17]) *)
Notation p214 := (ABS r41 i94). (* ABS(c6 + float<53,-1074,ne>(zh * w7), [0.125, 0.25]) *)
Notation p215 := (ABS r42 i95). (* ABS(float<53,-1074,ne>(zh * w7), [0, 0.03125]) *)
Notation p216 := (BND r42 i96). (* BND(float<53,-1074,ne>(zh * w7), [-0.03125, 0.03125]) *)
Lemma t145 : p216 -> p215.
Proof.
 intros h0.
 refine (abs_of_bnd_o r42 i96 i95 h0 _) ; finalize.
Qed.
Lemma l171 : s1 -> p215 (* ABS(float<53,-1074,ne>(zh * w7), [0, 0.03125]) *).
Proof.
 intros h0.
 assert (h1 := l70 h0).
 apply t145. refine (subset r42 i42 i96 h1 _) ; finalize.
Qed.
Definition i107 := makepairF f33 f22.
Notation p217 := (ABS _c6 i107). (* ABS(c6, [0.15625, 0.1875]) *)
Lemma t146 : p217 -> p215 -> p214.
Proof.
 intros h0 h1.
 refine (add_aa_p _c6 r42 i107 i95 i94 h0 h1 _) ; finalize.
Qed.
Lemma l170 : s1 -> p214 (* ABS(c6 + float<53,-1074,ne>(zh * w7), [0.125, 0.25]) *).
Proof.
 intros h0.
 assert (h1 := l25 h0).
 assert (h2 := l171 h0).
 apply t146. refine (abs_subset _c6 i15 i107 h1 _) ; finalize. exact h2.
Qed.
Lemma t147 : p214 -> p213.
Proof.
 intros h0.
 refine (float_absolute_wide_ne _ _ r41 i94 i98 h0 _) ; finalize.
Qed.
Lemma l169 : s1 -> p213 (* BND(w6 - (c6 + float<53,-1074,ne>(zh * w7)), [-1.38778e-17, 1.38778e-17]) *).
Proof.
 intros h0.
 assert (h1 := l170 h0).
 apply t147. exact h1.
Qed.
Definition f119 := Float2 (-155128448202618185877333268313224772345909182313717678249317687609089716344441870955922012611415897293933277120217) (-438).
Definition f120 := Float2 (155128448202618185877333268313224772345909182313717678249317687609089716344441870955922012611415897293933277120217) (-438).
Definition i108 := makepairF f119 f120.
Notation p218 := (BND r91 i108). (* BND(c6 + float<53,-1074,ne>(zh * w7) - (c6 + zh * (c7 + zh * (c8 + zh * c9))), [-2.18551e-19, 2.18551e-19]) *)
Notation r92 := ((r42 - r17)%R).
Notation p219 := (BND r92 i108). (* BND(float<53,-1074,ne>(zh * w7) - zh * (c7 + zh * (c8 + zh * c9)), [-2.18551e-19, 2.18551e-19]) *)
Notation r94 := ((r42 - r43)%R).
Notation r95 := ((r43 - r17)%R).
Notation r93 := ((r94 + r95)%R).
Notation p220 := (BND r93 i108). (* BND(float<53,-1074,ne>(zh * w7) - zh * w7 + (zh * w7 - zh * (c7 + zh * (c8 + zh * c9))), [-2.18551e-19, 2.18551e-19]) *)
Notation p221 := (BND r94 i102). (* BND(float<53,-1074,ne>(zh * w7) - zh * w7, [-1.0842e-19, 1.0842e-19]) *)
Notation p222 := (ABS r43 i103). (* ABS(zh * w7, [6.77626e-21, 0.00195312]) *)
Lemma t148 : p208 -> p176 -> p222.
Proof.
 intros h0 h1.
 refine (mul_aa _zh _w7 i104 i40 i103 h0 h1 _) ; finalize.
Qed.
Lemma l176 : s1 -> p222 (* ABS(zh * w7, [6.77626e-21, 0.00195312]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 assert (h2 := l139 h0).
 apply t148. refine (abs_subset _zh i5 i104 h1 _) ; finalize. exact h2.
Qed.
Lemma t149 : p222 -> p221.
Proof.
 intros h0.
 refine (float_absolute_wide_ne _ _ r43 i103 i102 h0 _) ; finalize.
Qed.
Lemma l175 : s1 -> p221 (* BND(float<53,-1074,ne>(zh * w7) - zh * w7, [-1.0842e-19, 1.0842e-19]) *).
Proof.
 intros h0.
 assert (h1 := l176 h0).
 apply t149. exact h1.
Qed.
Definition f121 := Float2 (-78171404850285218665850768117631776632862816551089852725981177053922291009486381480503523832343796432982831826649) (-438).
Definition f122 := Float2 (78171404850285218665850768117631776632862816551089852725981177053922291009486381480503523832343796432982831826649) (-438).
Definition i109 := makepairF f121 f122.
Notation p223 := (BND r95 i109). (* BND(zh * w7 - zh * (c7 + zh * (c8 + zh * c9)), [-1.10131e-19, 1.10131e-19]) *)
Notation r97 := ((_w7 - r18)%R).
Notation r96 := ((_zh * r97)%R).
Notation p224 := (BND r96 i109). (* BND(zh * (w7 - (c7 + zh * (c8 + zh * c9))), [-1.10131e-19, 1.10131e-19]) *)
Definition f123 := Float2 (-20011623492892306956928747950139973026358143652840245942703114725935614522562624857410727243771291614310941767567517) (-439).
Definition f124 := Float2 (20011623492892306956928747950139973026358143652840245942703114725935614522562624857410727243771291614310941767567517) (-439).
Definition i110 := makepairF f123 f124.
Notation p225 := (BND r97 i110). (* BND(w7 - (c7 + zh * (c8 + zh * c9)), [-1.40966e-17, 1.40966e-17]) *)
Notation r99 := ((_w7 - r45)%R).
Notation r100 := ((r45 - r18)%R).
Notation r98 := ((r99 + r100)%R).
Notation p226 := (BND r98 i110). (* BND(w7 - (c7 + float<53,-1074,ne>(zh * w8)) + (c7 + float<53,-1074,ne>(zh * w8) - (c7 + zh * (c8 + zh * c9))), [-1.40966e-17, 1.40966e-17]) *)
Notation p227 := (BND r99 i98). (* BND(w7 - (c7 + float<53,-1074,ne>(zh * w8)), [-1.38778e-17, 1.38778e-17]) *)
Notation p228 := (ABS r45 i94). (* ABS(c7 + float<53,-1074,ne>(zh * w8), [0.125, 0.25]) *)
Definition i111 := makepairF f66 f25.
Notation p229 := (ABS r46 i111). (* ABS(float<53,-1074,ne>(zh * w8), [0, 0.015625]) *)
Definition i112 := makepairF f42 f25.
Notation p230 := (BND r46 i112). (* BND(float<53,-1074,ne>(zh * w8), [-0.015625, 0.015625]) *)
Lemma t150 : p230 -> p229.
Proof.
 intros h0.
 refine (abs_of_bnd_o r46 i112 i111 h0 _) ; finalize.
Qed.
Lemma l183 : s1 -> p229 (* ABS(float<53,-1074,ne>(zh * w8), [0, 0.015625]) *).
Proof.
 intros h0.
 assert (h1 := l75 h0).
 apply t150. refine (subset r46 i45 i112 h1 _) ; finalize.
Qed.
Lemma t151 : p30 -> p229 -> p228.
Proof.
 intros h0 h1.
 refine (add_aa_p _c7 r46 i18 i111 i94 h0 h1 _) ; finalize.
Qed.
Lemma l182 : s1 -> p228 (* ABS(c7 + float<53,-1074,ne>(zh * w8), [0.125, 0.25]) *).
Proof.
 intros h0.
 assert (h1 := l29 h0).
 assert (h2 := l183 h0).
 apply t151. exact h1. exact h2.
Qed.
Lemma t152 : p228 -> p227.
Proof.
 intros h0.
 refine (float_absolute_wide_ne _ _ r45 i94 i98 h0 _) ; finalize.
Qed.
Lemma l181 : s1 -> p227 (* BND(w7 - (c7 + float<53,-1074,ne>(zh * w8)), [-1.38778e-17, 1.38778e-17]) *).
Proof.
 intros h0.
 assert (h1 := l182 h0).
 apply t152. exact h1.
Qed.
Definition f125 := Float2 (-310620394695067350789227900068166123818274017607522608728968023812753636814019551703594116328833793907627772414109) (-439).
Definition f126 := Float2 (310620394695067350789227900068166123818274017607522608728968023812753636814019551703594116328833793907627772414109) (-439).
Definition i113 := makepairF f125 f126.
Notation p231 := (BND r100 i113). (* BND(c7 + float<53,-1074,ne>(zh * w8) - (c7 + zh * (c8 + zh * c9)), [-2.18807e-19, 2.18807e-19]) *)
Notation r101 := ((r46 - r20)%R).
Notation p232 := (BND r101 i113). (* BND(float<53,-1074,ne>(zh * w8) - zh * (c8 + zh * c9), [-2.18807e-19, 2.18807e-19]) *)
Definition f127 := Float2 (-9024913780010195) (-105).
Definition f128 := Float2 (616867162700984129571053607381245809701986834692794765259769226965873889528611217932951142871118159684498508671921) (-430).
Definition i114 := makepairF f127 f128.
Notation p233 := (REL r46 r20 i114). (* REL(float<53,-1074,ne>(zh * w8), zh * (c8 + zh * c9), [-2.22481e-16, 2.22481e-16]) *)
Notation p234 := (REL r46 r47 i39). (* REL(float<53,-1074,ne>(zh * w8), zh * w8, [-1.11022e-16, 1.11022e-16]) *)
Notation p235 := (FIX r47 (-288)). (* FIX(zh * w8, -288) *)
Notation p236 := (FIX _w8 (-172)). (* FIX(w8, -172) *)
Notation p237 := (FIX r49 (-172)). (* FIX(c8 + float<53,-1074,ne>(zh * c9), -172) *)
Notation p238 := (FIX _c8 (-55)). (* FIX(c8, -55) *)
Lemma t153 : p35 -> p238.
Proof.
 intros h0.
 refine (fix_of_singleton_bnd _c8 i22 (-55) h0 _) ; finalize.
Qed.
Lemma l191 : s1 -> p238 (* FIX(c8, -55) *).
Proof.
 intros h0.
 assert (h1 := l33 h0).
 apply t153. exact h1.
Qed.
Notation p239 := (FIX r50 (-172)). (* FIX(float<53,-1074,ne>(zh * c9), -172) *)
Notation p240 := (FIX r23 (-172)). (* FIX(zh * c9, -172) *)
Notation p241 := (FIX _c9 (-56)). (* FIX(c9, -56) *)
Lemma t154 : p38 -> p241.
Proof.
 intros h0.
 refine (fix_of_singleton_bnd _c9 i25 (-56) h0 _) ; finalize.
Qed.
Lemma l194 : s1 -> p241 (* FIX(c9, -56) *).
Proof.
 intros h0.
 assert (h1 := l36 h0).
 apply t154. exact h1.
Qed.
Lemma t155 : p58 -> p241 -> p240.
Proof.
 intros h0 h1.
 refine (mul_fix _zh _c9 (-116) (-56) (-172) h0 h1 _) ; finalize.
Qed.
Lemma l193 : s1 -> p240 (* FIX(zh * c9, -172) *).
Proof.
 intros h0.
 assert (h1 := l43 h0).
 assert (h2 := l194 h0).
 apply t155. exact h1. exact h2.
Qed.
Lemma t156 : p240 -> p239.
Proof.
 intros h0.
 refine (fix_float_of_fix _ _ _ (-172) (-172) r23 h0 _) ; finalize.
Qed.
Lemma l192 : s1 -> p239 (* FIX(float<53,-1074,ne>(zh * c9), -172) *).
Proof.
 intros h0.
 assert (h1 := l193 h0).
 apply t156. exact h1.
Qed.
Lemma t157 : p238 -> p239 -> p237.
Proof.
 intros h0 h1.
 refine (add_fix _c8 r50 (-55) (-172) (-172) h0 h1 _) ; finalize.
Qed.
Lemma l190 : s1 -> p237 (* FIX(c8 + float<53,-1074,ne>(zh * c9), -172) *).
Proof.
 intros h0.
 assert (h1 := l191 h0).
 assert (h2 := l192 h0).
 apply t157. exact h1. exact h2.
Qed.
Lemma t158 : p237 -> p236.
Proof.
 intros h0.
 refine (fix_float_of_fix _ _ _ (-172) (-172) r49 h0 _) ; finalize.
Qed.
Lemma l189 : s1 -> p236 (* FIX(w8, -172) *).
Proof.
 intros h0.
 assert (h1 := l190 h0).
 apply t158. exact h1.
Qed.
Lemma t159 : p58 -> p236 -> p235.
Proof.
 intros h0 h1.
 refine (mul_fix _zh _w8 (-116) (-172) (-288) h0 h1 _) ; finalize.
Qed.
Lemma l188 : s1 -> p235 (* FIX(zh * w8, -288) *).
Proof.
 intros h0.
 assert (h1 := l43 h0).
 assert (h2 := l189 h0).
 apply t159. exact h1. exact h2.
Qed.
Lemma t160 : p235 -> p234.
Proof.
 intros h0.
 refine (rel_of_fix_float_ne _ _ (-288) r47 i39 h0 _) ; finalize.
Qed.
Lemma l187 : s1 -> p234 (* REL(float<53,-1074,ne>(zh * w8), zh * w8, [-1.11022e-16, 1.11022e-16]) *).
Proof.
 intros h0.
 assert (h1 := l188 h0).
 apply t160. exact h1.
Qed.
Definition f129 := Float2 (-9042628305279399) (-106).
Definition f130 := Float2 (618077978583304452829806929501848020045230225002626047647866734749055377064827876721604549540884554573673670108367) (-431).
Definition i115 := makepairF f129 f130.
Notation p242 := (REL r47 r20 i115). (* REL(zh * w8, zh * (c8 + zh * c9), [-1.11459e-16, 1.11459e-16]) *)
Notation p243 := (REL _w8 r21 i115). (* REL(w8, c8 + zh * c9, [-1.11459e-16, 1.11459e-16]) *)
Notation p244 := (REL _w8 r49 i39). (* REL(w8, c8 + float<53,-1074,ne>(zh * c9), [-1.11022e-16, 1.11022e-16]) *)
Notation p245 := (FIX r49 (-1074)). (* FIX(c8 + float<53,-1074,ne>(zh * c9), -1074) *)
Notation p246 := (FIX r50 (-1074)). (* FIX(float<53,-1074,ne>(zh * c9), -1074) *)
Lemma t161 : p246.
Proof.
 refine (fix_of_float _ _ _ _ (-1074) _) ; finalize.
Qed.
Lemma l199 : s1 -> p246 (* FIX(float<53,-1074,ne>(zh * c9), -1074) *).
Proof.
 intros h0.
 apply t161.
Qed.
Lemma t162 : p238 -> p246 -> p245.
Proof.
 intros h0 h1.
 refine (add_fix _c8 r50 (-55) (-1074) (-1074) h0 h1 _) ; finalize.
Qed.
Lemma l198 : s1 -> p245 (* FIX(c8 + float<53,-1074,ne>(zh * c9), -1074) *).
Proof.
 intros h0.
 assert (h1 := l191 h0).
 assert (h2 := l199 h0).
 apply t162. exact h1. exact h2.
Qed.
Lemma t163 : p245 -> p244.
Proof.
 intros h0.
 refine (rel_of_fix_float_ne _ _ (-1074) r49 i39 h0 _) ; finalize.
Qed.
Lemma l197 : s1 -> p244 (* REL(w8, c8 + float<53,-1074,ne>(zh * c9), [-1.11022e-16, 1.11022e-16]) *).
Proof.
 intros h0.
 assert (h1 := l198 h0).
 apply t163. exact h1.
Qed.
Definition f131 := Float2 (-35429050538407) (-106).
Definition f132 := Float2 (9686527058562859476367174841308348704389635083229667272424936979085476141146010300861293114393854883652144840815) (-433).
Definition i116 := makepairF f131 f132.
Notation p247 := (REL r49 r21 i116). (* REL(c8 + float<53,-1074,ne>(zh * c9), c8 + zh * c9, [-4.36697e-19, 4.36697e-19]) *)
Notation p248 := (NZR r21). (* NZR(c8 + zh * c9) *)
Lemma t164 : p34 -> p248.
Proof.
 intros h0.
 refine (nzr_of_abs r21 i21 h0 _) ; finalize.
Qed.
Lemma l201 : s1 -> p248 (* NZR(c8 + zh * c9) *).
Proof.
 intros h0.
 assert (h1 := l32 h0).
 apply t164. exact h1.
Qed.
Notation r103 := ((r49 - r21)%R).
Notation r102 := ((r103 / r21)%R).
Notation p249 := (BND r102 i116). (* BND((c8 + float<53,-1074,ne>(zh * c9) - (c8 + zh * c9)) / (c8 + zh * c9), [-4.36697e-19, 4.36697e-19]) *)
Definition f133 := Float2 (-1) (-64).
Definition i117 := makepairF f133 f1.
Notation p250 := (BND r103 i117). (* BND(c8 + float<53,-1074,ne>(zh * c9) - (c8 + zh * c9), [-5.42101e-20, 5.42101e-20]) *)
Notation r104 := ((r50 - r23)%R).
Notation p251 := (BND r104 i117). (* BND(float<53,-1074,ne>(zh * c9) - zh * c9, [-5.42101e-20, 5.42101e-20]) *)
Lemma t165 : p37 -> p251.
Proof.
 intros h0.
 refine (float_absolute_wide_ne _ _ r23 i24 i117 h0 _) ; finalize.
Qed.
Lemma l204 : s1 -> p251 (* BND(float<53,-1074,ne>(zh * c9) - zh * c9, [-5.42101e-20, 5.42101e-20]) *).
Proof.
 intros h0.
 assert (h1 := l35 h0).
 apply t165. exact h1.
Qed.
Lemma t166 : p251 -> p250.
Proof.
 intros h0.
 refine (add_fils _ _ _ i117 h0) ; finalize.
Qed.
Lemma l203 : s1 -> p250 (* BND(c8 + float<53,-1074,ne>(zh * c9) - (c8 + zh * c9), [-5.42101e-20, 5.42101e-20]) *).
Proof.
 intros h0.
 assert (h1 := l204 h0).
 apply t166. exact h1.
Qed.
Definition f134 := Float2 (-4960107620603480708239418392319071465053820057805771331460596602909178150094912197552425446293081815381711816002201) (-384).
Definition f135 := Float2 (-4776597888979631659787655036775889987969918554797546596853589609880907027454472200545973393303396818422139667933) (-374).
Definition i118 := makepairF f134 f135.
Notation p252 := (BND r21 i118). (* BND(c8 + zh * c9, [-0.125885, -0.124137]) *)
Lemma t167 : p36 -> p95 -> p252.
Proof.
 intros h0 h1.
 refine (add _c8 r23 i23 i48 i118 h0 h1 _) ; finalize.
Qed.
Lemma l205 : s1 -> p252 (* BND(c8 + zh * c9, [-0.125885, -0.124137]) *).
Proof.
 intros h0.
 assert (h1 := l34 h0).
 assert (h2 := l80 h0).
 apply t167. exact h1. exact h2.
Qed.
Definition f136 := Float2 (-1) (0).
Definition i119 := makepairF f136 f135.
Notation p253 := (BND r21 i119). (* BND(c8 + zh * c9, [-1, -0.124137]) *)
Lemma t168 : p250 -> p253 -> p249.
Proof.
 intros h0 h1.
 refine (div_on r103 r21 i117 i119 i116 h0 h1 _) ; finalize.
Qed.
Lemma l202 : s1 -> p249 (* BND((c8 + float<53,-1074,ne>(zh * c9) - (c8 + zh * c9)) / (c8 + zh * c9), [-4.36697e-19, 4.36697e-19]) *).
Proof.
 intros h0.
 assert (h1 := l203 h0).
 assert (h2 := l205 h0).
 apply t168. exact h1. refine (subset r21 i118 i119 h2 _) ; finalize.
Qed.
Lemma t169 : p248 -> p249 -> p247.
Proof.
 intros h0 h1.
 refine (rel_of_nzr_bnd r49 r21 i116 h0 h1) ; finalize.
Qed.
Lemma l200 : s1 -> p247 (* REL(c8 + float<53,-1074,ne>(zh * c9), c8 + zh * c9, [-4.36697e-19, 4.36697e-19]) *).
Proof.
 intros h0.
 assert (h1 := l201 h0).
 assert (h2 := l202 h0).
 apply t169. exact h1. exact h2.
Qed.
Lemma t170 : p244 -> p247 -> p243.
Proof.
 intros h0 h1.
 refine (compose _w8 r49 r21 i39 i116 i115 h0 h1 _) ; finalize.
Qed.
Lemma l196 : s1 -> p243 (* REL(w8, c8 + zh * c9, [-1.11459e-16, 1.11459e-16]) *).
Proof.
 intros h0.
 assert (h1 := l197 h0).
 assert (h2 := l200 h0).
 apply t170. exact h1. exact h2.
Qed.
Lemma t171 : p243 -> p242.
Proof.
 intros h0.
 refine (mul_filq _ _w8 r21 i115 h0) ; finalize.
Qed.
Lemma l195 : s1 -> p242 (* REL(zh * w8, zh * (c8 + zh * c9), [-1.11459e-16, 1.11459e-16]) *).
Proof.
 intros h0.
 assert (h1 := l196 h0).
 apply t171. exact h1.
Qed.
Lemma t172 : p234 -> p242 -> p233.
Proof.
 intros h0 h1.
 refine (compose r46 r47 r20 i39 i115 i114 h0 h1 _) ; finalize.
Qed.
Lemma l186 : s1 -> p233 (* REL(float<53,-1074,ne>(zh * w8), zh * (c8 + zh * c9), [-2.22481e-16, 2.22481e-16]) *).
Proof.
 intros h0.
 assert (h1 := l187 h0).
 assert (h2 := l195 h0).
 apply t172. exact h1. exact h2.
Qed.
Definition f137 := Float2 (-620021388747628054099060482109311643646071593337813905666704912318211923446904176553569264667349295853618587739181) (-388).
Definition f138 := Float2 (620021388747628054099060482109311643646071593337813905666704912318211923446904176553569264667349295853618587739181) (-388).
Definition i120 := makepairF f137 f138.
Notation p254 := (BND r20 i120). (* BND(zh * (c8 + zh * c9), [-0.000983486, 0.000983486]) *)
Definition f139 := Float2 (-2462656908879612066350809829491055977708527768195506789104102696400081007295992860981880772343311135482926894696569) (-387).
Definition f140 := Float2 (2462656908879612066350809829491055977708527768195506789104102696400081007295992860981880772343311135482926894696569) (-387).
Definition i121 := makepairF f139 f140.
Notation p255 := (BND _zh i121). (* BND(zh, [-0.0078126, 0.0078126]) *)
Definition i122 := makepairF f134 f45.
Notation p256 := (BND r21 i122). (* BND(c8 + zh * c9, [-0.125885, -0.0625]) *)
Lemma t173 : p255 -> p256 -> p254.
Proof.
 intros h0 h1.
 refine (mul_on _zh r21 i121 i122 i120 h0 h1 _) ; finalize.
Qed.
Lemma l206 : s1 -> p254 (* BND(zh * (c8 + zh * c9), [-0.000983486, 0.000983486]) *).
Proof.
 intros h0.
 assert (h1 := l72 h0).
 assert (h2 := l205 h0).
 apply t173. refine (subset _zh i43 i121 h1 _) ; finalize. refine (subset r21 i118 i122 h2 _) ; finalize.
Qed.
Lemma t174 : p233 -> p254 -> p232.
Proof.
 intros h0 h1.
 refine (error_of_rel_oo r46 r20 i114 i120 i113 h0 h1 _) ; finalize.
Qed.
Lemma l185 : s1 -> p232 (* BND(float<53,-1074,ne>(zh * w8) - zh * (c8 + zh * c9), [-2.18807e-19, 2.18807e-19]) *).
Proof.
 intros h0.
 assert (h1 := l186 h0).
 assert (h2 := l206 h0).
 apply t174. exact h1. exact h2.
Qed.
Lemma t175 : p232 -> p231.
Proof.
 intros h0.
 refine (add_fils _ _ _ i113 h0) ; finalize.
Qed.
Lemma l184 : s1 -> p231 (* BND(c7 + float<53,-1074,ne>(zh * w8) - (c7 + zh * (c8 + zh * c9)), [-2.18807e-19, 2.18807e-19]) *).
Proof.
 intros h0.
 assert (h1 := l185 h0).
 apply t175. exact h1.
Qed.
Lemma t176 : p227 -> p231 -> p226.
Proof.
 intros h0 h1.
 refine (add r99 r100 i98 i113 i110 h0 h1 _) ; finalize.
Qed.
Lemma l180 : s1 -> p226 (* BND(w7 - (c7 + float<53,-1074,ne>(zh * w8)) + (c7 + float<53,-1074,ne>(zh * w8) - (c7 + zh * (c8 + zh * c9))), [-1.40966e-17, 1.40966e-17]) *).
Proof.
 intros h0.
 assert (h1 := l181 h0).
 assert (h2 := l184 h0).
 apply t176. exact h1. exact h2.
Qed.
Lemma t177 : p226 -> p225.
Proof.
 intros h0.
 refine (sub_xals _ _ _ i110 h0) ; finalize.
Qed.
Lemma l179 : s1 -> p225 (* BND(w7 - (c7 + zh * (c8 + zh * c9)), [-1.40966e-17, 1.40966e-17]) *).
Proof.
 intros h0.
 assert (h1 := l180 h0).
 apply t177. exact h1.
Qed.
Definition f141 := Float2 (-4925313817759224132701619658982111955417055536391013578208205392800162014591985721963761544686622270965853789393137) (-388).
Definition f142 := Float2 (4925313817759224132701619658982111955417055536391013578208205392800162014591985721963761544686622270965853789393137) (-388).
Definition i123 := makepairF f141 f142.
Notation p257 := (BND _zh i123). (* BND(zh, [-0.0078126, 0.0078126]) *)
Lemma t178 : p257 -> p225 -> p224.
Proof.
 intros h0 h1.
 refine (mul_oo _zh r97 i123 i110 i109 h0 h1 _) ; finalize.
Qed.
Lemma l178 : s1 -> p224 (* BND(zh * (w7 - (c7 + zh * (c8 + zh * c9))), [-1.10131e-19, 1.10131e-19]) *).
Proof.
 intros h0.
 assert (h1 := l72 h0).
 assert (h2 := l179 h0).
 apply t178. refine (subset _zh i43 i123 h1 _) ; finalize. exact h2.
Qed.
Lemma t179 : p224 -> p223.
Proof.
 intros h0.
 refine (mul_fils _ _ _ i109 h0) ; finalize.
Qed.
Lemma l177 : s1 -> p223 (* BND(zh * w7 - zh * (c7 + zh * (c8 + zh * c9)), [-1.10131e-19, 1.10131e-19]) *).
Proof.
 intros h0.
 assert (h1 := l178 h0).
 apply t179. exact h1.
Qed.
Lemma t180 : p221 -> p223 -> p220.
Proof.
 intros h0 h1.
 refine (add r94 r95 i102 i109 i108 h0 h1 _) ; finalize.
Qed.
Lemma l174 : s1 -> p220 (* BND(float<53,-1074,ne>(zh * w7) - zh * w7 + (zh * w7 - zh * (c7 + zh * (c8 + zh * c9))), [-2.18551e-19, 2.18551e-19]) *).
Proof.
 intros h0.
 assert (h1 := l175 h0).
 assert (h2 := l177 h0).
 apply t180. exact h1. exact h2.
Qed.
Lemma t181 : p220 -> p219.
Proof.
 intros h0.
 refine (sub_xals _ _ _ i108 h0) ; finalize.
Qed.
Lemma l173 : s1 -> p219 (* BND(float<53,-1074,ne>(zh * w7) - zh * (c7 + zh * (c8 + zh * c9)), [-2.18551e-19, 2.18551e-19]) *).
Proof.
 intros h0.
 assert (h1 := l174 h0).
 apply t181. exact h1.
Qed.
Lemma t182 : p219 -> p218.
Proof.
 intros h0.
 refine (add_fils _ _ _ i108 h0) ; finalize.
Qed.
Lemma l172 : s1 -> p218 (* BND(c6 + float<53,-1074,ne>(zh * w7) - (c6 + zh * (c7 + zh * (c8 + zh * c9))), [-2.18551e-19, 2.18551e-19]) *).
Proof.
 intros h0.
 assert (h1 := l173 h0).
 apply t182. exact h1.
Qed.
Lemma t183 : p213 -> p218 -> p212.
Proof.
 intros h0 h1.
 refine (add r90 r91 i98 i108 i106 h0 h1 _) ; finalize.
Qed.
Lemma l168 : s1 -> p212 (* BND(w6 - (c6 + float<53,-1074,ne>(zh * w7)) + (c6 + float<53,-1074,ne>(zh * w7) - (c6 + zh * (c7 + zh * (c8 + zh * c9)))), [-1.40963e-17, 1.40963e-17]) *).
Proof.
 intros h0.
 assert (h1 := l169 h0).
 assert (h2 := l172 h0).
 apply t183. exact h1. exact h2.
Qed.
Lemma t184 : p212 -> p211.
Proof.
 intros h0.
 refine (sub_xals _ _ _ i106 h0) ; finalize.
Qed.
Lemma l167 : s1 -> p211 (* BND(w6 - (c6 + zh * (c7 + zh * (c8 + zh * c9))), [-1.40963e-17, 1.40963e-17]) *).
Proof.
 intros h0.
 assert (h1 := l168 h0).
 apply t184. exact h1.
Qed.
Definition f143 := Float2 (-630440168673180688985807316349710330293383108658049738010650290278420737867774172411361477719887650683629285042321471) (-395).
Definition f144 := Float2 (630440168673180688985807316349710330293383108658049738010650290278420737867774172411361477719887650683629285042321471) (-395).
Definition i124 := makepairF f143 f144.
Notation p258 := (BND _zh i124). (* BND(zh, [-0.0078126, 0.0078126]) *)
Lemma t185 : p258 -> p211 -> p210.
Proof.
 intros h0 h1.
 refine (mul_oo _zh r88 i124 i106 i105 h0 h1 _) ; finalize.
Qed.
Lemma l166 : s1 -> p210 (* BND(zh * (w6 - (c6 + zh * (c7 + zh * (c8 + zh * c9)))), [-1.10129e-19, 1.10129e-19]) *).
Proof.
 intros h0.
 assert (h1 := l72 h0).
 assert (h2 := l167 h0).
 apply t185. refine (subset _zh i43 i124 h1 _) ; finalize. exact h2.
Qed.
Lemma t186 : p210 -> p209.
Proof.
 intros h0.
 refine (mul_fils _ _ _ i105 h0) ; finalize.
Qed.
Lemma l165 : s1 -> p209 (* BND(zh * w6 - zh * (c6 + zh * (c7 + zh * (c8 + zh * c9))), [-1.10129e-19, 1.10129e-19]) *).
Proof.
 intros h0.
 assert (h1 := l166 h0).
 apply t186. exact h1.
Qed.
Lemma t187 : p206 -> p209 -> p205.
Proof.
 intros h0 h1.
 refine (add r85 r86 i102 i105 i101 h0 h1 _) ; finalize.
Qed.
Lemma l162 : s1 -> p205 (* BND(float<53,-1074,ne>(zh * w6) - zh * w6 + (zh * w6 - zh * (c6 + zh * (c7 + zh * (c8 + zh * c9)))), [-2.18549e-19, 2.18549e-19]) *).
Proof.
 intros h0.
 assert (h1 := l163 h0).
 assert (h2 := l165 h0).
 apply t187. exact h1. exact h2.
Qed.
Lemma t188 : p205 -> p204.
Proof.
 intros h0.
 refine (sub_xals _ _ _ i101 h0) ; finalize.
Qed.
Lemma l161 : s1 -> p204 (* BND(float<53,-1074,ne>(zh * w6) - zh * (c6 + zh * (c7 + zh * (c8 + zh * c9))), [-2.18549e-19, 2.18549e-19]) *).
Proof.
 intros h0.
 assert (h1 := l162 h0).
 apply t188. exact h1.
Qed.
Lemma t189 : p204 -> p203.
Proof.
 intros h0.
 refine (add_fils _ _ _ i101 h0) ; finalize.
Qed.
Lemma l160 : s1 -> p203 (* BND(c5 + float<53,-1074,ne>(zh * w6) - (c5 + zh * (c6 + zh * (c7 + zh * (c8 + zh * c9)))), [-2.18549e-19, 2.18549e-19]) *).
Proof.
 intros h0.
 assert (h1 := l161 h0).
 apply t189. exact h1.
Qed.
Definition f145 := Float2 (31314999820479328024710771190855842372035097439644791354684928897627394404361071636150210085535169609513997487760629) (-386).
Definition f146 := Float2 (129958748547142507467390252182803014375087944990490420588704999206541353226014031836484636925297611564459235819215957387) (-398).
Definition i125 := makepairF f145 f146.
Notation p259 := (BND r12 i125). (* BND(c5 + zh * (c6 + zh * (c7 + zh * (c8 + zh * c9))), [0.198689, 0.201311]) *)
Definition f147 := Float2 (-206605137018942856222526047980649904691428940149579492177188774641057830291880177589523488152533794420154066082571) (-386).
Definition f148 := Float2 (846254641229589939087466692528742009616092938852677599957765220929772872875541207406688207472778421944951054674210187) (-398).
Definition i126 := makepairF f147 f148.
Notation p260 := (BND r14 i126). (* BND(zh * (c6 + zh * (c7 + zh * (c8 + zh * c9))), [-0.00131088, 0.00131088]) *)
Definition f149 := Float2 (-6769950474470646288427241671536540409211505603549695363561468180645470720979101126759083143517990345283188812576880511) (-394).
Definition i127 := makepairF f149 f38.
Notation p261 := (BND r15 i127). (* BND(c6 + zh * (c7 + zh * (c8 + zh * c9)), [-0.16779, -0.125]) *)
Definition f150 := Float2 (-45341430128873403900006447978653458218323675224387392131983024779052353920545328490109783315546343779656700772382591) (-394).
Definition i128 := makepairF f150 f20.
Notation p262 := (BND r17 i128). (* BND(zh * (c7 + zh * (c8 + zh * c9)), [-0.00112377, 0.03125]) *)
Definition f151 := Float2 (45340849765996399146097377932215925854472737973341333362915979454515336124242938180501072901813200570689395948114455) (-387).
Definition i129 := makepairF f14 f151.
Notation p263 := (BND r18 i129). (* BND(c7 + zh * (c8 + zh * c9), [0.125, 0.143841]) *)
Definition f152 := Float2 (310010694373814027049530241054655821823035796668906952833352456159105961723452088276784632333674647926809293869591) (-387).
Definition i130 := makepairF f42 f152.
Notation p264 := (BND r20 i130). (* BND(zh * (c8 + zh * c9), [-0.015625, 0.000983486]) *)
Lemma t190 : p31 -> p264 -> p263.
Proof.
 intros h0 h1.
 refine (add _c7 r20 i19 i130 i129 h0 h1 _) ; finalize.
Qed.
Lemma l211 : s1 -> p263 (* BND(c7 + zh * (c8 + zh * c9), [0.125, 0.143841]) *).
Proof.
 intros h0.
 assert (h1 := l30 h0).
 assert (h2 := l206 h0).
 apply t190. exact h1. refine (subset r20 i120 i130 h2 _) ; finalize.
Qed.
Definition f153 := Float2 (-9850627635518448265403239317964223910834111072782027156416410785600324029183971443927523089373244541931707578786273) (-389).
Definition i131 := makepairF f153 f14.
Notation p265 := (BND _zh i131). (* BND(zh, [-0.0078126, 0.125]) *)
Lemma t191 : p265 -> p263 -> p262.
Proof.
 intros h0 h1.
 refine (mul_op _zh r18 i131 i129 i128 h0 h1 _) ; finalize.
Qed.
Lemma l210 : s1 -> p262 (* BND(zh * (c7 + zh * (c8 + zh * c9)), [-0.00112377, 0.03125]) *).
Proof.
 intros h0.
 assert (h1 := l72 h0).
 assert (h2 := l211 h0).
 apply t191. refine (subset _zh i43 i131 h1 _) ; finalize. exact h2.
Qed.
Lemma t192 : p103 -> p262 -> p261.
Proof.
 intros h0 h1.
 refine (add _c6 r17 i55 i128 i127 h0 h1 _) ; finalize.
Qed.
Lemma l209 : s1 -> p261 (* BND(c6 + zh * (c7 + zh * (c8 + zh * c9)), [-0.16779, -0.125]) *).
Proof.
 intros h0.
 assert (h1 := l26 h0).
 assert (h2 := l210 h0).
 apply t192. refine (subset _c6 i16 i55 h1 _) ; finalize. exact h2.
Qed.
Definition f154 := Float2 (1231328454439806033175404914745527988854263884097753394552051348200040503647996430490940386171655567741463447348285) (-386).
Definition i132 := makepairF f40 f154.
Notation p266 := (BND _zh i132). (* BND(zh, [-0.0078126, 0.0078126]) *)
Lemma t193 : p266 -> p261 -> p260.
Proof.
 intros h0 h1.
 refine (mul_on _zh r15 i132 i127 i126 h0 h1 _) ; finalize.
Qed.
Lemma l208 : s1 -> p260 (* BND(zh * (c6 + zh * (c7 + zh * (c8 + zh * c9))), [-0.00131088, 0.00131088]) *).
Proof.
 intros h0.
 assert (h1 := l72 h0).
 assert (h2 := l209 h0).
 apply t193. refine (subset _zh i43 i132 h1 _) ; finalize. exact h2.
Qed.
Lemma t194 : p23 -> p260 -> p259.
Proof.
 intros h0 h1.
 refine (add _c5 r14 i14 i126 i125 h0 h1 _) ; finalize.
Qed.
Lemma l207 : s1 -> p259 (* BND(c5 + zh * (c6 + zh * (c7 + zh * (c8 + zh * c9))), [0.198689, 0.201311]) *).
Proof.
 intros h0.
 assert (h1 := l22 h0).
 assert (h2 := l208 h0).
 apply t194. exact h1. exact h2.
Qed.
Definition i133 := makepairF f145 f8.
Notation p267 := (BND r12 i133). (* BND(c5 + zh * (c6 + zh * (c7 + zh * (c8 + zh * c9))), [0.198689, 1]) *)
Lemma t195 : p203 -> p267 -> p202.
Proof.
 intros h0 h1.
 refine (div_op r82 r12 i101 i133 i100 h0 h1 _) ; finalize.
Qed.
Lemma l159 : s1 -> p202 (* BND((c5 + float<53,-1074,ne>(zh * w6) - (c5 + zh * (c6 + zh * (c7 + zh * (c8 + zh * c9))))) / (c5 + zh * (c6 + zh * (c7 + zh * (c8 + zh * c9)))), [-1.09996e-18, 1.09996e-18]) *).
Proof.
 intros h0.
 assert (h1 := l160 h0).
 assert (h2 := l207 h0).
 apply t195. exact h1. refine (subset r12 i125 i133 h2 _) ; finalize.
Qed.
Lemma t196 : p201 -> p202 -> p200.
Proof.
 intros h0 h1.
 refine (rel_of_nzr_bnd r37 r12 i100 h0 h1) ; finalize.
Qed.
Lemma l157 : s1 -> p200 (* REL(c5 + float<53,-1074,ne>(zh * w6), c5 + zh * (c6 + zh * (c7 + zh * (c8 + zh * c9))), [-1.09996e-18, 1.09996e-18]) *).
Proof.
 intros h0.
 assert (h1 := l158 h0).
 assert (h2 := l159 h0).
 apply t196. exact h1. exact h2.
Qed.
Lemma t197 : p190 -> p200 -> p189.
Proof.
 intros h0 h1.
 refine (compose _w5 r37 r12 i93 i100 i92 h0 h1 _) ; finalize.
Qed.
Lemma l150 : s1 -> p189 (* REL(w5, c5 + zh * (c6 + zh * (c7 + zh * (c8 + zh * c9))), [-7.09467e-17, 7.09467e-17]) *).
Proof.
 intros h0.
 assert (h1 := l151 h0).
 assert (h2 := l157 h0).
 apply t197. exact h1. exact h2.
Qed.
Lemma t198 : p189 -> p188.
Proof.
 intros h0.
 refine (mul_filq _ _w5 r12 i92 h0) ; finalize.
Qed.
Lemma l149 : s1 -> p188 (* REL(zh * w5, zh * (c5 + zh * (c6 + zh * (c7 + zh * (c8 + zh * c9)))), [-7.09467e-17, 7.09467e-17]) *).
Proof.
 intros h0.
 assert (h1 := l150 h0).
 apply t198. exact h1.
Qed.
Lemma t199 : p187 -> p188 -> p186.
Proof.
 intros h0 h1.
 refine (compose r34 r35 r11 i39 i92 i91 h0 h1 _) ; finalize.
Qed.
Lemma l147 : s1 -> p186 (* REL(float<53,-1074,ne>(zh * w5), zh * (c5 + zh * (c6 + zh * (c7 + zh * (c8 + zh * c9)))), [-1.81969e-16, 1.81969e-16]) *).
Proof.
 intros h0.
 assert (h1 := l148 h0).
 assert (h2 := l149 h0).
 apply t199. exact h1. exact h2.
Qed.
Notation r105 := ((_c4 / r9)%R).
Definition f155 := Float2 (16281) (-14).
Definition f156 := Float2 (81206180467265009931066189162947316903042592523600354043034130649875476680897634340550887140049590458074188818954491003) (-395).
Definition i134 := makepairF f155 f156.
Notation p268 := (BND r105 i134). (* BND(c4 / (c4 + zh * (c5 + zh * (c6 + zh * (c7 + zh * (c8 + zh * c9))))), [0.993713, 1.00633]) *)
Definition f157 := Float2 (-2537592704677075078492953896147237661471178647042803478071336490754009833506544153431653190161435450260118719237207557) (-392).
Definition f158 := Float2 (-641501206646135975663478332740065906695767237010696046707131608218618317567966845477497457685786834305722438318635481869) (-400).
Definition i135 := makepairF f157 f158.
Notation p269 := (BND r9 i135). (* BND(c4 + zh * (c5 + zh * (c6 + zh * (c7 + zh * (c8 + zh * c9)))), [-0.251573, -0.248427]) *)
Definition f159 := Float2 (-15864308107803211778745829440677606720418938734886022810801823075016015253336831642589373038165314376695222277518853) (-392).
Definition f160 := Float2 (4061262875597622215358932336813467320427248316130821839565266707204099904854228900502879497770320480433976903044826355) (-400).
Definition i136 := makepairF f159 f160.
Notation p270 := (BND r11 i136). (* BND(zh * (c5 + zh * (c6 + zh * (c7 + zh * (c8 + zh * c9)))), [-0.00157276, 0.00157276]) *)
Definition i137 := makepairF f153 f9.
Notation p271 := (BND _zh i137). (* BND(zh, [-0.0078126, 0.0078126]) *)
Definition i138 := makepairF f14 f146.
Notation p272 := (BND r12 i138). (* BND(c5 + zh * (c6 + zh * (c7 + zh * (c8 + zh * c9))), [0.125, 0.201311]) *)
Lemma t200 : p271 -> p272 -> p270.
Proof.
 intros h0 h1.
 refine (mul_op _zh r12 i137 i138 i136 h0 h1 _) ; finalize.
Qed.
Lemma l214 : s1 -> p270 (* BND(zh * (c5 + zh * (c6 + zh * (c7 + zh * (c8 + zh * c9)))), [-0.00157276, 0.00157276]) *).
Proof.
 intros h0.
 assert (h1 := l72 h0).
 assert (h2 := l207 h0).
 apply t200. refine (subset _zh i43 i137 h1 _) ; finalize. refine (subset r12 i125 i138 h2 _) ; finalize.
Qed.
Lemma t201 : p19 -> p270 -> p269.
Proof.
 intros h0 h1.
 refine (add _c4 r11 i12 i136 i135 h0 h1 _) ; finalize.
Qed.
Lemma l213 : s1 -> p269 (* BND(c4 + zh * (c5 + zh * (c6 + zh * (c7 + zh * (c8 + zh * c9)))), [-0.251573, -0.248427]) *).
Proof.
 intros h0.
 assert (h1 := l18 h0).
 assert (h2 := l214 h0).
 apply t201. exact h1. exact h2.
Qed.
Definition f161 := Float2 (-32975) (-17).
Definition i139 := makepairF f161 f158.
Notation p273 := (BND r9 i139). (* BND(c4 + zh * (c5 + zh * (c6 + zh * (c7 + zh * (c8 + zh * c9)))), [-0.251579, -0.248427]) *)
Lemma t202 : p146 -> p273 -> p268.
Proof.
 intros h0 h1.
 refine (div_nn _c4 r9 i79 i139 i134 h0 h1 _) ; finalize.
Qed.
Lemma l212 : s1 -> p268 (* BND(c4 / (c4 + zh * (c5 + zh * (c6 + zh * (c7 + zh * (c8 + zh * c9))))), [0.993713, 1.00633]) *).
Proof.
 intros h0.
 assert (h1 := l18 h0).
 assert (h2 := l213 h0).
 apply t202. refine (subset _c4 i12 i79 h1 _) ; finalize. refine (subset r9 i135 i139 h2 _) ; finalize.
Qed.
Notation p274 := (NZR r9). (* NZR(c4 + zh * (c5 + zh * (c6 + zh * (c7 + zh * (c8 + zh * c9))))) *)
Lemma t203 : p17 -> p274.
Proof.
 intros h0.
 refine (nzr_of_abs r9 i10 h0 _) ; finalize.
Qed.
Lemma l215 : s1 -> p274 (* NZR(c4 + zh * (c5 + zh * (c6 + zh * (c7 + zh * (c8 + zh * c9))))) *).
Proof.
 intros h0.
 assert (h1 := l16 h0).
 apply t203. exact h1.
Qed.
Lemma t204 : p185 -> p186 -> p268 -> p274 -> p184.
Proof.
 intros h0 h1 h2 h3.
 refine (add_rr _c4 _c4 r34 r11 i63 i91 i134 i90 h0 h1 h2 h3 _) ; finalize.
Qed.
Lemma l145 : s1 -> p184 (* REL(c4 + float<53,-1074,ne>(zh * w5), c4 + zh * (c5 + zh * (c6 + zh * (c7 + zh * (c8 + zh * c9)))), [-1.15202e-18, 1.15202e-18]) *).
Proof.
 intros h0.
 assert (h1 := l146 h0).
 assert (h2 := l147 h0).
 assert (h3 := l212 h0).
 assert (h4 := l215 h0).
 apply t204. exact h1. exact h2. exact h3. exact h4.
Qed.
Lemma t205 : p181 -> p184 -> p180.
Proof.
 intros h0 h1.
 refine (compose _w4 r33 r9 i39 i90 i89 h0 h1 _) ; finalize.
Qed.
Lemma l141 : s1 -> p180 (* REL(w4, c4 + zh * (c5 + zh * (c6 + zh * (c7 + zh * (c8 + zh * c9)))), [-1.12174e-16, 1.12174e-16]) *).
Proof.
 intros h0.
 assert (h1 := l142 h0).
 assert (h2 := l145 h0).
 apply t205. exact h1. exact h2.
Qed.
Lemma t206 : p180 -> p179.
Proof.
 intros h0.
 refine (mul_filq _ _w4 r9 i89 h0) ; finalize.
Qed.
Lemma l140 : s1 -> p179 (* REL(zh * w4, zh * (c4 + zh * (c5 + zh * (c6 + zh * (c7 + zh * (c8 + zh * c9))))), [-1.12174e-16, 1.12174e-16]) *).
Proof.
 intros h0.
 assert (h1 := l141 h0).
 apply t206. exact h1.
Qed.
Lemma t207 : p159 -> p179 -> p158.
Proof.
 intros h0 h1.
 refine (compose r30 r31 r8 i39 i89 i88 h0 h1 _) ; finalize.
Qed.
Lemma l121 : s1 -> p158 (* REL(float<53,-1074,ne>(zh * w4), zh * (c4 + zh * (c5 + zh * (c6 + zh * (c7 + zh * (c8 + zh * c9))))), [-2.23197e-16, 2.23197e-16]) *).
Proof.
 intros h0.
 assert (h1 := l122 h0).
 assert (h2 := l140 h0).
 apply t207. exact h1. exact h2.
Qed.
Notation r106 := ((_c3 / _W)%R).
Definition f162 := Float2 (16287) (-14).
Definition f163 := Float2 (1298782968733915753463231946805133586505455360670058709771661594094003879074807726720525664438871350023117135769336891563) (-399).
Definition i140 := makepairF f162 f163.
Notation p275 := (BND r106 i140). (* BND(c3 / W, [0.99408, 1.00593]) *)
Definition f164 := Float2 (855674708990575425547310640329266582858906787860004266429870799566636946502848084907928231685967903319980103432450400317) (-400).
Definition f165 := Float2 (21975) (-16).
Definition i141 := makepairF f164 f165.
Notation p276 := (BND _W i141). (* BND(W, [0.331368, 0.335312]) *)
Definition f166 := Float2 (-5075250371727389890107917211914216692226490956258971251911711607722182969664826074393634230644539033267764097513627587) (-400).
Definition f167 := Float2 (129) (-16).
Definition i142 := makepairF f166 f167.
Notation p277 := (BND r8 i142). (* BND(zh * (c4 + zh * (c5 + zh * (c6 + zh * (c7 + zh * (c8 + zh * c9))))), [-0.00196544, 0.00196838]) *)
Definition f168 := Float2 (-1025) (-17).
Definition i143 := makepairF f168 f9.
Notation p278 := (BND _zh i143). (* BND(zh, [-0.00782013, 0.0078126]) *)
Definition i144 := makepairF f157 f38.
Notation p279 := (BND r9 i144). (* BND(c4 + zh * (c5 + zh * (c6 + zh * (c7 + zh * (c8 + zh * c9)))), [-0.251573, -0.125]) *)
Lemma t208 : p278 -> p279 -> p277.
Proof.
 intros h0 h1.
 refine (mul_on _zh r9 i143 i144 i142 h0 h1 _) ; finalize.
Qed.
Lemma l218 : s1 -> p277 (* BND(zh * (c4 + zh * (c5 + zh * (c6 + zh * (c7 + zh * (c8 + zh * c9))))), [-0.00196544, 0.00196838]) *).
Proof.
 intros h0.
 assert (h1 := l72 h0).
 assert (h2 := l213 h0).
 apply t208. refine (subset _zh i43 i143 h1 _) ; finalize. refine (subset r9 i135 i144 h2 _) ; finalize.
Qed.
Definition f169 := Float2 (10923) (-15).
Definition i145 := makepairF f11 f169.
Notation p280 := (BND _c3 i145). (* BND(c3, [0.333333, 0.333344]) *)
Lemma t209 : p280 -> p277 -> p276.
Proof.
 intros h0 h1.
 refine (add _c3 r8 i145 i142 i141 h0 h1 _) ; finalize.
Qed.
Lemma l217 : s1 -> p276 (* BND(W, [0.331368, 0.335312]) *).
Proof.
 intros h0.
 assert (h1 := l14 h0).
 assert (h2 := l218 h0).
 apply t209. refine (subset _c3 i8 i145 h1 _) ; finalize. exact h2.
Qed.
Definition f170 := Float2 (21845) (-16).
Definition i146 := makepairF f170 f11.
Notation p281 := (BND _c3 i146). (* BND(c3, [0.333328, 0.333333]) *)
Lemma t210 : p281 -> p276 -> p275.
Proof.
 intros h0 h1.
 refine (div_pp _c3 _W i146 i141 i140 h0 h1 _) ; finalize.
Qed.
Lemma l216 : s1 -> p275 (* BND(c3 / W, [0.99408, 1.00593]) *).
Proof.
 intros h0.
 assert (h1 := l14 h0).
 assert (h2 := l217 h0).
 apply t210. refine (subset _c3 i8 i146 h1 _) ; finalize. exact h2.
Qed.
Lemma t211 : p157 -> p158 -> p275 -> p12 -> p156.
Proof.
 intros h0 h1 h2 h3.
 refine (add_rr _c3 _c3 r30 r8 i63 i88 i140 i87 h0 h1 h2 h3 _) ; finalize.
Qed.
Lemma l119 : s1 -> p156 (* REL(c3 + float<53,-1074,ne>(zh * w4), W, [-1.32384e-18, 1.32384e-18]) *).
Proof.
 intros h0.
 assert (h1 := l120 h0).
 assert (h2 := l121 h0).
 assert (h3 := l216 h0).
 assert (h4 := l11 h0).
 apply t211. exact h1. exact h2. exact h3. exact h4.
Qed.
Lemma t212 : p128 -> p156 -> p127.
Proof.
 intros h0 h1.
 refine (compose _w r29 _W i65 i87 i64 h0 h1 _) ; finalize.
Qed.
Lemma l101 : s1 -> p127 (* REL(w, W, [-8.50844e-17, 8.50844e-17]) *).
Proof.
 intros h0.
 assert (h1 := l102 h0).
 assert (h2 := l119 h0).
 apply t212. exact h1. exact h2.
Qed.
Lemma t213 : p107 -> p127 -> p106.
Proof.
 intros h0 h1.
 refine (mul_rr _z3 r2 _w _W i58 i64 i57 h0 h1 _) ; finalize.
Qed.
Lemma l81 : s1 -> p106 (* REL(z3 * w, T, [-3.07129e-16, 3.07129e-16]) *).
Proof.
 intros h0.
 assert (h1 := l82 h0).
 assert (h2 := l101 h0).
 apply t213. exact h1. exact h2.
Qed.
Lemma t214 : p54 -> p106 -> p53.
Proof.
 intros h0 h1.
 refine (compose _t r54 _T i39 i57 i3 h0 h1 _) ; finalize.
Qed.
Lemma l38 : s1 -> p53 (* REL(t, T, [-4.18151e-16, 4.18151e-16]) *).
Proof.
 intros h0.
 assert (h1 := l39 h0).
 assert (h2 := l81 h0).
 apply t214. exact h1. exact h2.
Qed.
Lemma t215 : p4 -> p53 -> p3.
Proof.
 intros h0 h1.
 refine (bnd_of_nzr_rel _t _T i3 h0 h1) ; finalize.
Qed.
Lemma l3 : s1 -> p3 (* BND((t - T) / T, [-4.18151e-16, 4.18151e-16]) *).
Proof.
 intros h0.
 assert (h1 := l4 h0).
 assert (h2 := l38 h0).
 apply t215. exact h1. exact h2.
Qed.
Lemma l1 : s1 -> False.
Proof.
 intros h0.
 assert (h1 := l2 h0).
 assert (h2 := l3 h0).
 refine (simplify (Tatom false (Abnd 0%nat i2)) Tfalse (Abnd 0%nat i3) (List.cons r51 List.nil) h2 h1 _) ; finalize.
Qed.
End Generated_by_Gappa.
