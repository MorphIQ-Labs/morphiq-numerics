Require Import Gappa.Gappa_library.
Section Generated_by_Gappa.
Notation r4 := (Float1 (1)).
Variable _x : R.
Notation r10 := (Float1 (5)).
Notation r9 := ((r4 / r10)%R).
Variable _k5 : R.
Notation r11 := ((r4 + _k5)%R).
Notation r8 := ((r9 * r11)%R).
Notation r6 := ((_x * r8)%R).
Variable _m5 : R.
Notation r13 := ((r4 + _m5)%R).
Notation r5 := ((r6 * r13)%R).
Notation r3 := ((r4 + r5)%R).
Variable _s5 : R.
Notation _g5 := ((r3 + _s5)%R).
Notation r17 := ((_x / r10)%R).
Notation _G5 := ((r4 + r17)%R).
Notation r1 := ((_g5 - _G5)%R).
Notation r21 := ((r11 * r13)%R).
Notation r20 := ((r21 - r4)%R).
Notation r19 := ((r17 * r20)%R).
Notation r18 := ((r19 + _s5)%R).
Hypothesis a1 : r1 = r18.
Lemma b1 : r1 = r18.
 apply a1.
Qed.
Notation r31 := (Float1 (4)).
Notation r30 := ((r4 / r31)%R).
Variable _k4 : R.
Notation r32 := ((r4 + _k4)%R).
Notation r29 := ((r30 * r32)%R).
Notation r28 := ((_x * r29)%R).
Variable _m4a : R.
Notation r34 := ((r4 + _m4a)%R).
Notation r27 := ((r28 * r34)%R).
Notation r26 := ((r27 * _g5)%R).
Variable _m4b : R.
Notation r36 := ((r4 + _m4b)%R).
Notation r25 := ((r26 * r36)%R).
Notation r24 := ((r4 + r25)%R).
Variable _s4 : R.
Notation _g4 := ((r24 + _s4)%R).
Notation r41 := ((_x / r31)%R).
Notation r40 := ((r41 * _G5)%R).
Notation _G4 := ((r4 + r40)%R).
Notation r22 := ((_g4 - _G4)%R).
Notation r48 := ((r32 * r34)%R).
Notation r47 := ((r48 * r36)%R).
Notation r46 := ((r47 - r4)%R).
Notation r45 := ((_g5 * r46)%R).
Notation r44 := ((r1 + r45)%R).
Notation r43 := ((r41 * r44)%R).
Notation r42 := ((r43 + _s4)%R).
Hypothesis a2 : r22 = r42.
Lemma b2 : r22 = r42.
 apply a2.
Qed.
Notation r58 := (Float1 (3)).
Notation r57 := ((r4 / r58)%R).
Variable _k3 : R.
Notation r59 := ((r4 + _k3)%R).
Notation r56 := ((r57 * r59)%R).
Notation r55 := ((_x * r56)%R).
Variable _m3a : R.
Notation r61 := ((r4 + _m3a)%R).
Notation r54 := ((r55 * r61)%R).
Notation r53 := ((r54 * _g4)%R).
Variable _m3b : R.
Notation r63 := ((r4 + _m3b)%R).
Notation r52 := ((r53 * r63)%R).
Notation r51 := ((r4 + r52)%R).
Variable _s3 : R.
Notation _g3 := ((r51 + _s3)%R).
Notation r68 := ((_x / r58)%R).
Notation r67 := ((r68 * _G4)%R).
Notation _G3 := ((r4 + r67)%R).
Notation r49 := ((_g3 - _G3)%R).
Notation r75 := ((r59 * r61)%R).
Notation r74 := ((r75 * r63)%R).
Notation r73 := ((r74 - r4)%R).
Notation r72 := ((_g4 * r73)%R).
Notation r71 := ((r22 + r72)%R).
Notation r70 := ((r68 * r71)%R).
Notation r69 := ((r70 + _s3)%R).
Hypothesis a3 : r49 = r69.
Lemma b3 : r49 = r69.
 apply a3.
Qed.
Notation r78 := ((_x * _x)%R).
Notation r79 := (Float1 (2)).
Notation r77 := ((r78 / r79)%R).
Notation _D := ((r77 * _G3)%R).
Variable _m2a : R.
Notation r87 := ((r4 + _m2a)%R).
Notation r86 := ((r78 * r87)%R).
Notation r90 := ((r4 / r79)%R).
Variable _k2 : R.
Notation r91 := ((r4 + _k2)%R).
Notation r89 := ((r90 * r91)%R).
Notation r85 := ((r86 * r89)%R).
Variable _m2b : R.
Notation r93 := ((r4 + _m2b)%R).
Notation r84 := ((r85 * r93)%R).
Notation r83 := ((r84 * _g3)%R).
Variable _m2c : R.
Notation r95 := ((r4 + _m2c)%R).
Notation _d := ((r83 * r95)%R).
Notation r81 := ((_d - _D)%R).
Notation r80 := ((r81 / _D)%R).
Notation r101 := ((r87 * r91)%R).
Notation r100 := ((r101 * r93)%R).
Notation r99 := ((r100 * r95)%R).
Notation r103 := ((r49 / _G3)%R).
Notation r102 := ((r4 + r103)%R).
Notation r98 := ((r99 * r102)%R).
Notation r97 := ((r98 - r4)%R).
Hypothesis a4 : (_D <> 0)%R -> (_G3 <> 0)%R -> r80 = r97.
Lemma b4 : NZR _D -> NZR _G3 -> r80 = r97.
 intros h0 h1.
 apply a4.
 exact h0.
 exact h1.
Qed.
Definition f1 := Float2 (-1) (-30).
Definition f2 := Float2 (1) (-30).
Definition i1 := makepairF f1 f2.
Notation p1 := (BND _x i1). (* BND(x, [-9.31323e-10, 9.31323e-10]) *)
Notation p2 := (NZR _x). (* NZR(x) *)
Definition s17 := (p1 /\ p2).
Definition f3 := Float2 (-1) (-127).
Definition f4 := Float2 (1) (-127).
Definition i2 := makepairF f3 f4.
Notation p3 := (BND _k2 i2). (* BND(k2, [-5.87747e-39, 5.87747e-39]) *)
Definition s16 := (s17 /\ p3).
Notation p4 := (BND _k3 i2). (* BND(k3, [-5.87747e-39, 5.87747e-39]) *)
Definition s15 := (s16 /\ p4).
Notation p5 := (BND _k4 i2). (* BND(k4, [-5.87747e-39, 5.87747e-39]) *)
Definition s14 := (s15 /\ p5).
Notation p6 := (BND _k5 i2). (* BND(k5, [-5.87747e-39, 5.87747e-39]) *)
Definition s13 := (s14 /\ p6).
Definition f5 := Float2 (0) (0).
Definition i3 := makepairF f3 f5.
Notation p7 := (BND _m5 i3). (* BND(m5, [-5.87747e-39, 0]) *)
Definition s12 := (s13 /\ p7).
Notation p8 := (BND _m4a i3). (* BND(m4a, [-5.87747e-39, 0]) *)
Definition s11 := (s12 /\ p8).
Notation p9 := (BND _m4b i3). (* BND(m4b, [-5.87747e-39, 0]) *)
Definition s10 := (s11 /\ p9).
Notation p10 := (BND _m3a i3). (* BND(m3a, [-5.87747e-39, 0]) *)
Definition s9 := (s10 /\ p10).
Notation p11 := (BND _m3b i3). (* BND(m3b, [-5.87747e-39, 0]) *)
Definition s8 := (s9 /\ p11).
Notation p12 := (BND _m2a i3). (* BND(m2a, [-5.87747e-39, 0]) *)
Definition s7 := (s8 /\ p12).
Notation p13 := (BND _m2b i3). (* BND(m2b, [-5.87747e-39, 0]) *)
Definition s6 := (s7 /\ p13).
Notation p14 := (BND _m2c i3). (* BND(m2c, [-5.87747e-39, 0]) *)
Definition s5 := (s6 /\ p14).
Definition f6 := Float2 (-1) (-126).
Definition f7 := Float2 (1) (-126).
Definition i4 := makepairF f6 f7.
Notation p15 := (BND _s5 i4). (* BND(s5, [-1.17549e-38, 1.17549e-38]) *)
Definition s4 := (s5 /\ p15).
Notation p16 := (BND _s4 i4). (* BND(s4, [-1.17549e-38, 1.17549e-38]) *)
Definition s3 := (s4 /\ p16).
Notation p17 := (BND _s3 i4). (* BND(s3, [-1.17549e-38, 1.17549e-38]) *)
Definition s2 := (s3 /\ p17).
Definition f8 := Float2 (-1) (-122).
Definition f9 := Float2 (1) (-122).
Definition i5 := makepairF f8 f9.
Notation p18 := (BND r80 i5). (* BND((d - D) / D, [-1.88079e-37, 1.88079e-37]) *)
Definition s18 := (not p18).
Definition s1 := (s2 /\ s18).
Lemma l2 : s1 -> s18.
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj2 h1).
Qed.
Definition f10 := Float2 (-45531302178031097714877504892195961005622120176326536990997205037081082727620030287) (-399).
Definition f11 := Float2 (22765651097260835165040060671607848819120038878021871290631556135281125757124579657) (-399).
Definition i6 := makepairF f10 f11.
Notation p19 := (BND r80 i6). (* BND((d - D) / D, [-3.52648e-38, 1.76324e-38]) *)
Notation p20 := (r80 = r97). (* EQL((d - D) / D, (1 + m2a) * (1 + k2) * (1 + m2b) * (1 + m2c) * (1 + (g3 - G3) / G3) - 1) *)
Notation p21 := (NZR _D). (* NZR(D) *)
Notation p22 := (NZR r77). (* NZR(x * x / 2) *)
Notation p23 := (NZR r78). (* NZR(x * x) *)
Lemma l24 : s1 -> s2.
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj1 h1).
Qed.
Lemma l23 : s1 -> s3.
Proof.
 intros h0.
 assert (h1 := l24 h0).
 exact (proj1 h1).
Qed.
Lemma l22 : s1 -> s4.
Proof.
 intros h0.
 assert (h1 := l23 h0).
 exact (proj1 h1).
Qed.
Lemma l21 : s1 -> s5.
Proof.
 intros h0.
 assert (h1 := l22 h0).
 exact (proj1 h1).
Qed.
Lemma l20 : s1 -> s6.
Proof.
 intros h0.
 assert (h1 := l21 h0).
 exact (proj1 h1).
Qed.
Lemma l19 : s1 -> s7.
Proof.
 intros h0.
 assert (h1 := l20 h0).
 exact (proj1 h1).
Qed.
Lemma l18 : s1 -> s8.
Proof.
 intros h0.
 assert (h1 := l19 h0).
 exact (proj1 h1).
Qed.
Lemma l17 : s1 -> s9.
Proof.
 intros h0.
 assert (h1 := l18 h0).
 exact (proj1 h1).
Qed.
Lemma l16 : s1 -> s10.
Proof.
 intros h0.
 assert (h1 := l17 h0).
 exact (proj1 h1).
Qed.
Lemma l15 : s1 -> s11.
Proof.
 intros h0.
 assert (h1 := l16 h0).
 exact (proj1 h1).
Qed.
Lemma l14 : s1 -> s12.
Proof.
 intros h0.
 assert (h1 := l15 h0).
 exact (proj1 h1).
Qed.
Lemma l13 : s1 -> s13.
Proof.
 intros h0.
 assert (h1 := l14 h0).
 exact (proj1 h1).
Qed.
Lemma l12 : s1 -> s14.
Proof.
 intros h0.
 assert (h1 := l13 h0).
 exact (proj1 h1).
Qed.
Lemma l11 : s1 -> s15.
Proof.
 intros h0.
 assert (h1 := l12 h0).
 exact (proj1 h1).
Qed.
Lemma l10 : s1 -> s16.
Proof.
 intros h0.
 assert (h1 := l11 h0).
 exact (proj1 h1).
Qed.
Lemma l9 : s1 -> s17.
Proof.
 intros h0.
 assert (h1 := l10 h0).
 exact (proj1 h1).
Qed.
Lemma l8 : s1 -> p2 (* NZR(x) *).
Proof.
 intros h0.
 assert (h1 := l9 h0).
 exact (proj2 h1).
Qed.
Lemma t1 : p2 -> p2 -> p23.
Proof.
 intros h0 h1.
 refine (mul_nzr _x _x h0 h1) ; finalize.
Qed.
Lemma l7 : s1 -> p23 (* NZR(x * x) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 apply t1. exact h1. exact h1.
Qed.
Notation p24 := (NZR r79). (* NZR(2) *)
Definition f12 := Float2 (1) (0).
Definition f13 := Float2 (1) (1).
Definition i7 := makepairF f12 f13.
Notation p25 := (ABS r79 i7). (* ABS(2, [1, 2]) *)
Notation p26 := (BND r79 i7). (* BND(2, [1, 2]) *)
Lemma t2 : p26.
Proof.
 refine (constant1 _ i7 _) ; finalize.
Qed.
Lemma l27 : s1 -> p26 (* BND(2, [1, 2]) *).
Proof.
 intros h0.
 apply t2.
Qed.
Lemma t3 : p26 -> p25.
Proof.
 intros h0.
 refine (abs_of_bnd_p r79 i7 i7 h0 _) ; finalize.
Qed.
Lemma l26 : s1 -> p25 (* ABS(2, [1, 2]) *).
Proof.
 intros h0.
 assert (h1 := l27 h0).
 apply t3. exact h1.
Qed.
Lemma t4 : p25 -> p24.
Proof.
 intros h0.
 refine (nzr_of_abs r79 i7 h0 _) ; finalize.
Qed.
Lemma l25 : s1 -> p24 (* NZR(2) *).
Proof.
 intros h0.
 assert (h1 := l26 h0).
 apply t4. exact h1.
Qed.
Lemma t5 : p23 -> p24 -> p22.
Proof.
 intros h0 h1.
 refine (div_nzr r78 r79 h0 h1) ; finalize.
Qed.
Lemma l6 : s1 -> p22 (* NZR(x * x / 2) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 assert (h2 := l25 h0).
 apply t5. exact h1. exact h2.
Qed.
Notation p27 := (NZR _G3). (* NZR(G3) *)
Definition f14 := Float2 (1) (-1).
Definition i8 := makepairF f14 f13.
Notation p28 := (ABS _G3 i8). (* ABS(G3, [0.5, 2]) *)
Definition i9 := makepairF f12 f12.
Notation p29 := (ABS r4 i9). (* ABS(1, [1, 1]) *)
Notation p30 := (BND r4 i9). (* BND(1, [1, 1]) *)
Lemma t6 : p30.
Proof.
 refine (constant1 _ i9 _) ; finalize.
Qed.
Lemma l31 : s1 -> p30 (* BND(1, [1, 1]) *).
Proof.
 intros h0.
 apply t6.
Qed.
Lemma t7 : p30 -> p29.
Proof.
 intros h0.
 refine (abs_of_bnd_p r4 i9 i9 h0 _) ; finalize.
Qed.
Lemma l30 : s1 -> p29 (* ABS(1, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l31 h0).
 apply t7. exact h1.
Qed.
Definition i10 := makepairF f5 f14.
Notation p31 := (ABS r67 i10). (* ABS(x / 3 * G4, [0, 0.5]) *)
Definition f15 := Float2 (1) (-2).
Definition i11 := makepairF f5 f15.
Notation p32 := (ABS r68 i11). (* ABS(x / 3, [0, 0.25]) *)
Definition f16 := Float2 (-301541899055510925582216106793458093367890585066772302186087458353940441771) (-279).
Definition f17 := Float2 (75385474763877731395554026698364523341972646266693075546521864588485110443) (-277).
Definition i12 := makepairF f16 f17.
Notation p33 := (BND r68 i12). (* BND(x / 3, [-3.10441e-10, 3.10441e-10]) *)
Lemma l35 : s1 -> p1 (* BND(x, [-9.31323e-10, 9.31323e-10]) *).
Proof.
 intros h0.
 assert (h1 := l9 h0).
 exact (proj1 h1).
Qed.
Definition f18 := Float2 (3) (0).
Definition f19 := Float2 (1) (2).
Definition i13 := makepairF f18 f19.
Notation p34 := (BND r58 i13). (* BND(3, [3, 4]) *)
Lemma t8 : p34.
Proof.
 refine (constant1 _ i13 _) ; finalize.
Qed.
Lemma l36 : s1 -> p34 (* BND(3, [3, 4]) *).
Proof.
 intros h0.
 apply t8.
Qed.
Lemma t9 : p1 -> p34 -> p33.
Proof.
 intros h0 h1.
 refine (div_op _x r58 i1 i13 i12 h0 h1 _) ; finalize.
Qed.
Lemma l34 : s1 -> p33 (* BND(x / 3, [-3.10441e-10, 3.10441e-10]) *).
Proof.
 intros h0.
 assert (h1 := l35 h0).
 assert (h2 := l36 h0).
 apply t9. exact h1. exact h2.
Qed.
Definition f20 := Float2 (-1) (-2).
Definition i14 := makepairF f20 f15.
Notation p35 := (BND r68 i14). (* BND(x / 3, [-0.25, 0.25]) *)
Lemma t10 : p35 -> p32.
Proof.
 intros h0.
 refine (abs_of_bnd_o r68 i14 i11 h0 _) ; finalize.
Qed.
Lemma l33 : s1 -> p32 (* ABS(x / 3, [0, 0.25]) *).
Proof.
 intros h0.
 assert (h1 := l34 h0).
 apply t10. refine (subset r68 i12 i14 h1 _) ; finalize.
Qed.
Notation p36 := (ABS _G4 i8). (* ABS(G4, [0.5, 2]) *)
Notation p37 := (ABS r40 i10). (* ABS(x / 4 * G5, [0, 0.5]) *)
Notation p38 := (ABS r41 i11). (* ABS(x / 4, [0, 0.25]) *)
Definition f21 := Float2 (-1) (-32).
Definition f22 := Float2 (1) (-32).
Definition i15 := makepairF f21 f22.
Notation p39 := (BND r41 i15). (* BND(x / 4, [-2.32831e-10, 2.32831e-10]) *)
Definition i16 := makepairF f19 f19.
Notation p40 := (BND r31 i16). (* BND(4, [4, 4]) *)
Lemma t11 : p40.
Proof.
 refine (constant1 _ i16 _) ; finalize.
Qed.
Lemma l41 : s1 -> p40 (* BND(4, [4, 4]) *).
Proof.
 intros h0.
 apply t11.
Qed.
Lemma t12 : p1 -> p40 -> p39.
Proof.
 intros h0 h1.
 refine (div_op _x r31 i1 i16 i15 h0 h1 _) ; finalize.
Qed.
Lemma l40 : s1 -> p39 (* BND(x / 4, [-2.32831e-10, 2.32831e-10]) *).
Proof.
 intros h0.
 assert (h1 := l35 h0).
 assert (h2 := l41 h0).
 apply t12. exact h1. exact h2.
Qed.
Notation p41 := (BND r41 i14). (* BND(x / 4, [-0.25, 0.25]) *)
Lemma t13 : p41 -> p38.
Proof.
 intros h0.
 refine (abs_of_bnd_o r41 i14 i11 h0 _) ; finalize.
Qed.
Lemma l39 : s1 -> p38 (* ABS(x / 4, [0, 0.25]) *).
Proof.
 intros h0.
 assert (h1 := l40 h0).
 apply t13. refine (subset r41 i15 i14 h1 _) ; finalize.
Qed.
Notation p42 := (ABS _G5 i8). (* ABS(G5, [0.5, 2]) *)
Notation p43 := (ABS r17 i10). (* ABS(x / 5, [0, 0.5]) *)
Notation p44 := (ABS _x i10). (* ABS(x, [0, 0.5]) *)
Definition f23 := Float2 (-1) (-1).
Definition i17 := makepairF f23 f14.
Notation p45 := (BND _x i17). (* BND(x, [-0.5, 0.5]) *)
Lemma t14 : p45 -> p44.
Proof.
 intros h0.
 refine (abs_of_bnd_o _x i17 i10 h0 _) ; finalize.
Qed.
Lemma l44 : s1 -> p44 (* ABS(x, [0, 0.5]) *).
Proof.
 intros h0.
 assert (h1 := l35 h0).
 apply t14. refine (subset _x i1 i17 h1 _) ; finalize.
Qed.
Definition f24 := Float2 (1) (3).
Definition i18 := makepairF f12 f24.
Notation p46 := (ABS r10 i18). (* ABS(5, [1, 8]) *)
Definition f25 := Float2 (5) (0).
Definition i19 := makepairF f25 f25.
Notation p47 := (BND r10 i19). (* BND(5, [5, 5]) *)
Lemma t15 : p47.
Proof.
 refine (constant1 _ i19 _) ; finalize.
Qed.
Lemma l46 : s1 -> p47 (* BND(5, [5, 5]) *).
Proof.
 intros h0.
 apply t15.
Qed.
Notation p48 := (BND r10 i18). (* BND(5, [1, 8]) *)
Lemma t16 : p48 -> p46.
Proof.
 intros h0.
 refine (abs_of_bnd_p r10 i18 i18 h0 _) ; finalize.
Qed.
Lemma l45 : s1 -> p46 (* ABS(5, [1, 8]) *).
Proof.
 intros h0.
 assert (h1 := l46 h0).
 apply t16. refine (subset r10 i19 i18 h1 _) ; finalize.
Qed.
Lemma t17 : p44 -> p46 -> p43.
Proof.
 intros h0 h1.
 refine (div_aa _x r10 i10 i18 i10 h0 h1 _) ; finalize.
Qed.
Lemma l43 : s1 -> p43 (* ABS(x / 5, [0, 0.5]) *).
Proof.
 intros h0.
 assert (h1 := l44 h0).
 assert (h2 := l45 h0).
 apply t17. exact h1. exact h2.
Qed.
Lemma t18 : p29 -> p43 -> p42.
Proof.
 intros h0 h1.
 refine (add_aa_p r4 r17 i9 i10 i8 h0 h1 _) ; finalize.
Qed.
Lemma l42 : s1 -> p42 (* ABS(G5, [0.5, 2]) *).
Proof.
 intros h0.
 assert (h1 := l30 h0).
 assert (h2 := l43 h0).
 apply t18. exact h1. exact h2.
Qed.
Lemma t19 : p38 -> p42 -> p37.
Proof.
 intros h0 h1.
 refine (mul_aa r41 _G5 i11 i8 i10 h0 h1 _) ; finalize.
Qed.
Lemma l38 : s1 -> p37 (* ABS(x / 4 * G5, [0, 0.5]) *).
Proof.
 intros h0.
 assert (h1 := l39 h0).
 assert (h2 := l42 h0).
 apply t19. exact h1. exact h2.
Qed.
Lemma t20 : p29 -> p37 -> p36.
Proof.
 intros h0 h1.
 refine (add_aa_p r4 r40 i9 i10 i8 h0 h1 _) ; finalize.
Qed.
Lemma l37 : s1 -> p36 (* ABS(G4, [0.5, 2]) *).
Proof.
 intros h0.
 assert (h1 := l30 h0).
 assert (h2 := l38 h0).
 apply t20. exact h1. exact h2.
Qed.
Lemma t21 : p32 -> p36 -> p31.
Proof.
 intros h0 h1.
 refine (mul_aa r68 _G4 i11 i8 i10 h0 h1 _) ; finalize.
Qed.
Lemma l32 : s1 -> p31 (* ABS(x / 3 * G4, [0, 0.5]) *).
Proof.
 intros h0.
 assert (h1 := l33 h0).
 assert (h2 := l37 h0).
 apply t21. exact h1. exact h2.
Qed.
Lemma t22 : p29 -> p31 -> p28.
Proof.
 intros h0 h1.
 refine (add_aa_p r4 r67 i9 i10 i8 h0 h1 _) ; finalize.
Qed.
Lemma l29 : s1 -> p28 (* ABS(G3, [0.5, 2]) *).
Proof.
 intros h0.
 assert (h1 := l30 h0).
 assert (h2 := l32 h0).
 apply t22. exact h1. exact h2.
Qed.
Lemma t23 : p28 -> p27.
Proof.
 intros h0.
 refine (nzr_of_abs _G3 i8 h0 _) ; finalize.
Qed.
Lemma l28 : s1 -> p27 (* NZR(G3) *).
Proof.
 intros h0.
 assert (h1 := l29 h0).
 apply t23. exact h1.
Qed.
Lemma t24 : p22 -> p27 -> p21.
Proof.
 intros h0 h1.
 refine (mul_nzr r77 _G3 h0 h1) ; finalize.
Qed.
Lemma l5 : s1 -> p21 (* NZR(D) *).
Proof.
 intros h0.
 assert (h1 := l6 h0).
 assert (h2 := l28 h0).
 apply t24. exact h1. exact h2.
Qed.
Lemma t25 : p21 -> p27 -> p20.
Proof.
 intros h0 h1.
 refine (b4 h0 h1) ; finalize.
Qed.
Lemma l4 : s1 -> p20 (* EQL((d - D) / D, (1 + m2a) * (1 + k2) * (1 + m2b) * (1 + m2c) * (1 + (g3 - G3) / G3) - 1) *).
Proof.
 intros h0.
 assert (h1 := l5 h0).
 assert (h2 := l28 h0).
 apply t25. exact h1. exact h2.
Qed.
Notation p49 := (BND r97 i6). (* BND((1 + m2a) * (1 + k2) * (1 + m2b) * (1 + m2c) * (1 + (g3 - G3) / G3) - 1, [-3.52648e-38, 1.76324e-38]) *)
Definition f26 := Float2 (1291124939043454294827959586001505937119321594236580658700452173378127850002798477138496139649071710680870503258753716401) (-399).
Definition f27 := Float2 (1291124939043454294827959586001505937187618547511872591580369738941931659827540636192844547930700471853232711743498326345) (-399).
Definition i20 := makepairF f26 f27.
Notation p50 := (BND r98 i20). (* BND((1 + m2a) * (1 + k2) * (1 + m2b) * (1 + m2c) * (1 + (g3 - G3) / G3), [1, 1]) *)
Definition f28 := Float2 (1231312693637327475383720003129487931379793829892716159517491422630506828396225547215476383302886748728802668445695) (-379).
Definition f29 := Float2 (170141183460469231731687303715884105729) (-127).
Definition i21 := makepairF f28 f29.
Notation p51 := (BND r99 i21). (* BND((1 + m2a) * (1 + k2) * (1 + m2b) * (1 + m2c), [1, 1]) *)
Definition f30 := Float2 (4925250774549309901534880012517951725548123341880193686925858436774199290547709261477934266526216329006041303875583) (-381).
Definition i22 := makepairF f30 f29.
Notation p52 := (BND r100 i22). (* BND((1 + m2a) * (1 + k2) * (1 + m2b), [1, 1]) *)
Definition f31 := Float2 (28948022309329048855892746252171976962977213799489202546401021394546514198529) (-254).
Definition i23 := makepairF f31 f29.
Notation p53 := (BND r101 i23). (* BND((1 + m2a) * (1 + k2), [1, 1]) *)
Definition f32 := Float2 (170141183460469231731687303715884105727) (-127).
Definition i24 := makepairF f32 f12.
Notation p54 := (BND r87 i24). (* BND(1 + m2a, [1, 1]) *)
Lemma l53 : s1 -> p12 (* BND(m2a, [-5.87747e-39, 0]) *).
Proof.
 intros h0.
 assert (h1 := l19 h0).
 exact (proj2 h1).
Qed.
Lemma t26 : p30 -> p12 -> p54.
Proof.
 intros h0 h1.
 refine (add r4 _m2a i9 i3 i24 h0 h1 _) ; finalize.
Qed.
Lemma l52 : s1 -> p54 (* BND(1 + m2a, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l31 h0).
 assert (h2 := l53 h0).
 apply t26. exact h1. exact h2.
Qed.
Definition i25 := makepairF f32 f29.
Notation p55 := (BND r91 i25). (* BND(1 + k2, [1, 1]) *)
Lemma l55 : s1 -> p3 (* BND(k2, [-5.87747e-39, 5.87747e-39]) *).
Proof.
 intros h0.
 assert (h1 := l10 h0).
 exact (proj2 h1).
Qed.
Lemma t27 : p30 -> p3 -> p55.
Proof.
 intros h0 h1.
 refine (add r4 _k2 i9 i2 i25 h0 h1 _) ; finalize.
Qed.
Lemma l54 : s1 -> p55 (* BND(1 + k2, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l31 h0).
 assert (h2 := l55 h0).
 apply t27. exact h1. exact h2.
Qed.
Lemma t28 : p54 -> p55 -> p53.
Proof.
 intros h0 h1.
 refine (mul_pp r87 r91 i24 i25 i23 h0 h1 _) ; finalize.
Qed.
Lemma l51 : s1 -> p53 (* BND((1 + m2a) * (1 + k2), [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l52 h0).
 assert (h2 := l54 h0).
 apply t28. exact h1. exact h2.
Qed.
Notation p56 := (BND r93 i24). (* BND(1 + m2b, [1, 1]) *)
Lemma l57 : s1 -> p13 (* BND(m2b, [-5.87747e-39, 0]) *).
Proof.
 intros h0.
 assert (h1 := l20 h0).
 exact (proj2 h1).
Qed.
Lemma t29 : p30 -> p13 -> p56.
Proof.
 intros h0 h1.
 refine (add r4 _m2b i9 i3 i24 h0 h1 _) ; finalize.
Qed.
Lemma l56 : s1 -> p56 (* BND(1 + m2b, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l31 h0).
 assert (h2 := l57 h0).
 apply t29. exact h1. exact h2.
Qed.
Lemma t30 : p53 -> p56 -> p52.
Proof.
 intros h0 h1.
 refine (mul_pp r101 r93 i23 i24 i22 h0 h1 _) ; finalize.
Qed.
Lemma l50 : s1 -> p52 (* BND((1 + m2a) * (1 + k2) * (1 + m2b), [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l51 h0).
 assert (h2 := l56 h0).
 apply t30. exact h1. exact h2.
Qed.
Notation p57 := (BND r95 i24). (* BND(1 + m2c, [1, 1]) *)
Lemma l59 : s1 -> p14 (* BND(m2c, [-5.87747e-39, 0]) *).
Proof.
 intros h0.
 assert (h1 := l21 h0).
 exact (proj2 h1).
Qed.
Lemma t31 : p30 -> p14 -> p57.
Proof.
 intros h0 h1.
 refine (add r4 _m2c i9 i3 i24 h0 h1 _) ; finalize.
Qed.
Lemma l58 : s1 -> p57 (* BND(1 + m2c, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l31 h0).
 assert (h2 := l59 h0).
 apply t31. exact h1. exact h2.
Qed.
Lemma t32 : p52 -> p57 -> p51.
Proof.
 intros h0 h1.
 refine (mul_pp r100 r95 i22 i24 i21 h0 h1 _) ; finalize.
Qed.
Lemma l49 : s1 -> p51 (* BND((1 + m2a) * (1 + k2) * (1 + m2b) * (1 + m2c), [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l50 h0).
 assert (h2 := l58 h0).
 apply t32. exact h1. exact h2.
Qed.
Definition f33 := Float2 (2582249878086908589655919172003011874299351591355215350867137531344490665836923326265478541443296743278648529100138231763) (-400).
Definition f34 := Float2 (1291124939043454294827959586001505937180029997151615837397090590868402289098379531496906082558489459796578907422678377495) (-399).
Definition i26 := makepairF f33 f34.
Notation p58 := (BND r102 i26). (* BND(1 + (g3 - G3) / G3, [1, 1]) *)
Definition f35 := Float2 (-30354201474008161963521825196156956179917868364166811836841088157254642872609261613) (-400).
Definition f36 := Float2 (15177100737004080981760912598078478089958934182083405918420544078627321436304630807) (-399).
Definition i27 := makepairF f35 f36.
Notation p59 := (BND r103 i27). (* BND((g3 - G3) / G3, [-1.17549e-38, 1.17549e-38]) *)
Definition f37 := Float2 (-60708402929169955211208815325151754122553274987721296499794656875529203739752171657) (-401).
Definition f38 := Float2 (30354201464584977605604407662575877061276637493860648249897328437764601869876085829) (-400).
Definition i28 := makepairF f37 f38.
Notation p60 := (BND r49 i28). (* BND(g3 - G3, [-1.17549e-38, 1.17549e-38]) *)
Notation p61 := (BND r69 i28). (* BND(x / 3 * (g4 - G4 + g4 * ((1 + k3) * (1 + m3a) * (1 + m3b) - 1)) + s3, [-1.17549e-38, 1.17549e-38]) *)
Definition f39 := Float2 (-47115921744975630736916788289978061267341936460675519071188444827089406089) (-401).
Definition f40 := Float2 (23557960872487815368458394144989030633670968230337759535594222413544703045) (-400).
Definition i29 := makepairF f39 f40.
Notation p62 := (BND r70 i29). (* BND(x / 3 * (g4 - G4 + g4 * ((1 + k3) * (1 + m3a) * (1 + m3b) - 1)), [-9.12304e-48, 9.12304e-48]) *)
Definition f41 := Float2 (-70673882617463446105375182434967091901012904691013278606782667240634109133) (-370).
Definition f42 := Float2 (1) (-125).
Definition i30 := makepairF f41 f42.
Notation p63 := (BND r71 i30). (* BND(g4 - G4 + g4 * ((1 + k3) * (1 + m3a) * (1 + m3b) - 1), [-2.93874e-38, 2.35099e-38]) *)
Definition f43 := Float2 (-113078212211636779398439246060672663182119765816783635171427501676876844237) (-372).
Definition f44 := Float2 (5) (-128).
Definition i31 := makepairF f43 f44.
Notation p64 := (BND r22 i31). (* BND(g4 - G4, [-1.17549e-38, 1.46937e-38]) *)
Notation p65 := (BND r42 i31). (* BND(x / 4 * (g5 - G5 + g5 * ((1 + k4) * (1 + m4a) * (1 + m4b) - 1)) + s4, [-1.17549e-38, 1.46937e-38]) *)
Definition f45 := Float2 (-65820182305108206013125878169160796416744021851644704794149178573) (-372).
Definition f46 := Float2 (1) (-128).
Definition i32 := makepairF f45 f46.
Notation p66 := (BND r43 i32). (* BND(x / 4 * (g5 - G5 + g5 * ((1 + k4) * (1 + m4a) * (1 + m4b) - 1)), [-6.84228e-48, 2.93874e-39]) *)
Definition f47 := Float2 (-65820182305108206013125878169160796416744021851644704794149178573) (-340).
Definition i33 := makepairF f47 f42.
Notation p67 := (BND r44 i33). (* BND(g5 - G5 + g5 * ((1 + k4) * (1 + m4a) * (1 + m4b) - 1), [-2.93874e-38, 2.35099e-38]) *)
Definition f48 := Float2 (-210624583376346259242002810141314548532838105901622651886061486081) (-343).
Definition i34 := makepairF f48 f44.
Notation p68 := (BND r1 i34). (* BND(g5 - G5, [-1.17549e-38, 1.46937e-38]) *)
Notation p69 := (r1 = r18). (* EQL(g5 - G5, x / 5 * ((1 + k5) * (1 + m5) - 1) + s5) *)
Lemma t33 : p69.
Proof.
 refine (b1) ; finalize.
Qed.
Lemma l71 : s1 -> p69 (* EQL(g5 - G5, x / 5 * ((1 + k5) * (1 + m5) - 1) + s5) *).
Proof.
 intros h0.
 apply t33.
Qed.
Notation p70 := (BND r18 i34). (* BND(x / 5 * ((1 + k5) * (1 + m5) - 1) + s5, [-1.17549e-38, 1.46937e-38]) *)
Definition f49 := Float2 (-39231885846166754773973683895047915100524429377439531009) (-343).
Definition i35 := makepairF f49 f46.
Notation p71 := (BND r19 i35). (* BND(x / 5 * ((1 + k5) * (1 + m5) - 1), [-2.18953e-48, 2.93874e-39]) *)
Definition f50 := Float2 (19615942923083377386986841947523957550319860763950107853) (-216).
Definition i36 := makepairF f21 f50.
Notation p72 := (BND r17 i36). (* BND(x / 5, [-2.32831e-10, 1.86265e-10]) *)
Definition i37 := makepairF f25 f24.
Notation p73 := (BND r10 i37). (* BND(5, [5, 8]) *)
Lemma t34 : p1 -> p73 -> p72.
Proof.
 intros h0 h1.
 refine (div_op _x r10 i1 i37 i36 h0 h1 _) ; finalize.
Qed.
Lemma l74 : s1 -> p72 (* BND(x / 5, [-2.32831e-10, 1.86265e-10]) *).
Proof.
 intros h0.
 assert (h1 := l35 h0).
 assert (h2 := l46 h0).
 apply t34. exact h1. refine (subset r10 i19 i37 h2 _) ; finalize.
Qed.
Definition f51 := Float2 (-340282366920938463463374607431768211455) (-254).
Definition i38 := makepairF f51 f4.
Notation p74 := (BND r20 i38). (* BND((1 + k5) * (1 + m5) - 1, [-1.17549e-38, 5.87747e-39]) *)
Notation p75 := (BND r21 i23). (* BND((1 + k5) * (1 + m5), [1, 1]) *)
Notation p76 := (BND r11 i25). (* BND(1 + k5, [1, 1]) *)
Lemma l78 : s1 -> p6 (* BND(k5, [-5.87747e-39, 5.87747e-39]) *).
Proof.
 intros h0.
 assert (h1 := l13 h0).
 exact (proj2 h1).
Qed.
Lemma t35 : p30 -> p6 -> p76.
Proof.
 intros h0 h1.
 refine (add r4 _k5 i9 i2 i25 h0 h1 _) ; finalize.
Qed.
Lemma l77 : s1 -> p76 (* BND(1 + k5, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l31 h0).
 assert (h2 := l78 h0).
 apply t35. exact h1. exact h2.
Qed.
Notation p77 := (BND r13 i24). (* BND(1 + m5, [1, 1]) *)
Lemma l80 : s1 -> p7 (* BND(m5, [-5.87747e-39, 0]) *).
Proof.
 intros h0.
 assert (h1 := l14 h0).
 exact (proj2 h1).
Qed.
Lemma t36 : p30 -> p7 -> p77.
Proof.
 intros h0 h1.
 refine (add r4 _m5 i9 i3 i24 h0 h1 _) ; finalize.
Qed.
Lemma l79 : s1 -> p77 (* BND(1 + m5, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l31 h0).
 assert (h2 := l80 h0).
 apply t36. exact h1. exact h2.
Qed.
Lemma t37 : p76 -> p77 -> p75.
Proof.
 intros h0 h1.
 refine (mul_pp r11 r13 i25 i24 i23 h0 h1 _) ; finalize.
Qed.
Lemma l76 : s1 -> p75 (* BND((1 + k5) * (1 + m5), [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l77 h0).
 assert (h2 := l79 h0).
 apply t37. exact h1. exact h2.
Qed.
Lemma t38 : p75 -> p30 -> p74.
Proof.
 intros h0 h1.
 refine (sub r21 r4 i23 i9 i38 h0 h1 _) ; finalize.
Qed.
Lemma l75 : s1 -> p74 (* BND((1 + k5) * (1 + m5) - 1, [-1.17549e-38, 5.87747e-39]) *).
Proof.
 intros h0.
 assert (h1 := l76 h0).
 assert (h2 := l31 h0).
 apply t38. exact h1. exact h2.
Qed.
Lemma t39 : p72 -> p74 -> p71.
Proof.
 intros h0 h1.
 refine (mul_oo r17 r20 i36 i38 i35 h0 h1 _) ; finalize.
Qed.
Lemma l73 : s1 -> p71 (* BND(x / 5 * ((1 + k5) * (1 + m5) - 1), [-2.18953e-48, 2.93874e-39]) *).
Proof.
 intros h0.
 assert (h1 := l74 h0).
 assert (h2 := l75 h0).
 apply t39. exact h1. exact h2.
Qed.
Lemma l81 : s1 -> p15 (* BND(s5, [-1.17549e-38, 1.17549e-38]) *).
Proof.
 intros h0.
 assert (h1 := l22 h0).
 exact (proj2 h1).
Qed.
Lemma t40 : p71 -> p15 -> p70.
Proof.
 intros h0 h1.
 refine (add r19 _s5 i35 i4 i34 h0 h1 _) ; finalize.
Qed.
Lemma l72 : s1 -> p70 (* BND(x / 5 * ((1 + k5) * (1 + m5) - 1) + s5, [-1.17549e-38, 1.46937e-38]) *).
Proof.
 intros h0.
 assert (h1 := l73 h0).
 assert (h2 := l81 h0).
 apply t40. exact h1. exact h2.
Qed.
Lemma t41 : p69 -> p70 -> p68.
Proof.
 intros h0 h1.
 refine (bnd_rewrite r1 r18 i34 h0 h1) ; finalize.
Qed.
Lemma l70 : s1 -> p68 (* BND(g5 - G5, [-1.17549e-38, 1.46937e-38]) *).
Proof.
 intros h0.
 assert (h1 := l71 h0).
 assert (h2 := l72 h0).
 apply t41. exact h1. exact h2.
Qed.
Definition f52 := Float2 (-315936875064519388863004215211971822801114068911534986467131942503) (-343).
Definition f53 := Float2 (3) (-128).
Definition i39 := makepairF f52 f53.
Notation p78 := (BND r45 i39). (* BND(g5 * ((1 + k4) * (1 + m4a) * (1 + m4b) - 1), [-1.76324e-38, 8.81621e-39]) *)
Definition f54 := Float2 (3369993334021540147872044962261032776565023775688628622195868617933) (-221).
Definition i40 := makepairF f14 f54.
Notation p79 := (BND _g5 i40). (* BND(g5, [0.5, 1]) *)
Definition f55 := Float2 (3) (-2).
Definition f56 := Float2 (3369993334021540147872044962261032776525409694431496453399096642765) (-221).
Definition i41 := makepairF f55 f56.
Notation p80 := (BND r3 i41). (* BND(1 + x * (1 / 5 * (1 + k5)) * (1 + m5), [0.75, 1]) *)
Definition f57 := Float2 (627710173538668076383578942320766641613924893261145361613) (-221).
Definition i42 := makepairF f20 f57.
Notation p81 := (BND r5 i42). (* BND(x * (1 / 5 * (1 + k5)) * (1 + m5), [-0.25, 1.86265e-10]) *)
Notation p82 := (BND r6 i42). (* BND(x * (1 / 5 * (1 + k5)), [-0.25, 1.86265e-10]) *)
Definition f58 := Float2 (1) (-3).
Definition f59 := Float2 (627710173538668076383578942320766641613924893261145361613) (-191).
Definition i43 := makepairF f58 f59.
Notation p83 := (BND r8 i43). (* BND(1 / 5 * (1 + k5), [0.125, 0.2]) *)
Definition f60 := Float2 (3) (-4).
Definition f61 := Float2 (2510840694154672305534315769283066566440942177785613805159) (-193).
Definition i44 := makepairF f60 f61.
Notation p84 := (BND r9 i44). (* BND(1 / 5, [0.1875, 0.2]) *)
Lemma t42 : p30 -> p47 -> p84.
Proof.
 intros h0 h1.
 refine (div_pp r4 r10 i9 i19 i44 h0 h1 _) ; finalize.
Qed.
Lemma l88 : s1 -> p84 (* BND(1 / 5, [0.1875, 0.2]) *).
Proof.
 intros h0.
 assert (h1 := l31 h0).
 assert (h2 := l46 h0).
 apply t42. exact h1. exact h2.
Qed.
Definition i45 := makepairF f55 f29.
Notation p85 := (BND r11 i45). (* BND(1 + k5, [0.75, 1]) *)
Lemma t43 : p84 -> p85 -> p83.
Proof.
 intros h0 h1.
 refine (mul_pp r9 r11 i44 i45 i43 h0 h1 _) ; finalize.
Qed.
Lemma l87 : s1 -> p83 (* BND(1 / 5 * (1 + k5), [0.125, 0.2]) *).
Proof.
 intros h0.
 assert (h1 := l88 h0).
 assert (h2 := l77 h0).
 apply t43. exact h1. refine (subset r11 i25 i45 h2 _) ; finalize.
Qed.
Definition f62 := Float2 (-1) (0).
Definition i46 := makepairF f62 f2.
Notation p86 := (BND _x i46). (* BND(x, [-1, 9.31323e-10]) *)
Lemma t44 : p86 -> p83 -> p82.
Proof.
 intros h0 h1.
 refine (mul_op _x r8 i46 i43 i42 h0 h1 _) ; finalize.
Qed.
Lemma l86 : s1 -> p82 (* BND(x * (1 / 5 * (1 + k5)), [-0.25, 1.86265e-10]) *).
Proof.
 intros h0.
 assert (h1 := l35 h0).
 assert (h2 := l87 h0).
 apply t44. refine (subset _x i1 i46 h1 _) ; finalize. exact h2.
Qed.
Definition i47 := makepairF f14 f12.
Notation p87 := (BND r13 i47). (* BND(1 + m5, [0.5, 1]) *)
Lemma t45 : p82 -> p87 -> p81.
Proof.
 intros h0 h1.
 refine (mul_op r6 r13 i42 i47 i42 h0 h1 _) ; finalize.
Qed.
Lemma l85 : s1 -> p81 (* BND(x * (1 / 5 * (1 + k5)) * (1 + m5), [-0.25, 1.86265e-10]) *).
Proof.
 intros h0.
 assert (h1 := l86 h0).
 assert (h2 := l79 h0).
 apply t45. exact h1. refine (subset r13 i24 i47 h2 _) ; finalize.
Qed.
Lemma t46 : p30 -> p81 -> p80.
Proof.
 intros h0 h1.
 refine (add r4 r5 i9 i42 i41 h0 h1 _) ; finalize.
Qed.
Lemma l84 : s1 -> p80 (* BND(1 + x * (1 / 5 * (1 + k5)) * (1 + m5), [0.75, 1]) *).
Proof.
 intros h0.
 assert (h1 := l31 h0).
 assert (h2 := l85 h0).
 apply t46. exact h1. exact h2.
Qed.
Definition i48 := makepairF f20 f7.
Notation p88 := (BND _s5 i48). (* BND(s5, [-0.25, 1.17549e-38]) *)
Lemma t47 : p80 -> p88 -> p79.
Proof.
 intros h0 h1.
 refine (add r3 _s5 i41 i48 i40 h0 h1 _) ; finalize.
Qed.
Lemma l83 : s1 -> p79 (* BND(g5, [0.5, 1]) *).
Proof.
 intros h0.
 assert (h1 := l84 h0).
 assert (h2 := l81 h0).
 apply t47. exact h1. refine (subset _s5 i4 i48 h2 _) ; finalize.
Qed.
Definition f63 := Float2 (-631873750011343120187508166102022593909656752285438526701168492545) (-344).
Definition i49 := makepairF f63 f4.
Notation p89 := (BND r46 i49). (* BND((1 + k4) * (1 + m4a) * (1 + m4b) - 1, [-1.76324e-38, 5.87747e-39]) *)
Definition f64 := Float2 (35835915874844867368919076489095108449314454205743049438212317449318647344972918373808601365644545359871) (-344).
Definition i50 := makepairF f64 f29.
Notation p90 := (BND r47 i50). (* BND((1 + k4) * (1 + m4a) * (1 + m4b), [1, 1]) *)
Notation p91 := (BND r48 i23). (* BND((1 + k4) * (1 + m4a), [1, 1]) *)
Notation p92 := (BND r32 i25). (* BND(1 + k4, [1, 1]) *)
Lemma l93 : s1 -> p5 (* BND(k4, [-5.87747e-39, 5.87747e-39]) *).
Proof.
 intros h0.
 assert (h1 := l12 h0).
 exact (proj2 h1).
Qed.
Lemma t48 : p30 -> p5 -> p92.
Proof.
 intros h0 h1.
 refine (add r4 _k4 i9 i2 i25 h0 h1 _) ; finalize.
Qed.
Lemma l92 : s1 -> p92 (* BND(1 + k4, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l31 h0).
 assert (h2 := l93 h0).
 apply t48. exact h1. exact h2.
Qed.
Notation p93 := (BND r34 i24). (* BND(1 + m4a, [1, 1]) *)
Lemma l95 : s1 -> p8 (* BND(m4a, [-5.87747e-39, 0]) *).
Proof.
 intros h0.
 assert (h1 := l15 h0).
 exact (proj2 h1).
Qed.
Lemma t49 : p30 -> p8 -> p93.
Proof.
 intros h0 h1.
 refine (add r4 _m4a i9 i3 i24 h0 h1 _) ; finalize.
Qed.
Lemma l94 : s1 -> p93 (* BND(1 + m4a, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l31 h0).
 assert (h2 := l95 h0).
 apply t49. exact h1. exact h2.
Qed.
Lemma t50 : p92 -> p93 -> p91.
Proof.
 intros h0 h1.
 refine (mul_pp r32 r34 i25 i24 i23 h0 h1 _) ; finalize.
Qed.
Lemma l91 : s1 -> p91 (* BND((1 + k4) * (1 + m4a), [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l92 h0).
 assert (h2 := l94 h0).
 apply t50. exact h1. exact h2.
Qed.
Notation p94 := (BND r36 i24). (* BND(1 + m4b, [1, 1]) *)
Lemma l97 : s1 -> p9 (* BND(m4b, [-5.87747e-39, 0]) *).
Proof.
 intros h0.
 assert (h1 := l16 h0).
 exact (proj2 h1).
Qed.
Lemma t51 : p30 -> p9 -> p94.
Proof.
 intros h0 h1.
 refine (add r4 _m4b i9 i3 i24 h0 h1 _) ; finalize.
Qed.
Lemma l96 : s1 -> p94 (* BND(1 + m4b, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l31 h0).
 assert (h2 := l97 h0).
 apply t51. exact h1. exact h2.
Qed.
Lemma t52 : p91 -> p94 -> p90.
Proof.
 intros h0 h1.
 refine (mul_pp r48 r36 i23 i24 i50 h0 h1 _) ; finalize.
Qed.
Lemma l90 : s1 -> p90 (* BND((1 + k4) * (1 + m4a) * (1 + m4b), [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l91 h0).
 assert (h2 := l96 h0).
 apply t52. exact h1. exact h2.
Qed.
Lemma t53 : p90 -> p30 -> p89.
Proof.
 intros h0 h1.
 refine (sub r47 r4 i50 i9 i49 h0 h1 _) ; finalize.
Qed.
Lemma l89 : s1 -> p89 (* BND((1 + k4) * (1 + m4a) * (1 + m4b) - 1, [-1.76324e-38, 5.87747e-39]) *).
Proof.
 intros h0.
 assert (h1 := l90 h0).
 assert (h2 := l31 h0).
 apply t53. exact h1. exact h2.
Qed.
Lemma t54 : p79 -> p89 -> p78.
Proof.
 intros h0 h1.
 refine (mul_po _g5 r46 i40 i49 i39 h0 h1 _) ; finalize.
Qed.
Lemma l82 : s1 -> p78 (* BND(g5 * ((1 + k4) * (1 + m4a) * (1 + m4b) - 1), [-1.76324e-38, 8.81621e-39]) *).
Proof.
 intros h0.
 assert (h1 := l83 h0).
 assert (h2 := l89 h0).
 apply t54. exact h1. exact h2.
Qed.
Lemma t55 : p68 -> p78 -> p67.
Proof.
 intros h0 h1.
 refine (add r1 r45 i34 i39 i33 h0 h1 _) ; finalize.
Qed.
Lemma l69 : s1 -> p67 (* BND(g5 - G5 + g5 * ((1 + k4) * (1 + m4a) * (1 + m4b) - 1), [-2.93874e-38, 2.35099e-38]) *).
Proof.
 intros h0.
 assert (h1 := l70 h0).
 assert (h2 := l82 h0).
 apply t55. exact h1. exact h2.
Qed.
Lemma t56 : p39 -> p67 -> p66.
Proof.
 intros h0 h1.
 refine (mul_oo r41 r44 i15 i33 i32 h0 h1 _) ; finalize.
Qed.
Lemma l68 : s1 -> p66 (* BND(x / 4 * (g5 - G5 + g5 * ((1 + k4) * (1 + m4a) * (1 + m4b) - 1)), [-6.84228e-48, 2.93874e-39]) *).
Proof.
 intros h0.
 assert (h1 := l40 h0).
 assert (h2 := l69 h0).
 apply t56. exact h1. exact h2.
Qed.
Lemma l98 : s1 -> p16 (* BND(s4, [-1.17549e-38, 1.17549e-38]) *).
Proof.
 intros h0.
 assert (h1 := l23 h0).
 exact (proj2 h1).
Qed.
Lemma t57 : p66 -> p16 -> p65.
Proof.
 intros h0 h1.
 refine (add r43 _s4 i32 i4 i31 h0 h1 _) ; finalize.
Qed.
Lemma l67 : s1 -> p65 (* BND(x / 4 * (g5 - G5 + g5 * ((1 + k4) * (1 + m4a) * (1 + m4b) - 1)) + s4, [-1.17549e-38, 1.46937e-38]) *).
Proof.
 intros h0.
 assert (h1 := l68 h0).
 assert (h2 := l98 h0).
 apply t57. exact h1. exact h2.
Qed.
Definition i51 := makepairF f5 f5.
Notation p95 := (REL r22 r42 i51). (* REL(g4 - G4, x / 4 * (g5 - G5 + g5 * ((1 + k4) * (1 + m4a) * (1 + m4b) - 1)) + s4, [0, 0]) *)
Notation p96 := (r22 = r42). (* EQL(g4 - G4, x / 4 * (g5 - G5 + g5 * ((1 + k4) * (1 + m4a) * (1 + m4b) - 1)) + s4) *)
Lemma t58 : p96.
Proof.
 refine (b2) ; finalize.
Qed.
Lemma l100 : s1 -> p96 (* EQL(g4 - G4, x / 4 * (g5 - G5 + g5 * ((1 + k4) * (1 + m4a) * (1 + m4b) - 1)) + s4) *).
Proof.
 intros h0.
 apply t58.
Qed.
Notation p97 := (REL r42 r42 i51). (* REL(x / 4 * (g5 - G5 + g5 * ((1 + k4) * (1 + m4a) * (1 + m4b) - 1)) + s4, x / 4 * (g5 - G5 + g5 * ((1 + k4) * (1 + m4a) * (1 + m4b) - 1)) + s4, [0, 0]) *)
Lemma t59 : p97.
Proof.
 refine (rel_refl r42 i51 _) ; finalize.
Qed.
Lemma l101 : s1 -> p97 (* REL(x / 4 * (g5 - G5 + g5 * ((1 + k4) * (1 + m4a) * (1 + m4b) - 1)) + s4, x / 4 * (g5 - G5 + g5 * ((1 + k4) * (1 + m4a) * (1 + m4b) - 1)) + s4, [0, 0]) *).
Proof.
 intros h0.
 apply t59.
Qed.
Lemma t60 : p96 -> p97 -> p95.
Proof.
 intros h0 h1.
 refine (rel_rewrite_1 r22 r42 r42 i51 h0 h1) ; finalize.
Qed.
Lemma l99 : s1 -> p95 (* REL(g4 - G4, x / 4 * (g5 - G5 + g5 * ((1 + k4) * (1 + m4a) * (1 + m4b) - 1)) + s4, [0, 0]) *).
Proof.
 intros h0.
 assert (h1 := l100 h0).
 assert (h2 := l101 h0).
 apply t60. exact h1. exact h2.
Qed.
Lemma t61 : p65 -> p95 -> p64.
Proof.
 intros h0 h1.
 refine (bnd_of_bnd_rel_o r22 r42 i31 i51 i31 h0 h1 _) ; finalize.
Qed.
Lemma l66 : s1 -> p64 (* BND(g4 - G4, [-1.17549e-38, 1.46937e-38]) *).
Proof.
 intros h0.
 assert (h1 := l67 h0).
 assert (h2 := l99 h0).
 apply t61. exact h1. exact h2.
Qed.
Definition f65 := Float2 (-169617318258217005023061483679195704421931852947269479255703167285659592295) (-372).
Definition i52 := makepairF f65 f53.
Notation p98 := (BND r72 i52). (* BND(g4 * ((1 + k3) * (1 + m3a) * (1 + m3b) - 1), [-1.76324e-38, 8.81621e-39]) *)
Definition f66 := Float2 (1809251394754314720245989159244754180511240255406296319123096170014252728321) (-250).
Definition i53 := makepairF f14 f66.
Notation p99 := (BND _g4 i53). (* BND(g4, [0.5, 1]) *)
Definition f67 := Float2 (1809251394754314720245989159244754180489972607473737665156635257049767215105) (-250).
Definition i54 := makepairF f55 f67.
Notation p100 := (BND r24 i54). (* BND(1 + x * (1 / 4 * (1 + k4)) * (1 + m4a) * g5 * (1 + m4b), [0.75, 1]) *)
Definition f68 := Float2 (421249166752692518484005620282629097073103852040110506926124564481) (-250).
Definition i55 := makepairF f20 f68.
Notation p101 := (BND r25 i55). (* BND(x * (1 / 4 * (1 + k4)) * (1 + m4a) * g5 * (1 + m4b), [-0.25, 2.32831e-10]) *)
Notation p102 := (BND r26 i55). (* BND(x * (1 / 4 * (1 + k4)) * (1 + m4a) * g5, [-0.25, 2.32831e-10]) *)
Definition f69 := Float2 (-1) (-3).
Definition f70 := Float2 (170141183460469231731687303715884105729) (-159).
Definition i56 := makepairF f69 f70.
Notation p103 := (BND r27 i56). (* BND(x * (1 / 4 * (1 + k4)) * (1 + m4a), [-0.125, 2.32831e-10]) *)
Notation p104 := (BND r28 i56). (* BND(x * (1 / 4 * (1 + k4)), [-0.125, 2.32831e-10]) *)
Definition f71 := Float2 (170141183460469231731687303715884105729) (-129).
Definition i57 := makepairF f58 f71.
Notation p105 := (BND r29 i57). (* BND(1 / 4 * (1 + k4), [0.125, 0.25]) *)
Definition i58 := makepairF f15 f15.
Notation p106 := (BND r30 i58). (* BND(1 / 4, [0.25, 0.25]) *)
Lemma t62 : p30 -> p40 -> p106.
Proof.
 intros h0 h1.
 refine (div_pp r4 r31 i9 i16 i58 h0 h1 _) ; finalize.
Qed.
Lemma l110 : s1 -> p106 (* BND(1 / 4, [0.25, 0.25]) *).
Proof.
 intros h0.
 assert (h1 := l31 h0).
 assert (h2 := l41 h0).
 apply t62. exact h1. exact h2.
Qed.
Definition i59 := makepairF f14 f29.
Notation p107 := (BND r32 i59). (* BND(1 + k4, [0.5, 1]) *)
Lemma t63 : p106 -> p107 -> p105.
Proof.
 intros h0 h1.
 refine (mul_pp r30 r32 i58 i59 i57 h0 h1 _) ; finalize.
Qed.
Lemma l109 : s1 -> p105 (* BND(1 / 4 * (1 + k4), [0.125, 0.25]) *).
Proof.
 intros h0.
 assert (h1 := l110 h0).
 assert (h2 := l92 h0).
 apply t63. exact h1. refine (subset r32 i25 i59 h2 _) ; finalize.
Qed.
Definition i60 := makepairF f20 f2.
Notation p108 := (BND _x i60). (* BND(x, [-0.25, 9.31323e-10]) *)
Lemma t64 : p108 -> p105 -> p104.
Proof.
 intros h0 h1.
 refine (mul_op _x r29 i60 i57 i56 h0 h1 _) ; finalize.
Qed.
Lemma l108 : s1 -> p104 (* BND(x * (1 / 4 * (1 + k4)), [-0.125, 2.32831e-10]) *).
Proof.
 intros h0.
 assert (h1 := l35 h0).
 assert (h2 := l109 h0).
 apply t64. refine (subset _x i1 i60 h1 _) ; finalize. exact h2.
Qed.
Notation p109 := (BND r34 i47). (* BND(1 + m4a, [0.5, 1]) *)
Lemma t65 : p104 -> p109 -> p103.
Proof.
 intros h0 h1.
 refine (mul_op r28 r34 i56 i47 i56 h0 h1 _) ; finalize.
Qed.
Lemma l107 : s1 -> p103 (* BND(x * (1 / 4 * (1 + k4)) * (1 + m4a), [-0.125, 2.32831e-10]) *).
Proof.
 intros h0.
 assert (h1 := l108 h0).
 assert (h2 := l94 h0).
 apply t65. exact h1. refine (subset r34 i24 i47 h2 _) ; finalize.
Qed.
Definition f72 := Float2 (210624583376346259242002810141314548535313985980539288887241788621) (-217).
Definition i61 := makepairF f14 f72.
Notation p110 := (BND _g5 i61). (* BND(g5, [0.5, 1]) *)
Lemma t66 : p103 -> p110 -> p102.
Proof.
 intros h0 h1.
 refine (mul_op r27 _g5 i56 i61 i55 h0 h1 _) ; finalize.
Qed.
Lemma l106 : s1 -> p102 (* BND(x * (1 / 4 * (1 + k4)) * (1 + m4a) * g5, [-0.25, 2.32831e-10]) *).
Proof.
 intros h0.
 assert (h1 := l107 h0).
 assert (h2 := l83 h0).
 apply t66. exact h1. refine (subset _g5 i40 i61 h2 _) ; finalize.
Qed.
Notation p111 := (BND r36 i47). (* BND(1 + m4b, [0.5, 1]) *)
Lemma t67 : p102 -> p111 -> p101.
Proof.
 intros h0 h1.
 refine (mul_op r26 r36 i55 i47 i55 h0 h1 _) ; finalize.
Qed.
Lemma l105 : s1 -> p101 (* BND(x * (1 / 4 * (1 + k4)) * (1 + m4a) * g5 * (1 + m4b), [-0.25, 2.32831e-10]) *).
Proof.
 intros h0.
 assert (h1 := l106 h0).
 assert (h2 := l96 h0).
 apply t67. exact h1. refine (subset r36 i24 i47 h2 _) ; finalize.
Qed.
Lemma t68 : p30 -> p101 -> p100.
Proof.
 intros h0 h1.
 refine (add r4 r25 i9 i55 i54 h0 h1 _) ; finalize.
Qed.
Lemma l104 : s1 -> p100 (* BND(1 + x * (1 / 4 * (1 + k4)) * (1 + m4a) * g5 * (1 + m4b), [0.75, 1]) *).
Proof.
 intros h0.
 assert (h1 := l31 h0).
 assert (h2 := l105 h0).
 apply t68. exact h1. exact h2.
Qed.
Notation p112 := (BND _s4 i48). (* BND(s4, [-0.25, 1.17549e-38]) *)
Lemma t69 : p100 -> p112 -> p99.
Proof.
 intros h0 h1.
 refine (add r24 _s4 i54 i48 i53 h0 h1 _) ; finalize.
Qed.
Lemma l103 : s1 -> p99 (* BND(g4, [0.5, 1]) *).
Proof.
 intros h0.
 assert (h1 := l104 h0).
 assert (h2 := l98 h0).
 apply t69. exact h1. refine (subset _s4 i4 i48 h2 _) ; finalize.
Qed.
Definition f73 := Float2 (-339234636437449791279993120142640355036883066206441466149992680057762480129) (-373).
Definition i62 := makepairF f73 f4.
Notation p113 := (BND r73 i62). (* BND((1 + k3) * (1 + m3a) * (1 + m3b) - 1, [-1.76324e-38, 5.87747e-39]) *)
Definition f74 := Float2 (19239260838083241802870625048898248927922356804219506589554134518649215978701989302648180728618032535179848843263) (-373).
Definition i63 := makepairF f74 f29.
Notation p114 := (BND r74 i63). (* BND((1 + k3) * (1 + m3a) * (1 + m3b), [1, 1]) *)
Notation p115 := (BND r75 i23). (* BND((1 + k3) * (1 + m3a), [1, 1]) *)
Notation p116 := (BND r59 i25). (* BND(1 + k3, [1, 1]) *)
Lemma l115 : s1 -> p4 (* BND(k3, [-5.87747e-39, 5.87747e-39]) *).
Proof.
 intros h0.
 assert (h1 := l11 h0).
 exact (proj2 h1).
Qed.
Lemma t70 : p30 -> p4 -> p116.
Proof.
 intros h0 h1.
 refine (add r4 _k3 i9 i2 i25 h0 h1 _) ; finalize.
Qed.
Lemma l114 : s1 -> p116 (* BND(1 + k3, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l31 h0).
 assert (h2 := l115 h0).
 apply t70. exact h1. exact h2.
Qed.
Notation p117 := (BND r61 i24). (* BND(1 + m3a, [1, 1]) *)
Lemma l117 : s1 -> p10 (* BND(m3a, [-5.87747e-39, 0]) *).
Proof.
 intros h0.
 assert (h1 := l17 h0).
 exact (proj2 h1).
Qed.
Lemma t71 : p30 -> p10 -> p117.
Proof.
 intros h0 h1.
 refine (add r4 _m3a i9 i3 i24 h0 h1 _) ; finalize.
Qed.
Lemma l116 : s1 -> p117 (* BND(1 + m3a, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l31 h0).
 assert (h2 := l117 h0).
 apply t71. exact h1. exact h2.
Qed.
Lemma t72 : p116 -> p117 -> p115.
Proof.
 intros h0 h1.
 refine (mul_pp r59 r61 i25 i24 i23 h0 h1 _) ; finalize.
Qed.
Lemma l113 : s1 -> p115 (* BND((1 + k3) * (1 + m3a), [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l114 h0).
 assert (h2 := l116 h0).
 apply t72. exact h1. exact h2.
Qed.
Notation p118 := (BND r63 i24). (* BND(1 + m3b, [1, 1]) *)
Lemma l119 : s1 -> p11 (* BND(m3b, [-5.87747e-39, 0]) *).
Proof.
 intros h0.
 assert (h1 := l18 h0).
 exact (proj2 h1).
Qed.
Lemma t73 : p30 -> p11 -> p118.
Proof.
 intros h0 h1.
 refine (add r4 _m3b i9 i3 i24 h0 h1 _) ; finalize.
Qed.
Lemma l118 : s1 -> p118 (* BND(1 + m3b, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l31 h0).
 assert (h2 := l119 h0).
 apply t73. exact h1. exact h2.
Qed.
Lemma t74 : p115 -> p118 -> p114.
Proof.
 intros h0 h1.
 refine (mul_pp r75 r63 i23 i24 i63 h0 h1 _) ; finalize.
Qed.
Lemma l112 : s1 -> p114 (* BND((1 + k3) * (1 + m3a) * (1 + m3b), [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l113 h0).
 assert (h2 := l118 h0).
 apply t74. exact h1. exact h2.
Qed.
Lemma t75 : p114 -> p30 -> p113.
Proof.
 intros h0 h1.
 refine (sub r74 r4 i63 i9 i62 h0 h1 _) ; finalize.
Qed.
Lemma l111 : s1 -> p113 (* BND((1 + k3) * (1 + m3a) * (1 + m3b) - 1, [-1.76324e-38, 5.87747e-39]) *).
Proof.
 intros h0.
 assert (h1 := l112 h0).
 assert (h2 := l31 h0).
 apply t75. exact h1. exact h2.
Qed.
Lemma t76 : p99 -> p113 -> p98.
Proof.
 intros h0 h1.
 refine (mul_po _g4 r73 i53 i62 i52 h0 h1 _) ; finalize.
Qed.
Lemma l102 : s1 -> p98 (* BND(g4 * ((1 + k3) * (1 + m3a) * (1 + m3b) - 1), [-1.76324e-38, 8.81621e-39]) *).
Proof.
 intros h0.
 assert (h1 := l103 h0).
 assert (h2 := l111 h0).
 apply t76. exact h1. exact h2.
Qed.
Lemma t77 : p64 -> p98 -> p63.
Proof.
 intros h0 h1.
 refine (add r22 r72 i31 i52 i30 h0 h1 _) ; finalize.
Qed.
Lemma l65 : s1 -> p63 (* BND(g4 - G4 + g4 * ((1 + k3) * (1 + m3a) * (1 + m3b) - 1), [-2.93874e-38, 2.35099e-38]) *).
Proof.
 intros h0.
 assert (h1 := l66 h0).
 assert (h2 := l102 h0).
 apply t77. exact h1. exact h2.
Qed.
Definition f75 := Float2 (-18846368690969432848888506674591130835493161566673268886630466147121277611) (-275).
Definition i64 := makepairF f75 f17.
Notation p119 := (BND r68 i64). (* BND(x / 3, [-3.10441e-10, 3.10441e-10]) *)
Lemma t78 : p119 -> p63 -> p62.
Proof.
 intros h0 h1.
 refine (mul_oo r68 r71 i64 i30 i29 h0 h1 _) ; finalize.
Qed.
Lemma l64 : s1 -> p62 (* BND(x / 3 * (g4 - G4 + g4 * ((1 + k3) * (1 + m3a) * (1 + m3b) - 1)), [-9.12304e-48, 9.12304e-48]) *).
Proof.
 intros h0.
 assert (h1 := l34 h0).
 assert (h2 := l65 h0).
 apply t78. refine (subset r68 i12 i64 h1 _) ; finalize. exact h2.
Qed.
Lemma l120 : s1 -> p17 (* BND(s3, [-1.17549e-38, 1.17549e-38]) *).
Proof.
 intros h0.
 assert (h1 := l24 h0).
 exact (proj2 h1).
Qed.
Lemma t79 : p62 -> p17 -> p61.
Proof.
 intros h0 h1.
 refine (add r70 _s3 i29 i4 i28 h0 h1 _) ; finalize.
Qed.
Lemma l63 : s1 -> p61 (* BND(x / 3 * (g4 - G4 + g4 * ((1 + k3) * (1 + m3a) * (1 + m3b) - 1)) + s3, [-1.17549e-38, 1.17549e-38]) *).
Proof.
 intros h0.
 assert (h1 := l64 h0).
 assert (h2 := l120 h0).
 apply t79. exact h1. exact h2.
Qed.
Notation p120 := (REL r49 r69 i51). (* REL(g3 - G3, x / 3 * (g4 - G4 + g4 * ((1 + k3) * (1 + m3a) * (1 + m3b) - 1)) + s3, [0, 0]) *)
Notation p121 := (r49 = r69). (* EQL(g3 - G3, x / 3 * (g4 - G4 + g4 * ((1 + k3) * (1 + m3a) * (1 + m3b) - 1)) + s3) *)
Lemma t80 : p121.
Proof.
 refine (b3) ; finalize.
Qed.
Lemma l122 : s1 -> p121 (* EQL(g3 - G3, x / 3 * (g4 - G4 + g4 * ((1 + k3) * (1 + m3a) * (1 + m3b) - 1)) + s3) *).
Proof.
 intros h0.
 apply t80.
Qed.
Notation p122 := (REL r69 r69 i51). (* REL(x / 3 * (g4 - G4 + g4 * ((1 + k3) * (1 + m3a) * (1 + m3b) - 1)) + s3, x / 3 * (g4 - G4 + g4 * ((1 + k3) * (1 + m3a) * (1 + m3b) - 1)) + s3, [0, 0]) *)
Lemma t81 : p122.
Proof.
 refine (rel_refl r69 i51 _) ; finalize.
Qed.
Lemma l123 : s1 -> p122 (* REL(x / 3 * (g4 - G4 + g4 * ((1 + k3) * (1 + m3a) * (1 + m3b) - 1)) + s3, x / 3 * (g4 - G4 + g4 * ((1 + k3) * (1 + m3a) * (1 + m3b) - 1)) + s3, [0, 0]) *).
Proof.
 intros h0.
 apply t81.
Qed.
Lemma t82 : p121 -> p122 -> p120.
Proof.
 intros h0 h1.
 refine (rel_rewrite_1 r49 r69 r69 i51 h0 h1) ; finalize.
Qed.
Lemma l121 : s1 -> p120 (* REL(g3 - G3, x / 3 * (g4 - G4 + g4 * ((1 + k3) * (1 + m3a) * (1 + m3b) - 1)) + s3, [0, 0]) *).
Proof.
 intros h0.
 assert (h1 := l122 h0).
 assert (h2 := l123 h0).
 apply t82. exact h1. exact h2.
Qed.
Lemma t83 : p61 -> p120 -> p60.
Proof.
 intros h0 h1.
 refine (bnd_of_bnd_rel_o r49 r69 i28 i51 i28 h0 h1 _) ; finalize.
Qed.
Lemma l62 : s1 -> p60 (* BND(g3 - G3, [-1.17549e-38, 1.17549e-38]) *).
Proof.
 intros h0.
 assert (h1 := l63 h0).
 assert (h2 := l121 h0).
 apply t83. exact h1. exact h2.
Qed.
Definition f76 := Float2 (30354201431603832385437869792836289378554512170137739355672537522378709465723638033) (-274).
Definition i65 := makepairF f76 f13.
Notation p123 := (BND _G3 i65). (* BND(G3, [1, 2]) *)
Definition f77 := Float2 (-9423184347678722501281193537733094690051940663887031379791669990607744751) (-274).
Definition i66 := makepairF f77 f12.
Notation p124 := (BND r67 i66). (* BND(x / 3 * G4, [-3.10441e-10, 1]) *)
Definition f78 := Float2 (226156424344289340030748644905594272561246575933288753115000079774585874023) (-247).
Definition i67 := makepairF f14 f78.
Notation p125 := (BND _G4 i67). (* BND(G4, [0.5, 1]) *)
Definition f79 := Float2 (52656145844086564810500702535328637133209526475434486009130542695) (-247).
Definition i68 := makepairF f23 f79.
Notation p126 := (BND r40 i68). (* BND(x / 4 * G5, [-0.5, 2.32831e-10]) *)
Definition f80 := Float2 (52656145844086564810500702535328637133209526475434486009130542695) (-215).
Definition i69 := makepairF f14 f80.
Notation p127 := (BND _G5 i69). (* BND(G5, [0.5, 1]) *)
Definition f81 := Float2 (9807971461541688693493420973761978775159930381975053927) (-215).
Definition i70 := makepairF f23 f81.
Notation p128 := (BND r17 i70). (* BND(x / 5, [-0.5, 1.86265e-10]) *)
Lemma t84 : p30 -> p128 -> p127.
Proof.
 intros h0 h1.
 refine (add r4 r17 i9 i70 i69 h0 h1 _) ; finalize.
Qed.
Lemma l128 : s1 -> p127 (* BND(G5, [0.5, 1]) *).
Proof.
 intros h0.
 assert (h1 := l31 h0).
 assert (h2 := l74 h0).
 apply t84. exact h1. refine (subset r17 i36 i70 h2 _) ; finalize.
Qed.
Definition i71 := makepairF f20 f22.
Notation p129 := (BND r41 i71). (* BND(x / 4, [-0.25, 2.32831e-10]) *)
Lemma t85 : p129 -> p127 -> p126.
Proof.
 intros h0 h1.
 refine (mul_op r41 _G5 i71 i69 i68 h0 h1 _) ; finalize.
Qed.
Lemma l127 : s1 -> p126 (* BND(x / 4 * G5, [-0.5, 2.32831e-10]) *).
Proof.
 intros h0.
 assert (h1 := l40 h0).
 assert (h2 := l128 h0).
 apply t85. refine (subset r41 i15 i71 h1 _) ; finalize. exact h2.
Qed.
Lemma t86 : p30 -> p126 -> p125.
Proof.
 intros h0 h1.
 refine (add r4 r40 i9 i68 i67 h0 h1 _) ; finalize.
Qed.
Lemma l126 : s1 -> p125 (* BND(G4, [0.5, 1]) *).
Proof.
 intros h0.
 assert (h1 := l31 h0).
 assert (h2 := l127 h0).
 apply t86. exact h1. exact h2.
Qed.
Definition i72 := makepairF f16 f14.
Notation p130 := (BND r68 i72). (* BND(x / 3, [-3.10441e-10, 0.5]) *)
Lemma t87 : p130 -> p125 -> p124.
Proof.
 intros h0 h1.
 refine (mul_op r68 _G4 i72 i67 i66 h0 h1 _) ; finalize.
Qed.
Lemma l125 : s1 -> p124 (* BND(x / 3 * G4, [-3.10441e-10, 1]) *).
Proof.
 intros h0.
 assert (h1 := l34 h0).
 assert (h2 := l126 h0).
 apply t87. refine (subset r68 i12 i72 h1 _) ; finalize. exact h2.
Qed.
Lemma t88 : p30 -> p124 -> p123.
Proof.
 intros h0 h1.
 refine (add r4 r67 i9 i66 i65 h0 h1 _) ; finalize.
Qed.
Lemma l124 : s1 -> p123 (* BND(G3, [1, 2]) *).
Proof.
 intros h0.
 assert (h1 := l31 h0).
 assert (h2 := l125 h0).
 apply t88. exact h1. exact h2.
Qed.
Lemma t89 : p60 -> p123 -> p59.
Proof.
 intros h0 h1.
 refine (div_op r49 _G3 i28 i65 i27 h0 h1 _) ; finalize.
Qed.
Lemma l61 : s1 -> p59 (* BND((g3 - G3) / G3, [-1.17549e-38, 1.17549e-38]) *).
Proof.
 intros h0.
 assert (h1 := l62 h0).
 assert (h2 := l124 h0).
 apply t89. exact h1. exact h2.
Qed.
Lemma t90 : p30 -> p59 -> p58.
Proof.
 intros h0 h1.
 refine (add r4 r103 i9 i27 i26 h0 h1 _) ; finalize.
Qed.
Lemma l60 : s1 -> p58 (* BND(1 + (g3 - G3) / G3, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l31 h0).
 assert (h2 := l61 h0).
 apply t90. exact h1. exact h2.
Qed.
Lemma t91 : p51 -> p58 -> p50.
Proof.
 intros h0 h1.
 refine (mul_pp r99 r102 i21 i26 i20 h0 h1 _) ; finalize.
Qed.
Lemma l48 : s1 -> p50 (* BND((1 + m2a) * (1 + k2) * (1 + m2b) * (1 + m2c) * (1 + (g3 - G3) / G3), [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l49 h0).
 assert (h2 := l60 h0).
 apply t91. exact h1. exact h2.
Qed.
Lemma t92 : p50 -> p30 -> p49.
Proof.
 intros h0 h1.
 refine (sub r98 r4 i20 i9 i6 h0 h1 _) ; finalize.
Qed.
Lemma l47 : s1 -> p49 (* BND((1 + m2a) * (1 + k2) * (1 + m2b) * (1 + m2c) * (1 + (g3 - G3) / G3) - 1, [-3.52648e-38, 1.76324e-38]) *).
Proof.
 intros h0.
 assert (h1 := l48 h0).
 assert (h2 := l31 h0).
 apply t92. exact h1. exact h2.
Qed.
Lemma t93 : p20 -> p49 -> p19.
Proof.
 intros h0 h1.
 refine (bnd_rewrite r80 r97 i6 h0 h1) ; finalize.
Qed.
Lemma l3 : s1 -> p19 (* BND((d - D) / D, [-3.52648e-38, 1.76324e-38]) *).
Proof.
 intros h0.
 assert (h1 := l4 h0).
 assert (h2 := l47 h0).
 apply t93. exact h1. exact h2.
Qed.
Lemma l1 : s1 -> False.
Proof.
 intros h0.
 assert (h1 := l2 h0).
 assert (h2 := l3 h0).
 refine (simplify (Tatom false (Abnd 0%nat i5)) Tfalse (Abnd 0%nat i6) (List.cons r80 List.nil) h2 h1 _) ; finalize.
Qed.
End Generated_by_Gappa.
