Require Import Gappa.Gappa_library.
Section Generated_by_Gappa.
Variable _x_ : R.
Notation _x := ((rounding_float rndNE (53)%positive (-1074)%Z) _x_).
Notation r3 := ((_x * _x)%R).
Notation r2 := ((r3 * _x)%R).
Notation _c3 := (float2R (Float2 (6004799503160661) (-55))).
Notation _c4 := (float2R (Float2 (6004799503160665) (-57))).
Notation _c5 := (float2R (Float2 (600479950321527) (-56))).
Notation _c6 := (float2R (Float2 (6405119469017259) (-62))).
Notation _c7 := (float2R (Float2 (114377043920237) (-59))).
Notation _c8 := (float2R (Float2 (1830068419841075) (-66))).
Notation _c9 := (float2R (Float2 (6721293999218467) (-71))).
Notation r23 := ((_x * _c9)%R).
Notation r21 := ((_c8 + r23)%R).
Notation r20 := ((_x * r21)%R).
Notation r18 := ((_c7 + r20)%R).
Notation r17 := ((_x * r18)%R).
Notation r15 := ((_c6 + r17)%R).
Notation r14 := ((_x * r15)%R).
Notation r12 := ((_c5 + r14)%R).
Notation r11 := ((_x * r12)%R).
Notation r9 := ((_c4 + r11)%R).
Notation r8 := ((_x * r9)%R).
Notation _W := ((_c3 + r8)%R).
Notation _T := ((r2 * _W)%R).
Notation _sh := ((rounding_float rndNE (53)%positive (-1074)%Z) r3).
Notation r26 := ((_x * _sh)%R).
Notation _x3 := ((rounding_float rndNE (53)%positive (-1074)%Z) r26).
Notation r50 := ((rounding_float rndNE (53)%positive (-1074)%Z) r23).
Notation r49 := ((_c8 + r50)%R).
Notation _w8 := ((rounding_float rndNE (53)%positive (-1074)%Z) r49).
Notation r47 := ((_x * _w8)%R).
Notation r46 := ((rounding_float rndNE (53)%positive (-1074)%Z) r47).
Notation r45 := ((_c7 + r46)%R).
Notation _w7 := ((rounding_float rndNE (53)%positive (-1074)%Z) r45).
Notation r43 := ((_x * _w7)%R).
Notation r42 := ((rounding_float rndNE (53)%positive (-1074)%Z) r43).
Notation r41 := ((_c6 + r42)%R).
Notation _w6 := ((rounding_float rndNE (53)%positive (-1074)%Z) r41).
Notation r39 := ((_x * _w6)%R).
Notation r38 := ((rounding_float rndNE (53)%positive (-1074)%Z) r39).
Notation r37 := ((_c5 + r38)%R).
Notation _w5 := ((rounding_float rndNE (53)%positive (-1074)%Z) r37).
Notation r35 := ((_x * _w5)%R).
Notation r34 := ((rounding_float rndNE (53)%positive (-1074)%Z) r35).
Notation r33 := ((_c4 + r34)%R).
Notation _w4 := ((rounding_float rndNE (53)%positive (-1074)%Z) r33).
Notation r31 := ((_x * _w4)%R).
Notation r30 := ((rounding_float rndNE (53)%positive (-1074)%Z) r31).
Notation r29 := ((_c3 + r30)%R).
Notation _w := ((rounding_float rndNE (53)%positive (-1074)%Z) r29).
Notation r54 := ((_x3 * _w)%R).
Notation _t := ((rounding_float rndNE (53)%positive (-1074)%Z) r54).
Notation r52 := ((_t - _T)%R).
Notation r51 := ((r52 / _T)%R).
Notation r59 := (Float1 (1)).
Notation r61 := ((_x3 - r2)%R).
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
Hypothesis a1 : (_T <> 0)%R -> (_x <> 0)%R -> (_W <> 0)%R -> (_x3 <> 0)%R -> (_w <> 0)%R -> r51 = r55.
Lemma b1 : NZR _T -> NZR _x -> NZR _W -> NZR _x3 -> NZR _w -> r51 = r55.
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
Notation r75 := ((_x3 - r26)%R).
Notation r74 := ((r75 / r26)%R).
Notation r73 := ((r59 + r74)%R).
Notation r69 := ((r70 * r73)%R).
Notation r68 := ((r69 - r59)%R).
Hypothesis a2 : (_x <> 0)%R -> (_sh <> 0)%R -> r60 = r68.
Lemma b2 : NZR _x -> NZR _sh -> r60 = r68.
 intros h0 h1.
 apply a2.
 exact h0.
 exact h1.
Qed.
Notation r76 := ((Rabs _x)%R).
Definition f1 := Float2 (1) (-54).
Definition f2 := Float2 (322782267660814808470425758868045285495962955985970070793237551831323569011153956065183521018158540984620470857862225771) (-402).
Definition i1 := makepairF f1 f2.
Notation p1 := (BND r76 i1). (* BND(|x|, [5.55112e-17, 0.0312501]) *)
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
Definition f5 := Float2 (-2432380740175760339061114075950902537455991489298996965787973476289419816047625167182891013419856487578542451689245189483) (-451).
Definition f6 := Float2 (2432380740175761100580136540637829334919462772583684218606755989430991507594319988791494817659842366647158557294017774603) (-451).
Definition i3 := makepairF f5 f6.
Notation p3 := (BND r51 i3). (* BND((t - T) / T, [-4.18315e-16, 4.18315e-16]) *)
Notation p4 := (NZR _T). (* NZR(T) *)
Notation p5 := (NZR r2). (* NZR(x * x * x) *)
Notation p6 := (NZR r3). (* NZR(x * x) *)
Definition f7 := Float2 (1) (-108).
Definition f8 := Float2 (1) (0).
Definition i4 := makepairF f7 f8.
Notation p7 := (ABS r3 i4). (* ABS(x * x, [3.08149e-33, 1]) *)
Definition f9 := Float2 (80695566915203702117606439717011321373990738996492517698309387957830892252788489016295880254539635246155117714465556443) (-400).
Definition i5 := makepairF f1 f9.
Notation p8 := (ABS _x i5). (* ABS(x, [5.55112e-17, 0.0312501]) *)
Lemma l9 : s1 -> p1 (* BND(|x|, [5.55112e-17, 0.0312501]) *).
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj1 h1).
Qed.
Notation p9 := (BND r76 i5). (* BND(|x|, [5.55112e-17, 0.0312501]) *)
Lemma t1 : p9 -> p8.
Proof.
 intros h0.
 refine (abs_of_uabs _x i5 h0 _) ; finalize.
Qed.
Lemma l8 : s1 -> p8 (* ABS(x, [5.55112e-17, 0.0312501]) *).
Proof.
 intros h0.
 assert (h1 := l9 h0).
 apply t1. refine (subset r76 i1 i5 h1 _) ; finalize.
Qed.
Definition i6 := makepairF f1 f8.
Notation p10 := (ABS _x i6). (* ABS(x, [5.55112e-17, 1]) *)
Lemma t2 : p10 -> p10 -> p7.
Proof.
 intros h0 h1.
 refine (mul_aa _x _x i6 i6 i4 h0 h1 _) ; finalize.
Qed.
Lemma l7 : s1 -> p7 (* ABS(x * x, [3.08149e-33, 1]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 apply t2. refine (abs_subset _x i5 i6 h1 _) ; finalize. refine (abs_subset _x i5 i6 h1 _) ; finalize.
Qed.
Lemma t3 : p7 -> p6.
Proof.
 intros h0.
 refine (nzr_of_abs r3 i4 h0 _) ; finalize.
Qed.
Lemma l6 : s1 -> p6 (* NZR(x * x) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 apply t3. exact h1.
Qed.
Notation p11 := (NZR _x). (* NZR(x) *)
Lemma t4 : p10 -> p11.
Proof.
 intros h0.
 refine (nzr_of_abs _x i6 h0 _) ; finalize.
Qed.
Lemma l10 : s1 -> p11 (* NZR(x) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 apply t4. refine (abs_subset _x i5 i6 h1 _) ; finalize.
Qed.
Lemma t5 : p6 -> p11 -> p5.
Proof.
 intros h0 h1.
 refine (mul_nzr r3 _x h0 h1) ; finalize.
Qed.
Lemma l5 : s1 -> p5 (* NZR(x * x * x) *).
Proof.
 intros h0.
 assert (h1 := l6 h0).
 assert (h2 := l10 h0).
 apply t5. exact h1. exact h2.
Qed.
Notation p12 := (NZR _W). (* NZR(W) *)
Definition f10 := Float2 (1) (-3).
Definition i7 := makepairF f10 f8.
Notation p13 := (ABS _W i7). (* ABS(W, [0.125, 1]) *)
Definition f11 := Float2 (6004799503160661) (-55).
Definition i8 := makepairF f11 f11.
Notation p14 := (ABS _c3 i8). (* ABS(c3, [0.166667, 0.166667]) *)
Notation p15 := (BND _c3 i8). (* BND(c3, [0.166667, 0.166667]) *)
Lemma t6 : p15.
Proof.
 refine (constant2 _ i8 _) ; finalize.
Qed.
Lemma l14 : s1 -> p15 (* BND(c3, [0.166667, 0.166667]) *).
Proof.
 intros h0.
 apply t6.
Qed.
Lemma t7 : p15 -> p14.
Proof.
 intros h0.
 refine (abs_of_bnd_p _c3 i8 i8 h0 _) ; finalize.
Qed.
Lemma l13 : s1 -> p14 (* ABS(c3, [0.166667, 0.166667]) *).
Proof.
 intros h0.
 assert (h1 := l14 h0).
 apply t7. exact h1.
Qed.
Definition f12 := Float2 (1) (-59).
Definition f13 := Float2 (1) (-5).
Definition i9 := makepairF f12 f13.
Notation p16 := (ABS r8 i9). (* ABS(x * (c4 + x * (c5 + x * (c6 + x * (c7 + x * (c8 + x * c9))))), [1.73472e-18, 0.03125]) *)
Definition f14 := Float2 (1) (-1).
Definition i10 := makepairF f13 f14.
Notation p17 := (ABS r9 i10). (* ABS(c4 + x * (c5 + x * (c6 + x * (c7 + x * (c8 + x * c9)))), [0.03125, 0.5]) *)
Definition f15 := Float2 (6004799503160665) (-57).
Definition i11 := makepairF f15 f15.
Notation p18 := (ABS _c4 i11). (* ABS(c4, [0.0416667, 0.0416667]) *)
Notation p19 := (BND _c4 i11). (* BND(c4, [0.0416667, 0.0416667]) *)
Lemma t8 : p19.
Proof.
 refine (constant2 _ i11 _) ; finalize.
Qed.
Lemma l18 : s1 -> p19 (* BND(c4, [0.0416667, 0.0416667]) *).
Proof.
 intros h0.
 apply t8.
Qed.
Lemma t9 : p19 -> p18.
Proof.
 intros h0.
 refine (abs_of_bnd_p _c4 i11 i11 h0 _) ; finalize.
Qed.
Lemma l17 : s1 -> p18 (* ABS(c4, [0.0416667, 0.0416667]) *).
Proof.
 intros h0.
 assert (h1 := l18 h0).
 apply t9. exact h1.
Qed.
Definition f16 := Float2 (1) (-61).
Definition f17 := Float2 (1) (-7).
Definition i12 := makepairF f16 f17.
Notation p20 := (ABS r11 i12). (* ABS(x * (c5 + x * (c6 + x * (c7 + x * (c8 + x * c9)))), [4.33681e-19, 0.0078125]) *)
Definition i13 := makepairF f17 f10.
Notation p21 := (ABS r12 i13). (* ABS(c5 + x * (c6 + x * (c7 + x * (c8 + x * c9))), [0.0078125, 0.125]) *)
Definition f18 := Float2 (600479950321527) (-56).
Definition i14 := makepairF f18 f18.
Notation p22 := (ABS _c5 i14). (* ABS(c5, [0.00833333, 0.00833333]) *)
Notation p23 := (BND _c5 i14). (* BND(c5, [0.00833333, 0.00833333]) *)
Lemma t10 : p23.
Proof.
 refine (constant2 _ i14 _) ; finalize.
Qed.
Lemma l22 : s1 -> p23 (* BND(c5, [0.00833333, 0.00833333]) *).
Proof.
 intros h0.
 apply t10.
Qed.
Lemma t11 : p23 -> p22.
Proof.
 intros h0.
 refine (abs_of_bnd_p _c5 i14 i14 h0 _) ; finalize.
Qed.
Lemma l21 : s1 -> p22 (* ABS(c5, [0.00833333, 0.00833333]) *).
Proof.
 intros h0.
 assert (h1 := l22 h0).
 apply t11. exact h1.
Qed.
Definition f19 := Float2 (1) (-64).
Definition f20 := Float2 (1) (-11).
Definition i15 := makepairF f19 f20.
Notation p24 := (ABS r14 i15). (* ABS(x * (c6 + x * (c7 + x * (c8 + x * c9))), [5.42101e-20, 0.000488281]) *)
Definition f21 := Float2 (1) (-10).
Definition i16 := makepairF f21 f17.
Notation p25 := (ABS r15 i16). (* ABS(c6 + x * (c7 + x * (c8 + x * c9)), [0.000976562, 0.0078125]) *)
Definition f22 := Float2 (5) (-12).
Definition f23 := Float2 (3) (-11).
Definition i17 := makepairF f22 f23.
Notation p26 := (ABS _c6 i17). (* ABS(c6, [0.0012207, 0.00146484]) *)
Definition f24 := Float2 (6405119469017259) (-62).
Definition i18 := makepairF f22 f24.
Notation p27 := (BND _c6 i18). (* BND(c6, [0.0012207, 0.00138889]) *)
Lemma t12 : p27.
Proof.
 refine (constant2 _ i18 _) ; finalize.
Qed.
Lemma l26 : s1 -> p27 (* BND(c6, [0.0012207, 0.00138889]) *).
Proof.
 intros h0.
 apply t12.
Qed.
Notation p28 := (BND _c6 i17). (* BND(c6, [0.0012207, 0.00146484]) *)
Lemma t13 : p28 -> p26.
Proof.
 intros h0.
 refine (abs_of_bnd_p _c6 i17 i17 h0 _) ; finalize.
Qed.
Lemma l25 : s1 -> p26 (* ABS(c6, [0.0012207, 0.00146484]) *).
Proof.
 intros h0.
 assert (h1 := l26 h0).
 apply t13. refine (subset _c6 i18 i17 h1 _) ; finalize.
Qed.
Definition f25 := Float2 (1) (-67).
Definition f26 := Float2 (1) (-12).
Definition i19 := makepairF f25 f26.
Notation p29 := (ABS r17 i19). (* ABS(x * (c7 + x * (c8 + x * c9)), [6.77626e-21, 0.000244141]) *)
Definition f27 := Float2 (1) (-13).
Definition f28 := Float2 (1) (-8).
Definition i20 := makepairF f27 f28.
Notation p30 := (ABS r18 i20). (* ABS(c7 + x * (c8 + x * c9), [0.00012207, 0.00390625]) *)
Definition f29 := Float2 (3) (-14).
Definition f30 := Float2 (7) (-15).
Definition i21 := makepairF f29 f30.
Notation p31 := (ABS _c7 i21). (* ABS(c7, [0.000183105, 0.000213623]) *)
Definition f31 := Float2 (114377043920237) (-59).
Definition i22 := makepairF f29 f31.
Notation p32 := (BND _c7 i22). (* BND(c7, [0.000183105, 0.000198413]) *)
Lemma t14 : p32.
Proof.
 refine (constant2 _ i22 _) ; finalize.
Qed.
Lemma l30 : s1 -> p32 (* BND(c7, [0.000183105, 0.000198413]) *).
Proof.
 intros h0.
 apply t14.
Qed.
Notation p33 := (BND _c7 i21). (* BND(c7, [0.000183105, 0.000213623]) *)
Lemma t15 : p33 -> p31.
Proof.
 intros h0.
 refine (abs_of_bnd_p _c7 i21 i21 h0 _) ; finalize.
Qed.
Lemma l29 : s1 -> p31 (* ABS(c7, [0.000183105, 0.000213623]) *).
Proof.
 intros h0.
 assert (h1 := l30 h0).
 apply t15. refine (subset _c7 i22 i21 h1 _) ; finalize.
Qed.
Definition f32 := Float2 (1) (-70).
Definition f33 := Float2 (1) (-14).
Definition i23 := makepairF f32 f33.
Notation p34 := (ABS r20 i23). (* ABS(x * (c8 + x * c9), [8.47033e-22, 6.10352e-05]) *)
Definition f34 := Float2 (1) (-16).
Definition i24 := makepairF f34 f21.
Notation p35 := (ABS r21 i24). (* ABS(c8 + x * c9, [1.52588e-05, 0.000976562]) *)
Definition f35 := Float2 (3) (-17).
Definition f36 := Float2 (7) (-18).
Definition i25 := makepairF f35 f36.
Notation p36 := (ABS _c8 i25). (* ABS(c8, [2.28882e-05, 2.67029e-05]) *)
Definition f37 := Float2 (1830068419841075) (-66).
Definition i26 := makepairF f35 f37.
Notation p37 := (BND _c8 i26). (* BND(c8, [2.28882e-05, 2.48021e-05]) *)
Lemma t16 : p37.
Proof.
 refine (constant2 _ i26 _) ; finalize.
Qed.
Lemma l34 : s1 -> p37 (* BND(c8, [2.28882e-05, 2.48021e-05]) *).
Proof.
 intros h0.
 apply t16.
Qed.
Notation p38 := (BND _c8 i25). (* BND(c8, [2.28882e-05, 2.67029e-05]) *)
Lemma t17 : p38 -> p36.
Proof.
 intros h0.
 refine (abs_of_bnd_p _c8 i25 i25 h0 _) ; finalize.
Qed.
Lemma l33 : s1 -> p36 (* ABS(c8, [2.28882e-05, 2.67029e-05]) *).
Proof.
 intros h0.
 assert (h1 := l34 h0).
 apply t17. refine (subset _c8 i26 i25 h1 _) ; finalize.
Qed.
Definition f38 := Float2 (1) (-73).
Definition f39 := Float2 (1) (-23).
Definition i27 := makepairF f38 f39.
Notation p39 := (ABS r23 i27). (* ABS(x * c9, [1.05879e-22, 1.19209e-07]) *)
Definition f40 := Float2 (1) (-19).
Definition f41 := Float2 (3) (-20).
Definition i28 := makepairF f40 f41.
Notation p40 := (ABS _c9 i28). (* ABS(c9, [1.90735e-06, 2.86102e-06]) *)
Definition f42 := Float2 (6721293999218467) (-71).
Definition i29 := makepairF f40 f42.
Notation p41 := (BND _c9 i29). (* BND(c9, [1.90735e-06, 2.84658e-06]) *)
Lemma t18 : p41.
Proof.
 refine (constant2 _ i29 _) ; finalize.
Qed.
Lemma l37 : s1 -> p41 (* BND(c9, [1.90735e-06, 2.84658e-06]) *).
Proof.
 intros h0.
 apply t18.
Qed.
Notation p42 := (BND _c9 i28). (* BND(c9, [1.90735e-06, 2.86102e-06]) *)
Lemma t19 : p42 -> p40.
Proof.
 intros h0.
 refine (abs_of_bnd_p _c9 i28 i28 h0 _) ; finalize.
Qed.
Lemma l36 : s1 -> p40 (* ABS(c9, [1.90735e-06, 2.86102e-06]) *).
Proof.
 intros h0.
 assert (h1 := l37 h0).
 apply t19. refine (subset _c9 i29 i28 h1 _) ; finalize.
Qed.
Definition f43 := Float2 (5) (-7).
Definition i30 := makepairF f1 f43.
Notation p43 := (ABS _x i30). (* ABS(x, [5.55112e-17, 0.0390625]) *)
Lemma t20 : p43 -> p40 -> p39.
Proof.
 intros h0 h1.
 refine (mul_aa _x _c9 i30 i28 i27 h0 h1 _) ; finalize.
Qed.
Lemma l35 : s1 -> p39 (* ABS(x * c9, [1.05879e-22, 1.19209e-07]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 assert (h2 := l36 h0).
 apply t20. refine (abs_subset _x i5 i30 h1 _) ; finalize. exact h2.
Qed.
Definition i31 := makepairF f35 f20.
Notation p44 := (ABS _c8 i31). (* ABS(c8, [2.28882e-05, 0.000488281]) *)
Definition f44 := Float2 (1) (-17).
Definition i32 := makepairF f38 f44.
Notation p45 := (ABS r23 i32). (* ABS(x * c9, [1.05879e-22, 7.62939e-06]) *)
Lemma t21 : p44 -> p45 -> p35.
Proof.
 intros h0 h1.
 refine (add_aa_p _c8 r23 i31 i32 i24 h0 h1 _) ; finalize.
Qed.
Lemma l32 : s1 -> p35 (* ABS(c8 + x * c9, [1.52588e-05, 0.000976562]) *).
Proof.
 intros h0.
 assert (h1 := l33 h0).
 assert (h2 := l35 h0).
 apply t21. refine (abs_subset _c8 i25 i31 h1 _) ; finalize. refine (abs_subset r23 i27 i32 h2 _) ; finalize.
Qed.
Definition f45 := Float2 (1) (-4).
Definition i33 := makepairF f1 f45.
Notation p46 := (ABS _x i33). (* ABS(x, [5.55112e-17, 0.0625]) *)
Lemma t22 : p46 -> p35 -> p34.
Proof.
 intros h0 h1.
 refine (mul_aa _x r21 i33 i24 i23 h0 h1 _) ; finalize.
Qed.
Lemma l31 : s1 -> p34 (* ABS(x * (c8 + x * c9), [8.47033e-22, 6.10352e-05]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 assert (h2 := l32 h0).
 apply t22. refine (abs_subset _x i5 i33 h1 _) ; finalize. exact h2.
Qed.
Definition f46 := Float2 (1) (-9).
Definition i34 := makepairF f29 f46.
Notation p47 := (ABS _c7 i34). (* ABS(c7, [0.000183105, 0.00195312]) *)
Lemma t23 : p47 -> p34 -> p30.
Proof.
 intros h0 h1.
 refine (add_aa_p _c7 r20 i34 i23 i20 h0 h1 _) ; finalize.
Qed.
Lemma l28 : s1 -> p30 (* ABS(c7 + x * (c8 + x * c9), [0.00012207, 0.00390625]) *).
Proof.
 intros h0.
 assert (h1 := l29 h0).
 assert (h2 := l31 h0).
 apply t23. refine (abs_subset _c7 i21 i34 h1 _) ; finalize. exact h2.
Qed.
Lemma t24 : p46 -> p30 -> p29.
Proof.
 intros h0 h1.
 refine (mul_aa _x r18 i33 i20 i19 h0 h1 _) ; finalize.
Qed.
Lemma l27 : s1 -> p29 (* ABS(x * (c7 + x * (c8 + x * c9)), [6.77626e-21, 0.000244141]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 assert (h2 := l28 h0).
 apply t24. refine (abs_subset _x i5 i33 h1 _) ; finalize. exact h2.
Qed.
Definition i35 := makepairF f22 f28.
Notation p48 := (ABS _c6 i35). (* ABS(c6, [0.0012207, 0.00390625]) *)
Lemma t25 : p48 -> p29 -> p25.
Proof.
 intros h0 h1.
 refine (add_aa_p _c6 r17 i35 i19 i16 h0 h1 _) ; finalize.
Qed.
Lemma l24 : s1 -> p25 (* ABS(c6 + x * (c7 + x * (c8 + x * c9)), [0.000976562, 0.0078125]) *).
Proof.
 intros h0.
 assert (h1 := l25 h0).
 assert (h2 := l27 h0).
 apply t25. refine (abs_subset _c6 i17 i35 h1 _) ; finalize. exact h2.
Qed.
Lemma t26 : p46 -> p25 -> p24.
Proof.
 intros h0 h1.
 refine (mul_aa _x r15 i33 i16 i15 h0 h1 _) ; finalize.
Qed.
Lemma l23 : s1 -> p24 (* ABS(x * (c6 + x * (c7 + x * (c8 + x * c9))), [5.42101e-20, 0.000488281]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 assert (h2 := l24 h0).
 apply t26. refine (abs_subset _x i5 i33 h1 _) ; finalize. exact h2.
Qed.
Definition f47 := Float2 (17) (-11).
Definition i36 := makepairF f47 f45.
Notation p49 := (ABS _c5 i36). (* ABS(c5, [0.00830078, 0.0625]) *)
Lemma t27 : p49 -> p24 -> p21.
Proof.
 intros h0 h1.
 refine (add_aa_p _c5 r14 i36 i15 i13 h0 h1 _) ; finalize.
Qed.
Lemma l20 : s1 -> p21 (* ABS(c5 + x * (c6 + x * (c7 + x * (c8 + x * c9))), [0.0078125, 0.125]) *).
Proof.
 intros h0.
 assert (h1 := l21 h0).
 assert (h2 := l23 h0).
 apply t27. refine (abs_subset _c5 i14 i36 h1 _) ; finalize. exact h2.
Qed.
Lemma t28 : p46 -> p21 -> p20.
Proof.
 intros h0 h1.
 refine (mul_aa _x r12 i33 i13 i12 h0 h1 _) ; finalize.
Qed.
Lemma l19 : s1 -> p20 (* ABS(x * (c5 + x * (c6 + x * (c7 + x * (c8 + x * c9)))), [4.33681e-19, 0.0078125]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 assert (h2 := l20 h0).
 apply t28. refine (abs_subset _x i5 i33 h1 _) ; finalize. exact h2.
Qed.
Definition f48 := Float2 (1) (-2).
Definition i37 := makepairF f43 f48.
Notation p50 := (ABS _c4 i37). (* ABS(c4, [0.0390625, 0.25]) *)
Lemma t29 : p50 -> p20 -> p17.
Proof.
 intros h0 h1.
 refine (add_aa_p _c4 r11 i37 i12 i10 h0 h1 _) ; finalize.
Qed.
Lemma l16 : s1 -> p17 (* ABS(c4 + x * (c5 + x * (c6 + x * (c7 + x * (c8 + x * c9)))), [0.03125, 0.5]) *).
Proof.
 intros h0.
 assert (h1 := l17 h0).
 assert (h2 := l19 h0).
 apply t29. refine (abs_subset _c4 i11 i37 h1 _) ; finalize. exact h2.
Qed.
Lemma t30 : p46 -> p17 -> p16.
Proof.
 intros h0 h1.
 refine (mul_aa _x r9 i33 i10 i9 h0 h1 _) ; finalize.
Qed.
Lemma l15 : s1 -> p16 (* ABS(x * (c4 + x * (c5 + x * (c6 + x * (c7 + x * (c8 + x * c9))))), [1.73472e-18, 0.03125]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 assert (h2 := l16 h0).
 apply t30. refine (abs_subset _x i5 i33 h1 _) ; finalize. exact h2.
Qed.
Definition f49 := Float2 (5) (-5).
Definition i38 := makepairF f49 f14.
Notation p51 := (ABS _c3 i38). (* ABS(c3, [0.15625, 0.5]) *)
Lemma t31 : p51 -> p16 -> p13.
Proof.
 intros h0 h1.
 refine (add_aa_p _c3 r8 i38 i9 i7 h0 h1 _) ; finalize.
Qed.
Lemma l12 : s1 -> p13 (* ABS(W, [0.125, 1]) *).
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
Notation p52 := (REL _t _T i3). (* REL(t, T, [-4.18315e-16, 4.18315e-16]) *)
Definition f50 := Float2 (-1) (-53).
Definition f51 := Float2 (1) (-53).
Definition i39 := makepairF f50 f51.
Notation p53 := (REL _t r54 i39). (* REL(t, x3 * w, [-1.11022e-16, 1.11022e-16]) *)
Notation p54 := (FIX r54 (-646)). (* FIX(x3 * w, -646) *)
Notation p55 := (FIX _x3 (-266)). (* FIX(x3, -266) *)
Notation p56 := (FIX r26 (-266)). (* FIX(x * sh, -266) *)
Notation p57 := (FIX _x (-106)). (* FIX(x, -106) *)
Notation p58 := (FLT _x (53)). (* FLT(x, 53) *)
Lemma t34 : p58.
Proof.
 refine (flt_of_float _ _ _ (53) _ _) ; finalize.
Qed.
Lemma l44 : s1 -> p58 (* FLT(x, 53) *).
Proof.
 intros h0.
 apply t34.
Qed.
Lemma t35 : p58 -> p10 -> p57.
Proof.
 intros h0 h1.
 refine (fix_of_flt_bnd _x i6 (-106) (53) h0 h1 _) ; finalize.
Qed.
Lemma l43 : s1 -> p57 (* FIX(x, -106) *).
Proof.
 intros h0.
 assert (h1 := l44 h0).
 assert (h2 := l8 h0).
 apply t35. exact h1. refine (abs_subset _x i5 i6 h2 _) ; finalize.
Qed.
Notation p59 := (FIX _sh (-160)). (* FIX(sh, -160) *)
Notation p60 := (FLT _sh (53)). (* FLT(sh, 53) *)
Lemma t36 : p60.
Proof.
 refine (flt_of_float _ _ _ (53) _ _) ; finalize.
Qed.
Lemma l46 : s1 -> p60 (* FLT(sh, 53) *).
Proof.
 intros h0.
 apply t36.
Qed.
Notation p61 := (ABS _sh i4). (* ABS(sh, [3.08149e-33, 1]) *)
Notation p62 := (BND _sh i4). (* BND(sh, [3.08149e-33, 1]) *)
Notation p63 := (BND r3 i4). (* BND(x * x, [3.08149e-33, 1]) *)
Lemma t37 : p10 -> p63.
Proof.
 intros h0.
 refine (square _x i6 i4 h0 _) ; finalize.
Qed.
Lemma l49 : s1 -> p63 (* BND(x * x, [3.08149e-33, 1]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 apply t37. refine (abs_subset _x i5 i6 h1 _) ; finalize.
Qed.
Lemma t38 : p63 -> p62.
Proof.
 intros h0.
 refine (float_round_ne _ _ r3 i4 i4 h0 _) ; finalize.
Qed.
Lemma l48 : s1 -> p62 (* BND(sh, [3.08149e-33, 1]) *).
Proof.
 intros h0.
 assert (h1 := l49 h0).
 apply t38. exact h1.
Qed.
Lemma t39 : p62 -> p61.
Proof.
 intros h0.
 refine (abs_of_bnd_p _sh i4 i4 h0 _) ; finalize.
Qed.
Lemma l47 : s1 -> p61 (* ABS(sh, [3.08149e-33, 1]) *).
Proof.
 intros h0.
 assert (h1 := l48 h0).
 apply t39. exact h1.
Qed.
Lemma t40 : p60 -> p61 -> p59.
Proof.
 intros h0 h1.
 refine (fix_of_flt_bnd _sh i4 (-160) (53) h0 h1 _) ; finalize.
Qed.
Lemma l45 : s1 -> p59 (* FIX(sh, -160) *).
Proof.
 intros h0.
 assert (h1 := l46 h0).
 assert (h2 := l47 h0).
 apply t40. exact h1. exact h2.
Qed.
Lemma t41 : p57 -> p59 -> p56.
Proof.
 intros h0 h1.
 refine (mul_fix _x _sh (-106) (-160) (-266) h0 h1 _) ; finalize.
Qed.
Lemma l42 : s1 -> p56 (* FIX(x * sh, -266) *).
Proof.
 intros h0.
 assert (h1 := l43 h0).
 assert (h2 := l45 h0).
 apply t41. exact h1. exact h2.
Qed.
Lemma t42 : p56 -> p55.
Proof.
 intros h0.
 refine (fix_float_of_fix _ _ _ (-266) (-266) r26 h0 _) ; finalize.
Qed.
Lemma l41 : s1 -> p55 (* FIX(x3, -266) *).
Proof.
 intros h0.
 assert (h1 := l42 h0).
 apply t42. exact h1.
Qed.
Notation p64 := (FIX _w (-380)). (* FIX(w, -380) *)
Notation p65 := (FIX r29 (-380)). (* FIX(c3 + float<53,-1074,ne>(x * w4), -380) *)
Notation p66 := (FIX _c3 (-55)). (* FIX(c3, -55) *)
Lemma t43 : p14 -> p66.
Proof.
 intros h0.
 refine (fix_of_singleton_bnd _c3 i8 (-55) h0 _) ; finalize.
Qed.
Lemma l52 : s1 -> p66 (* FIX(c3, -55) *).
Proof.
 intros h0.
 assert (h1 := l13 h0).
 apply t43. exact h1.
Qed.
Notation p67 := (FIX r30 (-380)). (* FIX(float<53,-1074,ne>(x * w4), -380) *)
Notation p68 := (FIX r31 (-380)). (* FIX(x * w4, -380) *)
Notation p69 := (FIX _w4 (-274)). (* FIX(w4, -274) *)
Notation p70 := (FIX r33 (-274)). (* FIX(c4 + float<53,-1074,ne>(x * w5), -274) *)
Notation p71 := (FIX _c4 (-57)). (* FIX(c4, -57) *)
Lemma t44 : p18 -> p71.
Proof.
 intros h0.
 refine (fix_of_singleton_bnd _c4 i11 (-57) h0 _) ; finalize.
Qed.
Lemma l57 : s1 -> p71 (* FIX(c4, -57) *).
Proof.
 intros h0.
 assert (h1 := l17 h0).
 apply t44. exact h1.
Qed.
Notation p72 := (FIX r34 (-274)). (* FIX(float<53,-1074,ne>(x * w5), -274) *)
Notation p73 := (FIX r35 (-274)). (* FIX(x * w5, -274) *)
Notation p74 := (FIX _w5 (-168)). (* FIX(w5, -168) *)
Notation p75 := (FIX r37 (-168)). (* FIX(c5 + float<53,-1074,ne>(x * w6), -168) *)
Notation p76 := (FIX _c5 (-56)). (* FIX(c5, -56) *)
Lemma t45 : p22 -> p76.
Proof.
 intros h0.
 refine (fix_of_singleton_bnd _c5 i14 (-56) h0 _) ; finalize.
Qed.
Lemma l62 : s1 -> p76 (* FIX(c5, -56) *).
Proof.
 intros h0.
 assert (h1 := l21 h0).
 apply t45. exact h1.
Qed.
Notation p77 := (FIX r38 (-168)). (* FIX(float<53,-1074,ne>(x * w6), -168) *)
Notation p78 := (FIX r39 (-168)). (* FIX(x * w6, -168) *)
Notation p79 := (FIX _w6 (-62)). (* FIX(w6, -62) *)
Notation p80 := (FLT _w6 (53)). (* FLT(w6, 53) *)
Lemma t46 : p80.
Proof.
 refine (flt_of_float _ _ _ (53) _ _) ; finalize.
Qed.
Lemma l66 : s1 -> p80 (* FLT(w6, 53) *).
Proof.
 intros h0.
 apply t46.
Qed.
Definition i40 := makepairF f21 f23.
Notation p81 := (ABS _w6 i40). (* ABS(w6, [0.000976562, 0.00146484]) *)
Definition f52 := Float2 (392689570395) (-48).
Definition i41 := makepairF f21 f52.
Notation p82 := (BND _w6 i41). (* BND(w6, [0.000976562, 0.00139511]) *)
Notation p83 := (BND r41 i41). (* BND(c6 + float<53,-1074,ne>(x * w7), [0.000976562, 0.00139511]) *)
Definition f53 := Float2 (-1) (-12).
Definition f54 := Float2 (28033644857) (-52).
Definition i42 := makepairF f53 f54.
Notation p84 := (BND r42 i42). (* BND(float<53,-1074,ne>(x * w7), [-0.000244141, 6.22472e-06]) *)
Notation p85 := (BND r43 i42). (* BND(x * w7, [-0.000244141, 6.22472e-06]) *)
Definition f55 := Float2 (-80695566915203702117606439717011321373990738996492517698309387957830892252788489016295880254539635246155117714465556443) (-400).
Definition i43 := makepairF f55 f9.
Notation p86 := (BND _x i43). (* BND(x, [-0.0312501, 0.0312501]) *)
Lemma t47 : p8 -> p86.
Proof.
 intros h0.
 refine (bnd_of_abs _x i5 i43 h0 _) ; finalize.
Qed.
Lemma l72 : s1 -> p86 (* BND(x, [-0.0312501, 0.0312501]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 apply t47. exact h1.
Qed.
Definition f56 := Float2 (28033555149) (-47).
Definition i44 := makepairF f27 f56.
Notation p87 := (BND _w7 i44). (* BND(w7, [0.00012207, 0.00019919]) *)
Notation p88 := (BND r45 i44). (* BND(c7 + float<53,-1074,ne>(x * w8), [0.00012207, 0.00019919]) *)
Definition f57 := Float2 (-1) (-15).
Definition f58 := Float2 (218944321) (-48).
Definition i45 := makepairF f57 f58.
Notation p89 := (BND r46 i45). (* BND(float<53,-1074,ne>(x * w8), [-3.05176e-05, 7.77846e-07]) *)
Notation p90 := (BND r47 i45). (* BND(x * w8, [-3.05176e-05, 7.77846e-07]) *)
Definition f59 := Float2 (1751548963) (-46).
Definition i46 := makepairF f34 f59.
Notation p91 := (BND _w8 i46). (* BND(w8, [1.52588e-05, 2.4891e-05]) *)
Notation p92 := (BND r49 i46). (* BND(c8 + float<53,-1074,ne>(x * c9), [1.52588e-05, 2.4891e-05]) *)
Definition f60 := Float2 (-1) (-18).
Definition f61 := Float2 (6259713) (-46).
Definition i47 := makepairF f60 f61.
Notation p93 := (BND r50 i47). (* BND(float<53,-1074,ne>(x * c9), [-3.8147e-06, 8.89559e-08]) *)
Definition f62 := Float2 (3505039743177139471407852791466220289126713488482503757604381540784216826977566403293764900931803411832388439) (-384).
Definition i48 := makepairF f60 f62.
Notation p94 := (BND r23 i48). (* BND(x * c9, [-3.8147e-06, 8.89559e-08]) *)
Definition f63 := Float2 (-1) (0).
Definition f64 := Float2 (4697100196220196208311619686254493506508340302184952754661754469726635856366977620421436164443127068583569357) (-366).
Definition i49 := makepairF f63 f64.
Notation p95 := (BND _x i49). (* BND(x, [-1, 0.0312501]) *)
Lemma t48 : p95 -> p41 -> p94.
Proof.
 intros h0 h1.
 refine (mul_op _x _c9 i49 i29 i48 h0 h1 _) ; finalize.
Qed.
Lemma l80 : s1 -> p94 (* BND(x * c9, [-3.8147e-06, 8.89559e-08]) *).
Proof.
 intros h0.
 assert (h1 := l72 h0).
 assert (h2 := l37 h0).
 apply t48. refine (subset _x i43 i49 h1 _) ; finalize. exact h2.
Qed.
Notation p96 := (BND r23 i47). (* BND(x * c9, [-3.8147e-06, 8.89559e-08]) *)
Lemma t49 : p96 -> p93.
Proof.
 intros h0.
 refine (float_round_ne _ _ r23 i47 i47 h0 _) ; finalize.
Qed.
Lemma l79 : s1 -> p93 (* BND(float<53,-1074,ne>(x * c9), [-3.8147e-06, 8.89559e-08]) *).
Proof.
 intros h0.
 assert (h1 := l80 h0).
 apply t49. refine (subset r23 i48 i47 h1 _) ; finalize.
Qed.
Definition f65 := Float2 (872644625) (-45).
Definition i50 := makepairF f35 f65.
Notation p97 := (BND _c8 i50). (* BND(c8, [2.28882e-05, 2.48021e-05]) *)
Definition f66 := Float2 (-1) (-17).
Definition i51 := makepairF f66 f61.
Notation p98 := (BND r50 i51). (* BND(float<53,-1074,ne>(x * c9), [-7.62939e-06, 8.89559e-08]) *)
Lemma t50 : p97 -> p98 -> p92.
Proof.
 intros h0 h1.
 refine (add _c8 r50 i50 i51 i46 h0 h1 _) ; finalize.
Qed.
Lemma l78 : s1 -> p92 (* BND(c8 + float<53,-1074,ne>(x * c9), [1.52588e-05, 2.4891e-05]) *).
Proof.
 intros h0.
 assert (h1 := l34 h0).
 assert (h2 := l79 h0).
 apply t50. refine (subset _c8 i26 i50 h1 _) ; finalize. refine (subset r50 i47 i51 h2 _) ; finalize.
Qed.
Lemma t51 : p92 -> p91.
Proof.
 intros h0.
 refine (float_round_ne _ _ r49 i46 i46 h0 _) ; finalize.
Qed.
Lemma l77 : s1 -> p91 (* BND(w8, [1.52588e-05, 2.4891e-05]) *).
Proof.
 intros h0.
 assert (h1 := l78 h0).
 apply t51. exact h1.
Qed.
Definition f67 := Float2 (268436315) (-33).
Definition i52 := makepairF f63 f67.
Notation p99 := (BND _x i52). (* BND(x, [-1, 0.0312501]) *)
Lemma t52 : p99 -> p91 -> p90.
Proof.
 intros h0 h1.
 refine (mul_op _x _w8 i52 i46 i45 h0 h1 _) ; finalize.
Qed.
Lemma l76 : s1 -> p90 (* BND(x * w8, [-3.05176e-05, 7.77846e-07]) *).
Proof.
 intros h0.
 assert (h1 := l72 h0).
 assert (h2 := l77 h0).
 apply t52. refine (subset _x i43 i52 h1 _) ; finalize. exact h2.
Qed.
Lemma t53 : p90 -> p89.
Proof.
 intros h0.
 refine (float_round_ne _ _ r47 i45 i45 h0 _) ; finalize.
Qed.
Lemma l75 : s1 -> p89 (* BND(float<53,-1074,ne>(x * w8), [-3.05176e-05, 7.77846e-07]) *).
Proof.
 intros h0.
 assert (h1 := l76 h0).
 apply t53. exact h1.
Qed.
Definition f68 := Float2 (55848165977) (-48).
Definition i53 := makepairF f29 f68.
Notation p100 := (BND _c7 i53). (* BND(c7, [0.000183105, 0.000198413]) *)
Definition f69 := Float2 (-1) (-14).
Definition i54 := makepairF f69 f58.
Notation p101 := (BND r46 i54). (* BND(float<53,-1074,ne>(x * w8), [-6.10352e-05, 7.77846e-07]) *)
Lemma t54 : p100 -> p101 -> p88.
Proof.
 intros h0 h1.
 refine (add _c7 r46 i53 i54 i44 h0 h1 _) ; finalize.
Qed.
Lemma l74 : s1 -> p88 (* BND(c7 + float<53,-1074,ne>(x * w8), [0.00012207, 0.00019919]) *).
Proof.
 intros h0.
 assert (h1 := l30 h0).
 assert (h2 := l75 h0).
 apply t54. refine (subset _c7 i22 i53 h1 _) ; finalize. refine (subset r46 i45 i54 h2 _) ; finalize.
Qed.
Lemma t55 : p88 -> p87.
Proof.
 intros h0.
 refine (float_round_ne _ _ r45 i44 i44 h0 _) ; finalize.
Qed.
Lemma l73 : s1 -> p87 (* BND(w7, [0.00012207, 0.00019919]) *).
Proof.
 intros h0.
 assert (h1 := l74 h0).
 apply t55. exact h1.
Qed.
Definition f70 := Float2 (68719696639) (-41).
Definition i55 := makepairF f63 f70.
Notation p102 := (BND _x i55). (* BND(x, [-1, 0.0312501]) *)
Lemma t56 : p102 -> p87 -> p85.
Proof.
 intros h0 h1.
 refine (mul_op _x _w7 i55 i44 i42 h0 h1 _) ; finalize.
Qed.
Lemma l71 : s1 -> p85 (* BND(x * w7, [-0.000244141, 6.22472e-06]) *).
Proof.
 intros h0.
 assert (h1 := l72 h0).
 assert (h2 := l73 h0).
 apply t56. refine (subset _x i43 i55 h1 _) ; finalize. exact h2.
Qed.
Lemma t57 : p85 -> p84.
Proof.
 intros h0.
 refine (float_round_ne _ _ r43 i42 i42 h0 _) ; finalize.
Qed.
Lemma l70 : s1 -> p84 (* BND(float<53,-1074,ne>(x * w7), [-0.000244141, 6.22472e-06]) *).
Proof.
 intros h0.
 assert (h1 := l71 h0).
 apply t57. exact h1.
Qed.
Definition f71 := Float2 (6254999481463) (-52).
Definition i56 := makepairF f22 f71.
Notation p103 := (BND _c6 i56). (* BND(c6, [0.0012207, 0.00138889]) *)
Lemma t58 : p103 -> p84 -> p83.
Proof.
 intros h0 h1.
 refine (add _c6 r42 i56 i42 i41 h0 h1 _) ; finalize.
Qed.
Lemma l69 : s1 -> p83 (* BND(c6 + float<53,-1074,ne>(x * w7), [0.000976562, 0.00139511]) *).
Proof.
 intros h0.
 assert (h1 := l26 h0).
 assert (h2 := l70 h0).
 apply t58. refine (subset _c6 i18 i56 h1 _) ; finalize. exact h2.
Qed.
Lemma t59 : p83 -> p82.
Proof.
 intros h0.
 refine (float_round_ne _ _ r41 i41 i41 h0 _) ; finalize.
Qed.
Lemma l68 : s1 -> p82 (* BND(w6, [0.000976562, 0.00139511]) *).
Proof.
 intros h0.
 assert (h1 := l69 h0).
 apply t59. exact h1.
Qed.
Notation p104 := (BND _w6 i40). (* BND(w6, [0.000976562, 0.00146484]) *)
Lemma t60 : p104 -> p81.
Proof.
 intros h0.
 refine (abs_of_bnd_p _w6 i40 i40 h0 _) ; finalize.
Qed.
Lemma l67 : s1 -> p81 (* ABS(w6, [0.000976562, 0.00146484]) *).
Proof.
 intros h0.
 assert (h1 := l68 h0).
 apply t60. refine (subset _w6 i41 i40 h1 _) ; finalize.
Qed.
Definition i57 := makepairF f21 f8.
Notation p105 := (ABS _w6 i57). (* ABS(w6, [0.000976562, 1]) *)
Lemma t61 : p80 -> p105 -> p79.
Proof.
 intros h0 h1.
 refine (fix_of_flt_bnd _w6 i57 (-62) (53) h0 h1 _) ; finalize.
Qed.
Lemma l65 : s1 -> p79 (* FIX(w6, -62) *).
Proof.
 intros h0.
 assert (h1 := l66 h0).
 assert (h2 := l67 h0).
 apply t61. exact h1. refine (abs_subset _w6 i40 i57 h2 _) ; finalize.
Qed.
Lemma t62 : p57 -> p79 -> p78.
Proof.
 intros h0 h1.
 refine (mul_fix _x _w6 (-106) (-62) (-168) h0 h1 _) ; finalize.
Qed.
Lemma l64 : s1 -> p78 (* FIX(x * w6, -168) *).
Proof.
 intros h0.
 assert (h1 := l43 h0).
 assert (h2 := l65 h0).
 apply t62. exact h1. exact h2.
Qed.
Lemma t63 : p78 -> p77.
Proof.
 intros h0.
 refine (fix_float_of_fix _ _ _ (-168) (-168) r39 h0 _) ; finalize.
Qed.
Lemma l63 : s1 -> p77 (* FIX(float<53,-1074,ne>(x * w6), -168) *).
Proof.
 intros h0.
 assert (h1 := l64 h0).
 apply t63. exact h1.
Qed.
Lemma t64 : p76 -> p77 -> p75.
Proof.
 intros h0 h1.
 refine (add_fix _c5 r38 (-56) (-168) (-168) h0 h1 _) ; finalize.
Qed.
Lemma l61 : s1 -> p75 (* FIX(c5 + float<53,-1074,ne>(x * w6), -168) *).
Proof.
 intros h0.
 assert (h1 := l62 h0).
 assert (h2 := l63 h0).
 apply t64. exact h1. exact h2.
Qed.
Lemma t65 : p75 -> p74.
Proof.
 intros h0.
 refine (fix_float_of_fix _ _ _ (-168) (-168) r37 h0 _) ; finalize.
Qed.
Lemma l60 : s1 -> p74 (* FIX(w5, -168) *).
Proof.
 intros h0.
 assert (h1 := l61 h0).
 apply t65. exact h1.
Qed.
Lemma t66 : p57 -> p74 -> p73.
Proof.
 intros h0 h1.
 refine (mul_fix _x _w5 (-106) (-168) (-274) h0 h1 _) ; finalize.
Qed.
Lemma l59 : s1 -> p73 (* FIX(x * w5, -274) *).
Proof.
 intros h0.
 assert (h1 := l43 h0).
 assert (h2 := l60 h0).
 apply t66. exact h1. exact h2.
Qed.
Lemma t67 : p73 -> p72.
Proof.
 intros h0.
 refine (fix_float_of_fix _ _ _ (-274) (-274) r35 h0 _) ; finalize.
Qed.
Lemma l58 : s1 -> p72 (* FIX(float<53,-1074,ne>(x * w5), -274) *).
Proof.
 intros h0.
 assert (h1 := l59 h0).
 apply t67. exact h1.
Qed.
Lemma t68 : p71 -> p72 -> p70.
Proof.
 intros h0 h1.
 refine (add_fix _c4 r34 (-57) (-274) (-274) h0 h1 _) ; finalize.
Qed.
Lemma l56 : s1 -> p70 (* FIX(c4 + float<53,-1074,ne>(x * w5), -274) *).
Proof.
 intros h0.
 assert (h1 := l57 h0).
 assert (h2 := l58 h0).
 apply t68. exact h1. exact h2.
Qed.
Lemma t69 : p70 -> p69.
Proof.
 intros h0.
 refine (fix_float_of_fix _ _ _ (-274) (-274) r33 h0 _) ; finalize.
Qed.
Lemma l55 : s1 -> p69 (* FIX(w4, -274) *).
Proof.
 intros h0.
 assert (h1 := l56 h0).
 apply t69. exact h1.
Qed.
Lemma t70 : p57 -> p69 -> p68.
Proof.
 intros h0 h1.
 refine (mul_fix _x _w4 (-106) (-274) (-380) h0 h1 _) ; finalize.
Qed.
Lemma l54 : s1 -> p68 (* FIX(x * w4, -380) *).
Proof.
 intros h0.
 assert (h1 := l43 h0).
 assert (h2 := l55 h0).
 apply t70. exact h1. exact h2.
Qed.
Lemma t71 : p68 -> p67.
Proof.
 intros h0.
 refine (fix_float_of_fix _ _ _ (-380) (-380) r31 h0 _) ; finalize.
Qed.
Lemma l53 : s1 -> p67 (* FIX(float<53,-1074,ne>(x * w4), -380) *).
Proof.
 intros h0.
 assert (h1 := l54 h0).
 apply t71. exact h1.
Qed.
Lemma t72 : p66 -> p67 -> p65.
Proof.
 intros h0 h1.
 refine (add_fix _c3 r30 (-55) (-380) (-380) h0 h1 _) ; finalize.
Qed.
Lemma l51 : s1 -> p65 (* FIX(c3 + float<53,-1074,ne>(x * w4), -380) *).
Proof.
 intros h0.
 assert (h1 := l52 h0).
 assert (h2 := l53 h0).
 apply t72. exact h1. exact h2.
Qed.
Lemma t73 : p65 -> p64.
Proof.
 intros h0.
 refine (fix_float_of_fix _ _ _ (-380) (-380) r29 h0 _) ; finalize.
Qed.
Lemma l50 : s1 -> p64 (* FIX(w, -380) *).
Proof.
 intros h0.
 assert (h1 := l51 h0).
 apply t73. exact h1.
Qed.
Lemma t74 : p55 -> p64 -> p54.
Proof.
 intros h0 h1.
 refine (mul_fix _x3 _w (-266) (-380) (-646) h0 h1 _) ; finalize.
Qed.
Lemma l40 : s1 -> p54 (* FIX(x3 * w, -646) *).
Proof.
 intros h0.
 assert (h1 := l41 h0).
 assert (h2 := l50 h0).
 apply t74. exact h1. exact h2.
Qed.
Lemma t75 : p54 -> p53.
Proof.
 intros h0.
 refine (rel_of_fix_float_ne _ _ (-646) r54 i39 h0 _) ; finalize.
Qed.
Lemma l39 : s1 -> p53 (* REL(t, x3 * w, [-1.11022e-16, 1.11022e-16]) *).
Proof.
 intros h0.
 assert (h1 := l40 h0).
 apply t75. exact h1.
Qed.
Definition f72 := Float2 (-1786818270654033390023812773051403220575635504195182234023589271567203986104313504862226656313774648594646685299094236451) (-451).
Definition f73 := Float2 (893409135327016877394739128767891108755462251020752079800471621647131149621330165944340828239874924575710041275979128409) (-450).
Definition i58 := makepairF f72 f73.
Notation p106 := (REL r54 _T i58). (* REL(x3 * w, T, [-3.07293e-16, 3.07293e-16]) *)
Definition f74 := Float2 (-18014398509481983) (-106).
Definition f75 := Float2 (18014398509481985) (-106).
Definition i59 := makepairF f74 f75.
Notation p107 := (REL _x3 r2 i59). (* REL(x3, x * x * x, [-2.22045e-16, 2.22045e-16]) *)
Notation p108 := (BND r60 i59). (* BND((x3 - x * x * x) / (x * x * x), [-2.22045e-16, 2.22045e-16]) *)
Notation p109 := (BND r68 i59). (* BND((1 + (sh - x * x) / (x * x)) * (1 + (x3 - x * sh) / (x * sh)) - 1, [-2.22045e-16, 2.22045e-16]) *)
Definition f76 := Float2 (81129638414606663681390495662081) (-106).
Definition f77 := Float2 (81129638414606699710187514626049) (-106).
Definition i60 := makepairF f76 f77.
Notation p110 := (BND r69 i60). (* BND((1 + (sh - x * x) / (x * x)) * (1 + (x3 - x * sh) / (x * sh)), [1, 1]) *)
Definition f78 := Float2 (9007199254740991) (-53).
Definition f79 := Float2 (9007199254740993) (-53).
Definition i61 := makepairF f78 f79.
Notation p111 := (BND r70 i61). (* BND(1 + (sh - x * x) / (x * x), [1, 1]) *)
Definition i62 := makepairF f8 f8.
Notation p112 := (BND r59 i62). (* BND(1, [1, 1]) *)
Lemma t76 : p112.
Proof.
 refine (constant1 _ i62 _) ; finalize.
Qed.
Lemma l87 : s1 -> p112 (* BND(1, [1, 1]) *).
Proof.
 intros h0.
 apply t76.
Qed.
Notation p113 := (BND r71 i39). (* BND((sh - x * x) / (x * x), [-1.11022e-16, 1.11022e-16]) *)
Notation p114 := (REL _sh r3 i39). (* REL(sh, x * x, [-1.11022e-16, 1.11022e-16]) *)
Notation p115 := (FIX r3 (-212)). (* FIX(x * x, -212) *)
Lemma t77 : p57 -> p57 -> p115.
Proof.
 intros h0 h1.
 refine (mul_fix _x _x (-106) (-106) (-212) h0 h1 _) ; finalize.
Qed.
Lemma l90 : s1 -> p115 (* FIX(x * x, -212) *).
Proof.
 intros h0.
 assert (h1 := l43 h0).
 apply t77. exact h1. exact h1.
Qed.
Lemma t78 : p115 -> p114.
Proof.
 intros h0.
 refine (rel_of_fix_float_ne _ _ (-212) r3 i39 h0 _) ; finalize.
Qed.
Lemma l89 : s1 -> p114 (* REL(sh, x * x, [-1.11022e-16, 1.11022e-16]) *).
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
Lemma l88 : s1 -> p113 (* BND((sh - x * x) / (x * x), [-1.11022e-16, 1.11022e-16]) *).
Proof.
 intros h0.
 assert (h1 := l6 h0).
 assert (h2 := l89 h0).
 apply t79. exact h1. exact h2.
Qed.
Lemma t80 : p112 -> p113 -> p111.
Proof.
 intros h0 h1.
 refine (add r59 r71 i62 i39 i61 h0 h1 _) ; finalize.
Qed.
Lemma l86 : s1 -> p111 (* BND(1 + (sh - x * x) / (x * x), [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l87 h0).
 assert (h2 := l88 h0).
 apply t80. exact h1. exact h2.
Qed.
Notation p116 := (BND r73 i61). (* BND(1 + (x3 - x * sh) / (x * sh), [1, 1]) *)
Notation p117 := (BND r74 i39). (* BND((x3 - x * sh) / (x * sh), [-1.11022e-16, 1.11022e-16]) *)
Notation p118 := (NZR r26). (* NZR(x * sh) *)
Notation p119 := (NZR _sh). (* NZR(sh) *)
Definition f80 := Float2 (-1) (-1).
Definition i63 := makepairF f80 f8.
Notation p120 := (REL _sh r3 i63). (* REL(sh, x * x, [-0.5, 1]) *)
Lemma t81 : p6 -> p120 -> p119.
Proof.
 intros h0 h1.
 refine (nzr_of_nzr_rel _sh r3 i63 h0 h1 _) ; finalize.
Qed.
Lemma l94 : s1 -> p119 (* NZR(sh) *).
Proof.
 intros h0.
 assert (h1 := l6 h0).
 assert (h2 := l89 h0).
 apply t81. exact h1. refine (rel_subset _sh r3 i39 i63 h2 _) ; finalize.
Qed.
Lemma t82 : p11 -> p119 -> p118.
Proof.
 intros h0 h1.
 refine (mul_nzr _x _sh h0 h1) ; finalize.
Qed.
Lemma l93 : s1 -> p118 (* NZR(x * sh) *).
Proof.
 intros h0.
 assert (h1 := l10 h0).
 assert (h2 := l94 h0).
 apply t82. exact h1. exact h2.
Qed.
Notation p121 := (REL _x3 r26 i39). (* REL(x3, x * sh, [-1.11022e-16, 1.11022e-16]) *)
Notation p122 := (FIX r26 (-318)). (* FIX(x * sh, -318) *)
Notation p123 := (FIX _sh (-212)). (* FIX(sh, -212) *)
Lemma t83 : p115 -> p123.
Proof.
 intros h0.
 refine (fix_float_of_fix _ _ _ (-212) (-212) r3 h0 _) ; finalize.
Qed.
Lemma l97 : s1 -> p123 (* FIX(sh, -212) *).
Proof.
 intros h0.
 assert (h1 := l90 h0).
 apply t83. exact h1.
Qed.
Lemma t84 : p57 -> p123 -> p122.
Proof.
 intros h0 h1.
 refine (mul_fix _x _sh (-106) (-212) (-318) h0 h1 _) ; finalize.
Qed.
Lemma l96 : s1 -> p122 (* FIX(x * sh, -318) *).
Proof.
 intros h0.
 assert (h1 := l43 h0).
 assert (h2 := l97 h0).
 apply t84. exact h1. exact h2.
Qed.
Lemma t85 : p122 -> p121.
Proof.
 intros h0.
 refine (rel_of_fix_float_ne _ _ (-318) r26 i39 h0 _) ; finalize.
Qed.
Lemma l95 : s1 -> p121 (* REL(x3, x * sh, [-1.11022e-16, 1.11022e-16]) *).
Proof.
 intros h0.
 assert (h1 := l96 h0).
 apply t85. exact h1.
Qed.
Lemma t86 : p118 -> p121 -> p117.
Proof.
 intros h0 h1.
 refine (bnd_of_nzr_rel _x3 r26 i39 h0 h1) ; finalize.
Qed.
Lemma l92 : s1 -> p117 (* BND((x3 - x * sh) / (x * sh), [-1.11022e-16, 1.11022e-16]) *).
Proof.
 intros h0.
 assert (h1 := l93 h0).
 assert (h2 := l95 h0).
 apply t86. exact h1. exact h2.
Qed.
Lemma t87 : p112 -> p117 -> p116.
Proof.
 intros h0 h1.
 refine (add r59 r74 i62 i39 i61 h0 h1 _) ; finalize.
Qed.
Lemma l91 : s1 -> p116 (* BND(1 + (x3 - x * sh) / (x * sh), [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l87 h0).
 assert (h2 := l92 h0).
 apply t87. exact h1. exact h2.
Qed.
Lemma t88 : p111 -> p116 -> p110.
Proof.
 intros h0 h1.
 refine (mul_pp r70 r73 i61 i61 i60 h0 h1 _) ; finalize.
Qed.
Lemma l85 : s1 -> p110 (* BND((1 + (sh - x * x) / (x * x)) * (1 + (x3 - x * sh) / (x * sh)), [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l86 h0).
 assert (h2 := l91 h0).
 apply t88. exact h1. exact h2.
Qed.
Lemma t89 : p110 -> p112 -> p109.
Proof.
 intros h0 h1.
 refine (sub r69 r59 i60 i62 i59 h0 h1 _) ; finalize.
Qed.
Lemma l84 : s1 -> p109 (* BND((1 + (sh - x * x) / (x * x)) * (1 + (x3 - x * sh) / (x * sh)) - 1, [-2.22045e-16, 2.22045e-16]) *).
Proof.
 intros h0.
 assert (h1 := l85 h0).
 assert (h2 := l87 h0).
 apply t89. exact h1. exact h2.
Qed.
Definition f81 := Float2 (0) (0).
Definition i64 := makepairF f81 f81.
Notation p124 := (REL r60 r68 i64). (* REL((x3 - x * x * x) / (x * x * x), (1 + (sh - x * x) / (x * x)) * (1 + (x3 - x * sh) / (x * sh)) - 1, [0, 0]) *)
Notation p125 := (r60 = r68). (* EQL((x3 - x * x * x) / (x * x * x), (1 + (sh - x * x) / (x * x)) * (1 + (x3 - x * sh) / (x * sh)) - 1) *)
Lemma t90 : p11 -> p119 -> p125.
Proof.
 intros h0 h1.
 refine (b2 h0 h1) ; finalize.
Qed.
Lemma l99 : s1 -> p125 (* EQL((x3 - x * x * x) / (x * x * x), (1 + (sh - x * x) / (x * x)) * (1 + (x3 - x * sh) / (x * sh)) - 1) *).
Proof.
 intros h0.
 assert (h1 := l10 h0).
 assert (h2 := l94 h0).
 apply t90. exact h1. exact h2.
Qed.
Notation p126 := (REL r68 r68 i64). (* REL((1 + (sh - x * x) / (x * x)) * (1 + (x3 - x * sh) / (x * sh)) - 1, (1 + (sh - x * x) / (x * x)) * (1 + (x3 - x * sh) / (x * sh)) - 1, [0, 0]) *)
Lemma t91 : p126.
Proof.
 refine (rel_refl r68 i64 _) ; finalize.
Qed.
Lemma l100 : s1 -> p126 (* REL((1 + (sh - x * x) / (x * x)) * (1 + (x3 - x * sh) / (x * sh)) - 1, (1 + (sh - x * x) / (x * x)) * (1 + (x3 - x * sh) / (x * sh)) - 1, [0, 0]) *).
Proof.
 intros h0.
 apply t91.
Qed.
Lemma t92 : p125 -> p126 -> p124.
Proof.
 intros h0 h1.
 refine (rel_rewrite_1 r60 r68 r68 i64 h0 h1) ; finalize.
Qed.
Lemma l98 : s1 -> p124 (* REL((x3 - x * x * x) / (x * x * x), (1 + (sh - x * x) / (x * x)) * (1 + (x3 - x * sh) / (x * sh)) - 1, [0, 0]) *).
Proof.
 intros h0.
 assert (h1 := l99 h0).
 assert (h2 := l100 h0).
 apply t92. exact h1. exact h2.
Qed.
Lemma t93 : p109 -> p124 -> p108.
Proof.
 intros h0 h1.
 refine (bnd_of_bnd_rel_o r60 r68 i59 i64 i59 h0 h1 _) ; finalize.
Qed.
Lemma l83 : s1 -> p108 (* BND((x3 - x * x * x) / (x * x * x), [-2.22045e-16, 2.22045e-16]) *).
Proof.
 intros h0.
 assert (h1 := l84 h0).
 assert (h2 := l98 h0).
 apply t93. exact h1. exact h2.
Qed.
Lemma t94 : p5 -> p108 -> p107.
Proof.
 intros h0 h1.
 refine (rel_of_nzr_bnd _x3 r2 i59 h0 h1) ; finalize.
Qed.
Lemma l82 : s1 -> p107 (* REL(x3, x * x * x, [-2.22045e-16, 2.22045e-16]) *).
Proof.
 intros h0.
 assert (h1 := l5 h0).
 assert (h2 := l83 h0).
 apply t94. exact h1. exact h2.
Qed.
Definition f82 := Float2 (-495693331610579276933714918183234617320136884810944030021338675895393148837989626872996337321337512011855700542981957321) (-451).
Definition f83 := Float2 (495693331610579278223656940400926440227979180924597736887153488121897355913497139944939663830922878731316039512864038407) (-451).
Definition i65 := makepairF f82 f83.
Notation p127 := (REL _w _W i65). (* REL(w, W, [-8.52482e-17, 8.52482e-17]) *)
Definition f84 := Float2 (-61001047898294428660263603976012825979216440956379580651631129394123728073581001837450114577543881650659813740497374413) (-448).
Definition f85 := Float2 (61001047898294428660263603976012825979216440956379580651631129394123728073581001837450114577543881650659813740497374413) (-448).
Definition i66 := makepairF f84 f85.
Notation p128 := (REL _w r29 i66). (* REL(w, c3 + float<53,-1074,ne>(x * w4), [-8.39265e-17, 8.39265e-17]) *)
Notation p129 := (NZR r29). (* NZR(c3 + float<53,-1074,ne>(x * w4)) *)
Definition i67 := makepairF f10 f48.
Notation p130 := (ABS r29 i67). (* ABS(c3 + float<53,-1074,ne>(x * w4), [0.125, 0.25]) *)
Definition i68 := makepairF f81 f13.
Notation p131 := (ABS r30 i68). (* ABS(float<53,-1074,ne>(x * w4), [0, 0.03125]) *)
Definition f86 := Float2 (-6042545302276649) (-62).
Definition i69 := makepairF f86 f13.
Notation p132 := (BND r30 i69). (* BND(float<53,-1074,ne>(x * w4), [-0.00131027, 0.03125]) *)
Notation p133 := (BND r31 i69). (* BND(x * w4, [-0.00131027, 0.03125]) *)
Definition f87 := Float2 (6042525966193557) (-57).
Definition i70 := makepairF f13 f87.
Notation p134 := (BND _w4 i70). (* BND(w4, [0.03125, 0.0419284]) *)
Notation p135 := (BND r33 i70). (* BND(c4 + float<53,-1074,ne>(x * w5), [0.03125, 0.0419284]) *)
Definition f88 := Float2 (-1) (-7).
Definition f89 := Float2 (9431615758223) (-55).
Definition i71 := makepairF f88 f89.
Notation p136 := (BND r34 i71). (* BND(float<53,-1074,ne>(x * w5), [-0.0078125, 0.00026178]) *)
Notation p137 := (BND r35 i71). (* BND(x * w5, [-0.0078125, 0.00026178]) *)
Definition f90 := Float2 (75452684617193) (-53).
Definition i72 := makepairF f17 f90.
Notation p138 := (BND _w5 i72). (* BND(w5, [0.0078125, 0.00837693]) *)
Notation p139 := (BND r37 i72). (* BND(c5 + float<53,-1074,ne>(x * w6), [0.0078125, 0.00837693]) *)
Definition f91 := Float2 (-1) (-11).
Definition f92 := Float2 (196345413501) (-52).
Definition i73 := makepairF f91 f92.
Notation p140 := (BND r38 i73). (* BND(float<53,-1074,ne>(x * w6), [-0.000488281, 4.35974e-05]) *)
Notation p141 := (BND r39 i73). (* BND(x * w6, [-0.000488281, 4.35974e-05]) *)
Definition f93 := Float2 (-1) (-2).
Definition f94 := Float2 (549757573107) (-44).
Definition i74 := makepairF f93 f94.
Notation p142 := (BND _x i74). (* BND(x, [-0.25, 0.0312501]) *)
Lemma t95 : p142 -> p82 -> p141.
Proof.
 intros h0 h1.
 refine (mul_op _x _w6 i74 i41 i73 h0 h1 _) ; finalize.
Qed.
Lemma l115 : s1 -> p141 (* BND(x * w6, [-0.000488281, 4.35974e-05]) *).
Proof.
 intros h0.
 assert (h1 := l72 h0).
 assert (h2 := l68 h0).
 apply t95. refine (subset _x i43 i74 h1 _) ; finalize. exact h2.
Qed.
Lemma t96 : p141 -> p140.
Proof.
 intros h0.
 refine (float_round_ne _ _ r39 i73 i73 h0 _) ; finalize.
Qed.
Lemma l114 : s1 -> p140 (* BND(float<53,-1074,ne>(x * w6), [-0.000488281, 4.35974e-05]) *).
Proof.
 intros h0.
 assert (h1 := l115 h0).
 apply t96. exact h1.
Qed.
Definition f95 := Float2 (75059993790191) (-53).
Definition i75 := makepairF f47 f95.
Notation p143 := (BND _c5 i75). (* BND(c5, [0.00830078, 0.00833333]) *)
Lemma t97 : p143 -> p140 -> p139.
Proof.
 intros h0 h1.
 refine (add _c5 r38 i75 i73 i72 h0 h1 _) ; finalize.
Qed.
Lemma l113 : s1 -> p139 (* BND(c5 + float<53,-1074,ne>(x * w6), [0.0078125, 0.00837693]) *).
Proof.
 intros h0.
 assert (h1 := l22 h0).
 assert (h2 := l114 h0).
 apply t97. refine (subset _c5 i14 i75 h1 _) ; finalize. exact h2.
Qed.
Lemma t98 : p139 -> p138.
Proof.
 intros h0.
 refine (float_round_ne _ _ r37 i72 i72 h0 _) ; finalize.
Qed.
Lemma l112 : s1 -> p138 (* BND(w5, [0.0078125, 0.00837693]) *).
Proof.
 intros h0.
 assert (h1 := l113 h0).
 apply t98. exact h1.
Qed.
Definition f96 := Float2 (140737938715291) (-52).
Definition i76 := makepairF f80 f96.
Notation p144 := (BND _x i76). (* BND(x, [-0.5, 0.0312501]) *)
Lemma t99 : p144 -> p138 -> p137.
Proof.
 intros h0 h1.
 refine (mul_op _x _w5 i76 i72 i71 h0 h1 _) ; finalize.
Qed.
Lemma l111 : s1 -> p137 (* BND(x * w5, [-0.0078125, 0.00026178]) *).
Proof.
 intros h0.
 assert (h1 := l72 h0).
 assert (h2 := l112 h0).
 apply t99. refine (subset _x i43 i76 h1 _) ; finalize. exact h2.
Qed.
Lemma t100 : p137 -> p136.
Proof.
 intros h0.
 refine (float_round_ne _ _ r35 i71 i71 h0 _) ; finalize.
Qed.
Lemma l110 : s1 -> p136 (* BND(float<53,-1074,ne>(x * w5), [-0.0078125, 0.00026178]) *).
Proof.
 intros h0.
 assert (h1 := l111 h0).
 apply t100. exact h1.
Qed.
Definition i77 := makepairF f43 f15.
Notation p145 := (BND _c4 i77). (* BND(c4, [0.0390625, 0.0416667]) *)
Lemma t101 : p145 -> p136 -> p135.
Proof.
 intros h0 h1.
 refine (add _c4 r34 i77 i71 i70 h0 h1 _) ; finalize.
Qed.
Lemma l109 : s1 -> p135 (* BND(c4 + float<53,-1074,ne>(x * w5), [0.03125, 0.0419284]) *).
Proof.
 intros h0.
 assert (h1 := l18 h0).
 assert (h2 := l110 h0).
 apply t101. refine (subset _c4 i11 i77 h1 _) ; finalize. exact h2.
Qed.
Lemma t102 : p135 -> p134.
Proof.
 intros h0.
 refine (float_round_ne _ _ r33 i70 i70 h0 _) ; finalize.
Qed.
Lemma l108 : s1 -> p134 (* BND(w4, [0.03125, 0.0419284]) *).
Proof.
 intros h0.
 assert (h1 := l109 h0).
 apply t102. exact h1.
Qed.
Definition f97 := Float2 (-36028912311114429) (-60).
Definition i78 := makepairF f97 f14.
Notation p146 := (BND _x i78). (* BND(x, [-0.0312501, 0.5]) *)
Lemma t103 : p146 -> p134 -> p133.
Proof.
 intros h0 h1.
 refine (mul_op _x _w4 i78 i70 i69 h0 h1 _) ; finalize.
Qed.
Lemma l107 : s1 -> p133 (* BND(x * w4, [-0.00131027, 0.03125]) *).
Proof.
 intros h0.
 assert (h1 := l72 h0).
 assert (h2 := l108 h0).
 apply t103. refine (subset _x i43 i78 h1 _) ; finalize. exact h2.
Qed.
Lemma t104 : p133 -> p132.
Proof.
 intros h0.
 refine (float_round_ne _ _ r31 i69 i69 h0 _) ; finalize.
Qed.
Lemma l106 : s1 -> p132 (* BND(float<53,-1074,ne>(x * w4), [-0.00131027, 0.03125]) *).
Proof.
 intros h0.
 assert (h1 := l107 h0).
 apply t104. exact h1.
Qed.
Definition f98 := Float2 (-1) (-5).
Definition i79 := makepairF f98 f13.
Notation p147 := (BND r30 i79). (* BND(float<53,-1074,ne>(x * w4), [-0.03125, 0.03125]) *)
Lemma t105 : p147 -> p131.
Proof.
 intros h0.
 refine (abs_of_bnd_o r30 i79 i68 h0 _) ; finalize.
Qed.
Lemma l105 : s1 -> p131 (* ABS(float<53,-1074,ne>(x * w4), [0, 0.03125]) *).
Proof.
 intros h0.
 assert (h1 := l106 h0).
 apply t105. refine (subset r30 i69 i79 h1 _) ; finalize.
Qed.
Definition f99 := Float2 (3) (-4).
Definition i80 := makepairF f49 f99.
Notation p148 := (ABS _c3 i80). (* ABS(c3, [0.15625, 0.1875]) *)
Lemma t106 : p148 -> p131 -> p130.
Proof.
 intros h0 h1.
 refine (add_aa_p _c3 r30 i80 i68 i67 h0 h1 _) ; finalize.
Qed.
Lemma l104 : s1 -> p130 (* ABS(c3 + float<53,-1074,ne>(x * w4), [0.125, 0.25]) *).
Proof.
 intros h0.
 assert (h1 := l13 h0).
 assert (h2 := l105 h0).
 apply t106. refine (abs_subset _c3 i8 i80 h1 _) ; finalize. exact h2.
Qed.
Notation p149 := (ABS r29 i7). (* ABS(c3 + float<53,-1074,ne>(x * w4), [0.125, 1]) *)
Lemma t107 : p149 -> p129.
Proof.
 intros h0.
 refine (nzr_of_abs r29 i7 h0 _) ; finalize.
Qed.
Lemma l103 : s1 -> p129 (* NZR(c3 + float<53,-1074,ne>(x * w4)) *).
Proof.
 intros h0.
 assert (h1 := l104 h0).
 apply t107. refine (abs_subset r29 i67 i7 h1 _) ; finalize.
Qed.
Notation r78 := ((_w - r29)%R).
Notation r77 := ((r78 / r29)%R).
Notation p150 := (BND r77 i66). (* BND((w - (c3 + float<53,-1074,ne>(x * w4))) / (c3 + float<53,-1074,ne>(x * w4)), [-8.39265e-17, 8.39265e-17]) *)
Definition f100 := Float2 (-1) (-56).
Definition f101 := Float2 (1) (-56).
Definition i81 := makepairF f100 f101.
Notation p151 := (BND r78 i81). (* BND(w - (c3 + float<53,-1074,ne>(x * w4)), [-1.38778e-17, 1.38778e-17]) *)
Lemma t108 : p130 -> p151.
Proof.
 intros h0.
 refine (float_absolute_wide_ne _ _ r29 i67 i81 h0 _) ; finalize.
Qed.
Lemma l117 : s1 -> p151 (* BND(w - (c3 + float<53,-1074,ne>(x * w4)), [-1.38778e-17, 1.38778e-17]) *).
Proof.
 intros h0.
 assert (h1 := l104 h0).
 apply t108. exact h1.
Qed.
Definition f102 := Float2 (762571791102287959) (-62).
Definition i82 := makepairF f102 f8.
Notation p152 := (BND r29 i82). (* BND(c3 + float<53,-1074,ne>(x * w4), [0.165356, 1]) *)
Definition i83 := makepairF f11 f14.
Notation p153 := (BND _c3 i83). (* BND(c3, [0.166667, 0.5]) *)
Definition i84 := makepairF f86 f14.
Notation p154 := (BND r30 i84). (* BND(float<53,-1074,ne>(x * w4), [-0.00131027, 0.5]) *)
Lemma t109 : p153 -> p154 -> p152.
Proof.
 intros h0 h1.
 refine (add _c3 r30 i83 i84 i82 h0 h1 _) ; finalize.
Qed.
Lemma l118 : s1 -> p152 (* BND(c3 + float<53,-1074,ne>(x * w4), [0.165356, 1]) *).
Proof.
 intros h0.
 assert (h1 := l14 h0).
 assert (h2 := l106 h0).
 apply t109. refine (subset _c3 i8 i83 h1 _) ; finalize. refine (subset r30 i69 i84 h2 _) ; finalize.
Qed.
Lemma t110 : p151 -> p152 -> p150.
Proof.
 intros h0 h1.
 refine (div_op r78 r29 i81 i82 i66 h0 h1 _) ; finalize.
Qed.
Lemma l116 : s1 -> p150 (* BND((w - (c3 + float<53,-1074,ne>(x * w4))) / (c3 + float<53,-1074,ne>(x * w4)), [-8.39265e-17, 8.39265e-17]) *).
Proof.
 intros h0.
 assert (h1 := l117 h0).
 assert (h2 := l118 h0).
 apply t110. exact h1. exact h2.
Qed.
Lemma t111 : p129 -> p150 -> p128.
Proof.
 intros h0 h1.
 refine (rel_of_nzr_bnd _w r29 i66 h0 h1) ; finalize.
Qed.
Lemma l102 : s1 -> p128 (* REL(w, c3 + float<53,-1074,ne>(x * w4), [-8.39265e-17, 8.39265e-17]) *).
Proof.
 intros h0.
 assert (h1 := l103 h0).
 assert (h2 := l116 h0).
 apply t111. exact h1. exact h2.
Qed.
Definition f103 := Float2 (-7504832445531101852126071761697188418287602750717029532418991069976003698335321005241292925565568521784531351507815) (-441).
Definition f104 := Float2 (30739793696895393186308389935911683761306020866936952964788187422621711148381474837468335823116568665229440415776010239) (-453).
Definition i85 := makepairF f103 f104.
Notation p155 := (REL r29 _W i85). (* REL(c3 + float<53,-1074,ne>(x * w4), W, [-1.32164e-18, 1.32164e-18]) *)
Notation r80 := ((r29 - _W)%R).
Notation r79 := ((r80 / _W)%R).
Notation p156 := (BND r79 i85). (* BND((c3 + float<53,-1074,ne>(x * w4) - W) / W, [-1.32164e-18, 1.32164e-18]) *)
Definition f105 := Float2 (-10166043153800814528752753406578119128658885615837431427237321138313961894949746341376573486807951607755942958492911367) (-454).
Definition f106 := Float2 (162656690460813032460044054505249906058542169853398902835797138213023390319195941462025175788927225724095087335886581867) (-458).
Definition i86 := makepairF f105 f106.
Notation p157 := (BND r80 i86). (* BND(c3 + float<53,-1074,ne>(x * w4) - W, [-2.18541e-19, 2.18541e-19]) *)
Notation r81 := ((r30 - r8)%R).
Notation p158 := (BND r81 i86). (* BND(float<53,-1074,ne>(x * w4) - x * (c4 + x * (c5 + x * (c6 + x * (c7 + x * (c8 + x * c9))))), [-2.18541e-19, 2.18541e-19]) *)
Notation r83 := ((r30 - r31)%R).
Notation r84 := ((r31 - r8)%R).
Notation r82 := ((r83 + r84)%R).
Notation p159 := (BND r82 i86). (* BND(float<53,-1074,ne>(x * w4) - x * w4 + (x * w4 - x * (c4 + x * (c5 + x * (c6 + x * (c7 + x * (c8 + x * c9)))))), [-2.18541e-19, 2.18541e-19]) *)
Definition f107 := Float2 (-1) (-63).
Definition f108 := Float2 (1) (-63).
Definition i87 := makepairF f107 f108.
Notation p160 := (BND r83 i87). (* BND(float<53,-1074,ne>(x * w4) - x * w4, [-1.0842e-19, 1.0842e-19]) *)
Definition i88 := makepairF f12 f46.
Notation p161 := (ABS r31 i88). (* ABS(x * w4, [1.73472e-18, 0.00195312]) *)
Definition f109 := Float2 (3) (-6).
Definition i89 := makepairF f13 f109.
Notation p162 := (ABS _w4 i89). (* ABS(w4, [0.03125, 0.046875]) *)
Notation p163 := (BND _w4 i89). (* BND(w4, [0.03125, 0.046875]) *)
Lemma t112 : p163 -> p162.
Proof.
 intros h0.
 refine (abs_of_bnd_p _w4 i89 i89 h0 _) ; finalize.
Qed.
Lemma l126 : s1 -> p162 (* ABS(w4, [0.03125, 0.046875]) *).
Proof.
 intros h0.
 assert (h1 := l108 h0).
 apply t112. refine (subset _w4 i70 i89 h1 _) ; finalize.
Qed.
Lemma t113 : p43 -> p162 -> p161.
Proof.
 intros h0 h1.
 refine (mul_aa _x _w4 i30 i89 i88 h0 h1 _) ; finalize.
Qed.
Lemma l125 : s1 -> p161 (* ABS(x * w4, [1.73472e-18, 0.00195312]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 assert (h2 := l126 h0).
 apply t113. refine (abs_subset _x i5 i30 h1 _) ; finalize. exact h2.
Qed.
Lemma t114 : p161 -> p160.
Proof.
 intros h0.
 refine (float_absolute_wide_ne _ _ r31 i88 i87 h0 _) ; finalize.
Qed.
Lemma l124 : s1 -> p160 (* BND(float<53,-1074,ne>(x * w4) - x * w4, [-1.0842e-19, 1.0842e-19]) *).
Proof.
 intros h0.
 assert (h1 := l125 h0).
 apply t114. exact h1.
Qed.
Definition f110 := Float2 (-5122586360662321189581036273759736561608678989217854253739939582570509508198103383115547406182682405732694575733638919) (-454).
Definition f111 := Float2 (81961381770597139033296580380155784985738863827485668059839033321128152131169654129848758498922918491723113211738222699) (-458).
Definition i90 := makepairF f110 f111.
Notation p164 := (BND r84 i90). (* BND(x * w4 - x * (c4 + x * (c5 + x * (c6 + x * (c7 + x * (c8 + x * c9))))), [-1.10121e-19, 1.10121e-19]) *)
Notation r86 := ((_w4 - r9)%R).
Notation r85 := ((_x * r86)%R).
Notation p165 := (BND r85 i90). (* BND(x * (w4 - (c4 + x * (c5 + x * (c6 + x * (c7 + x * (c8 + x * c9)))))), [-1.10121e-19, 1.10121e-19]) *)
Definition f112 := Float2 (-327844477980059019944322499688624136345719149008665844508653705592654712029600121799005277178804701791846718937452290947) (-455).
Definition f113 := Float2 (327844477980059019944322499688624136345719149008665844508653705592654712029600121799005277178804701791846718937452290947) (-455).
Definition i91 := makepairF f112 f113.
Notation p166 := (BND r86 i91). (* BND(w4 - (c4 + x * (c5 + x * (c6 + x * (c7 + x * (c8 + x * c9))))), [-3.52387e-18, 3.52387e-18]) *)
Notation r88 := ((_w4 - r33)%R).
Notation r89 := ((r33 - r9)%R).
Notation r87 := ((r88 + r89)%R).
Notation p167 := (BND r87 i91). (* BND(w4 - (c4 + float<53,-1074,ne>(x * w5)) + (c4 + float<53,-1074,ne>(x * w5) - (c4 + x * (c5 + x * (c6 + x * (c7 + x * (c8 + x * c9)))))), [-3.52387e-18, 3.52387e-18]) *)
Definition f114 := Float2 (-1) (-58).
Definition f115 := Float2 (1) (-58).
Definition i92 := makepairF f114 f115.
Notation p168 := (BND r88 i92). (* BND(w4 - (c4 + float<53,-1074,ne>(x * w5)), [-3.46945e-18, 3.46945e-18]) *)
Definition i93 := makepairF f13 f45.
Notation p169 := (ABS r33 i93). (* ABS(c4 + float<53,-1074,ne>(x * w5), [0.03125, 0.0625]) *)
Definition i94 := makepairF f81 f17.
Notation p170 := (ABS r34 i94). (* ABS(float<53,-1074,ne>(x * w5), [0, 0.0078125]) *)
Definition i95 := makepairF f88 f17.
Notation p171 := (BND r34 i95). (* BND(float<53,-1074,ne>(x * w5), [-0.0078125, 0.0078125]) *)
Lemma t115 : p171 -> p170.
Proof.
 intros h0.
 refine (abs_of_bnd_o r34 i95 i94 h0 _) ; finalize.
Qed.
Lemma l133 : s1 -> p170 (* ABS(float<53,-1074,ne>(x * w5), [0, 0.0078125]) *).
Proof.
 intros h0.
 assert (h1 := l110 h0).
 apply t115. refine (subset r34 i71 i95 h1 _) ; finalize.
Qed.
Definition i96 := makepairF f43 f109.
Notation p172 := (ABS _c4 i96). (* ABS(c4, [0.0390625, 0.046875]) *)
Lemma t116 : p172 -> p170 -> p169.
Proof.
 intros h0 h1.
 refine (add_aa_p _c4 r34 i96 i94 i93 h0 h1 _) ; finalize.
Qed.
Lemma l132 : s1 -> p169 (* ABS(c4 + float<53,-1074,ne>(x * w5), [0.03125, 0.0625]) *).
Proof.
 intros h0.
 assert (h1 := l17 h0).
 assert (h2 := l133 h0).
 apply t116. refine (abs_subset _c4 i11 i96 h1 _) ; finalize. exact h2.
Qed.
Lemma t117 : p169 -> p168.
Proof.
 intros h0.
 refine (float_absolute_wide_ne _ _ r33 i93 i92 h0 _) ; finalize.
Qed.
Lemma l131 : s1 -> p168 (* BND(w4 - (c4 + float<53,-1074,ne>(x * w5)), [-3.46945e-18, 3.46945e-18]) *).
Proof.
 intros h0.
 assert (h1 := l132 h0).
 apply t117. exact h1.
Qed.
Definition f116 := Float2 (-5063243219195446237332603188247652054505924905012905404821286025073759277494972470299608018787472862358822440858854275) (-455).
Definition f117 := Float2 (5063243219195446237332603188247652054505924905012905404821286025073759277494972470299608018787472862358822440858854275) (-455).
Definition i97 := makepairF f116 f117.
Notation p173 := (BND r89 i97). (* BND(c4 + float<53,-1074,ne>(x * w5) - (c4 + x * (c5 + x * (c6 + x * (c7 + x * (c8 + x * c9))))), [-5.44228e-20, 5.44228e-20]) *)
Notation r90 := ((r34 - r11)%R).
Notation p174 := (BND r90 i97). (* BND(float<53,-1074,ne>(x * w5) - x * (c5 + x * (c6 + x * (c7 + x * (c8 + x * c9)))), [-5.44228e-20, 5.44228e-20]) *)
Notation r92 := ((r34 - r35)%R).
Notation r93 := ((r35 - r11)%R).
Notation r91 := ((r92 + r93)%R).
Notation p175 := (BND r91 i97). (* BND(float<53,-1074,ne>(x * w5) - x * w5 + (x * w5 - x * (c5 + x * (c6 + x * (c7 + x * (c8 + x * c9))))), [-5.44228e-20, 5.44228e-20]) *)
Definition f118 := Float2 (-1) (-65).
Definition f119 := Float2 (1) (-65).
Definition i98 := makepairF f118 f119.
Notation p176 := (BND r92 i98). (* BND(float<53,-1074,ne>(x * w5) - x * w5, [-2.71051e-20, 2.71051e-20]) *)
Definition i99 := makepairF f16 f20.
Notation p177 := (ABS r35 i99). (* ABS(x * w5, [4.33681e-19, 0.000488281]) *)
Definition f120 := Float2 (3) (-8).
Definition i100 := makepairF f17 f120.
Notation p178 := (ABS _w5 i100). (* ABS(w5, [0.0078125, 0.0117188]) *)
Notation p179 := (BND _w5 i100). (* BND(w5, [0.0078125, 0.0117188]) *)
Lemma t118 : p179 -> p178.
Proof.
 intros h0.
 refine (abs_of_bnd_p _w5 i100 i100 h0 _) ; finalize.
Qed.
Lemma l139 : s1 -> p178 (* ABS(w5, [0.0078125, 0.0117188]) *).
Proof.
 intros h0.
 assert (h1 := l112 h0).
 apply t118. refine (subset _w5 i72 i100 h1 _) ; finalize.
Qed.
Lemma t119 : p43 -> p178 -> p177.
Proof.
 intros h0 h1.
 refine (mul_aa _x _w5 i30 i100 i99 h0 h1 _) ; finalize.
Qed.
Lemma l138 : s1 -> p177 (* ABS(x * w5, [4.33681e-19, 0.000488281]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 assert (h2 := l139 h0).
 apply t119. refine (abs_subset _x i5 i30 h1 _) ; finalize. exact h2.
Qed.
Lemma t120 : p177 -> p176.
Proof.
 intros h0.
 refine (float_absolute_wide_ne _ _ r35 i99 i98 h0 _) ; finalize.
Qed.
Lemma l137 : s1 -> p176 (* BND(float<53,-1074,ne>(x * w5) - x * w5, [-2.71051e-20, 2.71051e-20]) *).
Proof.
 intros h0.
 assert (h1 := l138 h0).
 apply t120. exact h1.
Qed.
Definition f121 := Float2 (-2541514822626199567746744621838460770980821591703116818072595247202033084119150991169094978474838261347198249479218051) (-455).
Definition f122 := Float2 (2541514822626199567746744621838460770980821591703116818072595247202033084119150991169094978474838261347198249479218051) (-455).
Definition i101 := makepairF f121 f122.
Notation p180 := (BND r93 i101). (* BND(x * w5 - x * (c5 + x * (c6 + x * (c7 + x * (c8 + x * c9)))), [-2.73177e-20, 2.73177e-20]) *)
Notation r95 := ((_w5 - r12)%R).
Notation r94 := ((_x * r95)%R).
Notation p181 := (BND r94 i101). (* BND(x * (w5 - (c5 + x * (c6 + x * (c7 + x * (c8 + x * c9))))), [-2.73177e-20, 2.73177e-20]) *)
Definition f123 := Float2 (-19855521014099939003216632064890367124112871523991723367677373801169719726577742069733931370754287503054976548131437) (-443).
Definition f124 := Float2 (19855521014099939003216632064890367124112871523991723367677373801169719726577742069733931370754287503054976548131437) (-443).
Definition i102 := makepairF f123 f124.
Notation p182 := (BND r95 i102). (* BND(w5 - (c5 + x * (c6 + x * (c7 + x * (c8 + x * c9)))), [-8.74165e-19, 8.74165e-19]) *)
Notation r97 := ((_w5 - r37)%R).
Notation r98 := ((r37 - r12)%R).
Notation r96 := ((r97 + r98)%R).
Notation p183 := (BND r96 i102). (* BND(w5 - (c5 + float<53,-1074,ne>(x * w6)) + (c5 + float<53,-1074,ne>(x * w6) - (c5 + x * (c6 + x * (c7 + x * (c8 + x * c9))))), [-8.74165e-19, 8.74165e-19]) *)
Definition f125 := Float2 (-1) (-60).
Definition f126 := Float2 (1) (-60).
Definition i103 := makepairF f125 f126.
Notation p184 := (BND r97 i103). (* BND(w5 - (c5 + float<53,-1074,ne>(x * w6)), [-8.67362e-19, 8.67362e-19]) *)
Definition f127 := Float2 (1) (-6).
Definition i104 := makepairF f17 f127.
Notation p185 := (ABS r37 i104). (* ABS(c5 + float<53,-1074,ne>(x * w6), [0.0078125, 0.015625]) *)
Definition i105 := makepairF f81 f20.
Notation p186 := (ABS r38 i105). (* ABS(float<53,-1074,ne>(x * w6), [0, 0.000488281]) *)
Definition i106 := makepairF f91 f20.
Notation p187 := (BND r38 i106). (* BND(float<53,-1074,ne>(x * w6), [-0.000488281, 0.000488281]) *)
Lemma t121 : p187 -> p186.
Proof.
 intros h0.
 refine (abs_of_bnd_o r38 i106 i105 h0 _) ; finalize.
Qed.
Lemma l146 : s1 -> p186 (* ABS(float<53,-1074,ne>(x * w6), [0, 0.000488281]) *).
Proof.
 intros h0.
 assert (h1 := l114 h0).
 apply t121. refine (subset r38 i73 i106 h1 _) ; finalize.
Qed.
Definition i107 := makepairF f47 f120.
Notation p188 := (ABS _c5 i107). (* ABS(c5, [0.00830078, 0.0117188]) *)
Lemma t122 : p188 -> p186 -> p185.
Proof.
 intros h0 h1.
 refine (add_aa_p _c5 r38 i107 i105 i104 h0 h1 _) ; finalize.
Qed.
Lemma l145 : s1 -> p185 (* ABS(c5 + float<53,-1074,ne>(x * w6), [0.0078125, 0.015625]) *).
Proof.
 intros h0.
 assert (h1 := l21 h0).
 assert (h2 := l146 h0).
 apply t122. refine (abs_subset _c5 i14 i107 h1 _) ; finalize. exact h2.
Qed.
Lemma t123 : p185 -> p184.
Proof.
 intros h0.
 refine (float_absolute_wide_ne _ _ r37 i104 i103 h0 _) ; finalize.
Qed.
Lemma l144 : s1 -> p184 (* BND(w5 - (c5 + float<53,-1074,ne>(x * w6)), [-8.67362e-19, 8.67362e-19]) *).
Proof.
 intros h0.
 assert (h1 := l145 h0).
 apply t123. exact h1.
Qed.
Definition f128 := Float2 (-154517915902699397077112014818560221573001888759000033703227099046858840829136764026798243311829682651662552978029) (-443).
Definition f129 := Float2 (154517915902699397077112014818560221573001888759000033703227099046858840829136764026798243311829682651662552978029) (-443).
Definition i108 := makepairF f128 f129.
Notation p189 := (BND r98 i108). (* BND(c5 + float<53,-1074,ne>(x * w6) - (c5 + x * (c6 + x * (c7 + x * (c8 + x * c9)))), [-6.80285e-21, 6.80285e-21]) *)
Notation r99 := ((r38 - r14)%R).
Notation p190 := (BND r99 i108). (* BND(float<53,-1074,ne>(x * w6) - x * (c6 + x * (c7 + x * (c8 + x * c9))), [-6.80285e-21, 6.80285e-21]) *)
Notation r101 := ((r38 - r39)%R).
Notation r102 := ((r39 - r14)%R).
Notation r100 := ((r101 + r102)%R).
Notation p191 := (BND r100 i108). (* BND(float<53,-1074,ne>(x * w6) - x * w6 + (x * w6 - x * (c6 + x * (c7 + x * (c8 + x * c9)))), [-6.80285e-21, 6.80285e-21]) *)
Definition f130 := Float2 (-1) (-68).
Definition f131 := Float2 (1) (-68).
Definition i109 := makepairF f130 f131.
Notation p192 := (BND r101 i109). (* BND(float<53,-1074,ne>(x * w6) - x * w6, [-3.38813e-21, 3.38813e-21]) *)
Definition i110 := makepairF f19 f33.
Notation p193 := (ABS r39 i110). (* ABS(x * w6, [5.42101e-20, 6.10352e-05]) *)
Lemma t124 : p43 -> p81 -> p193.
Proof.
 intros h0 h1.
 refine (mul_aa _x _w6 i30 i40 i110 h0 h1 _) ; finalize.
Qed.
Lemma l151 : s1 -> p193 (* ABS(x * w6, [5.42101e-20, 6.10352e-05]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 assert (h2 := l67 h0).
 apply t124. refine (abs_subset _x i5 i30 h1 _) ; finalize. exact h2.
Qed.
Lemma t125 : p193 -> p192.
Proof.
 intros h0.
 refine (float_absolute_wide_ne _ _ r39 i110 i109 h0 _) ; finalize.
Qed.
Lemma l150 : s1 -> p192 (* BND(float<53,-1074,ne>(x * w6) - x * w6, [-3.38813e-21, 3.38813e-21]) *).
Proof.
 intros h0.
 assert (h1 := l151 h0).
 apply t125. exact h1.
Qed.
Definition f132 := Float2 (-77560872550366429865629514622967225859955522996372208179890588491691415494181274551379754532757581790712107684461) (-443).
Definition f133 := Float2 (77560872550366429865629514622967225859955522996372208179890588491691415494181274551379754532757581790712107684461) (-443).
Definition i111 := makepairF f132 f133.
Notation p194 := (BND r102 i111). (* BND(x * w6 - x * (c6 + x * (c7 + x * (c8 + x * c9))), [-3.41472e-21, 3.41472e-21]) *)
Notation r104 := ((_w6 - r15)%R).
Notation r103 := ((_x * r104)%R).
Notation p195 := (BND r103 i111). (* BND(x * (w6 - (c6 + x * (c7 + x * (c8 + x * c9)))), [-3.41472e-21, 3.41472e-21]) *)
Definition f134 := Float2 (-158844158681842666468276547462884997329197457664705755293998984434233829383829222027715248594292025772895923270821657) (-449).
Definition f135 := Float2 (158844158681842666468276547462884997329197457664705755293998984434233829383829222027715248594292025772895923270821657) (-449).
Definition i112 := makepairF f134 f135.
Notation p196 := (BND r104 i112). (* BND(w6 - (c6 + x * (c7 + x * (c8 + x * c9))), [-1.09271e-19, 1.09271e-19]) *)
Notation r106 := ((_w6 - r41)%R).
Notation r107 := ((r41 - r15)%R).
Notation r105 := ((r106 + r107)%R).
Notation p197 := (BND r105 i112). (* BND(w6 - (c6 + float<53,-1074,ne>(x * w7)) + (c6 + float<53,-1074,ne>(x * w7) - (c6 + x * (c7 + x * (c8 + x * c9)))), [-1.09271e-19, 1.09271e-19]) *)
Notation p198 := (BND r106 i87). (* BND(w6 - (c6 + float<53,-1074,ne>(x * w7)), [-1.0842e-19, 1.0842e-19]) *)
Definition i113 := makepairF f21 f46.
Notation p199 := (ABS r41 i113). (* ABS(c6 + float<53,-1074,ne>(x * w7), [0.000976562, 0.00195312]) *)
Definition i114 := makepairF f81 f26.
Notation p200 := (ABS r42 i114). (* ABS(float<53,-1074,ne>(x * w7), [0, 0.000244141]) *)
Definition i115 := makepairF f53 f26.
Notation p201 := (BND r42 i115). (* BND(float<53,-1074,ne>(x * w7), [-0.000244141, 0.000244141]) *)
Lemma t126 : p201 -> p200.
Proof.
 intros h0.
 refine (abs_of_bnd_o r42 i115 i114 h0 _) ; finalize.
Qed.
Lemma l158 : s1 -> p200 (* ABS(float<53,-1074,ne>(x * w7), [0, 0.000244141]) *).
Proof.
 intros h0.
 assert (h1 := l70 h0).
 apply t126. refine (subset r42 i42 i115 h1 _) ; finalize.
Qed.
Lemma t127 : p26 -> p200 -> p199.
Proof.
 intros h0 h1.
 refine (add_aa_p _c6 r42 i17 i114 i113 h0 h1 _) ; finalize.
Qed.
Lemma l157 : s1 -> p199 (* ABS(c6 + float<53,-1074,ne>(x * w7), [0.000976562, 0.00195312]) *).
Proof.
 intros h0.
 assert (h1 := l25 h0).
 assert (h2 := l158 h0).
 apply t127. exact h1. exact h2.
Qed.
Lemma t128 : p199 -> p198.
Proof.
 intros h0.
 refine (float_absolute_wide_ne _ _ r41 i113 i87 h0 _) ; finalize.
Qed.
Lemma l156 : s1 -> p198 (* BND(w6 - (c6 + float<53,-1074,ne>(x * w7)), [-1.0842e-19, 1.0842e-19]) *).
Proof.
 intros h0.
 assert (h1 := l157 h0).
 apply t128. exact h1.
Qed.
Definition f136 := Float2 (-1236133896264749619160387062310542108878500582843968622205810817250942297840379582058183574752363209669411309594393) (-449).
Definition f137 := Float2 (1236133896264749619160387062310542108878500582843968622205810817250942297840379582058183574752363209669411309594393) (-449).
Definition i116 := makepairF f136 f137.
Notation p202 := (BND r107 i116). (* BND(c6 + float<53,-1074,ne>(x * w7) - (c6 + x * (c7 + x * (c8 + x * c9))), [-8.5035e-22, 8.5035e-22]) *)
Notation r108 := ((r42 - r17)%R).
Notation p203 := (BND r108 i116). (* BND(float<53,-1074,ne>(x * w7) - x * (c7 + x * (c8 + x * c9)), [-8.5035e-22, 8.5035e-22]) *)
Notation r110 := ((r42 - r43)%R).
Notation r111 := ((r43 - r17)%R).
Notation r109 := ((r110 + r111)%R).
Notation p204 := (BND r109 i116). (* BND(float<53,-1074,ne>(x * w7) - x * w7 + (x * w7 - x * (c7 + x * (c8 + x * c9))), [-8.5035e-22, 8.5035e-22]) *)
Definition f138 := Float2 (-1) (-71).
Definition f139 := Float2 (1) (-71).
Definition i117 := makepairF f138 f139.
Notation p205 := (BND r110 i117). (* BND(float<53,-1074,ne>(x * w7) - x * w7, [-4.23516e-22, 4.23516e-22]) *)
Definition i118 := makepairF f25 f44.
Notation p206 := (ABS r43 i118). (* ABS(x * w7, [6.77626e-21, 7.62939e-06]) *)
Definition i119 := makepairF f27 f30.
Notation p207 := (ABS _w7 i119). (* ABS(w7, [0.00012207, 0.000213623]) *)
Notation p208 := (BND _w7 i119). (* BND(w7, [0.00012207, 0.000213623]) *)
Lemma t129 : p208 -> p207.
Proof.
 intros h0.
 refine (abs_of_bnd_p _w7 i119 i119 h0 _) ; finalize.
Qed.
Lemma l164 : s1 -> p207 (* ABS(w7, [0.00012207, 0.000213623]) *).
Proof.
 intros h0.
 assert (h1 := l73 h0).
 apply t129. refine (subset _w7 i44 i119 h1 _) ; finalize.
Qed.
Definition f140 := Float2 (9) (-8).
Definition i120 := makepairF f1 f140.
Notation p209 := (ABS _x i120). (* ABS(x, [5.55112e-17, 0.0351562]) *)
Lemma t130 : p209 -> p207 -> p206.
Proof.
 intros h0 h1.
 refine (mul_aa _x _w7 i120 i119 i118 h0 h1 _) ; finalize.
Qed.
Lemma l163 : s1 -> p206 (* ABS(x * w7, [6.77626e-21, 7.62939e-06]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 assert (h2 := l164 h0).
 apply t130. refine (abs_subset _x i5 i120 h1 _) ; finalize. exact h2.
Qed.
Lemma t131 : p206 -> p205.
Proof.
 intros h0.
 refine (float_absolute_wide_ne _ _ r43 i118 i117 h0 _) ; finalize.
Qed.
Lemma l162 : s1 -> p205 (* BND(float<53,-1074,ne>(x * w7) - x * w7, [-4.23516e-22, 4.23516e-22]) *).
Proof.
 intros h0.
 assert (h1 := l163 h0).
 apply t131. exact h1.
Qed.
Definition f141 := Float2 (-620477549446085881468527060745798143174129656742946018019118732809602895160735666254835664519786402781807747245849) (-449).
Definition f142 := Float2 (620477549446085881468527060745798143174129656742946018019118732809602895160735666254835664519786402781807747245849) (-449).
Definition i121 := makepairF f141 f142.
Notation p210 := (BND r111 i121). (* BND(x * w7 - x * (c7 + x * (c8 + x * c9)), [-4.26833e-22, 4.26833e-22]) *)
Notation r113 := ((_w7 - r18)%R).
Notation r112 := ((_x * r113)%R).
Notation p211 := (BND r112 i121). (* BND(x * (w7 - (c7 + x * (c8 + x * c9))), [-4.26833e-22, 4.26833e-22]) *)
Definition f143 := Float2 (-1240951127848562647536582004429182112965497823892855578900384984387255751103067802692702712390893154705520436826299) (-445).
Definition f144 := Float2 (1240951127848562647536582004429182112965497823892855578900384984387255751103067802692702712390893154705520436826299) (-445).
Definition i122 := makepairF f143 f144.
Notation p212 := (BND r113 i122). (* BND(w7 - (c7 + x * (c8 + x * c9)), [-1.36586e-20, 1.36586e-20]) *)
Notation r115 := ((_w7 - r45)%R).
Notation r116 := ((r45 - r18)%R).
Notation r114 := ((r115 + r116)%R).
Notation p213 := (BND r114 i122). (* BND(w7 - (c7 + float<53,-1074,ne>(x * w8)) + (c7 + float<53,-1074,ne>(x * w8) - (c7 + x * (c8 + x * c9))), [-1.36586e-20, 1.36586e-20]) *)
Definition f145 := Float2 (-1) (-66).
Definition f146 := Float2 (1) (-66).
Definition i123 := makepairF f145 f146.
Notation p214 := (BND r115 i123). (* BND(w7 - (c7 + float<53,-1074,ne>(x * w8)), [-1.35525e-20, 1.35525e-20]) *)
Definition i124 := makepairF f27 f26.
Notation p215 := (ABS r45 i124). (* ABS(c7 + float<53,-1074,ne>(x * w8), [0.00012207, 0.000244141]) *)
Definition f147 := Float2 (1) (-15).
Definition i125 := makepairF f81 f147.
Notation p216 := (ABS r46 i125). (* ABS(float<53,-1074,ne>(x * w8), [0, 3.05176e-05]) *)
Definition i126 := makepairF f57 f147.
Notation p217 := (BND r46 i126). (* BND(float<53,-1074,ne>(x * w8), [-3.05176e-05, 3.05176e-05]) *)
Lemma t132 : p217 -> p216.
Proof.
 intros h0.
 refine (abs_of_bnd_o r46 i126 i125 h0 _) ; finalize.
Qed.
Lemma l171 : s1 -> p216 (* ABS(float<53,-1074,ne>(x * w8), [0, 3.05176e-05]) *).
Proof.
 intros h0.
 assert (h1 := l75 h0).
 apply t132. refine (subset r46 i45 i126 h1 _) ; finalize.
Qed.
Lemma t133 : p31 -> p216 -> p215.
Proof.
 intros h0 h1.
 refine (add_aa_p _c7 r46 i21 i125 i124 h0 h1 _) ; finalize.
Qed.
Lemma l170 : s1 -> p215 (* ABS(c7 + float<53,-1074,ne>(x * w8), [0.00012207, 0.000244141]) *).
Proof.
 intros h0.
 assert (h1 := l29 h0).
 assert (h2 := l171 h0).
 apply t133. exact h1. exact h2.
Qed.
Lemma t134 : p215 -> p214.
Proof.
 intros h0.
 refine (float_absolute_wide_ne _ _ r45 i124 i123 h0 _) ; finalize.
Qed.
Lemma l169 : s1 -> p214 (* BND(w7 - (c7 + float<53,-1074,ne>(x * w8)), [-1.35525e-20, 1.35525e-20]) *).
Proof.
 intros h0.
 assert (h1 := l170 h0).
 apply t134. exact h1.
Qed.
Definition f148 := Float2 (-9638434211235172152862001299694181556755971690810370527000815504576945743779971086006891925739540930313312129211) (-445).
Definition f149 := Float2 (9638434211235172152862001299694181556755971690810370527000815504576945743779971086006891925739540930313312129211) (-445).
Definition i127 := makepairF f148 f149.
Notation p218 := (BND r116 i127). (* BND(c7 + float<53,-1074,ne>(x * w8) - (c7 + x * (c8 + x * c9)), [-1.06086e-22, 1.06086e-22]) *)
Notation r117 := ((r46 - r20)%R).
Notation p219 := (BND r117 i127). (* BND(float<53,-1074,ne>(x * w8) - x * (c8 + x * c9), [-1.06086e-22, 1.06086e-22]) *)
Notation r119 := ((r46 - r47)%R).
Notation r120 := ((r47 - r20)%R).
Notation r118 := ((r119 + r120)%R).
Notation p220 := (BND r118 i127). (* BND(float<53,-1074,ne>(x * w8) - x * w8 + (x * w8 - x * (c8 + x * c9)), [-1.06086e-22, 1.06086e-22]) *)
Definition f150 := Float2 (-1) (-74).
Definition f151 := Float2 (1) (-74).
Definition i128 := makepairF f150 f151.
Notation p221 := (BND r119 i128). (* BND(float<53,-1074,ne>(x * w8) - x * w8, [-5.29396e-23, 5.29396e-23]) *)
Definition f152 := Float2 (1) (-20).
Definition i129 := makepairF f32 f152.
Notation p222 := (ABS r47 i129). (* ABS(x * w8, [8.47033e-22, 9.53674e-07]) *)
Definition i130 := makepairF f34 f36.
Notation p223 := (ABS _w8 i130). (* ABS(w8, [1.52588e-05, 2.67029e-05]) *)
Notation p224 := (BND _w8 i130). (* BND(w8, [1.52588e-05, 2.67029e-05]) *)
Lemma t135 : p224 -> p223.
Proof.
 intros h0.
 refine (abs_of_bnd_p _w8 i130 i130 h0 _) ; finalize.
Qed.
Lemma l177 : s1 -> p223 (* ABS(w8, [1.52588e-05, 2.67029e-05]) *).
Proof.
 intros h0.
 assert (h1 := l77 h0).
 apply t135. refine (subset _w8 i46 i130 h1 _) ; finalize.
Qed.
Lemma t136 : p209 -> p223 -> p222.
Proof.
 intros h0 h1.
 refine (mul_aa _x _w8 i120 i130 i129 h0 h1 _) ; finalize.
Qed.
Lemma l176 : s1 -> p222 (* ABS(x * w8, [8.47033e-22, 9.53674e-07]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 assert (h2 := l177 h0).
 apply t136. refine (abs_subset _x i5 i120 h1 _) ; finalize. exact h2.
Qed.
Lemma t137 : p222 -> p221.
Proof.
 intros h0.
 refine (float_absolute_wide_ne _ _ r47 i129 i128 h0 _) ; finalize.
Qed.
Lemma l175 : s1 -> p221 (* BND(float<53,-1074,ne>(x * w8) - x * w8, [-5.29396e-23, 5.29396e-23]) *).
Proof.
 intros h0.
 assert (h1 := l176 h0).
 apply t137. exact h1.
Qed.
Definition f153 := Float2 (-4828619001714361702144345037469619324690573830646131431792283594878981660345252993793236377047534626503909298363) (-445).
Definition f154 := Float2 (4828619001714361702144345037469619324690573830646131431792283594878981660345252993793236377047534626503909298363) (-445).
Definition i131 := makepairF f153 f154.
Notation p225 := (BND r120 i131). (* BND(x * w8 - x * (c8 + x * c9), [-5.31465e-23, 5.31465e-23]) *)
Notation r122 := ((_w8 - r21)%R).
Notation r121 := ((_x * r122)%R).
Notation p226 := (BND r121 i131). (* BND(x * (w8 - (c8 + x * c9)), [-5.31465e-23, 5.31465e-23]) *)
Definition f155 := Float2 (-257) (-77).
Definition f156 := Float2 (257) (-77).
Definition i132 := makepairF f155 f156.
Notation p227 := (BND r122 i132). (* BND(w8 - (c8 + x * c9), [-1.70068e-21, 1.70068e-21]) *)
Notation r124 := ((_w8 - r49)%R).
Notation r125 := ((r49 - r21)%R).
Notation r123 := ((r124 + r125)%R).
Notation p228 := (BND r123 i132). (* BND(w8 - (c8 + float<53,-1074,ne>(x * c9)) + (c8 + float<53,-1074,ne>(x * c9) - (c8 + x * c9)), [-1.70068e-21, 1.70068e-21]) *)
Definition f157 := Float2 (-1) (-69).
Definition f158 := Float2 (1) (-69).
Definition i133 := makepairF f157 f158.
Notation p229 := (BND r124 i133). (* BND(w8 - (c8 + float<53,-1074,ne>(x * c9)), [-1.69407e-21, 1.69407e-21]) *)
Definition i134 := makepairF f34 f147.
Notation p230 := (ABS r49 i134). (* ABS(c8 + float<53,-1074,ne>(x * c9), [1.52588e-05, 3.05176e-05]) *)
Definition f159 := Float2 (1) (-18).
Definition i135 := makepairF f81 f159.
Notation p231 := (ABS r50 i135). (* ABS(float<53,-1074,ne>(x * c9), [0, 3.8147e-06]) *)
Definition i136 := makepairF f60 f159.
Notation p232 := (BND r50 i136). (* BND(float<53,-1074,ne>(x * c9), [-3.8147e-06, 3.8147e-06]) *)
Lemma t138 : p232 -> p231.
Proof.
 intros h0.
 refine (abs_of_bnd_o r50 i136 i135 h0 _) ; finalize.
Qed.
Lemma l184 : s1 -> p231 (* ABS(float<53,-1074,ne>(x * c9), [0, 3.8147e-06]) *).
Proof.
 intros h0.
 assert (h1 := l79 h0).
 apply t138. refine (subset r50 i47 i136 h1 _) ; finalize.
Qed.
Lemma t139 : p36 -> p231 -> p230.
Proof.
 intros h0 h1.
 refine (add_aa_p _c8 r50 i25 i135 i134 h0 h1 _) ; finalize.
Qed.
Lemma l183 : s1 -> p230 (* ABS(c8 + float<53,-1074,ne>(x * c9), [1.52588e-05, 3.05176e-05]) *).
Proof.
 intros h0.
 assert (h1 := l33 h0).
 assert (h2 := l184 h0).
 apply t139. exact h1. exact h2.
Qed.
Lemma t140 : p230 -> p229.
Proof.
 intros h0.
 refine (float_absolute_wide_ne _ _ r49 i134 i133 h0 _) ; finalize.
Qed.
Lemma l182 : s1 -> p229 (* BND(w8 - (c8 + float<53,-1074,ne>(x * c9)), [-1.69407e-21, 1.69407e-21]) *).
Proof.
 intros h0.
 assert (h1 := l183 h0).
 apply t140. exact h1.
Qed.
Definition f160 := Float2 (-1) (-77).
Definition f161 := Float2 (1) (-77).
Definition i137 := makepairF f160 f161.
Notation p233 := (BND r125 i137). (* BND(c8 + float<53,-1074,ne>(x * c9) - (c8 + x * c9), [-6.61744e-24, 6.61744e-24]) *)
Notation r126 := ((r50 - r23)%R).
Notation p234 := (BND r126 i137). (* BND(float<53,-1074,ne>(x * c9) - x * c9, [-6.61744e-24, 6.61744e-24]) *)
Lemma t141 : p39 -> p234.
Proof.
 intros h0.
 refine (float_absolute_wide_ne _ _ r23 i27 i137 h0 _) ; finalize.
Qed.
Lemma l186 : s1 -> p234 (* BND(float<53,-1074,ne>(x * c9) - x * c9, [-6.61744e-24, 6.61744e-24]) *).
Proof.
 intros h0.
 assert (h1 := l35 h0).
 apply t141. exact h1.
Qed.
Lemma t142 : p234 -> p233.
Proof.
 intros h0.
 refine (add_fils _ _ _ i137 h0) ; finalize.
Qed.
Lemma l185 : s1 -> p233 (* BND(c8 + float<53,-1074,ne>(x * c9) - (c8 + x * c9), [-6.61744e-24, 6.61744e-24]) *).
Proof.
 intros h0.
 assert (h1 := l186 h0).
 apply t142. exact h1.
Qed.
Lemma t143 : p229 -> p233 -> p228.
Proof.
 intros h0 h1.
 refine (add r124 r125 i133 i137 i132 h0 h1 _) ; finalize.
Qed.
Lemma l181 : s1 -> p228 (* BND(w8 - (c8 + float<53,-1074,ne>(x * c9)) + (c8 + float<53,-1074,ne>(x * c9) - (c8 + x * c9)), [-1.70068e-21, 1.70068e-21]) *).
Proof.
 intros h0.
 assert (h1 := l182 h0).
 assert (h2 := l185 h0).
 apply t143. exact h1. exact h2.
Qed.
Lemma t144 : p228 -> p227.
Proof.
 intros h0.
 refine (sub_xals _ _ _ i132 h0) ; finalize.
Qed.
Lemma l180 : s1 -> p227 (* BND(w8 - (c8 + x * c9), [-1.70068e-21, 1.70068e-21]) *).
Proof.
 intros h0.
 assert (h1 := l181 h0).
 apply t144. exact h1.
Qed.
Definition f162 := Float2 (-19239322403717923669244394234898405402658161877749566483094546308000300467679140333246202529559048472918300083749) (-378).
Definition f163 := Float2 (19239322403717923669244394234898405402658161877749566483094546308000300467679140333246202529559048472918300083749) (-378).
Definition i138 := makepairF f162 f163.
Notation p235 := (BND _x i138). (* BND(x, [-0.0312501, 0.0312501]) *)
Lemma t145 : p235 -> p227 -> p226.
Proof.
 intros h0 h1.
 refine (mul_oo _x r122 i138 i132 i131 h0 h1 _) ; finalize.
Qed.
Lemma l179 : s1 -> p226 (* BND(x * (w8 - (c8 + x * c9)), [-5.31465e-23, 5.31465e-23]) *).
Proof.
 intros h0.
 assert (h1 := l72 h0).
 assert (h2 := l180 h0).
 apply t145. refine (subset _x i43 i138 h1 _) ; finalize. exact h2.
Qed.
Lemma t146 : p226 -> p225.
Proof.
 intros h0.
 refine (mul_fils _ _ _ i131 h0) ; finalize.
Qed.
Lemma l178 : s1 -> p225 (* BND(x * w8 - x * (c8 + x * c9), [-5.31465e-23, 5.31465e-23]) *).
Proof.
 intros h0.
 assert (h1 := l179 h0).
 apply t146. exact h1.
Qed.
Lemma t147 : p221 -> p225 -> p220.
Proof.
 intros h0 h1.
 refine (add r119 r120 i128 i131 i127 h0 h1 _) ; finalize.
Qed.
Lemma l174 : s1 -> p220 (* BND(float<53,-1074,ne>(x * w8) - x * w8 + (x * w8 - x * (c8 + x * c9)), [-1.06086e-22, 1.06086e-22]) *).
Proof.
 intros h0.
 assert (h1 := l175 h0).
 assert (h2 := l178 h0).
 apply t147. exact h1. exact h2.
Qed.
Lemma t148 : p220 -> p219.
Proof.
 intros h0.
 refine (sub_xals _ _ _ i127 h0) ; finalize.
Qed.
Lemma l173 : s1 -> p219 (* BND(float<53,-1074,ne>(x * w8) - x * (c8 + x * c9), [-1.06086e-22, 1.06086e-22]) *).
Proof.
 intros h0.
 assert (h1 := l174 h0).
 apply t148. exact h1.
Qed.
Lemma t149 : p219 -> p218.
Proof.
 intros h0.
 refine (add_fils _ _ _ i127 h0) ; finalize.
Qed.
Lemma l172 : s1 -> p218 (* BND(c7 + float<53,-1074,ne>(x * w8) - (c7 + x * (c8 + x * c9)), [-1.06086e-22, 1.06086e-22]) *).
Proof.
 intros h0.
 assert (h1 := l173 h0).
 apply t149. exact h1.
Qed.
Lemma t150 : p214 -> p218 -> p213.
Proof.
 intros h0 h1.
 refine (add r115 r116 i123 i127 i122 h0 h1 _) ; finalize.
Qed.
Lemma l168 : s1 -> p213 (* BND(w7 - (c7 + float<53,-1074,ne>(x * w8)) + (c7 + float<53,-1074,ne>(x * w8) - (c7 + x * (c8 + x * c9))), [-1.36586e-20, 1.36586e-20]) *).
Proof.
 intros h0.
 assert (h1 := l169 h0).
 assert (h2 := l172 h0).
 apply t150. exact h1. exact h2.
Qed.
Lemma t151 : p213 -> p212.
Proof.
 intros h0.
 refine (sub_xals _ _ _ i122 h0) ; finalize.
Qed.
Lemma l167 : s1 -> p212 (* BND(w7 - (c7 + x * (c8 + x * c9)), [-1.36586e-20, 1.36586e-20]) *).
Proof.
 intros h0.
 assert (h1 := l168 h0).
 apply t151. exact h1.
Qed.
Definition f164 := Float2 (-76957289614871694676977576939593621610632647510998265932378185232001201870716561332984810118236193891673200334993) (-380).
Definition f165 := Float2 (76957289614871694676977576939593621610632647510998265932378185232001201870716561332984810118236193891673200334993) (-380).
Definition i139 := makepairF f164 f165.
Notation p236 := (BND _x i139). (* BND(x, [-0.0312501, 0.0312501]) *)
Lemma t152 : p236 -> p212 -> p211.
Proof.
 intros h0 h1.
 refine (mul_oo _x r113 i139 i122 i121 h0 h1 _) ; finalize.
Qed.
Lemma l166 : s1 -> p211 (* BND(x * (w7 - (c7 + x * (c8 + x * c9))), [-4.26833e-22, 4.26833e-22]) *).
Proof.
 intros h0.
 assert (h1 := l72 h0).
 assert (h2 := l167 h0).
 apply t152. refine (subset _x i43 i139 h1 _) ; finalize. exact h2.
Qed.
Lemma t153 : p211 -> p210.
Proof.
 intros h0.
 refine (mul_fils _ _ _ i121 h0) ; finalize.
Qed.
Lemma l165 : s1 -> p210 (* BND(x * w7 - x * (c7 + x * (c8 + x * c9)), [-4.26833e-22, 4.26833e-22]) *).
Proof.
 intros h0.
 assert (h1 := l166 h0).
 apply t153. exact h1.
Qed.
Lemma t154 : p205 -> p210 -> p204.
Proof.
 intros h0 h1.
 refine (add r110 r111 i117 i121 i116 h0 h1 _) ; finalize.
Qed.
Lemma l161 : s1 -> p204 (* BND(float<53,-1074,ne>(x * w7) - x * w7 + (x * w7 - x * (c7 + x * (c8 + x * c9))), [-8.5035e-22, 8.5035e-22]) *).
Proof.
 intros h0.
 assert (h1 := l162 h0).
 assert (h2 := l165 h0).
 apply t154. exact h1. exact h2.
Qed.
Lemma t155 : p204 -> p203.
Proof.
 intros h0.
 refine (sub_xals _ _ _ i116 h0) ; finalize.
Qed.
Lemma l160 : s1 -> p203 (* BND(float<53,-1074,ne>(x * w7) - x * (c7 + x * (c8 + x * c9)), [-8.5035e-22, 8.5035e-22]) *).
Proof.
 intros h0.
 assert (h1 := l161 h0).
 apply t155. exact h1.
Qed.
Lemma t156 : p203 -> p202.
Proof.
 intros h0.
 refine (add_fils _ _ _ i116 h0) ; finalize.
Qed.
Lemma l159 : s1 -> p202 (* BND(c6 + float<53,-1074,ne>(x * w7) - (c6 + x * (c7 + x * (c8 + x * c9))), [-8.5035e-22, 8.5035e-22]) *).
Proof.
 intros h0.
 assert (h1 := l160 h0).
 apply t156. exact h1.
Qed.
Lemma t157 : p198 -> p202 -> p197.
Proof.
 intros h0 h1.
 refine (add r106 r107 i87 i116 i112 h0 h1 _) ; finalize.
Qed.
Lemma l155 : s1 -> p197 (* BND(w6 - (c6 + float<53,-1074,ne>(x * w7)) + (c6 + float<53,-1074,ne>(x * w7) - (c6 + x * (c7 + x * (c8 + x * c9)))), [-1.09271e-19, 1.09271e-19]) *).
Proof.
 intros h0.
 assert (h1 := l156 h0).
 assert (h2 := l159 h0).
 apply t157. exact h1. exact h2.
Qed.
Lemma t158 : p197 -> p196.
Proof.
 intros h0.
 refine (sub_xals _ _ _ i112 h0) ; finalize.
Qed.
Lemma l154 : s1 -> p196 (* BND(w6 - (c6 + x * (c7 + x * (c8 + x * c9))), [-1.09271e-19, 1.09271e-19]) *).
Proof.
 intros h0.
 assert (h1 := l155 h0).
 apply t158. exact h1.
Qed.
Definition f166 := Float2 (-19701066141407153837306259696535967132321957762815556078688815419392307678903439701244111390268465636268339285758193) (-388).
Definition f167 := Float2 (19701066141407153837306259696535967132321957762815556078688815419392307678903439701244111390268465636268339285758193) (-388).
Definition i140 := makepairF f166 f167.
Notation p237 := (BND _x i140). (* BND(x, [-0.0312501, 0.0312501]) *)
Lemma t159 : p237 -> p196 -> p195.
Proof.
 intros h0 h1.
 refine (mul_oo _x r104 i140 i112 i111 h0 h1 _) ; finalize.
Qed.
Lemma l153 : s1 -> p195 (* BND(x * (w6 - (c6 + x * (c7 + x * (c8 + x * c9)))), [-3.41472e-21, 3.41472e-21]) *).
Proof.
 intros h0.
 assert (h1 := l72 h0).
 assert (h2 := l154 h0).
 apply t159. refine (subset _x i43 i140 h1 _) ; finalize. exact h2.
Qed.
Lemma t160 : p195 -> p194.
Proof.
 intros h0.
 refine (mul_fils _ _ _ i111 h0) ; finalize.
Qed.
Lemma l152 : s1 -> p194 (* BND(x * w6 - x * (c6 + x * (c7 + x * (c8 + x * c9))), [-3.41472e-21, 3.41472e-21]) *).
Proof.
 intros h0.
 assert (h1 := l153 h0).
 apply t160. exact h1.
Qed.
Lemma t161 : p192 -> p194 -> p191.
Proof.
 intros h0 h1.
 refine (add r101 r102 i109 i111 i108 h0 h1 _) ; finalize.
Qed.
Lemma l149 : s1 -> p191 (* BND(float<53,-1074,ne>(x * w6) - x * w6 + (x * w6 - x * (c6 + x * (c7 + x * (c8 + x * c9)))), [-6.80285e-21, 6.80285e-21]) *).
Proof.
 intros h0.
 assert (h1 := l150 h0).
 assert (h2 := l152 h0).
 apply t161. exact h1. exact h2.
Qed.
Lemma t162 : p191 -> p190.
Proof.
 intros h0.
 refine (sub_xals _ _ _ i108 h0) ; finalize.
Qed.
Lemma l148 : s1 -> p190 (* BND(float<53,-1074,ne>(x * w6) - x * (c6 + x * (c7 + x * (c8 + x * c9))), [-6.80285e-21, 6.80285e-21]) *).
Proof.
 intros h0.
 assert (h1 := l149 h0).
 apply t162. exact h1.
Qed.
Lemma t163 : p190 -> p189.
Proof.
 intros h0.
 refine (add_fils _ _ _ i108 h0) ; finalize.
Qed.
Lemma l147 : s1 -> p189 (* BND(c5 + float<53,-1074,ne>(x * w6) - (c5 + x * (c6 + x * (c7 + x * (c8 + x * c9)))), [-6.80285e-21, 6.80285e-21]) *).
Proof.
 intros h0.
 assert (h1 := l148 h0).
 apply t163. exact h1.
Qed.
Lemma t164 : p184 -> p189 -> p183.
Proof.
 intros h0 h1.
 refine (add r97 r98 i103 i108 i102 h0 h1 _) ; finalize.
Qed.
Lemma l143 : s1 -> p183 (* BND(w5 - (c5 + float<53,-1074,ne>(x * w6)) + (c5 + float<53,-1074,ne>(x * w6) - (c5 + x * (c6 + x * (c7 + x * (c8 + x * c9))))), [-8.74165e-19, 8.74165e-19]) *).
Proof.
 intros h0.
 assert (h1 := l144 h0).
 assert (h2 := l147 h0).
 apply t164. exact h1. exact h2.
Qed.
Lemma t165 : p183 -> p182.
Proof.
 intros h0.
 refine (sub_xals _ _ _ i102 h0) ; finalize.
Qed.
Lemma l142 : s1 -> p182 (* BND(w5 - (c5 + x * (c6 + x * (c7 + x * (c8 + x * c9)))), [-8.74165e-19, 8.74165e-19]) *).
Proof.
 intros h0.
 assert (h1 := l143 h0).
 apply t165. exact h1.
Qed.
Definition f168 := Float2 (-2521736466100115691175201241156603792937210593640391178072168373682215382899640281759246257954363601442347428577048639) (-395).
Definition f169 := Float2 (2521736466100115691175201241156603792937210593640391178072168373682215382899640281759246257954363601442347428577048639) (-395).
Definition i141 := makepairF f168 f169.
Notation p238 := (BND _x i141). (* BND(x, [-0.0312501, 0.0312501]) *)
Lemma t166 : p238 -> p182 -> p181.
Proof.
 intros h0 h1.
 refine (mul_oo _x r95 i141 i102 i101 h0 h1 _) ; finalize.
Qed.
Lemma l141 : s1 -> p181 (* BND(x * (w5 - (c5 + x * (c6 + x * (c7 + x * (c8 + x * c9))))), [-2.73177e-20, 2.73177e-20]) *).
Proof.
 intros h0.
 assert (h1 := l72 h0).
 assert (h2 := l142 h0).
 apply t166. refine (subset _x i43 i141 h1 _) ; finalize. exact h2.
Qed.
Lemma t167 : p181 -> p180.
Proof.
 intros h0.
 refine (mul_fils _ _ _ i101 h0) ; finalize.
Qed.
Lemma l140 : s1 -> p180 (* BND(x * w5 - x * (c5 + x * (c6 + x * (c7 + x * (c8 + x * c9)))), [-2.73177e-20, 2.73177e-20]) *).
Proof.
 intros h0.
 assert (h1 := l141 h0).
 apply t167. exact h1.
Qed.
Lemma t168 : p176 -> p180 -> p175.
Proof.
 intros h0 h1.
 refine (add r92 r93 i98 i101 i97 h0 h1 _) ; finalize.
Qed.
Lemma l136 : s1 -> p175 (* BND(float<53,-1074,ne>(x * w5) - x * w5 + (x * w5 - x * (c5 + x * (c6 + x * (c7 + x * (c8 + x * c9))))), [-5.44228e-20, 5.44228e-20]) *).
Proof.
 intros h0.
 assert (h1 := l137 h0).
 assert (h2 := l140 h0).
 apply t168. exact h1. exact h2.
Qed.
Lemma t169 : p175 -> p174.
Proof.
 intros h0.
 refine (sub_xals _ _ _ i97 h0) ; finalize.
Qed.
Lemma l135 : s1 -> p174 (* BND(float<53,-1074,ne>(x * w5) - x * (c5 + x * (c6 + x * (c7 + x * (c8 + x * c9)))), [-5.44228e-20, 5.44228e-20]) *).
Proof.
 intros h0.
 assert (h1 := l136 h0).
 apply t169. exact h1.
Qed.
Lemma t170 : p174 -> p173.
Proof.
 intros h0.
 refine (add_fils _ _ _ i97 h0) ; finalize.
Qed.
Lemma l134 : s1 -> p173 (* BND(c4 + float<53,-1074,ne>(x * w5) - (c4 + x * (c5 + x * (c6 + x * (c7 + x * (c8 + x * c9))))), [-5.44228e-20, 5.44228e-20]) *).
Proof.
 intros h0.
 assert (h1 := l135 h0).
 apply t170. exact h1.
Qed.
Lemma t171 : p168 -> p173 -> p167.
Proof.
 intros h0 h1.
 refine (add r88 r89 i92 i97 i91 h0 h1 _) ; finalize.
Qed.
Lemma l130 : s1 -> p167 (* BND(w4 - (c4 + float<53,-1074,ne>(x * w5)) + (c4 + float<53,-1074,ne>(x * w5) - (c4 + x * (c5 + x * (c6 + x * (c7 + x * (c8 + x * c9)))))), [-3.52387e-18, 3.52387e-18]) *).
Proof.
 intros h0.
 assert (h1 := l131 h0).
 assert (h2 := l134 h0).
 apply t171. exact h1. exact h2.
Qed.
Lemma t172 : p167 -> p166.
Proof.
 intros h0.
 refine (sub_xals _ _ _ i91 h0) ; finalize.
Qed.
Lemma l129 : s1 -> p166 (* BND(w4 - (c4 + x * (c5 + x * (c6 + x * (c7 + x * (c8 + x * c9))))), [-3.52387e-18, 3.52387e-18]) *).
Proof.
 intros h0.
 assert (h1 := l130 h0).
 apply t172. exact h1.
Qed.
Lemma t173 : p86 -> p166 -> p165.
Proof.
 intros h0 h1.
 refine (mul_oo _x r86 i43 i91 i90 h0 h1 _) ; finalize.
Qed.
Lemma l128 : s1 -> p165 (* BND(x * (w4 - (c4 + x * (c5 + x * (c6 + x * (c7 + x * (c8 + x * c9)))))), [-1.10121e-19, 1.10121e-19]) *).
Proof.
 intros h0.
 assert (h1 := l72 h0).
 assert (h2 := l129 h0).
 apply t173. exact h1. exact h2.
Qed.
Lemma t174 : p165 -> p164.
Proof.
 intros h0.
 refine (mul_fils _ _ _ i90 h0) ; finalize.
Qed.
Lemma l127 : s1 -> p164 (* BND(x * w4 - x * (c4 + x * (c5 + x * (c6 + x * (c7 + x * (c8 + x * c9))))), [-1.10121e-19, 1.10121e-19]) *).
Proof.
 intros h0.
 assert (h1 := l128 h0).
 apply t174. exact h1.
Qed.
Lemma t175 : p160 -> p164 -> p159.
Proof.
 intros h0 h1.
 refine (add r83 r84 i87 i90 i86 h0 h1 _) ; finalize.
Qed.
Lemma l123 : s1 -> p159 (* BND(float<53,-1074,ne>(x * w4) - x * w4 + (x * w4 - x * (c4 + x * (c5 + x * (c6 + x * (c7 + x * (c8 + x * c9)))))), [-2.18541e-19, 2.18541e-19]) *).
Proof.
 intros h0.
 assert (h1 := l124 h0).
 assert (h2 := l127 h0).
 apply t175. exact h1. exact h2.
Qed.
Lemma t176 : p159 -> p158.
Proof.
 intros h0.
 refine (sub_xals _ _ _ i86 h0) ; finalize.
Qed.
Lemma l122 : s1 -> p158 (* BND(float<53,-1074,ne>(x * w4) - x * (c4 + x * (c5 + x * (c6 + x * (c7 + x * (c8 + x * c9))))), [-2.18541e-19, 2.18541e-19]) *).
Proof.
 intros h0.
 assert (h1 := l123 h0).
 apply t176. exact h1.
Qed.
Lemma t177 : p158 -> p157.
Proof.
 intros h0.
 refine (add_fils _ _ _ i86 h0) ; finalize.
Qed.
Lemma l121 : s1 -> p157 (* BND(c3 + float<53,-1074,ne>(x * w4) - W, [-2.18541e-19, 2.18541e-19]) *).
Proof.
 intros h0.
 assert (h1 := l122 h0).
 apply t177. exact h1.
Qed.
Definition f170 := Float2 (426991539913615079245951986782130473812508782603361192983647754617908889936448143173715292738383925558847308867868809227) (-400).
Definition i142 := makepairF f170 f8.
Notation p239 := (BND _W i142). (* BND(W, [0.165356, 1]) *)
Definition f171 := Float2 (-3383439767536328472757291988459925963057856804770425857243500969270674799808312317445640219922295617776624897113204725) (-400).
Definition i143 := makepairF f171 f14.
Notation p240 := (BND r8 i143). (* BND(x * (c4 + x * (c5 + x * (c6 + x * (c7 + x * (c8 + x * c9))))), [-0.00131027, 0.5]) *)
Definition f172 := Float2 (6766857881127437337715103288589328440264704762485611760529368244562966998122230643753220429539216710059777602938080047) (-396).
Definition i144 := makepairF f13 f172.
Notation p241 := (BND r9 i144). (* BND(c4 + x * (c5 + x * (c6 + x * (c7 + x * (c8 + x * c9)))), [0.03125, 0.0419284]) *)
Definition f173 := Float2 (42248823609442112620786452190432328886914884844998972849447906714216499140021599120088491743791242420042094646004527) (-396).
Definition i145 := makepairF f88 f173.
Notation p242 := (BND r11 i145). (* BND(x * (c5 + x * (c6 + x * (c7 + x * (c8 + x * c9)))), [-0.0078125, 0.00026178]) *)
Definition f174 := Float2 (42248688413639188975381730968893228428583913376476168125709904442522283068715779229594957039928714648155220549298769) (-391).
Definition i146 := makepairF f17 f174.
Notation p243 := (BND r12 i146). (* BND(c5 + x * (c6 + x * (c7 + x * (c8 + x * c9))), [0.0078125, 0.00837693]) *)
Definition f175 := Float2 (219881803769527375896566369782974183315101954325986789033845962676298997395323153369780277386921676906573289482833) (-391).
Definition i147 := makepairF f91 f175.
Notation p244 := (BND r14 i147). (* BND(x * (c6 + x * (c7 + x * (c8 + x * c9))), [-0.000488281, 4.35974e-05]) *)
Definition f176 := Float2 (1759048801200055166995996571074766027269528372117103537539447575178151409078076177114475452773924538694062494862679) (-389).
Definition i148 := makepairF f21 f176.
Notation p245 := (BND r15 i148). (* BND(c6 + x * (c7 + x * (c8 + x * c9)), [0.000976562, 0.00139511]) *)
Definition f177 := Float2 (7848526083832637306434117829805855253057045890304114075520820442576593397714487451731013050509523211619952119127) (-389).
Definition i149 := makepairF f53 f177.
Notation p246 := (BND r17 i149). (* BND(x * (c7 + x * (c8 + x * c9)), [-0.000244141, 6.22472e-06]) *)
Definition f178 := Float2 (31394003874518150767654014826375976609103034431506275482001739364740406421557400823241417829501038443156790374777) (-386).
Definition i150 := makepairF f27 f178.
Notation p247 := (BND r18 i150). (* BND(c7 + x * (c8 + x * c9), [0.00012207, 0.00019919]) *)
Definition f179 := Float2 (122594847883555046952642389200191991758446609998392378741456387661764503022162864749346989642471605265988645241) (-386).
Definition i151 := makepairF f69 f179.
Notation p248 := (BND r20 i151). (* BND(x * (c8 + x * c9), [-6.10352e-05, 7.77846e-07]) *)
Definition f180 := Float2 (980755644650377494413156991499163136745535294274197352500123100900193143559243528415484987587812561127713553239) (-384).
Definition i152 := makepairF f34 f180.
Notation p249 := (BND r21 i152). (* BND(c8 + x * c9, [1.52588e-05, 2.4891e-05]) *)
Definition i153 := makepairF f66 f62.
Notation p250 := (BND r23 i153). (* BND(x * c9, [-7.62939e-06, 8.89559e-08]) *)
Lemma t178 : p37 -> p250 -> p249.
Proof.
 intros h0 h1.
 refine (add _c8 r23 i26 i153 i152 h0 h1 _) ; finalize.
Qed.
Lemma l197 : s1 -> p249 (* BND(c8 + x * c9, [1.52588e-05, 2.4891e-05]) *).
Proof.
 intros h0.
 assert (h1 := l34 h0).
 assert (h2 := l80 h0).
 apply t178. exact h1. refine (subset r23 i48 i153 h2 _) ; finalize.
Qed.
Definition f181 := Float2 (150307206279046278665971829960143792208266889669918488149176143031252347403743283853485957262180066194674219405) (-371).
Definition i154 := makepairF f63 f181.
Notation p251 := (BND _x i154). (* BND(x, [-1, 0.0312501]) *)
Lemma t179 : p251 -> p249 -> p248.
Proof.
 intros h0 h1.
 refine (mul_op _x r21 i154 i152 i151 h0 h1 _) ; finalize.
Qed.
Lemma l196 : s1 -> p248 (* BND(x * (c8 + x * c9), [-6.10352e-05, 7.77846e-07]) *).
Proof.
 intros h0.
 assert (h1 := l72 h0).
 assert (h2 := l197 h0).
 apply t179. refine (subset _x i43 i154 h1 _) ; finalize. exact h2.
Qed.
Lemma t180 : p32 -> p248 -> p247.
Proof.
 intros h0 h1.
 refine (add _c7 r20 i22 i151 i150 h0 h1 _) ; finalize.
Qed.
Lemma l195 : s1 -> p247 (* BND(c7 + x * (c8 + x * c9), [0.00012207, 0.00019919]) *).
Proof.
 intros h0.
 assert (h1 := l30 h0).
 assert (h2 := l196 h0).
 apply t180. exact h1. exact h2.
Qed.
Definition i155 := makepairF f63 f163.
Notation p252 := (BND _x i155). (* BND(x, [-1, 0.0312501]) *)
Lemma t181 : p252 -> p247 -> p246.
Proof.
 intros h0 h1.
 refine (mul_op _x r18 i155 i150 i149 h0 h1 _) ; finalize.
Qed.
Lemma l194 : s1 -> p246 (* BND(x * (c7 + x * (c8 + x * c9)), [-0.000244141, 6.22472e-06]) *).
Proof.
 intros h0.
 assert (h1 := l72 h0).
 assert (h2 := l195 h0).
 apply t181. refine (subset _x i43 i155 h1 _) ; finalize. exact h2.
Qed.
Lemma t182 : p27 -> p246 -> p245.
Proof.
 intros h0 h1.
 refine (add _c6 r17 i18 i149 i148 h0 h1 _) ; finalize.
Qed.
Lemma l193 : s1 -> p245 (* BND(c6 + x * (c7 + x * (c8 + x * c9)), [0.000976562, 0.00139511]) *).
Proof.
 intros h0.
 assert (h1 := l26 h0).
 assert (h2 := l194 h0).
 apply t182. exact h1. exact h2.
Qed.
Definition i156 := makepairF f93 f165.
Notation p253 := (BND _x i156). (* BND(x, [-0.25, 0.0312501]) *)
Lemma t183 : p253 -> p245 -> p244.
Proof.
 intros h0 h1.
 refine (mul_op _x r15 i156 i148 i147 h0 h1 _) ; finalize.
Qed.
Lemma l192 : s1 -> p244 (* BND(x * (c6 + x * (c7 + x * (c8 + x * c9))), [-0.000488281, 4.35974e-05]) *).
Proof.
 intros h0.
 assert (h1 := l72 h0).
 assert (h2 := l193 h0).
 apply t183. refine (subset _x i43 i156 h1 _) ; finalize. exact h2.
Qed.
Definition i157 := makepairF f47 f18.
Notation p254 := (BND _c5 i157). (* BND(c5, [0.00830078, 0.00833333]) *)
Lemma t184 : p254 -> p244 -> p243.
Proof.
 intros h0 h1.
 refine (add _c5 r14 i157 i147 i146 h0 h1 _) ; finalize.
Qed.
Lemma l191 : s1 -> p243 (* BND(c5 + x * (c6 + x * (c7 + x * (c8 + x * c9))), [0.0078125, 0.00837693]) *).
Proof.
 intros h0.
 assert (h1 := l22 h0).
 assert (h2 := l192 h0).
 apply t184. refine (subset _c5 i14 i157 h1 _) ; finalize. exact h2.
Qed.
Definition f182 := Float2 (39402132282814307674612519393071934264643915525631112157377630838784615357806879402488222780536931272536678571516385) (-389).
Definition i158 := makepairF f80 f182.
Notation p255 := (BND _x i158). (* BND(x, [-0.5, 0.0312501]) *)
Lemma t185 : p255 -> p243 -> p242.
Proof.
 intros h0 h1.
 refine (mul_op _x r12 i158 i146 i145 h0 h1 _) ; finalize.
Qed.
Lemma l190 : s1 -> p242 (* BND(x * (c5 + x * (c6 + x * (c7 + x * (c8 + x * c9)))), [-0.0078125, 0.00026178]) *).
Proof.
 intros h0.
 assert (h1 := l72 h0).
 assert (h2 := l191 h0).
 apply t185. refine (subset _x i43 i158 h1 _) ; finalize. exact h2.
Qed.
Lemma t186 : p145 -> p242 -> p241.
Proof.
 intros h0 h1.
 refine (add _c4 r11 i77 i145 i144 h0 h1 _) ; finalize.
Qed.
Lemma l189 : s1 -> p241 (* BND(c4 + x * (c5 + x * (c6 + x * (c7 + x * (c8 + x * c9)))), [0.03125, 0.0419284]) *).
Proof.
 intros h0.
 assert (h1 := l18 h0).
 assert (h2 := l190 h0).
 apply t186. refine (subset _c4 i11 i77 h1 _) ; finalize. exact h2.
Qed.
Definition i159 := makepairF f168 f8.
Notation p256 := (BND _x i159). (* BND(x, [-0.0312501, 1]) *)
Lemma t187 : p256 -> p241 -> p240.
Proof.
 intros h0 h1.
 refine (mul_op _x r9 i159 i144 i143 h0 h1 _) ; finalize.
Qed.
Lemma l188 : s1 -> p240 (* BND(x * (c4 + x * (c5 + x * (c6 + x * (c7 + x * (c8 + x * c9))))), [-0.00131027, 0.5]) *).
Proof.
 intros h0.
 assert (h1 := l72 h0).
 assert (h2 := l189 h0).
 apply t187. refine (subset _x i43 i159 h1 _) ; finalize. exact h2.
Qed.
Lemma t188 : p153 -> p240 -> p239.
Proof.
 intros h0 h1.
 refine (add _c3 r8 i83 i143 i142 h0 h1 _) ; finalize.
Qed.
Lemma l187 : s1 -> p239 (* BND(W, [0.165356, 1]) *).
Proof.
 intros h0.
 assert (h1 := l14 h0).
 assert (h2 := l188 h0).
 apply t188. refine (subset _c3 i8 i83 h1 _) ; finalize. exact h2.
Qed.
Lemma t189 : p157 -> p239 -> p156.
Proof.
 intros h0 h1.
 refine (div_op r80 _W i86 i142 i85 h0 h1 _) ; finalize.
Qed.
Lemma l120 : s1 -> p156 (* BND((c3 + float<53,-1074,ne>(x * w4) - W) / W, [-1.32164e-18, 1.32164e-18]) *).
Proof.
 intros h0.
 assert (h1 := l121 h0).
 assert (h2 := l187 h0).
 apply t189. exact h1. exact h2.
Qed.
Lemma t190 : p12 -> p156 -> p155.
Proof.
 intros h0 h1.
 refine (rel_of_nzr_bnd r29 _W i85 h0 h1) ; finalize.
Qed.
Lemma l119 : s1 -> p155 (* REL(c3 + float<53,-1074,ne>(x * w4), W, [-1.32164e-18, 1.32164e-18]) *).
Proof.
 intros h0.
 assert (h1 := l11 h0).
 assert (h2 := l120 h0).
 apply t190. exact h1. exact h2.
Qed.
Lemma t191 : p128 -> p155 -> p127.
Proof.
 intros h0 h1.
 refine (compose _w r29 _W i66 i85 i65 h0 h1 _) ; finalize.
Qed.
Lemma l101 : s1 -> p127 (* REL(w, W, [-8.52482e-17, 8.52482e-17]) *).
Proof.
 intros h0.
 assert (h1 := l102 h0).
 assert (h2 := l119 h0).
 apply t191. exact h1. exact h2.
Qed.
Lemma t192 : p107 -> p127 -> p106.
Proof.
 intros h0 h1.
 refine (mul_rr _x3 r2 _w _W i59 i65 i58 h0 h1 _) ; finalize.
Qed.
Lemma l81 : s1 -> p106 (* REL(x3 * w, T, [-3.07293e-16, 3.07293e-16]) *).
Proof.
 intros h0.
 assert (h1 := l82 h0).
 assert (h2 := l101 h0).
 apply t192. exact h1. exact h2.
Qed.
Lemma t193 : p53 -> p106 -> p52.
Proof.
 intros h0 h1.
 refine (compose _t r54 _T i39 i58 i3 h0 h1 _) ; finalize.
Qed.
Lemma l38 : s1 -> p52 (* REL(t, T, [-4.18315e-16, 4.18315e-16]) *).
Proof.
 intros h0.
 assert (h1 := l39 h0).
 assert (h2 := l81 h0).
 apply t193. exact h1. exact h2.
Qed.
Lemma t194 : p4 -> p52 -> p3.
Proof.
 intros h0 h1.
 refine (bnd_of_nzr_rel _t _T i3 h0 h1) ; finalize.
Qed.
Lemma l3 : s1 -> p3 (* BND((t - T) / T, [-4.18315e-16, 4.18315e-16]) *).
Proof.
 intros h0.
 assert (h1 := l4 h0).
 assert (h2 := l38 h0).
 apply t194. exact h1. exact h2.
Qed.
Lemma l1 : s1 -> False.
Proof.
 intros h0.
 assert (h1 := l2 h0).
 assert (h2 := l3 h0).
 refine (simplify (Tatom false (Abnd 0%nat i2)) Tfalse (Abnd 0%nat i3) (List.cons r51 List.nil) h2 h1 _) ; finalize.
Qed.
End Generated_by_Gappa.
