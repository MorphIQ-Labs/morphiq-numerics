Require Import Gappa.Gappa_library.
Section Generated_by_Gappa.
Variable _r_ : R.
Notation _r := ((rounding_float rndNE (53)%positive (-1074)%Z) _r_).
Definition f1 := Float2 (-1789941246693356131382101079560334144543371360062384257457043542964508560930560231090864825107617076781822724800155747281) (-408).
Definition f2 := Float2 (1789941246693356131382101079560334144543371360062384257457043542964508560930560231090864825107617076781822724800155747281) (-408).
Definition i1 := makepairF f1 f2.
Notation p1 := (BND _r i1). (* BND(r, [-0.0027077, 0.0027077]) *)
Notation r7 := ((_r * _r)%R).
Notation _r2 := ((rounding_float rndNE (53)%positive (-1074)%Z) r7).
Notation r10 := (float10R (Float10 (5) (-1))).
Notation _c3 := (float2R (Float2 (375299968947529) (-51))).
Notation _c4 := (float2R (Float2 (6004799503160511) (-57))).
Notation _c5 := (float2R (Float2 (4803840849707593) (-59))).
Notation _c6 := (float2R (Float2 (3202560482380763) (-61))).
Notation r27 := ((_r * _c6)%R).
Notation r26 := ((rounding_float rndNE (53)%positive (-1074)%Z) r27).
Notation r24 := ((_c5 + r26)%R).
Notation _t5 := ((rounding_float rndNE (53)%positive (-1074)%Z) r24).
Notation r22 := ((_r * _t5)%R).
Notation r21 := ((rounding_float rndNE (53)%positive (-1074)%Z) r22).
Notation r19 := ((_c4 + r21)%R).
Notation _t4 := ((rounding_float rndNE (53)%positive (-1074)%Z) r19).
Notation r17 := ((_r * _t4)%R).
Notation r16 := ((rounding_float rndNE (53)%positive (-1074)%Z) r17).
Notation r14 := ((_c3 + r16)%R).
Notation _t3 := ((rounding_float rndNE (53)%positive (-1074)%Z) r14).
Notation r12 := ((_r * _t3)%R).
Notation r11 := ((rounding_float rndNE (53)%positive (-1074)%Z) r12).
Notation r9 := ((r10 + r11)%R).
Notation _h := ((rounding_float rndNE (53)%positive (-1074)%Z) r9).
Notation r5 := ((_r2 * _h)%R).
Notation _q := ((rounding_float rndNE (53)%positive (-1074)%Z) r5).
Notation _T5 := ((_c5 + r27)%R).
Notation r35 := ((_r * _T5)%R).
Notation _T4 := ((_c4 + r35)%R).
Notation r33 := ((_r * _T4)%R).
Notation _T3 := ((_c3 + r33)%R).
Notation r31 := ((_r * _T3)%R).
Notation _H := ((r10 + r31)%R).
Notation _Q := ((r7 * _H)%R).
Notation r3 := ((_q - _Q)%R).
Definition f3 := Float2 (-1) (-70).
Definition f4 := Float2 (1) (-70).
Definition i2 := makepairF f3 f4.
Notation p2 := (BND r3 i2). (* BND(q - Q, [-8.47033e-22, 8.47033e-22]) *)
Definition s2 := (not p2).
Definition s1 := (p1 /\ s2).
Lemma l2 : s1 -> s2.
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj2 h1).
Qed.
Definition f5 := Float2 (-1267505508114920192223328404669752302728462255273511993929679536241229421444424885017842914636248027076494467256261755129) (-469).
Definition f6 := Float2 (1267505508114920192223328404669752302728462255273511993929679536241229421444424885017842914636248027076494467256261755129) (-469).
Definition i3 := makepairF f5 f6.
Notation p3 := (BND r3 i3). (* BND(q - Q, [-8.31538e-22, 8.31538e-22]) *)
Notation r38 := ((_q - r5)%R).
Notation r39 := ((r5 - _Q)%R).
Notation r37 := ((r38 + r39)%R).
Notation p4 := (BND r37 i3). (* BND(q - r2 * h + (r2 * h - Q), [-8.31538e-22, 8.31538e-22]) *)
Definition f7 := Float2 (-1) (-72).
Definition f8 := Float2 (1) (-72).
Definition i4 := makepairF f7 f8.
Notation p5 := (BND r38 i4). (* BND(q - r2 * h, [-2.11758e-22, 2.11758e-22]) *)
Definition f9 := Float2 (0) (0).
Definition f10 := Float2 (1) (-18).
Definition i5 := makepairF f9 f10.
Notation p6 := (ABS r5 i5). (* ABS(r2 * h, [0, 3.8147e-06]) *)
Definition f11 := Float2 (31) (-22).
Definition i6 := makepairF f9 f11.
Notation p7 := (ABS _r2 i6). (* ABS(r2, [0, 7.39098e-06]) *)
Definition f12 := Float2 (8655671911896551) (-70).
Definition i7 := makepairF f9 f12.
Notation p8 := (BND _r2 i7). (* BND(r2, [0, 7.33164e-06]) *)
Notation p9 := (BND r7 i7). (* BND(r * r, [0, 7.33164e-06]) *)
Definition f13 := Float2 (49948248928383353) (-64).
Definition i8 := makepairF f9 f13.
Notation p10 := (ABS _r i8). (* ABS(r, [0, 0.0027077]) *)
Lemma l11 : s1 -> p1 (* BND(r, [-0.0027077, 0.0027077]) *).
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj1 h1).
Qed.
Definition f14 := Float2 (-49948248928383353) (-64).
Definition i9 := makepairF f14 f13.
Notation p11 := (BND _r i9). (* BND(r, [-0.0027077, 0.0027077]) *)
Lemma t1 : p11 -> p10.
Proof.
 intros h0.
 refine (abs_of_bnd_o _r i9 i8 h0 _) ; finalize.
Qed.
Lemma l10 : s1 -> p10 (* ABS(r, [0, 0.0027077]) *).
Proof.
 intros h0.
 assert (h1 := l11 h0).
 apply t1. refine (subset _r i1 i9 h1 _) ; finalize.
Qed.
Lemma t2 : p10 -> p9.
Proof.
 intros h0.
 refine (square _r i8 i7 h0 _) ; finalize.
Qed.
Lemma l9 : s1 -> p9 (* BND(r * r, [0, 7.33164e-06]) *).
Proof.
 intros h0.
 assert (h1 := l10 h0).
 apply t2. exact h1.
Qed.
Lemma t3 : p9 -> p8.
Proof.
 intros h0.
 refine (float_round_ne _ _ r7 i7 i7 h0 _) ; finalize.
Qed.
Lemma l8 : s1 -> p8 (* BND(r2, [0, 7.33164e-06]) *).
Proof.
 intros h0.
 assert (h1 := l9 h0).
 apply t3. exact h1.
Qed.
Notation p12 := (BND _r2 i6). (* BND(r2, [0, 7.39098e-06]) *)
Lemma t4 : p12 -> p7.
Proof.
 intros h0.
 refine (abs_of_bnd_p _r2 i6 i6 h0 _) ; finalize.
Qed.
Lemma l7 : s1 -> p7 (* ABS(r2, [0, 7.39098e-06]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 apply t4. refine (subset _r2 i7 i6 h1 _) ; finalize.
Qed.
Definition f15 := Float2 (1) (-2).
Definition f16 := Float2 (33) (-6).
Definition i10 := makepairF f15 f16.
Notation p13 := (ABS _h i10). (* ABS(h, [0.25, 0.515625]) *)
Notation p14 := (BND _h i10). (* BND(h, [0.25, 0.515625]) *)
Definition f17 := Float2 (2307925595816409893) (-62).
Definition i11 := makepairF f15 f17.
Notation p15 := (BND r9 i11). (* BND(5e-1 + float<53,-1074,ne>(r * t3), [0.25, 0.500452]) *)
Definition f18 := Float2 (1) (-1).
Definition i12 := makepairF f18 f18.
Notation p16 := (BND r10 i12). (* BND(5e-1, [0.5, 0.5]) *)
Lemma t5 : p16.
Proof.
 refine (constant10 _ i12 _) ; finalize.
Qed.
Lemma l15 : s1 -> p16 (* BND(5e-1, [0.5, 0.5]) *).
Proof.
 intros h0.
 apply t5.
Qed.
Definition f19 := Float2 (-1) (-2).
Definition f20 := Float2 (2082586602715941) (-62).
Definition i13 := makepairF f19 f20.
Notation p17 := (BND r11 i13). (* BND(float<53,-1074,ne>(r * t3), [-0.25, 0.000451589]) *)
Notation p18 := (BND r12 i13). (* BND(r * t3, [-0.25, 0.000451589]) *)
Definition f21 := Float2 (1) (-3).
Definition f22 := Float2 (6008866504309299) (-55).
Definition i14 := makepairF f21 f22.
Notation p19 := (BND _t3 i14). (* BND(t3, [0.125, 0.16678]) *)
Notation p20 := (BND r14 i14). (* BND(c3 + float<53,-1074,ne>(r * t4), [0.125, 0.16678]) *)
Definition f23 := Float2 (5) (-5).
Definition f24 := Float2 (375299968947529) (-51).
Definition i15 := makepairF f23 f24.
Notation p21 := (BND _c3 i15). (* BND(c3, [0.15625, 0.166667]) *)
Lemma t6 : p21.
Proof.
 refine (constant2 _ i15 _) ; finalize.
Qed.
Lemma l20 : s1 -> p21 (* BND(c3, [0.15625, 0.166667]) *).
Proof.
 intros h0.
 apply t6.
Qed.
Definition f25 := Float2 (-1) (-5).
Definition f26 := Float2 (4067001148835) (-55).
Definition i16 := makepairF f25 f26.
Notation p22 := (BND r16 i16). (* BND(float<53,-1074,ne>(r * t4), [-0.03125, 0.000112882]) *)
Notation p23 := (BND r17 i16). (* BND(r * t4, [-0.03125, 0.000112882]) *)
Definition f27 := Float2 (1) (-5).
Definition f28 := Float2 (23468956291519) (-49).
Definition i17 := makepairF f27 f28.
Notation p24 := (BND _t4 i17). (* BND(t4, [0.03125, 0.0416892]) *)
Notation p25 := (BND r19 i17). (* BND(c4 + float<53,-1074,ne>(r * t5), [0.03125, 0.0416892]) *)
Definition f29 := Float2 (5) (-7).
Definition f30 := Float2 (6004799503160511) (-57).
Definition i18 := makepairF f29 f30.
Notation p26 := (BND _c4 i18). (* BND(c4, [0.0390625, 0.0416667]) *)
Lemma t7 : p26.
Proof.
 refine (constant2 _ i18 _) ; finalize.
Qed.
Lemma l25 : s1 -> p26 (* BND(c4, [0.0390625, 0.0416667]) *).
Proof.
 intros h0.
 apply t7.
Qed.
Definition f31 := Float2 (-1) (-7).
Definition f32 := Float2 (50832929193) (-51).
Definition i19 := makepairF f31 f32.
Notation p27 := (BND r21 i19). (* BND(float<53,-1074,ne>(r * t5), [-0.0078125, 2.25744e-05]) *)
Notation p28 := (BND r22 i19). (* BND(r * t5, [-0.0078125, 2.25744e-05]) *)
Definition f33 := Float2 (1) (-7).
Definition f34 := Float2 (146667747283) (-44).
Definition i20 := makepairF f33 f34.
Notation p29 := (BND _t5 i20). (* BND(t5, [0.0078125, 0.0083371]) *)
Notation p30 := (BND r24 i20). (* BND(c5 + float<53,-1074,ne>(r * c6), [0.0078125, 0.0083371]) *)
Definition f35 := Float2 (17) (-11).
Definition f36 := Float2 (4803840849707593) (-59).
Definition i21 := makepairF f35 f36.
Notation p31 := (BND _c5 i21). (* BND(c5, [0.00830078, 0.00833334]) *)
Lemma t8 : p31.
Proof.
 refine (constant2 _ i21 _) ; finalize.
Qed.
Lemma l30 : s1 -> p31 (* BND(c5, [0.00830078, 0.00833334]) *).
Proof.
 intros h0.
 apply t8.
Qed.
Definition f37 := Float2 (-1) (-11).
Definition f38 := Float2 (529270815) (-47).
Definition i22 := makepairF f37 f38.
Notation p32 := (BND r26 i22). (* BND(float<53,-1074,ne>(r * c6), [-0.000488281, 3.7607e-06]) *)
Definition f39 := Float2 (1157647971737106754083350004922871445580156919185949286337987074365758968242902941047242694423568915051105311) (-377).
Definition i23 := makepairF f37 f39.
Notation p33 := (BND r27 i23). (* BND(r * c6, [-0.000488281, 3.7607e-06]) *)
Definition f40 := Float2 (1) (-10).
Definition f41 := Float2 (3202560482380763) (-61).
Definition i24 := makepairF f40 f41.
Notation p34 := (BND _c6 i24). (* BND(c6, [0.000976562, 0.00138889]) *)
Lemma t9 : p34.
Proof.
 refine (constant2 _ i24 _) ; finalize.
Qed.
Lemma l33 : s1 -> p34 (* BND(c6, [0.000976562, 0.00138889]) *).
Proof.
 intros h0.
 apply t9.
Qed.
Definition f42 := Float2 (813971040176218653588012366326590447235217361622919387381008865743073584294761636142932195574584091801545003) (-367).
Definition i25 := makepairF f19 f42.
Notation p35 := (BND _r i25). (* BND(r, [-0.25, 0.0027077]) *)
Lemma t10 : p35 -> p34 -> p33.
Proof.
 intros h0 h1.
 refine (mul_op _r _c6 i25 i24 i23 h0 h1 _) ; finalize.
Qed.
Lemma l32 : s1 -> p33 (* BND(r * c6, [-0.000488281, 3.7607e-06]) *).
Proof.
 intros h0.
 assert (h1 := l11 h0).
 assert (h2 := l33 h0).
 apply t10. refine (subset _r i1 i25 h1 _) ; finalize. exact h2.
Qed.
Notation p36 := (BND r27 i22). (* BND(r * c6, [-0.000488281, 3.7607e-06]) *)
Lemma t11 : p36 -> p32.
Proof.
 intros h0.
 refine (float_round_ne _ _ r27 i22 i22 h0 _) ; finalize.
Qed.
Lemma l31 : s1 -> p32 (* BND(float<53,-1074,ne>(r * c6), [-0.000488281, 3.7607e-06]) *).
Proof.
 intros h0.
 assert (h1 := l32 h0).
 apply t11. refine (subset r27 i23 i22 h1 _) ; finalize.
Qed.
Definition f43 := Float2 (1172812707449) (-47).
Definition i26 := makepairF f35 f43.
Notation p37 := (BND _c5 i26). (* BND(c5, [0.00830078, 0.00833334]) *)
Lemma t12 : p37 -> p32 -> p30.
Proof.
 intros h0 h1.
 refine (add _c5 r26 i26 i22 i20 h0 h1 _) ; finalize.
Qed.
Lemma l29 : s1 -> p30 (* BND(c5 + float<53,-1074,ne>(r * c6), [0.0078125, 0.0083371]) *).
Proof.
 intros h0.
 assert (h1 := l30 h0).
 assert (h2 := l31 h0).
 apply t12. refine (subset _c5 i21 i26 h1 _) ; finalize. exact h2.
Qed.
Lemma t13 : p30 -> p29.
Proof.
 intros h0.
 refine (float_round_ne _ _ r24 i20 i20 h0 _) ; finalize.
Qed.
Lemma l28 : s1 -> p29 (* BND(t5, [0.0078125, 0.0083371]) *).
Proof.
 intros h0.
 assert (h1 := l29 h0).
 apply t13. exact h1.
Qed.
Definition f44 := Float2 (-1) (-1).
Definition f45 := Float2 (95268724305) (-45).
Definition i27 := makepairF f44 f45.
Notation p38 := (BND _r i27). (* BND(r, [-0.5, 0.0027077]) *)
Lemma t14 : p38 -> p29 -> p28.
Proof.
 intros h0 h1.
 refine (mul_op _r _t5 i27 i20 i19 h0 h1 _) ; finalize.
Qed.
Lemma l27 : s1 -> p28 (* BND(r * t5, [-0.0078125, 2.25744e-05]) *).
Proof.
 intros h0.
 assert (h1 := l11 h0).
 assert (h2 := l28 h0).
 apply t14. refine (subset _r i1 i27 h1 _) ; finalize. exact h2.
Qed.
Lemma t15 : p28 -> p27.
Proof.
 intros h0.
 refine (float_round_ne _ _ r22 i19 i19 h0 _) ; finalize.
Qed.
Lemma l26 : s1 -> p27 (* BND(float<53,-1074,ne>(r * t5), [-0.0078125, 2.25744e-05]) *).
Proof.
 intros h0.
 assert (h1 := l27 h0).
 apply t15. exact h1.
Qed.
Definition f46 := Float2 (93824992236883) (-51).
Definition i28 := makepairF f29 f46.
Notation p39 := (BND _c4 i28). (* BND(c4, [0.0390625, 0.0416667]) *)
Lemma t16 : p39 -> p27 -> p25.
Proof.
 intros h0 h1.
 refine (add _c4 r21 i28 i19 i17 h0 h1 _) ; finalize.
Qed.
Lemma l24 : s1 -> p25 (* BND(c4 + float<53,-1074,ne>(r * t5), [0.03125, 0.0416892]) *).
Proof.
 intros h0.
 assert (h1 := l25 h0).
 assert (h2 := l26 h0).
 apply t16. refine (subset _c4 i18 i28 h1 _) ; finalize. exact h2.
Qed.
Lemma t17 : p25 -> p24.
Proof.
 intros h0.
 refine (float_round_ne _ _ r19 i17 i17 h0 _) ; finalize.
Qed.
Lemma l23 : s1 -> p24 (* BND(t4, [0.03125, 0.0416892]) *).
Proof.
 intros h0.
 assert (h1 := l24 h0).
 apply t17. exact h1.
Qed.
Definition f47 := Float2 (48777586844125) (-54).
Definition i29 := makepairF f44 f47.
Notation p40 := (BND _r i29). (* BND(r, [-0.5, 0.0027077]) *)
Lemma t18 : p40 -> p24 -> p23.
Proof.
 intros h0 h1.
 refine (mul_op _r _t4 i29 i17 i16 h0 h1 _) ; finalize.
Qed.
Lemma l22 : s1 -> p23 (* BND(r * t4, [-0.03125, 0.000112882]) *).
Proof.
 intros h0.
 assert (h1 := l11 h0).
 assert (h2 := l23 h0).
 apply t18. refine (subset _r i1 i29 h1 _) ; finalize. exact h2.
Qed.
Lemma t19 : p23 -> p22.
Proof.
 intros h0.
 refine (float_round_ne _ _ r17 i16 i16 h0 _) ; finalize.
Qed.
Lemma l21 : s1 -> p22 (* BND(float<53,-1074,ne>(r * t4), [-0.03125, 0.000112882]) *).
Proof.
 intros h0.
 assert (h1 := l22 h0).
 apply t19. exact h1.
Qed.
Lemma t20 : p21 -> p22 -> p20.
Proof.
 intros h0 h1.
 refine (add _c3 r16 i15 i16 i14 h0 h1 _) ; finalize.
Qed.
Lemma l19 : s1 -> p20 (* BND(c3 + float<53,-1074,ne>(r * t4), [0.125, 0.16678]) *).
Proof.
 intros h0.
 assert (h1 := l20 h0).
 assert (h2 := l21 h0).
 apply t20. exact h1. exact h2.
Qed.
Lemma t21 : p20 -> p19.
Proof.
 intros h0.
 refine (float_round_ne _ _ r14 i14 i14 h0 _) ; finalize.
Qed.
Lemma l18 : s1 -> p19 (* BND(t3, [0.125, 0.16678]) *).
Proof.
 intros h0.
 assert (h1 := l19 h0).
 apply t21. exact h1.
Qed.
Definition f48 := Float2 (-1) (0).
Definition i30 := makepairF f48 f13.
Notation p41 := (BND _r i30). (* BND(r, [-1, 0.0027077]) *)
Lemma t22 : p41 -> p19 -> p18.
Proof.
 intros h0 h1.
 refine (mul_op _r _t3 i30 i14 i13 h0 h1 _) ; finalize.
Qed.
Lemma l17 : s1 -> p18 (* BND(r * t3, [-0.25, 0.000451589]) *).
Proof.
 intros h0.
 assert (h1 := l11 h0).
 assert (h2 := l18 h0).
 apply t22. refine (subset _r i1 i30 h1 _) ; finalize. exact h2.
Qed.
Lemma t23 : p18 -> p17.
Proof.
 intros h0.
 refine (float_round_ne _ _ r12 i13 i13 h0 _) ; finalize.
Qed.
Lemma l16 : s1 -> p17 (* BND(float<53,-1074,ne>(r * t3), [-0.25, 0.000451589]) *).
Proof.
 intros h0.
 assert (h1 := l17 h0).
 apply t23. exact h1.
Qed.
Lemma t24 : p16 -> p17 -> p15.
Proof.
 intros h0 h1.
 refine (add r10 r11 i12 i13 i11 h0 h1 _) ; finalize.
Qed.
Lemma l14 : s1 -> p15 (* BND(5e-1 + float<53,-1074,ne>(r * t3), [0.25, 0.500452]) *).
Proof.
 intros h0.
 assert (h1 := l15 h0).
 assert (h2 := l16 h0).
 apply t24. exact h1. exact h2.
Qed.
Notation p42 := (BND r9 i10). (* BND(5e-1 + float<53,-1074,ne>(r * t3), [0.25, 0.515625]) *)
Lemma t25 : p42 -> p14.
Proof.
 intros h0.
 refine (float_round_ne _ _ r9 i10 i10 h0 _) ; finalize.
Qed.
Lemma l13 : s1 -> p14 (* BND(h, [0.25, 0.515625]) *).
Proof.
 intros h0.
 assert (h1 := l14 h0).
 apply t25. refine (subset r9 i11 i10 h1 _) ; finalize.
Qed.
Lemma t26 : p14 -> p13.
Proof.
 intros h0.
 refine (abs_of_bnd_p _h i10 i10 h0 _) ; finalize.
Qed.
Lemma l12 : s1 -> p13 (* ABS(h, [0.25, 0.515625]) *).
Proof.
 intros h0.
 assert (h1 := l13 h0).
 apply t26. exact h1.
Qed.
Lemma t27 : p7 -> p13 -> p6.
Proof.
 intros h0 h1.
 refine (mul_aa _r2 _h i6 i10 i5 h0 h1 _) ; finalize.
Qed.
Lemma l6 : s1 -> p6 (* ABS(r2 * h, [0, 3.8147e-06]) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 assert (h2 := l12 h0).
 apply t27. exact h1. exact h2.
Qed.
Lemma t28 : p6 -> p5.
Proof.
 intros h0.
 refine (float_absolute_wide_ne _ _ r5 i5 i4 h0 _) ; finalize.
Qed.
Lemma l5 : s1 -> p5 (* BND(q - r2 * h, [-2.11758e-22, 2.11758e-22]) *).
Proof.
 intros h0.
 assert (h1 := l6 h0).
 apply t28. exact h1.
Qed.
Definition f49 := Float2 (-944724273354056618516338508169375818437249031169859054825847116673648468692319735689137245476230798147006570759668318457) (-469).
Definition f50 := Float2 (944724273354056618516338508169375818437249031169859054825847116673648468692319735689137245476230798147006570759668318457) (-469).
Definition i31 := makepairF f49 f50.
Notation p43 := (BND r39 i31). (* BND(r2 * h - Q, [-6.19779e-22, 6.19779e-22]) *)
Notation r42 := ((_h - _H)%R).
Notation r41 := ((_r2 * r42)%R).
Notation r44 := ((_r2 - r7)%R).
Notation r43 := ((r44 * _H)%R).
Notation r40 := ((r41 + r43)%R).
Notation p44 := (BND r40 i31). (* BND(r2 * (h - H) + (r2 - r * r) * H, [-6.19779e-22, 6.19779e-22]) *)
Definition f51 := Float2 (-2486606038774381438152572406800893829083246858665583193562940758475027698366452772863114737062182337888553382117260356189) (-471).
Definition f52 := Float2 (2486606038774381438152572406800893829083246858665583193562940758475027698366452772863114737062182337888553382117260356189) (-471).
Definition i32 := makepairF f51 f52.
Notation p45 := (BND r41 i32). (* BND(r2 * (h - H), [-4.0783e-22, 4.0783e-22]) *)
Definition f53 := Float2 (-161724562570495153016092090158807114214166909408875241881210564519495415342482647941651968052342630860103261693643059937) (-450).
Definition f54 := Float2 (161724562570495153016092090158807114214166909408875241881210564519495415342482647941651968052342630860103261693643059937) (-450).
Definition i33 := makepairF f53 f54.
Notation p46 := (BND r42 i33). (* BND(h - H, [-5.5626e-17, 5.5626e-17]) *)
Notation r46 := ((_h - r9)%R).
Notation r47 := ((r9 - _H)%R).
Notation r45 := ((r46 + r47)%R).
Notation p47 := (BND r45 i33). (* BND(h - (5e-1 + float<53,-1074,ne>(r * t3)) + (5e-1 + float<53,-1074,ne>(r * t3) - H), [-5.5626e-17, 5.5626e-17]) *)
Definition f55 := Float2 (-2307925595816409893) (-115).
Definition f56 := Float2 (2307925595816409893) (-115).
Definition i34 := makepairF f55 f56.
Notation p48 := (BND r46 i34). (* BND(h - (5e-1 + float<53,-1074,ne>(r * t3)), [-5.55613e-17, 5.55613e-17]) *)
Definition f57 := Float2 (-1) (-53).
Definition f58 := Float2 (1) (-53).
Definition i35 := makepairF f57 f58.
Notation p49 := (REL _h r9 i35). (* REL(h, 5e-1 + float<53,-1074,ne>(r * t3), [-1.11022e-16, 1.11022e-16]) *)
Notation p50 := (FIX r9 (-1074)). (* FIX(5e-1 + float<53,-1074,ne>(r * t3), -1074) *)
Notation p51 := (FIX r10 (-1)). (* FIX(5e-1, -1) *)
Notation p52 := (ABS r10 i12). (* ABS(5e-1, [0.5, 0.5]) *)
Lemma t29 : p16 -> p52.
Proof.
 intros h0.
 refine (abs_of_bnd_p r10 i12 i12 h0 _) ; finalize.
Qed.
Lemma l43 : s1 -> p52 (* ABS(5e-1, [0.5, 0.5]) *).
Proof.
 intros h0.
 assert (h1 := l15 h0).
 apply t29. exact h1.
Qed.
Lemma t30 : p52 -> p51.
Proof.
 intros h0.
 refine (fix_of_singleton_bnd r10 i12 (-1) h0 _) ; finalize.
Qed.
Lemma l42 : s1 -> p51 (* FIX(5e-1, -1) *).
Proof.
 intros h0.
 assert (h1 := l43 h0).
 apply t30. exact h1.
Qed.
Notation p53 := (FIX r11 (-1074)). (* FIX(float<53,-1074,ne>(r * t3), -1074) *)
Lemma t31 : p53.
Proof.
 refine (fix_of_float _ _ _ _ (-1074) _) ; finalize.
Qed.
Lemma l44 : s1 -> p53 (* FIX(float<53,-1074,ne>(r * t3), -1074) *).
Proof.
 intros h0.
 apply t31.
Qed.
Lemma t32 : p51 -> p53 -> p50.
Proof.
 intros h0 h1.
 refine (add_fix r10 r11 (-1) (-1074) (-1074) h0 h1 _) ; finalize.
Qed.
Lemma l41 : s1 -> p50 (* FIX(5e-1 + float<53,-1074,ne>(r * t3), -1074) *).
Proof.
 intros h0.
 assert (h1 := l42 h0).
 assert (h2 := l44 h0).
 apply t32. exact h1. exact h2.
Qed.
Lemma t33 : p50 -> p49.
Proof.
 intros h0.
 refine (rel_of_fix_float_ne _ _ (-1074) r9 i35 h0 _) ; finalize.
Qed.
Lemma l40 : s1 -> p49 (* REL(h, 5e-1 + float<53,-1074,ne>(r * t3), [-1.11022e-16, 1.11022e-16]) *).
Proof.
 intros h0.
 assert (h1 := l41 h0).
 apply t33. exact h1.
Qed.
Lemma t34 : p49 -> p15 -> p48.
Proof.
 intros h0 h1.
 refine (error_of_rel_op _h r9 i35 i11 i34 h0 h1 _) ; finalize.
Qed.
Lemma l39 : s1 -> p48 (* BND(h - (5e-1 + float<53,-1074,ne>(r * t3)), [-5.55613e-17, 5.55613e-17]) *).
Proof.
 intros h0.
 assert (h1 := l40 h0).
 assert (h2 := l14 h0).
 apply t34. exact h1. exact h2.
Qed.
Definition f59 := Float2 (-188180740264523523811340797081032294141792569434484886466732206508718612212278551389806445400024990992646942120473313) (-450).
Definition f60 := Float2 (188180740264523523811340797081032294141792569434484886466732206508718612212278551389806445400024990992646942120473313) (-450).
Definition i36 := makepairF f59 f60.
Notation p54 := (BND r47 i36). (* BND(5e-1 + float<53,-1074,ne>(r * t3) - H, [-6.47258e-20, 6.47258e-20]) *)
Notation r48 := ((r11 - r31)%R).
Notation p55 := (BND r48 i36). (* BND(float<53,-1074,ne>(r * t3) - r * T3, [-6.47258e-20, 6.47258e-20]) *)
Notation r50 := ((r11 - r12)%R).
Notation r51 := ((r12 - r31)%R).
Notation r49 := ((r50 + r51)%R).
Notation p56 := (BND r49 i36). (* BND(float<53,-1074,ne>(r * t3) - r * t3 + (r * t3 - r * T3), [-6.47258e-20, 6.47258e-20]) *)
Definition f61 := Float2 (-1) (-65).
Definition f62 := Float2 (1) (-65).
Definition i37 := makepairF f61 f62.
Notation p57 := (BND r50 i37). (* BND(float<53,-1074,ne>(r * t3) - r * t3, [-2.71051e-20, 2.71051e-20]) *)
Definition f63 := Float2 (1) (-11).
Definition i38 := makepairF f9 f63.
Notation p58 := (ABS r12 i38). (* ABS(r * t3, [0, 0.000488281]) *)
Definition f64 := Float2 (11) (-6).
Definition i39 := makepairF f21 f64.
Notation p59 := (ABS _t3 i39). (* ABS(t3, [0.125, 0.171875]) *)
Notation p60 := (BND _t3 i39). (* BND(t3, [0.125, 0.171875]) *)
Lemma t35 : p60 -> p59.
Proof.
 intros h0.
 refine (abs_of_bnd_p _t3 i39 i39 h0 _) ; finalize.
Qed.
Lemma l50 : s1 -> p59 (* ABS(t3, [0.125, 0.171875]) *).
Proof.
 intros h0.
 assert (h1 := l18 h0).
 apply t35. refine (subset _t3 i14 i39 h1 _) ; finalize.
Qed.
Definition f65 := Float2 (23) (-13).
Definition i40 := makepairF f9 f65.
Notation p61 := (ABS _r i40). (* ABS(r, [0, 0.00280762]) *)
Lemma t36 : p61 -> p59 -> p58.
Proof.
 intros h0 h1.
 refine (mul_aa _r _t3 i40 i39 i38 h0 h1 _) ; finalize.
Qed.
Lemma l49 : s1 -> p58 (* ABS(r * t3, [0, 0.000488281]) *).
Proof.
 intros h0.
 assert (h1 := l10 h0).
 assert (h2 := l50 h0).
 apply t36. refine (abs_subset _r i8 i40 h1 _) ; finalize. exact h2.
Qed.
Lemma t37 : p58 -> p57.
Proof.
 intros h0.
 refine (float_absolute_wide_ne _ _ r12 i38 i37 h0 _) ; finalize.
Qed.
Lemma l48 : s1 -> p57 (* BND(float<53,-1074,ne>(r * t3) - r * t3, [-2.71051e-20, 2.71051e-20]) *).
Proof.
 intros h0.
 assert (h1 := l49 h0).
 apply t37. exact h1.
Qed.
Definition f66 := Float2 (-109376727871734565386782716880745066531633090893553993130835619700227168669284130166977912890255159711033686139859681) (-450).
Definition f67 := Float2 (109376727871734565386782716880745066531633090893553993130835619700227168669284130166977912890255159711033686139859681) (-450).
Definition i41 := makepairF f66 f67.
Notation p62 := (BND r51 i41). (* BND(r * t3 - r * T3, [-3.76207e-20, 3.76207e-20]) *)
Notation r53 := ((_t3 - _T3)%R).
Notation r52 := ((_r * r53)%R).
Notation p63 := (BND r52 i41). (* BND(r * (t3 - T3), [-3.76207e-20, 3.76207e-20]) *)
Definition f68 := Float2 (-5049337439142748706779864685930174434558531728660578772151439399685488083488021668158303767508178514561883062186527357) (-447).
Definition f69 := Float2 (5049337439142748706779864685930174434558531728660578772151439399685488083488021668158303767508178514561883062186527357) (-447).
Definition i42 := makepairF f68 f69.
Notation p64 := (BND r53 i42). (* BND(t3 - T3, [-1.3894e-17, 1.3894e-17]) *)
Notation r55 := ((_t3 - r14)%R).
Notation r56 := ((r14 - _T3)%R).
Notation r54 := ((r55 + r56)%R).
Notation p65 := (BND r54 i42). (* BND(t3 - (c3 + float<53,-1074,ne>(r * t4)) + (c3 + float<53,-1074,ne>(r * t4) - T3), [-1.3894e-17, 1.3894e-17]) *)
Definition f70 := Float2 (-1) (-56).
Definition f71 := Float2 (1) (-56).
Definition i43 := makepairF f70 f71.
Notation p66 := (BND r55 i43). (* BND(t3 - (c3 + float<53,-1074,ne>(r * t4)), [-1.38778e-17, 1.38778e-17]) *)
Definition i44 := makepairF f21 f15.
Notation p67 := (ABS r14 i44). (* ABS(c3 + float<53,-1074,ne>(r * t4), [0.125, 0.25]) *)
Definition f72 := Float2 (3) (-4).
Definition i45 := makepairF f23 f72.
Notation p68 := (ABS _c3 i45). (* ABS(c3, [0.15625, 0.1875]) *)
Notation p69 := (BND _c3 i45). (* BND(c3, [0.15625, 0.1875]) *)
Lemma t38 : p69 -> p68.
Proof.
 intros h0.
 refine (abs_of_bnd_p _c3 i45 i45 h0 _) ; finalize.
Qed.
Lemma l57 : s1 -> p68 (* ABS(c3, [0.15625, 0.1875]) *).
Proof.
 intros h0.
 assert (h1 := l20 h0).
 apply t38. refine (subset _c3 i15 i45 h1 _) ; finalize.
Qed.
Definition i46 := makepairF f9 f27.
Notation p70 := (ABS r16 i46). (* ABS(float<53,-1074,ne>(r * t4), [0, 0.03125]) *)
Definition i47 := makepairF f25 f27.
Notation p71 := (BND r16 i47). (* BND(float<53,-1074,ne>(r * t4), [-0.03125, 0.03125]) *)
Lemma t39 : p71 -> p70.
Proof.
 intros h0.
 refine (abs_of_bnd_o r16 i47 i46 h0 _) ; finalize.
Qed.
Lemma l58 : s1 -> p70 (* ABS(float<53,-1074,ne>(r * t4), [0, 0.03125]) *).
Proof.
 intros h0.
 assert (h1 := l21 h0).
 apply t39. refine (subset r16 i16 i47 h1 _) ; finalize.
Qed.
Lemma t40 : p68 -> p70 -> p67.
Proof.
 intros h0 h1.
 refine (add_aa_p _c3 r16 i45 i46 i44 h0 h1 _) ; finalize.
Qed.
Lemma l56 : s1 -> p67 (* ABS(c3 + float<53,-1074,ne>(r * t4), [0.125, 0.25]) *).
Proof.
 intros h0.
 assert (h1 := l57 h0).
 assert (h2 := l58 h0).
 apply t40. exact h1. exact h2.
Qed.
Lemma t41 : p67 -> p66.
Proof.
 intros h0.
 refine (float_absolute_wide_ne _ _ r14 i44 i43 h0 _) ; finalize.
Qed.
Lemma l55 : s1 -> p66 (* BND(t3 - (c3 + float<53,-1074,ne>(r * t4)), [-1.38778e-17, 1.38778e-17]) *).
Proof.
 intros h0.
 assert (h1 := l56 h0).
 apply t41. exact h1.
Qed.
Definition f73 := Float2 (-5880646004255367608147553111791867508325102041001598654057843942035696736378709897277686882909312538634679427254909) (-447).
Definition f74 := Float2 (5880646004255367608147553111791867508325102041001598654057843942035696736378709897277686882909312538634679427254909) (-447).
Definition i48 := makepairF f73 f74.
Notation p72 := (BND r56 i48). (* BND(c3 + float<53,-1074,ne>(r * t4) - T3, [-1.61814e-20, 1.61814e-20]) *)
Notation r57 := ((r16 - r33)%R).
Notation p73 := (BND r57 i48). (* BND(float<53,-1074,ne>(r * t4) - r * T4, [-1.61814e-20, 1.61814e-20]) *)
Notation r59 := ((r16 - r17)%R).
Notation r60 := ((r17 - r33)%R).
Notation r58 := ((r59 + r60)%R).
Notation p74 := (BND r58 i48). (* BND(float<53,-1074,ne>(r * t4) - r * t4 + (r * t4 - r * T4), [-1.61814e-20, 1.61814e-20]) *)
Definition f75 := Float2 (-1) (-67).
Definition f76 := Float2 (1) (-67).
Definition i49 := makepairF f75 f76.
Notation p75 := (BND r59 i49). (* BND(float<53,-1074,ne>(r * t4) - r * t4, [-6.77626e-21, 6.77626e-21]) *)
Definition f77 := Float2 (1) (-13).
Definition i50 := makepairF f9 f77.
Notation p76 := (ABS r17 i50). (* ABS(r * t4, [0, 0.00012207]) *)
Definition f78 := Float2 (11) (-8).
Definition i51 := makepairF f27 f78.
Notation p77 := (ABS _t4 i51). (* ABS(t4, [0.03125, 0.0429688]) *)
Notation p78 := (BND _t4 i51). (* BND(t4, [0.03125, 0.0429688]) *)
Lemma t42 : p78 -> p77.
Proof.
 intros h0.
 refine (abs_of_bnd_p _t4 i51 i51 h0 _) ; finalize.
Qed.
Lemma l64 : s1 -> p77 (* ABS(t4, [0.03125, 0.0429688]) *).
Proof.
 intros h0.
 assert (h1 := l23 h0).
 apply t42. refine (subset _t4 i17 i51 h1 _) ; finalize.
Qed.
Lemma t43 : p61 -> p77 -> p76.
Proof.
 intros h0 h1.
 refine (mul_aa _r _t4 i40 i51 i50 h0 h1 _) ; finalize.
Qed.
Lemma l63 : s1 -> p76 (* ABS(r * t4, [0, 0.00012207]) *).
Proof.
 intros h0.
 assert (h1 := l10 h0).
 assert (h2 := l64 h0).
 apply t43. refine (abs_subset _r i8 i40 h1 _) ; finalize. exact h2.
Qed.
Lemma t44 : p76 -> p75.
Proof.
 intros h0.
 refine (float_absolute_wide_ne _ _ r17 i50 i49 h0 _) ; finalize.
Qed.
Lemma l62 : s1 -> p75 (* BND(float<53,-1074,ne>(r * t4) - r * t4, [-6.77626e-21, 6.77626e-21]) *).
Proof.
 intros h0.
 assert (h1 := l63 h0).
 apply t44. exact h1.
Qed.
Definition f79 := Float2 (-3418020616980712657380113105532891645507618336597508237311075604270339125660134234064295241979005311084265177860733) (-447).
Definition f80 := Float2 (3418020616980712657380113105532891645507618336597508237311075604270339125660134234064295241979005311084265177860733) (-447).
Definition i52 := makepairF f79 f80.
Notation p79 := (BND r60 i52). (* BND(r * t4 - r * T4, [-9.40517e-21, 9.40517e-21]) *)
Notation r62 := ((_t4 - _T4)%R).
Notation r61 := ((_r * r62)%R).
Notation p80 := (BND r61 i52). (* BND(r * (t4 - T4), [-9.40517e-21, 9.40517e-21]) *)
Definition f81 := Float2 (-2465495260752836137291994463656952023906661396634416026885620467404256787976862161948083851420114764638422065040161) (-438).
Definition f82 := Float2 (2465495260752836137291994463656952023906661396634416026885620467404256787976862161948083851420114764638422065040161) (-438).
Definition i53 := makepairF f81 f82.
Notation p81 := (BND r62 i53). (* BND(t4 - T4, [-3.47349e-18, 3.47349e-18]) *)
Notation r64 := ((_t4 - r19)%R).
Notation r65 := ((r19 - _T4)%R).
Notation r63 := ((r64 + r65)%R).
Notation p82 := (BND r63 i53). (* BND(t4 - (c4 + float<53,-1074,ne>(r * t5)) + (c4 + float<53,-1074,ne>(r * t5) - T4), [-3.47349e-18, 3.47349e-18]) *)
Definition f83 := Float2 (-1) (-58).
Definition f84 := Float2 (1) (-58).
Definition i54 := makepairF f83 f84.
Notation p83 := (BND r64 i54). (* BND(t4 - (c4 + float<53,-1074,ne>(r * t5)), [-3.46945e-18, 3.46945e-18]) *)
Definition f85 := Float2 (1) (-4).
Definition i55 := makepairF f27 f85.
Notation p84 := (ABS r19 i55). (* ABS(c4 + float<53,-1074,ne>(r * t5), [0.03125, 0.0625]) *)
Definition f86 := Float2 (3) (-6).
Definition i56 := makepairF f29 f86.
Notation p85 := (ABS _c4 i56). (* ABS(c4, [0.0390625, 0.046875]) *)
Notation p86 := (BND _c4 i56). (* BND(c4, [0.0390625, 0.046875]) *)
Lemma t45 : p86 -> p85.
Proof.
 intros h0.
 refine (abs_of_bnd_p _c4 i56 i56 h0 _) ; finalize.
Qed.
Lemma l71 : s1 -> p85 (* ABS(c4, [0.0390625, 0.046875]) *).
Proof.
 intros h0.
 assert (h1 := l25 h0).
 apply t45. refine (subset _c4 i18 i56 h1 _) ; finalize.
Qed.
Definition i57 := makepairF f9 f33.
Notation p87 := (ABS r21 i57). (* ABS(float<53,-1074,ne>(r * t5), [0, 0.0078125]) *)
Definition i58 := makepairF f31 f33.
Notation p88 := (BND r21 i58). (* BND(float<53,-1074,ne>(r * t5), [-0.0078125, 0.0078125]) *)
Lemma t46 : p88 -> p87.
Proof.
 intros h0.
 refine (abs_of_bnd_o r21 i58 i57 h0 _) ; finalize.
Qed.
Lemma l72 : s1 -> p87 (* ABS(float<53,-1074,ne>(r * t5), [0, 0.0078125]) *).
Proof.
 intros h0.
 assert (h1 := l26 h0).
 apply t46. refine (subset r21 i19 i58 h1 _) ; finalize.
Qed.
Lemma t47 : p85 -> p87 -> p84.
Proof.
 intros h0 h1.
 refine (add_aa_p _c4 r21 i56 i57 i55 h0 h1 _) ; finalize.
Qed.
Lemma l70 : s1 -> p84 (* ABS(c4 + float<53,-1074,ne>(r * t5), [0.03125, 0.0625]) *).
Proof.
 intros h0.
 assert (h1 := l71 h0).
 assert (h2 := l72 h0).
 apply t47. exact h1. exact h2.
Qed.
Lemma t48 : p84 -> p83.
Proof.
 intros h0.
 refine (float_absolute_wide_ne _ _ r19 i55 i54 h0 _) ; finalize.
Qed.
Lemma l69 : s1 -> p83 (* BND(t4 - (c4 + float<53,-1074,ne>(r * t5)), [-3.46945e-18, 3.46945e-18]) *).
Proof.
 intros h0.
 assert (h1 := l70 h0).
 apply t48. exact h1.
Qed.
Definition f87 := Float2 (-2869873478181186524554457397976161089177692230325610138852129638899177258286498734692210489807537088007815645985) (-438).
Definition f88 := Float2 (2869873478181186524554457397976161089177692230325610138852129638899177258286498734692210489807537088007815645985) (-438).
Definition i59 := makepairF f87 f88.
Notation p89 := (BND r65 i59). (* BND(c4 + float<53,-1074,ne>(r * t5) - T4, [-4.04319e-21, 4.04319e-21]) *)
Notation r66 := ((r21 - r35)%R).
Notation p90 := (BND r66 i59). (* BND(float<53,-1074,ne>(r * t5) - r * T5, [-4.04319e-21, 4.04319e-21]) *)
Notation r68 := ((r21 - r22)%R).
Notation r69 := ((r22 - r35)%R).
Notation r67 := ((r68 + r69)%R).
Notation p91 := (BND r67 i59). (* BND(float<53,-1074,ne>(r * t5) - r * t5 + (r * t5 - r * T5), [-4.04319e-21, 4.04319e-21]) *)
Definition f89 := Float2 (-1) (-69).
Definition f90 := Float2 (1) (-69).
Definition i60 := makepairF f89 f90.
Notation p92 := (BND r68 i60). (* BND(float<53,-1074,ne>(r * t5) - r * t5, [-1.69407e-21, 1.69407e-21]) *)
Definition f91 := Float2 (1) (-15).
Definition i61 := makepairF f9 f91.
Notation p93 := (ABS r22 i61). (* ABS(r * t5, [0, 3.05176e-05]) *)
Definition f92 := Float2 (5) (-9).
Definition i62 := makepairF f33 f92.
Notation p94 := (ABS _t5 i62). (* ABS(t5, [0.0078125, 0.00976562]) *)
Notation p95 := (BND _t5 i62). (* BND(t5, [0.0078125, 0.00976562]) *)
Lemma t49 : p95 -> p94.
Proof.
 intros h0.
 refine (abs_of_bnd_p _t5 i62 i62 h0 _) ; finalize.
Qed.
Lemma l78 : s1 -> p94 (* ABS(t5, [0.0078125, 0.00976562]) *).
Proof.
 intros h0.
 assert (h1 := l28 h0).
 apply t49. refine (subset _t5 i20 i62 h1 _) ; finalize.
Qed.
Definition f93 := Float2 (3) (-10).
Definition i63 := makepairF f9 f93.
Notation p96 := (ABS _r i63). (* ABS(r, [0, 0.00292969]) *)
Lemma t50 : p96 -> p94 -> p93.
Proof.
 intros h0 h1.
 refine (mul_aa _r _t5 i63 i62 i61 h0 h1 _) ; finalize.
Qed.
Lemma l77 : s1 -> p93 (* ABS(r * t5, [0, 3.05176e-05]) *).
Proof.
 intros h0.
 assert (h1 := l10 h0).
 assert (h2 := l78 h0).
 apply t50. refine (abs_subset _r i8 i63 h1 _) ; finalize. exact h2.
Qed.
Lemma t51 : p93 -> p92.
Proof.
 intros h0.
 refine (float_absolute_wide_ne _ _ r22 i61 i60 h0 _) ; finalize.
Qed.
Lemma l76 : s1 -> p92 (* BND(float<53,-1074,ne>(r * t5) - r * t5, [-1.69407e-21, 1.69407e-21]) *).
Proof.
 intros h0.
 assert (h1 := l77 h0).
 apply t51. exact h1.
Qed.
Definition f94 := Float2 (-1667419675800983911875043332420020531161342765284550365049996661474686237427819211638796602634535512055464938273) (-438).
Definition f95 := Float2 (1667419675800983911875043332420020531161342765284550365049996661474686237427819211638796602634535512055464938273) (-438).
Definition i64 := makepairF f94 f95.
Notation p97 := (BND r69 i64). (* BND(r * t5 - r * T5, [-2.34913e-21, 2.34913e-21]) *)
Notation r71 := ((_t5 - _T5)%R).
Notation r70 := ((_r * r71)%R).
Notation p98 := (BND r70 i64). (* BND(r * (t5 - T5), [-2.34913e-21, 2.34913e-21]) *)
Definition f96 := Float2 (-4097) (-72).
Definition f97 := Float2 (4097) (-72).
Definition i65 := makepairF f96 f97.
Notation p99 := (BND r71 i65). (* BND(t5 - T5, [-8.67573e-19, 8.67573e-19]) *)
Notation r73 := ((_t5 - r24)%R).
Notation r74 := ((r24 - _T5)%R).
Notation r72 := ((r73 + r74)%R).
Notation p100 := (BND r72 i65). (* BND(t5 - (c5 + float<53,-1074,ne>(r * c6)) + (c5 + float<53,-1074,ne>(r * c6) - T5), [-8.67573e-19, 8.67573e-19]) *)
Definition f98 := Float2 (-1) (-60).
Definition f99 := Float2 (1) (-60).
Definition i66 := makepairF f98 f99.
Notation p101 := (BND r73 i66). (* BND(t5 - (c5 + float<53,-1074,ne>(r * c6)), [-8.67362e-19, 8.67362e-19]) *)
Definition f100 := Float2 (1) (-6).
Definition i67 := makepairF f33 f100.
Notation p102 := (ABS r24 i67). (* ABS(c5 + float<53,-1074,ne>(r * c6), [0.0078125, 0.015625]) *)
Definition f101 := Float2 (3) (-8).
Definition i68 := makepairF f35 f101.
Notation p103 := (ABS _c5 i68). (* ABS(c5, [0.00830078, 0.0117188]) *)
Notation p104 := (BND _c5 i68). (* BND(c5, [0.00830078, 0.0117188]) *)
Lemma t52 : p104 -> p103.
Proof.
 intros h0.
 refine (abs_of_bnd_p _c5 i68 i68 h0 _) ; finalize.
Qed.
Lemma l85 : s1 -> p103 (* ABS(c5, [0.00830078, 0.0117188]) *).
Proof.
 intros h0.
 assert (h1 := l30 h0).
 apply t52. refine (subset _c5 i21 i68 h1 _) ; finalize.
Qed.
Notation p105 := (ABS r26 i38). (* ABS(float<53,-1074,ne>(r * c6), [0, 0.000488281]) *)
Definition i69 := makepairF f37 f63.
Notation p106 := (BND r26 i69). (* BND(float<53,-1074,ne>(r * c6), [-0.000488281, 0.000488281]) *)
Lemma t53 : p106 -> p105.
Proof.
 intros h0.
 refine (abs_of_bnd_o r26 i69 i38 h0 _) ; finalize.
Qed.
Lemma l86 : s1 -> p105 (* ABS(float<53,-1074,ne>(r * c6), [0, 0.000488281]) *).
Proof.
 intros h0.
 assert (h1 := l31 h0).
 apply t53. refine (subset r26 i22 i69 h1 _) ; finalize.
Qed.
Lemma t54 : p103 -> p105 -> p102.
Proof.
 intros h0 h1.
 refine (add_aa_p _c5 r26 i68 i38 i67 h0 h1 _) ; finalize.
Qed.
Lemma l84 : s1 -> p102 (* ABS(c5 + float<53,-1074,ne>(r * c6), [0.0078125, 0.015625]) *).
Proof.
 intros h0.
 assert (h1 := l85 h0).
 assert (h2 := l86 h0).
 apply t54. exact h1. exact h2.
Qed.
Lemma t55 : p102 -> p101.
Proof.
 intros h0.
 refine (float_absolute_wide_ne _ _ r24 i67 i66 h0 _) ; finalize.
Qed.
Lemma l83 : s1 -> p101 (* BND(t5 - (c5 + float<53,-1074,ne>(r * c6)), [-8.67362e-19, 8.67362e-19]) *).
Proof.
 intros h0.
 assert (h1 := l84 h0).
 apply t55. exact h1.
Qed.
Notation p107 := (BND r74 i4). (* BND(c5 + float<53,-1074,ne>(r * c6) - T5, [-2.11758e-22, 2.11758e-22]) *)
Notation r75 := ((r26 - r27)%R).
Notation p108 := (BND r75 i4). (* BND(float<53,-1074,ne>(r * c6) - r * c6, [-2.11758e-22, 2.11758e-22]) *)
Notation p109 := (ABS r27 i5). (* ABS(r * c6, [0, 3.8147e-06]) *)
Definition f102 := Float2 (23) (-14).
Definition i70 := makepairF f40 f102.
Notation p110 := (ABS _c6 i70). (* ABS(c6, [0.000976562, 0.00140381]) *)
Notation p111 := (BND _c6 i70). (* BND(c6, [0.000976562, 0.00140381]) *)
Lemma t56 : p111 -> p110.
Proof.
 intros h0.
 refine (abs_of_bnd_p _c6 i70 i70 h0 _) ; finalize.
Qed.
Lemma l90 : s1 -> p110 (* ABS(c6, [0.000976562, 0.00140381]) *).
Proof.
 intros h0.
 assert (h1 := l33 h0).
 apply t56. refine (subset _c6 i24 i70 h1 _) ; finalize.
Qed.
Definition f103 := Float2 (89) (-15).
Definition i71 := makepairF f9 f103.
Notation p112 := (ABS _r i71). (* ABS(r, [0, 0.00271606]) *)
Lemma t57 : p112 -> p110 -> p109.
Proof.
 intros h0 h1.
 refine (mul_aa _r _c6 i71 i70 i5 h0 h1 _) ; finalize.
Qed.
Lemma l89 : s1 -> p109 (* ABS(r * c6, [0, 3.8147e-06]) *).
Proof.
 intros h0.
 assert (h1 := l10 h0).
 assert (h2 := l90 h0).
 apply t57. refine (abs_subset _r i8 i71 h1 _) ; finalize. exact h2.
Qed.
Lemma t58 : p109 -> p108.
Proof.
 intros h0.
 refine (float_absolute_wide_ne _ _ r27 i5 i4 h0 _) ; finalize.
Qed.
Lemma l88 : s1 -> p108 (* BND(float<53,-1074,ne>(r * c6) - r * c6, [-2.11758e-22, 2.11758e-22]) *).
Proof.
 intros h0.
 assert (h1 := l89 h0).
 apply t58. exact h1.
Qed.
Lemma t59 : p108 -> p107.
Proof.
 intros h0.
 refine (add_fils _ _ _ i4 h0) ; finalize.
Qed.
Lemma l87 : s1 -> p107 (* BND(c5 + float<53,-1074,ne>(r * c6) - T5, [-2.11758e-22, 2.11758e-22]) *).
Proof.
 intros h0.
 assert (h1 := l88 h0).
 apply t59. exact h1.
Qed.
Lemma t60 : p101 -> p107 -> p100.
Proof.
 intros h0 h1.
 refine (add r73 r74 i66 i4 i65 h0 h1 _) ; finalize.
Qed.
Lemma l82 : s1 -> p100 (* BND(t5 - (c5 + float<53,-1074,ne>(r * c6)) + (c5 + float<53,-1074,ne>(r * c6) - T5), [-8.67573e-19, 8.67573e-19]) *).
Proof.
 intros h0.
 assert (h1 := l83 h0).
 assert (h2 := l87 h0).
 apply t60. exact h1. exact h2.
Qed.
Lemma t61 : p100 -> p99.
Proof.
 intros h0.
 refine (sub_xals _ _ _ i65 h0) ; finalize.
Qed.
Lemma l81 : s1 -> p99 (* BND(t5 - T5, [-8.67573e-19, 8.67573e-19]) *).
Proof.
 intros h0.
 assert (h1 := l82 h0).
 apply t61. exact h1.
Qed.
Definition f104 := Float2 (-3334025380561791605096498652473714471875450313207477810712612314083629401271343661641450273073496440019128331543) (-379).
Definition f105 := Float2 (3334025380561791605096498652473714471875450313207477810712612314083629401271343661641450273073496440019128331543) (-379).
Definition i72 := makepairF f104 f105.
Notation p113 := (BND _r i72). (* BND(r, [-0.0027077, 0.0027077]) *)
Lemma t62 : p113 -> p99 -> p98.
Proof.
 intros h0 h1.
 refine (mul_oo _r r71 i72 i65 i64 h0 h1 _) ; finalize.
Qed.
Lemma l80 : s1 -> p98 (* BND(r * (t5 - T5), [-2.34913e-21, 2.34913e-21]) *).
Proof.
 intros h0.
 assert (h1 := l11 h0).
 assert (h2 := l81 h0).
 apply t62. refine (subset _r i1 i72 h1 _) ; finalize. exact h2.
Qed.
Lemma t63 : p98 -> p97.
Proof.
 intros h0.
 refine (mul_fils _ _ _ i64 h0) ; finalize.
Qed.
Lemma l79 : s1 -> p97 (* BND(r * t5 - r * T5, [-2.34913e-21, 2.34913e-21]) *).
Proof.
 intros h0.
 assert (h1 := l80 h0).
 apply t63. exact h1.
Qed.
Lemma t64 : p92 -> p97 -> p91.
Proof.
 intros h0 h1.
 refine (add r68 r69 i60 i64 i59 h0 h1 _) ; finalize.
Qed.
Lemma l75 : s1 -> p91 (* BND(float<53,-1074,ne>(r * t5) - r * t5 + (r * t5 - r * T5), [-4.04319e-21, 4.04319e-21]) *).
Proof.
 intros h0.
 assert (h1 := l76 h0).
 assert (h2 := l79 h0).
 apply t64. exact h1. exact h2.
Qed.
Lemma t65 : p91 -> p90.
Proof.
 intros h0.
 refine (sub_xals _ _ _ i59 h0) ; finalize.
Qed.
Lemma l74 : s1 -> p90 (* BND(float<53,-1074,ne>(r * t5) - r * T5, [-4.04319e-21, 4.04319e-21]) *).
Proof.
 intros h0.
 assert (h1 := l75 h0).
 apply t65. exact h1.
Qed.
Lemma t66 : p90 -> p89.
Proof.
 intros h0.
 refine (add_fils _ _ _ i59 h0) ; finalize.
Qed.
Lemma l73 : s1 -> p89 (* BND(c4 + float<53,-1074,ne>(r * t5) - T4, [-4.04319e-21, 4.04319e-21]) *).
Proof.
 intros h0.
 assert (h1 := l74 h0).
 apply t66. exact h1.
Qed.
Lemma t67 : p83 -> p89 -> p82.
Proof.
 intros h0 h1.
 refine (add r64 r65 i54 i59 i53 h0 h1 _) ; finalize.
Qed.
Lemma l68 : s1 -> p82 (* BND(t4 - (c4 + float<53,-1074,ne>(r * t5)) + (c4 + float<53,-1074,ne>(r * t5) - T4), [-3.47349e-18, 3.47349e-18]) *).
Proof.
 intros h0.
 assert (h1 := l69 h0).
 assert (h2 := l73 h0).
 apply t67. exact h1. exact h2.
Qed.
Lemma t68 : p82 -> p81.
Proof.
 intros h0.
 refine (sub_xals _ _ _ i53 h0) ; finalize.
Qed.
Lemma l67 : s1 -> p81 (* BND(t4 - T4, [-3.47349e-18, 3.47349e-18]) *).
Proof.
 intros h0.
 assert (h1 := l68 h0).
 apply t68. exact h1.
Qed.
Definition f106 := Float2 (-54624671835124393657901033922129337907207377931591316450715440153946184110429694552333521274036165673273398583989129) (-393).
Definition f107 := Float2 (54624671835124393657901033922129337907207377931591316450715440153946184110429694552333521274036165673273398583989129) (-393).
Definition i73 := makepairF f106 f107.
Notation p114 := (BND _r i73). (* BND(r, [-0.0027077, 0.0027077]) *)
Lemma t69 : p114 -> p81 -> p80.
Proof.
 intros h0 h1.
 refine (mul_oo _r r62 i73 i53 i52 h0 h1 _) ; finalize.
Qed.
Lemma l66 : s1 -> p80 (* BND(r * (t4 - T4), [-9.40517e-21, 9.40517e-21]) *).
Proof.
 intros h0.
 assert (h1 := l11 h0).
 assert (h2 := l67 h0).
 apply t69. refine (subset _r i1 i73 h1 _) ; finalize. exact h2.
Qed.
Lemma t70 : p80 -> p79.
Proof.
 intros h0.
 refine (mul_fils _ _ _ i52 h0) ; finalize.
Qed.
Lemma l65 : s1 -> p79 (* BND(r * t4 - r * T4, [-9.40517e-21, 9.40517e-21]) *).
Proof.
 intros h0.
 assert (h1 := l66 h0).
 apply t70. exact h1.
Qed.
Lemma t71 : p75 -> p79 -> p74.
Proof.
 intros h0 h1.
 refine (add r59 r60 i49 i52 i48 h0 h1 _) ; finalize.
Qed.
Lemma l61 : s1 -> p74 (* BND(float<53,-1074,ne>(r * t4) - r * t4 + (r * t4 - r * T4), [-1.61814e-20, 1.61814e-20]) *).
Proof.
 intros h0.
 assert (h1 := l62 h0).
 assert (h2 := l65 h0).
 apply t71. exact h1. exact h2.
Qed.
Lemma t72 : p74 -> p73.
Proof.
 intros h0.
 refine (sub_xals _ _ _ i48 h0) ; finalize.
Qed.
Lemma l60 : s1 -> p73 (* BND(float<53,-1074,ne>(r * t4) - r * T4, [-1.61814e-20, 1.61814e-20]) *).
Proof.
 intros h0.
 assert (h1 := l61 h0).
 apply t72. exact h1.
Qed.
Lemma t73 : p73 -> p72.
Proof.
 intros h0.
 refine (add_fils _ _ _ i48 h0) ; finalize.
Qed.
Lemma l59 : s1 -> p72 (* BND(c3 + float<53,-1074,ne>(r * t4) - T3, [-1.61814e-20, 1.61814e-20]) *).
Proof.
 intros h0.
 assert (h1 := l60 h0).
 apply t73. exact h1.
Qed.
Lemma t74 : p66 -> p72 -> p65.
Proof.
 intros h0 h1.
 refine (add r55 r56 i43 i48 i42 h0 h1 _) ; finalize.
Qed.
Lemma l54 : s1 -> p65 (* BND(t3 - (c3 + float<53,-1074,ne>(r * t4)) + (c3 + float<53,-1074,ne>(r * t4) - T3), [-1.3894e-17, 1.3894e-17]) *).
Proof.
 intros h0.
 assert (h1 := l55 h0).
 assert (h2 := l59 h0).
 apply t74. exact h1. exact h2.
Qed.
Lemma t75 : p65 -> p64.
Proof.
 intros h0.
 refine (sub_xals _ _ _ i42 h0) ; finalize.
Qed.
Lemma l53 : s1 -> p64 (* BND(t3 - T3, [-1.3894e-17, 1.3894e-17]) *).
Proof.
 intros h0.
 assert (h1 := l54 h0).
 apply t75. exact h1.
Qed.
Definition f108 := Float2 (-1747989498723980597052833085508138813030636093810922126422894084926277891533750225674672680769157301544748754687652097) (-398).
Definition f109 := Float2 (1747989498723980597052833085508138813030636093810922126422894084926277891533750225674672680769157301544748754687652097) (-398).
Definition i74 := makepairF f108 f109.
Notation p115 := (BND _r i74). (* BND(r, [-0.0027077, 0.0027077]) *)
Lemma t76 : p115 -> p64 -> p63.
Proof.
 intros h0 h1.
 refine (mul_oo _r r53 i74 i42 i41 h0 h1 _) ; finalize.
Qed.
Lemma l52 : s1 -> p63 (* BND(r * (t3 - T3), [-3.76207e-20, 3.76207e-20]) *).
Proof.
 intros h0.
 assert (h1 := l11 h0).
 assert (h2 := l53 h0).
 apply t76. refine (subset _r i1 i74 h1 _) ; finalize. exact h2.
Qed.
Lemma t77 : p63 -> p62.
Proof.
 intros h0.
 refine (mul_fils _ _ _ i41 h0) ; finalize.
Qed.
Lemma l51 : s1 -> p62 (* BND(r * t3 - r * T3, [-3.76207e-20, 3.76207e-20]) *).
Proof.
 intros h0.
 assert (h1 := l52 h0).
 apply t77. exact h1.
Qed.
Lemma t78 : p57 -> p62 -> p56.
Proof.
 intros h0 h1.
 refine (add r50 r51 i37 i41 i36 h0 h1 _) ; finalize.
Qed.
Lemma l47 : s1 -> p56 (* BND(float<53,-1074,ne>(r * t3) - r * t3 + (r * t3 - r * T3), [-6.47258e-20, 6.47258e-20]) *).
Proof.
 intros h0.
 assert (h1 := l48 h0).
 assert (h2 := l51 h0).
 apply t78. exact h1. exact h2.
Qed.
Lemma t79 : p56 -> p55.
Proof.
 intros h0.
 refine (sub_xals _ _ _ i36 h0) ; finalize.
Qed.
Lemma l46 : s1 -> p55 (* BND(float<53,-1074,ne>(r * t3) - r * T3, [-6.47258e-20, 6.47258e-20]) *).
Proof.
 intros h0.
 assert (h1 := l47 h0).
 apply t79. exact h1.
Qed.
Lemma t80 : p55 -> p54.
Proof.
 intros h0.
 refine (add_fils _ _ _ i36 h0) ; finalize.
Qed.
Lemma l45 : s1 -> p54 (* BND(5e-1 + float<53,-1074,ne>(r * t3) - H, [-6.47258e-20, 6.47258e-20]) *).
Proof.
 intros h0.
 assert (h1 := l46 h0).
 apply t80. exact h1.
Qed.
Lemma t81 : p48 -> p54 -> p47.
Proof.
 intros h0 h1.
 refine (add r46 r47 i34 i36 i33 h0 h1 _) ; finalize.
Qed.
Lemma l38 : s1 -> p47 (* BND(h - (5e-1 + float<53,-1074,ne>(r * t3)) + (5e-1 + float<53,-1074,ne>(r * t3) - H), [-5.5626e-17, 5.5626e-17]) *).
Proof.
 intros h0.
 assert (h1 := l39 h0).
 assert (h2 := l45 h0).
 apply t81. exact h1. exact h2.
Qed.
Lemma t82 : p47 -> p46.
Proof.
 intros h0.
 refine (sub_xals _ _ _ i33 h0) ; finalize.
Qed.
Lemma l37 : s1 -> p46 (* BND(h - H, [-5.5626e-17, 5.5626e-17]) *).
Proof.
 intros h0.
 assert (h1 := l38 h0).
 apply t82. exact h1.
Qed.
Lemma t83 : p8 -> p46 -> p45.
Proof.
 intros h0 h1.
 refine (mul_po _r2 r42 i7 i33 i32 h0 h1 _) ; finalize.
Qed.
Lemma l36 : s1 -> p45 (* BND(r2 * (h - H), [-4.0783e-22, 4.0783e-22]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 assert (h2 := l37 h0).
 apply t83. exact h1. exact h2.
Qed.
Definition f110 := Float2 (-1292291054641845035912781625876609444665749266013853025740447708219566176402826169893434244842740854699472900921412917639) (-471).
Definition f111 := Float2 (1292291054641845035912781625876609444665749266013853025740447708219566176402826169893434244842740854699472900921412917639) (-471).
Definition i75 := makepairF f110 f111.
Notation p116 := (BND r43 i75). (* BND((r2 - r * r) * H, [-2.11949e-22, 2.11949e-22]) *)
Definition f112 := Float2 (-1) (-71).
Definition f113 := Float2 (1) (-71).
Definition i76 := makepairF f112 f113.
Notation p117 := (BND r44 i76). (* BND(r2 - r * r, [-4.23516e-22, 4.23516e-22]) *)
Definition f114 := Float2 (1) (-17).
Definition i77 := makepairF f9 f114.
Notation p118 := (ABS r7 i77). (* ABS(r * r, [0, 7.62939e-06]) *)
Definition f115 := Float2 (45) (-14).
Definition i78 := makepairF f9 f115.
Notation p119 := (ABS _r i78). (* ABS(r, [0, 0.00274658]) *)
Lemma t84 : p119 -> p119 -> p118.
Proof.
 intros h0 h1.
 refine (mul_aa _r _r i78 i78 i77 h0 h1 _) ; finalize.
Qed.
Lemma l93 : s1 -> p118 (* ABS(r * r, [0, 7.62939e-06]) *).
Proof.
 intros h0.
 assert (h1 := l10 h0).
 apply t84. refine (abs_subset _r i8 i78 h1 _) ; finalize. refine (abs_subset _r i8 i78 h1 _) ; finalize.
Qed.
Lemma t85 : p118 -> p117.
Proof.
 intros h0.
 refine (float_absolute_wide_ne _ _ r7 i77 i76 h0 _) ; finalize.
Qed.
Lemma l92 : s1 -> p117 (* BND(r2 - r * r, [-4.23516e-22, 4.23516e-22]) *).
Proof.
 intros h0.
 assert (h1 := l93 h0).
 apply t85. exact h1.
Qed.
Definition f116 := Float2 (1292291054641845035912781625876609444665749266013853025740447708219566176402826169893434244842740854699472900921412917639) (-400).
Definition i79 := makepairF f15 f116.
Notation p120 := (BND _H i79). (* BND(H, [0.25, 0.500452]) *)
Definition f117 := Float2 (1166115598390741084822039875103507500896369599241269325118029949242365394405572578611568202671938981521314935039170951) (-400).
Definition i80 := makepairF f19 f117.
Notation p121 := (BND r31 i80). (* BND(r * T3, [-0.25, 0.000451589]) *)
Definition f118 := Float2 (3364581789868768595181218940150737655852896367423428224132883620214935053290074886583770943374274584752842977432331149) (-393).
Definition i81 := makepairF f21 f118.
Notation p122 := (BND _T3 i81). (* BND(T3, [0.125, 0.16678]) *)
Definition f119 := Float2 (2277261109883529807354956612870111638599992928097442979159492429688528251293794808731777564067240027012121543861133) (-393).
Definition i82 := makepairF f25 f119.
Notation p123 := (BND r33 i82). (* BND(r * T4, [-0.03125, 0.000112882]) *)
Definition f120 := Float2 (410659933268204486740605461693682534451805147144284662136765857714610808140506055490291857925437472555863822649645) (-382).
Definition i83 := makepairF f27 f120.
Notation p124 := (BND _T4 i83). (* BND(T4, [0.03125, 0.0416892]) *)
Definition f121 := Float2 (222368722438937134332930841956265633312342735642241422860018491309831588904808379754073171858911760407670638893) (-382).
Definition i84 := makepairF f31 f121.
Notation p125 := (BND r35 i84). (* BND(r * T5, [-0.0078125, 2.25744e-05]) *)
Definition f122 := Float2 (2566393092372414022197469738572700462019688476869684405353465248525404274208834755443655730173576287158735260703) (-377).
Definition i85 := makepairF f33 f122.
Notation p126 := (BND _T5 i85). (* BND(T5, [0.0078125, 0.0083371]) *)
Lemma t86 : p31 -> p33 -> p126.
Proof.
 intros h0 h1.
 refine (add _c5 r27 i21 i23 i85 h0 h1 _) ; finalize.
Qed.
Lemma l100 : s1 -> p126 (* BND(T5, [0.0078125, 0.0083371]) *).
Proof.
 intros h0.
 assert (h1 := l30 h0).
 assert (h2 := l32 h0).
 apply t86. exact h1. exact h2.
Qed.
Definition f123 := Float2 (6668050761123583210192997304947428943750900626414955621425224628167258802542687323282900546146992880038256663085) (-380).
Definition i86 := makepairF f44 f123.
Notation p127 := (BND _r i86). (* BND(r, [-0.5, 0.0027077]) *)
Lemma t87 : p127 -> p126 -> p125.
Proof.
 intros h0 h1.
 refine (mul_op _r _T5 i86 i85 i84 h0 h1 _) ; finalize.
Qed.
Lemma l99 : s1 -> p125 (* BND(r * T5, [-0.0078125, 2.25744e-05]) *).
Proof.
 intros h0.
 assert (h1 := l11 h0).
 assert (h2 := l100 h0).
 apply t87. refine (subset _r i1 i86 h1 _) ; finalize. exact h2.
Qed.
Lemma t88 : p26 -> p125 -> p124.
Proof.
 intros h0 h1.
 refine (add _c4 r35 i18 i84 i83 h0 h1 _) ; finalize.
Qed.
Lemma l98 : s1 -> p124 (* BND(T4, [0.03125, 0.0416892]) *).
Proof.
 intros h0.
 assert (h1 := l25 h0).
 assert (h2 := l99 h0).
 apply t88. exact h1. exact h2.
Qed.
Definition f124 := Float2 (13656167958781098414475258480532334476801844482897829112678860038486546027607423638083380318509041418318349645997283) (-391).
Definition i87 := makepairF f44 f124.
Notation p128 := (BND _r i87). (* BND(r, [-0.5, 0.0027077]) *)
Lemma t89 : p128 -> p124 -> p123.
Proof.
 intros h0 h1.
 refine (mul_op _r _T4 i87 i83 i82 h0 h1 _) ; finalize.
Qed.
Lemma l97 : s1 -> p123 (* BND(r * T4, [-0.03125, 0.000112882]) *).
Proof.
 intros h0.
 assert (h1 := l11 h0).
 assert (h2 := l98 h0).
 apply t89. refine (subset _r i1 i87 h1 _) ; finalize. exact h2.
Qed.
Lemma t90 : p21 -> p123 -> p122.
Proof.
 intros h0 h1.
 refine (add _c3 r33 i15 i82 i81 h0 h1 _) ; finalize.
Qed.
Lemma l96 : s1 -> p122 (* BND(T3, [0.125, 0.16678]) *).
Proof.
 intros h0.
 assert (h1 := l20 h0).
 assert (h2 := l97 h0).
 apply t90. exact h1. exact h2.
Qed.
Definition i88 := makepairF f48 f109.
Notation p129 := (BND _r i88). (* BND(r, [-1, 0.0027077]) *)
Lemma t91 : p129 -> p122 -> p121.
Proof.
 intros h0 h1.
 refine (mul_op _r _T3 i88 i81 i80 h0 h1 _) ; finalize.
Qed.
Lemma l95 : s1 -> p121 (* BND(r * T3, [-0.25, 0.000451589]) *).
Proof.
 intros h0.
 assert (h1 := l11 h0).
 assert (h2 := l96 h0).
 apply t91. refine (subset _r i1 i88 h1 _) ; finalize. exact h2.
Qed.
Lemma t92 : p16 -> p121 -> p120.
Proof.
 intros h0 h1.
 refine (add r10 r31 i12 i80 i79 h0 h1 _) ; finalize.
Qed.
Lemma l94 : s1 -> p120 (* BND(H, [0.25, 0.500452]) *).
Proof.
 intros h0.
 assert (h1 := l15 h0).
 assert (h2 := l95 h0).
 apply t92. exact h1. exact h2.
Qed.
Lemma t93 : p117 -> p120 -> p116.
Proof.
 intros h0 h1.
 refine (mul_op r44 _H i76 i79 i75 h0 h1 _) ; finalize.
Qed.
Lemma l91 : s1 -> p116 (* BND((r2 - r * r) * H, [-2.11949e-22, 2.11949e-22]) *).
Proof.
 intros h0.
 assert (h1 := l92 h0).
 assert (h2 := l94 h0).
 apply t93. exact h1. exact h2.
Qed.
Lemma t94 : p45 -> p116 -> p44.
Proof.
 intros h0 h1.
 refine (add r41 r43 i32 i75 i31 h0 h1 _) ; finalize.
Qed.
Lemma l35 : s1 -> p44 (* BND(r2 * (h - H) + (r2 - r * r) * H, [-6.19779e-22, 6.19779e-22]) *).
Proof.
 intros h0.
 assert (h1 := l36 h0).
 assert (h2 := l91 h0).
 apply t94. exact h1. exact h2.
Qed.
Lemma t95 : p44 -> p43.
Proof.
 intros h0.
 refine (mul_mars _ _ _ _ i31 h0) ; finalize.
Qed.
Lemma l34 : s1 -> p43 (* BND(r2 * h - Q, [-6.19779e-22, 6.19779e-22]) *).
Proof.
 intros h0.
 assert (h1 := l35 h0).
 apply t95. exact h1.
Qed.
Lemma t96 : p5 -> p43 -> p4.
Proof.
 intros h0 h1.
 refine (add r38 r39 i4 i31 i3 h0 h1 _) ; finalize.
Qed.
Lemma l4 : s1 -> p4 (* BND(q - r2 * h + (r2 * h - Q), [-8.31538e-22, 8.31538e-22]) *).
Proof.
 intros h0.
 assert (h1 := l5 h0).
 assert (h2 := l34 h0).
 apply t96. exact h1. exact h2.
Qed.
Lemma t97 : p4 -> p3.
Proof.
 intros h0.
 refine (sub_xals _ _ _ i3 h0) ; finalize.
Qed.
Lemma l3 : s1 -> p3 (* BND(q - Q, [-8.31538e-22, 8.31538e-22]) *).
Proof.
 intros h0.
 assert (h1 := l4 h0).
 apply t97. exact h1.
Qed.
Lemma l1 : s1 -> False.
Proof.
 intros h0.
 assert (h1 := l2 h0).
 assert (h2 := l3 h0).
 refine (simplify (Tatom false (Abnd 0%nat i2)) Tfalse (Abnd 0%nat i3) (List.cons r3 List.nil) h2 h1 _) ; finalize.
Qed.
End Generated_by_Gappa.
