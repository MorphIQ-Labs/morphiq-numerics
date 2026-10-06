Require Import Gappa.Gappa_library.
Section Generated_by_Gappa.
Variable _R : R.
Variable _n_ : R.
Notation _n := ((rounding_fixed rndNE (0)%Z) _n_).
Notation _L2 := (float2R (Float2 (-7988006341064857) (-96))).
Notation _L3 := (float2R (Float2 (6759741496705267) (-151))).
Notation r12 := ((_L2 + _L3)%R).
Notation _L4 := (float2R (Float2 (4725274267454307) (-205))).
Notation r11 := ((r12 + _L4)%R).
Variable _dL : R.
Notation r10 := ((r11 + _dL)%R).
Notation r7 := ((_n * r10)%R).
Notation _r1 := ((_R + r7)%R).
Notation r18 := ((_n * _L2)%R).
Notation _p2 := ((rounding_float rndNE (53)%positive (-1074)%Z) r18).
Notation r4 := ((_r1 - _p2)%R).
Notation _s := ((rounding_float rndNE (53)%positive (-1074)%Z) r4).
Notation _t := ((r4 - _s)%R).
Notation _e2 := ((r18 - _p2)%R).
Notation r22 := ((_t - _e2)%R).
Notation _u1 := ((rounding_float rndNE (53)%positive (-1074)%Z) r22).
Notation r26 := ((_n * _L3)%R).
Notation _u2 := ((rounding_float rndNE (53)%positive (-1074)%Z) r26).
Notation r20 := ((_u1 - _u2)%R).
Notation _rr := ((rounding_float rndNE (53)%positive (-1074)%Z) r20).
Notation r2 := ((_s + _rr)%R).
Notation r1 := ((r2 - _R)%R).
Notation r30 := ((_u1 - r22)%R).
Notation r31 := ((_u2 - r26)%R).
Notation r29 := ((r30 - r31)%R).
Notation r32 := ((_rr - r20)%R).
Notation r28 := ((r29 + r32)%R).
Notation r34 := ((_L4 + _dL)%R).
Notation r33 := ((_n * r34)%R).
Notation r27 := ((r28 + r33)%R).
Hypothesis a1 : r1 = r27.
Lemma b1 : r1 = r27.
 apply a1.
Qed.
Definition f1 := Float2 (-137601) (0).
Definition f2 := Float2 (137601) (0).
Definition i1 := makepairF f1 f2.
Notation p1 := (BND _n i1). (* BND(n, [-137601, 137601]) *)
Definition f3 := Float2 (-1789941246693356131382101079560334144543371360062384257457043542964508560930560231090864825107617076781822724800155747281) (-408).
Definition f4 := Float2 (1789941246693356131382101079560334144543371360062384257457043542964508560930560231090864825107617076781822724800155747281) (-408).
Definition i2 := makepairF f3 f4.
Notation p2 := (BND _R i2). (* BND(R, [-0.0027077, 0.0027077]) *)
Definition s3 := (p1 /\ p2).
Definition f5 := Float2 (-1) (-206).
Definition f6 := Float2 (1) (-206).
Definition i3 := makepairF f5 f6.
Notation p3 := (BND _dL i3). (* BND(dL, [-9.72346e-63, 9.72346e-63]) *)
Definition s2 := (s3 /\ p3).
Definition f7 := Float2 (-1) (-113).
Definition f8 := Float2 (1) (-113).
Definition i4 := makepairF f7 f8.
Notation p4 := (BND r1 i4). (* BND(s + rr - R, [-9.62965e-35, 9.62965e-35]) *)
Definition s4 := (not p4).
Definition s1 := (s2 /\ s4).
Lemma l2 : s1 -> s4.
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj2 h1).
Qed.
Definition f9 := Float2 (-4951776984051415978235783495) (-206).
Definition f10 := Float2 (4951776984051415978235783495) (-206).
Definition i5 := makepairF f9 f10.
Notation p5 := (BND r1 i5). (* BND(s + rr - R, [-4.81484e-35, 4.81484e-35]) *)
Notation p6 := (BND r27 i5). (* BND(u1 - (t - e2) - (u2 - n * L3) + (rr - (u1 - u2)) + n * (L4 + dL), [-4.81484e-35, 4.81484e-35]) *)
Definition f11 := Float2 (-9444762580197309544135) (-187).
Definition f12 := Float2 (9444762580197309544135) (-187).
Definition i6 := makepairF f11 f12.
Notation p7 := (BND r28 i6). (* BND(u1 - (t - e2) - (u2 - n * L3) + (rr - (u1 - u2)), [-4.81484e-35, 4.81484e-35]) *)
Definition f13 := Float2 (-1048577) (-135).
Definition f14 := Float2 (1048577) (-135).
Definition i7 := makepairF f13 f14.
Notation p8 := (BND r29 i7). (* BND(u1 - (t - e2) - (u2 - n * L3), [-2.40741e-35, 2.40741e-35]) *)
Definition f15 := Float2 (-1) (-115).
Definition f16 := Float2 (1) (-115).
Definition i8 := makepairF f15 f16.
Notation p9 := (BND r30 i8). (* BND(u1 - (t - e2), [-2.40741e-35, 2.40741e-35]) *)
Definition f17 := Float2 (0) (0).
Definition f18 := Float2 (1) (-61).
Definition i9 := makepairF f17 f18.
Notation p10 := (ABS r22 i9). (* ABS(t - e2, [0, 4.33681e-19]) *)
Definition f19 := Float2 (-262145) (-80).
Definition f20 := Float2 (262145) (-80).
Definition i10 := makepairF f19 f20.
Notation p11 := (BND r22 i10). (* BND(t - e2, [-2.16841e-19, 2.16841e-19]) *)
Definition f21 := Float2 (-1) (-62).
Definition f22 := Float2 (1) (-62).
Definition i11 := makepairF f21 f22.
Notation p12 := (BND _t i11). (* BND(t, [-2.1684e-19, 2.1684e-19]) *)
Notation r36 := ((r4 - r4)%R).
Notation r37 := ((_s - r4)%R).
Notation r35 := ((r36 - r37)%R).
Notation p13 := (BND r35 i11). (* BND(r1 - p2 - (r1 - p2) - (s - (r1 - p2)), [-2.1684e-19, 2.1684e-19]) *)
Definition i12 := makepairF f17 f17.
Notation p14 := (BND r36 i12). (* BND(r1 - p2 - (r1 - p2), [0, 0]) *)
Lemma t1 : p14.
Proof.
 refine (sub_refl _ i12 _) ; finalize.
Qed.
Lemma l12 : s1 -> p14 (* BND(r1 - p2 - (r1 - p2), [0, 0]) *).
Proof.
 intros h0.
 apply t1.
Qed.
Notation p15 := (BND r37 i11). (* BND(s - (r1 - p2), [-2.1684e-19, 2.1684e-19]) *)
Definition f23 := Float2 (1) (-8).
Definition i13 := makepairF f17 f23.
Notation p16 := (ABS r4 i13). (* ABS(r1 - p2, [0, 0.00390625]) *)
Definition f24 := Float2 (3) (-10).
Definition i14 := makepairF f17 f24.
Notation p17 := (ABS _r1 i14). (* ABS(r1, [0, 0.00292969]) *)
Definition f25 := Float2 (23) (-13).
Definition i15 := makepairF f17 f25.
Notation p18 := (ABS _R i15). (* ABS(R, [0, 0.00280762]) *)
Lemma l19 : s1 -> s2.
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj1 h1).
Qed.
Lemma l18 : s1 -> s3.
Proof.
 intros h0.
 assert (h1 := l19 h0).
 exact (proj1 h1).
Qed.
Lemma l17 : s1 -> p2 (* BND(R, [-0.0027077, 0.0027077]) *).
Proof.
 intros h0.
 assert (h1 := l18 h0).
 exact (proj2 h1).
Qed.
Definition f26 := Float2 (-23) (-13).
Definition i16 := makepairF f26 f25.
Notation p19 := (BND _R i16). (* BND(R, [-0.00280762, 0.00280762]) *)
Lemma t2 : p19 -> p18.
Proof.
 intros h0.
 refine (abs_of_bnd_o _R i16 i15 h0 _) ; finalize.
Qed.
Lemma l16 : s1 -> p18 (* ABS(R, [0, 0.00280762]) *).
Proof.
 intros h0.
 assert (h1 := l17 h0).
 apply t2. refine (subset _R i2 i16 h1 _) ; finalize.
Qed.
Definition f27 := Float2 (1) (-13).
Definition i17 := makepairF f17 f27.
Notation p20 := (ABS r7 i17). (* ABS(n * (L2 + L3 + L4 + dL), [0, 0.00012207]) *)
Definition f28 := Float2 (9) (14).
Definition i18 := makepairF f17 f28.
Notation p21 := (ABS _n i18). (* ABS(n, [0, 147456]) *)
Lemma l22 : s1 -> p1 (* BND(n, [-137601, 137601]) *).
Proof.
 intros h0.
 assert (h1 := l18 h0).
 exact (proj1 h1).
Qed.
Definition f29 := Float2 (-9) (14).
Definition i19 := makepairF f29 f28.
Notation p22 := (BND _n i19). (* BND(n, [-147456, 147456]) *)
Lemma t3 : p22 -> p21.
Proof.
 intros h0.
 refine (abs_of_bnd_o _n i19 i18 h0 _) ; finalize.
Qed.
Lemma l21 : s1 -> p21 (* ABS(n, [0, 147456]) *).
Proof.
 intros h0.
 assert (h1 := l22 h0).
 apply t3. refine (subset _n i1 i19 h1 _) ; finalize.
Qed.
Definition f30 := Float2 (1) (-44).
Definition f31 := Float2 (1) (-31).
Definition i20 := makepairF f30 f31.
Notation p23 := (ABS r10 i20). (* ABS(L2 + L3 + L4 + dL, [5.68434e-14, 4.65661e-10]) *)
Definition f32 := Float2 (3) (-45).
Definition f33 := Float2 (1) (-32).
Definition i21 := makepairF f32 f33.
Notation p24 := (ABS r11 i21). (* ABS(L2 + L3 + L4, [8.52651e-14, 2.32831e-10]) *)
Definition f34 := Float2 (-1) (-32).
Definition f35 := Float2 (-3) (-45).
Definition i22 := makepairF f34 f35.
Notation p25 := (BND r11 i22). (* BND(L2 + L3 + L4, [-2.32831e-10, -8.52651e-14]) *)
Definition f36 := Float2 (-7) (-46).
Definition i23 := makepairF f34 f36.
Notation p26 := (BND r12 i23). (* BND(L2 + L3, [-2.32831e-10, -9.9476e-14]) *)
Definition f37 := Float2 (-455) (-52).
Definition f38 := Float2 (-113) (-50).
Definition i24 := makepairF f37 f38.
Notation p27 := (BND _L2 i24). (* BND(L2, [-1.0103e-13, -1.00364e-13]) *)
Lemma t4 : p27.
Proof.
 refine (constant2 _ i24 _) ; finalize.
Qed.
Lemma l27 : s1 -> p27 (* BND(L2, [-1.0103e-13, -1.00364e-13]) *).
Proof.
 intros h0.
 apply t4.
Qed.
Definition f39 := Float2 (1) (-99).
Definition f40 := Float2 (6759741496705267) (-151).
Definition i25 := makepairF f39 f40.
Notation p28 := (BND _L3 i25). (* BND(L3, [1.57772e-30, 2.3681e-30]) *)
Lemma t5 : p28.
Proof.
 refine (constant2 _ i25 _) ; finalize.
Qed.
Lemma l28 : s1 -> p28 (* BND(L3, [1.57772e-30, 2.3681e-30]) *).
Proof.
 intros h0.
 apply t5.
Qed.
Definition i26 := makepairF f34 f38.
Notation p29 := (BND _L2 i26). (* BND(L2, [-2.32831e-10, -1.00364e-13]) *)
Definition f41 := Float2 (1) (-50).
Definition i27 := makepairF f39 f41.
Notation p30 := (BND _L3 i27). (* BND(L3, [1.57772e-30, 8.88178e-16]) *)
Lemma t6 : p29 -> p30 -> p26.
Proof.
 intros h0 h1.
 refine (add _L2 _L3 i26 i27 i23 h0 h1 _) ; finalize.
Qed.
Lemma l26 : s1 -> p26 (* BND(L2 + L3, [-2.32831e-10, -9.9476e-14]) *).
Proof.
 intros h0.
 assert (h1 := l27 h0).
 assert (h2 := l28 h0).
 apply t6. refine (subset _L2 i24 i26 h1 _) ; finalize. refine (subset _L3 i25 i27 h2 _) ; finalize.
Qed.
Definition f42 := Float2 (33) (-158).
Definition f43 := Float2 (4725274267454307) (-205).
Definition i28 := makepairF f42 f43.
Notation p31 := (BND _L4 i28). (* BND(L4, [9.03181e-47, 9.1892e-47]) *)
Lemma t7 : p31.
Proof.
 refine (constant2 _ i28 _) ; finalize.
Qed.
Lemma l29 : s1 -> p31 (* BND(L4, [9.03181e-47, 9.1892e-47]) *).
Proof.
 intros h0.
 apply t7.
Qed.
Definition f44 := Float2 (1) (-153).
Definition f45 := Float2 (1) (-46).
Definition i29 := makepairF f44 f45.
Notation p32 := (BND _L4 i29). (* BND(L4, [8.75812e-47, 1.42109e-14]) *)
Lemma t8 : p26 -> p32 -> p25.
Proof.
 intros h0 h1.
 refine (add r12 _L4 i23 i29 i22 h0 h1 _) ; finalize.
Qed.
Lemma l25 : s1 -> p25 (* BND(L2 + L3 + L4, [-2.32831e-10, -8.52651e-14]) *).
Proof.
 intros h0.
 assert (h1 := l26 h0).
 assert (h2 := l29 h0).
 apply t8. exact h1. refine (subset _L4 i28 i29 h2 _) ; finalize.
Qed.
Lemma t9 : p25 -> p24.
Proof.
 intros h0.
 refine (abs_of_bnd_n r11 i22 i21 h0 _) ; finalize.
Qed.
Lemma l24 : s1 -> p24 (* ABS(L2 + L3 + L4, [8.52651e-14, 2.32831e-10]) *).
Proof.
 intros h0.
 assert (h1 := l25 h0).
 apply t9. exact h1.
Qed.
Definition f46 := Float2 (1) (-45).
Definition i30 := makepairF f17 f46.
Notation p33 := (ABS _dL i30). (* ABS(dL, [0, 2.84217e-14]) *)
Lemma l31 : s1 -> p3 (* BND(dL, [-9.72346e-63, 9.72346e-63]) *).
Proof.
 intros h0.
 assert (h1 := l19 h0).
 exact (proj2 h1).
Qed.
Definition f47 := Float2 (-1) (-45).
Definition i31 := makepairF f47 f46.
Notation p34 := (BND _dL i31). (* BND(dL, [-2.84217e-14, 2.84217e-14]) *)
Lemma t10 : p34 -> p33.
Proof.
 intros h0.
 refine (abs_of_bnd_o _dL i31 i30 h0 _) ; finalize.
Qed.
Lemma l30 : s1 -> p33 (* ABS(dL, [0, 2.84217e-14]) *).
Proof.
 intros h0.
 assert (h1 := l31 h0).
 apply t10. refine (subset _dL i3 i31 h1 _) ; finalize.
Qed.
Lemma t11 : p24 -> p33 -> p23.
Proof.
 intros h0 h1.
 refine (add_aa_p r11 _dL i21 i30 i20 h0 h1 _) ; finalize.
Qed.
Lemma l23 : s1 -> p23 (* ABS(L2 + L3 + L4 + dL, [5.68434e-14, 4.65661e-10]) *).
Proof.
 intros h0.
 assert (h1 := l24 h0).
 assert (h2 := l30 h0).
 apply t11. exact h1. exact h2.
Qed.
Definition f48 := Float2 (1) (18).
Definition i32 := makepairF f17 f48.
Notation p35 := (ABS _n i32). (* ABS(n, [0, 262144]) *)
Lemma t12 : p35 -> p23 -> p20.
Proof.
 intros h0 h1.
 refine (mul_aa _n r10 i32 i20 i17 h0 h1 _) ; finalize.
Qed.
Lemma l20 : s1 -> p20 (* ABS(n * (L2 + L3 + L4 + dL), [0, 0.00012207]) *).
Proof.
 intros h0.
 assert (h1 := l21 h0).
 assert (h2 := l23 h0).
 apply t12. refine (abs_subset _n i18 i32 h1 _) ; finalize. exact h2.
Qed.
Lemma t13 : p18 -> p20 -> p17.
Proof.
 intros h0 h1.
 refine (add_aa_o _R r7 i15 i17 i14 h0 h1 _) ; finalize.
Qed.
Lemma l15 : s1 -> p17 (* ABS(r1, [0, 0.00292969]) *).
Proof.
 intros h0.
 assert (h1 := l16 h0).
 assert (h2 := l20 h0).
 apply t13. exact h1. exact h2.
Qed.
Definition f49 := Float2 (1) (-10).
Definition i33 := makepairF f17 f49.
Notation p36 := (ABS _p2 i33). (* ABS(p2, [0, 0.000976562]) *)
Definition f50 := Float2 (-1) (-10).
Definition i34 := makepairF f50 f49.
Notation p37 := (BND _p2 i34). (* BND(p2, [-0.000976562, 0.000976562]) *)
Notation p38 := (BND r18 i34). (* BND(n * L2, [-0.000976562, 0.000976562]) *)
Definition f51 := Float2 (-1) (18).
Definition i35 := makepairF f51 f48.
Notation p39 := (BND _n i35). (* BND(n, [-262144, 262144]) *)
Definition f52 := Float2 (-1) (-28).
Definition f53 := Float2 (-1) (-44).
Definition i36 := makepairF f52 f53.
Notation p40 := (BND _L2 i36). (* BND(L2, [-3.72529e-09, -5.68434e-14]) *)
Lemma t14 : p39 -> p40 -> p38.
Proof.
 intros h0 h1.
 refine (mul_on _n _L2 i35 i36 i34 h0 h1 _) ; finalize.
Qed.
Lemma l34 : s1 -> p38 (* BND(n * L2, [-0.000976562, 0.000976562]) *).
Proof.
 intros h0.
 assert (h1 := l22 h0).
 assert (h2 := l27 h0).
 apply t14. refine (subset _n i1 i35 h1 _) ; finalize. refine (subset _L2 i24 i36 h2 _) ; finalize.
Qed.
Lemma t15 : p38 -> p37.
Proof.
 intros h0.
 refine (float_round_ne _ _ r18 i34 i34 h0 _) ; finalize.
Qed.
Lemma l33 : s1 -> p37 (* BND(p2, [-0.000976562, 0.000976562]) *).
Proof.
 intros h0.
 assert (h1 := l34 h0).
 apply t15. exact h1.
Qed.
Lemma t16 : p37 -> p36.
Proof.
 intros h0.
 refine (abs_of_bnd_o _p2 i34 i33 h0 _) ; finalize.
Qed.
Lemma l32 : s1 -> p36 (* ABS(p2, [0, 0.000976562]) *).
Proof.
 intros h0.
 assert (h1 := l33 h0).
 apply t16. exact h1.
Qed.
Lemma t17 : p17 -> p36 -> p16.
Proof.
 intros h0 h1.
 refine (sub_aa_o _r1 _p2 i14 i33 i13 h0 h1 _) ; finalize.
Qed.
Lemma l14 : s1 -> p16 (* ABS(r1 - p2, [0, 0.00390625]) *).
Proof.
 intros h0.
 assert (h1 := l15 h0).
 assert (h2 := l32 h0).
 apply t17. exact h1. exact h2.
Qed.
Lemma t18 : p16 -> p15.
Proof.
 intros h0.
 refine (float_absolute_wide_ne _ _ r4 i13 i11 h0 _) ; finalize.
Qed.
Lemma l13 : s1 -> p15 (* BND(s - (r1 - p2), [-2.1684e-19, 2.1684e-19]) *).
Proof.
 intros h0.
 assert (h1 := l14 h0).
 apply t18. exact h1.
Qed.
Lemma t19 : p14 -> p15 -> p13.
Proof.
 intros h0 h1.
 refine (sub r36 r37 i12 i11 i11 h0 h1 _) ; finalize.
Qed.
Lemma l11 : s1 -> p13 (* BND(r1 - p2 - (r1 - p2) - (s - (r1 - p2)), [-2.1684e-19, 2.1684e-19]) *).
Proof.
 intros h0.
 assert (h1 := l12 h0).
 assert (h2 := l13 h0).
 apply t19. exact h1. exact h2.
Qed.
Lemma t20 : p13 -> p12.
Proof.
 intros h0.
 refine (sub_xars _ _ _ i11 h0) ; finalize.
Qed.
Lemma l10 : s1 -> p12 (* BND(t, [-2.1684e-19, 2.1684e-19]) *).
Proof.
 intros h0.
 assert (h1 := l11 h0).
 apply t20. exact h1.
Qed.
Definition f54 := Float2 (-1) (-80).
Definition f55 := Float2 (1) (-80).
Definition i37 := makepairF f54 f55.
Notation p41 := (BND _e2 i37). (* BND(e2, [-8.27181e-25, 8.27181e-25]) *)
Notation r39 := ((r18 - r18)%R).
Notation r40 := ((_p2 - r18)%R).
Notation r38 := ((r39 - r40)%R).
Notation p42 := (BND r38 i37). (* BND(n * L2 - n * L2 - (p2 - n * L2), [-8.27181e-25, 8.27181e-25]) *)
Notation p43 := (BND r39 i12). (* BND(n * L2 - n * L2, [0, 0]) *)
Lemma t21 : p43.
Proof.
 refine (sub_refl _ i12 _) ; finalize.
Qed.
Lemma l37 : s1 -> p43 (* BND(n * L2 - n * L2, [0, 0]) *).
Proof.
 intros h0.
 apply t21.
Qed.
Notation p44 := (BND r40 i37). (* BND(p2 - n * L2, [-8.27181e-25, 8.27181e-25]) *)
Definition f56 := Float2 (1) (-26).
Definition i38 := makepairF f17 f56.
Notation p45 := (ABS r18 i38). (* ABS(n * L2, [0, 1.49012e-08]) *)
Definition f57 := Float2 (455) (-52).
Definition i39 := makepairF f30 f57.
Notation p46 := (ABS _L2 i39). (* ABS(L2, [5.68434e-14, 1.0103e-13]) *)
Definition i40 := makepairF f37 f53.
Notation p47 := (BND _L2 i40). (* BND(L2, [-1.0103e-13, -5.68434e-14]) *)
Lemma t22 : p47 -> p46.
Proof.
 intros h0.
 refine (abs_of_bnd_n _L2 i40 i39 h0 _) ; finalize.
Qed.
Lemma l40 : s1 -> p46 (* ABS(L2, [5.68434e-14, 1.0103e-13]) *).
Proof.
 intros h0.
 assert (h1 := l27 h0).
 apply t22. refine (subset _L2 i24 i40 h1 _) ; finalize.
Qed.
Lemma t23 : p21 -> p46 -> p45.
Proof.
 intros h0 h1.
 refine (mul_aa _n _L2 i18 i39 i38 h0 h1 _) ; finalize.
Qed.
Lemma l39 : s1 -> p45 (* ABS(n * L2, [0, 1.49012e-08]) *).
Proof.
 intros h0.
 assert (h1 := l21 h0).
 assert (h2 := l40 h0).
 apply t23. exact h1. exact h2.
Qed.
Lemma t24 : p45 -> p44.
Proof.
 intros h0.
 refine (float_absolute_wide_ne _ _ r18 i38 i37 h0 _) ; finalize.
Qed.
Lemma l38 : s1 -> p44 (* BND(p2 - n * L2, [-8.27181e-25, 8.27181e-25]) *).
Proof.
 intros h0.
 assert (h1 := l39 h0).
 apply t24. exact h1.
Qed.
Lemma t25 : p43 -> p44 -> p42.
Proof.
 intros h0 h1.
 refine (sub r39 r40 i12 i37 i37 h0 h1 _) ; finalize.
Qed.
Lemma l36 : s1 -> p42 (* BND(n * L2 - n * L2 - (p2 - n * L2), [-8.27181e-25, 8.27181e-25]) *).
Proof.
 intros h0.
 assert (h1 := l37 h0).
 assert (h2 := l38 h0).
 apply t25. exact h1. exact h2.
Qed.
Lemma t26 : p42 -> p41.
Proof.
 intros h0.
 refine (sub_xars _ _ _ i37 h0) ; finalize.
Qed.
Lemma l35 : s1 -> p41 (* BND(e2, [-8.27181e-25, 8.27181e-25]) *).
Proof.
 intros h0.
 assert (h1 := l36 h0).
 apply t26. exact h1.
Qed.
Lemma t27 : p12 -> p41 -> p11.
Proof.
 intros h0 h1.
 refine (sub _t _e2 i11 i37 i10 h0 h1 _) ; finalize.
Qed.
Lemma l9 : s1 -> p11 (* BND(t - e2, [-2.16841e-19, 2.16841e-19]) *).
Proof.
 intros h0.
 assert (h1 := l10 h0).
 assert (h2 := l35 h0).
 apply t27. exact h1. exact h2.
Qed.
Definition f58 := Float2 (-1) (-61).
Definition i41 := makepairF f58 f18.
Notation p48 := (BND r22 i41). (* BND(t - e2, [-4.33681e-19, 4.33681e-19]) *)
Lemma t28 : p48 -> p10.
Proof.
 intros h0.
 refine (abs_of_bnd_o r22 i41 i9 h0 _) ; finalize.
Qed.
Lemma l8 : s1 -> p10 (* ABS(t - e2, [0, 4.33681e-19]) *).
Proof.
 intros h0.
 assert (h1 := l9 h0).
 apply t28. refine (subset r22 i10 i41 h1 _) ; finalize.
Qed.
Lemma t29 : p10 -> p9.
Proof.
 intros h0.
 refine (float_absolute_wide_ne _ _ r22 i9 i8 h0 _) ; finalize.
Qed.
Lemma l7 : s1 -> p9 (* BND(u1 - (t - e2), [-2.40741e-35, 2.40741e-35]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 apply t29. exact h1.
Qed.
Definition f59 := Float2 (-1) (-135).
Definition f60 := Float2 (1) (-135).
Definition i42 := makepairF f59 f60.
Notation p49 := (BND r31 i42). (* BND(u2 - n * L3, [-2.29589e-41, 2.29589e-41]) *)
Definition f61 := Float2 (1) (-81).
Definition i43 := makepairF f17 f61.
Notation p50 := (ABS r26 i43). (* ABS(n * L3, [0, 4.1359e-25]) *)
Definition f62 := Float2 (25) (-103).
Definition i44 := makepairF f39 f62.
Notation p51 := (ABS _L3 i44). (* ABS(L3, [1.57772e-30, 2.46519e-30]) *)
Notation p52 := (BND _L3 i44). (* BND(L3, [1.57772e-30, 2.46519e-30]) *)
Lemma t30 : p52 -> p51.
Proof.
 intros h0.
 refine (abs_of_bnd_p _L3 i44 i44 h0 _) ; finalize.
Qed.
Lemma l43 : s1 -> p51 (* ABS(L3, [1.57772e-30, 2.46519e-30]) *).
Proof.
 intros h0.
 assert (h1 := l28 h0).
 apply t30. refine (subset _L3 i25 i44 h1 _) ; finalize.
Qed.
Definition f63 := Float2 (5) (15).
Definition i45 := makepairF f17 f63.
Notation p53 := (ABS _n i45). (* ABS(n, [0, 163840]) *)
Lemma t31 : p53 -> p51 -> p50.
Proof.
 intros h0 h1.
 refine (mul_aa _n _L3 i45 i44 i43 h0 h1 _) ; finalize.
Qed.
Lemma l42 : s1 -> p50 (* ABS(n * L3, [0, 4.1359e-25]) *).
Proof.
 intros h0.
 assert (h1 := l21 h0).
 assert (h2 := l43 h0).
 apply t31. refine (abs_subset _n i18 i45 h1 _) ; finalize. exact h2.
Qed.
Lemma t32 : p50 -> p49.
Proof.
 intros h0.
 refine (float_absolute_wide_ne _ _ r26 i43 i42 h0 _) ; finalize.
Qed.
Lemma l41 : s1 -> p49 (* BND(u2 - n * L3, [-2.29589e-41, 2.29589e-41]) *).
Proof.
 intros h0.
 assert (h1 := l42 h0).
 apply t32. exact h1.
Qed.
Lemma t33 : p9 -> p49 -> p8.
Proof.
 intros h0 h1.
 refine (sub r30 r31 i8 i42 i7 h0 h1 _) ; finalize.
Qed.
Lemma l6 : s1 -> p8 (* BND(u1 - (t - e2) - (u2 - n * L3), [-2.40741e-35, 2.40741e-35]) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 assert (h2 := l41 h0).
 apply t33. exact h1. exact h2.
Qed.
Definition f64 := Float2 (-4722391593728036959943) (-187).
Definition f65 := Float2 (4722391593728036959943) (-187).
Definition i46 := makepairF f64 f65.
Notation p54 := (BND r32 i46). (* BND(rr - (u1 - u2), [-2.40743e-35, 2.40743e-35]) *)
Definition f66 := Float2 (-1) (-53).
Definition f67 := Float2 (1) (-53).
Definition i47 := makepairF f66 f67.
Notation p55 := (REL _rr r20 i47). (* REL(rr, u1 - u2, [-1.11022e-16, 1.11022e-16]) *)
Notation p56 := (FIX r20 (-1074)). (* FIX(u1 - u2, -1074) *)
Notation p57 := (FIX _u1 (-1074)). (* FIX(u1, -1074) *)
Lemma t34 : p57.
Proof.
 refine (fix_of_float _ _ _ _ (-1074) _) ; finalize.
Qed.
Lemma l47 : s1 -> p57 (* FIX(u1, -1074) *).
Proof.
 intros h0.
 apply t34.
Qed.
Notation p58 := (FIX _u2 (-1074)). (* FIX(u2, -1074) *)
Lemma t35 : p58.
Proof.
 refine (fix_of_float _ _ _ _ (-1074) _) ; finalize.
Qed.
Lemma l48 : s1 -> p58 (* FIX(u2, -1074) *).
Proof.
 intros h0.
 apply t35.
Qed.
Lemma t36 : p57 -> p58 -> p56.
Proof.
 intros h0 h1.
 refine (sub_fix _u1 _u2 (-1074) (-1074) (-1074) h0 h1 _) ; finalize.
Qed.
Lemma l46 : s1 -> p56 (* FIX(u1 - u2, -1074) *).
Proof.
 intros h0.
 assert (h1 := l47 h0).
 assert (h2 := l48 h0).
 apply t36. exact h1. exact h2.
Qed.
Lemma t37 : p56 -> p55.
Proof.
 intros h0.
 refine (rel_of_fix_float_ne _ _ (-1074) r20 i47 h0 _) ; finalize.
Qed.
Lemma l45 : s1 -> p55 (* REL(rr, u1 - u2, [-1.11022e-16, 1.11022e-16]) *).
Proof.
 intros h0.
 assert (h1 := l46 h0).
 apply t37. exact h1.
Qed.
Definition f68 := Float2 (-4722391593728036959943) (-134).
Definition f69 := Float2 (4722391593728036959943) (-134).
Definition i48 := makepairF f68 f69.
Notation p59 := (BND r20 i48). (* BND(u1 - u2, [-2.16842e-19, 2.16842e-19]) *)
Notation p60 := (BND _u1 i10). (* BND(u1, [-2.16841e-19, 2.16841e-19]) *)
Lemma t38 : p11 -> p60.
Proof.
 intros h0.
 refine (float_round_ne _ _ r22 i10 i10 h0 _) ; finalize.
Qed.
Lemma l50 : s1 -> p60 (* BND(u1, [-2.16841e-19, 2.16841e-19]) *).
Proof.
 intros h0.
 assert (h1 := l9 h0).
 apply t38. exact h1.
Qed.
Definition f70 := Float2 (-7096459882264263) (-134).
Definition f71 := Float2 (7096459882264263) (-134).
Definition i49 := makepairF f70 f71.
Notation p61 := (BND _u2 i49). (* BND(u2, [-3.25853e-25, 3.25853e-25]) *)
Notation p62 := (BND r26 i49). (* BND(n * L3, [-3.25853e-25, 3.25853e-25]) *)
Lemma t39 : p1 -> p28 -> p62.
Proof.
 intros h0 h1.
 refine (mul_op _n _L3 i1 i25 i49 h0 h1 _) ; finalize.
Qed.
Lemma l52 : s1 -> p62 (* BND(n * L3, [-3.25853e-25, 3.25853e-25]) *).
Proof.
 intros h0.
 assert (h1 := l22 h0).
 assert (h2 := l28 h0).
 apply t39. exact h1. exact h2.
Qed.
Lemma t40 : p62 -> p61.
Proof.
 intros h0.
 refine (float_round_ne _ _ r26 i49 i49 h0 _) ; finalize.
Qed.
Lemma l51 : s1 -> p61 (* BND(u2, [-3.25853e-25, 3.25853e-25]) *).
Proof.
 intros h0.
 assert (h1 := l52 h0).
 apply t40. exact h1.
Qed.
Lemma t41 : p60 -> p61 -> p59.
Proof.
 intros h0 h1.
 refine (sub _u1 _u2 i10 i49 i48 h0 h1 _) ; finalize.
Qed.
Lemma l49 : s1 -> p59 (* BND(u1 - u2, [-2.16842e-19, 2.16842e-19]) *).
Proof.
 intros h0.
 assert (h1 := l50 h0).
 assert (h2 := l51 h0).
 apply t41. exact h1. exact h2.
Qed.
Lemma t42 : p55 -> p59 -> p54.
Proof.
 intros h0 h1.
 refine (error_of_rel_oo _rr r20 i47 i48 i46 h0 h1 _) ; finalize.
Qed.
Lemma l44 : s1 -> p54 (* BND(rr - (u1 - u2), [-2.40743e-35, 2.40743e-35]) *).
Proof.
 intros h0.
 assert (h1 := l45 h0).
 assert (h2 := l49 h0).
 apply t42. exact h1. exact h2.
Qed.
Lemma t43 : p8 -> p54 -> p7.
Proof.
 intros h0 h1.
 refine (add r29 r32 i7 i46 i6 h0 h1 _) ; finalize.
Qed.
Lemma l5 : s1 -> p7 (* BND(u1 - (t - e2) - (u2 - n * L3) + (rr - (u1 - u2)), [-4.81484e-35, 4.81484e-35]) *).
Proof.
 intros h0.
 assert (h1 := l6 h0).
 assert (h2 := l44 h0).
 apply t43. exact h1. exact h2.
Qed.
Definition f72 := Float2 (-1300404928951960332615) (-206).
Definition f73 := Float2 (1300404928951960332615) (-206).
Definition i50 := makepairF f72 f73.
Notation p63 := (BND r33 i50). (* BND(n * (L4 + dL), [-1.26444e-41, 1.26444e-41]) *)
Definition f74 := Float2 (9450548534908615) (-206).
Definition i51 := makepairF f44 f74.
Notation p64 := (BND r34 i51). (* BND(L4 + dL, [8.75812e-47, 9.1892e-47]) *)
Definition f75 := Float2 (-1) (-158).
Definition i52 := makepairF f75 f6.
Notation p65 := (BND _dL i52). (* BND(dL, [-2.73691e-48, 9.72346e-63]) *)
Lemma t44 : p31 -> p65 -> p64.
Proof.
 intros h0 h1.
 refine (add _L4 _dL i28 i52 i51 h0 h1 _) ; finalize.
Qed.
Lemma l54 : s1 -> p64 (* BND(L4 + dL, [8.75812e-47, 9.1892e-47]) *).
Proof.
 intros h0.
 assert (h1 := l29 h0).
 assert (h2 := l31 h0).
 apply t44. exact h1. refine (subset _dL i3 i52 h2 _) ; finalize.
Qed.
Lemma t45 : p1 -> p64 -> p63.
Proof.
 intros h0 h1.
 refine (mul_op _n r34 i1 i51 i50 h0 h1 _) ; finalize.
Qed.
Lemma l53 : s1 -> p63 (* BND(n * (L4 + dL), [-1.26444e-41, 1.26444e-41]) *).
Proof.
 intros h0.
 assert (h1 := l22 h0).
 assert (h2 := l54 h0).
 apply t45. exact h1. exact h2.
Qed.
Lemma t46 : p7 -> p63 -> p6.
Proof.
 intros h0 h1.
 refine (add r28 r33 i6 i50 i5 h0 h1 _) ; finalize.
Qed.
Lemma l4 : s1 -> p6 (* BND(u1 - (t - e2) - (u2 - n * L3) + (rr - (u1 - u2)) + n * (L4 + dL), [-4.81484e-35, 4.81484e-35]) *).
Proof.
 intros h0.
 assert (h1 := l5 h0).
 assert (h2 := l53 h0).
 apply t46. exact h1. exact h2.
Qed.
Notation p66 := (REL r1 r27 i12). (* REL(s + rr - R, u1 - (t - e2) - (u2 - n * L3) + (rr - (u1 - u2)) + n * (L4 + dL), [0, 0]) *)
Notation p67 := (r1 = r27). (* EQL(s + rr - R, u1 - (t - e2) - (u2 - n * L3) + (rr - (u1 - u2)) + n * (L4 + dL)) *)
Lemma t47 : p67.
Proof.
 refine (b1) ; finalize.
Qed.
Lemma l56 : s1 -> p67 (* EQL(s + rr - R, u1 - (t - e2) - (u2 - n * L3) + (rr - (u1 - u2)) + n * (L4 + dL)) *).
Proof.
 intros h0.
 apply t47.
Qed.
Notation p68 := (REL r27 r27 i12). (* REL(u1 - (t - e2) - (u2 - n * L3) + (rr - (u1 - u2)) + n * (L4 + dL), u1 - (t - e2) - (u2 - n * L3) + (rr - (u1 - u2)) + n * (L4 + dL), [0, 0]) *)
Lemma t48 : p68.
Proof.
 refine (rel_refl r27 i12 _) ; finalize.
Qed.
Lemma l57 : s1 -> p68 (* REL(u1 - (t - e2) - (u2 - n * L3) + (rr - (u1 - u2)) + n * (L4 + dL), u1 - (t - e2) - (u2 - n * L3) + (rr - (u1 - u2)) + n * (L4 + dL), [0, 0]) *).
Proof.
 intros h0.
 apply t48.
Qed.
Lemma t49 : p67 -> p68 -> p66.
Proof.
 intros h0 h1.
 refine (rel_rewrite_1 r1 r27 r27 i12 h0 h1) ; finalize.
Qed.
Lemma l55 : s1 -> p66 (* REL(s + rr - R, u1 - (t - e2) - (u2 - n * L3) + (rr - (u1 - u2)) + n * (L4 + dL), [0, 0]) *).
Proof.
 intros h0.
 assert (h1 := l56 h0).
 assert (h2 := l57 h0).
 apply t49. exact h1. exact h2.
Qed.
Lemma t50 : p6 -> p66 -> p5.
Proof.
 intros h0 h1.
 refine (bnd_of_bnd_rel_o r1 r27 i5 i12 i5 h0 h1 _) ; finalize.
Qed.
Lemma l3 : s1 -> p5 (* BND(s + rr - R, [-4.81484e-35, 4.81484e-35]) *).
Proof.
 intros h0.
 assert (h1 := l4 h0).
 assert (h2 := l55 h0).
 apply t50. exact h1. exact h2.
Qed.
Lemma l1 : s1 -> False.
Proof.
 intros h0.
 assert (h1 := l2 h0).
 assert (h2 := l3 h0).
 refine (simplify (Tatom false (Abnd 0%nat i4)) Tfalse (Abnd 0%nat i5) (List.cons r1 List.nil) h2 h1 _) ; finalize.
Qed.
End Generated_by_Gappa.
