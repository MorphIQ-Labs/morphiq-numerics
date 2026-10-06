Require Import Gappa.Gappa_library.
Section Generated_by_Gappa.
Notation _k1 := (Float1 0).
Notation r7 := (Float1 (1)).
Variable _lam : R.
Notation r6 := ((r7 + _lam)%R).
Notation r4 := ((_k1 * r6)%R).
Variable _k3 : R.
Notation _k2 := ((r7 - _k3)%R).
Variable _dT : R.
Notation r14 := ((r7 + _dT)%R).
Notation r11 := ((_k2 * r14)%R).
Variable _dP : R.
Notation r17 := ((r7 + _dP)%R).
Notation r16 := ((_k3 * r17)%R).
Notation r10 := ((r11 + r16)%R).
Variable _e1 : R.
Notation r19 := ((r7 + _e1)%R).
Notation r9 := ((r10 * r19)%R).
Notation r3 := ((r4 + r9)%R).
Variable _e2 : R.
Notation r21 := ((r7 + _e2)%R).
Notation _Y := ((r3 * r21)%R).
Notation r1 := ((_Y - r7)%R).
Notation r26 := ((_k1 * _lam)%R).
Notation r29 := ((_k2 * _dT)%R).
Notation r30 := ((_k3 * _dP)%R).
Notation r28 := ((r29 + r30)%R).
Notation r27 := ((r28 * r19)%R).
Notation r25 := ((r26 + r27)%R).
Notation r32 := ((_k2 + _k3)%R).
Notation r31 := ((r32 * _e1)%R).
Notation r24 := ((r25 + r31)%R).
Notation r33 := ((r3 * _e2)%R).
Notation r23 := ((r24 + r33)%R).
Hypothesis a1 : r1 = r23.
Lemma b1 : r1 = r23.
 apply a1.
Qed.
Definition f1 := Float2 (-533) (-10).
Definition f2 := Float2 (533) (-10).
Definition i1 := makepairF f1 f2.
Notation p1 := (BND _k3 i1). (* BND(k3, [-0.520508, 0.520508]) *)
Definition f3 := Float2 (-123) (-114).
Definition f4 := Float2 (123) (-114).
Definition i2 := makepairF f3 f4.
Notation p2 := (BND _dT i2). (* BND(dT, [-5.92223e-33, 5.92223e-33]) *)
Definition s6 := (p1 /\ p2).
Definition f5 := Float2 (-745) (-106).
Definition f6 := Float2 (745) (-106).
Definition i3 := makepairF f5 f6.
Notation p3 := (BND _lam i3). (* BND(lam, [-9.18283e-30, 9.18283e-30]) *)
Definition s5 := (s6 /\ p3).
Definition f7 := Float2 (-3) (-66).
Definition f8 := Float2 (3) (-66).
Definition i4 := makepairF f7 f8.
Notation p4 := (BND _dP i4). (* BND(dP, [-4.06576e-20, 4.06576e-20]) *)
Definition s4 := (s5 /\ p4).
Definition f9 := Float2 (-97) (-111).
Definition f10 := Float2 (97) (-111).
Definition i5 := makepairF f9 f10.
Notation p5 := (BND _e1 i5). (* BND(e1, [-3.7363e-32, 3.7363e-32]) *)
Definition s3 := (s4 /\ p5).
Notation p6 := (BND _e2 i5). (* BND(e2, [-3.7363e-32, 3.7363e-32]) *)
Definition s2 := (s3 /\ p6).
Definition f11 := Float2 (-1) (-64).
Definition f12 := Float2 (1) (-64).
Definition i6 := makepairF f11 f12.
Notation p7 := (BND r1 i6). (* BND(Y - 1, [-5.42101e-20, 5.42101e-20]) *)
Definition s7 := (not p7).
Definition s1 := (s2 /\ s7).
Lemma l2 : s1 -> s7.
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj2 h1).
Qed.
Definition f13 := Float2 (-3033523006535790626303708410760313126790896663531054080228648174030156862613780642135) (-346).
Definition f14 := Float2 (3033523006535790626303708410760313126790896663531054080228648174030156862613780642135) (-346).
Definition i7 := makepairF f13 f14.
Notation p8 := (BND r1 i7). (* BND(Y - 1, [-2.11626e-20, 2.11626e-20]) *)
Notation p9 := (BND r23 i7). (* BND(k1 * lam + (k2 * dT + k3 * dP) * (1 + e1) + (k2 + k3) * e1 + (k1 * (1 + lam) + (k2 * (1 + dT) + k3 * (1 + dP)) * (1 + e1)) * e2, [-2.11626e-20, 2.11626e-20]) *)
Definition f15 := Float2 (-1168470559050764611454206517864223633852774634714295) (-235).
Definition f16 := Float2 (1168470559050764611454206517864223633852774634714295) (-235).
Definition i8 := makepairF f15 f16.
Notation p10 := (BND r24 i8). (* BND(k1 * lam + (k2 * dT + k3 * dP) * (1 + e1) + (k2 + k3) * e1, [-2.11626e-20, 2.11626e-20]) *)
Definition f17 := Float2 (-1168470559046554074085683455443695683769483474465975) (-235).
Definition f18 := Float2 (1168470559046554074085683455443695683769483474465975) (-235).
Definition i9 := makepairF f17 f18.
Notation p11 := (BND r25 i9). (* BND(k1 * lam + (k2 * dT + k3 * dP) * (1 + e1), [-2.11626e-20, 2.11626e-20]) *)
Definition f19 := Float2 (0) (0).
Definition i10 := makepairF f19 f19.
Notation p12 := (BND r26 i10). (* BND(k1 * lam, [0, 0]) *)
Notation p13 := (BND _k1 i10). (* BND(k1, [0, 0]) *)
Lemma t1 : p13.
Proof.
 refine (constant1 _ i10 _) ; finalize.
Qed.
Lemma l8 : s1 -> p13 (* BND(k1, [0, 0]) *).
Proof.
 intros h0.
 apply t1.
Qed.
Lemma l13 : s1 -> s2.
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj1 h1).
Qed.
Lemma l12 : s1 -> s3.
Proof.
 intros h0.
 assert (h1 := l13 h0).
 exact (proj1 h1).
Qed.
Lemma l11 : s1 -> s4.
Proof.
 intros h0.
 assert (h1 := l12 h0).
 exact (proj1 h1).
Qed.
Lemma l10 : s1 -> s5.
Proof.
 intros h0.
 assert (h1 := l11 h0).
 exact (proj1 h1).
Qed.
Lemma l9 : s1 -> p3 (* BND(lam, [-9.18283e-30, 9.18283e-30]) *).
Proof.
 intros h0.
 assert (h1 := l10 h0).
 exact (proj2 h1).
Qed.
Definition f20 := Float2 (-1) (0).
Definition f21 := Float2 (1) (0).
Definition i11 := makepairF f20 f21.
Notation p14 := (BND _lam i11). (* BND(lam, [-1, 1]) *)
Lemma t2 : p13 -> p14 -> p12.
Proof.
 intros h0 h1.
 refine (mul_po _k1 _lam i10 i11 i10 h0 h1 _) ; finalize.
Qed.
Lemma l7 : s1 -> p12 (* BND(k1 * lam, [0, 0]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 assert (h2 := l9 h0).
 apply t2. exact h1. refine (subset _lam i3 i11 h2 _) ; finalize.
Qed.
Notation p15 := (BND r27 i9). (* BND((k2 * dT + k3 * dP) * (1 + e1), [-2.11626e-20, 2.11626e-20]) *)
Definition f22 := Float2 (-450078487760530455) (-124).
Definition f23 := Float2 (450078487760530455) (-124).
Definition i12 := makepairF f22 f23.
Notation p16 := (BND r28 i12). (* BND(k2 * dT + k3 * dP, [-2.11626e-20, 2.11626e-20]) *)
Definition f24 := Float2 (-191511) (-124).
Definition f25 := Float2 (191511) (-124).
Definition i13 := makepairF f24 f25.
Notation p17 := (BND r29 i13). (* BND(k2 * dT, [-9.0048e-33, 9.0048e-33]) *)
Definition f26 := Float2 (3) (-3).
Definition f27 := Float2 (1557) (-10).
Definition i14 := makepairF f26 f27.
Notation p18 := (BND _k2 i14). (* BND(k2, [0.375, 1.52051]) *)
Definition i15 := makepairF f21 f21.
Notation p19 := (BND r7 i15). (* BND(1, [1, 1]) *)
Lemma t3 : p19.
Proof.
 refine (constant1 _ i15 _) ; finalize.
Qed.
Lemma l18 : s1 -> p19 (* BND(1, [1, 1]) *).
Proof.
 intros h0.
 apply t3.
Qed.
Lemma l20 : s1 -> s6.
Proof.
 intros h0.
 assert (h1 := l10 h0).
 exact (proj1 h1).
Qed.
Lemma l19 : s1 -> p1 (* BND(k3, [-0.520508, 0.520508]) *).
Proof.
 intros h0.
 assert (h1 := l20 h0).
 exact (proj1 h1).
Qed.
Definition f28 := Float2 (5) (-3).
Definition i16 := makepairF f1 f28.
Notation p20 := (BND _k3 i16). (* BND(k3, [-0.520508, 0.625]) *)
Lemma t4 : p19 -> p20 -> p18.
Proof.
 intros h0 h1.
 refine (sub r7 _k3 i15 i16 i14 h0 h1 _) ; finalize.
Qed.
Lemma l17 : s1 -> p18 (* BND(k2, [0.375, 1.52051]) *).
Proof.
 intros h0.
 assert (h1 := l18 h0).
 assert (h2 := l19 h0).
 apply t4. exact h1. refine (subset _k3 i1 i16 h2 _) ; finalize.
Qed.
Lemma l21 : s1 -> p2 (* BND(dT, [-5.92223e-33, 5.92223e-33]) *).
Proof.
 intros h0.
 assert (h1 := l20 h0).
 exact (proj2 h1).
Qed.
Definition f29 := Float2 (1) (-2).
Definition i17 := makepairF f29 f27.
Notation p21 := (BND _k2 i17). (* BND(k2, [0.25, 1.52051]) *)
Lemma t5 : p21 -> p2 -> p17.
Proof.
 intros h0 h1.
 refine (mul_po _k2 _dT i17 i2 i13 h0 h1 _) ; finalize.
Qed.
Lemma l16 : s1 -> p17 (* BND(k2 * dT, [-9.0048e-33, 9.0048e-33]) *).
Proof.
 intros h0.
 assert (h1 := l17 h0).
 assert (h2 := l21 h0).
 apply t5. refine (subset _k2 i14 i17 h1 _) ; finalize. exact h2.
Qed.
Definition f30 := Float2 (-1599) (-76).
Definition f31 := Float2 (1599) (-76).
Definition i18 := makepairF f30 f31.
Notation p22 := (BND r30 i18). (* BND(k3 * dP, [-2.11626e-20, 2.11626e-20]) *)
Lemma l23 : s1 -> p4 (* BND(dP, [-4.06576e-20, 4.06576e-20]) *).
Proof.
 intros h0.
 assert (h1 := l11 h0).
 exact (proj2 h1).
Qed.
Lemma t6 : p1 -> p4 -> p22.
Proof.
 intros h0 h1.
 refine (mul_oo _k3 _dP i1 i4 i18 h0 h1 _) ; finalize.
Qed.
Lemma l22 : s1 -> p22 (* BND(k3 * dP, [-2.11626e-20, 2.11626e-20]) *).
Proof.
 intros h0.
 assert (h1 := l19 h0).
 assert (h2 := l23 h0).
 apply t6. exact h1. exact h2.
Qed.
Lemma t7 : p17 -> p22 -> p16.
Proof.
 intros h0 h1.
 refine (add r29 r30 i13 i18 i12 h0 h1 _) ; finalize.
Qed.
Lemma l15 : s1 -> p16 (* BND(k2 * dT + k3 * dP, [-2.11626e-20, 2.11626e-20]) *).
Proof.
 intros h0.
 assert (h1 := l16 h0).
 assert (h2 := l22 h0).
 apply t7. exact h1. exact h2.
Qed.
Definition f32 := Float2 (1) (-1).
Definition f33 := Float2 (2596148429267413814265248164610145) (-111).
Definition i19 := makepairF f32 f33.
Notation p23 := (BND r19 i19). (* BND(1 + e1, [0.5, 1]) *)
Lemma l25 : s1 -> p5 (* BND(e1, [-3.7363e-32, 3.7363e-32]) *).
Proof.
 intros h0.
 assert (h1 := l12 h0).
 exact (proj2 h1).
Qed.
Definition f34 := Float2 (-1) (-1).
Definition i20 := makepairF f34 f10.
Notation p24 := (BND _e1 i20). (* BND(e1, [-0.5, 3.7363e-32]) *)
Lemma t8 : p19 -> p24 -> p23.
Proof.
 intros h0 h1.
 refine (add r7 _e1 i15 i20 i19 h0 h1 _) ; finalize.
Qed.
Lemma l24 : s1 -> p23 (* BND(1 + e1, [0.5, 1]) *).
Proof.
 intros h0.
 assert (h1 := l18 h0).
 assert (h2 := l25 h0).
 apply t8. exact h1. refine (subset _e1 i5 i20 h2 _) ; finalize.
Qed.
Lemma t9 : p16 -> p23 -> p15.
Proof.
 intros h0 h1.
 refine (mul_op r28 r19 i12 i19 i9 h0 h1 _) ; finalize.
Qed.
Lemma l14 : s1 -> p15 (* BND((k2 * dT + k3 * dP) * (1 + e1), [-2.11626e-20, 2.11626e-20]) *).
Proof.
 intros h0.
 assert (h1 := l15 h0).
 assert (h2 := l24 h0).
 apply t9. exact h1. exact h2.
Qed.
Lemma t10 : p12 -> p15 -> p11.
Proof.
 intros h0 h1.
 refine (add r26 r27 i10 i9 i9 h0 h1 _) ; finalize.
Qed.
Lemma l6 : s1 -> p11 (* BND(k1 * lam + (k2 * dT + k3 * dP) * (1 + e1), [-2.11626e-20, 2.11626e-20]) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 assert (h2 := l14 h0).
 apply t10. exact h1. exact h2.
Qed.
Definition f35 := Float2 (-101365) (-120).
Definition f36 := Float2 (101365) (-120).
Definition i21 := makepairF f35 f36.
Notation p25 := (BND r31 i21). (* BND((k2 + k3) * e1, [-7.62586e-32, 7.62586e-32]) *)
Definition f37 := Float2 (1045) (-9).
Definition i22 := makepairF f20 f37.
Notation p26 := (BND r32 i22). (* BND(k2 + k3, [-1, 2.04102]) *)
Definition i23 := makepairF f20 f2.
Notation p27 := (BND _k3 i23). (* BND(k3, [-1, 0.520508]) *)
Lemma t11 : p21 -> p27 -> p26.
Proof.
 intros h0 h1.
 refine (add _k2 _k3 i17 i23 i22 h0 h1 _) ; finalize.
Qed.
Lemma l27 : s1 -> p26 (* BND(k2 + k3, [-1, 2.04102]) *).
Proof.
 intros h0.
 assert (h1 := l17 h0).
 assert (h2 := l19 h0).
 apply t11. refine (subset _k2 i14 i17 h1 _) ; finalize. refine (subset _k3 i1 i23 h2 _) ; finalize.
Qed.
Lemma t12 : p26 -> p5 -> p25.
Proof.
 intros h0 h1.
 refine (mul_oo r32 _e1 i22 i5 i21 h0 h1 _) ; finalize.
Qed.
Lemma l26 : s1 -> p25 (* BND((k2 + k3) * e1, [-7.62586e-32, 7.62586e-32]) *).
Proof.
 intros h0.
 assert (h1 := l27 h0).
 assert (h2 := l25 h0).
 apply t12. exact h1. exact h2.
Qed.
Lemma t13 : p11 -> p25 -> p10.
Proof.
 intros h0 h1.
 refine (add r25 r31 i9 i21 i8 h0 h1 _) ; finalize.
Qed.
Lemma l5 : s1 -> p10 (* BND(k1 * lam + (k2 * dT + k3 * dP) * (1 + e1) + (k2 + k3) * e1, [-2.11626e-20, 2.11626e-20]) *).
Proof.
 intros h0.
 assert (h1 := l6 h0).
 assert (h2 := l26 h0).
 apply t13. exact h1. exact h2.
Qed.
Definition f38 := Float2 (-10931179975662898411259029581410903620243974609796130210671988951214405975) (-346).
Definition f39 := Float2 (10931179975662898411259029581410903620243974609796130210671988951214405975) (-346).
Definition i24 := makepairF f38 f39.
Notation p28 := (BND r33 i24). (* BND((k1 * (1 + lam) + (k2 * (1 + dT) + k3 * (1 + dP)) * (1 + e1)) * e2, [-7.62586e-32, 7.62586e-32]) *)
Definition f40 := Float2 (112692577068689674342876593622792820827257470204083816604865865476437175) (-235).
Definition i25 := makepairF f20 f40.
Notation p29 := (BND r3 i25). (* BND(k1 * (1 + lam) + (k2 * (1 + dT) + k3 * (1 + dP)) * (1 + e1), [-1, 2.04102]) *)
Notation p30 := (BND r4 i10). (* BND(k1 * (1 + lam), [0, 0]) *)
Definition f41 := Float2 (1) (1).
Definition i26 := makepairF f32 f41.
Notation p31 := (BND r6 i26). (* BND(1 + lam, [0.5, 2]) *)
Definition i27 := makepairF f34 f21.
Notation p32 := (BND _lam i27). (* BND(lam, [-0.5, 1]) *)
Lemma t14 : p19 -> p32 -> p31.
Proof.
 intros h0 h1.
 refine (add r7 _lam i15 i27 i26 h0 h1 _) ; finalize.
Qed.
Lemma l31 : s1 -> p31 (* BND(1 + lam, [0.5, 2]) *).
Proof.
 intros h0.
 assert (h1 := l18 h0).
 assert (h2 := l9 h0).
 apply t14. exact h1. refine (subset _lam i3 i27 h2 _) ; finalize.
Qed.
Lemma t15 : p13 -> p31 -> p30.
Proof.
 intros h0 h1.
 refine (mul_pp _k1 r6 i10 i26 i10 h0 h1 _) ; finalize.
Qed.
Lemma l30 : s1 -> p30 (* BND(k1 * (1 + lam), [0, 0]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 assert (h2 := l31 h0).
 apply t15. exact h1. exact h2.
Qed.
Notation p33 := (BND r9 i25). (* BND((k2 * (1 + dT) + k3 * (1 + dP)) * (1 + e1), [-1, 2.04102]) *)
Definition f42 := Float2 (43407601737351158974965027800040533015) (-124).
Definition i28 := makepairF f34 f42.
Notation p34 := (BND r10 i28). (* BND(k2 * (1 + dT) + k3 * (1 + dP), [-0.5, 2.04102]) *)
Definition f43 := Float2 (32337624834954906470487931138382949399) (-124).
Definition i29 := makepairF f29 f43.
Notation p35 := (BND r11 i29). (* BND(k2 * (1 + dT), [0.25, 1.52051]) *)
Definition f44 := Float2 (3) (-2).
Definition f45 := Float2 (20769187434139310514121985316880507) (-114).
Definition i30 := makepairF f44 f45.
Notation p36 := (BND r14 i30). (* BND(1 + dT, [0.75, 1]) *)
Definition f46 := Float2 (-1) (-2).
Definition i31 := makepairF f46 f4.
Notation p37 := (BND _dT i31). (* BND(dT, [-0.25, 5.92223e-33]) *)
Lemma t16 : p19 -> p37 -> p36.
Proof.
 intros h0 h1.
 refine (add r7 _dT i15 i31 i30 h0 h1 _) ; finalize.
Qed.
Lemma l35 : s1 -> p36 (* BND(1 + dT, [0.75, 1]) *).
Proof.
 intros h0.
 assert (h1 := l18 h0).
 assert (h2 := l21 h0).
 apply t16. exact h1. refine (subset _dT i2 i31 h2 _) ; finalize.
Qed.
Lemma t17 : p18 -> p36 -> p35.
Proof.
 intros h0 h1.
 refine (mul_pp _k2 r14 i14 i30 i29 h0 h1 _) ; finalize.
Qed.
Lemma l34 : s1 -> p35 (* BND(k2 * (1 + dT), [0.25, 1.52051]) *).
Proof.
 intros h0.
 assert (h1 := l17 h0).
 assert (h2 := l35 h0).
 apply t17. exact h1. exact h2.
Qed.
Definition f47 := Float2 (-3) (-2).
Definition f48 := Float2 (39328458365148764046911) (-76).
Definition i32 := makepairF f47 f48.
Notation p38 := (BND r16 i32). (* BND(k3 * (1 + dP), [-0.75, 0.520508]) *)
Definition f49 := Float2 (73786976294838206467) (-66).
Definition i33 := makepairF f32 f49.
Notation p39 := (BND r17 i33). (* BND(1 + dP, [0.5, 1]) *)
Definition i34 := makepairF f34 f8.
Notation p40 := (BND _dP i34). (* BND(dP, [-0.5, 4.06576e-20]) *)
Lemma t18 : p19 -> p40 -> p39.
Proof.
 intros h0 h1.
 refine (add r7 _dP i15 i34 i33 h0 h1 _) ; finalize.
Qed.
Lemma l37 : s1 -> p39 (* BND(1 + dP, [0.5, 1]) *).
Proof.
 intros h0.
 assert (h1 := l18 h0).
 assert (h2 := l23 h0).
 apply t18. exact h1. refine (subset _dP i4 i34 h2 _) ; finalize.
Qed.
Definition f50 := Float2 (-5) (-3).
Definition i35 := makepairF f50 f2.
Notation p41 := (BND _k3 i35). (* BND(k3, [-0.625, 0.520508]) *)
Lemma t19 : p41 -> p39 -> p38.
Proof.
 intros h0 h1.
 refine (mul_op _k3 r17 i35 i33 i32 h0 h1 _) ; finalize.
Qed.
Lemma l36 : s1 -> p38 (* BND(k3 * (1 + dP), [-0.75, 0.520508]) *).
Proof.
 intros h0.
 assert (h1 := l19 h0).
 assert (h2 := l37 h0).
 apply t19. refine (subset _k3 i1 i35 h1 _) ; finalize. exact h2.
Qed.
Lemma t20 : p35 -> p38 -> p34.
Proof.
 intros h0 h1.
 refine (add r11 r16 i29 i32 i28 h0 h1 _) ; finalize.
Qed.
Lemma l33 : s1 -> p34 (* BND(k2 * (1 + dT) + k3 * (1 + dP), [-0.5, 2.04102]) *).
Proof.
 intros h0.
 assert (h1 := l34 h0).
 assert (h2 := l36 h0).
 apply t20. exact h1. exact h2.
Qed.
Lemma t21 : p34 -> p23 -> p33.
Proof.
 intros h0 h1.
 refine (mul_op r10 r19 i28 i19 i25 h0 h1 _) ; finalize.
Qed.
Lemma l32 : s1 -> p33 (* BND((k2 * (1 + dT) + k3 * (1 + dP)) * (1 + e1), [-1, 2.04102]) *).
Proof.
 intros h0.
 assert (h1 := l33 h0).
 assert (h2 := l24 h0).
 apply t21. exact h1. exact h2.
Qed.
Lemma t22 : p30 -> p33 -> p29.
Proof.
 intros h0 h1.
 refine (add r4 r9 i10 i25 i25 h0 h1 _) ; finalize.
Qed.
Lemma l29 : s1 -> p29 (* BND(k1 * (1 + lam) + (k2 * (1 + dT) + k3 * (1 + dP)) * (1 + e1), [-1, 2.04102]) *).
Proof.
 intros h0.
 assert (h1 := l30 h0).
 assert (h2 := l32 h0).
 apply t22. exact h1. exact h2.
Qed.
Lemma l38 : s1 -> p6 (* BND(e2, [-3.7363e-32, 3.7363e-32]) *).
Proof.
 intros h0.
 assert (h1 := l13 h0).
 exact (proj2 h1).
Qed.
Lemma t23 : p29 -> p6 -> p28.
Proof.
 intros h0 h1.
 refine (mul_oo r3 _e2 i25 i5 i24 h0 h1 _) ; finalize.
Qed.
Lemma l28 : s1 -> p28 (* BND((k1 * (1 + lam) + (k2 * (1 + dT) + k3 * (1 + dP)) * (1 + e1)) * e2, [-7.62586e-32, 7.62586e-32]) *).
Proof.
 intros h0.
 assert (h1 := l29 h0).
 assert (h2 := l38 h0).
 apply t23. exact h1. exact h2.
Qed.
Lemma t24 : p10 -> p28 -> p9.
Proof.
 intros h0 h1.
 refine (add r24 r33 i8 i24 i7 h0 h1 _) ; finalize.
Qed.
Lemma l4 : s1 -> p9 (* BND(k1 * lam + (k2 * dT + k3 * dP) * (1 + e1) + (k2 + k3) * e1 + (k1 * (1 + lam) + (k2 * (1 + dT) + k3 * (1 + dP)) * (1 + e1)) * e2, [-2.11626e-20, 2.11626e-20]) *).
Proof.
 intros h0.
 assert (h1 := l5 h0).
 assert (h2 := l28 h0).
 apply t24. exact h1. exact h2.
Qed.
Notation p42 := (REL r1 r23 i10). (* REL(Y - 1, k1 * lam + (k2 * dT + k3 * dP) * (1 + e1) + (k2 + k3) * e1 + (k1 * (1 + lam) + (k2 * (1 + dT) + k3 * (1 + dP)) * (1 + e1)) * e2, [0, 0]) *)
Notation p43 := (r1 = r23). (* EQL(Y - 1, k1 * lam + (k2 * dT + k3 * dP) * (1 + e1) + (k2 + k3) * e1 + (k1 * (1 + lam) + (k2 * (1 + dT) + k3 * (1 + dP)) * (1 + e1)) * e2) *)
Lemma t25 : p43.
Proof.
 refine (b1) ; finalize.
Qed.
Lemma l40 : s1 -> p43 (* EQL(Y - 1, k1 * lam + (k2 * dT + k3 * dP) * (1 + e1) + (k2 + k3) * e1 + (k1 * (1 + lam) + (k2 * (1 + dT) + k3 * (1 + dP)) * (1 + e1)) * e2) *).
Proof.
 intros h0.
 apply t25.
Qed.
Notation p44 := (REL r23 r23 i10). (* REL(k1 * lam + (k2 * dT + k3 * dP) * (1 + e1) + (k2 + k3) * e1 + (k1 * (1 + lam) + (k2 * (1 + dT) + k3 * (1 + dP)) * (1 + e1)) * e2, k1 * lam + (k2 * dT + k3 * dP) * (1 + e1) + (k2 + k3) * e1 + (k1 * (1 + lam) + (k2 * (1 + dT) + k3 * (1 + dP)) * (1 + e1)) * e2, [0, 0]) *)
Lemma t26 : p44.
Proof.
 refine (rel_refl r23 i10 _) ; finalize.
Qed.
Lemma l41 : s1 -> p44 (* REL(k1 * lam + (k2 * dT + k3 * dP) * (1 + e1) + (k2 + k3) * e1 + (k1 * (1 + lam) + (k2 * (1 + dT) + k3 * (1 + dP)) * (1 + e1)) * e2, k1 * lam + (k2 * dT + k3 * dP) * (1 + e1) + (k2 + k3) * e1 + (k1 * (1 + lam) + (k2 * (1 + dT) + k3 * (1 + dP)) * (1 + e1)) * e2, [0, 0]) *).
Proof.
 intros h0.
 apply t26.
Qed.
Lemma t27 : p43 -> p44 -> p42.
Proof.
 intros h0 h1.
 refine (rel_rewrite_1 r1 r23 r23 i10 h0 h1) ; finalize.
Qed.
Lemma l39 : s1 -> p42 (* REL(Y - 1, k1 * lam + (k2 * dT + k3 * dP) * (1 + e1) + (k2 + k3) * e1 + (k1 * (1 + lam) + (k2 * (1 + dT) + k3 * (1 + dP)) * (1 + e1)) * e2, [0, 0]) *).
Proof.
 intros h0.
 assert (h1 := l40 h0).
 assert (h2 := l41 h0).
 apply t27. exact h1. exact h2.
Qed.
Lemma t28 : p9 -> p42 -> p8.
Proof.
 intros h0 h1.
 refine (bnd_of_bnd_rel_o r1 r23 i7 i10 i7 h0 h1 _) ; finalize.
Qed.
Lemma l3 : s1 -> p8 (* BND(Y - 1, [-2.11626e-20, 2.11626e-20]) *).
Proof.
 intros h0.
 assert (h1 := l4 h0).
 assert (h2 := l39 h0).
 apply t28. exact h1. exact h2.
Qed.
Lemma l1 : s1 -> False.
Proof.
 intros h0.
 assert (h1 := l2 h0).
 assert (h2 := l3 h0).
 refine (simplify (Tatom false (Abnd 0%nat i6)) Tfalse (Abnd 0%nat i7) (List.cons r1 List.nil) h2 h1 _) ; finalize.
Qed.
End Generated_by_Gappa.
