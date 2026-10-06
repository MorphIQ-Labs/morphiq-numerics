Require Import Gappa.Gappa_library.
Section Generated_by_Gappa.
Notation r7 := (Float1 (1)).
Variable _k2 : R.
Notation r6 := ((r7 - _k2)%R).
Variable _k3 : R.
Notation _k1 := ((r6 - _k3)%R).
Variable _lam : R.
Notation r10 := ((r7 + _lam)%R).
Notation r4 := ((_k1 * r10)%R).
Variable _dT : R.
Notation r15 := ((r7 + _dT)%R).
Notation r14 := ((_k2 * r15)%R).
Variable _dP : R.
Notation r18 := ((r7 + _dP)%R).
Notation r17 := ((_k3 * r18)%R).
Notation r13 := ((r14 + r17)%R).
Variable _e1 : R.
Notation r20 := ((r7 + _e1)%R).
Notation r12 := ((r13 * r20)%R).
Notation r3 := ((r4 + r12)%R).
Variable _e2 : R.
Notation r22 := ((r7 + _e2)%R).
Notation _Y := ((r3 * r22)%R).
Notation r1 := ((_Y - r7)%R).
Notation r27 := ((_k1 * _lam)%R).
Notation r30 := ((_k2 * _dT)%R).
Notation r31 := ((_k3 * _dP)%R).
Notation r29 := ((r30 + r31)%R).
Notation r28 := ((r29 * r20)%R).
Notation r26 := ((r27 + r28)%R).
Notation r33 := ((_k2 + _k3)%R).
Notation r32 := ((r33 * _e1)%R).
Notation r25 := ((r26 + r32)%R).
Notation r34 := ((r3 * _e2)%R).
Notation r24 := ((r25 + r34)%R).
Hypothesis a1 : r1 = r24.
Lemma b1 : r1 = r24.
 apply a1.
Qed.
Definition f1 := Float2 (-47) (-12).
Definition f2 := Float2 (47) (-12).
Definition i1 := makepairF f1 f2.
Notation p1 := (BND _k3 i1). (* BND(k3, [-0.0114746, 0.0114746]) *)
Definition f3 := Float2 (-257) (-8).
Definition f4 := Float2 (257) (-8).
Definition i2 := makepairF f3 f4.
Notation p2 := (BND _k2 i2). (* BND(k2, [-1.00391, 1.00391]) *)
Definition s7 := (p1 /\ p2).
Definition f5 := Float2 (-123) (-114).
Definition f6 := Float2 (123) (-114).
Definition i3 := makepairF f5 f6.
Notation p3 := (BND _dT i3). (* BND(dT, [-5.92223e-33, 5.92223e-33]) *)
Definition s6 := (s7 /\ p3).
Definition f7 := Float2 (-745) (-106).
Definition f8 := Float2 (745) (-106).
Definition i4 := makepairF f7 f8.
Notation p4 := (BND _lam i4). (* BND(lam, [-9.18283e-30, 9.18283e-30]) *)
Definition s5 := (s6 /\ p4).
Definition f9 := Float2 (-3) (-66).
Definition f10 := Float2 (3) (-66).
Definition i5 := makepairF f9 f10.
Notation p5 := (BND _dP i5). (* BND(dP, [-4.06576e-20, 4.06576e-20]) *)
Definition s4 := (s5 /\ p5).
Definition f11 := Float2 (-97) (-111).
Definition f12 := Float2 (97) (-111).
Definition i6 := makepairF f11 f12.
Notation p6 := (BND _e1 i6). (* BND(e1, [-3.7363e-32, 3.7363e-32]) *)
Definition s3 := (s4 /\ p6).
Notation p7 := (BND _e2 i6). (* BND(e2, [-3.7363e-32, 3.7363e-32]) *)
Definition s2 := (s3 /\ p7).
Definition f13 := Float2 (-1) (-64).
Definition f14 := Float2 (1) (-64).
Definition i7 := makepairF f13 f14.
Notation p8 := (BND r1 i7). (* BND(Y - 1, [-5.42101e-20, 5.42101e-20]) *)
Definition s8 := (not p8).
Definition s1 := (s2 /\ s8).
Lemma l2 : s1 -> s8.
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj2 h1).
Qed.
Definition f15 := Float2 (-16718525681283248548690308286930877737608660829417654923928081940186177213264716731) (-344).
Definition f16 := Float2 (16718525681283248548690308286930877737608660829417654923928081940186177213264716731) (-344).
Definition i8 := makepairF f15 f16.
Notation p9 := (BND r1 i8). (* BND(Y - 1, [-4.6653e-22, 4.6653e-22]) *)
Notation p10 := (BND r24 i8). (* BND(k1 * lam + (k2 * dT + k3 * dP) * (1 + e1) + (k2 + k3) * e1 + (k1 * (1 + lam) + (k2 * (1 + dT) + k3 * (1 + dP)) * (1 + e1)) * e2, [-4.6653e-22, 4.6653e-22]) *)
Definition f17 := Float2 (-6439741845554997805764544812009979326937592416667) (-233).
Definition f18 := Float2 (6439741845554997805764544812009979326937592416667) (-233).
Definition i9 := makepairF f17 f18.
Notation p11 := (BND r25 i9). (* BND(k1 * lam + (k2 * dT + k3 * dP) * (1 + e1) + (k2 + k3) * e1, [-4.6653e-22, 4.6653e-22]) *)
Definition f19 := Float2 (-6439741845031324811874370870413814721781852719515) (-233).
Definition f20 := Float2 (6439741845031324811874370870413814721781852719515) (-233).
Definition i10 := makepairF f19 f20.
Notation p12 := (BND r26 i10). (* BND(k1 * lam + (k2 * dT + k3 * dP) * (1 + e1), [-4.6653e-22, 4.6653e-22]) *)
Definition f21 := Float2 (-6149975) (-118).
Definition f22 := Float2 (6149975) (-118).
Definition i11 := makepairF f21 f22.
Notation p13 := (BND r27 i11). (* BND(k1 * lam, [-1.85069e-29, 1.85069e-29]) *)
Definition f23 := Float2 (-1) (-2).
Definition f24 := Float2 (8255) (-12).
Definition i12 := makepairF f23 f24.
Notation p14 := (BND _k1 i12). (* BND(k1, [-0.25, 2.01538]) *)
Definition f25 := Float2 (-1) (-3).
Definition f26 := Float2 (513) (-8).
Definition i13 := makepairF f25 f26.
Notation p15 := (BND r6 i13). (* BND(1 - k2, [-0.125, 2.00391]) *)
Definition f27 := Float2 (1) (0).
Definition i14 := makepairF f27 f27.
Notation p16 := (BND r7 i14). (* BND(1, [1, 1]) *)
Lemma t1 : p16.
Proof.
 refine (constant1 _ i14 _) ; finalize.
Qed.
Lemma l10 : s1 -> p16 (* BND(1, [1, 1]) *).
Proof.
 intros h0.
 apply t1.
Qed.
Lemma l17 : s1 -> s2.
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj1 h1).
Qed.
Lemma l16 : s1 -> s3.
Proof.
 intros h0.
 assert (h1 := l17 h0).
 exact (proj1 h1).
Qed.
Lemma l15 : s1 -> s4.
Proof.
 intros h0.
 assert (h1 := l16 h0).
 exact (proj1 h1).
Qed.
Lemma l14 : s1 -> s5.
Proof.
 intros h0.
 assert (h1 := l15 h0).
 exact (proj1 h1).
Qed.
Lemma l13 : s1 -> s6.
Proof.
 intros h0.
 assert (h1 := l14 h0).
 exact (proj1 h1).
Qed.
Lemma l12 : s1 -> s7.
Proof.
 intros h0.
 assert (h1 := l13 h0).
 exact (proj1 h1).
Qed.
Lemma l11 : s1 -> p2 (* BND(k2, [-1.00391, 1.00391]) *).
Proof.
 intros h0.
 assert (h1 := l12 h0).
 exact (proj2 h1).
Qed.
Definition f28 := Float2 (9) (-3).
Definition i15 := makepairF f3 f28.
Notation p17 := (BND _k2 i15). (* BND(k2, [-1.00391, 1.125]) *)
Lemma t2 : p16 -> p17 -> p15.
Proof.
 intros h0 h1.
 refine (sub r7 _k2 i14 i15 i13 h0 h1 _) ; finalize.
Qed.
Lemma l9 : s1 -> p15 (* BND(1 - k2, [-0.125, 2.00391]) *).
Proof.
 intros h0.
 assert (h1 := l10 h0).
 assert (h2 := l11 h0).
 apply t2. exact h1. refine (subset _k2 i2 i15 h2 _) ; finalize.
Qed.
Lemma l18 : s1 -> p1 (* BND(k3, [-0.0114746, 0.0114746]) *).
Proof.
 intros h0.
 assert (h1 := l12 h0).
 exact (proj1 h1).
Qed.
Definition f29 := Float2 (1) (-3).
Definition i16 := makepairF f1 f29.
Notation p18 := (BND _k3 i16). (* BND(k3, [-0.0114746, 0.125]) *)
Lemma t3 : p15 -> p18 -> p14.
Proof.
 intros h0 h1.
 refine (sub r6 _k3 i13 i16 i12 h0 h1 _) ; finalize.
Qed.
Lemma l8 : s1 -> p14 (* BND(k1, [-0.25, 2.01538]) *).
Proof.
 intros h0.
 assert (h1 := l9 h0).
 assert (h2 := l18 h0).
 apply t3. exact h1. refine (subset _k3 i1 i16 h2 _) ; finalize.
Qed.
Lemma l19 : s1 -> p4 (* BND(lam, [-9.18283e-30, 9.18283e-30]) *).
Proof.
 intros h0.
 assert (h1 := l14 h0).
 exact (proj2 h1).
Qed.
Definition f30 := Float2 (-1) (0).
Definition i17 := makepairF f30 f24.
Notation p19 := (BND _k1 i17). (* BND(k1, [-1, 2.01538]) *)
Lemma t4 : p19 -> p4 -> p13.
Proof.
 intros h0 h1.
 refine (mul_oo _k1 _lam i17 i4 i11 h0 h1 _) ; finalize.
Qed.
Lemma l7 : s1 -> p13 (* BND(k1 * lam, [-1.85069e-29, 1.85069e-29]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 assert (h2 := l19 h0).
 apply t4. refine (subset _k1 i12 i17 h1 _) ; finalize. exact h2.
Qed.
Definition f31 := Float2 (-6439741589571357831332558512239101423418973538715) (-233).
Definition f32 := Float2 (6439741589571357831332558512239101423418973538715) (-233).
Definition i18 := makepairF f31 f32.
Notation p20 := (BND r28 i18). (* BND((k2 * dT + k3 * dP) * (1 + e1), [-4.6653e-22, 4.6653e-22]) *)
Definition f33 := Float2 (-2480498232294267) (-122).
Definition f34 := Float2 (2480498232294267) (-122).
Definition i19 := makepairF f33 f34.
Notation p21 := (BND r29 i19). (* BND(k2 * dT + k3 * dP, [-4.6653e-22, 4.6653e-22]) *)
Definition f35 := Float2 (-31611) (-122).
Definition f36 := Float2 (31611) (-122).
Definition i20 := makepairF f35 f36.
Notation p22 := (BND r30 i20). (* BND(k2 * dT, [-5.94537e-33, 5.94537e-33]) *)
Lemma l23 : s1 -> p3 (* BND(dT, [-5.92223e-33, 5.92223e-33]) *).
Proof.
 intros h0.
 assert (h1 := l13 h0).
 exact (proj2 h1).
Qed.
Lemma t5 : p2 -> p3 -> p22.
Proof.
 intros h0 h1.
 refine (mul_oo _k2 _dT i2 i3 i20 h0 h1 _) ; finalize.
Qed.
Lemma l22 : s1 -> p22 (* BND(k2 * dT, [-5.94537e-33, 5.94537e-33]) *).
Proof.
 intros h0.
 assert (h1 := l11 h0).
 assert (h2 := l23 h0).
 apply t5. exact h1. exact h2.
Qed.
Definition f37 := Float2 (-141) (-78).
Definition f38 := Float2 (141) (-78).
Definition i21 := makepairF f37 f38.
Notation p23 := (BND r31 i21). (* BND(k3 * dP, [-4.6653e-22, 4.6653e-22]) *)
Lemma l25 : s1 -> p5 (* BND(dP, [-4.06576e-20, 4.06576e-20]) *).
Proof.
 intros h0.
 assert (h1 := l15 h0).
 exact (proj2 h1).
Qed.
Lemma t6 : p1 -> p5 -> p23.
Proof.
 intros h0 h1.
 refine (mul_oo _k3 _dP i1 i5 i21 h0 h1 _) ; finalize.
Qed.
Lemma l24 : s1 -> p23 (* BND(k3 * dP, [-4.6653e-22, 4.6653e-22]) *).
Proof.
 intros h0.
 assert (h1 := l18 h0).
 assert (h2 := l25 h0).
 apply t6. exact h1. exact h2.
Qed.
Lemma t7 : p22 -> p23 -> p21.
Proof.
 intros h0 h1.
 refine (add r30 r31 i20 i21 i19 h0 h1 _) ; finalize.
Qed.
Lemma l21 : s1 -> p21 (* BND(k2 * dT + k3 * dP, [-4.6653e-22, 4.6653e-22]) *).
Proof.
 intros h0.
 assert (h1 := l22 h0).
 assert (h2 := l24 h0).
 apply t7. exact h1. exact h2.
Qed.
Definition f39 := Float2 (1) (-1).
Definition f40 := Float2 (2596148429267413814265248164610145) (-111).
Definition i22 := makepairF f39 f40.
Notation p24 := (BND r20 i22). (* BND(1 + e1, [0.5, 1]) *)
Lemma l27 : s1 -> p6 (* BND(e1, [-3.7363e-32, 3.7363e-32]) *).
Proof.
 intros h0.
 assert (h1 := l16 h0).
 exact (proj2 h1).
Qed.
Definition f41 := Float2 (-1) (-1).
Definition i23 := makepairF f41 f12.
Notation p25 := (BND _e1 i23). (* BND(e1, [-0.5, 3.7363e-32]) *)
Lemma t8 : p16 -> p25 -> p24.
Proof.
 intros h0 h1.
 refine (add r7 _e1 i14 i23 i22 h0 h1 _) ; finalize.
Qed.
Lemma l26 : s1 -> p24 (* BND(1 + e1, [0.5, 1]) *).
Proof.
 intros h0.
 assert (h1 := l10 h0).
 assert (h2 := l27 h0).
 apply t8. exact h1. refine (subset _e1 i6 i23 h2 _) ; finalize.
Qed.
Lemma t9 : p21 -> p24 -> p20.
Proof.
 intros h0 h1.
 refine (mul_op r29 r20 i19 i22 i18 h0 h1 _) ; finalize.
Qed.
Lemma l20 : s1 -> p20 (* BND((k2 * dT + k3 * dP) * (1 + e1), [-4.6653e-22, 4.6653e-22]) *).
Proof.
 intros h0.
 assert (h1 := l21 h0).
 assert (h2 := l26 h0).
 apply t9. exact h1. exact h2.
Qed.
Lemma t10 : p13 -> p20 -> p12.
Proof.
 intros h0 h1.
 refine (add r27 r28 i11 i18 i10 h0 h1 _) ; finalize.
Qed.
Lemma l6 : s1 -> p12 (* BND(k1 * lam + (k2 * dT + k3 * dP) * (1 + e1), [-4.6653e-22, 4.6653e-22]) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 assert (h2 := l20 h0).
 apply t10. exact h1. exact h2.
Qed.
Definition f42 := Float2 (-403423) (-123).
Definition f43 := Float2 (403423) (-123).
Definition i24 := makepairF f42 f43.
Notation p26 := (BND r32 i24). (* BND((k2 + k3) * e1, [-3.79377e-32, 3.79377e-32]) *)
Definition f44 := Float2 (-4159) (-12).
Definition f45 := Float2 (4159) (-12).
Definition i25 := makepairF f44 f45.
Notation p27 := (BND r33 i25). (* BND(k2 + k3, [-1.01538, 1.01538]) *)
Lemma t11 : p2 -> p1 -> p27.
Proof.
 intros h0 h1.
 refine (add _k2 _k3 i2 i1 i25 h0 h1 _) ; finalize.
Qed.
Lemma l29 : s1 -> p27 (* BND(k2 + k3, [-1.01538, 1.01538]) *).
Proof.
 intros h0.
 assert (h1 := l11 h0).
 assert (h2 := l18 h0).
 apply t11. exact h1. exact h2.
Qed.
Lemma t12 : p27 -> p6 -> p26.
Proof.
 intros h0 h1.
 refine (mul_oo r33 _e1 i25 i6 i24 h0 h1 _) ; finalize.
Qed.
Lemma l28 : s1 -> p26 (* BND((k2 + k3) * e1, [-3.79377e-32, 3.79377e-32]) *).
Proof.
 intros h0.
 assert (h1 := l29 h0).
 assert (h2 := l27 h0).
 apply t12. exact h1. exact h2.
Qed.
Lemma t13 : p12 -> p26 -> p11.
Proof.
 intros h0 h1.
 refine (add r26 r32 i10 i24 i9 h0 h1 _) ; finalize.
Qed.
Lemma l5 : s1 -> p11 (* BND(k1 * lam + (k2 * dT + k3 * dP) * (1 + e1) + (k2 + k3) * e1, [-4.6653e-22, 4.6653e-22]) *).
Proof.
 intros h0.
 assert (h1 := l6 h0).
 assert (h2 := l28 h0).
 apply t13. exact h1. exact h2.
Qed.
Definition f46 := Float2 (-4058004432352847514233955099103441888875353730041466302707308085273846715) (-344).
Definition f47 := Float2 (4058004432352847514233955099103441888875353730041466302707308085273846715) (-344).
Definition i26 := makepairF f46 f47.
Notation p28 := (BND r34 i26). (* BND((k1 * (1 + lam) + (k2 * (1 + dT) + k3 * (1 + dP)) * (1 + e1)) * e2, [-1.13238e-31, 1.13238e-31]) *)
Definition f48 := Float2 (-1) (1).
Definition f49 := Float2 (41835097240751005301380980403128266895622203402489343326879464796637595) (-233).
Definition i27 := makepairF f48 f49.
Notation p29 := (BND r3 i27). (* BND(k1 * (1 + lam) + (k2 * (1 + dT) + k3 * (1 + dP)) * (1 + e1), [-2, 3.03076]) *)
Definition f50 := Float2 (669725165112578157398738237470398295) (-118).
Definition i28 := makepairF f41 f50.
Notation p30 := (BND r4 i28). (* BND(k1 * (1 + lam), [-0.5, 2.01538]) *)
Definition f51 := Float2 (81129638414606681695789005144809) (-106).
Definition i29 := makepairF f39 f51.
Notation p31 := (BND r10 i29). (* BND(1 + lam, [0.5, 1]) *)
Definition i30 := makepairF f41 f8.
Notation p32 := (BND _lam i30). (* BND(lam, [-0.5, 9.18283e-30]) *)
Lemma t14 : p16 -> p32 -> p31.
Proof.
 intros h0 h1.
 refine (add r7 _lam i14 i30 i29 h0 h1 _) ; finalize.
Qed.
Lemma l33 : s1 -> p31 (* BND(1 + lam, [0.5, 1]) *).
Proof.
 intros h0.
 assert (h1 := l10 h0).
 assert (h2 := l19 h0).
 apply t14. exact h1. refine (subset _lam i4 i30 h2 _) ; finalize.
Qed.
Lemma t15 : p14 -> p31 -> p30.
Proof.
 intros h0 h1.
 refine (mul_op _k1 r10 i12 i29 i28 h0 h1 _) ; finalize.
Qed.
Lemma l32 : s1 -> p30 (* BND(k1 * (1 + lam), [-0.5, 2.01538]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 assert (h2 := l33 h0).
 apply t15. exact h1. exact h2.
Qed.
Definition f52 := Float2 (-3) (-1).
Definition f53 := Float2 (14015802273584938863258954209954425527282333189122115384642314091547035) (-233).
Definition i31 := makepairF f52 f53.
Notation p33 := (BND r12 i31). (* BND((k2 * (1 + dT) + k3 * (1 + dP)) * (1 + e1), [-1.5, 1.01538]) *)
Definition f54 := Float2 (-5) (-2).
Definition f55 := Float2 (5398690658661587026767064056538889083) (-122).
Definition i32 := makepairF f54 f55.
Notation p34 := (BND r13 i32). (* BND(k2 * (1 + dT) + k3 * (1 + dP), [-1.25, 1.01538]) *)
Definition f56 := Float2 (-9) (-3).
Definition f57 := Float2 (5337681170573802802129350226438290299) (-122).
Definition i33 := makepairF f56 f57.
Notation p35 := (BND r14 i33). (* BND(k2 * (1 + dT), [-1.125, 1.00391]) *)
Definition f58 := Float2 (20769187434139310514121985316880507) (-114).
Definition i34 := makepairF f39 f58.
Notation p36 := (BND r15 i34). (* BND(1 + dT, [0.5, 1]) *)
Definition i35 := makepairF f41 f6.
Notation p37 := (BND _dT i35). (* BND(dT, [-0.5, 5.92223e-33]) *)
Lemma t16 : p16 -> p37 -> p36.
Proof.
 intros h0 h1.
 refine (add r7 _dT i14 i35 i34 h0 h1 _) ; finalize.
Qed.
Lemma l37 : s1 -> p36 (* BND(1 + dT, [0.5, 1]) *).
Proof.
 intros h0.
 assert (h1 := l10 h0).
 assert (h2 := l23 h0).
 apply t16. exact h1. refine (subset _dT i3 i35 h2 _) ; finalize.
Qed.
Definition f59 := Float2 (-17) (-4).
Definition i36 := makepairF f59 f4.
Notation p38 := (BND _k2 i36). (* BND(k2, [-1.0625, 1.00391]) *)
Lemma t17 : p38 -> p36 -> p35.
Proof.
 intros h0 h1.
 refine (mul_op _k2 r15 i36 i34 i33 h0 h1 _) ; finalize.
Qed.
Lemma l36 : s1 -> p35 (* BND(k2 * (1 + dT), [-1.125, 1.00391]) *).
Proof.
 intros h0.
 assert (h1 := l11 h0).
 assert (h2 := l37 h0).
 apply t17. refine (subset _k2 i2 i36 h1 _) ; finalize. exact h2.
Qed.
Definition f60 := Float2 (3467987885857395703949) (-78).
Definition i37 := makepairF f25 f60.
Notation p39 := (BND r17 i37). (* BND(k3 * (1 + dP), [-0.125, 0.0114746]) *)
Definition f61 := Float2 (73786976294838206467) (-66).
Definition i38 := makepairF f39 f61.
Notation p40 := (BND r18 i38). (* BND(1 + dP, [0.5, 1]) *)
Definition i39 := makepairF f41 f10.
Notation p41 := (BND _dP i39). (* BND(dP, [-0.5, 4.06576e-20]) *)
Lemma t18 : p16 -> p41 -> p40.
Proof.
 intros h0 h1.
 refine (add r7 _dP i14 i39 i38 h0 h1 _) ; finalize.
Qed.
Lemma l39 : s1 -> p40 (* BND(1 + dP, [0.5, 1]) *).
Proof.
 intros h0.
 assert (h1 := l10 h0).
 assert (h2 := l25 h0).
 apply t18. exact h1. refine (subset _dP i5 i39 h2 _) ; finalize.
Qed.
Definition f62 := Float2 (-1) (-4).
Definition i40 := makepairF f62 f2.
Notation p42 := (BND _k3 i40). (* BND(k3, [-0.0625, 0.0114746]) *)
Lemma t19 : p42 -> p40 -> p39.
Proof.
 intros h0 h1.
 refine (mul_op _k3 r18 i40 i38 i37 h0 h1 _) ; finalize.
Qed.
Lemma l38 : s1 -> p39 (* BND(k3 * (1 + dP), [-0.125, 0.0114746]) *).
Proof.
 intros h0.
 assert (h1 := l18 h0).
 assert (h2 := l39 h0).
 apply t19. refine (subset _k3 i1 i40 h1 _) ; finalize. exact h2.
Qed.
Lemma t20 : p35 -> p39 -> p34.
Proof.
 intros h0 h1.
 refine (add r14 r17 i33 i37 i32 h0 h1 _) ; finalize.
Qed.
Lemma l35 : s1 -> p34 (* BND(k2 * (1 + dT) + k3 * (1 + dP), [-1.25, 1.01538]) *).
Proof.
 intros h0.
 assert (h1 := l36 h0).
 assert (h2 := l38 h0).
 apply t20. exact h1. exact h2.
Qed.
Lemma t21 : p34 -> p24 -> p33.
Proof.
 intros h0 h1.
 refine (mul_op r13 r20 i32 i22 i31 h0 h1 _) ; finalize.
Qed.
Lemma l34 : s1 -> p33 (* BND((k2 * (1 + dT) + k3 * (1 + dP)) * (1 + e1), [-1.5, 1.01538]) *).
Proof.
 intros h0.
 assert (h1 := l35 h0).
 assert (h2 := l26 h0).
 apply t21. exact h1. exact h2.
Qed.
Lemma t22 : p30 -> p33 -> p29.
Proof.
 intros h0 h1.
 refine (add r4 r12 i28 i31 i27 h0 h1 _) ; finalize.
Qed.
Lemma l31 : s1 -> p29 (* BND(k1 * (1 + lam) + (k2 * (1 + dT) + k3 * (1 + dP)) * (1 + e1), [-2, 3.03076]) *).
Proof.
 intros h0.
 assert (h1 := l32 h0).
 assert (h2 := l34 h0).
 apply t22. exact h1. exact h2.
Qed.
Lemma l40 : s1 -> p7 (* BND(e2, [-3.7363e-32, 3.7363e-32]) *).
Proof.
 intros h0.
 assert (h1 := l17 h0).
 exact (proj2 h1).
Qed.
Lemma t23 : p29 -> p7 -> p28.
Proof.
 intros h0 h1.
 refine (mul_oo r3 _e2 i27 i6 i26 h0 h1 _) ; finalize.
Qed.
Lemma l30 : s1 -> p28 (* BND((k1 * (1 + lam) + (k2 * (1 + dT) + k3 * (1 + dP)) * (1 + e1)) * e2, [-1.13238e-31, 1.13238e-31]) *).
Proof.
 intros h0.
 assert (h1 := l31 h0).
 assert (h2 := l40 h0).
 apply t23. exact h1. exact h2.
Qed.
Lemma t24 : p11 -> p28 -> p10.
Proof.
 intros h0 h1.
 refine (add r25 r34 i9 i26 i8 h0 h1 _) ; finalize.
Qed.
Lemma l4 : s1 -> p10 (* BND(k1 * lam + (k2 * dT + k3 * dP) * (1 + e1) + (k2 + k3) * e1 + (k1 * (1 + lam) + (k2 * (1 + dT) + k3 * (1 + dP)) * (1 + e1)) * e2, [-4.6653e-22, 4.6653e-22]) *).
Proof.
 intros h0.
 assert (h1 := l5 h0).
 assert (h2 := l30 h0).
 apply t24. exact h1. exact h2.
Qed.
Definition f63 := Float2 (0) (0).
Definition i41 := makepairF f63 f63.
Notation p43 := (REL r1 r24 i41). (* REL(Y - 1, k1 * lam + (k2 * dT + k3 * dP) * (1 + e1) + (k2 + k3) * e1 + (k1 * (1 + lam) + (k2 * (1 + dT) + k3 * (1 + dP)) * (1 + e1)) * e2, [0, 0]) *)
Notation p44 := (r1 = r24). (* EQL(Y - 1, k1 * lam + (k2 * dT + k3 * dP) * (1 + e1) + (k2 + k3) * e1 + (k1 * (1 + lam) + (k2 * (1 + dT) + k3 * (1 + dP)) * (1 + e1)) * e2) *)
Lemma t25 : p44.
Proof.
 refine (b1) ; finalize.
Qed.
Lemma l42 : s1 -> p44 (* EQL(Y - 1, k1 * lam + (k2 * dT + k3 * dP) * (1 + e1) + (k2 + k3) * e1 + (k1 * (1 + lam) + (k2 * (1 + dT) + k3 * (1 + dP)) * (1 + e1)) * e2) *).
Proof.
 intros h0.
 apply t25.
Qed.
Notation p45 := (REL r24 r24 i41). (* REL(k1 * lam + (k2 * dT + k3 * dP) * (1 + e1) + (k2 + k3) * e1 + (k1 * (1 + lam) + (k2 * (1 + dT) + k3 * (1 + dP)) * (1 + e1)) * e2, k1 * lam + (k2 * dT + k3 * dP) * (1 + e1) + (k2 + k3) * e1 + (k1 * (1 + lam) + (k2 * (1 + dT) + k3 * (1 + dP)) * (1 + e1)) * e2, [0, 0]) *)
Lemma t26 : p45.
Proof.
 refine (rel_refl r24 i41 _) ; finalize.
Qed.
Lemma l43 : s1 -> p45 (* REL(k1 * lam + (k2 * dT + k3 * dP) * (1 + e1) + (k2 + k3) * e1 + (k1 * (1 + lam) + (k2 * (1 + dT) + k3 * (1 + dP)) * (1 + e1)) * e2, k1 * lam + (k2 * dT + k3 * dP) * (1 + e1) + (k2 + k3) * e1 + (k1 * (1 + lam) + (k2 * (1 + dT) + k3 * (1 + dP)) * (1 + e1)) * e2, [0, 0]) *).
Proof.
 intros h0.
 apply t26.
Qed.
Lemma t27 : p44 -> p45 -> p43.
Proof.
 intros h0 h1.
 refine (rel_rewrite_1 r1 r24 r24 i41 h0 h1) ; finalize.
Qed.
Lemma l41 : s1 -> p43 (* REL(Y - 1, k1 * lam + (k2 * dT + k3 * dP) * (1 + e1) + (k2 + k3) * e1 + (k1 * (1 + lam) + (k2 * (1 + dT) + k3 * (1 + dP)) * (1 + e1)) * e2, [0, 0]) *).
Proof.
 intros h0.
 assert (h1 := l42 h0).
 assert (h2 := l43 h0).
 apply t27. exact h1. exact h2.
Qed.
Lemma t28 : p10 -> p43 -> p9.
Proof.
 intros h0 h1.
 refine (bnd_of_bnd_rel_o r1 r24 i8 i41 i8 h0 h1 _) ; finalize.
Qed.
Lemma l3 : s1 -> p9 (* BND(Y - 1, [-4.6653e-22, 4.6653e-22]) *).
Proof.
 intros h0.
 assert (h1 := l4 h0).
 assert (h2 := l41 h0).
 apply t28. exact h1. exact h2.
Qed.
Lemma l1 : s1 -> False.
Proof.
 intros h0.
 assert (h1 := l2 h0).
 assert (h2 := l3 h0).
 refine (simplify (Tatom false (Abnd 0%nat i7)) Tfalse (Abnd 0%nat i8) (List.cons r1 List.nil) h2 h1 _) ; finalize.
Qed.
End Generated_by_Gappa.
