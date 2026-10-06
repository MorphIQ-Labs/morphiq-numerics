Require Import Gappa.Gappa_library.
Section Generated_by_Gappa.
Variable _th : R.
Notation r5 := (Float1 (1)).
Variable _dl : R.
Notation r4 := ((r5 + _dl)%R).
Notation _t := ((_th * r4)%R).
Notation r10 := ((_t * _t)%R).
Notation r9 := ((r10 * _t)%R).
Notation _s0 := (float2R (Float2 (-6004799503160661) (-55))).
Notation _s1 := (float2R (Float2 (600479950272053) (-56))).
Notation _s2 := (float2R (Float2 (-3659917331012787) (-64))).
Notation r16 := ((r10 * _s2)%R).
Notation r14 := ((_s1 + r16)%R).
Notation r13 := ((r10 * r14)%R).
Notation _Pt := ((_s0 + r13)%R).
Notation r8 := ((r9 * _Pt)%R).
Variable _al : R.
Notation r18 := ((r5 + _al)%R).
Notation r7 := ((r8 * r18)%R).
Notation _ST := ((_t + r7)%R).
Notation r27 := ((_th * _th)%R).
Notation r26 := ((r27 * _th)%R).
Notation r31 := ((r27 * _s2)%R).
Notation r30 := ((_s1 + r31)%R).
Notation r29 := ((r27 * r30)%R).
Notation _Ph := ((_s0 + r29)%R).
Notation r25 := ((r26 * _Ph)%R).
Variable _et : R.
Notation r32 := ((r5 + _et)%R).
Notation r24 := ((r25 * r32)%R).
Notation r23 := ((_t + r24)%R).
Variable _d2 : R.
Notation r34 := ((r5 + _d2)%R).
Notation _SN := ((r23 * r34)%R).
Notation r21 := ((_SN - _ST)%R).
Notation r20 := ((r21 / _ST)%R).
Notation r37 := ((r21 / _th)%R).
Notation r38 := ((_ST / _th)%R).
Notation r36 := ((r37 / r38)%R).
Hypothesis a1 : (_th <> 0)%R -> (_ST <> 0)%R -> r20 = r36.
Lemma b1 : NZR _th -> NZR _ST -> r20 = r36.
 intros h0 h1.
 apply a1.
 exact h0.
 exact h1.
Qed.
Notation r45 := ((r4 * r4)%R).
Notation r44 := ((r45 * r4)%R).
Notation r43 := ((r44 * _th)%R).
Notation r42 := ((r43 * _th)%R).
Notation r41 := ((r42 * _Pt)%R).
Notation r40 := ((r41 * r18)%R).
Notation r39 := ((r4 + r40)%R).
Hypothesis a2 : (_th <> 0)%R -> r38 = r39.
Lemma b2 : NZR _th -> r38 = r39.
 intros h0.
 apply a2.
 exact h0.
Qed.
Notation r47 := ((r4 * _d2)%R).
Notation r51 := ((_Ph * r32)%R).
Notation r50 := ((r51 * r34)%R).
Notation r53 := ((r44 * _Pt)%R).
Notation r52 := ((r53 * r18)%R).
Notation r49 := ((r50 - r52)%R).
Notation r48 := ((r27 * r49)%R).
Notation r46 := ((r47 + r48)%R).
Hypothesis a3 : (_th <> 0)%R -> r37 = r46.
Lemma b3 : NZR _th -> r37 = r46.
 intros h0.
 apply a3.
 exact h0.
Qed.
Notation r58 := ((r32 * r34)%R).
Notation r57 := ((r58 - r5)%R).
Notation r56 := ((_Ph * r57)%R).
Notation r61 := ((r44 * r18)%R).
Notation r60 := ((r61 - r5)%R).
Notation r59 := ((_Pt * r60)%R).
Notation r55 := ((r56 - r59)%R).
Notation r64 := ((r45 - r5)%R).
Notation r63 := ((r27 * r64)%R).
Notation r68 := ((_s2 * _th)%R).
Notation r67 := ((r68 * _th)%R).
Notation r69 := ((r5 + r45)%R).
Notation r66 := ((r67 * r69)%R).
Notation r65 := ((_s1 + r66)%R).
Notation r62 := ((r63 * r65)%R).
Notation r54 := ((r55 - r62)%R).
Hypothesis a4 : r49 = r54.
Lemma b4 : r49 = r54.
 apply a4.
Qed.
Notation r70 := ((Rabs _th)%R).
Definition f1 := Float2 (1) (-320).
Definition f2 := Float2 (1) (-60).
Definition i1 := makepairF f1 f2.
Notation p1 := (BND r70 i1). (* BND(|th|, [4.68168e-97, 8.67362e-19]) *)
Definition f3 := Float2 (-1) (-53).
Definition f4 := Float2 (1) (-53).
Definition i2 := makepairF f3 f4.
Notation p2 := (BND _dl i2). (* BND(dl, [-1.11022e-16, 1.11022e-16]) *)
Definition s5 := (p1 /\ p2).
Definition f5 := Float2 (-1) (0).
Definition f6 := Float2 (1) (1).
Definition i3 := makepairF f5 f6.
Notation p3 := (BND _et i3). (* BND(et, [-1, 2]) *)
Definition s4 := (s5 /\ p3).
Definition f7 := Float2 (-259) (-62).
Definition f8 := Float2 (259) (-62).
Definition i4 := makepairF f7 f8.
Notation p4 := (BND _al i4). (* BND(al, [-5.61617e-17, 5.61617e-17]) *)
Definition s3 := (s4 /\ p4).
Definition f9 := Float2 (-1) (-105).
Definition f10 := Float2 (1) (-105).
Definition i5 := makepairF f9 f10.
Notation p5 := (BND _d2 i5). (* BND(d2, [-2.46519e-32, 2.46519e-32]) *)
Definition s2 := (s3 /\ p5).
Definition f11 := Float2 (-1) (-65).
Definition f12 := Float2 (1) (-65).
Definition i6 := makepairF f11 f12.
Notation p6 := (BND r20 i6). (* BND((SN - ST) / ST, [-2.71051e-20, 2.71051e-20]) *)
Definition s6 := (not p6).
Definition s1 := (s2 /\ s6).
Definition f13 := Float2 (0) (0).
Notation p7 := ((_th <= f13)%R). (* BND(th, [-inf, 0]) *)
Lemma l3 : s1 -> s6.
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj2 h1).
Qed.
Definition f14 := Float2 (-1291138073045520046344975825835089791953973145688565307228379581135959788839909669565070981082993360627278286417877719761) (-504).
Definition f15 := Float2 (645565753022243656965704618770471299784741430459620493596502077855004083872619971412554374336464155786484050891202312341) (-503).
Definition i7 := makepairF f14 f15.
Notation p8 := (BND r20 i7). (* BND((SN - ST) / ST, [-2.46522e-32, 2.4652e-32]) *)
Notation p9 := (r20 = r36). (* EQL((SN - ST) / ST, (SN - ST) / th / (ST / th)) *)
Notation p10 := (NZR _th). (* NZR(th) *)
Notation p11 := (ABS _th i1). (* ABS(th, [4.68168e-97, 8.67362e-19]) *)
Lemma l12 : s1 -> s2.
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj1 h1).
Qed.
Lemma l11 : s1 -> s3.
Proof.
 intros h0.
 assert (h1 := l12 h0).
 exact (proj1 h1).
Qed.
Lemma l10 : s1 -> s4.
Proof.
 intros h0.
 assert (h1 := l11 h0).
 exact (proj1 h1).
Qed.
Lemma l9 : s1 -> s5.
Proof.
 intros h0.
 assert (h1 := l10 h0).
 exact (proj1 h1).
Qed.
Lemma l8 : s1 -> p1 (* BND(|th|, [4.68168e-97, 8.67362e-19]) *).
Proof.
 intros h0.
 assert (h1 := l9 h0).
 exact (proj1 h1).
Qed.
Lemma t1 : p1 -> p11.
Proof.
 intros h0.
 refine (abs_of_uabs _th i1 h0 _) ; finalize.
Qed.
Lemma l7 : s1 -> p11 (* ABS(th, [4.68168e-97, 8.67362e-19]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 apply t1. exact h1.
Qed.
Definition f16 := Float2 (1) (0).
Definition i8 := makepairF f1 f16.
Notation p12 := (ABS _th i8). (* ABS(th, [4.68168e-97, 1]) *)
Lemma t2 : p12 -> p10.
Proof.
 intros h0.
 refine (nzr_of_abs _th i8 h0 _) ; finalize.
Qed.
Lemma l6 : s1 -> p10 (* NZR(th) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 apply t2. refine (abs_subset _th i1 i8 h1 _) ; finalize.
Qed.
Notation p13 := (NZR _ST). (* NZR(ST) *)
Definition f17 := Float2 (1) (-321).
Definition i9 := makepairF f17 f16.
Notation p14 := (ABS _ST i9). (* ABS(ST, [2.34084e-97, 1]) *)
Definition f18 := Float2 (-1) (-321).
Definition i10 := makepairF f5 f18.
Notation p15 := (BND _ST i10). (* BND(ST, [-1, -2.34084e-97]) *)
Notation r71 := ((r38 * _th)%R).
Notation p16 := (BND r71 i10). (* BND(ST / th * th, [-1, -2.34084e-97]) *)
Definition f19 := Float2 (161390617380431768935537010827754557665832233210254226670190467130952255309431956534157533786513152701958937777369950977) (-396).
Definition i11 := makepairF f19 f6.
Notation p17 := (BND r38 i11). (* BND(ST / th, [1, 2]) *)
Notation p18 := (BND r39 i11). (* BND(1 + dl + (1 + dl) * (1 + dl) * (1 + dl) * th * th * Pt * (1 + al), [1, 2]) *)
Definition f20 := Float2 (9007199254740991) (-53).
Definition f21 := Float2 (9007199254740993) (-53).
Definition i12 := makepairF f20 f21.
Notation p19 := (BND r4 i12). (* BND(1 + dl, [1, 1]) *)
Definition i13 := makepairF f16 f16.
Notation p20 := (BND r5 i13). (* BND(1, [1, 1]) *)
Lemma t3 : p20.
Proof.
 refine (constant1 _ i13 _) ; finalize.
Qed.
Lemma l20 : s1 -> p20 (* BND(1, [1, 1]) *).
Proof.
 intros h0.
 apply t3.
Qed.
Lemma l21 : s1 -> p2 (* BND(dl, [-1.11022e-16, 1.11022e-16]) *).
Proof.
 intros h0.
 assert (h1 := l9 h0).
 exact (proj2 h1).
Qed.
Lemma t4 : p20 -> p2 -> p19.
Proof.
 intros h0 h1.
 refine (add r5 _dl i13 i2 i12 h0 h1 _) ; finalize.
Qed.
Lemma l19 : s1 -> p19 (* BND(1 + dl, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l20 h0).
 assert (h2 := l21 h0).
 apply t4. exact h1. exact h2.
Qed.
Definition f22 := Float2 (-20236134294018017908561764775641941866707810419860331352207898715765064298069841151) (-396).
Definition f23 := Float2 (1) (-1).
Definition i14 := makepairF f22 f23.
Notation p21 := (BND r40 i14). (* BND((1 + dl) * (1 + dl) * (1 + dl) * th * th * Pt * (1 + al), [-1.25386e-37, 0.5]) *)
Definition f24 := Float2 (-4388012152856550663664615595905447645996404178604089404793640277) (-334).
Definition f25 := Float2 (1) (-2).
Definition i15 := makepairF f24 f25.
Notation p22 := (BND r41 i15). (* BND((1 + dl) * (1 + dl) * (1 + dl) * th * th * Pt, [-1.25386e-37, 0.25]) *)
Definition f26 := Float2 (730750818665451702490757660178213618792745926657) (-279).
Definition i16 := makepairF f5 f26.
Notation p23 := (BND r42 i16). (* BND((1 + dl) * (1 + dl) * (1 + dl) * th * th, [-1, 7.52316e-37]) *)
Definition f27 := Float2 (-730750818665451702490757660178213618792745926657) (-219).
Definition f28 := Float2 (730750818665451702490757660178213618792745926657) (-219).
Definition i17 := makepairF f27 f28.
Notation p24 := (BND r43 i17). (* BND((1 + dl) * (1 + dl) * (1 + dl) * th, [-8.67362e-19, 8.67362e-19]) *)
Definition f29 := Float2 (730750818665451215712927172538123444058715062271) (-159).
Definition f30 := Float2 (730750818665451702490757660178213618792745926657) (-159).
Definition i18 := makepairF f29 f30.
Notation p25 := (BND r44 i18). (* BND((1 + dl) * (1 + dl) * (1 + dl), [1, 1]) *)
Definition f31 := Float2 (81129638414606663681390495662081) (-106).
Definition f32 := Float2 (81129638414606699710187514626049) (-106).
Definition i19 := makepairF f31 f32.
Notation p26 := (BND r45 i19). (* BND((1 + dl) * (1 + dl), [1, 1]) *)
Notation p27 := (ABS r4 i12). (* ABS(1 + dl, [1, 1]) *)
Lemma t5 : p19 -> p27.
Proof.
 intros h0.
 refine (abs_of_bnd_p r4 i12 i12 h0 _) ; finalize.
Qed.
Lemma l28 : s1 -> p27 (* ABS(1 + dl, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l19 h0).
 apply t5. exact h1.
Qed.
Lemma t6 : p27 -> p26.
Proof.
 intros h0.
 refine (square r4 i12 i19 h0 _) ; finalize.
Qed.
Lemma l27 : s1 -> p26 (* BND((1 + dl) * (1 + dl), [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l28 h0).
 apply t6. exact h1.
Qed.
Lemma t7 : p26 -> p19 -> p25.
Proof.
 intros h0 h1.
 refine (mul_pp r45 r4 i19 i12 i18 h0 h1 _) ; finalize.
Qed.
Lemma l26 : s1 -> p25 (* BND((1 + dl) * (1 + dl) * (1 + dl), [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l27 h0).
 assert (h2 := l19 h0).
 apply t7. exact h1. exact h2.
Qed.
Definition f33 := Float2 (-1) (-60).
Definition i20 := makepairF f33 f2.
Notation p28 := (BND _th i20). (* BND(th, [-8.67362e-19, 8.67362e-19]) *)
Lemma t8 : p11 -> p28.
Proof.
 intros h0.
 refine (bnd_of_abs _th i1 i20 h0 _) ; finalize.
Qed.
Lemma l29 : s1 -> p28 (* BND(th, [-8.67362e-19, 8.67362e-19]) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 apply t8. exact h1.
Qed.
Definition i21 := makepairF f23 f30.
Notation p29 := (BND r44 i21). (* BND((1 + dl) * (1 + dl) * (1 + dl), [0.5, 1]) *)
Lemma t9 : p29 -> p28 -> p24.
Proof.
 intros h0 h1.
 refine (mul_po r44 _th i21 i20 i17 h0 h1 _) ; finalize.
Qed.
Lemma l25 : s1 -> p24 (* BND((1 + dl) * (1 + dl) * (1 + dl) * th, [-8.67362e-19, 8.67362e-19]) *).
Proof.
 intros h0.
 assert (h1 := l26 h0).
 assert (h2 := l29 h0).
 apply t9. refine (subset r44 i18 i21 h1 _) ; finalize. exact h2.
Qed.
Lemma t10 : p24 -> p28 -> p23.
Proof.
 intros h0 h1.
 refine (mul_oo r43 _th i17 i20 i16 h0 h1 _) ; finalize.
Qed.
Lemma l24 : s1 -> p23 (* BND((1 + dl) * (1 + dl) * (1 + dl) * th * th, [-1, 7.52316e-37]) *).
Proof.
 intros h0.
 assert (h1 := l25 h0).
 assert (h2 := l29 h0).
 apply t10. exact h1. exact h2.
Qed.
Definition f34 := Float2 (-6004799503160661) (-55).
Definition f35 := Float2 (-1295112594817152642053116825480639818600847606074951879304242403301546424393067825611) (-282).
Definition i22 := makepairF f34 f35.
Notation p30 := (BND _Pt i22). (* BND(Pt, [-0.166667, -0.166667]) *)
Definition i23 := makepairF f34 f34.
Notation p31 := (BND _s0 i23). (* BND(s0, [-0.166667, -0.166667]) *)
Lemma t11 : p31.
Proof.
 refine (constant2 _ i23 _) ; finalize.
Qed.
Lemma l31 : s1 -> p31 (* BND(s0, [-0.166667, -0.166667]) *).
Proof.
 intros h0.
 apply t11.
Qed.
Definition f36 := Float2 (1) (-647).
Definition f37 := Float2 (48716721240792671831247409749529816134110508597) (-282).
Definition i24 := makepairF f36 f37.
Notation p32 := (BND r13 i24). (* BND(t * t * (s1 + t * t * s2), [1.71235e-195, 6.2693e-39]) *)
Definition f38 := Float2 (31) (-645).
Definition f39 := Float2 (81129638414606699710187514626049) (-226).
Definition i25 := makepairF f38 f39.
Notation p33 := (BND r10 i25). (* BND(t * t, [2.12332e-193, 7.52316e-37]) *)
Definition f40 := Float2 (63) (-326).
Definition f41 := Float2 (9007199254740993) (-113).
Definition i26 := makepairF f40 f41.
Notation p34 := (ABS _t i26). (* ABS(t, [4.60853e-97, 8.67362e-19]) *)
Definition f42 := Float2 (63) (-6).
Definition i27 := makepairF f42 f21.
Notation p35 := (ABS r4 i27). (* ABS(1 + dl, [0.984375, 1]) *)
Lemma t12 : p11 -> p35 -> p34.
Proof.
 intros h0 h1.
 refine (mul_aa _th r4 i1 i27 i26 h0 h1 _) ; finalize.
Qed.
Lemma l34 : s1 -> p34 (* ABS(t, [4.60853e-97, 8.67362e-19]) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 assert (h2 := l28 h0).
 apply t12. exact h1. refine (abs_subset r4 i12 i27 h2 _) ; finalize.
Qed.
Lemma t13 : p34 -> p33.
Proof.
 intros h0.
 refine (square _t i26 i25 h0 _) ; finalize.
Qed.
Lemma l33 : s1 -> p33 (* BND(t * t, [2.12332e-193, 7.52316e-37]) *).
Proof.
 intros h0.
 assert (h1 := l34 h0).
 apply t13. exact h1.
Qed.
Definition f43 := Float2 (17) (-11).
Definition f44 := Float2 (600479950272053) (-56).
Definition i28 := makepairF f43 f44.
Notation p36 := (BND r14 i28). (* BND(s1 + t * t * s2, [0.00830078, 0.00833333]) *)
Definition f45 := Float2 (273) (-15).
Definition i29 := makepairF f45 f44.
Notation p37 := (BND _s1 i29). (* BND(s1, [0.0083313, 0.00833333]) *)
Lemma t14 : p37.
Proof.
 refine (constant2 _ i29 _) ; finalize.
Qed.
Lemma l36 : s1 -> p37 (* BND(s1, [0.0083313, 0.00833333]) *).
Proof.
 intros h0.
 apply t14.
Qed.
Definition f46 := Float2 (-1) (-15).
Definition f47 := Float2 (-1) (-653).
Definition i30 := makepairF f46 f47.
Notation p38 := (BND r16 i30). (* BND(t * t * s2, [-3.05176e-05, -2.67555e-197]) *)
Definition f48 := Float2 (-3) (-14).
Definition i31 := makepairF f5 f48.
Notation p39 := (BND _s2 i31). (* BND(s2, [-1, -0.000183105]) *)
Lemma t15 : p39.
Proof.
 refine (constant2 _ i31 _) ; finalize.
Qed.
Lemma l38 : s1 -> p39 (* BND(s2, [-1, -0.000183105]) *).
Proof.
 intros h0.
 apply t15.
Qed.
Definition f49 := Float2 (3) (-642).
Definition f50 := Float2 (1) (-15).
Definition i32 := makepairF f49 f50.
Notation p40 := (BND r10 i32). (* BND(t * t, [1.64386e-193, 3.05176e-05]) *)
Lemma t16 : p40 -> p39 -> p38.
Proof.
 intros h0 h1.
 refine (mul_pn r10 _s2 i32 i31 i30 h0 h1 _) ; finalize.
Qed.
Lemma l37 : s1 -> p38 (* BND(t * t * s2, [-3.05176e-05, -2.67555e-197]) *).
Proof.
 intros h0.
 assert (h1 := l33 h0).
 assert (h2 := l38 h0).
 apply t16. refine (subset r10 i25 i32 h1 _) ; finalize. exact h2.
Qed.
Lemma t17 : p37 -> p38 -> p36.
Proof.
 intros h0 h1.
 refine (add _s1 r16 i29 i30 i28 h0 h1 _) ; finalize.
Qed.
Lemma l35 : s1 -> p36 (* BND(s1 + t * t * s2, [0.00830078, 0.00833333]) *).
Proof.
 intros h0.
 assert (h1 := l36 h0).
 assert (h2 := l37 h0).
 apply t17. exact h1. exact h2.
Qed.
Lemma t18 : p33 -> p36 -> p32.
Proof.
 intros h0 h1.
 refine (mul_pp r10 r14 i25 i28 i24 h0 h1 _) ; finalize.
Qed.
Lemma l32 : s1 -> p32 (* BND(t * t * (s1 + t * t * s2), [1.71235e-195, 6.2693e-39]) *).
Proof.
 intros h0.
 assert (h1 := l33 h0).
 assert (h2 := l35 h0).
 apply t18. exact h1. exact h2.
Qed.
Lemma t19 : p31 -> p32 -> p30.
Proof.
 intros h0 h1.
 refine (add _s0 r13 i23 i24 i22 h0 h1 _) ; finalize.
Qed.
Lemma l30 : s1 -> p30 (* BND(Pt, [-0.166667, -0.166667]) *).
Proof.
 intros h0.
 assert (h1 := l31 h0).
 assert (h2 := l32 h0).
 apply t19. exact h1. exact h2.
Qed.
Definition f51 := Float2 (-1) (-3).
Definition i33 := makepairF f34 f51.
Notation p41 := (BND _Pt i33). (* BND(Pt, [-0.166667, -0.125]) *)
Lemma t20 : p23 -> p41 -> p22.
Proof.
 intros h0 h1.
 refine (mul_on r42 _Pt i16 i33 i15 h0 h1 _) ; finalize.
Qed.
Lemma l23 : s1 -> p22 (* BND((1 + dl) * (1 + dl) * (1 + dl) * th * th * Pt, [-1.25386e-37, 0.25]) *).
Proof.
 intros h0.
 assert (h1 := l24 h0).
 assert (h2 := l30 h0).
 apply t20. exact h1. refine (subset _Pt i22 i33 h2 _) ; finalize.
Qed.
Definition f52 := Float2 (4611686018427387645) (-62).
Definition f53 := Float2 (4611686018427388163) (-62).
Definition i34 := makepairF f52 f53.
Notation p42 := (BND r18 i34). (* BND(1 + al, [1, 1]) *)
Lemma l40 : s1 -> p4 (* BND(al, [-5.61617e-17, 5.61617e-17]) *).
Proof.
 intros h0.
 assert (h1 := l11 h0).
 exact (proj2 h1).
Qed.
Lemma t21 : p20 -> p4 -> p42.
Proof.
 intros h0 h1.
 refine (add r5 _al i13 i4 i34 h0 h1 _) ; finalize.
Qed.
Lemma l39 : s1 -> p42 (* BND(1 + al, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l20 h0).
 assert (h2 := l40 h0).
 apply t21. exact h1. exact h2.
Qed.
Definition i35 := makepairF f23 f53.
Notation p43 := (BND r18 i35). (* BND(1 + al, [0.5, 1]) *)
Lemma t22 : p22 -> p43 -> p21.
Proof.
 intros h0 h1.
 refine (mul_op r41 r18 i15 i35 i14 h0 h1 _) ; finalize.
Qed.
Lemma l22 : s1 -> p21 (* BND((1 + dl) * (1 + dl) * (1 + dl) * th * th * Pt * (1 + al), [-1.25386e-37, 0.5]) *).
Proof.
 intros h0.
 assert (h1 := l23 h0).
 assert (h2 := l39 h0).
 apply t22. exact h1. refine (subset r18 i34 i35 h2 _) ; finalize.
Qed.
Definition f54 := Float2 (3) (-1).
Definition i36 := makepairF f20 f54.
Notation p44 := (BND r4 i36). (* BND(1 + dl, [1, 1.5]) *)
Lemma t23 : p44 -> p21 -> p18.
Proof.
 intros h0 h1.
 refine (add r4 r40 i36 i14 i11 h0 h1 _) ; finalize.
Qed.
Lemma l18 : s1 -> p18 (* BND(1 + dl + (1 + dl) * (1 + dl) * (1 + dl) * th * th * Pt * (1 + al), [1, 2]) *).
Proof.
 intros h0.
 assert (h1 := l19 h0).
 assert (h2 := l22 h0).
 apply t23. refine (subset r4 i12 i36 h1 _) ; finalize. exact h2.
Qed.
Definition i37 := makepairF f13 f13.
Notation p45 := (REL r38 r39 i37). (* REL(ST / th, 1 + dl + (1 + dl) * (1 + dl) * (1 + dl) * th * th * Pt * (1 + al), [0, 0]) *)
Notation p46 := (r38 = r39). (* EQL(ST / th, 1 + dl + (1 + dl) * (1 + dl) * (1 + dl) * th * th * Pt * (1 + al)) *)
Lemma t24 : p10 -> p46.
Proof.
 intros h0.
 refine (b2 h0) ; finalize.
Qed.
Lemma l42 : s1 -> p46 (* EQL(ST / th, 1 + dl + (1 + dl) * (1 + dl) * (1 + dl) * th * th * Pt * (1 + al)) *).
Proof.
 intros h0.
 assert (h1 := l6 h0).
 apply t24. exact h1.
Qed.
Notation p47 := (REL r39 r39 i37). (* REL(1 + dl + (1 + dl) * (1 + dl) * (1 + dl) * th * th * Pt * (1 + al), 1 + dl + (1 + dl) * (1 + dl) * (1 + dl) * th * th * Pt * (1 + al), [0, 0]) *)
Lemma t25 : p47.
Proof.
 refine (rel_refl r39 i37 _) ; finalize.
Qed.
Lemma l43 : s1 -> p47 (* REL(1 + dl + (1 + dl) * (1 + dl) * (1 + dl) * th * th * Pt * (1 + al), 1 + dl + (1 + dl) * (1 + dl) * (1 + dl) * th * th * Pt * (1 + al), [0, 0]) *).
Proof.
 intros h0.
 apply t25.
Qed.
Lemma t26 : p46 -> p47 -> p45.
Proof.
 intros h0 h1.
 refine (rel_rewrite_1 r38 r39 r39 i37 h0 h1) ; finalize.
Qed.
Lemma l41 : s1 -> p45 (* REL(ST / th, 1 + dl + (1 + dl) * (1 + dl) * (1 + dl) * th * th * Pt * (1 + al), [0, 0]) *).
Proof.
 intros h0.
 assert (h1 := l42 h0).
 assert (h2 := l43 h0).
 apply t26. exact h1. exact h2.
Qed.
Lemma t27 : p18 -> p45 -> p17.
Proof.
 intros h0 h1.
 refine (bnd_of_bnd_rel_p r38 r39 i11 i37 i11 h0 h1 _) ; finalize.
Qed.
Lemma l17 : s1 -> p17 (* BND(ST / th, [1, 2]) *).
Proof.
 intros h0.
 assert (h1 := l18 h0).
 assert (h2 := l41 h0).
 apply t27. exact h1. exact h2.
Qed.
Definition f55 := Float2 (-1) (-1).
Definition f56 := Float2 (-1) (-320).
Definition i38 := makepairF f55 f56.
Notation p48 := (BND _th i38). (* BND(th, [-0.5, -4.68168e-97]) *)
Definition i39 := makepairF f33 f13.
Notation p49 := (BND _th i39). (* BND(th, [-8.67362e-19, 0]) *)
Lemma l46 : p7 -> s1 -> p7 (* BND(th, [-inf, 0]) *).
Proof.
 intros h0 h1.
 assert (h2 := h0).
 exact (h2).
Qed.
Lemma l45 : p7 -> s1 -> p49 (* BND(th, [-8.67362e-19, 0]) *).
Proof.
 intros h0 h1.
 assert (h2 := l46 h0 h1).
 assert (h3 := l29 h1).
 apply intersect_hb with (1 := h2) (2 := h3). finalize.
Qed.
Definition i40 := makepairF f55 f13.
Notation p50 := (BND _th i40). (* BND(th, [-0.5, 0]) *)
Lemma t28 : p50 -> p12 -> p48.
Proof.
 intros h0 h1.
 refine (bnd_of_bnd_abs_n _th i40 i8 i38 h0 h1 _) ; finalize.
Qed.
Lemma l44 : p7 -> s1 -> p48 (* BND(th, [-0.5, -4.68168e-97]) *).
Proof.
 intros h0 h1.
 assert (h2 := l45 h0 h1).
 assert (h3 := l7 h1).
 apply t28. refine (subset _th i39 i40 h2 _) ; finalize. refine (abs_subset _th i1 i8 h3 _) ; finalize.
Qed.
Definition i41 := makepairF f23 f6.
Notation p51 := (BND r38 i41). (* BND(ST / th, [0.5, 2]) *)
Lemma t29 : p51 -> p48 -> p16.
Proof.
 intros h0 h1.
 refine (mul_pn r38 _th i41 i38 i10 h0 h1 _) ; finalize.
Qed.
Lemma l16 : p7 -> s1 -> p16 (* BND(ST / th * th, [-1, -2.34084e-97]) *).
Proof.
 intros h0 h1.
 assert (h2 := l17 h1).
 assert (h3 := l44 h0 h1).
 apply t29. refine (subset r38 i11 i41 h2 _) ; finalize. exact h3.
Qed.
Lemma t30 : p10 -> p16 -> p15.
Proof.
 intros h0 h1.
 refine (div_xilu _ST _ i10 h0 h1) ; finalize.
Qed.
Lemma l15 : p7 -> s1 -> p15 (* BND(ST, [-1, -2.34084e-97]) *).
Proof.
 intros h0 h1.
 assert (h2 := l6 h1).
 assert (h3 := l16 h0 h1).
 apply t30. exact h2. exact h3.
Qed.
Lemma t31 : p15 -> p14.
Proof.
 intros h0.
 refine (abs_of_bnd_n _ST i10 i9 h0 _) ; finalize.
Qed.
Lemma l14 : p7 -> s1 -> p14 (* ABS(ST, [2.34084e-97, 1]) *).
Proof.
 intros h0 h1.
 assert (h2 := l15 h0 h1).
 apply t31. exact h2.
Qed.
Lemma t32 : p14 -> p13.
Proof.
 intros h0.
 refine (nzr_of_abs _ST i9 h0 _) ; finalize.
Qed.
Lemma l13 : p7 -> s1 -> p13 (* NZR(ST) *).
Proof.
 intros h0 h1.
 assert (h2 := l14 h0 h1).
 apply t32. exact h2.
Qed.
Lemma t33 : p10 -> p13 -> p9.
Proof.
 intros h0 h1.
 refine (b1 h0 h1) ; finalize.
Qed.
Lemma l5 : p7 -> s1 -> p9 (* EQL((SN - ST) / ST, (SN - ST) / th / (ST / th)) *).
Proof.
 intros h0 h1.
 assert (h2 := l6 h1).
 assert (h3 := l13 h0 h1).
 apply t33. exact h2. exact h3.
Qed.
Notation p52 := (BND r36 i7). (* BND((SN - ST) / th / (ST / th), [-2.46522e-32, 2.4652e-32]) *)
Definition f57 := Float2 (-645569036522759951499927079652866572890503269305972798128680951194671300345904394328832251797855555577196357345449135325) (-503).
Definition f58 := Float2 (3978606127412587596972732741535424758569891099918830556726038241948731271566115397260543) (-396).
Definition i42 := makepairF f57 f58.
Notation p53 := (BND r37 i42). (* BND((SN - ST) / th, [-2.46522e-32, 2.4652e-32]) *)
Notation p54 := (BND r46 i42). (* BND((1 + dl) * d2 + th * th * (Ph * (1 + et) * (1 + d2) - (1 + dl) * (1 + dl) * (1 + dl) * Pt * (1 + al)), [-2.46522e-32, 2.4652e-32]) *)
Definition f59 := Float2 (-9007199254740993) (-158).
Definition f60 := Float2 (9007199254740993) (-158).
Definition i43 := makepairF f59 f60.
Notation p55 := (BND r47 i43). (* BND((1 + dl) * d2, [-2.46519e-32, 2.46519e-32]) *)
Lemma l51 : s1 -> p5 (* BND(d2, [-2.46519e-32, 2.46519e-32]) *).
Proof.
 intros h0.
 assert (h1 := l12 h0).
 exact (proj2 h1).
Qed.
Definition i44 := makepairF f23 f21.
Notation p56 := (BND r4 i44). (* BND(1 + dl, [0.5, 1]) *)
Lemma t34 : p56 -> p5 -> p55.
Proof.
 intros h0 h1.
 refine (mul_po r4 _d2 i44 i5 i43 h0 h1 _) ; finalize.
Qed.
Lemma l50 : s1 -> p55 (* BND((1 + dl) * d2, [-2.46519e-32, 2.46519e-32]) *).
Proof.
 intros h0.
 assert (h1 := l19 h0).
 assert (h2 := l51 h0).
 apply t34. refine (subset r4 i12 i44 h1 _) ; finalize. exact h2.
Qed.
Definition f61 := Float2 (-6567001032732414115536962378866469923842908450020028360200550724278042042864830081035712670845530140779660834557149) (-503).
Definition f62 := Float2 (20236134294018017908561764775641941866707810419860331352207898715765064298069841151) (-396).
Definition i45 := makepairF f61 f62.
Notation p57 := (BND r48 i45). (* BND(th * th * (Ph * (1 + et) * (1 + d2) - (1 + dl) * (1 + dl) * (1 + dl) * Pt * (1 + al)), [-2.50772e-37, 1.25386e-37]) *)
Definition f63 := Float2 (1) (-640).
Definition f64 := Float2 (1) (-120).
Definition i46 := makepairF f63 f64.
Notation p58 := (BND r27 i46). (* BND(th * th, [2.19181e-193, 7.52316e-37]) *)
Lemma t35 : p11 -> p58.
Proof.
 intros h0.
 refine (square _th i1 i46 h0 _) ; finalize.
Qed.
Lemma l53 : s1 -> p58 (* BND(th * th, [2.19181e-193, 7.52316e-37]) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 apply t35. exact h1.
Qed.
Definition f65 := Float2 (-6567001032732414115536962378866469923842908450020028360200550724278042042864830081035712670845530140779660834557149) (-383).
Definition f66 := Float2 (20236134294018017908561764775641941866707810419860331352207898715765064298069841151) (-276).
Definition i47 := makepairF f65 f66.
Notation p59 := (BND r49 i47). (* BND(Ph * (1 + et) * (1 + d2) - (1 + dl) * (1 + dl) * (1 + dl) * Pt * (1 + al), [-0.333333, 0.166667]) *)
Definition f67 := Float2 (-730750818665451418537023209054818676331973181439) (-160).
Definition i48 := makepairF f67 f13.
Notation p60 := (BND r50 i48). (* BND(Ph * (1 + et) * (1 + d2), [-0.5, 0]) *)
Definition f68 := Float2 (-18014398509481983) (-55).
Definition i49 := makepairF f68 f13.
Notation p61 := (BND r51 i49). (* BND(Ph * (1 + et), [-0.5, 0]) *)
Notation p62 := (BND _Ph i33). (* BND(Ph, [-0.166667, -0.125]) *)
Definition f69 := Float2 (1) (-5).
Definition i50 := makepairF f36 f69.
Notation p63 := (BND r29 i50). (* BND(th * th * (s1 + th * th * s2), [1.71235e-195, 0.03125]) *)
Definition f70 := Float2 (1) (-7).
Definition i51 := makepairF f70 f16.
Notation p64 := (BND r30 i51). (* BND(s1 + th * th * s2, [0.0078125, 1]) *)
Definition f71 := Float2 (-1) (-11).
Definition i52 := makepairF f71 f47.
Notation p65 := (BND r31 i52). (* BND(th * th * s2, [-0.000488281, -2.67555e-197]) *)
Definition f72 := Float2 (1) (-11).
Definition i53 := makepairF f63 f72.
Notation p66 := (BND r27 i53). (* BND(th * th, [2.19181e-193, 0.000488281]) *)
Definition f73 := Float2 (-1) (-13).
Definition i54 := makepairF f5 f73.
Notation p67 := (BND _s2 i54). (* BND(s2, [-1, -0.00012207]) *)
Lemma t36 : p66 -> p67 -> p65.
Proof.
 intros h0 h1.
 refine (mul_pn r27 _s2 i53 i54 i52 h0 h1 _) ; finalize.
Qed.
Lemma l60 : s1 -> p65 (* BND(th * th * s2, [-0.000488281, -2.67555e-197]) *).
Proof.
 intros h0.
 assert (h1 := l53 h0).
 assert (h2 := l38 h0).
 apply t36. refine (subset r27 i46 i53 h1 _) ; finalize. refine (subset _s2 i31 i54 h2 _) ; finalize.
Qed.
Definition i55 := makepairF f43 f16.
Notation p68 := (BND _s1 i55). (* BND(s1, [0.00830078, 1]) *)
Lemma t37 : p68 -> p65 -> p64.
Proof.
 intros h0 h1.
 refine (add _s1 r31 i55 i52 i51 h0 h1 _) ; finalize.
Qed.
Lemma l59 : s1 -> p64 (* BND(s1 + th * th * s2, [0.0078125, 1]) *).
Proof.
 intros h0.
 assert (h1 := l36 h0).
 assert (h2 := l60 h0).
 apply t37. refine (subset _s1 i29 i55 h1 _) ; finalize. exact h2.
Qed.
Definition i56 := makepairF f63 f69.
Notation p69 := (BND r27 i56). (* BND(th * th, [2.19181e-193, 0.03125]) *)
Lemma t38 : p69 -> p64 -> p63.
Proof.
 intros h0 h1.
 refine (mul_pp r27 r30 i56 i51 i50 h0 h1 _) ; finalize.
Qed.
Lemma l58 : s1 -> p63 (* BND(th * th * (s1 + th * th * s2), [1.71235e-195, 0.03125]) *).
Proof.
 intros h0.
 assert (h1 := l53 h0).
 assert (h2 := l59 h0).
 apply t38. refine (subset r27 i46 i56 h1 _) ; finalize. exact h2.
Qed.
Definition f74 := Float2 (-5) (-5).
Definition i57 := makepairF f34 f74.
Notation p70 := (BND _s0 i57). (* BND(s0, [-0.166667, -0.15625]) *)
Lemma t39 : p70 -> p63 -> p62.
Proof.
 intros h0 h1.
 refine (add _s0 r29 i57 i50 i33 h0 h1 _) ; finalize.
Qed.
Lemma l57 : s1 -> p62 (* BND(Ph, [-0.166667, -0.125]) *).
Proof.
 intros h0.
 assert (h1 := l31 h0).
 assert (h2 := l58 h0).
 apply t39. refine (subset _s0 i23 i57 h1 _) ; finalize. exact h2.
Qed.
Definition f75 := Float2 (3) (0).
Definition i58 := makepairF f13 f75.
Notation p71 := (BND r32 i58). (* BND(1 + et, [-0, 3]) *)
Lemma l62 : s1 -> p3 (* BND(et, [-1, 2]) *).
Proof.
 intros h0.
 assert (h1 := l10 h0).
 exact (proj2 h1).
Qed.
Lemma t40 : p20 -> p3 -> p71.
Proof.
 intros h0 h1.
 refine (add r5 _et i13 i3 i58 h0 h1 _) ; finalize.
Qed.
Lemma l61 : s1 -> p71 (* BND(1 + et, [-0, 3]) *).
Proof.
 intros h0.
 assert (h1 := l20 h0).
 assert (h2 := l62 h0).
 apply t40. exact h1. exact h2.
Qed.
Lemma t41 : p62 -> p71 -> p61.
Proof.
 intros h0 h1.
 refine (mul_np _Ph r32 i33 i58 i49 h0 h1 _) ; finalize.
Qed.
Lemma l56 : s1 -> p61 (* BND(Ph * (1 + et), [-0.5, 0]) *).
Proof.
 intros h0.
 assert (h1 := l57 h0).
 assert (h2 := l61 h0).
 apply t41. exact h1. exact h2.
Qed.
Definition f76 := Float2 (40564819207303340847894502572033) (-105).
Definition i59 := makepairF f23 f76.
Notation p72 := (BND r34 i59). (* BND(1 + d2, [0.5, 1]) *)
Definition i60 := makepairF f55 f10.
Notation p73 := (BND _d2 i60). (* BND(d2, [-0.5, 2.46519e-32]) *)
Lemma t42 : p20 -> p73 -> p72.
Proof.
 intros h0 h1.
 refine (add r5 _d2 i13 i60 i59 h0 h1 _) ; finalize.
Qed.
Lemma l63 : s1 -> p72 (* BND(1 + d2, [0.5, 1]) *).
Proof.
 intros h0.
 assert (h1 := l20 h0).
 assert (h2 := l51 h0).
 apply t42. exact h1. refine (subset _d2 i5 i60 h2 _) ; finalize.
Qed.
Lemma t43 : p61 -> p72 -> p60.
Proof.
 intros h0 h1.
 refine (mul_np r51 r34 i49 i59 i48 h0 h1 _) ; finalize.
Qed.
Lemma l55 : s1 -> p60 (* BND(Ph * (1 + et) * (1 + d2), [-0.5, 0]) *).
Proof.
 intros h0.
 assert (h1 := l56 h0).
 assert (h2 := l63 h0).
 apply t43. exact h1. exact h2.
Qed.
Definition f77 := Float2 (-20236134294018017908561764775641941866707810419860331352207898715765064298069841151) (-276).
Definition f78 := Float2 (-3283500516366205140720116450416695267912997804311376927898942523446276086878192671432941997371665040338800753193763) (-383).
Definition i61 := makepairF f77 f78.
Notation p74 := (BND r52 i61). (* BND((1 + dl) * (1 + dl) * (1 + dl) * Pt * (1 + al), [-0.166667, -0.166667]) *)
Definition f79 := Float2 (-4388012152856550663664615595905447645996404178604089404793640277) (-214).
Definition f80 := Float2 (-52536008261859285202031955492083104931447686200075816583231235137384221696415051410455371353450222946893192445773029) (-387).
Definition i62 := makepairF f79 f80.
Notation p75 := (BND r53 i62). (* BND((1 + dl) * (1 + dl) * (1 + dl) * Pt, [-0.166667, -0.166667]) *)
Lemma t44 : p25 -> p30 -> p75.
Proof.
 intros h0 h1.
 refine (mul_pn r44 _Pt i18 i22 i62 h0 h1 _) ; finalize.
Qed.
Lemma l65 : s1 -> p75 (* BND((1 + dl) * (1 + dl) * (1 + dl) * Pt, [-0.166667, -0.166667]) *).
Proof.
 intros h0.
 assert (h1 := l26 h0).
 assert (h2 := l30 h0).
 apply t44. exact h1. exact h2.
Qed.
Lemma t45 : p75 -> p42 -> p74.
Proof.
 intros h0 h1.
 refine (mul_np r53 r18 i62 i34 i61 h0 h1 _) ; finalize.
Qed.
Lemma l64 : s1 -> p74 (* BND((1 + dl) * (1 + dl) * (1 + dl) * Pt * (1 + al), [-0.166667, -0.166667]) *).
Proof.
 intros h0.
 assert (h1 := l65 h0).
 assert (h2 := l39 h0).
 apply t45. exact h1. exact h2.
Qed.
Lemma t46 : p60 -> p74 -> p59.
Proof.
 intros h0 h1.
 refine (sub r50 r52 i48 i61 i47 h0 h1 _) ; finalize.
Qed.
Lemma l54 : s1 -> p59 (* BND(Ph * (1 + et) * (1 + d2) - (1 + dl) * (1 + dl) * (1 + dl) * Pt * (1 + al), [-0.333333, 0.166667]) *).
Proof.
 intros h0.
 assert (h1 := l55 h0).
 assert (h2 := l64 h0).
 apply t46. exact h1. exact h2.
Qed.
Lemma t47 : p58 -> p59 -> p57.
Proof.
 intros h0 h1.
 refine (mul_po r27 r49 i46 i47 i45 h0 h1 _) ; finalize.
Qed.
Lemma l52 : s1 -> p57 (* BND(th * th * (Ph * (1 + et) * (1 + d2) - (1 + dl) * (1 + dl) * (1 + dl) * Pt * (1 + al)), [-2.50772e-37, 1.25386e-37]) *).
Proof.
 intros h0.
 assert (h1 := l53 h0).
 assert (h2 := l54 h0).
 apply t47. exact h1. exact h2.
Qed.
Lemma t48 : p55 -> p57 -> p54.
Proof.
 intros h0 h1.
 refine (add r47 r48 i43 i45 i42 h0 h1 _) ; finalize.
Qed.
Lemma l49 : s1 -> p54 (* BND((1 + dl) * d2 + th * th * (Ph * (1 + et) * (1 + d2) - (1 + dl) * (1 + dl) * (1 + dl) * Pt * (1 + al)), [-2.46522e-32, 2.4652e-32]) *).
Proof.
 intros h0.
 assert (h1 := l50 h0).
 assert (h2 := l52 h0).
 apply t48. exact h1. exact h2.
Qed.
Notation p76 := (REL r37 r46 i37). (* REL((SN - ST) / th, (1 + dl) * d2 + th * th * (Ph * (1 + et) * (1 + d2) - (1 + dl) * (1 + dl) * (1 + dl) * Pt * (1 + al)), [0, 0]) *)
Notation p77 := (r37 = r46). (* EQL((SN - ST) / th, (1 + dl) * d2 + th * th * (Ph * (1 + et) * (1 + d2) - (1 + dl) * (1 + dl) * (1 + dl) * Pt * (1 + al))) *)
Lemma t49 : p10 -> p77.
Proof.
 intros h0.
 refine (b3 h0) ; finalize.
Qed.
Lemma l67 : s1 -> p77 (* EQL((SN - ST) / th, (1 + dl) * d2 + th * th * (Ph * (1 + et) * (1 + d2) - (1 + dl) * (1 + dl) * (1 + dl) * Pt * (1 + al))) *).
Proof.
 intros h0.
 assert (h1 := l6 h0).
 apply t49. exact h1.
Qed.
Notation p78 := (REL r46 r46 i37). (* REL((1 + dl) * d2 + th * th * (Ph * (1 + et) * (1 + d2) - (1 + dl) * (1 + dl) * (1 + dl) * Pt * (1 + al)), (1 + dl) * d2 + th * th * (Ph * (1 + et) * (1 + d2) - (1 + dl) * (1 + dl) * (1 + dl) * Pt * (1 + al)), [0, 0]) *)
Lemma t50 : p78.
Proof.
 refine (rel_refl r46 i37 _) ; finalize.
Qed.
Lemma l68 : s1 -> p78 (* REL((1 + dl) * d2 + th * th * (Ph * (1 + et) * (1 + d2) - (1 + dl) * (1 + dl) * (1 + dl) * Pt * (1 + al)), (1 + dl) * d2 + th * th * (Ph * (1 + et) * (1 + d2) - (1 + dl) * (1 + dl) * (1 + dl) * Pt * (1 + al)), [0, 0]) *).
Proof.
 intros h0.
 apply t50.
Qed.
Lemma t51 : p77 -> p78 -> p76.
Proof.
 intros h0 h1.
 refine (rel_rewrite_1 r37 r46 r46 i37 h0 h1) ; finalize.
Qed.
Lemma l66 : s1 -> p76 (* REL((SN - ST) / th, (1 + dl) * d2 + th * th * (Ph * (1 + et) * (1 + d2) - (1 + dl) * (1 + dl) * (1 + dl) * Pt * (1 + al)), [0, 0]) *).
Proof.
 intros h0.
 assert (h1 := l67 h0).
 assert (h2 := l68 h0).
 apply t51. exact h1. exact h2.
Qed.
Lemma t52 : p54 -> p76 -> p53.
Proof.
 intros h0 h1.
 refine (bnd_of_bnd_rel_o r37 r46 i42 i37 i42 h0 h1 _) ; finalize.
Qed.
Lemma l48 : s1 -> p53 (* BND((SN - ST) / th, [-2.46522e-32, 2.4652e-32]) *).
Proof.
 intros h0.
 assert (h1 := l49 h0).
 assert (h2 := l66 h0).
 apply t52. exact h1. exact h2.
Qed.
Lemma t53 : p53 -> p17 -> p52.
Proof.
 intros h0 h1.
 refine (div_op r37 r38 i42 i11 i7 h0 h1 _) ; finalize.
Qed.
Lemma l47 : s1 -> p52 (* BND((SN - ST) / th / (ST / th), [-2.46522e-32, 2.4652e-32]) *).
Proof.
 intros h0.
 assert (h1 := l48 h0).
 assert (h2 := l17 h0).
 apply t53. exact h1. exact h2.
Qed.
Lemma t54 : p9 -> p52 -> p8.
Proof.
 intros h0 h1.
 refine (bnd_rewrite r20 r36 i7 h0 h1) ; finalize.
Qed.
Lemma l4 : p7 -> s1 -> p8 (* BND((SN - ST) / ST, [-2.46522e-32, 2.4652e-32]) *).
Proof.
 intros h0 h1.
 assert (h2 := l5 h0 h1).
 assert (h3 := l47 h1).
 apply t54. exact h2. exact h3.
Qed.
Lemma l2 : p7 -> s1 -> False.
Proof.
 intros h0 h1.
 assert (h2 := l3 h1).
 assert (h3 := l4 h0 h1).
 refine (simplify (Tatom false (Abnd 0%nat i6)) Tfalse (Abnd 0%nat i7) (List.cons r20 List.nil) h3 h2 _) ; finalize.
Qed.
Notation p79 := ((f13 <= _th)%R). (* BND(th, [0, inf]) *)
Notation p80 := (BND _ST i9). (* BND(ST, [2.34084e-97, 1]) *)
Notation p81 := (BND r71 i9). (* BND(ST / th * th, [2.34084e-97, 1]) *)
Definition i63 := makepairF f1 f23.
Notation p82 := (BND _th i63). (* BND(th, [4.68168e-97, 0.5]) *)
Definition i64 := makepairF f13 f23.
Notation p83 := (BND _th i64). (* BND(th, [0, 0.5]) *)
Lemma l78 : p79 -> s1 -> p79 (* BND(th, [0, inf]) *).
Proof.
 intros h0 h1.
 assert (h2 := h0).
 exact (h2).
Qed.
Lemma l77 : p79 -> s1 -> p83 (* BND(th, [0, 0.5]) *).
Proof.
 intros h0 h1.
 assert (h2 := l29 h1).
 assert (h3 := l78 h0 h1).
 apply intersect_bh with (1 := h2) (2 := h3). finalize.
Qed.
Lemma t55 : p83 -> p12 -> p82.
Proof.
 intros h0 h1.
 refine (bnd_of_bnd_abs_p _th i64 i8 i63 h0 h1 _) ; finalize.
Qed.
Lemma l76 : p79 -> s1 -> p82 (* BND(th, [4.68168e-97, 0.5]) *).
Proof.
 intros h0 h1.
 assert (h2 := l77 h0 h1).
 assert (h3 := l7 h1).
 apply t55. exact h2. refine (abs_subset _th i1 i8 h3 _) ; finalize.
Qed.
Lemma t56 : p51 -> p82 -> p81.
Proof.
 intros h0 h1.
 refine (mul_pp r38 _th i41 i63 i9 h0 h1 _) ; finalize.
Qed.
Lemma l75 : p79 -> s1 -> p81 (* BND(ST / th * th, [2.34084e-97, 1]) *).
Proof.
 intros h0 h1.
 assert (h2 := l17 h1).
 assert (h3 := l76 h0 h1).
 apply t56. refine (subset r38 i11 i41 h2 _) ; finalize. exact h3.
Qed.
Lemma t57 : p10 -> p81 -> p80.
Proof.
 intros h0 h1.
 refine (div_xilu _ST _ i9 h0 h1) ; finalize.
Qed.
Lemma l74 : p79 -> s1 -> p80 (* BND(ST, [2.34084e-97, 1]) *).
Proof.
 intros h0 h1.
 assert (h2 := l6 h1).
 assert (h3 := l75 h0 h1).
 apply t57. exact h2. exact h3.
Qed.
Lemma t58 : p80 -> p14.
Proof.
 intros h0.
 refine (abs_of_bnd_p _ST i9 i9 h0 _) ; finalize.
Qed.
Lemma l73 : p79 -> s1 -> p14 (* ABS(ST, [2.34084e-97, 1]) *).
Proof.
 intros h0 h1.
 assert (h2 := l74 h0 h1).
 apply t58. exact h2.
Qed.
Lemma t59 : p14 -> p13.
Proof.
 intros h0.
 refine (nzr_of_abs _ST i9 h0 _) ; finalize.
Qed.
Lemma l72 : p79 -> s1 -> p13 (* NZR(ST) *).
Proof.
 intros h0 h1.
 assert (h2 := l73 h0 h1).
 apply t59. exact h2.
Qed.
Lemma t60 : p10 -> p13 -> p9.
Proof.
 intros h0 h1.
 refine (b1 h0 h1) ; finalize.
Qed.
Lemma l71 : p79 -> s1 -> p9 (* EQL((SN - ST) / ST, (SN - ST) / th / (ST / th)) *).
Proof.
 intros h0 h1.
 assert (h2 := l6 h1).
 assert (h3 := l72 h0 h1).
 apply t60. exact h2. exact h3.
Qed.
Lemma t61 : p9 -> p52 -> p8.
Proof.
 intros h0 h1.
 refine (bnd_rewrite r20 r36 i7 h0 h1) ; finalize.
Qed.
Lemma l70 : p79 -> s1 -> p8 (* BND((SN - ST) / ST, [-2.46522e-32, 2.4652e-32]) *).
Proof.
 intros h0 h1.
 assert (h2 := l71 h0 h1).
 assert (h3 := l47 h1).
 apply t61. exact h2. exact h3.
Qed.
Lemma l69 : p79 -> s1 -> False.
Proof.
 intros h0 h1.
 assert (h2 := l3 h1).
 assert (h3 := l70 h0 h1).
 refine (simplify (Tatom false (Abnd 0%nat i6)) Tfalse (Abnd 0%nat i7) (List.cons r20 List.nil) h3 h2 _) ; finalize.
Qed.
Lemma l1 : s1 -> False.
Proof.
 intros h0.
 apply (union _th f13).
 intro h1. (* [-inf, 0] *)
 apply (l2 h1 h0).
 intro h1. (* [0, inf] *)
 apply (l69 h1 h0).
Qed.
End Generated_by_Gappa.
