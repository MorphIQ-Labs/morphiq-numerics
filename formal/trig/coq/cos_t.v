Require Import Gappa.Gappa_library.
Section Generated_by_Gappa.
Variable _th : R.
Notation r8 := (Float1 (1)).
Variable _dl : R.
Notation r7 := ((r8 + _dl)%R).
Notation _t := ((_th * r7)%R).
Notation r5 := ((_t * _t)%R).
Notation r10 := (Float1 (2)).
Notation r4 := ((r5 / r10)%R).
Notation r3 := ((- r4)%R).
Notation r14 := ((r5 * _t)%R).
Notation r13 := ((r14 * _t)%R).
Notation _c0 := (float2R (Float2 (6004799503160661) (-57))).
Notation _c1 := (float2R (Float2 (-6405119469336935) (-62))).
Notation _c2 := (float2R (Float2 (3659771605655355) (-67))).
Notation r20 := ((r5 * _c2)%R).
Notation r18 := ((_c1 + r20)%R).
Notation r17 := ((r5 * r18)%R).
Notation _Pt := ((_c0 + r17)%R).
Notation r12 := ((r13 * _Pt)%R).
Variable _al : R.
Notation r22 := ((r8 + _al)%R).
Notation r11 := ((r12 * r22)%R).
Notation _CT := ((r3 + r11)%R).
Notation r30 := ((_th * _th)%R).
Notation r29 := ((r30 / r10)%R).
Notation r28 := ((- r29)%R).
Notation r36 := ((r30 * _th)%R).
Notation r35 := ((r36 * _th)%R).
Notation r40 := ((r30 * _c2)%R).
Notation r39 := ((_c1 + r40)%R).
Notation r38 := ((r30 * r39)%R).
Notation _Ph := ((_c0 + r38)%R).
Notation r34 := ((r35 * _Ph)%R).
Variable _et : R.
Notation r41 := ((r8 + _et)%R).
Notation r33 := ((r34 * r41)%R).
Notation r44 := ((r30 * _dl)%R).
Variable _ec : R.
Notation r45 := ((r8 + _ec)%R).
Notation r43 := ((r44 * r45)%R).
Notation r32 := ((r33 - r43)%R).
Variable _eu : R.
Notation r47 := ((r8 + _eu)%R).
Notation _V := ((r32 * r47)%R).
Notation r27 := ((r28 + _V)%R).
Variable _d2 : R.
Notation r49 := ((r8 + _d2)%R).
Notation _CM := ((r27 * r49)%R).
Notation r25 := ((_CM - _CT)%R).
Notation r24 := ((r25 / _CT)%R).
Notation r52 := ((r25 / r30)%R).
Notation r53 := ((_CT / r30)%R).
Notation r51 := ((r52 / r53)%R).
Hypothesis a1 : (_th <> 0)%R -> (_CT <> 0)%R -> r24 = r51.
Lemma b1 : NZR _th -> NZR _CT -> r24 = r51.
 intros h0 h1.
 apply a1.
 exact h0.
 exact h1.
Qed.
Notation r57 := ((r7 * r7)%R).
Notation r56 := ((r57 / r10)%R).
Notation r55 := ((- r56)%R).
Notation r63 := ((r57 * r7)%R).
Notation r62 := ((r63 * r7)%R).
Notation r61 := ((r62 * _th)%R).
Notation r60 := ((r61 * _th)%R).
Notation r59 := ((r60 * _Pt)%R).
Notation r58 := ((r59 * r22)%R).
Notation r54 := ((r55 + r58)%R).
Hypothesis a2 : (_th <> 0)%R -> r53 = r54.
Lemma b2 : NZR _th -> r53 = r54.
 intros h0.
 apply a2.
 exact h0.
Qed.
Notation r73 := ((r41 * r47)%R).
Notation r72 := ((r73 * r49)%R).
Notation r71 := ((r72 - r8)%R).
Notation r70 := ((_Ph * r71)%R).
Notation r76 := ((r62 * r22)%R).
Notation r75 := ((r76 - r8)%R).
Notation r74 := ((_Pt * r75)%R).
Notation r69 := ((r70 - r74)%R).
Notation r79 := ((r57 - r8)%R).
Notation r78 := ((r30 * r79)%R).
Notation r83 := ((_c2 * _th)%R).
Notation r82 := ((r83 * _th)%R).
Notation r84 := ((r8 + r57)%R).
Notation r81 := ((r82 * r84)%R).
Notation r80 := ((_c1 + r81)%R).
Notation r77 := ((r78 * r80)%R).
Notation r68 := ((r69 - r77)%R).
Notation r67 := ((r30 * r68)%R).
Notation r88 := ((r45 * r47)%R).
Notation r87 := ((r88 * r49)%R).
Notation r86 := ((r8 - r87)%R).
Notation r85 := ((_dl * r86)%R).
Notation r66 := ((r67 + r85)%R).
Notation r90 := ((_dl * _dl)%R).
Notation r89 := ((r90 / r10)%R).
Notation r65 := ((r66 + r89)%R).
Notation r91 := ((_d2 / r10)%R).
Notation r64 := ((r65 - r91)%R).
Hypothesis a3 : (_th <> 0)%R -> r52 = r64.
Lemma b3 : NZR _th -> r52 = r64.
 intros h0.
 apply a3.
 exact h0.
Qed.
Notation r92 := ((Rabs _th)%R).
Definition f1 := Float2 (1) (-60).
Definition f2 := Float2 (80696341590167128190183336492762922277553037908230366465363237155637854447075094068654269148145619287504548485417148267) (-402).
Definition i1 := makepairF f1 f2.
Notation p1 := (BND r92 i1). (* BND(|th|, [8.67362e-19, 0.0078126]) *)
Definition f3 := Float2 (-1) (-53).
Definition f4 := Float2 (1) (-53).
Definition i2 := makepairF f3 f4.
Notation p2 := (BND _dl i2). (* BND(dl, [-1.11022e-16, 1.11022e-16]) *)
Definition s7 := (p1 /\ p2).
Definition f5 := Float2 (-1) (-50).
Definition f6 := Float2 (1) (-50).
Definition i3 := makepairF f5 f6.
Notation p3 := (BND _et i3). (* BND(et, [-8.88178e-16, 8.88178e-16]) *)
Definition s6 := (s7 /\ p3).
Definition f7 := Float2 (-259) (-62).
Definition f8 := Float2 (259) (-62).
Definition i4 := makepairF f7 f8.
Notation p4 := (BND _al i4). (* BND(al, [-5.61617e-17, 5.61617e-17]) *)
Definition s5 := (s6 /\ p4).
Notation p5 := (BND _ec i2). (* BND(ec, [-1.11022e-16, 1.11022e-16]) *)
Definition s4 := (s5 /\ p5).
Notation p6 := (BND _eu i2). (* BND(eu, [-1.11022e-16, 1.11022e-16]) *)
Definition s3 := (s4 /\ p6).
Definition f9 := Float2 (-1) (-105).
Definition f10 := Float2 (1) (-105).
Definition i5 := makepairF f9 f10.
Notation p7 := (BND _d2 i5). (* BND(d2, [-2.46519e-32, 2.46519e-32]) *)
Definition s2 := (s3 /\ p7).
Definition f11 := Float2 (-1) (-65).
Definition f12 := Float2 (1) (-65).
Definition i6 := makepairF f11 f12.
Notation p8 := (BND r24 i6). (* BND((CM - CT) / CT, [-2.71051e-20, 2.71051e-20]) *)
Definition s8 := (not p8).
Definition s1 := (s2 /\ s8).
Lemma l2 : s1 -> s8.
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj2 h1).
Qed.
Definition f13 := Float2 (-726595509319628054004667809189887662652733936944502257002954731451521745927878513547375949693219895115638239209928266501) (-465).
Definition f14 := Float2 (363297754659226888510198672647605251632753415137881305188697273784368424260386288170012483649792890599823433404360763043) (-464).
Definition i7 := makepairF f13 f14.
Notation p9 := (BND r24 i7). (* BND((CM - CT) / CT, [-7.62684e-21, 7.62684e-21]) *)
Notation p10 := (r24 = r51). (* EQL((CM - CT) / CT, (CM - CT) / (th * th) / (CT / (th * th))) *)
Notation p11 := (NZR _th). (* NZR(th) *)
Notation p12 := (ABS _th i1). (* ABS(th, [8.67362e-19, 0.0078126]) *)
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
Lemma l9 : s1 -> s6.
Proof.
 intros h0.
 assert (h1 := l10 h0).
 exact (proj1 h1).
Qed.
Lemma l8 : s1 -> s7.
Proof.
 intros h0.
 assert (h1 := l9 h0).
 exact (proj1 h1).
Qed.
Lemma l7 : s1 -> p1 (* BND(|th|, [8.67362e-19, 0.0078126]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 exact (proj1 h1).
Qed.
Lemma t1 : p1 -> p12.
Proof.
 intros h0.
 refine (abs_of_uabs _th i1 h0 _) ; finalize.
Qed.
Lemma l6 : s1 -> p12 (* ABS(th, [8.67362e-19, 0.0078126]) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 apply t1. exact h1.
Qed.
Definition f15 := Float2 (1) (0).
Definition i8 := makepairF f1 f15.
Notation p13 := (ABS _th i8). (* ABS(th, [8.67362e-19, 1]) *)
Lemma t2 : p13 -> p11.
Proof.
 intros h0.
 refine (nzr_of_abs _th i8 h0 _) ; finalize.
Qed.
Lemma l5 : s1 -> p11 (* NZR(th) *).
Proof.
 intros h0.
 assert (h1 := l6 h0).
 apply t2. refine (abs_subset _th i1 i8 h1 _) ; finalize.
Qed.
Notation p14 := (NZR _CT). (* NZR(CT) *)
Definition f16 := Float2 (1) (-122).
Definition i9 := makepairF f16 f15.
Notation p15 := (ABS _CT i9). (* ABS(CT, [1.88079e-37, 1]) *)
Definition f17 := Float2 (-1) (0).
Definition f18 := Float2 (-1) (-122).
Definition i10 := makepairF f17 f18.
Notation p16 := (BND _CT i10). (* BND(CT, [-1, -1.88079e-37]) *)
Notation p17 := (NZR r30). (* NZR(th * th) *)
Lemma t3 : p11 -> p11 -> p17.
Proof.
 intros h0 h1.
 refine (mul_nzr _th _th h0 h1) ; finalize.
Qed.
Lemma l17 : s1 -> p17 (* NZR(th * th) *).
Proof.
 intros h0.
 assert (h1 := l5 h0).
 apply t3. exact h1. exact h1.
Qed.
Notation r93 := ((r53 * r30)%R).
Notation p18 := (BND r93 i10). (* BND(CT / (th * th) * (th * th), [-1, -1.88079e-37]) *)
Definition f19 := Float2 (-2582236743748609946698221757686296605351238032724475423687386199226509031257616665492596557328090339981635114508210575801) (-401).
Definition i11 := makepairF f17 f19.
Notation p19 := (BND r53 i11). (* BND(CT / (th * th), [-1, -0.499997]) *)
Notation p20 := (BND r54 i11). (* BND(-((1 + dl) * (1 + dl) / 2) + (1 + dl) * (1 + dl) * (1 + dl) * (1 + dl) * th * th * Pt * (1 + al), [-1, -0.499997]) *)
Definition f20 := Float2 (-3) (-2).
Definition f21 := Float2 (-81129638414606663681390495662081) (-107).
Definition i12 := makepairF f20 f21.
Notation p21 := (BND r55 i12). (* BND(-((1 + dl) * (1 + dl) / 2), [-0.75, -0.5]) *)
Definition f22 := Float2 (81129638414606663681390495662081) (-107).
Definition f23 := Float2 (3) (-2).
Definition i13 := makepairF f22 f23.
Notation p22 := (BND r56 i13). (* BND((1 + dl) * (1 + dl) / 2, [0.5, 0.75]) *)
Definition f24 := Float2 (81129638414606663681390495662081) (-106).
Definition f25 := Float2 (81129638414606699710187514626049) (-106).
Definition i14 := makepairF f24 f25.
Notation p23 := (BND r57 i14). (* BND((1 + dl) * (1 + dl), [1, 1]) *)
Definition f26 := Float2 (9007199254740991) (-53).
Definition f27 := Float2 (9007199254740993) (-53).
Definition i15 := makepairF f26 f27.
Notation p24 := (ABS r7 i15). (* ABS(1 + dl, [1, 1]) *)
Definition i16 := makepairF f15 f15.
Notation p25 := (ABS r8 i16). (* ABS(1, [1, 1]) *)
Notation p26 := (BND r8 i16). (* BND(1, [1, 1]) *)
Lemma t4 : p26.
Proof.
 refine (constant1 _ i16 _) ; finalize.
Qed.
Lemma l26 : s1 -> p26 (* BND(1, [1, 1]) *).
Proof.
 intros h0.
 apply t4.
Qed.
Lemma t5 : p26 -> p25.
Proof.
 intros h0.
 refine (abs_of_bnd_p r8 i16 i16 h0 _) ; finalize.
Qed.
Lemma l25 : s1 -> p25 (* ABS(1, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l26 h0).
 apply t5. exact h1.
Qed.
Definition f28 := Float2 (0) (0).
Definition i17 := makepairF f28 f4.
Notation p27 := (ABS _dl i17). (* ABS(dl, [0, 1.11022e-16]) *)
Lemma l28 : s1 -> p2 (* BND(dl, [-1.11022e-16, 1.11022e-16]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 exact (proj2 h1).
Qed.
Lemma t6 : p2 -> p27.
Proof.
 intros h0.
 refine (abs_of_bnd_o _dl i2 i17 h0 _) ; finalize.
Qed.
Lemma l27 : s1 -> p27 (* ABS(dl, [0, 1.11022e-16]) *).
Proof.
 intros h0.
 assert (h1 := l28 h0).
 apply t6. exact h1.
Qed.
Lemma t7 : p25 -> p27 -> p24.
Proof.
 intros h0 h1.
 refine (add_aa_p r8 _dl i16 i17 i15 h0 h1 _) ; finalize.
Qed.
Lemma l24 : s1 -> p24 (* ABS(1 + dl, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l25 h0).
 assert (h2 := l27 h0).
 apply t7. exact h1. exact h2.
Qed.
Lemma t8 : p24 -> p23.
Proof.
 intros h0.
 refine (square r7 i15 i14 h0 _) ; finalize.
Qed.
Lemma l23 : s1 -> p23 (* BND((1 + dl) * (1 + dl), [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l24 h0).
 apply t8. exact h1.
Qed.
Definition f29 := Float2 (1) (1).
Definition i18 := makepairF f29 f29.
Notation p28 := (BND r10 i18). (* BND(2, [2, 2]) *)
Lemma t9 : p28.
Proof.
 refine (constant1 _ i18 _) ; finalize.
Qed.
Lemma l29 : s1 -> p28 (* BND(2, [2, 2]) *).
Proof.
 intros h0.
 apply t9.
Qed.
Definition f30 := Float2 (3) (-1).
Definition i19 := makepairF f24 f30.
Notation p29 := (BND r57 i19). (* BND((1 + dl) * (1 + dl), [1, 1.5]) *)
Lemma t10 : p29 -> p28 -> p22.
Proof.
 intros h0 h1.
 refine (div_pp r57 r10 i19 i18 i13 h0 h1 _) ; finalize.
Qed.
Lemma l22 : s1 -> p22 (* BND((1 + dl) * (1 + dl) / 2, [0.5, 0.75]) *).
Proof.
 intros h0.
 assert (h1 := l23 h0).
 assert (h2 := l29 h0).
 apply t10. refine (subset r57 i14 i19 h1 _) ; finalize. exact h2.
Qed.
Lemma t11 : p22 -> p21.
Proof.
 intros h0.
 refine (neg r56 i13 i12 h0 _) ; finalize.
Qed.
Lemma l21 : s1 -> p21 (* BND(-((1 + dl) * (1 + dl) / 2), [-0.75, -0.5]) *).
Proof.
 intros h0.
 assert (h1 := l22 h0).
 apply t11. exact h1.
Qed.
Definition f31 := Float2 (-1) (-2).
Definition f32 := Float2 (13134338298069583043416798869194960374160928110834465907261777624085555665712660245963525366636157438582069149394503) (-401).
Definition i20 := makepairF f31 f32.
Notation p30 := (BND r58 i20). (* BND((1 + dl) * (1 + dl) * (1 + dl) * (1 + dl) * th * th * Pt * (1 + al), [-0.25, 2.5432e-06]) *)
Definition f33 := Float2 (-1) (-3).
Definition f34 := Float2 (26268676596139164611540784824793743808494191992153823732044491516704352046199128033080035748852157291127600122077669) (-402).
Definition i21 := makepairF f33 f34.
Notation p31 := (BND r59 i21). (* BND((1 + dl) * (1 + dl) * (1 + dl) * (1 + dl) * th * th * Pt, [-0.125, 2.5432e-06]) *)
Definition f35 := Float2 (157612059576834996418471583988468461197026701575291119520632660275671539649162823754664954814028477089421494502236319) (-400).
Definition i22 := makepairF f17 f35.
Notation p32 := (BND r60 i22). (* BND((1 + dl) * (1 + dl) * (1 + dl) * (1 + dl) * th * th, [-1, 6.10367e-05]) *)
Definition f36 := Float2 (-315220084336590484478741840081383880680380694277695484539063220542120140160531592704943286353991623086067487340634677) (-394).
Definition f37 := Float2 (315220084336590484478741840081383880680380694277695484539063220542120140160531592704943286353991623086067487340634677) (-394).
Definition i23 := makepairF f36 f37.
Notation p33 := (BND r61 i23). (* BND((1 + dl) * (1 + dl) * (1 + dl) * (1 + dl) * th, [-0.0078126, 0.0078126]) *)
Definition f38 := Float2 (6582018229284821245616602068424052390391765670022426078541250561) (-212).
Definition f39 := Float2 (6582018229284827091623151392035725205131096535226562296309350401) (-212).
Definition i24 := makepairF f38 f39.
Notation p34 := (BND r62 i24). (* BND((1 + dl) * (1 + dl) * (1 + dl) * (1 + dl), [1, 1]) *)
Definition f40 := Float2 (730750818665451215712927172538123444058715062271) (-159).
Definition f41 := Float2 (730750818665451702490757660178213618792745926657) (-159).
Definition i25 := makepairF f40 f41.
Notation p35 := (BND r63 i25). (* BND((1 + dl) * (1 + dl) * (1 + dl), [1, 1]) *)
Notation p36 := (BND r7 i15). (* BND(1 + dl, [1, 1]) *)
Lemma t12 : p26 -> p2 -> p36.
Proof.
 intros h0 h1.
 refine (add r8 _dl i16 i2 i15 h0 h1 _) ; finalize.
Qed.
Lemma l36 : s1 -> p36 (* BND(1 + dl, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l26 h0).
 assert (h2 := l28 h0).
 apply t12. exact h1. exact h2.
Qed.
Lemma t13 : p23 -> p36 -> p35.
Proof.
 intros h0 h1.
 refine (mul_pp r57 r7 i14 i15 i25 h0 h1 _) ; finalize.
Qed.
Lemma l35 : s1 -> p35 (* BND((1 + dl) * (1 + dl) * (1 + dl), [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l23 h0).
 assert (h2 := l36 h0).
 apply t13. exact h1. exact h2.
Qed.
Lemma t14 : p35 -> p36 -> p34.
Proof.
 intros h0 h1.
 refine (mul_pp r63 r7 i25 i15 i24 h0 h1 _) ; finalize.
Qed.
Lemma l34 : s1 -> p34 (* BND((1 + dl) * (1 + dl) * (1 + dl) * (1 + dl), [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l35 h0).
 assert (h2 := l36 h0).
 apply t14. exact h1. exact h2.
Qed.
Definition f42 := Float2 (-9850627635518448265403239317964223910834111072782027156416410785600324029183971443927523089373244541931707578786273) (-389).
Definition f43 := Float2 (9850627635518448265403239317964223910834111072782027156416410785600324029183971443927523089373244541931707578786273) (-389).
Definition i26 := makepairF f42 f43.
Notation p37 := (BND _th i26). (* BND(th, [-0.0078126, 0.0078126]) *)
Definition i27 := makepairF f1 f43.
Notation p38 := (ABS _th i27). (* ABS(th, [8.67362e-19, 0.0078126]) *)
Lemma t15 : p38 -> p37.
Proof.
 intros h0.
 refine (bnd_of_abs _th i27 i26 h0 _) ; finalize.
Qed.
Lemma l37 : s1 -> p37 (* BND(th, [-0.0078126, 0.0078126]) *).
Proof.
 intros h0.
 assert (h1 := l6 h0).
 apply t15. refine (abs_subset _th i1 i27 h1 _) ; finalize.
Qed.
Definition f44 := Float2 (1) (-1).
Definition i28 := makepairF f44 f39.
Notation p39 := (BND r62 i28). (* BND((1 + dl) * (1 + dl) * (1 + dl) * (1 + dl), [0.5, 1]) *)
Lemma t16 : p39 -> p37 -> p33.
Proof.
 intros h0 h1.
 refine (mul_po r62 _th i28 i26 i23 h0 h1 _) ; finalize.
Qed.
Lemma l33 : s1 -> p33 (* BND((1 + dl) * (1 + dl) * (1 + dl) * (1 + dl) * th, [-0.0078126, 0.0078126]) *).
Proof.
 intros h0.
 assert (h1 := l34 h0).
 assert (h2 := l37 h0).
 apply t16. refine (subset r62 i24 i28 h1 _) ; finalize. exact h2.
Qed.
Lemma t17 : p33 -> p37 -> p32.
Proof.
 intros h0 h1.
 refine (mul_oo r61 _th i23 i26 i22 h0 h1 _) ; finalize.
Qed.
Lemma l32 : s1 -> p32 (* BND((1 + dl) * (1 + dl) * (1 + dl) * (1 + dl) * th * th, [-1, 6.10367e-05]) *).
Proof.
 intros h0.
 assert (h1 := l33 h0).
 assert (h2 := l37 h0).
 apply t17. exact h1. exact h2.
Qed.
Definition f45 := Float2 (1) (-5).
Definition f46 := Float2 (1721499918724605630874837115082361599059096184859427744406349660441581748593690555760277414613896631500247244006821374179) (-404).
Definition i29 := makepairF f45 f46.
Notation p40 := (BND _Pt i29). (* BND(Pt, [0.03125, 0.0416667]) *)
Definition f47 := Float2 (5) (-7).
Definition f48 := Float2 (6004799503160661) (-57).
Definition i30 := makepairF f47 f48.
Notation p41 := (BND _c0 i30). (* BND(c0, [0.0390625, 0.0416667]) *)
Lemma t18 : p41.
Proof.
 refine (constant2 _ i30 _) ; finalize.
Qed.
Lemma l39 : s1 -> p41 (* BND(c0, [0.0390625, 0.0416667]) *).
Proof.
 intros h0.
 apply t18.
Qed.
Definition f49 := Float2 (-1) (-7).
Definition f50 := Float2 (-43170372773098730957215361907136510351335266204366317219328253206248491053106681629) (-404).
Definition i31 := makepairF f49 f50.
Notation p42 := (BND r17 i31). (* BND(t * t * (c1 + t * t * c2), [-0.0078125, -1.04488e-39]) *)
Definition f51 := Float2 (81129638414606663681390495662081) (-226).
Definition f52 := Float2 (115795053533772072330482628063367985562307868981689050815102314663647768412537) (-270).
Definition i32 := makepairF f51 f52.
Notation p43 := (BND r5 i32). (* BND(t * t, [7.52316e-37, 6.10367e-05]) *)
Definition f53 := Float2 (9007199254740991) (-113).
Definition f54 := Float2 (926348571008467567412330489959602751987221937352006715734396103311155770602707) (-266).
Definition i33 := makepairF f53 f54.
Notation p44 := (ABS _t i33). (* ABS(t, [8.67362e-19, 0.0078126]) *)
Definition f55 := Float2 (231587142752116866141744813434592038116981013042888568477354578129976861855991) (-264).
Definition i34 := makepairF f1 f55.
Notation p45 := (ABS _th i34). (* ABS(th, [8.67362e-19, 0.0078126]) *)
Lemma t19 : p45 -> p24 -> p44.
Proof.
 intros h0 h1.
 refine (mul_aa _th r7 i34 i15 i33 h0 h1 _) ; finalize.
Qed.
Lemma l42 : s1 -> p44 (* ABS(t, [8.67362e-19, 0.0078126]) *).
Proof.
 intros h0.
 assert (h1 := l6 h0).
 assert (h2 := l24 h0).
 apply t19. refine (abs_subset _th i1 i34 h1 _) ; finalize. exact h2.
Qed.
Lemma t20 : p44 -> p43.
Proof.
 intros h0.
 refine (square _t i33 i32 h0 _) ; finalize.
Qed.
Lemma l41 : s1 -> p43 (* BND(t * t, [7.52316e-37, 6.10367e-05]) *).
Proof.
 intros h0.
 assert (h1 := l42 h0).
 apply t20. exact h1.
Qed.
Definition f56 := Float2 (-21585186386549370271481864388087035900658367113936383655252272508044588760946553827) (-283).
Definition i35 := makepairF f17 f56.
Notation p46 := (BND r18 i35). (* BND(c1 + t * t * c2, [-1, -0.00138889]) *)
Definition f57 := Float2 (-6405119469336935) (-62).
Definition i36 := makepairF f57 f57.
Notation p47 := (BND _c1 i36). (* BND(c1, [-0.00138889, -0.00138889]) *)
Lemma t21 : p47.
Proof.
 refine (constant2 _ i36 _) ; finalize.
Qed.
Lemma l44 : s1 -> p47 (* BND(c1, [-0.00138889, -0.00138889]) *).
Proof.
 intros h0.
 apply t21.
Qed.
Definition f58 := Float2 (1) (-136).
Definition f59 := Float2 (23524707126645383668302563251141997610141488780656889112042250659802256395293) (-283).
Definition i37 := makepairF f58 f59.
Notation p48 := (BND r20 i37). (* BND(t * t * c2, [1.14794e-41, 1.51368e-09]) *)
Definition f60 := Float2 (3) (-17).
Definition f61 := Float2 (3659771605655355) (-67).
Definition i38 := makepairF f60 f61.
Notation p49 := (BND _c2 i38). (* BND(c2, [2.28882e-05, 2.47996e-05]) *)
Lemma t22 : p49.
Proof.
 refine (constant2 _ i38 _) ; finalize.
Qed.
Lemma l46 : s1 -> p49 (* BND(c2, [2.28882e-05, 2.47996e-05]) *).
Proof.
 intros h0.
 apply t22.
Qed.
Definition f62 := Float2 (3) (-122).
Definition i39 := makepairF f62 f52.
Notation p50 := (BND r5 i39). (* BND(t * t, [5.64237e-37, 6.10367e-05]) *)
Lemma t23 : p50 -> p49 -> p48.
Proof.
 intros h0 h1.
 refine (mul_pp r5 _c2 i39 i38 i37 h0 h1 _) ; finalize.
Qed.
Lemma l45 : s1 -> p48 (* BND(t * t * c2, [1.14794e-41, 1.51368e-09]) *).
Proof.
 intros h0.
 assert (h1 := l41 h0).
 assert (h2 := l46 h0).
 apply t23. refine (subset r5 i32 i39 h1 _) ; finalize. exact h2.
Qed.
Definition i40 := makepairF f17 f57.
Notation p51 := (BND _c1 i40). (* BND(c1, [-1, -0.00138889]) *)
Lemma t24 : p51 -> p48 -> p46.
Proof.
 intros h0 h1.
 refine (add _c1 r20 i40 i37 i35 h0 h1 _) ; finalize.
Qed.
Lemma l43 : s1 -> p46 (* BND(c1 + t * t * c2, [-1, -0.00138889]) *).
Proof.
 intros h0.
 assert (h1 := l44 h0).
 assert (h2 := l45 h0).
 apply t24. refine (subset _c1 i36 i40 h1 _) ; finalize. exact h2.
Qed.
Definition f63 := Float2 (1) (-7).
Definition i41 := makepairF f51 f63.
Notation p52 := (BND r5 i41). (* BND(t * t, [7.52316e-37, 0.0078125]) *)
Lemma t25 : p52 -> p46 -> p42.
Proof.
 intros h0 h1.
 refine (mul_pn r5 r18 i41 i35 i31 h0 h1 _) ; finalize.
Qed.
Lemma l40 : s1 -> p42 (* BND(t * t * (c1 + t * t * c2), [-0.0078125, -1.04488e-39]) *).
Proof.
 intros h0.
 assert (h1 := l41 h0).
 assert (h2 := l43 h0).
 apply t25. refine (subset r5 i32 i41 h1 _) ; finalize. exact h2.
Qed.
Lemma t26 : p41 -> p42 -> p40.
Proof.
 intros h0 h1.
 refine (add _c0 r17 i30 i31 i29 h0 h1 _) ; finalize.
Qed.
Lemma l38 : s1 -> p40 (* BND(Pt, [0.03125, 0.0416667]) *).
Proof.
 intros h0.
 assert (h1 := l39 h0).
 assert (h2 := l40 h0).
 apply t26. exact h1. exact h2.
Qed.
Definition f64 := Float2 (420288066094874421600302030049404687270287154506696226661706460068745544090256483339911478177220857299865049806352875) (-392).
Definition i42 := makepairF f45 f64.
Notation p53 := (BND _Pt i42). (* BND(Pt, [0.03125, 0.0416667]) *)
Lemma t27 : p32 -> p53 -> p31.
Proof.
 intros h0 h1.
 refine (mul_op r60 _Pt i22 i42 i21 h0 h1 _) ; finalize.
Qed.
Lemma l31 : s1 -> p31 (* BND((1 + dl) * (1 + dl) * (1 + dl) * (1 + dl) * th * th * Pt, [-0.125, 2.5432e-06]) *).
Proof.
 intros h0.
 assert (h1 := l32 h0).
 assert (h2 := l38 h0).
 apply t27. exact h1. refine (subset _Pt i29 i42 h2 _) ; finalize.
Qed.
Definition f65 := Float2 (4611686018427387645) (-62).
Definition f66 := Float2 (4611686018427388163) (-62).
Definition i43 := makepairF f65 f66.
Notation p54 := (BND r22 i43). (* BND(1 + al, [1, 1]) *)
Lemma l48 : s1 -> p4 (* BND(al, [-5.61617e-17, 5.61617e-17]) *).
Proof.
 intros h0.
 assert (h1 := l10 h0).
 exact (proj2 h1).
Qed.
Lemma t28 : p26 -> p4 -> p54.
Proof.
 intros h0 h1.
 refine (add r8 _al i16 i4 i43 h0 h1 _) ; finalize.
Qed.
Lemma l47 : s1 -> p54 (* BND(1 + al, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l26 h0).
 assert (h2 := l48 h0).
 apply t28. exact h1. exact h2.
Qed.
Definition i44 := makepairF f44 f66.
Notation p55 := (BND r22 i44). (* BND(1 + al, [0.5, 1]) *)
Lemma t29 : p31 -> p55 -> p30.
Proof.
 intros h0 h1.
 refine (mul_op r59 r22 i21 i44 i20 h0 h1 _) ; finalize.
Qed.
Lemma l30 : s1 -> p30 (* BND((1 + dl) * (1 + dl) * (1 + dl) * (1 + dl) * th * th * Pt * (1 + al), [-0.25, 2.5432e-06]) *).
Proof.
 intros h0.
 assert (h1 := l31 h0).
 assert (h2 := l47 h0).
 apply t29. exact h1. refine (subset r22 i43 i44 h2 _) ; finalize.
Qed.
Lemma t30 : p21 -> p30 -> p20.
Proof.
 intros h0 h1.
 refine (add r55 r58 i12 i20 i11 h0 h1 _) ; finalize.
Qed.
Lemma l20 : s1 -> p20 (* BND(-((1 + dl) * (1 + dl) / 2) + (1 + dl) * (1 + dl) * (1 + dl) * (1 + dl) * th * th * Pt * (1 + al), [-1, -0.499997]) *).
Proof.
 intros h0.
 assert (h1 := l21 h0).
 assert (h2 := l30 h0).
 apply t30. exact h1. exact h2.
Qed.
Definition i45 := makepairF f28 f28.
Notation p56 := (REL r53 r54 i45). (* REL(CT / (th * th), -((1 + dl) * (1 + dl) / 2) + (1 + dl) * (1 + dl) * (1 + dl) * (1 + dl) * th * th * Pt * (1 + al), [0, 0]) *)
Notation p57 := (r53 = r54). (* EQL(CT / (th * th), -((1 + dl) * (1 + dl) / 2) + (1 + dl) * (1 + dl) * (1 + dl) * (1 + dl) * th * th * Pt * (1 + al)) *)
Lemma t31 : p11 -> p57.
Proof.
 intros h0.
 refine (b2 h0) ; finalize.
Qed.
Lemma l50 : s1 -> p57 (* EQL(CT / (th * th), -((1 + dl) * (1 + dl) / 2) + (1 + dl) * (1 + dl) * (1 + dl) * (1 + dl) * th * th * Pt * (1 + al)) *).
Proof.
 intros h0.
 assert (h1 := l5 h0).
 apply t31. exact h1.
Qed.
Notation p58 := (REL r54 r54 i45). (* REL(-((1 + dl) * (1 + dl) / 2) + (1 + dl) * (1 + dl) * (1 + dl) * (1 + dl) * th * th * Pt * (1 + al), -((1 + dl) * (1 + dl) / 2) + (1 + dl) * (1 + dl) * (1 + dl) * (1 + dl) * th * th * Pt * (1 + al), [0, 0]) *)
Lemma t32 : p58.
Proof.
 refine (rel_refl r54 i45 _) ; finalize.
Qed.
Lemma l51 : s1 -> p58 (* REL(-((1 + dl) * (1 + dl) / 2) + (1 + dl) * (1 + dl) * (1 + dl) * (1 + dl) * th * th * Pt * (1 + al), -((1 + dl) * (1 + dl) / 2) + (1 + dl) * (1 + dl) * (1 + dl) * (1 + dl) * th * th * Pt * (1 + al), [0, 0]) *).
Proof.
 intros h0.
 apply t32.
Qed.
Lemma t33 : p57 -> p58 -> p56.
Proof.
 intros h0 h1.
 refine (rel_rewrite_1 r53 r54 r54 i45 h0 h1) ; finalize.
Qed.
Lemma l49 : s1 -> p56 (* REL(CT / (th * th), -((1 + dl) * (1 + dl) / 2) + (1 + dl) * (1 + dl) * (1 + dl) * (1 + dl) * th * th * Pt * (1 + al), [0, 0]) *).
Proof.
 intros h0.
 assert (h1 := l50 h0).
 assert (h2 := l51 h0).
 apply t33. exact h1. exact h2.
Qed.
Lemma t34 : p20 -> p56 -> p19.
Proof.
 intros h0 h1.
 refine (bnd_of_bnd_rel_n r53 r54 i11 i45 i11 h0 h1 _) ; finalize.
Qed.
Lemma l19 : s1 -> p19 (* BND(CT / (th * th), [-1, -0.499997]) *).
Proof.
 intros h0.
 assert (h1 := l20 h0).
 assert (h2 := l49 h0).
 apply t34. exact h1. exact h2.
Qed.
Definition f67 := Float2 (1) (-120).
Definition f68 := Float2 (1291157992053431717270786733431520474287331049393849469024863900881175145785792266077733566764651448822902856698204185705) (-413).
Definition i46 := makepairF f67 f68.
Notation p59 := (BND r30 i46). (* BND(th * th, [7.52316e-37, 6.10367e-05]) *)
Lemma t35 : p12 -> p59.
Proof.
 intros h0.
 refine (square _th i1 i46 h0 _) ; finalize.
Qed.
Lemma l52 : s1 -> p59 (* BND(th * th, [7.52316e-37, 6.10367e-05]) *).
Proof.
 intros h0.
 assert (h1 := l6 h0).
 apply t35. exact h1.
Qed.
Definition i47 := makepairF f17 f31.
Notation p60 := (BND r53 i47). (* BND(CT / (th * th), [-1, -0.25]) *)
Definition i48 := makepairF f67 f15.
Notation p61 := (BND r30 i48). (* BND(th * th, [7.52316e-37, 1]) *)
Lemma t36 : p60 -> p61 -> p18.
Proof.
 intros h0 h1.
 refine (mul_np r53 r30 i47 i48 i10 h0 h1 _) ; finalize.
Qed.
Lemma l18 : s1 -> p18 (* BND(CT / (th * th) * (th * th), [-1, -1.88079e-37]) *).
Proof.
 intros h0.
 assert (h1 := l19 h0).
 assert (h2 := l52 h0).
 apply t36. refine (subset r53 i11 i47 h1 _) ; finalize. refine (subset r30 i46 i48 h2 _) ; finalize.
Qed.
Lemma t37 : p17 -> p18 -> p16.
Proof.
 intros h0 h1.
 refine (div_xilu _CT _ i10 h0 h1) ; finalize.
Qed.
Lemma l16 : s1 -> p16 (* BND(CT, [-1, -1.88079e-37]) *).
Proof.
 intros h0.
 assert (h1 := l17 h0).
 assert (h2 := l18 h0).
 apply t37. exact h1. exact h2.
Qed.
Lemma t38 : p16 -> p15.
Proof.
 intros h0.
 refine (abs_of_bnd_n _CT i10 i9 h0 _) ; finalize.
Qed.
Lemma l15 : s1 -> p15 (* ABS(CT, [1.88079e-37, 1]) *).
Proof.
 intros h0.
 assert (h1 := l16 h0).
 apply t38. exact h1.
Qed.
Lemma t39 : p15 -> p14.
Proof.
 intros h0.
 refine (nzr_of_abs _CT i9 h0 _) ; finalize.
Qed.
Lemma l14 : s1 -> p14 (* NZR(CT) *).
Proof.
 intros h0.
 assert (h1 := l15 h0).
 apply t39. exact h1.
Qed.
Lemma t40 : p11 -> p14 -> p10.
Proof.
 intros h0 h1.
 refine (b1 h0 h1) ; finalize.
Qed.
Lemma l4 : s1 -> p10 (* EQL((CM - CT) / CT, (CM - CT) / (th * th) / (CT / (th * th))) *).
Proof.
 intros h0.
 assert (h1 := l5 h0).
 assert (h2 := l14 h0).
 apply t40. exact h1. exact h2.
Qed.
Notation p62 := (BND r51 i7). (* BND((CM - CT) / (th * th) / (CT / (th * th)), [-7.62684e-21, 7.62684e-21]) *)
Definition f69 := Float2 (-90823976695996758737116923352991673104172175590356065085609427099386425771121000110776660910346894887933356341188288479) (-463).
Definition f70 := Float2 (363295906784574170454185673759880987986782281237856163509651623871150953027355929150878359673953373677135191271550343143) (-465).
Definition i49 := makepairF f69 f70.
Notation p63 := (BND r52 i49). (* BND((CM - CT) / (th * th), [-3.8134e-21, 3.8134e-21]) *)
Notation p64 := (BND r64 i49). (* BND(th * th * (Ph * ((1 + et) * (1 + eu) * (1 + d2) - 1) - Pt * ((1 + dl) * (1 + dl) * (1 + dl) * (1 + dl) * (1 + al) - 1) - th * th * ((1 + dl) * (1 + dl) - 1) * (c1 + c2 * th * th * (1 + (1 + dl) * (1 + dl)))) + dl * (1 - (1 + ec) * (1 + eu) * (1 + d2)) + dl * dl / 2 - d2 / 2, [-3.8134e-21, 3.8134e-21]) *)
Definition f71 := Float2 (-90823976695703190914270194199505488029573508461934104766995887115548014399679473982637334854913932513135260253309296607) (-463).
Definition f72 := Float2 (363295906783399899162798757145936247688387612724168322235197463935797307541589824638321055452221524177942806920034375655) (-465).
Definition i50 := makepairF f71 f72.
Notation p65 := (BND r65 i50). (* BND(th * th * (Ph * ((1 + et) * (1 + eu) * (1 + d2) - 1) - Pt * ((1 + dl) * (1 + dl) * (1 + dl) * (1 + dl) * (1 + al) - 1) - th * th * ((1 + dl) * (1 + dl) - 1) * (c1 + c2 * th * th * (1 + (1 + dl) * (1 + dl)))) + dl * (1 - (1 + ec) * (1 + eu) * (1 + d2)) + dl * dl / 2, [-3.8134e-21, 3.8134e-21]) *)
Definition f73 := Float2 (363295906782812763517105298838963877539190278467324401597970383968120484798706772382042403341355599428346614744276391911) (-465).
Definition i51 := makepairF f71 f73.
Notation p66 := (BND r66 i51). (* BND(th * th * (Ph * ((1 + et) * (1 + eu) * (1 + d2) - 1) - Pt * ((1 + dl) * (1 + dl) * (1 + dl) * (1 + dl) * (1 + al) - 1) - th * th * ((1 + dl) * (1 + dl) - 1) * (c1 + c2 * th * th * (1 + (1 + dl) * (1 + dl)))) + dl * (1 - (1 + ec) * (1 + eu) * (1 + d2)), [-3.8134e-21, 3.8134e-21]) *)
Definition f74 := Float2 (-90823976695116055268576735794755391016320827590193636421593424002005453179705229056029687388665939341204013795189383135) (-463).
Definition f75 := Float2 (363295906780464220934331465219963489486179554980362528216360531513950239918809792675611813476363626740621628911796738023) (-465).
Definition i52 := makepairF f74 f75.
Notation p67 := (BND r67 i52). (* BND(th * th * (Ph * ((1 + et) * (1 + eu) * (1 + d2) - 1) - Pt * ((1 + dl) * (1 + dl) * (1 + dl) * (1 + dl) * (1 + al) - 1) - th * th * ((1 + dl) * (1 + dl) - 1) * (c1 + c2 * th * th * (1 + (1 + dl) * (1 + dl)))), [-3.8134e-21, 3.8134e-21]) *)
Definition f76 := Float2 (-726573213167629595585582462506261137188428772228027883817081586242845161511479387313881480925909469612309027749123976399) (-452).
Definition f77 := Float2 (45410825822976849706602417074688584144501367511301922644773653227601438048226969864201446384967233205694606343631190991) (-448).
Definition i53 := makepairF f76 f77.
Notation p68 := (BND r68 i53). (* BND(Ph * ((1 + et) * (1 + eu) * (1 + d2) - 1) - Pt * ((1 + dl) * (1 + dl) * (1 + dl) * (1 + dl) * (1 + al) - 1) - th * th * ((1 + dl) * (1 + dl) - 1) * (c1 + c2 * th * th * (1 + (1 + dl) * (1 + dl))), [-6.24772e-17, 6.24772e-17]) *)
Definition f78 := Float2 (-363286497130757084213405736224484482143804902571021925925621838343120448730970326292183773062522361286034938820690237857) (-451).
Definition f79 := Float2 (1453145988523028336293686759353534650049256655267748089717426647451519065611601272778699722615978601215879673613169485603) (-453).
Definition i54 := makepairF f78 f79.
Notation p69 := (BND r69 i54). (* BND(Ph * ((1 + et) * (1 + eu) * (1 + d2) - 1) - Pt * ((1 + dl) * (1 + dl) * (1 + dl) * (1 + dl) * (1 + al) - 1), [-6.24772e-17, 6.24772e-17]) *)
Definition f80 := Float2 (-121042963035323824461908015943009221087891529291400739854535419103318799108051690991731250193391602838889998510725978913) (-450).
Definition f81 := Float2 (968343704282590786820148793383403536406525440238414978367852319543809681426678083107645778359443410891684874831309998525) (-453).
Definition i55 := makepairF f80 f81.
Notation p70 := (BND r70 i55). (* BND(Ph * ((1 + et) * (1 + eu) * (1 + d2) - 1), [-4.16334e-17, 4.16334e-17]) *)
Definition f82 := Float2 (26898436230071962982419329923161899985298377888428558356571731976624130641564178434460545937777529712728884182786811067) (-398).
Definition i56 := makepairF f45 f82.
Notation p71 := (BND _Ph i56). (* BND(Ph, [0.03125, 0.0416667]) *)
Definition f83 := Float2 (-674537074579667820983971497574592154451850033737012372116609110810111677524564805) (-398).
Definition i57 := makepairF f49 f83.
Notation p72 := (BND r38 i57). (* BND(th * th * (c1 + th * th * c2), [-0.0078125, -1.04488e-39]) *)
Definition f84 := Float2 (-674537074579667820983971497574592154451850033737012372116609110810111677524564805) (-278).
Definition i58 := makepairF f17 f84.
Notation p73 := (BND r39 i58). (* BND(c1 + th * th * c2, [-1, -0.00138889]) *)
Definition f85 := Float2 (735147097707668076399008229315631149255495024012637809156386614840075527355) (-278).
Definition i59 := makepairF f58 f85.
Notation p74 := (BND r40 i59). (* BND(th * th * c2, [1.14794e-41, 1.51368e-09]) *)
Definition f86 := Float2 (14474381691721505827351964235512750055941806899990969840689443016786057847489) (-267).
Definition i60 := makepairF f67 f86.
Notation p75 := (BND r30 i60). (* BND(th * th, [7.52316e-37, 6.10367e-05]) *)
Definition f87 := Float2 (1) (-16).
Definition i61 := makepairF f87 f61.
Notation p76 := (BND _c2 i61). (* BND(c2, [1.52588e-05, 2.47996e-05]) *)
Lemma t41 : p75 -> p76 -> p74.
Proof.
 intros h0 h1.
 refine (mul_pp r30 _c2 i60 i61 i59 h0 h1 _) ; finalize.
Qed.
Lemma l65 : s1 -> p74 (* BND(th * th * c2, [1.14794e-41, 1.51368e-09]) *).
Proof.
 intros h0.
 assert (h1 := l52 h0).
 assert (h2 := l46 h0).
 apply t41. refine (subset r30 i46 i60 h1 _) ; finalize. refine (subset _c2 i38 i61 h2 _) ; finalize.
Qed.
Lemma t42 : p51 -> p74 -> p73.
Proof.
 intros h0 h1.
 refine (add _c1 r40 i40 i59 i58 h0 h1 _) ; finalize.
Qed.
Lemma l64 : s1 -> p73 (* BND(c1 + th * th * c2, [-1, -0.00138889]) *).
Proof.
 intros h0.
 assert (h1 := l44 h0).
 assert (h2 := l65 h0).
 apply t42. refine (subset _c1 i36 i40 h1 _) ; finalize. exact h2.
Qed.
Definition i62 := makepairF f67 f63.
Notation p77 := (BND r30 i62). (* BND(th * th, [7.52316e-37, 0.0078125]) *)
Lemma t43 : p77 -> p73 -> p72.
Proof.
 intros h0 h1.
 refine (mul_pn r30 r39 i62 i58 i57 h0 h1 _) ; finalize.
Qed.
Lemma l63 : s1 -> p72 (* BND(th * th * (c1 + th * th * c2), [-0.0078125, -1.04488e-39]) *).
Proof.
 intros h0.
 assert (h1 := l52 h0).
 assert (h2 := l64 h0).
 apply t43. refine (subset r30 i46 i62 h1 _) ; finalize. exact h2.
Qed.
Lemma t44 : p41 -> p72 -> p71.
Proof.
 intros h0 h1.
 refine (add _c0 r38 i30 i57 i56 h0 h1 _) ; finalize.
Qed.
Lemma l62 : s1 -> p71 (* BND(Ph, [0.03125, 0.0416667]) *).
Proof.
 intros h0.
 assert (h1 := l39 h0).
 assert (h2 := l63 h0).
 apply t44. exact h1. exact h2.
Qed.
Definition f88 := Float2 (-411047335499316415321171953723938830258192515073) (-208).
Definition f89 := Float2 (411047335499316496450810368330640792245520826369) (-208).
Definition i63 := makepairF f88 f89.
Notation p78 := (BND r71 i63). (* BND((1 + et) * (1 + eu) * (1 + d2) - 1, [-9.99201e-16, 9.99201e-16]) *)
Definition f90 := Float2 (411376139330301099491406796322922305073730242469564707644637183) (-208).
Definition f91 := Float2 (411376139330301921586077794955834077056052297049187211357978625) (-208).
Definition i64 := makepairF f90 f91.
Notation p79 := (BND r72 i64). (* BND((1 + et) * (1 + eu) * (1 + d2), [1, 1]) *)
Definition f92 := Float2 (10141204801825825078874464059393) (-103).
Definition f93 := Float2 (10141204801825845345072787226625) (-103).
Definition i65 := makepairF f92 f93.
Notation p80 := (BND r73 i65). (* BND((1 + et) * (1 + eu), [1, 1]) *)
Definition f94 := Float2 (1125899906842623) (-50).
Definition f95 := Float2 (1125899906842625) (-50).
Definition i66 := makepairF f94 f95.
Notation p81 := (BND r41 i66). (* BND(1 + et, [1, 1]) *)
Lemma l70 : s1 -> p3 (* BND(et, [-8.88178e-16, 8.88178e-16]) *).
Proof.
 intros h0.
 assert (h1 := l9 h0).
 exact (proj2 h1).
Qed.
Lemma t45 : p26 -> p3 -> p81.
Proof.
 intros h0 h1.
 refine (add r8 _et i16 i3 i66 h0 h1 _) ; finalize.
Qed.
Lemma l69 : s1 -> p81 (* BND(1 + et, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l26 h0).
 assert (h2 := l70 h0).
 apply t45. exact h1. exact h2.
Qed.
Notation p82 := (BND r47 i15). (* BND(1 + eu, [1, 1]) *)
Lemma l72 : s1 -> p6 (* BND(eu, [-1.11022e-16, 1.11022e-16]) *).
Proof.
 intros h0.
 assert (h1 := l12 h0).
 exact (proj2 h1).
Qed.
Lemma t46 : p26 -> p6 -> p82.
Proof.
 intros h0 h1.
 refine (add r8 _eu i16 i2 i15 h0 h1 _) ; finalize.
Qed.
Lemma l71 : s1 -> p82 (* BND(1 + eu, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l26 h0).
 assert (h2 := l72 h0).
 apply t46. exact h1. exact h2.
Qed.
Lemma t47 : p81 -> p82 -> p80.
Proof.
 intros h0 h1.
 refine (mul_pp r41 r47 i66 i15 i65 h0 h1 _) ; finalize.
Qed.
Lemma l68 : s1 -> p80 (* BND((1 + et) * (1 + eu), [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l69 h0).
 assert (h2 := l71 h0).
 apply t47. exact h1. exact h2.
Qed.
Definition f96 := Float2 (40564819207303340847894502572031) (-105).
Definition f97 := Float2 (40564819207303340847894502572033) (-105).
Definition i67 := makepairF f96 f97.
Notation p83 := (BND r49 i67). (* BND(1 + d2, [1, 1]) *)
Lemma l74 : s1 -> p7 (* BND(d2, [-2.46519e-32, 2.46519e-32]) *).
Proof.
 intros h0.
 assert (h1 := l13 h0).
 exact (proj2 h1).
Qed.
Lemma t48 : p26 -> p7 -> p83.
Proof.
 intros h0 h1.
 refine (add r8 _d2 i16 i5 i67 h0 h1 _) ; finalize.
Qed.
Lemma l73 : s1 -> p83 (* BND(1 + d2, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l26 h0).
 assert (h2 := l74 h0).
 apply t48. exact h1. exact h2.
Qed.
Lemma t49 : p80 -> p83 -> p79.
Proof.
 intros h0 h1.
 refine (mul_pp r73 r49 i65 i67 i64 h0 h1 _) ; finalize.
Qed.
Lemma l67 : s1 -> p79 (* BND((1 + et) * (1 + eu) * (1 + d2), [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l68 h0).
 assert (h2 := l73 h0).
 apply t49. exact h1. exact h2.
Qed.
Lemma t50 : p79 -> p26 -> p78.
Proof.
 intros h0 h1.
 refine (sub r72 r8 i64 i16 i63 h0 h1 _) ; finalize.
Qed.
Lemma l66 : s1 -> p78 (* BND((1 + et) * (1 + eu) * (1 + d2) - 1, [-9.99201e-16, 9.99201e-16]) *).
Proof.
 intros h0.
 assert (h1 := l67 h0).
 assert (h2 := l26 h0).
 apply t50. exact h1. exact h2.
Qed.
Lemma t51 : p71 -> p78 -> p70.
Proof.
 intros h0 h1.
 refine (mul_po _Ph r71 i56 i63 i55 h0 h1 _) ; finalize.
Qed.
Lemma l61 : s1 -> p70 (* BND(Ph * ((1 + et) * (1 + eu) * (1 + d2) - 1), [-4.16334e-17, 4.16334e-17]) *).
Proof.
 intros h0.
 assert (h1 := l62 h0).
 assert (h2 := l66 h0).
 apply t51. exact h1. exact h2.
Qed.
Definition f98 := Float2 (-242401142120218774736768982985065556821365607514666555674787163953854692092461594835526972128267595162097399390929743539) (-452).
Definition f99 := Float2 (121200571060109435289589704338466039968021843988220446216551000136482850514866944308721272675739155608254941799238280031) (-451).
Definition i68 := makepairF f98 f99.
Notation p84 := (BND r74 i68). (* BND(Pt * ((1 + dl) * (1 + dl) * (1 + dl) * (1 + dl) * (1 + al) - 1), [-2.08438e-17, 2.08438e-17]) *)
Definition f100 := Float2 (-15184716054960086355081692538964928698569609582074877693245710663939) (-274).
Definition f101 := Float2 (15184716054960092358930418694314116679306902380593408728709275320579) (-274).
Definition i69 := makepairF f100 f101.
Notation p85 := (BND r75 i69). (* BND((1 + dl) * (1 + dl) * (1 + dl) * (1 + dl) * (1 + al) - 1, [-5.00251e-16, 5.00251e-16]) *)
Definition f102 := Float2 (30354201441027001548400537334031127834595067895260981449949986827292686210620718845) (-274).
Definition f103 := Float2 (30354201441027031917832647254209841846706301174306359326461949495579108165606703363) (-274).
Definition i70 := makepairF f102 f103.
Notation p86 := (BND r76 i70). (* BND((1 + dl) * (1 + dl) * (1 + dl) * (1 + dl) * (1 + al), [1, 1]) *)
Lemma t52 : p34 -> p54 -> p86.
Proof.
 intros h0 h1.
 refine (mul_pp r62 r22 i24 i43 i70 h0 h1 _) ; finalize.
Qed.
Lemma l77 : s1 -> p86 (* BND((1 + dl) * (1 + dl) * (1 + dl) * (1 + dl) * (1 + al), [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l34 h0).
 assert (h2 := l47 h0).
 apply t52. exact h1. exact h2.
Qed.
Lemma t53 : p86 -> p26 -> p85.
Proof.
 intros h0 h1.
 refine (sub r76 r8 i70 i16 i69 h0 h1 _) ; finalize.
Qed.
Lemma l76 : s1 -> p85 (* BND((1 + dl) * (1 + dl) * (1 + dl) * (1 + dl) * (1 + al) - 1, [-5.00251e-16, 5.00251e-16]) *).
Proof.
 intros h0.
 assert (h1 := l77 h0).
 assert (h2 := l26 h0).
 apply t53. exact h1. exact h2.
Qed.
Lemma t54 : p40 -> p85 -> p84.
Proof.
 intros h0 h1.
 refine (mul_po _Pt r75 i29 i69 i68 h0 h1 _) ; finalize.
Qed.
Lemma l75 : s1 -> p84 (* BND(Pt * ((1 + dl) * (1 + dl) * (1 + dl) * (1 + dl) * (1 + al) - 1), [-2.08438e-17, 2.08438e-17]) *).
Proof.
 intros h0.
 assert (h1 := l38 h0).
 assert (h2 := l76 h0).
 apply t54. exact h1. exact h2.
Qed.
Lemma t55 : p70 -> p84 -> p69.
Proof.
 intros h0 h1.
 refine (sub r70 r74 i55 i68 i54 h0 h1 _) ; finalize.
Qed.
Lemma l60 : s1 -> p69 (* BND(Ph * ((1 + et) * (1 + eu) * (1 + d2) - 1) - Pt * ((1 + dl) * (1 + dl) * (1 + dl) * (1 + dl) * (1 + al) - 1), [-6.24772e-17, 6.24772e-17]) *).
Proof.
 intros h0.
 assert (h1 := l61 h0).
 assert (h2 := l75 h0).
 apply t55. exact h1. exact h2.
Qed.
Definition f104 := Float2 (-437812230854317590587036500042574787105093913434915330255831726951931661762875746561702972861366347729383028626109) (-453).
Definition f105 := Float2 (218906115427158770990057292172900818967085984031965837909556604264049538734729513934800864747040239150107743500685) (-452).
Definition i71 := makepairF f104 f105.
Notation p87 := (BND r77 i71). (* BND(th * th * ((1 + dl) * (1 + dl) - 1) * (c1 + c2 * th * th * (1 + (1 + dl) * (1 + dl))), [-1.88235e-23, 1.88235e-23]) *)
Definition f106 := Float2 (-2462688430888045588678589197361527949086615133361793357148905945782933539477446767098291956019564215117120437327945) (-446).
Definition f107 := Float2 (615672107722011465522982260588054744340867435335021506508275128011564079297081433070677681203707511153450428748425) (-444).
Definition i72 := makepairF f106 f107.
Notation p88 := (BND r78 i72). (* BND(th * th * ((1 + dl) * (1 + dl) - 1), [-1.35529e-20, 1.35529e-20]) *)
Definition f108 := Float2 (-18014398509481983) (-106).
Definition f109 := Float2 (18014398509481985) (-106).
Definition i73 := makepairF f108 f109.
Notation p89 := (BND r79 i73). (* BND((1 + dl) * (1 + dl) - 1, [-2.22045e-16, 2.22045e-16]) *)
Lemma t56 : p23 -> p26 -> p89.
Proof.
 intros h0 h1.
 refine (sub r57 r8 i14 i16 i73 h0 h1 _) ; finalize.
Qed.
Lemma l80 : s1 -> p89 (* BND((1 + dl) * (1 + dl) - 1, [-2.22045e-16, 2.22045e-16]) *).
Proof.
 intros h0.
 assert (h1 := l23 h0).
 assert (h2 := l26 h0).
 apply t56. exact h1. exact h2.
Qed.
Definition f110 := Float2 (4925376861776091450770518239713746926450084874701879383182006457829189856665772499381002680834394259730922152321641) (-395).
Definition i74 := makepairF f67 f110.
Notation p90 := (BND r30 i74). (* BND(th * th, [7.52316e-37, 6.10367e-05]) *)
Lemma t57 : p90 -> p89 -> p88.
Proof.
 intros h0 h1.
 refine (mul_po r30 r79 i74 i73 i72 h0 h1 _) ; finalize.
Qed.
Lemma l79 : s1 -> p88 (* BND(th * th * ((1 + dl) * (1 + dl) - 1), [-1.35529e-20, 1.35529e-20]) *).
Proof.
 intros h0.
 assert (h1 := l52 h0).
 assert (h2 := l80 h0).
 apply t57. refine (subset r30 i46 i74 h1 _) ; finalize. exact h2.
Qed.
Definition f111 := Float2 (-28019265476889439416766199731671940635539107653080457936794353771540045308345698108610810860501474343819389167225245) (-393).
Definition f112 := Float2 (-1) (-10).
Definition i75 := makepairF f111 f112.
Notation p91 := (BND r80 i75). (* BND(c1 + c2 * th * th * (1 + (1 + dl) * (1 + dl)), [-0.00138889, -0.000976562]) *)
Definition f113 := Float2 (-61073631455816341732239881169839363460978270387579391088538117158968710494804062780429662034499344264974846365) (-393).
Definition f114 := Float2 (1) (-12).
Definition i76 := makepairF f113 f114.
Notation p92 := (BND r81 i76). (* BND(c2 * th * th * (1 + (1 + dl) * (1 + dl)), [-3.02737e-09, 0.000244141]) *)
Definition f115 := Float2 (-61073631455816334951704697197987593995213235858088525450731781105673854521648828656215975770228639897659160287) (-394).
Definition f116 := Float2 (1) (-14).
Definition i77 := makepairF f115 f116.
Notation p93 := (BND r82 i77). (* BND(c2 * th * th, [-1.51368e-09, 6.10352e-05]) *)
Definition f117 := Float2 (-3908662382293752076882516524459692931624122306152146881366752496331173650362800390152828493089921402456234818559) (-393).
Definition f118 := Float2 (3908662382293752076882516524459692931624122306152146881366752496331173650362800390152828493089921402456234818559) (-393).
Definition i78 := makepairF f117 f118.
Notation p94 := (BND r83 i78). (* BND(c2 * th, [-1.93749e-07, 1.93749e-07]) *)
Definition f119 := Float2 (-9619753550310984634182850896449437412923936594513698394937901157812816434749972113210471766966059122980183182409) (-379).
Definition f120 := Float2 (9619753550310984634182850896449437412923936594513698394937901157812816434749972113210471766966059122980183182409) (-379).
Definition i79 := makepairF f119 f120.
Notation p95 := (BND _th i79). (* BND(th, [-0.0078126, 0.0078126]) *)
Lemma t58 : p76 -> p95 -> p94.
Proof.
 intros h0 h1.
 refine (mul_po _c2 _th i61 i79 i78 h0 h1 _) ; finalize.
Qed.
Lemma l84 : s1 -> p94 (* BND(c2 * th, [-1.93749e-07, 1.93749e-07]) *).
Proof.
 intros h0.
 assert (h1 := l46 h0).
 assert (h2 := l37 h0).
 apply t58. refine (subset _c2 i38 i61 h1 _) ; finalize. refine (subset _th i26 i79 h2 _) ; finalize.
Qed.
Definition f121 := Float2 (-601234596894436539636428181028089838307746037157106149683618822363301027171873257075654485435378695186261448901) (-375).
Definition f122 := Float2 (601234596894436539636428181028089838307746037157106149683618822363301027171873257075654485435378695186261448901) (-375).
Definition i80 := makepairF f121 f122.
Notation p96 := (BND _th i80). (* BND(th, [-0.0078126, 0.0078126]) *)
Lemma t59 : p94 -> p96 -> p93.
Proof.
 intros h0 h1.
 refine (mul_oo r83 _th i78 i80 i77 h0 h1 _) ; finalize.
Qed.
Lemma l83 : s1 -> p93 (* BND(c2 * th * th, [-1.51368e-09, 6.10352e-05]) *).
Proof.
 intros h0.
 assert (h1 := l84 h0).
 assert (h2 := l37 h0).
 apply t59. exact h1. refine (subset _th i26 i80 h2 _) ; finalize.
Qed.
Definition f123 := Float2 (162259276829213381405976519770113) (-106).
Definition i81 := makepairF f15 f123.
Notation p97 := (BND r84 i81). (* BND(1 + (1 + dl) * (1 + dl), [1, 2]) *)
Definition i82 := makepairF f44 f25.
Notation p98 := (BND r57 i82). (* BND((1 + dl) * (1 + dl), [0.5, 1]) *)
Lemma t60 : p26 -> p98 -> p97.
Proof.
 intros h0 h1.
 refine (add r8 r57 i16 i82 i81 h0 h1 _) ; finalize.
Qed.
Lemma l85 : s1 -> p97 (* BND(1 + (1 + dl) * (1 + dl), [1, 2]) *).
Proof.
 intros h0.
 assert (h1 := l26 h0).
 assert (h2 := l23 h0).
 apply t60. exact h1. refine (subset r57 i14 i82 h2 _) ; finalize.
Qed.
Lemma t61 : p93 -> p97 -> p92.
Proof.
 intros h0 h1.
 refine (mul_op r82 r84 i77 i81 i76 h0 h1 _) ; finalize.
Qed.
Lemma l82 : s1 -> p92 (* BND(c2 * th * th * (1 + (1 + dl) * (1 + dl)), [-3.02737e-09, 0.000244141]) *).
Proof.
 intros h0.
 assert (h1 := l83 h0).
 assert (h2 := l85 h0).
 apply t61. exact h1. exact h2.
Qed.
Definition f124 := Float2 (-5) (-12).
Definition i83 := makepairF f57 f124.
Notation p99 := (BND _c1 i83). (* BND(c1, [-0.00138889, -0.0012207]) *)
Lemma t62 : p99 -> p92 -> p91.
Proof.
 intros h0 h1.
 refine (add _c1 r81 i83 i76 i75 h0 h1 _) ; finalize.
Qed.
Lemma l81 : s1 -> p91 (* BND(c1 + c2 * th * th * (1 + (1 + dl) * (1 + dl)), [-0.00138889, -0.000976562]) *).
Proof.
 intros h0.
 assert (h1 := l44 h0).
 assert (h2 := l82 h0).
 apply t62. refine (subset _c1 i36 i83 h1 _) ; finalize. exact h2.
Qed.
Lemma t63 : p88 -> p91 -> p87.
Proof.
 intros h0 h1.
 refine (mul_on r78 r80 i72 i75 i71 h0 h1 _) ; finalize.
Qed.
Lemma l78 : s1 -> p87 (* BND(th * th * ((1 + dl) * (1 + dl) - 1) * (c1 + c2 * th * th * (1 + (1 + dl) * (1 + dl))), [-1.88235e-23, 1.88235e-23]) *).
Proof.
 intros h0.
 assert (h1 := l79 h0).
 assert (h2 := l81 h0).
 apply t63. exact h1. exact h2.
Qed.
Lemma t64 : p69 -> p87 -> p68.
Proof.
 intros h0 h1.
 refine (sub r69 r77 i54 i71 i53 h0 h1 _) ; finalize.
Qed.
Lemma l59 : s1 -> p68 (* BND(Ph * ((1 + et) * (1 + eu) * (1 + d2) - 1) - Pt * ((1 + dl) * (1 + dl) * (1 + dl) * (1 + dl) * (1 + al) - 1) - th * th * ((1 + dl) * (1 + dl) - 1) * (c1 + c2 * th * th * (1 + (1 + dl) * (1 + dl))), [-6.24772e-17, 6.24772e-17]) *).
Proof.
 intros h0.
 assert (h1 := l60 h0).
 assert (h2 := l78 h0).
 apply t64. exact h1. exact h2.
Qed.
Lemma t65 : p59 -> p68 -> p67.
Proof.
 intros h0 h1.
 refine (mul_po r30 r68 i46 i53 i52 h0 h1 _) ; finalize.
Qed.
Lemma l58 : s1 -> p67 (* BND(th * th * (Ph * ((1 + et) * (1 + eu) * (1 + d2) - 1) - Pt * ((1 + dl) * (1 + dl) * (1 + dl) * (1 + dl) * (1 + al) - 1) - th * th * ((1 + dl) * (1 + dl) - 1) * (c1 + c2 * th * th * (1 + (1 + dl) * (1 + dl)))), [-3.8134e-21, 3.8134e-21]) *).
Proof.
 intros h0.
 assert (h1 := l52 h0).
 assert (h2 := l59 h0).
 apply t65. exact h1. exact h2.
Qed.
Definition f125 := Float2 (-730750818665451580796300038268182067909983469569) (-264).
Definition f126 := Float2 (730750818665451580796300038268182067909983469569) (-264).
Definition i84 := makepairF f125 f126.
Notation p100 := (BND r85 i84). (* BND(dl * (1 - (1 + ec) * (1 + eu) * (1 + d2)), [-2.46519e-32, 2.46519e-32]) *)
Definition f127 := Float2 (-730750818665451580796300038268182067909983469569) (-211).
Definition f128 := Float2 (9007199254740993) (-105).
Definition i85 := makepairF f127 f128.
Notation p101 := (BND r86 i85). (* BND(1 - (1 + ec) * (1 + eu) * (1 + d2), [-2.22045e-16, 2.22045e-16]) *)
Definition f129 := Float2 (40564819207303331840695247831039) (-105).
Definition f130 := Float2 (3291009114642412815060757030566281806265509999449227636680687617) (-211).
Definition i86 := makepairF f129 f130.
Notation p102 := (BND r87 i86). (* BND((1 + ec) * (1 + eu) * (1 + d2), [1, 1]) *)
Definition f131 := Float2 (4503599627370495) (-52).
Definition i87 := makepairF f131 f25.
Notation p103 := (BND r88 i87). (* BND((1 + ec) * (1 + eu), [1, 1]) *)
Notation p104 := (BND r45 i15). (* BND(1 + ec, [1, 1]) *)
Lemma l91 : s1 -> p5 (* BND(ec, [-1.11022e-16, 1.11022e-16]) *).
Proof.
 intros h0.
 assert (h1 := l11 h0).
 exact (proj2 h1).
Qed.
Lemma t66 : p26 -> p5 -> p104.
Proof.
 intros h0 h1.
 refine (add r8 _ec i16 i2 i15 h0 h1 _) ; finalize.
Qed.
Lemma l90 : s1 -> p104 (* BND(1 + ec, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l26 h0).
 assert (h2 := l91 h0).
 apply t66. exact h1. exact h2.
Qed.
Lemma t67 : p104 -> p82 -> p103.
Proof.
 intros h0 h1.
 refine (mul_pp r45 r47 i15 i15 i87 h0 h1 _) ; finalize.
Qed.
Lemma l89 : s1 -> p103 (* BND((1 + ec) * (1 + eu), [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l90 h0).
 assert (h2 := l71 h0).
 apply t67. exact h1. exact h2.
Qed.
Lemma t68 : p103 -> p83 -> p102.
Proof.
 intros h0 h1.
 refine (mul_pp r88 r49 i87 i67 i86 h0 h1 _) ; finalize.
Qed.
Lemma l88 : s1 -> p102 (* BND((1 + ec) * (1 + eu) * (1 + d2), [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l89 h0).
 assert (h2 := l73 h0).
 apply t68. exact h1. exact h2.
Qed.
Lemma t69 : p26 -> p102 -> p101.
Proof.
 intros h0 h1.
 refine (sub r8 r87 i16 i86 i85 h0 h1 _) ; finalize.
Qed.
Lemma l87 : s1 -> p101 (* BND(1 - (1 + ec) * (1 + eu) * (1 + d2), [-2.22045e-16, 2.22045e-16]) *).
Proof.
 intros h0.
 assert (h1 := l26 h0).
 assert (h2 := l88 h0).
 apply t69. exact h1. exact h2.
Qed.
Lemma t70 : p2 -> p101 -> p100.
Proof.
 intros h0 h1.
 refine (mul_oo _dl r86 i2 i85 i84 h0 h1 _) ; finalize.
Qed.
Lemma l86 : s1 -> p100 (* BND(dl * (1 - (1 + ec) * (1 + eu) * (1 + d2)), [-2.46519e-32, 2.46519e-32]) *).
Proof.
 intros h0.
 assert (h1 := l28 h0).
 assert (h2 := l87 h0).
 apply t70. exact h1. exact h2.
Qed.
Lemma t71 : p67 -> p100 -> p66.
Proof.
 intros h0 h1.
 refine (add r67 r85 i52 i84 i51 h0 h1 _) ; finalize.
Qed.
Lemma l57 : s1 -> p66 (* BND(th * th * (Ph * ((1 + et) * (1 + eu) * (1 + d2) - 1) - Pt * ((1 + dl) * (1 + dl) * (1 + dl) * (1 + dl) * (1 + al) - 1) - th * th * ((1 + dl) * (1 + dl) - 1) * (c1 + c2 * th * th * (1 + (1 + dl) * (1 + dl)))) + dl * (1 - (1 + ec) * (1 + eu) * (1 + d2)), [-3.8134e-21, 3.8134e-21]) *).
Proof.
 intros h0.
 assert (h1 := l58 h0).
 assert (h2 := l86 h0).
 apply t71. exact h1. exact h2.
Qed.
Definition f132 := Float2 (1) (-107).
Definition i88 := makepairF f28 f132.
Notation p105 := (BND r89 i88). (* BND(dl * dl / 2, [0, 6.16298e-33]) *)
Definition f133 := Float2 (1) (-106).
Definition i89 := makepairF f28 f133.
Notation p106 := (BND r90 i89). (* BND(dl * dl, [0, 1.2326e-32]) *)
Lemma t72 : p27 -> p106.
Proof.
 intros h0.
 refine (square _dl i17 i89 h0 _) ; finalize.
Qed.
Lemma l93 : s1 -> p106 (* BND(dl * dl, [0, 1.2326e-32]) *).
Proof.
 intros h0.
 assert (h1 := l27 h0).
 apply t72. exact h1.
Qed.
Lemma t73 : p106 -> p28 -> p105.
Proof.
 intros h0 h1.
 refine (div_pp r90 r10 i89 i18 i88 h0 h1 _) ; finalize.
Qed.
Lemma l92 : s1 -> p105 (* BND(dl * dl / 2, [0, 6.16298e-33]) *).
Proof.
 intros h0.
 assert (h1 := l93 h0).
 assert (h2 := l29 h0).
 apply t73. exact h1. exact h2.
Qed.
Lemma t74 : p66 -> p105 -> p65.
Proof.
 intros h0 h1.
 refine (add r66 r89 i51 i88 i50 h0 h1 _) ; finalize.
Qed.
Lemma l56 : s1 -> p65 (* BND(th * th * (Ph * ((1 + et) * (1 + eu) * (1 + d2) - 1) - Pt * ((1 + dl) * (1 + dl) * (1 + dl) * (1 + dl) * (1 + al) - 1) - th * th * ((1 + dl) * (1 + dl) - 1) * (c1 + c2 * th * th * (1 + (1 + dl) * (1 + dl)))) + dl * (1 - (1 + ec) * (1 + eu) * (1 + d2)) + dl * dl / 2, [-3.8134e-21, 3.8134e-21]) *).
Proof.
 intros h0.
 assert (h1 := l57 h0).
 assert (h2 := l92 h0).
 apply t74. exact h1. exact h2.
Qed.
Definition f134 := Float2 (-1) (-106).
Definition i90 := makepairF f134 f133.
Notation p107 := (BND r91 i90). (* BND(d2 / 2, [-1.2326e-32, 1.2326e-32]) *)
Lemma t75 : p7 -> p28 -> p107.
Proof.
 intros h0 h1.
 refine (div_op _d2 r10 i5 i18 i90 h0 h1 _) ; finalize.
Qed.
Lemma l94 : s1 -> p107 (* BND(d2 / 2, [-1.2326e-32, 1.2326e-32]) *).
Proof.
 intros h0.
 assert (h1 := l74 h0).
 assert (h2 := l29 h0).
 apply t75. exact h1. exact h2.
Qed.
Lemma t76 : p65 -> p107 -> p64.
Proof.
 intros h0 h1.
 refine (sub r65 r91 i50 i90 i49 h0 h1 _) ; finalize.
Qed.
Lemma l55 : s1 -> p64 (* BND(th * th * (Ph * ((1 + et) * (1 + eu) * (1 + d2) - 1) - Pt * ((1 + dl) * (1 + dl) * (1 + dl) * (1 + dl) * (1 + al) - 1) - th * th * ((1 + dl) * (1 + dl) - 1) * (c1 + c2 * th * th * (1 + (1 + dl) * (1 + dl)))) + dl * (1 - (1 + ec) * (1 + eu) * (1 + d2)) + dl * dl / 2 - d2 / 2, [-3.8134e-21, 3.8134e-21]) *).
Proof.
 intros h0.
 assert (h1 := l56 h0).
 assert (h2 := l94 h0).
 apply t76. exact h1. exact h2.
Qed.
Notation p108 := (REL r52 r64 i45). (* REL((CM - CT) / (th * th), th * th * (Ph * ((1 + et) * (1 + eu) * (1 + d2) - 1) - Pt * ((1 + dl) * (1 + dl) * (1 + dl) * (1 + dl) * (1 + al) - 1) - th * th * ((1 + dl) * (1 + dl) - 1) * (c1 + c2 * th * th * (1 + (1 + dl) * (1 + dl)))) + dl * (1 - (1 + ec) * (1 + eu) * (1 + d2)) + dl * dl / 2 - d2 / 2, [0, 0]) *)
Notation p109 := (r52 = r64). (* EQL((CM - CT) / (th * th), th * th * (Ph * ((1 + et) * (1 + eu) * (1 + d2) - 1) - Pt * ((1 + dl) * (1 + dl) * (1 + dl) * (1 + dl) * (1 + al) - 1) - th * th * ((1 + dl) * (1 + dl) - 1) * (c1 + c2 * th * th * (1 + (1 + dl) * (1 + dl)))) + dl * (1 - (1 + ec) * (1 + eu) * (1 + d2)) + dl * dl / 2 - d2 / 2) *)
Lemma t77 : p11 -> p109.
Proof.
 intros h0.
 refine (b3 h0) ; finalize.
Qed.
Lemma l96 : s1 -> p109 (* EQL((CM - CT) / (th * th), th * th * (Ph * ((1 + et) * (1 + eu) * (1 + d2) - 1) - Pt * ((1 + dl) * (1 + dl) * (1 + dl) * (1 + dl) * (1 + al) - 1) - th * th * ((1 + dl) * (1 + dl) - 1) * (c1 + c2 * th * th * (1 + (1 + dl) * (1 + dl)))) + dl * (1 - (1 + ec) * (1 + eu) * (1 + d2)) + dl * dl / 2 - d2 / 2) *).
Proof.
 intros h0.
 assert (h1 := l5 h0).
 apply t77. exact h1.
Qed.
Notation p110 := (REL r64 r64 i45). (* REL(th * th * (Ph * ((1 + et) * (1 + eu) * (1 + d2) - 1) - Pt * ((1 + dl) * (1 + dl) * (1 + dl) * (1 + dl) * (1 + al) - 1) - th * th * ((1 + dl) * (1 + dl) - 1) * (c1 + c2 * th * th * (1 + (1 + dl) * (1 + dl)))) + dl * (1 - (1 + ec) * (1 + eu) * (1 + d2)) + dl * dl / 2 - d2 / 2, th * th * (Ph * ((1 + et) * (1 + eu) * (1 + d2) - 1) - Pt * ((1 + dl) * (1 + dl) * (1 + dl) * (1 + dl) * (1 + al) - 1) - th * th * ((1 + dl) * (1 + dl) - 1) * (c1 + c2 * th * th * (1 + (1 + dl) * (1 + dl)))) + dl * (1 - (1 + ec) * (1 + eu) * (1 + d2)) + dl * dl / 2 - d2 / 2, [0, 0]) *)
Lemma t78 : p110.
Proof.
 refine (rel_refl r64 i45 _) ; finalize.
Qed.
Lemma l97 : s1 -> p110 (* REL(th * th * (Ph * ((1 + et) * (1 + eu) * (1 + d2) - 1) - Pt * ((1 + dl) * (1 + dl) * (1 + dl) * (1 + dl) * (1 + al) - 1) - th * th * ((1 + dl) * (1 + dl) - 1) * (c1 + c2 * th * th * (1 + (1 + dl) * (1 + dl)))) + dl * (1 - (1 + ec) * (1 + eu) * (1 + d2)) + dl * dl / 2 - d2 / 2, th * th * (Ph * ((1 + et) * (1 + eu) * (1 + d2) - 1) - Pt * ((1 + dl) * (1 + dl) * (1 + dl) * (1 + dl) * (1 + al) - 1) - th * th * ((1 + dl) * (1 + dl) - 1) * (c1 + c2 * th * th * (1 + (1 + dl) * (1 + dl)))) + dl * (1 - (1 + ec) * (1 + eu) * (1 + d2)) + dl * dl / 2 - d2 / 2, [0, 0]) *).
Proof.
 intros h0.
 apply t78.
Qed.
Lemma t79 : p109 -> p110 -> p108.
Proof.
 intros h0 h1.
 refine (rel_rewrite_1 r52 r64 r64 i45 h0 h1) ; finalize.
Qed.
Lemma l95 : s1 -> p108 (* REL((CM - CT) / (th * th), th * th * (Ph * ((1 + et) * (1 + eu) * (1 + d2) - 1) - Pt * ((1 + dl) * (1 + dl) * (1 + dl) * (1 + dl) * (1 + al) - 1) - th * th * ((1 + dl) * (1 + dl) - 1) * (c1 + c2 * th * th * (1 + (1 + dl) * (1 + dl)))) + dl * (1 - (1 + ec) * (1 + eu) * (1 + d2)) + dl * dl / 2 - d2 / 2, [0, 0]) *).
Proof.
 intros h0.
 assert (h1 := l96 h0).
 assert (h2 := l97 h0).
 apply t79. exact h1. exact h2.
Qed.
Lemma t80 : p64 -> p108 -> p63.
Proof.
 intros h0 h1.
 refine (bnd_of_bnd_rel_o r52 r64 i49 i45 i49 h0 h1 _) ; finalize.
Qed.
Lemma l54 : s1 -> p63 (* BND((CM - CT) / (th * th), [-3.8134e-21, 3.8134e-21]) *).
Proof.
 intros h0.
 assert (h1 := l55 h0).
 assert (h2 := l95 h0).
 apply t80. exact h1. exact h2.
Qed.
Lemma t81 : p63 -> p19 -> p62.
Proof.
 intros h0 h1.
 refine (div_on r52 r53 i49 i11 i7 h0 h1 _) ; finalize.
Qed.
Lemma l53 : s1 -> p62 (* BND((CM - CT) / (th * th) / (CT / (th * th)), [-7.62684e-21, 7.62684e-21]) *).
Proof.
 intros h0.
 assert (h1 := l54 h0).
 assert (h2 := l19 h0).
 apply t81. exact h1. exact h2.
Qed.
Lemma t82 : p10 -> p62 -> p9.
Proof.
 intros h0 h1.
 refine (bnd_rewrite r24 r51 i7 h0 h1) ; finalize.
Qed.
Lemma l3 : s1 -> p9 (* BND((CM - CT) / CT, [-7.62684e-21, 7.62684e-21]) *).
Proof.
 intros h0.
 assert (h1 := l4 h0).
 assert (h2 := l53 h0).
 apply t82. exact h1. exact h2.
Qed.
Lemma l1 : s1 -> False.
Proof.
 intros h0.
 assert (h1 := l2 h0).
 assert (h2 := l3 h0).
 refine (simplify (Tatom false (Abnd 0%nat i6)) Tfalse (Abnd 0%nat i7) (List.cons r24 List.nil) h2 h1 _) ; finalize.
Qed.
End Generated_by_Gappa.
