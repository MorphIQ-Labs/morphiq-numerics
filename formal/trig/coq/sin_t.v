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
Definition f1 := Float2 (1) (-60).
Definition f2 := Float2 (80696341590167128190183336492762922277553037908230366465363237155637854447075094068654269148145619287504548485417148267) (-402).
Definition i1 := makepairF f1 f2.
Notation p1 := (BND r70 i1). (* BND(|th|, [8.67362e-19, 0.0078126]) *)
Definition f3 := Float2 (-1) (-53).
Definition f4 := Float2 (1) (-53).
Definition i2 := makepairF f3 f4.
Notation p2 := (BND _dl i2). (* BND(dl, [-1.11022e-16, 1.11022e-16]) *)
Definition s5 := (p1 /\ p2).
Definition f5 := Float2 (-1) (-50).
Definition f6 := Float2 (1) (-50).
Definition i3 := makepairF f5 f6.
Notation p3 := (BND _et i3). (* BND(et, [-8.88178e-16, 8.88178e-16]) *)
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
Definition f14 := Float2 (-2476014438984709939022875276571624357319528108097248468427494373477362672147753014579357000552518084006068610807094265659) (-466).
Definition f15 := Float2 (2476014438984709939022875276571624357319528108097248468427494373477362672147753014579357000552518084006068610807094265659) (-466).
Definition i7 := makepairF f14 f15.
Notation p8 := (BND r20 i7). (* BND((SN - ST) / ST, [-1.2995e-20, 1.2995e-20]) *)
Notation p9 := (r20 = r36). (* EQL((SN - ST) / ST, (SN - ST) / th / (ST / th)) *)
Notation p10 := (NZR _th). (* NZR(th) *)
Notation p11 := (ABS _th i1). (* ABS(th, [8.67362e-19, 0.0078126]) *)
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
Lemma l8 : s1 -> p1 (* BND(|th|, [8.67362e-19, 0.0078126]) *).
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
Lemma l7 : s1 -> p11 (* ABS(th, [8.67362e-19, 0.0078126]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 apply t1. exact h1.
Qed.
Definition f16 := Float2 (1) (0).
Definition i8 := makepairF f1 f16.
Notation p12 := (ABS _th i8). (* ABS(th, [8.67362e-19, 1]) *)
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
Definition f17 := Float2 (1) (-61).
Definition i9 := makepairF f17 f16.
Notation p14 := (ABS _ST i9). (* ABS(ST, [4.33681e-19, 1]) *)
Definition f18 := Float2 (-1) (0).
Definition f19 := Float2 (-1) (-61).
Definition i10 := makepairF f18 f19.
Notation p15 := (BND _ST i10). (* BND(ST, [-1, -4.33681e-19]) *)
Notation r71 := ((r38 * _th)%R).
Notation p16 := (BND r71 i10). (* BND(ST / th * th, [-1, -4.33681e-19]) *)
Definition f20 := Float2 (645555902352578040951355437151170275350142668156022654786418273455036815833677835466839130610815108735387036187972722681) (-398).
Definition f21 := Float2 (1) (1).
Definition i11 := makepairF f20 f21.
Notation p17 := (BND r38 i11). (* BND(ST / th, [0.99999, 2]) *)
Notation p18 := (BND r39 i11). (* BND(1 + dl + (1 + dl) * (1 + dl) * (1 + dl) * th * th * Pt * (1 + al), [0.99999, 2]) *)
Definition f22 := Float2 (9007199254740991) (-53).
Definition f23 := Float2 (9007199254740993) (-53).
Definition i12 := makepairF f22 f23.
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
Definition f24 := Float2 (-6567169149034790792606159847955394130801861066323528590654171339972870881232349232329944069096935508972113786445831) (-398).
Definition f25 := Float2 (1) (-1).
Definition i14 := makepairF f24 f25.
Notation p21 := (BND r40 i14). (* BND((1 + dl) * (1 + dl) * (1 + dl) * th * th * Pt * (1 + al), [-1.01728e-05, 0.5]) *)
Definition f26 := Float2 (-6567169149034790423782956619556390843446169026138938224850607234354780708494677932679280769858654269101601513916553) (-398).
Definition f27 := Float2 (1) (-2).
Definition i15 := makepairF f26 f27.
Notation p22 := (BND r41 i15). (* BND((1 + dl) * (1 + dl) * (1 + dl) * th * th * Pt, [-1.01728e-05, 0.25]) *)
Definition f28 := Float2 (315224119153669957840035667818116814462866807386541351210094532399757207271105977292404816917923206080973998345562323) (-401).
Definition i16 := makepairF f18 f28.
Notation p23 := (BND r42 i16). (* BND((1 + dl) * (1 + dl) * (1 + dl) * th * th, [-1, 6.10367e-05]) *)
Definition f29 := Float2 (-161392683180334310134928534837629887342429822280183985464554454291660756865118386858359479260642145293998923966701135559) (-403).
Definition f30 := Float2 (161392683180334310134928534837629887342429822280183985464554454291660756865118386858359479260642145293998923966701135559) (-403).
Definition i17 := makepairF f29 f30.
Notation p24 := (BND r43 i17). (* BND((1 + dl) * (1 + dl) * (1 + dl) * th, [-0.0078126, 0.0078126]) *)
Definition f31 := Float2 (9007199254740989) (-53).
Definition f32 := Float2 (730750818665451702490757660178213618792745926657) (-159).
Definition i18 := makepairF f31 f32.
Notation p25 := (BND r44 i18). (* BND((1 + dl) * (1 + dl) * (1 + dl), [1, 1]) *)
Definition f33 := Float2 (4503599627370495) (-52).
Definition f34 := Float2 (81129638414606699710187514626049) (-106).
Definition i19 := makepairF f33 f34.
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
Definition f35 := Float2 (-80696341590167128190183336492762922277553037908230366465363237155637854447075094068654269148145619287504548485417148267) (-402).
Definition i20 := makepairF f35 f2.
Notation p28 := (BND _th i20). (* BND(th, [-0.0078126, 0.0078126]) *)
Lemma t8 : p11 -> p28.
Proof.
 intros h0.
 refine (bnd_of_abs _th i1 i20 h0 _) ; finalize.
Qed.
Lemma l29 : s1 -> p28 (* BND(th, [-0.0078126, 0.0078126]) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 apply t8. exact h1.
Qed.
Definition i21 := makepairF f25 f32.
Notation p29 := (BND r44 i21). (* BND((1 + dl) * (1 + dl) * (1 + dl), [0.5, 1]) *)
Lemma t9 : p29 -> p28 -> p24.
Proof.
 intros h0 h1.
 refine (mul_po r44 _th i21 i20 i17 h0 h1 _) ; finalize.
Qed.
Lemma l25 : s1 -> p24 (* BND((1 + dl) * (1 + dl) * (1 + dl) * th, [-0.0078126, 0.0078126]) *).
Proof.
 intros h0.
 assert (h1 := l26 h0).
 assert (h2 := l29 h0).
 apply t9. refine (subset r44 i18 i21 h1 _) ; finalize. exact h2.
Qed.
Definition f36 := Float2 (-630440168673180688985807316349710330293383108658049738010650290278420737867774172411361477719887650683629285042321471) (-395).
Definition f37 := Float2 (630440168673180688985807316349710330293383108658049738010650290278420737867774172411361477719887650683629285042321471) (-395).
Definition i22 := makepairF f36 f37.
Notation p30 := (BND _th i22). (* BND(th, [-0.0078126, 0.0078126]) *)
Lemma t10 : p24 -> p30 -> p23.
Proof.
 intros h0 h1.
 refine (mul_oo r43 _th i17 i22 i16 h0 h1 _) ; finalize.
Qed.
Lemma l24 : s1 -> p23 (* BND((1 + dl) * (1 + dl) * (1 + dl) * th * th, [-1, 6.10367e-05]) *).
Proof.
 intros h0.
 assert (h1 := l25 h0).
 assert (h2 := l29 h0).
 apply t10. exact h1. refine (subset _th i20 i22 h2 _) ; finalize.
Qed.
Definition f38 := Float2 (-420288066094874421600302030049404687265017339355222306979230067057659731779270703669307340374452424094308929811930643) (-390).
Definition f39 := Float2 (-1) (-3).
Definition i23 := makepairF f38 f39.
Notation p31 := (BND _Pt i23). (* BND(Pt, [-0.166667, -0.125]) *)
Definition f40 := Float2 (-6004799503160661) (-55).
Definition f41 := Float2 (-5) (-5).
Definition i24 := makepairF f40 f41.
Notation p32 := (BND _s0 i24). (* BND(s0, [-0.166667, -0.15625]) *)
Lemma t11 : p32.
Proof.
 refine (constant2 _ i24 _) ; finalize.
Qed.
Lemma l31 : s1 -> p32 (* BND(s0, [-0.166667, -0.15625]) *).
Proof.
 intros h0.
 apply t11.
Qed.
Definition f42 := Float2 (15809456941781227045077799726695311908479741146279508217643495023487880505434605) (-390).
Definition f43 := Float2 (1) (-5).
Definition i25 := makepairF f42 f43.
Notation p33 := (BND r13 i25). (* BND(t * t * (s1 + t * t * s2), [6.26929e-39, 0.03125]) *)
Definition f44 := Float2 (81129638414606663681390495662081) (-226).
Definition f45 := Float2 (904648855732594315081895531745062387205530226419445709492986833309748190723) (-263).
Definition i26 := makepairF f44 f45.
Notation p34 := (BND r10 i26). (* BND(t * t, [7.52316e-37, 6.10367e-05]) *)
Definition f46 := Float2 (9007199254740991) (-113).
Definition f47 := Float2 (9850627635518449359042600114108797373401208645846262609739386516564258801662399580785046388256082159596926574646133) (-389).
Definition i27 := makepairF f46 f47.
Notation p35 := (ABS _t i27). (* ABS(t, [8.67362e-19, 0.0078126]) *)
Definition f48 := Float2 (9850627635518448265403239317964223910834111072782027156416410785600324029183971443927523089373244541931707578786273) (-389).
Definition i28 := makepairF f1 f48.
Notation p36 := (ABS _th i28). (* ABS(th, [8.67362e-19, 0.0078126]) *)
Lemma t12 : p36 -> p27 -> p35.
Proof.
 intros h0 h1.
 refine (mul_aa _th r4 i28 i12 i27 h0 h1 _) ; finalize.
Qed.
Lemma l34 : s1 -> p35 (* ABS(t, [8.67362e-19, 0.0078126]) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 assert (h2 := l28 h0).
 apply t12. refine (abs_subset _th i1 i28 h1 _) ; finalize. exact h2.
Qed.
Definition f49 := Float2 (28948392844014611481635327811237585999600685542250209866699878228473617831335) (-261).
Definition i29 := makepairF f46 f49.
Notation p37 := (ABS _t i29). (* ABS(t, [8.67362e-19, 0.0078126]) *)
Lemma t13 : p37 -> p34.
Proof.
 intros h0.
 refine (square _t i29 i26 h0 _) ; finalize.
Qed.
Lemma l33 : s1 -> p34 (* BND(t * t, [7.52316e-37, 6.10367e-05]) *).
Proof.
 intros h0.
 assert (h1 := l34 h0).
 apply t13. refine (abs_subset _t i27 i29 h1 _) ; finalize.
Qed.
Definition f50 := Float2 (15809456941781230555482420443802145331720907777056276418164967899654207271495467) (-270).
Definition i30 := makepairF f50 f16.
Notation p38 := (BND r14 i30). (* BND(s1 + t * t * s2, [0.00833332, 1]) *)
Definition f51 := Float2 (600479950272053) (-56).
Definition i31 := makepairF f51 f51.
Notation p39 := (BND _s1 i31). (* BND(s1, [0.00833333, 0.00833333]) *)
Lemma t14 : p39.
Proof.
 refine (constant2 _ i31 _) ; finalize.
Qed.
Lemma l36 : s1 -> p39 (* BND(s1, [0.00833333, 0.00833333]) *).
Proof.
 intros h0.
 apply t14.
Qed.
Definition f52 := Float2 (-22974261559675970697226277287218467617989198555503719702210180159621404885) (-270).
Definition f53 := Float2 (-1) (-133).
Definition i32 := makepairF f52 f53.
Notation p40 := (BND r16 i32). (* BND(t * t * s2, [-1.211e-08, -9.18355e-41]) *)
Definition f54 := Float2 (-3659917331012787) (-64).
Definition f55 := Float2 (-3) (-14).
Definition i33 := makepairF f54 f55.
Notation p41 := (BND _s2 i33). (* BND(s2, [-0.000198405, -0.000183105]) *)
Lemma t15 : p41.
Proof.
 refine (constant2 _ i33 _) ; finalize.
Qed.
Lemma l38 : s1 -> p41 (* BND(s2, [-0.000198405, -0.000183105]) *).
Proof.
 intros h0.
 apply t15.
Qed.
Definition f56 := Float2 (3) (-122).
Definition i34 := makepairF f56 f45.
Notation p42 := (BND r10 i34). (* BND(t * t, [5.64237e-37, 6.10367e-05]) *)
Lemma t16 : p42 -> p41 -> p40.
Proof.
 intros h0 h1.
 refine (mul_pn r10 _s2 i34 i33 i32 h0 h1 _) ; finalize.
Qed.
Lemma l37 : s1 -> p40 (* BND(t * t * s2, [-1.211e-08, -9.18355e-41]) *).
Proof.
 intros h0.
 assert (h1 := l33 h0).
 assert (h2 := l38 h0).
 apply t16. refine (subset r10 i26 i34 h1 _) ; finalize. exact h2.
Qed.
Definition i35 := makepairF f51 f16.
Notation p43 := (BND _s1 i35). (* BND(s1, [0.00833333, 1]) *)
Lemma t17 : p43 -> p40 -> p38.
Proof.
 intros h0 h1.
 refine (add _s1 r16 i35 i32 i30 h0 h1 _) ; finalize.
Qed.
Lemma l35 : s1 -> p38 (* BND(s1 + t * t * s2, [0.00833332, 1]) *).
Proof.
 intros h0.
 assert (h1 := l36 h0).
 assert (h2 := l37 h0).
 apply t17. refine (subset _s1 i31 i35 h1 _) ; finalize. exact h2.
Qed.
Definition i36 := makepairF f44 f43.
Notation p44 := (BND r10 i36). (* BND(t * t, [7.52316e-37, 0.03125]) *)
Lemma t18 : p44 -> p38 -> p33.
Proof.
 intros h0 h1.
 refine (mul_pp r10 r14 i36 i30 i25 h0 h1 _) ; finalize.
Qed.
Lemma l32 : s1 -> p33 (* BND(t * t * (s1 + t * t * s2), [6.26929e-39, 0.03125]) *).
Proof.
 intros h0.
 assert (h1 := l33 h0).
 assert (h2 := l35 h0).
 apply t18. refine (subset r10 i26 i36 h1 _) ; finalize. exact h2.
Qed.
Lemma t19 : p32 -> p33 -> p31.
Proof.
 intros h0 h1.
 refine (add _s0 r13 i24 i25 i23 h0 h1 _) ; finalize.
Qed.
Lemma l30 : s1 -> p31 (* BND(Pt, [-0.166667, -0.125]) *).
Proof.
 intros h0.
 assert (h1 := l31 h0).
 assert (h2 := l32 h0).
 apply t19. exact h1. exact h2.
Qed.
Lemma t20 : p23 -> p31 -> p22.
Proof.
 intros h0 h1.
 refine (mul_on r42 _Pt i16 i23 i15 h0 h1 _) ; finalize.
Qed.
Lemma l23 : s1 -> p22 (* BND((1 + dl) * (1 + dl) * (1 + dl) * th * th * Pt, [-1.01728e-05, 0.25]) *).
Proof.
 intros h0.
 assert (h1 := l24 h0).
 assert (h2 := l30 h0).
 apply t20. exact h1. exact h2.
Qed.
Definition f57 := Float2 (4611686018427387645) (-62).
Definition f58 := Float2 (4611686018427388163) (-62).
Definition i37 := makepairF f57 f58.
Notation p45 := (BND r18 i37). (* BND(1 + al, [1, 1]) *)
Lemma l40 : s1 -> p4 (* BND(al, [-5.61617e-17, 5.61617e-17]) *).
Proof.
 intros h0.
 assert (h1 := l11 h0).
 exact (proj2 h1).
Qed.
Lemma t21 : p20 -> p4 -> p45.
Proof.
 intros h0 h1.
 refine (add r5 _al i13 i4 i37 h0 h1 _) ; finalize.
Qed.
Lemma l39 : s1 -> p45 (* BND(1 + al, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l20 h0).
 assert (h2 := l40 h0).
 apply t21. exact h1. exact h2.
Qed.
Definition i38 := makepairF f25 f58.
Notation p46 := (BND r18 i38). (* BND(1 + al, [0.5, 1]) *)
Lemma t22 : p22 -> p46 -> p21.
Proof.
 intros h0 h1.
 refine (mul_op r41 r18 i15 i38 i14 h0 h1 _) ; finalize.
Qed.
Lemma l22 : s1 -> p21 (* BND((1 + dl) * (1 + dl) * (1 + dl) * th * th * Pt * (1 + al), [-1.01728e-05, 0.5]) *).
Proof.
 intros h0.
 assert (h1 := l23 h0).
 assert (h2 := l39 h0).
 apply t22. exact h1. refine (subset r18 i37 i38 h2 _) ; finalize.
Qed.
Definition f59 := Float2 (3) (-1).
Definition i39 := makepairF f22 f59.
Notation p47 := (BND r4 i39). (* BND(1 + dl, [1, 1.5]) *)
Lemma t23 : p47 -> p21 -> p18.
Proof.
 intros h0 h1.
 refine (add r4 r40 i39 i14 i11 h0 h1 _) ; finalize.
Qed.
Lemma l18 : s1 -> p18 (* BND(1 + dl + (1 + dl) * (1 + dl) * (1 + dl) * th * th * Pt * (1 + al), [0.99999, 2]) *).
Proof.
 intros h0.
 assert (h1 := l19 h0).
 assert (h2 := l22 h0).
 apply t23. refine (subset r4 i12 i39 h1 _) ; finalize. exact h2.
Qed.
Definition i40 := makepairF f13 f13.
Notation p48 := (REL r38 r39 i40). (* REL(ST / th, 1 + dl + (1 + dl) * (1 + dl) * (1 + dl) * th * th * Pt * (1 + al), [0, 0]) *)
Notation p49 := (r38 = r39). (* EQL(ST / th, 1 + dl + (1 + dl) * (1 + dl) * (1 + dl) * th * th * Pt * (1 + al)) *)
Lemma t24 : p10 -> p49.
Proof.
 intros h0.
 refine (b2 h0) ; finalize.
Qed.
Lemma l42 : s1 -> p49 (* EQL(ST / th, 1 + dl + (1 + dl) * (1 + dl) * (1 + dl) * th * th * Pt * (1 + al)) *).
Proof.
 intros h0.
 assert (h1 := l6 h0).
 apply t24. exact h1.
Qed.
Notation p50 := (REL r39 r39 i40). (* REL(1 + dl + (1 + dl) * (1 + dl) * (1 + dl) * th * th * Pt * (1 + al), 1 + dl + (1 + dl) * (1 + dl) * (1 + dl) * th * th * Pt * (1 + al), [0, 0]) *)
Lemma t25 : p50.
Proof.
 refine (rel_refl r39 i40 _) ; finalize.
Qed.
Lemma l43 : s1 -> p50 (* REL(1 + dl + (1 + dl) * (1 + dl) * (1 + dl) * th * th * Pt * (1 + al), 1 + dl + (1 + dl) * (1 + dl) * (1 + dl) * th * th * Pt * (1 + al), [0, 0]) *).
Proof.
 intros h0.
 apply t25.
Qed.
Lemma t26 : p49 -> p50 -> p48.
Proof.
 intros h0 h1.
 refine (rel_rewrite_1 r38 r39 r39 i40 h0 h1) ; finalize.
Qed.
Lemma l41 : s1 -> p48 (* REL(ST / th, 1 + dl + (1 + dl) * (1 + dl) * (1 + dl) * th * th * Pt * (1 + al), [0, 0]) *).
Proof.
 intros h0.
 assert (h1 := l42 h0).
 assert (h2 := l43 h0).
 apply t26. exact h1. exact h2.
Qed.
Lemma t27 : p18 -> p48 -> p17.
Proof.
 intros h0 h1.
 refine (bnd_of_bnd_rel_p r38 r39 i11 i40 i11 h0 h1 _) ; finalize.
Qed.
Lemma l17 : s1 -> p17 (* BND(ST / th, [0.99999, 2]) *).
Proof.
 intros h0.
 assert (h1 := l18 h0).
 assert (h2 := l41 h0).
 apply t27. exact h1. exact h2.
Qed.
Definition f60 := Float2 (-1) (-1).
Definition f61 := Float2 (-1) (-60).
Definition i41 := makepairF f60 f61.
Notation p51 := (BND _th i41). (* BND(th, [-0.5, -8.67362e-19]) *)
Definition i42 := makepairF f35 f13.
Notation p52 := (BND _th i42). (* BND(th, [-0.0078126, 0]) *)
Lemma l46 : p7 -> s1 -> p7 (* BND(th, [-inf, 0]) *).
Proof.
 intros h0 h1.
 assert (h2 := h0).
 exact (h2).
Qed.
Lemma l45 : p7 -> s1 -> p52 (* BND(th, [-0.0078126, 0]) *).
Proof.
 intros h0 h1.
 assert (h2 := l46 h0 h1).
 assert (h3 := l29 h1).
 apply intersect_hb with (1 := h2) (2 := h3). finalize.
Qed.
Definition i43 := makepairF f60 f13.
Notation p53 := (BND _th i43). (* BND(th, [-0.5, 0]) *)
Lemma t28 : p53 -> p12 -> p51.
Proof.
 intros h0 h1.
 refine (bnd_of_bnd_abs_n _th i43 i8 i41 h0 h1 _) ; finalize.
Qed.
Lemma l44 : p7 -> s1 -> p51 (* BND(th, [-0.5, -8.67362e-19]) *).
Proof.
 intros h0 h1.
 assert (h2 := l45 h0 h1).
 assert (h3 := l7 h1).
 apply t28. refine (subset _th i42 i43 h2 _) ; finalize. refine (abs_subset _th i1 i8 h3 _) ; finalize.
Qed.
Definition i44 := makepairF f25 f21.
Notation p54 := (BND r38 i44). (* BND(ST / th, [0.5, 2]) *)
Lemma t29 : p54 -> p51 -> p16.
Proof.
 intros h0 h1.
 refine (mul_pn r38 _th i44 i41 i10 h0 h1 _) ; finalize.
Qed.
Lemma l16 : p7 -> s1 -> p16 (* BND(ST / th * th, [-1, -4.33681e-19]) *).
Proof.
 intros h0 h1.
 assert (h2 := l17 h1).
 assert (h3 := l44 h0 h1).
 apply t29. refine (subset r38 i11 i44 h2 _) ; finalize. exact h3.
Qed.
Lemma t30 : p10 -> p16 -> p15.
Proof.
 intros h0 h1.
 refine (div_xilu _ST _ i10 h0 h1) ; finalize.
Qed.
Lemma l15 : p7 -> s1 -> p15 (* BND(ST, [-1, -4.33681e-19]) *).
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
Lemma l14 : p7 -> s1 -> p14 (* ABS(ST, [4.33681e-19, 1]) *).
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
Notation p55 := (BND r36 i7). (* BND((SN - ST) / th / (ST / th), [-1.2995e-20, 1.2995e-20]) *)
Definition f62 := Float2 (-1237994625509274997984115473711570670009437781855324793210576564471276218576212125103177536404260692883574358507344689441) (-465).
Definition f63 := Float2 (1237994625509274997984115473711570670009437781855324793210576564471276218576212125103177536404260692883574358507344689441) (-465).
Definition i45 := makepairF f62 f63.
Notation p56 := (BND r37 i45). (* BND((SN - ST) / th, [-1.29948e-20, 1.29948e-20]) *)
Notation p57 := (BND r46 i45). (* BND((1 + dl) * d2 + th * th * (Ph * (1 + et) * (1 + d2) - (1 + dl) * (1 + dl) * (1 + dl) * Pt * (1 + al)), [-1.29948e-20, 1.29948e-20]) *)
Definition f64 := Float2 (-9007199254740993) (-158).
Definition f65 := Float2 (9007199254740993) (-158).
Definition i46 := makepairF f64 f65.
Notation p58 := (BND r47 i46). (* BND((1 + dl) * d2, [-2.46519e-32, 2.46519e-32]) *)
Lemma l51 : s1 -> p5 (* BND(d2, [-2.46519e-32, 2.46519e-32]) *).
Proof.
 intros h0.
 assert (h1 := l12 h0).
 exact (proj2 h1).
Qed.
Definition i47 := makepairF f25 f23.
Notation p59 := (BND r4 i47). (* BND(1 + dl, [0.5, 1]) *)
Lemma t34 : p59 -> p5 -> p58.
Proof.
 intros h0 h1.
 refine (mul_po r4 _d2 i47 i5 i46 h0 h1 _) ; finalize.
Qed.
Lemma l50 : s1 -> p58 (* BND((1 + dl) * d2, [-2.46519e-32, 2.46519e-32]) *).
Proof.
 intros h0.
 assert (h1 := l19 h0).
 assert (h2 := l51 h0).
 apply t34. refine (subset r4 i12 i47 h1 _) ; finalize. exact h2.
Qed.
Definition f66 := Float2 (-1237994625506926455401341640222940584441834225785588062545267839985980973215440075996636950443436187515482491412837890337) (-465).
Definition f67 := Float2 (1237994625506926455401341640222940584441834225785588062545267839985980973215440075996636950443436187515482491412837890337) (-465).
Definition i48 := makepairF f66 f67.
Notation p60 := (BND r48 i48). (* BND(th * th * (Ph * (1 + et) * (1 + d2) - (1 + dl) * (1 + dl) * (1 + dl) * Pt * (1 + al)), [-1.29948e-20, 1.29948e-20]) *)
Definition f68 := Float2 (1) (-120).
Definition f69 := Float2 (1291157992053431717270786733431520474287331049393849469024863900881175145785792266077733566764651448822902856698204185705) (-413).
Definition i49 := makepairF f68 f69.
Notation p61 := (BND r27 i49). (* BND(th * th, [7.52316e-37, 6.10367e-05]) *)
Lemma t35 : p11 -> p61.
Proof.
 intros h0.
 refine (square _th i1 i49 h0 _) ; finalize.
Qed.
Lemma l53 : s1 -> p61 (* BND(th * th, [7.52316e-37, 6.10367e-05]) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 apply t35. exact h1.
Qed.
Definition f70 := Float2 (-1237962933453002211527786646548076389515825784987219493113938081419309023644695181366047121122122300859931959381786464377) (-451).
Definition f71 := Float2 (1237962933453002211527786646548076389515825784987219493113938081419309023644695181366047121122122300859931959381786464377) (-451).
Definition i50 := makepairF f70 f71.
Notation p62 := (BND r49 i50). (* BND(Ph * (1 + et) * (1 + d2) - (1 + dl) * (1 + dl) * (1 + dl) * Pt * (1 + al), [-2.12902e-16, 2.12902e-16]) *)
Definition i51 := makepairF f13 f71.
Notation p63 := (ABS r49 i51). (* ABS(Ph * (1 + et) * (1 + d2) - (1 + dl) * (1 + dl) * (1 + dl) * Pt * (1 + al), [0, 2.12902e-16]) *)
Notation p64 := (r49 = r54). (* EQL(Ph * (1 + et) * (1 + d2) - (1 + dl) * (1 + dl) * (1 + dl) * Pt * (1 + al), Ph * ((1 + et) * (1 + d2) - 1) - Pt * ((1 + dl) * (1 + dl) * (1 + dl) * (1 + al) - 1) - th * th * ((1 + dl) * (1 + dl) - 1) * (s1 + s2 * th * th * (1 + (1 + dl) * (1 + dl)))) *)
Lemma t36 : p64.
Proof.
 refine (b4) ; finalize.
Qed.
Lemma l56 : s1 -> p64 (* EQL(Ph * (1 + et) * (1 + d2) - (1 + dl) * (1 + dl) * (1 + dl) * Pt * (1 + al), Ph * ((1 + et) * (1 + d2) - 1) - Pt * ((1 + dl) * (1 + dl) * (1 + dl) * (1 + al) - 1) - th * th * ((1 + dl) * (1 + dl) - 1) * (s1 + s2 * th * th * (1 + (1 + dl) * (1 + dl)))) *).
Proof.
 intros h0.
 apply t36.
Qed.
Notation p65 := (ABS r54 i51). (* ABS(Ph * ((1 + et) * (1 + d2) - 1) - Pt * ((1 + dl) * (1 + dl) * (1 + dl) * (1 + al) - 1) - th * th * ((1 + dl) * (1 + dl) - 1) * (s1 + s2 * th * th * (1 + (1 + dl) * (1 + dl))), [0, 2.12902e-16]) *)
Definition f72 := Float2 (618981138367089340172431231079184272881644495389184276130442387357310407744055796246546530464217308867238851694866330829) (-450).
Definition i52 := makepairF f13 f72.
Notation p66 := (ABS r55 i52). (* ABS(Ph * ((1 + et) * (1 + d2) - 1) - Pt * ((1 + dl) * (1 + dl) * (1 + dl) * (1 + al) - 1), [0, 2.12902e-16]) *)
Definition f73 := Float2 (1721505172467559224762750921631715306630863809175205974309199900690392553867740586654800189436238793393154707458916969091) (-452).
Definition i53 := makepairF f13 f73.
Notation p67 := (ABS r56 i53). (* ABS(Ph * ((1 + et) * (1 + d2) - 1), [0, 1.4803e-16]) *)
Definition f74 := Float2 (1) (-3).
Definition f75 := Float2 (1721505172467559176981383934512040135541093861392973337789783308589896257289094654685940145842282082798327024839066647303) (-402).
Definition i54 := makepairF f74 f75.
Notation p68 := (ABS _Ph i54). (* ABS(Ph, [0.125, 0.166667]) *)
Definition f76 := Float2 (5) (-5).
Definition f77 := Float2 (6004799503160661) (-55).
Definition i55 := makepairF f76 f77.
Notation p69 := (ABS _s0 i55). (* ABS(s0, [0.15625, 0.166667]) *)
Lemma t37 : p32 -> p69.
Proof.
 intros h0.
 refine (abs_of_bnd_n _s0 i24 i55 h0 _) ; finalize.
Qed.
Lemma l61 : s1 -> p69 (* ABS(s0, [0.15625, 0.166667]) *).
Proof.
 intros h0.
 assert (h1 := l31 h0).
 apply t37. exact h1.
Qed.
Definition f78 := Float2 (1) (-127).
Definition f79 := Float2 (5253742953546106546819429678536438827303760446862426218286241177998344068832721296414009057198091831289779138591495) (-402).
Definition i56 := makepairF f78 f79.
Notation p70 := (ABS r29 i56). (* ABS(th * th * (s1 + th * th * s2), [5.87747e-39, 5.0864e-07]) *)
Definition f80 := Float2 (19701507447104365803082072958854987705800339498807517532728025831316759426663089997524010723337577038923688609286563) (-397).
Definition i57 := makepairF f68 f80.
Notation p71 := (ABS r27 i57). (* ABS(th * th, [7.52316e-37, 6.10367e-05]) *)
Lemma t38 : p36 -> p36 -> p71.
Proof.
 intros h0 h1.
 refine (mul_aa _th _th i28 i28 i57 h0 h1 _) ; finalize.
Qed.
Lemma l63 : s1 -> p71 (* ABS(th * th, [7.52316e-37, 6.10367e-05]) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 apply t38. refine (abs_subset _th i1 i28 h1 _) ; finalize. refine (abs_subset _th i1 i28 h1 _) ; finalize.
Qed.
Definition f81 := Float2 (1) (-7).
Definition f82 := Float2 (10507216920617542864267555884760631426283826174892433109790495478604361086807081811071182408200631200661229933780349) (-389).
Definition i58 := makepairF f81 f82.
Notation p72 := (ABS r30 i58). (* ABS(s1 + th * th * s2, [0.0078125, 0.00833335]) *)
Definition f83 := Float2 (273) (-15).
Definition i59 := makepairF f83 f51.
Notation p73 := (ABS _s1 i59). (* ABS(s1, [0.0083313, 0.00833333]) *)
Notation p74 := (BND _s1 i59). (* BND(s1, [0.0083313, 0.00833333]) *)
Lemma t39 : p74 -> p73.
Proof.
 intros h0.
 refine (abs_of_bnd_p _s1 i59 i59 h0 _) ; finalize.
Qed.
Lemma l65 : s1 -> p73 (* ABS(s1, [0.0083313, 0.00833333]) *).
Proof.
 intros h0.
 assert (h1 := l36 h0).
 apply t39. refine (subset _s1 i31 i59 h1 _) ; finalize.
Qed.
Definition f84 := Float2 (1) (-133).
Definition f85 := Float2 (15269015823803259582590554309266441960914790749411013567195280693668829175909474007612969663685209376637934973) (-389).
Definition i60 := makepairF f84 f85.
Notation p75 := (ABS r31 i60). (* ABS(th * th * s2, [9.18355e-41, 1.211e-08]) *)
Definition f86 := Float2 (3) (-14).
Definition f87 := Float2 (3659917331012787) (-64).
Definition i61 := makepairF f86 f87.
Notation p76 := (ABS _s2 i61). (* ABS(s2, [0.000183105, 0.000198405]) *)
Lemma t40 : p41 -> p76.
Proof.
 intros h0.
 refine (abs_of_bnd_n _s2 i33 i61 h0 _) ; finalize.
Qed.
Lemma l67 : s1 -> p76 (* ABS(s2, [0.000183105, 0.000198405]) *).
Proof.
 intros h0.
 assert (h1 := l38 h0).
 apply t40. exact h1.
Qed.
Definition f88 := Float2 (75155286587159598553016940913600874732209547038297720080291846585528409678127632131668131726599033504194979131) (-379).
Definition i62 := makepairF f68 f88.
Notation p77 := (ABS r27 i62). (* ABS(th * th, [7.52316e-37, 6.10367e-05]) *)
Definition f89 := Float2 (1) (-13).
Definition i63 := makepairF f89 f87.
Notation p78 := (ABS _s2 i63). (* ABS(s2, [0.00012207, 0.000198405]) *)
Lemma t41 : p77 -> p78 -> p75.
Proof.
 intros h0 h1.
 refine (mul_aa r27 _s2 i62 i63 i60 h0 h1 _) ; finalize.
Qed.
Lemma l66 : s1 -> p75 (* ABS(th * th * s2, [9.18355e-41, 1.211e-08]) *).
Proof.
 intros h0.
 assert (h1 := l63 h0).
 assert (h2 := l67 h0).
 apply t41. refine (abs_subset r27 i57 i62 h1 _) ; finalize. refine (abs_subset _s2 i61 i63 h2 _) ; finalize.
Qed.
Definition f90 := Float2 (17) (-11).
Definition i64 := makepairF f90 f51.
Notation p79 := (ABS _s1 i64). (* ABS(s1, [0.00830078, 0.00833333]) *)
Lemma t42 : p79 -> p75 -> p72.
Proof.
 intros h0 h1.
 refine (add_aa_p _s1 r31 i64 i60 i58 h0 h1 _) ; finalize.
Qed.
Lemma l64 : s1 -> p72 (* ABS(s1 + th * th * s2, [0.0078125, 0.00833335]) *).
Proof.
 intros h0.
 assert (h1 := l65 h0).
 assert (h2 := l66 h0).
 apply t42. refine (abs_subset _s1 i59 i64 h1 _) ; finalize. exact h2.
Qed.
Lemma t43 : p71 -> p72 -> p70.
Proof.
 intros h0 h1.
 refine (mul_aa r27 r30 i57 i58 i56 h0 h1 _) ; finalize.
Qed.
Lemma l62 : s1 -> p70 (* ABS(th * th * (s1 + th * th * s2), [5.87747e-39, 5.0864e-07]) *).
Proof.
 intros h0.
 assert (h1 := l63 h0).
 assert (h2 := l64 h0).
 apply t43. exact h1. exact h2.
Qed.
Lemma t44 : p69 -> p70 -> p68.
Proof.
 intros h0 h1.
 refine (add_aa_p _s0 r29 i55 i56 i54 h0 h1 _) ; finalize.
Qed.
Lemma l60 : s1 -> p68 (* ABS(Ph, [0.125, 0.166667]) *).
Proof.
 intros h0.
 assert (h1 := l61 h0).
 assert (h2 := l62 h0).
 apply t44. exact h1. exact h2.
Qed.
Definition f91 := Float2 (40564819207303341973794409414657) (-155).
Definition i65 := makepairF f13 f91.
Notation p80 := (ABS r57 i65). (* ABS((1 + et) * (1 + d2) - 1, [0, 8.88178e-16]) *)
Definition f92 := Float2 (-36028797018963969) (-105).
Definition i66 := makepairF f92 f91.
Notation p81 := (BND r57 i66). (* BND((1 + et) * (1 + d2) - 1, [-8.88178e-16, 8.88178e-16]) *)
Definition f93 := Float2 (40564819207303304819097483608063) (-105).
Definition f94 := Float2 (45671926166590756758684358325725818158657306625) (-155).
Definition i67 := makepairF f93 f94.
Notation p82 := (BND r58 i67). (* BND((1 + et) * (1 + d2), [1, 1]) *)
Definition f95 := Float2 (1125899906842623) (-50).
Definition f96 := Float2 (1125899906842625) (-50).
Definition i68 := makepairF f95 f96.
Notation p83 := (BND r32 i68). (* BND(1 + et, [1, 1]) *)
Lemma l72 : s1 -> p3 (* BND(et, [-8.88178e-16, 8.88178e-16]) *).
Proof.
 intros h0.
 assert (h1 := l10 h0).
 exact (proj2 h1).
Qed.
Lemma t45 : p20 -> p3 -> p83.
Proof.
 intros h0 h1.
 refine (add r5 _et i13 i3 i68 h0 h1 _) ; finalize.
Qed.
Lemma l71 : s1 -> p83 (* BND(1 + et, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l20 h0).
 assert (h2 := l72 h0).
 apply t45. exact h1. exact h2.
Qed.
Definition f97 := Float2 (40564819207303340847894502572031) (-105).
Definition f98 := Float2 (40564819207303340847894502572033) (-105).
Definition i69 := makepairF f97 f98.
Notation p84 := (BND r34 i69). (* BND(1 + d2, [1, 1]) *)
Lemma t46 : p20 -> p5 -> p84.
Proof.
 intros h0 h1.
 refine (add r5 _d2 i13 i5 i69 h0 h1 _) ; finalize.
Qed.
Lemma l73 : s1 -> p84 (* BND(1 + d2, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l20 h0).
 assert (h2 := l51 h0).
 apply t46. exact h1. exact h2.
Qed.
Lemma t47 : p83 -> p84 -> p82.
Proof.
 intros h0 h1.
 refine (mul_pp r32 r34 i68 i69 i67 h0 h1 _) ; finalize.
Qed.
Lemma l70 : s1 -> p82 (* BND((1 + et) * (1 + d2), [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l71 h0).
 assert (h2 := l73 h0).
 apply t47. exact h1. exact h2.
Qed.
Lemma t48 : p82 -> p20 -> p81.
Proof.
 intros h0 h1.
 refine (sub r58 r5 i67 i13 i66 h0 h1 _) ; finalize.
Qed.
Lemma l69 : s1 -> p81 (* BND((1 + et) * (1 + d2) - 1, [-8.88178e-16, 8.88178e-16]) *).
Proof.
 intros h0.
 assert (h1 := l70 h0).
 assert (h2 := l20 h0).
 apply t48. exact h1. exact h2.
Qed.
Lemma t49 : p81 -> p80.
Proof.
 intros h0.
 refine (abs_of_bnd_o r57 i66 i65 h0 _) ; finalize.
Qed.
Lemma l68 : s1 -> p80 (* ABS((1 + et) * (1 + d2) - 1, [0, 8.88178e-16]) *).
Proof.
 intros h0.
 assert (h1 := l69 h0).
 apply t49. exact h1.
Qed.
Lemma t50 : p68 -> p80 -> p67.
Proof.
 intros h0 h1.
 refine (mul_aa _Ph r57 i54 i65 i53 h0 h1 _) ; finalize.
Qed.
Lemma l59 : s1 -> p67 (* ABS(Ph * ((1 + et) * (1 + d2) - 1), [0, 1.4803e-16]) *).
Proof.
 intros h0.
 assert (h1 := l60 h0).
 assert (h2 := l68 h0).
 apply t50. exact h1. exact h2.
Qed.
Definition f99 := Float2 (754419381000798135926974002685021784895714172381531130212569648738849077108482598331385932420630442075800699320548354225) (-452).
Definition i70 := makepairF f13 f99.
Notation p85 := (ABS r59 i70). (* ABS(Pt * ((1 + dl) * (1 + dl) * (1 + dl) * (1 + al) - 1), [0, 6.48716e-17]) *)
Definition f100 := Float2 (53797036639611224280704703171430707452265932551765722752612610090977387093819351843570621885057688271915224390984049541) (-397).
Definition i71 := makepairF f74 f100.
Notation p86 := (ABS _Pt i71). (* ABS(Pt, [0.125, 0.166667]) *)
Definition f101 := Float2 (164179467298315866043325106907480320102625749270397501203142579941501787294907175505265269410624837232670361297797) (-397).
Definition i72 := makepairF f78 f101.
Notation p87 := (ABS r13 i72). (* ABS(t * t * (s1 + t * t * s2), [5.87747e-39, 5.0864e-07]) *)
Definition f102 := Float2 (31) (-125).
Definition f103 := Float2 (4925376861776092544423877619676571749514530420893827744371785590952091604453736219843444439109060655547221217104323) (-395).
Definition i73 := makepairF f102 f103.
Notation p88 := (ABS r10 i73). (* ABS(t * t, [7.28806e-37, 6.10367e-05]) *)
Definition f104 := Float2 (63) (-66).
Definition i74 := makepairF f104 f47.
Notation p89 := (ABS _t i74). (* ABS(t, [8.53809e-19, 0.0078126]) *)
Lemma t51 : p89 -> p89 -> p88.
Proof.
 intros h0 h1.
 refine (mul_aa _t _t i74 i74 i73 h0 h1 _) ; finalize.
Qed.
Lemma l77 : s1 -> p88 (* ABS(t * t, [7.28806e-37, 6.10367e-05]) *).
Proof.
 intros h0.
 assert (h1 := l34 h0).
 apply t51. refine (abs_subset _t i27 i74 h1 _) ; finalize. refine (abs_subset _t i27 i74 h1 _) ; finalize.
Qed.
Definition f105 := Float2 (2626804230154385716067736571836705468175153991247524009054744976942113530394404771938286467527720450490757615314267) (-387).
Definition i75 := makepairF f90 f105.
Notation p90 := (ABS r14 i75). (* ABS(s1 + t * t * s2, [0.00830078, 0.00833335]) *)
Definition f106 := Float2 (3817253955950815743248285124928214687676222103084360512906111196675899928296538992768719978571627794291352923) (-387).
Definition i76 := makepairF f84 f106.
Notation p91 := (ABS r16 i76). (* ABS(t * t * s2, [9.18355e-41, 1.211e-08]) *)
Definition f107 := Float2 (18788821646789903810210714796739851949747201617789565064894811977203718583884186629651811367450945493878254765) (-377).
Definition i77 := makepairF f56 f107.
Notation p92 := (ABS r10 i77). (* ABS(t * t, [5.64237e-37, 6.10367e-05]) *)
Lemma t52 : p92 -> p76 -> p91.
Proof.
 intros h0 h1.
 refine (mul_aa r10 _s2 i77 i61 i76 h0 h1 _) ; finalize.
Qed.
Lemma l79 : s1 -> p91 (* ABS(t * t * s2, [9.18355e-41, 1.211e-08]) *).
Proof.
 intros h0.
 assert (h1 := l77 h0).
 assert (h2 := l67 h0).
 apply t52. refine (abs_subset r10 i73 i77 h1 _) ; finalize. exact h2.
Qed.
Lemma t53 : p73 -> p91 -> p90.
Proof.
 intros h0 h1.
 refine (add_aa_p _s1 r16 i59 i76 i75 h0 h1 _) ; finalize.
Qed.
Lemma l78 : s1 -> p90 (* ABS(s1 + t * t * s2, [0.00830078, 0.00833335]) *).
Proof.
 intros h0.
 assert (h1 := l65 h0).
 assert (h2 := l79 h0).
 apply t53. exact h1. exact h2.
Qed.
Lemma t54 : p88 -> p90 -> p87.
Proof.
 intros h0 h1.
 refine (mul_aa r10 r14 i73 i75 i72 h0 h1 _) ; finalize.
Qed.
Lemma l76 : s1 -> p87 (* ABS(t * t * (s1 + t * t * s2), [5.87747e-39, 5.0864e-07]) *).
Proof.
 intros h0.
 assert (h1 := l77 h0).
 assert (h2 := l78 h0).
 apply t54. exact h1. exact h2.
Qed.
Lemma t55 : p69 -> p87 -> p86.
Proof.
 intros h0 h1.
 refine (add_aa_p _s0 r13 i55 i72 i71 h0 h1 _) ; finalize.
Qed.
Lemma l75 : s1 -> p86 (* ABS(Pt, [0.125, 0.166667]) *).
Proof.
 intros h0.
 assert (h1 := l61 h0).
 assert (h2 := l76 h0).
 apply t55. exact h1. exact h2.
Qed.
Definition f108 := Float2 (1311697719504485556740660790348130382781007716679939) (-221).
Definition i78 := makepairF f13 f108.
Notation p93 := (ABS r60 i78). (* ABS((1 + dl) * (1 + dl) * (1 + dl) * (1 + al) - 1, [0, 3.89229e-16]) *)
Definition f109 := Float2 (-1795) (-62).
Definition i79 := makepairF f109 f108.
Notation p94 := (BND r60 i79). (* BND((1 + dl) * (1 + dl) * (1 + dl) * (1 + al) - 1, [-3.89229e-16, 3.89229e-16]) *)
Definition f110 := Float2 (4611686018427386109) (-62).
Definition f111 := Float2 (3369993333393831286031096390363010574865433400947954341145667961091) (-221).
Definition i80 := makepairF f110 f111.
Notation p95 := (BND r61 i80). (* BND((1 + dl) * (1 + dl) * (1 + dl) * (1 + al), [1, 1]) *)
Lemma t56 : p25 -> p45 -> p95.
Proof.
 intros h0 h1.
 refine (mul_pp r44 r18 i18 i37 i80 h0 h1 _) ; finalize.
Qed.
Lemma l82 : s1 -> p95 (* BND((1 + dl) * (1 + dl) * (1 + dl) * (1 + al), [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l26 h0).
 assert (h2 := l39 h0).
 apply t56. exact h1. exact h2.
Qed.
Lemma t57 : p95 -> p20 -> p94.
Proof.
 intros h0 h1.
 refine (sub r61 r5 i80 i13 i79 h0 h1 _) ; finalize.
Qed.
Lemma l81 : s1 -> p94 (* BND((1 + dl) * (1 + dl) * (1 + dl) * (1 + al) - 1, [-3.89229e-16, 3.89229e-16]) *).
Proof.
 intros h0.
 assert (h1 := l82 h0).
 assert (h2 := l20 h0).
 apply t57. exact h1. exact h2.
Qed.
Lemma t58 : p94 -> p93.
Proof.
 intros h0.
 refine (abs_of_bnd_o r60 i79 i78 h0 _) ; finalize.
Qed.
Lemma l80 : s1 -> p93 (* ABS((1 + dl) * (1 + dl) * (1 + dl) * (1 + al) - 1, [0, 3.89229e-16]) *).
Proof.
 intros h0.
 assert (h1 := l81 h0).
 apply t58. exact h1.
Qed.
Lemma t59 : p86 -> p93 -> p85.
Proof.
 intros h0 h1.
 refine (mul_aa _Pt r60 i71 i78 i70 h0 h1 _) ; finalize.
Qed.
Lemma l74 : s1 -> p85 (* ABS(Pt * ((1 + dl) * (1 + dl) * (1 + dl) * (1 + al) - 1), [0, 6.48716e-17]) *).
Proof.
 intros h0.
 assert (h1 := l75 h0).
 assert (h2 := l80 h0).
 apply t59. exact h1. exact h2.
Qed.
Lemma t60 : p67 -> p85 -> p66.
Proof.
 intros h0 h1.
 refine (sub_aa_o r56 r59 i53 i70 i52 h0 h1 _) ; finalize.
Qed.
Lemma l58 : s1 -> p66 (* ABS(Ph * ((1 + et) * (1 + d2) - 1) - Pt * ((1 + dl) * (1 + dl) * (1 + dl) * (1 + al) - 1), [0, 2.12902e-16]) *).
Proof.
 intros h0.
 assert (h1 := l59 h0).
 assert (h2 := l74 h0).
 apply t60. exact h1. exact h2.
Qed.
Definition f112 := Float2 (656718823531182924184389707843752536794208850940853053306704688208156583588872954060193687683125454255992053802719) (-451).
Definition i81 := makepairF f13 f112.
Notation p96 := (ABS r62 i81). (* ABS(th * th * ((1 + dl) * (1 + dl) - 1) * (s1 + s2 * th * th * (1 + (1 + dl) * (1 + dl))), [0, 1.12941e-22]) *)
Definition f113 := Float2 (4925376861776091724183858084704437954726939482680172052066201024092512634376651464565421449629660089227603429987393) (-447).
Definition i82 := makepairF f13 f113.
Notation p97 := (ABS r63 i82). (* ABS(th * th * ((1 + dl) * (1 + dl) - 1), [0, 1.35529e-20]) *)
Definition f114 := Float2 (18014398509481985) (-106).
Definition i83 := makepairF f13 f114.
Notation p98 := (ABS r64 i83). (* ABS((1 + dl) * (1 + dl) - 1, [0, 2.22045e-16]) *)
Definition f115 := Float2 (-1) (-52).
Definition i84 := makepairF f115 f114.
Notation p99 := (BND r64 i84). (* BND((1 + dl) * (1 + dl) - 1, [-2.22045e-16, 2.22045e-16]) *)
Lemma t61 : p26 -> p20 -> p99.
Proof.
 intros h0 h1.
 refine (sub r45 r5 i19 i13 i84 h0 h1 _) ; finalize.
Qed.
Lemma l86 : s1 -> p99 (* BND((1 + dl) * (1 + dl) - 1, [-2.22045e-16, 2.22045e-16]) *).
Proof.
 intros h0.
 assert (h1 := l27 h0).
 assert (h2 := l20 h0).
 apply t61. exact h1. exact h2.
Qed.
Lemma t62 : p99 -> p98.
Proof.
 intros h0.
 refine (abs_of_bnd_o r64 i84 i83 h0 _) ; finalize.
Qed.
Lemma l85 : s1 -> p98 (* ABS((1 + dl) * (1 + dl) - 1, [0, 2.22045e-16]) *).
Proof.
 intros h0.
 assert (h1 := l86 h0).
 apply t62. exact h1.
Qed.
Definition f116 := Float2 (4925376861776091450770518239713746926450084874701879383182006457829189856665772499381002680834394259730922152321641) (-395).
Definition i85 := makepairF f68 f116.
Notation p100 := (ABS r27 i85). (* ABS(th * th, [7.52316e-37, 6.10367e-05]) *)
Lemma t63 : p100 -> p98 -> p97.
Proof.
 intros h0 h1.
 refine (mul_aa r27 r64 i85 i83 i82 h0 h1 _) ; finalize.
Qed.
Lemma l84 : s1 -> p97 (* ABS(th * th * ((1 + dl) * (1 + dl) - 1), [0, 1.35529e-20]) *).
Proof.
 intros h0.
 assert (h1 := l63 h0).
 assert (h2 := l85 h0).
 apply t63. refine (abs_subset r27 i57 i85 h1 _) ; finalize. exact h2.
Qed.
Definition f117 := Float2 (5253616094816683333765264438950565569571288439890422723616273551524573895203397498613576741540272743586203549596021) (-388).
Definition i86 := makepairF f81 f117.
Notation p101 := (ABS r65 i86). (* ABS(s1 + s2 * th * th * (1 + (1 + dl) * (1 + dl)), [0.0078125, 0.00833336]) *)
Definition f118 := Float2 (1) (-132).
Definition f119 := Float2 (15269015823803261277791847404489650355809839580874227809409862740186214444547814989343924788985860276901673333) (-388).
Definition i87 := makepairF f118 f119.
Notation p102 := (ABS r66 i87). (* ABS(s2 * th * th * (1 + (1 + dl) * (1 + dl)), [1.83671e-40, 2.42199e-08]) *)
Definition f120 := Float2 (3) (-134).
Definition i88 := makepairF f120 f85.
Notation p103 := (ABS r67 i88). (* ABS(s2 * th * th, [1.37753e-40, 1.211e-08]) *)
Definition f121 := Float2 (3) (-74).
Definition f122 := Float2 (977204504505750939673767651567112226462047893749264877710063275584877580825171774288519165430535889245445496567) (-388).
Definition i89 := makepairF f121 f122.
Notation p104 := (ABS r68 i89). (* ABS(s2 * th, [1.58819e-22, 1.55006e-06]) *)
Definition f123 := Float2 (2404938387577746158545712724112359353230984148628424598734475289453204108687493028302617941741514780745045795603) (-377).
Definition i90 := makepairF f1 f123.
Notation p105 := (ABS _th i90). (* ABS(th, [8.67362e-19, 0.0078126]) *)
Lemma t64 : p76 -> p105 -> p104.
Proof.
 intros h0 h1.
 refine (mul_aa _s2 _th i61 i90 i89 h0 h1 _) ; finalize.
Qed.
Lemma l90 : s1 -> p104 (* ABS(s2 * th, [1.58819e-22, 1.55006e-06]) *).
Proof.
 intros h0.
 assert (h1 := l67 h0).
 assert (h2 := l7 h0).
 apply t64. exact h1. refine (abs_subset _th i1 i90 h2 _) ; finalize.
Qed.
Definition f124 := Float2 (300617298447218269818214090514044919153873018578553074841809411181650513585936628537827242717689347593130724451) (-374).
Definition i91 := makepairF f1 f124.
Notation p106 := (ABS _th i91). (* ABS(th, [8.67362e-19, 0.0078126]) *)
Lemma t65 : p104 -> p106 -> p103.
Proof.
 intros h0 h1.
 refine (mul_aa r68 _th i89 i91 i88 h0 h1 _) ; finalize.
Qed.
Lemma l89 : s1 -> p103 (* ABS(s2 * th * th, [1.37753e-40, 1.211e-08]) *).
Proof.
 intros h0.
 assert (h1 := l90 h0).
 assert (h2 := l7 h0).
 apply t65. exact h1. refine (abs_subset _th i1 i91 h2 _) ; finalize.
Qed.
Definition f125 := Float2 (162259276829213381405976519770113) (-106).
Definition i92 := makepairF f59 f125.
Notation p107 := (ABS r69 i92). (* ABS(1 + (1 + dl) * (1 + dl), [1.5, 2]) *)
Notation p108 := (BND r69 i92). (* BND(1 + (1 + dl) * (1 + dl), [1.5, 2]) *)
Definition i93 := makepairF f25 f34.
Notation p109 := (BND r45 i93). (* BND((1 + dl) * (1 + dl), [0.5, 1]) *)
Lemma t66 : p20 -> p109 -> p108.
Proof.
 intros h0 h1.
 refine (add r5 r45 i13 i93 i92 h0 h1 _) ; finalize.
Qed.
Lemma l92 : s1 -> p108 (* BND(1 + (1 + dl) * (1 + dl), [1.5, 2]) *).
Proof.
 intros h0.
 assert (h1 := l20 h0).
 assert (h2 := l27 h0).
 apply t66. exact h1. refine (subset r45 i19 i93 h2 _) ; finalize.
Qed.
Lemma t67 : p108 -> p107.
Proof.
 intros h0.
 refine (abs_of_bnd_p r69 i92 i92 h0 _) ; finalize.
Qed.
Lemma l91 : s1 -> p107 (* ABS(1 + (1 + dl) * (1 + dl), [1.5, 2]) *).
Proof.
 intros h0.
 assert (h1 := l92 h0).
 apply t67. exact h1.
Qed.
Lemma t68 : p103 -> p107 -> p102.
Proof.
 intros h0 h1.
 refine (mul_aa r67 r69 i88 i92 i87 h0 h1 _) ; finalize.
Qed.
Lemma l88 : s1 -> p102 (* ABS(s2 * th * th * (1 + (1 + dl) * (1 + dl)), [1.83671e-40, 2.42199e-08]) *).
Proof.
 intros h0.
 assert (h1 := l89 h0).
 assert (h2 := l91 h0).
 apply t68. exact h1. exact h2.
Qed.
Lemma t69 : p79 -> p102 -> p101.
Proof.
 intros h0 h1.
 refine (add_aa_p _s1 r66 i64 i87 i86 h0 h1 _) ; finalize.
Qed.
Lemma l87 : s1 -> p101 (* ABS(s1 + s2 * th * th * (1 + (1 + dl) * (1 + dl)), [0.0078125, 0.00833336]) *).
Proof.
 intros h0.
 assert (h1 := l65 h0).
 assert (h2 := l88 h0).
 apply t69. refine (abs_subset _s1 i59 i64 h1 _) ; finalize. exact h2.
Qed.
Lemma t70 : p97 -> p101 -> p96.
Proof.
 intros h0 h1.
 refine (mul_aa r63 r65 i82 i86 i81 h0 h1 _) ; finalize.
Qed.
Lemma l83 : s1 -> p96 (* ABS(th * th * ((1 + dl) * (1 + dl) - 1) * (s1 + s2 * th * th * (1 + (1 + dl) * (1 + dl))), [0, 1.12941e-22]) *).
Proof.
 intros h0.
 assert (h1 := l84 h0).
 assert (h2 := l87 h0).
 apply t70. exact h1. exact h2.
Qed.
Lemma t71 : p66 -> p96 -> p65.
Proof.
 intros h0 h1.
 refine (sub_aa_o r55 r62 i52 i81 i51 h0 h1 _) ; finalize.
Qed.
Lemma l57 : s1 -> p65 (* ABS(Ph * ((1 + et) * (1 + d2) - 1) - Pt * ((1 + dl) * (1 + dl) * (1 + dl) * (1 + al) - 1) - th * th * ((1 + dl) * (1 + dl) - 1) * (s1 + s2 * th * th * (1 + (1 + dl) * (1 + dl))), [0, 2.12902e-16]) *).
Proof.
 intros h0.
 assert (h1 := l58 h0).
 assert (h2 := l83 h0).
 apply t71. exact h1. exact h2.
Qed.
Lemma t72 : p64 -> p65 -> p63.
Proof.
 intros h0 h1.
 refine (abs_rewrite r49 r54 i51 h0 h1) ; finalize.
Qed.
Lemma l55 : s1 -> p63 (* ABS(Ph * (1 + et) * (1 + d2) - (1 + dl) * (1 + dl) * (1 + dl) * Pt * (1 + al), [0, 2.12902e-16]) *).
Proof.
 intros h0.
 assert (h1 := l56 h0).
 assert (h2 := l57 h0).
 apply t72. exact h1. exact h2.
Qed.
Lemma t73 : p63 -> p62.
Proof.
 intros h0.
 refine (bnd_of_abs r49 i51 i50 h0 _) ; finalize.
Qed.
Lemma l54 : s1 -> p62 (* BND(Ph * (1 + et) * (1 + d2) - (1 + dl) * (1 + dl) * (1 + dl) * Pt * (1 + al), [-2.12902e-16, 2.12902e-16]) *).
Proof.
 intros h0.
 assert (h1 := l55 h0).
 apply t73. exact h1.
Qed.
Lemma t74 : p61 -> p62 -> p60.
Proof.
 intros h0 h1.
 refine (mul_po r27 r49 i49 i50 i48 h0 h1 _) ; finalize.
Qed.
Lemma l52 : s1 -> p60 (* BND(th * th * (Ph * (1 + et) * (1 + d2) - (1 + dl) * (1 + dl) * (1 + dl) * Pt * (1 + al)), [-1.29948e-20, 1.29948e-20]) *).
Proof.
 intros h0.
 assert (h1 := l53 h0).
 assert (h2 := l54 h0).
 apply t74. exact h1. exact h2.
Qed.
Lemma t75 : p58 -> p60 -> p57.
Proof.
 intros h0 h1.
 refine (add r47 r48 i46 i48 i45 h0 h1 _) ; finalize.
Qed.
Lemma l49 : s1 -> p57 (* BND((1 + dl) * d2 + th * th * (Ph * (1 + et) * (1 + d2) - (1 + dl) * (1 + dl) * (1 + dl) * Pt * (1 + al)), [-1.29948e-20, 1.29948e-20]) *).
Proof.
 intros h0.
 assert (h1 := l50 h0).
 assert (h2 := l52 h0).
 apply t75. exact h1. exact h2.
Qed.
Notation p110 := (REL r37 r46 i40). (* REL((SN - ST) / th, (1 + dl) * d2 + th * th * (Ph * (1 + et) * (1 + d2) - (1 + dl) * (1 + dl) * (1 + dl) * Pt * (1 + al)), [0, 0]) *)
Notation p111 := (r37 = r46). (* EQL((SN - ST) / th, (1 + dl) * d2 + th * th * (Ph * (1 + et) * (1 + d2) - (1 + dl) * (1 + dl) * (1 + dl) * Pt * (1 + al))) *)
Lemma t76 : p10 -> p111.
Proof.
 intros h0.
 refine (b3 h0) ; finalize.
Qed.
Lemma l94 : s1 -> p111 (* EQL((SN - ST) / th, (1 + dl) * d2 + th * th * (Ph * (1 + et) * (1 + d2) - (1 + dl) * (1 + dl) * (1 + dl) * Pt * (1 + al))) *).
Proof.
 intros h0.
 assert (h1 := l6 h0).
 apply t76. exact h1.
Qed.
Notation p112 := (REL r46 r46 i40). (* REL((1 + dl) * d2 + th * th * (Ph * (1 + et) * (1 + d2) - (1 + dl) * (1 + dl) * (1 + dl) * Pt * (1 + al)), (1 + dl) * d2 + th * th * (Ph * (1 + et) * (1 + d2) - (1 + dl) * (1 + dl) * (1 + dl) * Pt * (1 + al)), [0, 0]) *)
Lemma t77 : p112.
Proof.
 refine (rel_refl r46 i40 _) ; finalize.
Qed.
Lemma l95 : s1 -> p112 (* REL((1 + dl) * d2 + th * th * (Ph * (1 + et) * (1 + d2) - (1 + dl) * (1 + dl) * (1 + dl) * Pt * (1 + al)), (1 + dl) * d2 + th * th * (Ph * (1 + et) * (1 + d2) - (1 + dl) * (1 + dl) * (1 + dl) * Pt * (1 + al)), [0, 0]) *).
Proof.
 intros h0.
 apply t77.
Qed.
Lemma t78 : p111 -> p112 -> p110.
Proof.
 intros h0 h1.
 refine (rel_rewrite_1 r37 r46 r46 i40 h0 h1) ; finalize.
Qed.
Lemma l93 : s1 -> p110 (* REL((SN - ST) / th, (1 + dl) * d2 + th * th * (Ph * (1 + et) * (1 + d2) - (1 + dl) * (1 + dl) * (1 + dl) * Pt * (1 + al)), [0, 0]) *).
Proof.
 intros h0.
 assert (h1 := l94 h0).
 assert (h2 := l95 h0).
 apply t78. exact h1. exact h2.
Qed.
Lemma t79 : p57 -> p110 -> p56.
Proof.
 intros h0 h1.
 refine (bnd_of_bnd_rel_o r37 r46 i45 i40 i45 h0 h1 _) ; finalize.
Qed.
Lemma l48 : s1 -> p56 (* BND((SN - ST) / th, [-1.29948e-20, 1.29948e-20]) *).
Proof.
 intros h0.
 assert (h1 := l49 h0).
 assert (h2 := l93 h0).
 apply t79. exact h1. exact h2.
Qed.
Lemma t80 : p56 -> p17 -> p55.
Proof.
 intros h0 h1.
 refine (div_op r37 r38 i45 i11 i7 h0 h1 _) ; finalize.
Qed.
Lemma l47 : s1 -> p55 (* BND((SN - ST) / th / (ST / th), [-1.2995e-20, 1.2995e-20]) *).
Proof.
 intros h0.
 assert (h1 := l48 h0).
 assert (h2 := l17 h0).
 apply t80. exact h1. exact h2.
Qed.
Lemma t81 : p9 -> p55 -> p8.
Proof.
 intros h0 h1.
 refine (bnd_rewrite r20 r36 i7 h0 h1) ; finalize.
Qed.
Lemma l4 : p7 -> s1 -> p8 (* BND((SN - ST) / ST, [-1.2995e-20, 1.2995e-20]) *).
Proof.
 intros h0 h1.
 assert (h2 := l5 h0 h1).
 assert (h3 := l47 h1).
 apply t81. exact h2. exact h3.
Qed.
Lemma l2 : p7 -> s1 -> False.
Proof.
 intros h0 h1.
 assert (h2 := l3 h1).
 assert (h3 := l4 h0 h1).
 refine (simplify (Tatom false (Abnd 0%nat i6)) Tfalse (Abnd 0%nat i7) (List.cons r20 List.nil) h3 h2 _) ; finalize.
Qed.
Notation p113 := ((f13 <= _th)%R). (* BND(th, [0, inf]) *)
Notation p114 := (BND _ST i9). (* BND(ST, [4.33681e-19, 1]) *)
Notation p115 := (BND r71 i9). (* BND(ST / th * th, [4.33681e-19, 1]) *)
Definition i94 := makepairF f1 f25.
Notation p116 := (BND _th i94). (* BND(th, [8.67362e-19, 0.5]) *)
Definition i95 := makepairF f13 f25.
Notation p117 := (BND _th i95). (* BND(th, [0, 0.5]) *)
Lemma l105 : p113 -> s1 -> p113 (* BND(th, [0, inf]) *).
Proof.
 intros h0 h1.
 assert (h2 := h0).
 exact (h2).
Qed.
Lemma l104 : p113 -> s1 -> p117 (* BND(th, [0, 0.5]) *).
Proof.
 intros h0 h1.
 assert (h2 := l29 h1).
 assert (h3 := l105 h0 h1).
 apply intersect_bh with (1 := h2) (2 := h3). finalize.
Qed.
Lemma t82 : p117 -> p12 -> p116.
Proof.
 intros h0 h1.
 refine (bnd_of_bnd_abs_p _th i95 i8 i94 h0 h1 _) ; finalize.
Qed.
Lemma l103 : p113 -> s1 -> p116 (* BND(th, [8.67362e-19, 0.5]) *).
Proof.
 intros h0 h1.
 assert (h2 := l104 h0 h1).
 assert (h3 := l7 h1).
 apply t82. exact h2. refine (abs_subset _th i1 i8 h3 _) ; finalize.
Qed.
Lemma t83 : p54 -> p116 -> p115.
Proof.
 intros h0 h1.
 refine (mul_pp r38 _th i44 i94 i9 h0 h1 _) ; finalize.
Qed.
Lemma l102 : p113 -> s1 -> p115 (* BND(ST / th * th, [4.33681e-19, 1]) *).
Proof.
 intros h0 h1.
 assert (h2 := l17 h1).
 assert (h3 := l103 h0 h1).
 apply t83. refine (subset r38 i11 i44 h2 _) ; finalize. exact h3.
Qed.
Lemma t84 : p10 -> p115 -> p114.
Proof.
 intros h0 h1.
 refine (div_xilu _ST _ i9 h0 h1) ; finalize.
Qed.
Lemma l101 : p113 -> s1 -> p114 (* BND(ST, [4.33681e-19, 1]) *).
Proof.
 intros h0 h1.
 assert (h2 := l6 h1).
 assert (h3 := l102 h0 h1).
 apply t84. exact h2. exact h3.
Qed.
Lemma t85 : p114 -> p14.
Proof.
 intros h0.
 refine (abs_of_bnd_p _ST i9 i9 h0 _) ; finalize.
Qed.
Lemma l100 : p113 -> s1 -> p14 (* ABS(ST, [4.33681e-19, 1]) *).
Proof.
 intros h0 h1.
 assert (h2 := l101 h0 h1).
 apply t85. exact h2.
Qed.
Lemma t86 : p14 -> p13.
Proof.
 intros h0.
 refine (nzr_of_abs _ST i9 h0 _) ; finalize.
Qed.
Lemma l99 : p113 -> s1 -> p13 (* NZR(ST) *).
Proof.
 intros h0 h1.
 assert (h2 := l100 h0 h1).
 apply t86. exact h2.
Qed.
Lemma t87 : p10 -> p13 -> p9.
Proof.
 intros h0 h1.
 refine (b1 h0 h1) ; finalize.
Qed.
Lemma l98 : p113 -> s1 -> p9 (* EQL((SN - ST) / ST, (SN - ST) / th / (ST / th)) *).
Proof.
 intros h0 h1.
 assert (h2 := l6 h1).
 assert (h3 := l99 h0 h1).
 apply t87. exact h2. exact h3.
Qed.
Lemma t88 : p9 -> p55 -> p8.
Proof.
 intros h0 h1.
 refine (bnd_rewrite r20 r36 i7 h0 h1) ; finalize.
Qed.
Lemma l97 : p113 -> s1 -> p8 (* BND((SN - ST) / ST, [-1.2995e-20, 1.2995e-20]) *).
Proof.
 intros h0 h1.
 assert (h2 := l98 h0 h1).
 assert (h3 := l47 h1).
 apply t88. exact h2. exact h3.
Qed.
Lemma l96 : p113 -> s1 -> False.
Proof.
 intros h0 h1.
 assert (h2 := l3 h1).
 assert (h3 := l97 h0 h1).
 refine (simplify (Tatom false (Abnd 0%nat i6)) Tfalse (Abnd 0%nat i7) (List.cons r20 List.nil) h3 h2 _) ; finalize.
Qed.
Lemma l1 : s1 -> False.
Proof.
 intros h0.
 apply (union _th f13).
 intro h1. (* [-inf, 0] *)
 apply (l2 h1 h0).
 intro h1. (* [0, inf] *)
 apply (l96 h1 h0).
Qed.
End Generated_by_Gappa.
