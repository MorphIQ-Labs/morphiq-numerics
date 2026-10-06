Require Import Gappa.Gappa_library.
Section Generated_by_Gappa.
Variable _x : R.
Notation r5 := ((_x * _x)%R).
Notation r6 := (Float1 (2)).
Notation _B := ((r5 / r6)%R).
Notation r3 := ((_x + _B)%R).
Notation r9 := ((r5 * _x)%R).
Notation _c3 := (float2R (Float2 (6004799503160661) (-55))).
Notation _c4 := (float2R (Float2 (6004799503160665) (-57))).
Notation _c5 := (float2R (Float2 (600479950321527) (-56))).
Notation _c6 := (float2R (Float2 (6405119469017259) (-62))).
Notation _c7 := (float2R (Float2 (114377043920237) (-59))).
Notation _c8 := (float2R (Float2 (1830068419841075) (-66))).
Notation _c9 := (float2R (Float2 (6721293999218467) (-71))).
Notation r27 := ((_x * _c9)%R).
Notation r25 := ((_c8 + r27)%R).
Notation r24 := ((_x * r25)%R).
Notation r22 := ((_c7 + r24)%R).
Notation r21 := ((_x * r22)%R).
Notation r19 := ((_c6 + r21)%R).
Notation r18 := ((_x * r19)%R).
Notation r16 := ((_c5 + r18)%R).
Notation r15 := ((_x * r16)%R).
Notation r13 := ((_c4 + r15)%R).
Notation r12 := ((_x * r13)%R).
Notation _W := ((_c3 + r12)%R).
Notation _T := ((r9 * _W)%R).
Notation r30 := (Float1 (1)).
Variable _al : R.
Notation r29 := ((r30 + _al)%R).
Notation r7 := ((_T * r29)%R).
Notation _L := ((r3 + r7)%R).
Variable _d1 : R.
Notation r37 := ((r30 + _d1)%R).
Notation _P1 := ((r3 * r37)%R).
Variable _et : R.
Notation r40 := ((r30 + _et)%R).
Notation _t := ((_T * r40)%R).
Notation r35 := ((_P1 + _t)%R).
Variable _d2 : R.
Notation r42 := ((r30 + _d2)%R).
Notation _P := ((r35 * r42)%R).
Notation r33 := ((_P - _L)%R).
Notation r32 := ((r33 / _L)%R).
Notation r45 := ((r33 / _x)%R).
Notation r46 := ((_L / _x)%R).
Notation r44 := ((r45 / r46)%R).
Hypothesis a1 : (_x <> 0)%R -> (_L <> 0)%R -> r32 = r44.
Lemma b1 : NZR _x -> NZR _L -> r32 = r44.
 intros h0 h1.
 apply a1.
 exact h0.
 exact h1.
Qed.
Notation r49 := ((_x / r6)%R).
Notation r48 := ((r30 + r49)%R).
Notation r51 := ((r5 * _W)%R).
Notation r50 := ((r51 * r29)%R).
Notation r47 := ((r48 + r50)%R).
Hypothesis a2 : (_x <> 0)%R -> r46 = r47.
Lemma b2 : NZR _x -> r46 = r47.
 intros h0.
 apply a2.
 exact h0.
Qed.
Notation r55 := ((_et - _al)%R).
Notation r54 := ((r51 * r55)%R).
Notation r56 := ((r48 * _d1)%R).
Notation r53 := ((r54 + r56)%R).
Notation r59 := ((r48 * r37)%R).
Notation r60 := ((r51 * r40)%R).
Notation r58 := ((r59 + r60)%R).
Notation r57 := ((r58 * _d2)%R).
Notation r52 := ((r53 + r57)%R).
Hypothesis a3 : (_x <> 0)%R -> r45 = r52.
Lemma b3 : NZR _x -> r45 = r52.
 intros h0.
 apply a3.
 exact h0.
Qed.
Notation r61 := ((Rabs _x)%R).
Definition f1 := Float2 (1) (-54).
Definition f2 := Float2 (322782267660814808470425758868045285495962955985970070793237551831323569011153956065183521018158540984620470857862225771) (-402).
Definition i1 := makepairF f1 f2.
Notation p1 := (BND r61 i1). (* BND(|x|, [5.55112e-17, 0.0312501]) *)
Definition f3 := Float2 (-1) (-50).
Definition f4 := Float2 (1) (-50).
Definition i2 := makepairF f3 f4.
Notation p2 := (BND _et i2). (* BND(et, [-8.88178e-16, 8.88178e-16]) *)
Definition s5 := (p1 /\ p2).
Definition f5 := Float2 (-259) (-62).
Definition f6 := Float2 (259) (-62).
Definition i3 := makepairF f5 f6.
Notation p3 := (BND _al i3). (* BND(al, [-5.61617e-17, 5.61617e-17]) *)
Definition s4 := (s5 /\ p3).
Definition f7 := Float2 (-97) (-111).
Definition f8 := Float2 (97) (-111).
Definition i4 := makepairF f7 f8.
Notation p4 := (BND _d1 i4). (* BND(d1, [-3.7363e-32, 3.7363e-32]) *)
Definition s3 := (s4 /\ p4).
Definition f9 := Float2 (-1) (-105).
Definition f10 := Float2 (1) (-105).
Definition i5 := makepairF f9 f10.
Notation p5 := (BND _d2 i5). (* BND(d2, [-2.46519e-32, 2.46519e-32]) *)
Definition s2 := (s3 /\ p5).
Definition f11 := Float2 (-13) (-66).
Definition f12 := Float2 (13) (-66).
Definition i6 := makepairF f11 f12.
Notation p6 := (BND r32 i6). (* BND((P - L) / L, [-1.76183e-19, 1.76183e-19]) *)
Definition s6 := (not p6).
Definition s1 := (s2 /\ s6).
Definition f13 := Float2 (0) (0).
Notation p7 := ((_x <= f13)%R). (* BND(x, [-inf, 0]) *)
Lemma l3 : s1 -> s6.
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj2 h1).
Qed.
Definition f14 := Float2 (-937018899992335795529700674631369834456134329035232338251559242208831036901179393794882600843506219479622637811084366793) (-461).
Definition f15 := Float2 (937018899992335795529700674631369834456134329035232338251559242208831036901179393794882600843506219479622637811084366793) (-461).
Definition i7 := makepairF f14 f15.
Notation p8 := (BND r32 i7). (* BND((P - L) / L, [-1.57369e-19, 1.57369e-19]) *)
Notation p9 := (r32 = r44). (* EQL((P - L) / L, (P - L) / x / (L / x)) *)
Notation p10 := (NZR _x). (* NZR(x) *)
Notation p11 := (ABS _x i1). (* ABS(x, [5.55112e-17, 0.0312501]) *)
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
Lemma l8 : s1 -> p1 (* BND(|x|, [5.55112e-17, 0.0312501]) *).
Proof.
 intros h0.
 assert (h1 := l9 h0).
 exact (proj1 h1).
Qed.
Lemma t1 : p1 -> p11.
Proof.
 intros h0.
 refine (abs_of_uabs _x i1 h0 _) ; finalize.
Qed.
Lemma l7 : s1 -> p11 (* ABS(x, [5.55112e-17, 0.0312501]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 apply t1. exact h1.
Qed.
Definition f16 := Float2 (1) (0).
Definition i8 := makepairF f1 f16.
Notation p12 := (ABS _x i8). (* ABS(x, [5.55112e-17, 1]) *)
Lemma t2 : p12 -> p10.
Proof.
 intros h0.
 refine (nzr_of_abs _x i8 h0 _) ; finalize.
Qed.
Lemma l6 : s1 -> p10 (* NZR(x) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 apply t2. refine (abs_subset _x i1 i8 h1 _) ; finalize.
Qed.
Notation p13 := (NZR _L). (* NZR(L) *)
Definition f17 := Float2 (1) (-55).
Definition i9 := makepairF f17 f16.
Notation p14 := (ABS _L i9). (* ABS(L, [2.77556e-17, 1]) *)
Definition f18 := Float2 (-1) (0).
Definition f19 := Float2 (-2541902094629306738597115952144507529411978774769123543532742720236800234255698246083672197057050909583698841932997770387) (-454).
Definition i10 := makepairF f18 f19.
Notation p15 := (BND _L i10). (* BND(L, [-1, -5.46438e-17]) *)
Notation r62 := ((r46 * _x)%R).
Notation p16 := (BND r62 i10). (* BND(L / x * x, [-1, -5.46438e-17]) *)
Definition f20 := Float2 (2541902094629306738597115952144507529411978774769123543532742720236800234255698246083672197057050909583698841932997770387) (-400).
Definition f21 := Float2 (1) (1).
Definition i11 := makepairF f20 f21.
Notation p17 := (BND r46 i11). (* BND(L / x, [0.984375, 2]) *)
Notation p18 := (BND r47 i11). (* BND(1 + x / 2 + x * x * W * (1 + al), [0.984375, 2]) *)
Definition f22 := Float2 (1270951047314653369298557976072253106821355211665488626990752331280866087945223475060748706576434006906412806557757357577) (-399).
Definition f23 := Float2 (149077417378550219422932195349262516118454934844946238381442870520434272983904716007702591776217539578452757) (-356).
Definition i12 := makepairF f22 f23.
Notation p19 := (BND r48 i12). (* BND(1 + x / 2, [0.984375, 1.01563]) *)
Definition i13 := makepairF f16 f16.
Notation p20 := (BND r30 i13). (* BND(1, [1, 1]) *)
Lemma t3 : p20.
Proof.
 refine (constant1 _ i13 _) ; finalize.
Qed.
Lemma l20 : s1 -> p20 (* BND(1, [1, 1]) *).
Proof.
 intros h0.
 apply t3.
Qed.
Definition f24 := Float2 (-20173891728800925529401609929252830343497684749123129424577346989457723063197122254073970063634908811538779428616389111) (-399).
Definition f25 := Float2 (2293505955185642679839658049928951907474775538176246462237184799671208914241688291221404377169495638956821) (-356).
Definition i14 := makepairF f24 f25.
Notation p21 := (BND r49 i14). (* BND(x / 2, [-0.0156251, 0.0156251]) *)
Definition f26 := Float2 (-322782267660814808470425758868045285495962955985970070793237551831323569011153956065183521018158540984620470857862225771) (-402).
Definition f27 := Float2 (20173891728800925529401609929252830343497684749123129424577346989457723063197122254073970063634908811538779428616389111) (-398).
Definition i15 := makepairF f26 f27.
Notation p22 := (BND _x i15). (* BND(x, [-0.0312501, 0.0312501]) *)
Lemma t4 : p11 -> p22.
Proof.
 intros h0.
 refine (bnd_of_abs _x i1 i15 h0 _) ; finalize.
Qed.
Lemma l22 : s1 -> p22 (* BND(x, [-0.0312501, 0.0312501]) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 apply t4. exact h1.
Qed.
Definition i16 := makepairF f21 f21.
Notation p23 := (BND r6 i16). (* BND(2, [2, 2]) *)
Lemma t5 : p23.
Proof.
 refine (constant1 _ i16 _) ; finalize.
Qed.
Lemma l23 : s1 -> p23 (* BND(2, [2, 2]) *).
Proof.
 intros h0.
 apply t5.
Qed.
Definition f28 := Float2 (-20173891728800925529401609929252830343497684749123129424577346989457723063197122254073970063634908811538779428616389111) (-398).
Definition f29 := Float2 (2293505955185642679839658049928951907474775538176246462237184799671208914241688291221404377169495638956821) (-355).
Definition i17 := makepairF f28 f29.
Notation p24 := (BND _x i17). (* BND(x, [-0.0312501, 0.0312501]) *)
Lemma t6 : p24 -> p23 -> p21.
Proof.
 intros h0 h1.
 refine (div_op _x r6 i17 i16 i14 h0 h1 _) ; finalize.
Qed.
Lemma l21 : s1 -> p21 (* BND(x / 2, [-0.0156251, 0.0156251]) *).
Proof.
 intros h0.
 assert (h1 := l22 h0).
 assert (h2 := l23 h0).
 apply t6. refine (subset _x i15 i17 h1 _) ; finalize. exact h2.
Qed.
Lemma t7 : p20 -> p21 -> p19.
Proof.
 intros h0 h1.
 refine (add r30 r49 i13 i14 i12 h0 h1 _) ; finalize.
Qed.
Lemma l19 : s1 -> p19 (* BND(1 + x / 2, [0.984375, 1.01563]) *).
Proof.
 intros h0.
 assert (h1 := l20 h0).
 assert (h2 := l21 h0).
 apply t7. exact h1. exact h2.
Qed.
Definition f30 := Float2 (1315769268351438146289551238057675068058365251295962174783904182895770873228817483055233) (-400).
Definition f31 := Float2 (105898729371829569914279047585428125755071905275591285365572618170354498401299823436301766985733643981660865249336053) (-398).
Definition i18 := makepairF f30 f31.
Notation p25 := (BND r50 i18). (* BND(x * x * W * (1 + al), [5.09544e-34, 0.000164041]) *)
Definition f32 := Float2 (5263077073405752880741416073990400924323344005139139906211452250517031956984403863317789) (-402).
Definition f33 := Float2 (1735044782028055576032531034254815205381127594980965288449763766226404402898943396303879405930627955065012411350581271227) (-412).
Definition i19 := makepairF f32 f33.
Notation p26 := (BND r51 i19). (* BND(x * x * W, [5.09544e-34, 0.000164041]) *)
Definition f34 := Float2 (1) (-108).
Definition f35 := Float2 (1291133202256285292311251456921894652963506172269716903589856360765957716986299167031371718421703196367806486573475883721) (-409).
Definition i20 := makepairF f34 f35.
Notation p27 := (BND r5 i20). (* BND(x * x, [3.08149e-33, 0.000976569]) *)
Lemma t8 : p11 -> p27.
Proof.
 intros h0.
 refine (square _x i1 i20 h0 _) ; finalize.
Qed.
Lemma l26 : s1 -> p27 (* BND(x * x, [3.08149e-33, 0.000976569]) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 apply t8. exact h1.
Qed.
Definition f36 := Float2 (5263077073405752880741416073990400924323344005139139906211452250517031956984403863317789) (-294).
Definition f37 := Float2 (1735033677794750944765866283036201302954497984851608178792539026225800958144259071234426292712914067177602234648380874705) (-402).
Definition i21 := makepairF f36 f37.
Notation p28 := (BND _W i21). (* BND(W, [0.165356, 0.167977]) *)
Definition f38 := Float2 (6004799503160661) (-55).
Definition i22 := makepairF f38 f38.
Notation p29 := (BND _c3 i22). (* BND(c3, [0.166667, 0.166667]) *)
Lemma t9 : p29.
Proof.
 refine (constant2 _ i22 _) ; finalize.
Qed.
Lemma l28 : s1 -> p29 (* BND(c3, [0.166667, 0.166667]) *).
Proof.
 intros h0.
 apply t9.
Qed.
Definition f39 := Float2 (-41704114965304341108150443178299772865271479546149775239514023740176324214918593598179) (-294).
Definition f40 := Float2 (13533759070145313891029167953839703852231427219081703428974003877082699199233249269782560879689182471106499588452818897) (-402).
Definition i23 := makepairF f39 f40.
Notation p30 := (BND r12 i23). (* BND(x * (c4 + x * (c5 + x * (c6 + x * (c7 + x * (c8 + x * c9))))), [-0.00131027, 0.00131027]) *)
Definition f41 := Float2 (1) (-5).
Definition f42 := Float2 (13533715762254874675430206577178656880529409524971223521058736489125933996244461287506440859078433420119555205876160093) (-397).
Definition i24 := makepairF f41 f42.
Notation p31 := (BND r13 i24). (* BND(c4 + x * (c5 + x * (c6 + x * (c7 + x * (c8 + x * c9)))), [0.03125, 0.0419284]) *)
Definition f43 := Float2 (5) (-7).
Definition f44 := Float2 (6004799503160665) (-57).
Definition i25 := makepairF f43 f44.
Notation p32 := (BND _c4 i25). (* BND(c4, [0.0390625, 0.0416667]) *)
Lemma t10 : p32.
Proof.
 refine (constant2 _ i25 _) ; finalize.
Qed.
Lemma l31 : s1 -> p32 (* BND(c4, [0.0390625, 0.0416667]) *).
Proof.
 intros h0.
 apply t10.
Qed.
Definition f45 := Float2 (-1) (-7).
Definition f46 := Float2 (84497647218884225241572904380864657773829769689997945698895813428432998280043198240176983487582484840084189292009053) (-397).
Definition i26 := makepairF f45 f46.
Notation p33 := (BND r15 i26). (* BND(x * (c5 + x * (c6 + x * (c7 + x * (c8 + x * c9)))), [-0.0078125, 0.00026178]) *)
Definition f47 := Float2 (1) (-7).
Definition f48 := Float2 (5407832116945816188848861564018333238858740912188949520090867768642852232795619741388154501110875474963868230310242399) (-398).
Definition i27 := makepairF f47 f48.
Notation p34 := (BND r16 i27). (* BND(c5 + x * (c6 + x * (c7 + x * (c8 + x * c9))), [0.0078125, 0.00837693]) *)
Definition f49 := Float2 (17) (-11).
Definition f50 := Float2 (600479950321527) (-56).
Definition i28 := makepairF f49 f50.
Notation p35 := (BND _c5 i28). (* BND(c5, [0.00830078, 0.00833333]) *)
Lemma t11 : p35.
Proof.
 refine (constant2 _ i28 _) ; finalize.
Qed.
Lemma l34 : s1 -> p35 (* BND(c5, [0.00830078, 0.00833333]) *).
Proof.
 intros h0.
 apply t11.
Qed.
Definition f51 := Float2 (-1) (-11).
Definition f52 := Float2 (28144870882499504114760495332220695464333050153726308996332283222566271666601363631331875505525974644041381053802591) (-398).
Definition i29 := makepairF f51 f52.
Notation p36 := (BND r18 i29). (* BND(x * (c6 + x * (c7 + x * (c8 + x * c9))), [-0.000488281, 4.35974e-05]) *)
Definition f53 := Float2 (1) (-10).
Definition f54 := Float2 (14072390409600441335967972568598128218156226976936828300315580601425211272624609416915803622191396309552499958901427) (-392).
Definition i30 := makepairF f53 f54.
Notation p37 := (BND r19 i30). (* BND(c6 + x * (c7 + x * (c8 + x * c9)), [0.000976562, 0.00139511]) *)
Definition f55 := Float2 (5) (-12).
Definition f56 := Float2 (6405119469017259) (-62).
Definition i31 := makepairF f55 f56.
Notation p38 := (BND _c6 i31). (* BND(c6, [0.0012207, 0.00138889]) *)
Lemma t12 : p38.
Proof.
 refine (constant2 _ i31 _) ; finalize.
Qed.
Lemma l37 : s1 -> p38 (* BND(c6, [0.0012207, 0.00138889]) *).
Proof.
 intros h0.
 apply t12.
Qed.
Definition f57 := Float2 (-1) (-12).
Definition f58 := Float2 (62788208670661098451472942638446842024456367122432912604166563540612747181715899613848104404076185692959616953011) (-392).
Definition i32 := makepairF f57 f58.
Notation p39 := (BND r21 i32). (* BND(x * (c7 + x * (c8 + x * c9)), [-0.000244141, 6.22472e-06]) *)
Definition f59 := Float2 (1) (-13).
Definition f60 := Float2 (125576015498072603070616059305503906436412137726025101928006957458961625686229603292965671318004153772627161499105) (-388).
Definition i33 := makepairF f59 f60.
Notation p40 := (BND r22 i33). (* BND(c7 + x * (c8 + x * c9), [0.00012207, 0.00019919]) *)
Definition f61 := Float2 (3) (-14).
Definition f62 := Float2 (114377043920237) (-59).
Definition i34 := makepairF f61 f62.
Notation p41 := (BND _c7 i34). (* BND(c7, [0.000183105, 0.000198413]) *)
Lemma t13 : p41.
Proof.
 refine (constant2 _ i34 _) ; finalize.
Qed.
Lemma l40 : s1 -> p41 (* BND(c7, [0.000183105, 0.000198413]) *).
Proof.
 intros h0.
 apply t13.
Qed.
Definition f63 := Float2 (-1) (-14).
Definition f64 := Float2 (490379391534220187810569556800767967033786439993569514965825550647058012088651458997387958569886421063954580961) (-388).
Definition i35 := makepairF f63 f64.
Notation p42 := (BND r24 i35). (* BND(x * (c8 + x * c9), [-6.10352e-05, 7.77846e-07]) *)
Definition f65 := Float2 (1) (-16).
Definition f66 := Float2 (3923022578601509977652627965996652546982141177096789410000492403600772574236974113661939950351250244510854212953) (-386).
Definition i36 := makepairF f65 f66.
Notation p43 := (BND r25 i36). (* BND(c8 + x * c9, [1.52588e-05, 2.4891e-05]) *)
Definition f67 := Float2 (3) (-17).
Definition f68 := Float2 (1830068419841075) (-66).
Definition i37 := makepairF f67 f68.
Notation p44 := (BND _c8 i37). (* BND(c8, [2.28882e-05, 2.48021e-05]) *)
Lemma t14 : p44.
Proof.
 refine (constant2 _ i37 _) ; finalize.
Qed.
Lemma l43 : s1 -> p44 (* BND(c8, [2.28882e-05, 2.48021e-05]) *).
Proof.
 intros h0.
 apply t14.
Qed.
Definition f69 := Float2 (-1) (-17).
Definition f70 := Float2 (14020158972708557885631411165864881156506853953930015030417526163136867307910265613175059603727213647329553753) (-386).
Definition i38 := makepairF f69 f70.
Notation p45 := (BND r27 i38). (* BND(x * c9, [-7.62939e-06, 8.89559e-08]) *)
Definition f71 := Float2 (1) (-19).
Definition f72 := Float2 (6721293999218467) (-71).
Definition i39 := makepairF f71 f72.
Notation p46 := (BND _c9 i39). (* BND(c9, [1.90735e-06, 2.84658e-06]) *)
Lemma t15 : p46.
Proof.
 refine (constant2 _ i39 _) ; finalize.
Qed.
Lemma l45 : s1 -> p46 (* BND(c9, [1.90735e-06, 2.84658e-06]) *).
Proof.
 intros h0.
 apply t15.
Qed.
Definition f73 := Float2 (9394200392440392416623239372508987013016680604369905509323508939453271712733955240842872328886254137167138713) (-367).
Definition i40 := makepairF f18 f73.
Notation p47 := (BND _x i40). (* BND(x, [-1, 0.0312501]) *)
Lemma t16 : p47 -> p46 -> p45.
Proof.
 intros h0 h1.
 refine (mul_op _x _c9 i40 i39 i38 h0 h1 _) ; finalize.
Qed.
Lemma l44 : s1 -> p45 (* BND(x * c9, [-7.62939e-06, 8.89559e-08]) *).
Proof.
 intros h0.
 assert (h1 := l22 h0).
 assert (h2 := l45 h0).
 apply t16. refine (subset _x i15 i40 h1 _) ; finalize. exact h2.
Qed.
Lemma t17 : p44 -> p45 -> p43.
Proof.
 intros h0 h1.
 refine (add _c8 r27 i37 i38 i36 h0 h1 _) ; finalize.
Qed.
Lemma l42 : s1 -> p43 (* BND(c8 + x * c9, [1.52588e-05, 2.4891e-05]) *).
Proof.
 intros h0.
 assert (h1 := l43 h0).
 assert (h2 := l44 h0).
 apply t17. exact h1. exact h2.
Qed.
Definition f74 := Float2 (2404915300464740458655549279362300675332270234718695810386818288500037558459892541655775316194881059114787510469) (-375).
Definition i41 := makepairF f18 f74.
Notation p48 := (BND _x i41). (* BND(x, [-1, 0.0312501]) *)
Lemma t18 : p48 -> p43 -> p42.
Proof.
 intros h0 h1.
 refine (mul_op _x r25 i41 i36 i35 h0 h1 _) ; finalize.
Qed.
Lemma l41 : s1 -> p42 (* BND(x * (c8 + x * c9), [-6.10352e-05, 7.77846e-07]) *).
Proof.
 intros h0.
 assert (h1 := l22 h0).
 assert (h2 := l42 h0).
 apply t18. refine (subset _x i15 i41 h1 _) ; finalize. exact h2.
Qed.
Lemma t19 : p41 -> p42 -> p40.
Proof.
 intros h0 h1.
 refine (add _c7 r24 i34 i35 i33 h0 h1 _) ; finalize.
Qed.
Lemma l39 : s1 -> p40 (* BND(c7 + x * (c8 + x * c9), [0.00012207, 0.00019919]) *).
Proof.
 intros h0.
 assert (h1 := l40 h0).
 assert (h2 := l41 h0).
 apply t19. exact h1. exact h2.
Qed.
Definition f75 := Float2 (76957289614871694676977576939593621610632647510998265932378185232001201870716561332984810118236193891673200334993) (-380).
Definition i42 := makepairF f18 f75.
Notation p49 := (BND _x i42). (* BND(x, [-1, 0.0312501]) *)
Lemma t20 : p49 -> p40 -> p39.
Proof.
 intros h0 h1.
 refine (mul_op _x r22 i42 i33 i32 h0 h1 _) ; finalize.
Qed.
Lemma l38 : s1 -> p39 (* BND(x * (c7 + x * (c8 + x * c9)), [-0.000244141, 6.22472e-06]) *).
Proof.
 intros h0.
 assert (h1 := l22 h0).
 assert (h2 := l39 h0).
 apply t20. refine (subset _x i15 i42 h1 _) ; finalize. exact h2.
Qed.
Lemma t21 : p38 -> p39 -> p37.
Proof.
 intros h0 h1.
 refine (add _c6 r21 i31 i32 i30 h0 h1 _) ; finalize.
Qed.
Lemma l36 : s1 -> p37 (* BND(c6 + x * (c7 + x * (c8 + x * c9)), [0.000976562, 0.00139511]) *).
Proof.
 intros h0.
 assert (h1 := l37 h0).
 assert (h2 := l38 h0).
 apply t21. exact h1. exact h2.
Qed.
Definition f76 := Float2 (-1) (-2).
Definition f77 := Float2 (39402132282814307674612519393071934264643915525631112157377630838784615357806879402488222780536931272536678571516385) (-389).
Definition i43 := makepairF f76 f77.
Notation p50 := (BND _x i43). (* BND(x, [-0.25, 0.0312501]) *)
Lemma t22 : p50 -> p37 -> p36.
Proof.
 intros h0 h1.
 refine (mul_op _x r19 i43 i30 i29 h0 h1 _) ; finalize.
Qed.
Lemma l35 : s1 -> p36 (* BND(x * (c6 + x * (c7 + x * (c8 + x * c9))), [-0.000488281, 4.35974e-05]) *).
Proof.
 intros h0.
 assert (h1 := l22 h0).
 assert (h2 := l36 h0).
 apply t22. refine (subset _x i15 i43 h1 _) ; finalize. exact h2.
Qed.
Lemma t23 : p35 -> p36 -> p34.
Proof.
 intros h0 h1.
 refine (add _c5 r18 i28 i29 i27 h0 h1 _) ; finalize.
Qed.
Lemma l33 : s1 -> p34 (* BND(c5 + x * (c6 + x * (c7 + x * (c8 + x * c9))), [0.0078125, 0.00837693]) *).
Proof.
 intros h0.
 assert (h1 := l34 h0).
 assert (h2 := l35 h0).
 apply t23. exact h1. exact h2.
Qed.
Definition f78 := Float2 (-1) (-1).
Definition i44 := makepairF f78 f27.
Notation p51 := (BND _x i44). (* BND(x, [-0.5, 0.0312501]) *)
Lemma t24 : p51 -> p34 -> p33.
Proof.
 intros h0 h1.
 refine (mul_op _x r16 i44 i27 i26 h0 h1 _) ; finalize.
Qed.
Lemma l32 : s1 -> p33 (* BND(x * (c5 + x * (c6 + x * (c7 + x * (c8 + x * c9)))), [-0.0078125, 0.00026178]) *).
Proof.
 intros h0.
 assert (h1 := l22 h0).
 assert (h2 := l33 h0).
 apply t24. refine (subset _x i15 i44 h1 _) ; finalize. exact h2.
Qed.
Lemma t25 : p32 -> p33 -> p31.
Proof.
 intros h0 h1.
 refine (add _c4 r15 i25 i26 i24 h0 h1 _) ; finalize.
Qed.
Lemma l30 : s1 -> p31 (* BND(c4 + x * (c5 + x * (c6 + x * (c7 + x * (c8 + x * c9)))), [0.03125, 0.0419284]) *).
Proof.
 intros h0.
 assert (h1 := l31 h0).
 assert (h2 := l32 h0).
 apply t25. exact h1. exact h2.
Qed.
Definition f79 := Float2 (-62165603480517894184079643171251863740893059032128783619144973297235694390365476954983) (-290).
Definition i45 := makepairF f79 f27.
Notation p52 := (BND _x i45). (* BND(x, [-0.0312501, 0.0312501]) *)
Lemma t26 : p52 -> p31 -> p30.
Proof.
 intros h0 h1.
 refine (mul_op _x r13 i45 i24 i23 h0 h1 _) ; finalize.
Qed.
Lemma l29 : s1 -> p30 (* BND(x * (c4 + x * (c5 + x * (c6 + x * (c7 + x * (c8 + x * c9))))), [-0.00131027, 0.00131027]) *).
Proof.
 intros h0.
 assert (h1 := l22 h0).
 assert (h2 := l30 h0).
 apply t26. refine (subset _x i15 i45 h1 _) ; finalize. exact h2.
Qed.
Lemma t27 : p29 -> p30 -> p28.
Proof.
 intros h0 h1.
 refine (add _c3 r12 i22 i23 i21 h0 h1 _) ; finalize.
Qed.
Lemma l27 : s1 -> p28 (* BND(W, [0.165356, 0.167977]) *).
Proof.
 intros h0.
 assert (h1 := l28 h0).
 assert (h2 := l29 h0).
 apply t27. exact h1. exact h2.
Qed.
Lemma t28 : p27 -> p28 -> p26.
Proof.
 intros h0 h1.
 refine (mul_pp r5 _W i20 i21 i19 h0 h1 _) ; finalize.
Qed.
Lemma l25 : s1 -> p26 (* BND(x * x * W, [5.09544e-34, 0.000164041]) *).
Proof.
 intros h0.
 assert (h1 := l26 h0).
 assert (h2 := l27 h0).
 apply t28. exact h1. exact h2.
Qed.
Definition f80 := Float2 (4611686018427387645) (-62).
Definition f81 := Float2 (4611686018427388163) (-62).
Definition i46 := makepairF f80 f81.
Notation p53 := (BND r29 i46). (* BND(1 + al, [1, 1]) *)
Lemma l47 : s1 -> p3 (* BND(al, [-5.61617e-17, 5.61617e-17]) *).
Proof.
 intros h0.
 assert (h1 := l10 h0).
 exact (proj2 h1).
Qed.
Lemma t29 : p20 -> p3 -> p53.
Proof.
 intros h0 h1.
 refine (add r30 _al i13 i3 i46 h0 h1 _) ; finalize.
Qed.
Lemma l46 : s1 -> p53 (* BND(1 + al, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l20 h0).
 assert (h2 := l47 h0).
 apply t29. exact h1. exact h2.
Qed.
Definition f82 := Float2 (1694379669949273023469268588139467974005007416973598914501722427955473049705999410453007232354128862368176182959552023) (-402).
Definition i47 := makepairF f32 f82.
Notation p54 := (BND r51 i47). (* BND(x * x * W, [5.09544e-34, 0.000164041]) *)
Lemma t30 : p54 -> p53 -> p25.
Proof.
 intros h0 h1.
 refine (mul_pp r51 r29 i47 i46 i18 h0 h1 _) ; finalize.
Qed.
Lemma l24 : s1 -> p25 (* BND(x * x * W * (1 + al), [5.09544e-34, 0.000164041]) *).
Proof.
 intros h0.
 assert (h1 := l25 h0).
 assert (h2 := l46 h0).
 apply t30. refine (subset r51 i19 i47 h1 _) ; finalize. exact h2.
Qed.
Definition f83 := Float2 (3) (-1).
Definition i48 := makepairF f22 f83.
Notation p55 := (BND r48 i48). (* BND(1 + x / 2, [0.984375, 1.5]) *)
Definition f84 := Float2 (1) (-1).
Definition i49 := makepairF f30 f84.
Notation p56 := (BND r50 i49). (* BND(x * x * W * (1 + al), [5.09544e-34, 0.5]) *)
Lemma t31 : p55 -> p56 -> p18.
Proof.
 intros h0 h1.
 refine (add r48 r50 i48 i49 i11 h0 h1 _) ; finalize.
Qed.
Lemma l18 : s1 -> p18 (* BND(1 + x / 2 + x * x * W * (1 + al), [0.984375, 2]) *).
Proof.
 intros h0.
 assert (h1 := l19 h0).
 assert (h2 := l24 h0).
 apply t31. refine (subset r48 i12 i48 h1 _) ; finalize. refine (subset r50 i18 i49 h2 _) ; finalize.
Qed.
Definition i50 := makepairF f13 f13.
Notation p57 := (REL r46 r47 i50). (* REL(L / x, 1 + x / 2 + x * x * W * (1 + al), [0, 0]) *)
Notation p58 := (r46 = r47). (* EQL(L / x, 1 + x / 2 + x * x * W * (1 + al)) *)
Lemma t32 : p10 -> p58.
Proof.
 intros h0.
 refine (b2 h0) ; finalize.
Qed.
Lemma l49 : s1 -> p58 (* EQL(L / x, 1 + x / 2 + x * x * W * (1 + al)) *).
Proof.
 intros h0.
 assert (h1 := l6 h0).
 apply t32. exact h1.
Qed.
Notation p59 := (REL r47 r47 i50). (* REL(1 + x / 2 + x * x * W * (1 + al), 1 + x / 2 + x * x * W * (1 + al), [0, 0]) *)
Lemma t33 : p59.
Proof.
 refine (rel_refl r47 i50 _) ; finalize.
Qed.
Lemma l50 : s1 -> p59 (* REL(1 + x / 2 + x * x * W * (1 + al), 1 + x / 2 + x * x * W * (1 + al), [0, 0]) *).
Proof.
 intros h0.
 apply t33.
Qed.
Lemma t34 : p58 -> p59 -> p57.
Proof.
 intros h0 h1.
 refine (rel_rewrite_1 r46 r47 r47 i50 h0 h1) ; finalize.
Qed.
Lemma l48 : s1 -> p57 (* REL(L / x, 1 + x / 2 + x * x * W * (1 + al), [0, 0]) *).
Proof.
 intros h0.
 assert (h1 := l49 h0).
 assert (h2 := l50 h0).
 apply t34. exact h1. exact h2.
Qed.
Lemma t35 : p18 -> p57 -> p17.
Proof.
 intros h0 h1.
 refine (bnd_of_bnd_rel_p r46 r47 i11 i50 i11 h0 h1 _) ; finalize.
Qed.
Lemma l17 : s1 -> p17 (* BND(L / x, [0.984375, 2]) *).
Proof.
 intros h0.
 assert (h1 := l18 h0).
 assert (h2 := l48 h0).
 apply t35. exact h1. exact h2.
Qed.
Definition f85 := Float2 (-1) (-54).
Definition i51 := makepairF f78 f85.
Notation p60 := (BND _x i51). (* BND(x, [-0.5, -5.55112e-17]) *)
Definition i52 := makepairF f26 f13.
Notation p61 := (BND _x i52). (* BND(x, [-0.0312501, 0]) *)
Lemma l53 : p7 -> s1 -> p7 (* BND(x, [-inf, 0]) *).
Proof.
 intros h0 h1.
 assert (h2 := h0).
 exact (h2).
Qed.
Lemma l52 : p7 -> s1 -> p61 (* BND(x, [-0.0312501, 0]) *).
Proof.
 intros h0 h1.
 assert (h2 := l53 h0 h1).
 assert (h3 := l22 h1).
 apply intersect_hb with (1 := h2) (2 := h3). finalize.
Qed.
Definition i53 := makepairF f78 f13.
Notation p62 := (BND _x i53). (* BND(x, [-0.5, 0]) *)
Lemma t36 : p62 -> p12 -> p60.
Proof.
 intros h0 h1.
 refine (bnd_of_bnd_abs_n _x i53 i8 i51 h0 h1 _) ; finalize.
Qed.
Lemma l51 : p7 -> s1 -> p60 (* BND(x, [-0.5, -5.55112e-17]) *).
Proof.
 intros h0 h1.
 assert (h2 := l52 h0 h1).
 assert (h3 := l7 h1).
 apply t36. refine (subset _x i52 i53 h2 _) ; finalize. refine (abs_subset _x i1 i8 h3 _) ; finalize.
Qed.
Lemma t37 : p17 -> p60 -> p16.
Proof.
 intros h0 h1.
 refine (mul_pn r46 _x i11 i51 i10 h0 h1 _) ; finalize.
Qed.
Lemma l16 : p7 -> s1 -> p16 (* BND(L / x * x, [-1, -5.46438e-17]) *).
Proof.
 intros h0 h1.
 assert (h2 := l17 h1).
 assert (h3 := l51 h0 h1).
 apply t37. exact h2. exact h3.
Qed.
Lemma t38 : p10 -> p16 -> p15.
Proof.
 intros h0 h1.
 refine (div_xilu _L _ i10 h0 h1) ; finalize.
Qed.
Lemma l15 : p7 -> s1 -> p15 (* BND(L, [-1, -5.46438e-17]) *).
Proof.
 intros h0 h1.
 assert (h2 := l6 h1).
 assert (h3 := l16 h0 h1).
 apply t38. exact h2. exact h3.
Qed.
Definition f86 := Float2 (-1) (-55).
Definition i54 := makepairF f18 f86.
Notation p63 := (BND _L i54). (* BND(L, [-1, -2.77556e-17]) *)
Lemma t39 : p63 -> p14.
Proof.
 intros h0.
 refine (abs_of_bnd_n _L i54 i9 h0 _) ; finalize.
Qed.
Lemma l14 : p7 -> s1 -> p14 (* ABS(L, [2.77556e-17, 1]) *).
Proof.
 intros h0 h1.
 assert (h2 := l15 h0 h1).
 apply t39. refine (subset _L i10 i54 h2 _) ; finalize.
Qed.
Lemma t40 : p14 -> p13.
Proof.
 intros h0.
 refine (nzr_of_abs _L i9 h0 _) ; finalize.
Qed.
Lemma l13 : p7 -> s1 -> p13 (* NZR(L) *).
Proof.
 intros h0 h1.
 assert (h2 := l14 h0 h1).
 apply t40. exact h2.
Qed.
Lemma t41 : p10 -> p13 -> p9.
Proof.
 intros h0 h1.
 refine (b1 h0 h1) ; finalize.
Qed.
Lemma l5 : p7 -> s1 -> p9 (* EQL((P - L) / L, (P - L) / x / (L / x)) *).
Proof.
 intros h0 h1.
 assert (h2 := l6 h1).
 assert (h3 := l13 h0 h1).
 apply t41. exact h2. exact h3.
Qed.
Notation p64 := (BND r44 i7). (* BND((P - L) / x / (L / x), [-1.57369e-19, 1.57369e-19]) *)
Definition f87 := Float2 (-922377932829010549107759325105221426676383110996443110660577061286183588755189900654095354665433699911601377171676533721) (-461).
Definition f88 := Float2 (922377932829010549107759325105221426676383110996443110660577061286183588755189900654095354665433699911601377171676533721) (-461).
Definition i55 := makepairF f87 f88.
Notation p65 := (BND r45 i55). (* BND((P - L) / x, [-1.54911e-19, 1.54911e-19]) *)
Notation p66 := (BND r52 i55). (* BND(x * x * W * (et - al) + (1 + x / 2) * d1 + ((1 + x / 2) * (1 + d1) + x * x * W * (1 + et)) * d2, [-1.54911e-19, 1.54911e-19]) *)
Definition f89 := Float2 (-115297241603607680951474681605591969994694017326999367792812439795100939473041995282543380337247259211542092413378715601) (-458).
Definition f90 := Float2 (115297241603607680951474681605591969994694017326999367792812439795100939473041995282543380337247259211542092413378715601) (-458).
Definition i56 := makepairF f89 f90.
Notation p67 := (BND r53 i56). (* BND(x * x * W * (et - al) + (1 + x / 2) * d1, [-1.54911e-19, 1.54911e-19]) *)
Definition f91 := Float2 (-230594483207158875537770771917105719587243978153750727270468786679565160358425857266338953028194724862918977399651533087) (-459).
Definition f92 := Float2 (230594483207158875537770771917105719587243978153750727270468786679565160358425857266338953028194724862918977399651533087) (-459).
Definition i57 := makepairF f91 f92.
Notation p68 := (BND r54 i57). (* BND(x * x * W * (et - al), [-1.54911e-19, 1.54911e-19]) *)
Definition f93 := Float2 (-4355) (-62).
Definition f94 := Float2 (4355) (-62).
Definition i58 := makepairF f93 f94.
Notation p69 := (BND r55 i58). (* BND(et - al, [-9.4434e-16, 9.4434e-16]) *)
Lemma l60 : s1 -> p2 (* BND(et, [-8.88178e-16, 8.88178e-16]) *).
Proof.
 intros h0.
 assert (h1 := l9 h0).
 exact (proj2 h1).
Qed.
Lemma t42 : p2 -> p3 -> p69.
Proof.
 intros h0 h1.
 refine (sub _et _al i2 i3 i58 h0 h1 _) ; finalize.
Qed.
Lemma l59 : s1 -> p69 (* BND(et - al, [-9.4434e-16, 9.4434e-16]) *).
Proof.
 intros h0.
 assert (h1 := l60 h0).
 assert (h2 := l47 h0).
 apply t42. exact h1. exact h2.
Qed.
Definition f95 := Float2 (1) (-111).
Definition i59 := makepairF f95 f33.
Notation p70 := (BND r51 i59). (* BND(x * x * W, [3.85186e-34, 0.000164041]) *)
Lemma t43 : p70 -> p69 -> p68.
Proof.
 intros h0 h1.
 refine (mul_po r51 r55 i59 i58 i57 h0 h1 _) ; finalize.
Qed.
Lemma l58 : s1 -> p68 (* BND(x * x * W * (et - al), [-1.54911e-19, 1.54911e-19]) *).
Proof.
 intros h0.
 assert (h1 := l25 h0).
 assert (h2 := l59 h0).
 apply t43. refine (subset r51 i19 i59 h1 _) ; finalize. exact h2.
Qed.
Definition f96 := Float2 (-56486365178591294078220402144056500248008315156092910636718587658133298747807646299793560165207427105898115) (-459).
Definition f97 := Float2 (56486365178591294078220402144056500248008315156092910636718587658133298747807646299793560165207427105898115) (-459).
Definition i60 := makepairF f96 f97.
Notation p71 := (BND r56 i60). (* BND((1 + x / 2) * d1, [-3.79468e-32, 3.79468e-32]) *)
Lemma l62 : s1 -> p4 (* BND(d1, [-3.7363e-32, 3.7363e-32]) *).
Proof.
 intros h0.
 assert (h1 := l11 h0).
 exact (proj2 h1).
Qed.
Definition i61 := makepairF f84 f23.
Notation p72 := (BND r48 i61). (* BND(1 + x / 2, [0.5, 1.01563]) *)
Lemma t44 : p72 -> p4 -> p71.
Proof.
 intros h0 h1.
 refine (mul_po r48 _d1 i61 i4 i60 h0 h1 _) ; finalize.
Qed.
Lemma l61 : s1 -> p71 (* BND((1 + x / 2) * d1, [-3.79468e-32, 3.79468e-32]) *).
Proof.
 intros h0.
 assert (h1 := l19 h0).
 assert (h2 := l62 h0).
 apply t44. refine (subset r48 i12 i61 h1 _) ; finalize. exact h2.
Qed.
Lemma t45 : p68 -> p71 -> p67.
Proof.
 intros h0 h1.
 refine (add r54 r56 i57 i60 i56 h0 h1 _) ; finalize.
Qed.
Lemma l57 : s1 -> p67 (* BND(x * x * W * (et - al) + (1 + x / 2) * d1, [-1.54911e-19, 1.54911e-19]) *).
Proof.
 intros h0.
 assert (h1 := l58 h0).
 assert (h2 := l61 h0).
 apply t45. exact h1. exact h2.
Qed.
Definition f98 := Float2 (-149101495961872260485666718830972380448168318077542925376072970853938393748311967455626219264637864646808913) (-461).
Definition f99 := Float2 (149101495961872260485666718830972380448168318077542925376072970853938393748311967455626219264637864646808913) (-461).
Definition i62 := makepairF f98 f99.
Notation p73 := (BND r57 i62). (* BND(((1 + x / 2) * (1 + d1) + x * x * W * (1 + et)) * d2, [-2.50411e-32, 2.50411e-32]) *)
Definition f100 := Float2 (149101495961872260485666718830972380448168318077542925376072970853938393748311967455626219264637864646808913) (-356).
Definition i63 := makepairF f84 f100.
Notation p74 := (BND r58 i63). (* BND((1 + x / 2) * (1 + d1) + x * x * W * (1 + et), [0.5, 1.01579]) *)
Definition f101 := Float2 (37269354344637554855733048837317021526025215841499713743691322585792680020136510474315791550516896961184303) (-354).
Definition i64 := makepairF f84 f101.
Notation p75 := (BND r59 i64). (* BND((1 + x / 2) * (1 + d1), [0.5, 1.01563]) *)
Definition f102 := Float2 (3) (-2).
Definition f103 := Float2 (2596148429267413814265248164610145) (-111).
Definition i65 := makepairF f102 f103.
Notation p76 := (BND r37 i65). (* BND(1 + d1, [0.75, 1]) *)
Definition i66 := makepairF f76 f8.
Notation p77 := (BND _d1 i66). (* BND(d1, [-0.25, 3.7363e-32]) *)
Lemma t46 : p20 -> p77 -> p76.
Proof.
 intros h0 h1.
 refine (add r30 _d1 i13 i66 i65 h0 h1 _) ; finalize.
Qed.
Lemma l66 : s1 -> p76 (* BND(1 + d1, [0.75, 1]) *).
Proof.
 intros h0.
 assert (h1 := l20 h0).
 assert (h2 := l62 h0).
 apply t46. exact h1. refine (subset _d1 i4 i66 h2 _) ; finalize.
Qed.
Definition i67 := makepairF f102 f23.
Notation p78 := (BND r48 i67). (* BND(1 + x / 2, [0.75, 1.01563]) *)
Lemma t47 : p78 -> p76 -> p75.
Proof.
 intros h0 h1.
 refine (mul_pp r48 r37 i67 i65 i64 h0 h1 _) ; finalize.
Qed.
Lemma l65 : s1 -> p75 (* BND((1 + x / 2) * (1 + d1), [0.5, 1.01563]) *).
Proof.
 intros h0.
 assert (h1 := l19 h0).
 assert (h2 := l66 h0).
 apply t47. refine (subset r48 i12 i67 h1 _) ; finalize. exact h2.
Qed.
Definition f104 := Float2 (24078583322041062734523481704294344067454711544070401307680510767673667765925558363053062570276802071701) (-356).
Definition i68 := makepairF f95 f104.
Notation p79 := (BND r60 i68). (* BND(x * x * W * (1 + et), [3.85186e-34, 0.000164041]) *)
Definition f105 := Float2 (7) (-3).
Definition f106 := Float2 (1125899906842625) (-50).
Definition i69 := makepairF f105 f106.
Notation p80 := (BND r40 i69). (* BND(1 + et, [0.875, 1]) *)
Definition f107 := Float2 (-1) (-3).
Definition i70 := makepairF f107 f4.
Notation p81 := (BND _et i70). (* BND(et, [-0.125, 8.88178e-16]) *)
Lemma t48 : p20 -> p81 -> p80.
Proof.
 intros h0 h1.
 refine (add r30 _et i13 i70 i69 h0 h1 _) ; finalize.
Qed.
Lemma l68 : s1 -> p80 (* BND(1 + et, [0.875, 1]) *).
Proof.
 intros h0.
 assert (h1 := l20 h0).
 assert (h2 := l60 h0).
 apply t48. exact h1. refine (subset _et i2 i70 h2 _) ; finalize.
Qed.
Definition f108 := Float2 (5) (-113).
Definition f109 := Float2 (24656469321770026340808087670876818796459809774730804412709002324197689445369169850208086898115708934611411) (-366).
Definition i71 := makepairF f108 f109.
Notation p82 := (BND r51 i71). (* BND(x * x * W, [4.81482e-34, 0.000164041]) *)
Lemma t49 : p82 -> p80 -> p79.
Proof.
 intros h0 h1.
 refine (mul_pp r51 r40 i71 i69 i68 h0 h1 _) ; finalize.
Qed.
Lemma l67 : s1 -> p79 (* BND(x * x * W * (1 + et), [3.85186e-34, 0.000164041]) *).
Proof.
 intros h0.
 assert (h1 := l25 h0).
 assert (h2 := l68 h0).
 apply t49. refine (subset r51 i19 i71 h1 _) ; finalize. exact h2.
Qed.
Lemma t50 : p75 -> p79 -> p74.
Proof.
 intros h0 h1.
 refine (add r59 r60 i64 i68 i63 h0 h1 _) ; finalize.
Qed.
Lemma l64 : s1 -> p74 (* BND((1 + x / 2) * (1 + d1) + x * x * W * (1 + et), [0.5, 1.01579]) *).
Proof.
 intros h0.
 assert (h1 := l65 h0).
 assert (h2 := l67 h0).
 apply t50. exact h1. exact h2.
Qed.
Lemma l69 : s1 -> p5 (* BND(d2, [-2.46519e-32, 2.46519e-32]) *).
Proof.
 intros h0.
 assert (h1 := l12 h0).
 exact (proj2 h1).
Qed.
Lemma t51 : p74 -> p5 -> p73.
Proof.
 intros h0 h1.
 refine (mul_po r58 _d2 i63 i5 i62 h0 h1 _) ; finalize.
Qed.
Lemma l63 : s1 -> p73 (* BND(((1 + x / 2) * (1 + d1) + x * x * W * (1 + et)) * d2, [-2.50411e-32, 2.50411e-32]) *).
Proof.
 intros h0.
 assert (h1 := l64 h0).
 assert (h2 := l69 h0).
 apply t51. exact h1. exact h2.
Qed.
Lemma t52 : p67 -> p73 -> p66.
Proof.
 intros h0 h1.
 refine (add r53 r57 i56 i62 i55 h0 h1 _) ; finalize.
Qed.
Lemma l56 : s1 -> p66 (* BND(x * x * W * (et - al) + (1 + x / 2) * d1 + ((1 + x / 2) * (1 + d1) + x * x * W * (1 + et)) * d2, [-1.54911e-19, 1.54911e-19]) *).
Proof.
 intros h0.
 assert (h1 := l57 h0).
 assert (h2 := l63 h0).
 apply t52. exact h1. exact h2.
Qed.
Notation p83 := (REL r45 r52 i50). (* REL((P - L) / x, x * x * W * (et - al) + (1 + x / 2) * d1 + ((1 + x / 2) * (1 + d1) + x * x * W * (1 + et)) * d2, [0, 0]) *)
Notation p84 := (r45 = r52). (* EQL((P - L) / x, x * x * W * (et - al) + (1 + x / 2) * d1 + ((1 + x / 2) * (1 + d1) + x * x * W * (1 + et)) * d2) *)
Lemma t53 : p10 -> p84.
Proof.
 intros h0.
 refine (b3 h0) ; finalize.
Qed.
Lemma l71 : s1 -> p84 (* EQL((P - L) / x, x * x * W * (et - al) + (1 + x / 2) * d1 + ((1 + x / 2) * (1 + d1) + x * x * W * (1 + et)) * d2) *).
Proof.
 intros h0.
 assert (h1 := l6 h0).
 apply t53. exact h1.
Qed.
Notation p85 := (REL r52 r52 i50). (* REL(x * x * W * (et - al) + (1 + x / 2) * d1 + ((1 + x / 2) * (1 + d1) + x * x * W * (1 + et)) * d2, x * x * W * (et - al) + (1 + x / 2) * d1 + ((1 + x / 2) * (1 + d1) + x * x * W * (1 + et)) * d2, [0, 0]) *)
Lemma t54 : p85.
Proof.
 refine (rel_refl r52 i50 _) ; finalize.
Qed.
Lemma l72 : s1 -> p85 (* REL(x * x * W * (et - al) + (1 + x / 2) * d1 + ((1 + x / 2) * (1 + d1) + x * x * W * (1 + et)) * d2, x * x * W * (et - al) + (1 + x / 2) * d1 + ((1 + x / 2) * (1 + d1) + x * x * W * (1 + et)) * d2, [0, 0]) *).
Proof.
 intros h0.
 apply t54.
Qed.
Lemma t55 : p84 -> p85 -> p83.
Proof.
 intros h0 h1.
 refine (rel_rewrite_1 r45 r52 r52 i50 h0 h1) ; finalize.
Qed.
Lemma l70 : s1 -> p83 (* REL((P - L) / x, x * x * W * (et - al) + (1 + x / 2) * d1 + ((1 + x / 2) * (1 + d1) + x * x * W * (1 + et)) * d2, [0, 0]) *).
Proof.
 intros h0.
 assert (h1 := l71 h0).
 assert (h2 := l72 h0).
 apply t55. exact h1. exact h2.
Qed.
Lemma t56 : p66 -> p83 -> p65.
Proof.
 intros h0 h1.
 refine (bnd_of_bnd_rel_o r45 r52 i55 i50 i55 h0 h1 _) ; finalize.
Qed.
Lemma l55 : s1 -> p65 (* BND((P - L) / x, [-1.54911e-19, 1.54911e-19]) *).
Proof.
 intros h0.
 assert (h1 := l56 h0).
 assert (h2 := l70 h0).
 apply t56. exact h1. exact h2.
Qed.
Definition f110 := Float2 (1270951047314653369298557976072253764705989387384561771766371360118400117127849123041836098528525454791849420966498885193) (-399).
Definition i72 := makepairF f110 f21.
Notation p86 := (BND r46 i72). (* BND(L / x, [0.984375, 2]) *)
Lemma t57 : p65 -> p86 -> p64.
Proof.
 intros h0 h1.
 refine (div_op r45 r46 i55 i72 i7 h0 h1 _) ; finalize.
Qed.
Lemma l54 : s1 -> p64 (* BND((P - L) / x / (L / x), [-1.57369e-19, 1.57369e-19]) *).
Proof.
 intros h0.
 assert (h1 := l55 h0).
 assert (h2 := l17 h0).
 apply t57. exact h1. refine (subset r46 i11 i72 h2 _) ; finalize.
Qed.
Lemma t58 : p9 -> p64 -> p8.
Proof.
 intros h0 h1.
 refine (bnd_rewrite r32 r44 i7 h0 h1) ; finalize.
Qed.
Lemma l4 : p7 -> s1 -> p8 (* BND((P - L) / L, [-1.57369e-19, 1.57369e-19]) *).
Proof.
 intros h0 h1.
 assert (h2 := l5 h0 h1).
 assert (h3 := l54 h1).
 apply t58. exact h2. exact h3.
Qed.
Lemma l2 : p7 -> s1 -> False.
Proof.
 intros h0 h1.
 assert (h2 := l3 h1).
 assert (h3 := l4 h0 h1).
 refine (simplify (Tatom false (Abnd 0%nat i6)) Tfalse (Abnd 0%nat i7) (List.cons r32 List.nil) h3 h2 _) ; finalize.
Qed.
Notation p87 := ((f13 <= _x)%R). (* BND(x, [0, inf]) *)
Notation p88 := (ABS _L i8). (* ABS(L, [5.55112e-17, 1]) *)
Notation p89 := (BND _L i8). (* BND(L, [5.55112e-17, 1]) *)
Definition i73 := makepairF f1 f84.
Notation p90 := (BND r3 i73). (* BND(x + B, [5.55112e-17, 0.5]) *)
Definition f111 := Float2 (1) (-2).
Definition i74 := makepairF f1 f111.
Notation p91 := (BND _x i74). (* BND(x, [5.55112e-17, 0.25]) *)
Definition i75 := makepairF f13 f111.
Notation p92 := (BND _x i75). (* BND(x, [0, 0.25]) *)
Lemma l82 : p87 -> s1 -> p87 (* BND(x, [0, inf]) *).
Proof.
 intros h0 h1.
 assert (h2 := h0).
 exact (h2).
Qed.
Lemma l81 : p87 -> s1 -> p92 (* BND(x, [0, 0.25]) *).
Proof.
 intros h0 h1.
 assert (h2 := l22 h1).
 assert (h3 := l82 h0 h1).
 apply intersect_bh with (1 := h2) (2 := h3). finalize.
Qed.
Lemma t59 : p92 -> p12 -> p91.
Proof.
 intros h0 h1.
 refine (bnd_of_bnd_abs_p _x i75 i8 i74 h0 h1 _) ; finalize.
Qed.
Lemma l80 : p87 -> s1 -> p91 (* BND(x, [5.55112e-17, 0.25]) *).
Proof.
 intros h0 h1.
 assert (h2 := l81 h0 h1).
 assert (h3 := l7 h1).
 apply t59. exact h2. refine (abs_subset _x i1 i8 h3 _) ; finalize.
Qed.
Definition f112 := Float2 (1) (-109).
Definition i76 := makepairF f112 f111.
Notation p93 := (BND _B i76). (* BND(B, [1.54074e-33, 0.25]) *)
Definition i77 := makepairF f34 f111.
Notation p94 := (BND r5 i77). (* BND(x * x, [3.08149e-33, 0.25]) *)
Definition i78 := makepairF f16 f21.
Notation p95 := (BND r6 i78). (* BND(2, [1, 2]) *)
Lemma t60 : p94 -> p95 -> p93.
Proof.
 intros h0 h1.
 refine (div_pp r5 r6 i77 i78 i76 h0 h1 _) ; finalize.
Qed.
Lemma l83 : s1 -> p93 (* BND(B, [1.54074e-33, 0.25]) *).
Proof.
 intros h0.
 assert (h1 := l26 h0).
 assert (h2 := l23 h0).
 apply t60. refine (subset r5 i20 i77 h1 _) ; finalize. refine (subset r6 i16 i78 h2 _) ; finalize.
Qed.
Lemma t61 : p91 -> p93 -> p90.
Proof.
 intros h0 h1.
 refine (add _x _B i74 i76 i73 h0 h1 _) ; finalize.
Qed.
Lemma l79 : p87 -> s1 -> p90 (* BND(x + B, [5.55112e-17, 0.5]) *).
Proof.
 intros h0 h1.
 assert (h2 := l80 h0 h1).
 assert (h3 := l83 h1).
 apply t61. exact h2. exact h3.
Qed.
Definition f113 := Float2 (1) (-165).
Definition i79 := makepairF f113 f84.
Notation p96 := (BND r7 i79). (* BND(T * (1 + al), [2.13821e-50, 0.5]) *)
Definition f114 := Float2 (5) (-167).
Definition i80 := makepairF f114 f111.
Notation p97 := (BND _T i80). (* BND(T, [2.67276e-50, 0.25]) *)
Notation p98 := (BND _T i75). (* BND(T, [0, 0.25]) *)
Definition i81 := makepairF f13 f16.
Notation p99 := (BND r9 i81). (* BND(x * x * x, [0, 1]) *)
Definition i82 := makepairF f34 f16.
Notation p100 := (BND r5 i82). (* BND(x * x, [3.08149e-33, 1]) *)
Notation p101 := (BND _x i81). (* BND(x, [0, 1]) *)
Lemma t62 : p100 -> p101 -> p99.
Proof.
 intros h0 h1.
 refine (mul_pp r5 _x i82 i81 i81 h0 h1 _) ; finalize.
Qed.
Lemma l87 : p87 -> s1 -> p99 (* BND(x * x * x, [0, 1]) *).
Proof.
 intros h0 h1.
 assert (h2 := l26 h1).
 assert (h3 := l81 h0 h1).
 apply t62. refine (subset r5 i20 i82 h2 _) ; finalize. refine (subset _x i75 i81 h3 _) ; finalize.
Qed.
Definition f115 := Float2 (1) (-3).
Definition i83 := makepairF f115 f111.
Notation p102 := (BND _W i83). (* BND(W, [0.125, 0.25]) *)
Lemma t63 : p99 -> p102 -> p98.
Proof.
 intros h0 h1.
 refine (mul_pp r9 _W i81 i83 i75 h0 h1 _) ; finalize.
Qed.
Lemma l86 : p87 -> s1 -> p98 (* BND(T, [0, 0.25]) *).
Proof.
 intros h0 h1.
 assert (h2 := l87 h0 h1).
 assert (h3 := l27 h1).
 apply t63. exact h2. refine (subset _W i21 i83 h3 _) ; finalize.
Qed.
Definition i84 := makepairF f114 f16.
Notation p103 := (ABS _T i84). (* ABS(T, [2.67276e-50, 1]) *)
Definition f116 := Float2 (1) (-162).
Definition i85 := makepairF f116 f16.
Notation p104 := (ABS r9 i85). (* ABS(x * x * x, [1.71057e-49, 1]) *)
Notation p105 := (ABS r5 i82). (* ABS(x * x, [3.08149e-33, 1]) *)
Lemma t64 : p12 -> p12 -> p105.
Proof.
 intros h0 h1.
 refine (mul_aa _x _x i8 i8 i82 h0 h1 _) ; finalize.
Qed.
Lemma l90 : s1 -> p105 (* ABS(x * x, [3.08149e-33, 1]) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 apply t64. refine (abs_subset _x i1 i8 h1 _) ; finalize. refine (abs_subset _x i1 i8 h1 _) ; finalize.
Qed.
Lemma t65 : p105 -> p12 -> p104.
Proof.
 intros h0 h1.
 refine (mul_aa r5 _x i82 i8 i85 h0 h1 _) ; finalize.
Qed.
Lemma l89 : s1 -> p104 (* ABS(x * x * x, [1.71057e-49, 1]) *).
Proof.
 intros h0.
 assert (h1 := l90 h0).
 assert (h2 := l7 h0).
 apply t65. exact h1. refine (abs_subset _x i1 i8 h2 _) ; finalize.
Qed.
Definition f117 := Float2 (5) (-5).
Definition i86 := makepairF f117 f16.
Notation p106 := (ABS _W i86). (* ABS(W, [0.15625, 1]) *)
Definition f118 := Float2 (21) (-7).
Definition i87 := makepairF f118 f84.
Notation p107 := (ABS _c3 i87). (* ABS(c3, [0.164062, 0.5]) *)
Notation p108 := (BND _c3 i87). (* BND(c3, [0.164062, 0.5]) *)
Lemma t66 : p108 -> p107.
Proof.
 intros h0.
 refine (abs_of_bnd_p _c3 i87 i87 h0 _) ; finalize.
Qed.
Lemma l92 : s1 -> p107 (* ABS(c3, [0.164062, 0.5]) *).
Proof.
 intros h0.
 assert (h1 := l28 h0).
 apply t66. refine (subset _c3 i22 i87 h1 _) ; finalize.
Qed.
Definition f119 := Float2 (1) (-59).
Definition i88 := makepairF f119 f47.
Notation p109 := (ABS r12 i88). (* ABS(x * (c4 + x * (c5 + x * (c6 + x * (c7 + x * (c8 + x * c9))))), [1.73472e-18, 0.0078125]) *)
Definition i89 := makepairF f41 f115.
Notation p110 := (ABS r13 i89). (* ABS(c4 + x * (c5 + x * (c6 + x * (c7 + x * (c8 + x * c9)))), [0.03125, 0.125]) *)
Definition f120 := Float2 (1) (-4).
Definition i90 := makepairF f43 f120.
Notation p111 := (ABS _c4 i90). (* ABS(c4, [0.0390625, 0.0625]) *)
Notation p112 := (BND _c4 i90). (* BND(c4, [0.0390625, 0.0625]) *)
Lemma t67 : p112 -> p111.
Proof.
 intros h0.
 refine (abs_of_bnd_p _c4 i90 i90 h0 _) ; finalize.
Qed.
Lemma l95 : s1 -> p111 (* ABS(c4, [0.0390625, 0.0625]) *).
Proof.
 intros h0.
 assert (h1 := l31 h0).
 apply t67. refine (subset _c4 i25 i90 h1 _) ; finalize.
Qed.
Definition f121 := Float2 (1) (-61).
Definition i91 := makepairF f121 f47.
Notation p113 := (ABS r15 i91). (* ABS(x * (c5 + x * (c6 + x * (c7 + x * (c8 + x * c9)))), [4.33681e-19, 0.0078125]) *)
Definition i92 := makepairF f47 f115.
Notation p114 := (ABS r16 i92). (* ABS(c5 + x * (c6 + x * (c7 + x * (c8 + x * c9))), [0.0078125, 0.125]) *)
Definition i93 := makepairF f49 f120.
Notation p115 := (ABS _c5 i93). (* ABS(c5, [0.00830078, 0.0625]) *)
Notation p116 := (BND _c5 i93). (* BND(c5, [0.00830078, 0.0625]) *)
Lemma t68 : p116 -> p115.
Proof.
 intros h0.
 refine (abs_of_bnd_p _c5 i93 i93 h0 _) ; finalize.
Qed.
Lemma l98 : s1 -> p115 (* ABS(c5, [0.00830078, 0.0625]) *).
Proof.
 intros h0.
 assert (h1 := l34 h0).
 apply t68. refine (subset _c5 i28 i93 h1 _) ; finalize.
Qed.
Definition f122 := Float2 (1) (-64).
Definition f123 := Float2 (1) (-11).
Definition i94 := makepairF f122 f123.
Notation p117 := (ABS r18 i94). (* ABS(x * (c6 + x * (c7 + x * (c8 + x * c9))), [5.42101e-20, 0.000488281]) *)
Definition i95 := makepairF f53 f47.
Notation p118 := (ABS r19 i95). (* ABS(c6 + x * (c7 + x * (c8 + x * c9)), [0.000976562, 0.0078125]) *)
Definition f124 := Float2 (1) (-8).
Definition i96 := makepairF f55 f124.
Notation p119 := (ABS _c6 i96). (* ABS(c6, [0.0012207, 0.00390625]) *)
Notation p120 := (BND _c6 i96). (* BND(c6, [0.0012207, 0.00390625]) *)
Lemma t69 : p120 -> p119.
Proof.
 intros h0.
 refine (abs_of_bnd_p _c6 i96 i96 h0 _) ; finalize.
Qed.
Lemma l101 : s1 -> p119 (* ABS(c6, [0.0012207, 0.00390625]) *).
Proof.
 intros h0.
 assert (h1 := l37 h0).
 apply t69. refine (subset _c6 i31 i96 h1 _) ; finalize.
Qed.
Definition f125 := Float2 (1) (-67).
Definition f126 := Float2 (1) (-12).
Definition i97 := makepairF f125 f126.
Notation p121 := (ABS r21 i97). (* ABS(x * (c7 + x * (c8 + x * c9)), [6.77626e-21, 0.000244141]) *)
Definition i98 := makepairF f59 f124.
Notation p122 := (ABS r22 i98). (* ABS(c7 + x * (c8 + x * c9), [0.00012207, 0.00390625]) *)
Definition f127 := Float2 (1) (-9).
Definition i99 := makepairF f61 f127.
Notation p123 := (ABS _c7 i99). (* ABS(c7, [0.000183105, 0.00195312]) *)
Notation p124 := (BND _c7 i99). (* BND(c7, [0.000183105, 0.00195312]) *)
Lemma t70 : p124 -> p123.
Proof.
 intros h0.
 refine (abs_of_bnd_p _c7 i99 i99 h0 _) ; finalize.
Qed.
Lemma l104 : s1 -> p123 (* ABS(c7, [0.000183105, 0.00195312]) *).
Proof.
 intros h0.
 assert (h1 := l40 h0).
 apply t70. refine (subset _c7 i34 i99 h1 _) ; finalize.
Qed.
Definition f128 := Float2 (1) (-70).
Definition f129 := Float2 (1) (-14).
Definition i100 := makepairF f128 f129.
Notation p125 := (ABS r24 i100). (* ABS(x * (c8 + x * c9), [8.47033e-22, 6.10352e-05]) *)
Definition i101 := makepairF f65 f53.
Notation p126 := (ABS r25 i101). (* ABS(c8 + x * c9, [1.52588e-05, 0.000976562]) *)
Definition i102 := makepairF f67 f123.
Notation p127 := (ABS _c8 i102). (* ABS(c8, [2.28882e-05, 0.000488281]) *)
Notation p128 := (BND _c8 i102). (* BND(c8, [2.28882e-05, 0.000488281]) *)
Lemma t71 : p128 -> p127.
Proof.
 intros h0.
 refine (abs_of_bnd_p _c8 i102 i102 h0 _) ; finalize.
Qed.
Lemma l107 : s1 -> p127 (* ABS(c8, [2.28882e-05, 0.000488281]) *).
Proof.
 intros h0.
 assert (h1 := l43 h0).
 apply t71. refine (subset _c8 i37 i102 h1 _) ; finalize.
Qed.
Definition f130 := Float2 (1) (-73).
Definition f131 := Float2 (1) (-17).
Definition i103 := makepairF f130 f131.
Notation p129 := (ABS r27 i103). (* ABS(x * c9, [1.05879e-22, 7.62939e-06]) *)
Definition i104 := makepairF f71 f59.
Notation p130 := (ABS _c9 i104). (* ABS(c9, [1.90735e-06, 0.00012207]) *)
Notation p131 := (BND _c9 i104). (* BND(c9, [1.90735e-06, 0.00012207]) *)
Lemma t72 : p131 -> p130.
Proof.
 intros h0.
 refine (abs_of_bnd_p _c9 i104 i104 h0 _) ; finalize.
Qed.
Lemma l109 : s1 -> p130 (* ABS(c9, [1.90735e-06, 0.00012207]) *).
Proof.
 intros h0.
 assert (h1 := l45 h0).
 apply t72. refine (subset _c9 i39 i104 h1 _) ; finalize.
Qed.
Definition i105 := makepairF f1 f120.
Notation p132 := (ABS _x i105). (* ABS(x, [5.55112e-17, 0.0625]) *)
Lemma t73 : p132 -> p130 -> p129.
Proof.
 intros h0 h1.
 refine (mul_aa _x _c9 i105 i104 i103 h0 h1 _) ; finalize.
Qed.
Lemma l108 : s1 -> p129 (* ABS(x * c9, [1.05879e-22, 7.62939e-06]) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 assert (h2 := l109 h0).
 apply t73. refine (abs_subset _x i1 i105 h1 _) ; finalize. exact h2.
Qed.
Lemma t74 : p127 -> p129 -> p126.
Proof.
 intros h0 h1.
 refine (add_aa_p _c8 r27 i102 i103 i101 h0 h1 _) ; finalize.
Qed.
Lemma l106 : s1 -> p126 (* ABS(c8 + x * c9, [1.52588e-05, 0.000976562]) *).
Proof.
 intros h0.
 assert (h1 := l107 h0).
 assert (h2 := l108 h0).
 apply t74. exact h1. exact h2.
Qed.
Lemma t75 : p132 -> p126 -> p125.
Proof.
 intros h0 h1.
 refine (mul_aa _x r25 i105 i101 i100 h0 h1 _) ; finalize.
Qed.
Lemma l105 : s1 -> p125 (* ABS(x * (c8 + x * c9), [8.47033e-22, 6.10352e-05]) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 assert (h2 := l106 h0).
 apply t75. refine (abs_subset _x i1 i105 h1 _) ; finalize. exact h2.
Qed.
Lemma t76 : p123 -> p125 -> p122.
Proof.
 intros h0 h1.
 refine (add_aa_p _c7 r24 i99 i100 i98 h0 h1 _) ; finalize.
Qed.
Lemma l103 : s1 -> p122 (* ABS(c7 + x * (c8 + x * c9), [0.00012207, 0.00390625]) *).
Proof.
 intros h0.
 assert (h1 := l104 h0).
 assert (h2 := l105 h0).
 apply t76. exact h1. exact h2.
Qed.
Lemma t77 : p132 -> p122 -> p121.
Proof.
 intros h0 h1.
 refine (mul_aa _x r22 i105 i98 i97 h0 h1 _) ; finalize.
Qed.
Lemma l102 : s1 -> p121 (* ABS(x * (c7 + x * (c8 + x * c9)), [6.77626e-21, 0.000244141]) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 assert (h2 := l103 h0).
 apply t77. refine (abs_subset _x i1 i105 h1 _) ; finalize. exact h2.
Qed.
Lemma t78 : p119 -> p121 -> p118.
Proof.
 intros h0 h1.
 refine (add_aa_p _c6 r21 i96 i97 i95 h0 h1 _) ; finalize.
Qed.
Lemma l100 : s1 -> p118 (* ABS(c6 + x * (c7 + x * (c8 + x * c9)), [0.000976562, 0.0078125]) *).
Proof.
 intros h0.
 assert (h1 := l101 h0).
 assert (h2 := l102 h0).
 apply t78. exact h1. exact h2.
Qed.
Lemma t79 : p132 -> p118 -> p117.
Proof.
 intros h0 h1.
 refine (mul_aa _x r19 i105 i95 i94 h0 h1 _) ; finalize.
Qed.
Lemma l99 : s1 -> p117 (* ABS(x * (c6 + x * (c7 + x * (c8 + x * c9))), [5.42101e-20, 0.000488281]) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 assert (h2 := l100 h0).
 apply t79. refine (abs_subset _x i1 i105 h1 _) ; finalize. exact h2.
Qed.
Lemma t80 : p115 -> p117 -> p114.
Proof.
 intros h0 h1.
 refine (add_aa_p _c5 r18 i93 i94 i92 h0 h1 _) ; finalize.
Qed.
Lemma l97 : s1 -> p114 (* ABS(c5 + x * (c6 + x * (c7 + x * (c8 + x * c9))), [0.0078125, 0.125]) *).
Proof.
 intros h0.
 assert (h1 := l98 h0).
 assert (h2 := l99 h0).
 apply t80. exact h1. exact h2.
Qed.
Lemma t81 : p132 -> p114 -> p113.
Proof.
 intros h0 h1.
 refine (mul_aa _x r16 i105 i92 i91 h0 h1 _) ; finalize.
Qed.
Lemma l96 : s1 -> p113 (* ABS(x * (c5 + x * (c6 + x * (c7 + x * (c8 + x * c9)))), [4.33681e-19, 0.0078125]) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 assert (h2 := l97 h0).
 apply t81. refine (abs_subset _x i1 i105 h1 _) ; finalize. exact h2.
Qed.
Lemma t82 : p111 -> p113 -> p110.
Proof.
 intros h0 h1.
 refine (add_aa_p _c4 r15 i90 i91 i89 h0 h1 _) ; finalize.
Qed.
Lemma l94 : s1 -> p110 (* ABS(c4 + x * (c5 + x * (c6 + x * (c7 + x * (c8 + x * c9)))), [0.03125, 0.125]) *).
Proof.
 intros h0.
 assert (h1 := l95 h0).
 assert (h2 := l96 h0).
 apply t82. exact h1. exact h2.
Qed.
Lemma t83 : p132 -> p110 -> p109.
Proof.
 intros h0 h1.
 refine (mul_aa _x r13 i105 i89 i88 h0 h1 _) ; finalize.
Qed.
Lemma l93 : s1 -> p109 (* ABS(x * (c4 + x * (c5 + x * (c6 + x * (c7 + x * (c8 + x * c9))))), [1.73472e-18, 0.0078125]) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 assert (h2 := l94 h0).
 apply t83. refine (abs_subset _x i1 i105 h1 _) ; finalize. exact h2.
Qed.
Lemma t84 : p107 -> p109 -> p106.
Proof.
 intros h0 h1.
 refine (add_aa_p _c3 r12 i87 i88 i86 h0 h1 _) ; finalize.
Qed.
Lemma l91 : s1 -> p106 (* ABS(W, [0.15625, 1]) *).
Proof.
 intros h0.
 assert (h1 := l92 h0).
 assert (h2 := l93 h0).
 apply t84. exact h1. exact h2.
Qed.
Lemma t85 : p104 -> p106 -> p103.
Proof.
 intros h0 h1.
 refine (mul_aa r9 _W i85 i86 i84 h0 h1 _) ; finalize.
Qed.
Lemma l88 : s1 -> p103 (* ABS(T, [2.67276e-50, 1]) *).
Proof.
 intros h0.
 assert (h1 := l89 h0).
 assert (h2 := l91 h0).
 apply t85. exact h1. exact h2.
Qed.
Lemma t86 : p98 -> p103 -> p97.
Proof.
 intros h0 h1.
 refine (bnd_of_bnd_abs_p _T i75 i84 i80 h0 h1 _) ; finalize.
Qed.
Lemma l85 : p87 -> s1 -> p97 (* BND(T, [2.67276e-50, 0.25]) *).
Proof.
 intros h0 h1.
 assert (h2 := l86 h0 h1).
 assert (h3 := l88 h1).
 apply t86. exact h2. exact h3.
Qed.
Definition i106 := makepairF f105 f21.
Notation p133 := (BND r29 i106). (* BND(1 + al, [0.875, 2]) *)
Lemma t87 : p97 -> p133 -> p96.
Proof.
 intros h0 h1.
 refine (mul_pp _T r29 i80 i106 i79 h0 h1 _) ; finalize.
Qed.
Lemma l84 : p87 -> s1 -> p96 (* BND(T * (1 + al), [2.13821e-50, 0.5]) *).
Proof.
 intros h0 h1.
 assert (h2 := l85 h0 h1).
 assert (h3 := l46 h1).
 apply t87. exact h2. refine (subset r29 i46 i106 h3 _) ; finalize.
Qed.
Lemma t88 : p90 -> p96 -> p89.
Proof.
 intros h0 h1.
 refine (add r3 r7 i73 i79 i8 h0 h1 _) ; finalize.
Qed.
Lemma l78 : p87 -> s1 -> p89 (* BND(L, [5.55112e-17, 1]) *).
Proof.
 intros h0 h1.
 assert (h2 := l79 h0 h1).
 assert (h3 := l84 h0 h1).
 apply t88. exact h2. exact h3.
Qed.
Lemma t89 : p89 -> p88.
Proof.
 intros h0.
 refine (abs_of_bnd_p _L i8 i8 h0 _) ; finalize.
Qed.
Lemma l77 : p87 -> s1 -> p88 (* ABS(L, [5.55112e-17, 1]) *).
Proof.
 intros h0 h1.
 assert (h2 := l78 h0 h1).
 apply t89. exact h2.
Qed.
Lemma t90 : p88 -> p13.
Proof.
 intros h0.
 refine (nzr_of_abs _L i8 h0 _) ; finalize.
Qed.
Lemma l76 : p87 -> s1 -> p13 (* NZR(L) *).
Proof.
 intros h0 h1.
 assert (h2 := l77 h0 h1).
 apply t90. exact h2.
Qed.
Lemma t91 : p10 -> p13 -> p9.
Proof.
 intros h0 h1.
 refine (b1 h0 h1) ; finalize.
Qed.
Lemma l75 : p87 -> s1 -> p9 (* EQL((P - L) / L, (P - L) / x / (L / x)) *).
Proof.
 intros h0 h1.
 assert (h2 := l6 h1).
 assert (h3 := l76 h0 h1).
 apply t91. exact h2. exact h3.
Qed.
Lemma t92 : p9 -> p64 -> p8.
Proof.
 intros h0 h1.
 refine (bnd_rewrite r32 r44 i7 h0 h1) ; finalize.
Qed.
Lemma l74 : p87 -> s1 -> p8 (* BND((P - L) / L, [-1.57369e-19, 1.57369e-19]) *).
Proof.
 intros h0 h1.
 assert (h2 := l75 h0 h1).
 assert (h3 := l54 h1).
 apply t92. exact h2. exact h3.
Qed.
Lemma l73 : p87 -> s1 -> False.
Proof.
 intros h0 h1.
 assert (h2 := l3 h1).
 assert (h3 := l74 h0 h1).
 refine (simplify (Tatom false (Abnd 0%nat i6)) Tfalse (Abnd 0%nat i7) (List.cons r32 List.nil) h3 h2 _) ; finalize.
Qed.
Lemma l1 : s1 -> False.
Proof.
 intros h0.
 apply (union _x f13).
 intro h1. (* [-inf, 0] *)
 apply (l2 h1 h0).
 intro h1. (* [0, inf] *)
 apply (l73 h1 h0).
Qed.
End Generated_by_Gappa.
