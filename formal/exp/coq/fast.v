Require Import Gappa.Gappa_library.
Section Generated_by_Gappa.
Variable _Tj : R.
Notation r6 := (Float1 (1)).
Variable _rhi_ : R.
Notation _rhi := ((rounding_float rndNE (53)%positive (-1074)%Z) _rhi_).
Variable _rlo : R.
Notation r8 := ((_rhi + _rlo)%R).
Variable _dr : R.
Notation _R := ((r8 - _dr)%R).
Notation r5 := ((r6 + _R)%R).
Notation r14 := ((_rhi * _rhi)%R).
Notation r16 := (float10R (Float10 (5) (-1))).
Notation _c3 := (float2R (Float2 (375299968947529) (-51))).
Notation _c4 := (float2R (Float2 (6004799503160511) (-57))).
Notation _c5 := (float2R (Float2 (4803840849707593) (-59))).
Notation _c6 := (float2R (Float2 (3202560482380763) (-61))).
Notation r26 := ((_rhi * _c6)%R).
Notation r24 := ((_c5 + r26)%R).
Notation r23 := ((_rhi * r24)%R).
Notation r21 := ((_c4 + r23)%R).
Notation r20 := ((_rhi * r21)%R).
Notation r18 := ((_c3 + r20)%R).
Notation r17 := ((_rhi * r18)%R).
Notation r15 := ((r16 + r17)%R).
Notation _Q := ((r14 * r15)%R).
Notation r4 := ((r5 + _Q)%R).
Variable _m : R.
Notation r3 := ((r4 + _m)%R).
Variable _a : R.
Notation _expR := ((r3 + _a)%R).
Variable _d4 : R.
Notation r35 := ((r6 + _d4)%R).
Notation r34 := ((_Tj * r35)%R).
Notation _r2 := ((rounding_float rndNE (53)%positive (-1074)%Z) r14).
Notation r58 := ((rounding_float rndNE (53)%positive (-1074)%Z) r26).
Notation r57 := ((_c5 + r58)%R).
Notation _t5 := ((rounding_float rndNE (53)%positive (-1074)%Z) r57).
Notation r55 := ((_rhi * _t5)%R).
Notation r54 := ((rounding_float rndNE (53)%positive (-1074)%Z) r55).
Notation r53 := ((_c4 + r54)%R).
Notation _t4 := ((rounding_float rndNE (53)%positive (-1074)%Z) r53).
Notation r51 := ((_rhi * _t4)%R).
Notation r50 := ((rounding_float rndNE (53)%positive (-1074)%Z) r51).
Notation r49 := ((_c3 + r50)%R).
Notation _t3 := ((rounding_float rndNE (53)%positive (-1074)%Z) r49).
Notation r47 := ((_rhi * _t3)%R).
Notation r46 := ((rounding_float rndNE (53)%positive (-1074)%Z) r47).
Notation r45 := ((r16 + r46)%R).
Notation _h := ((rounding_float rndNE (53)%positive (-1074)%Z) r45).
Notation r42 := ((_r2 * _h)%R).
Notation _q := ((rounding_float rndNE (53)%positive (-1074)%Z) r42).
Notation r40 := ((r8 + _q)%R).
Variable _d1 : R.
Notation r59 := ((r6 + _d1)%R).
Notation _P := ((r40 * r59)%R).
Notation r38 := ((r6 + _P)%R).
Variable _d2 : R.
Notation r61 := ((r6 + _d2)%R).
Notation _E := ((r38 * r61)%R).
Notation r33 := ((r34 * _E)%R).
Variable _d3 : R.
Notation r63 := ((r6 + _d3)%R).
Notation _Y := ((r33 * r63)%R).
Notation r65 := ((_Tj * _expR)%R).
Notation r31 := ((_Y - r65)%R).
Notation r30 := ((r31 / r65)%R).
Notation r69 := ((r35 * r63)%R).
Notation r68 := ((r69 * r61)%R).
Notation r72 := ((r38 - _expR)%R).
Notation r71 := ((r72 / _expR)%R).
Notation r70 := ((r6 + r71)%R).
Notation r67 := ((r68 * r70)%R).
Notation r66 := ((r67 - r6)%R).
Hypothesis a1 : (_Tj <> 0)%R -> (_expR <> 0)%R -> r30 = r66.
Lemma b1 : NZR _Tj -> NZR _expR -> r30 = r66.
 intros h0 h1.
 apply a1.
 exact h0.
 exact h1.
Qed.
Notation r77 := ((_q - _Q)%R).
Notation r76 := ((_dr + r77)%R).
Notation r75 := ((r76 - _m)%R).
Notation r74 := ((r75 - _a)%R).
Notation r78 := ((r40 * _d1)%R).
Notation r73 := ((r74 + r78)%R).
Hypothesis a2 : r72 = r73.
Lemma b2 : r72 = r73.
 apply a2.
Qed.
Definition f1 := Float2 (-1789941246693356131382101079560334144543371360062384257457043542964508560930560231090864825107617076781822724800155747281) (-408).
Definition f2 := Float2 (1789941246693356131382101079560334144543371360062384257457043542964508560930560231090864825107617076781822724800155747281) (-408).
Definition i1 := makepairF f1 f2.
Notation p1 := (BND _rhi i1). (* BND(rhi, [-0.0027077, 0.0027077]) *)
Definition f3 := Float2 (-1) (-62).
Definition f4 := Float2 (1) (-62).
Definition i2 := makepairF f3 f4.
Notation p2 := (BND _rlo i2). (* BND(rlo, [-2.1684e-19, 2.1684e-19]) *)
Definition s10 := (p1 /\ p2).
Definition f5 := Float2 (-1) (-113).
Definition f6 := Float2 (1) (-113).
Definition i3 := makepairF f5 f6.
Notation p3 := (BND _dr i3). (* BND(dr, [-9.62965e-35, 9.62965e-35]) *)
Definition s9 := (s10 /\ p3).
Definition f7 := Float2 (-16264149585115708508880501) (-161).
Definition f8 := Float2 (16264149585115708508880501) (-161).
Definition i4 := makepairF f7 f8.
Notation p4 := (BND _a i4). (* BND(a, [-5.56419e-24, 5.56419e-24]) *)
Definition s8 := (s9 /\ p4).
Definition f9 := Float2 (-25) (-75).
Definition f10 := Float2 (25) (-75).
Definition i5 := makepairF f9 f10.
Notation p5 := (BND _m i5). (* BND(m, [-6.61744e-22, 6.61744e-22]) *)
Definition s7 := (s8 /\ p5).
Definition f11 := Float2 (-1) (-105).
Definition f12 := Float2 (1) (-105).
Definition i6 := makepairF f11 f12.
Notation p6 := (BND _d1 i6). (* BND(d1, [-2.46519e-32, 2.46519e-32]) *)
Definition s6 := (s7 /\ p6).
Definition f13 := Float2 (-25) (-109).
Definition f14 := Float2 (25) (-109).
Definition i7 := makepairF f13 f14.
Notation p7 := (BND _d2 i7). (* BND(d2, [-3.85186e-32, 3.85186e-32]) *)
Definition s5 := (s6 /\ p7).
Definition f15 := Float2 (-21) (-108).
Definition f16 := Float2 (21) (-108).
Definition i8 := makepairF f15 f16.
Notation p8 := (BND _d3 i8). (* BND(d3, [-6.47112e-32, 6.47112e-32]) *)
Definition s4 := (s5 /\ p8).
Definition f17 := Float2 (-1) (-107).
Definition f18 := Float2 (1) (-107).
Definition i9 := makepairF f17 f18.
Notation p9 := (BND _d4 i9). (* BND(d4, [-6.16298e-33, 6.16298e-33]) *)
Definition s3 := (s4 /\ p9).
Definition f19 := Float2 (1) (0).
Definition f20 := Float2 (1) (1).
Definition i10 := makepairF f19 f20.
Notation p10 := (BND _Tj i10). (* BND(Tj, [1, 2]) *)
Definition s2 := (s3 /\ p10).
Definition f21 := Float2 (-1) (-69).
Definition f22 := Float2 (1) (-69).
Definition i11 := makepairF f21 f22.
Notation p11 := (BND r30 i11). (* BND((Y - Tj * expR) / (Tj * expR), [-1.69407e-21, 1.69407e-21]) *)
Definition s11 := (not p11).
Definition s1 := (s2 /\ s11).
Lemma l2 : s1 -> s11.
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj2 h1).
Qed.
Definition f23 := Float2 (-1940451968743734349429005615630888425849184977135049278493258051093773353876704910971816151182907067) (-399).
Definition f24 := Float2 (1940451968743734349429005615631312968878297610101015966437199657402946942461548019736339837469719349) (-399).
Definition i12 := makepairF f23 f24.
Notation p12 := (BND r30 i12). (* BND((Y - Tj * expR) / (Tj * expR), [-1.50292e-21, 1.50292e-21]) *)
Notation p13 := (BND r66 i12). (* BND((1 + d4) * (1 + d3) * (1 + d2) * (1 + (1 + P - expR) / expR) - 1, [-1.50292e-21, 1.50292e-21]) *)
Definition f25 := Float2 (1291124939043454294826019134032762202815423890798980867989480493293188761729927339263728903286192210806979769835190839621) (-399).
Definition f26 := Float2 (1291124939043454294829900037970249671514281902030243069384207975880424826974857796972225623582530463737687925823843466037) (-399).
Definition i13 := makepairF f25 f26.
Notation p14 := (BND r67 i13). (* BND((1 + d4) * (1 + d3) * (1 + d2) * (1 + (1 + P - expR) / expR), [1, 1]) *)
Definition f27 := Float2 (34175792574734561318320347298709095247289038577578668229169895531737058267055135781967774131158515) (-324).
Definition f28 := Float2 (34175792574734561318320347298716572419997506137834220409135436132431699818828574768866830210564621) (-324).
Definition i14 := makepairF f27 f28.
Notation p15 := (BND r68 i14). (* BND((1 + d4) * (1 + d3) * (1 + d2), [1, 1]) *)
Definition f29 := Float2 (52656145834278593348959013841831484196080475792916549332918861845) (-215).
Definition f30 := Float2 (52656145834278593348959013841838948122814619607632561921392115733) (-215).
Definition i15 := makepairF f29 f30.
Notation p16 := (BND r69 i15). (* BND((1 + d4) * (1 + d3), [1, 1]) *)
Definition f31 := Float2 (162259276829213363391578010288127) (-107).
Definition f32 := Float2 (162259276829213363391578010288129) (-107).
Definition i16 := makepairF f31 f32.
Notation p17 := (BND r35 i16). (* BND(1 + d4, [1, 1]) *)
Definition i17 := makepairF f19 f19.
Notation p18 := (BND r6 i17). (* BND(1, [1, 1]) *)
Lemma t1 : p18.
Proof.
 refine (constant1 _ i17 _) ; finalize.
Qed.
Lemma l9 : s1 -> p18 (* BND(1, [1, 1]) *).
Proof.
 intros h0.
 apply t1.
Qed.
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
Lemma l10 : s1 -> p9 (* BND(d4, [-6.16298e-33, 6.16298e-33]) *).
Proof.
 intros h0.
 assert (h1 := l11 h0).
 exact (proj2 h1).
Qed.
Lemma t2 : p18 -> p9 -> p17.
Proof.
 intros h0 h1.
 refine (add r6 _d4 i17 i9 i16 h0 h1 _) ; finalize.
Qed.
Lemma l8 : s1 -> p17 (* BND(1 + d4, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l9 h0).
 assert (h2 := l10 h0).
 apply t2. exact h1. exact h2.
Qed.
Definition f33 := Float2 (324518553658426726783156020576235) (-108).
Definition f34 := Float2 (324518553658426726783156020576277) (-108).
Definition i18 := makepairF f33 f34.
Notation p19 := (BND r63 i18). (* BND(1 + d3, [1, 1]) *)
Lemma l15 : s1 -> s4.
Proof.
 intros h0.
 assert (h1 := l11 h0).
 exact (proj1 h1).
Qed.
Lemma l14 : s1 -> p8 (* BND(d3, [-6.47112e-32, 6.47112e-32]) *).
Proof.
 intros h0.
 assert (h1 := l15 h0).
 exact (proj2 h1).
Qed.
Lemma t3 : p18 -> p8 -> p19.
Proof.
 intros h0 h1.
 refine (add r6 _d3 i17 i8 i18 h0 h1 _) ; finalize.
Qed.
Lemma l13 : s1 -> p19 (* BND(1 + d3, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l9 h0).
 assert (h2 := l14 h0).
 apply t3. exact h1. exact h2.
Qed.
Lemma t4 : p17 -> p19 -> p16.
Proof.
 intros h0 h1.
 refine (mul_pp r35 r63 i16 i18 i15 h0 h1 _) ; finalize.
Qed.
Lemma l7 : s1 -> p16 (* BND((1 + d4) * (1 + d3), [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 assert (h2 := l13 h0).
 apply t4. exact h1. exact h2.
Qed.
Definition f35 := Float2 (649037107316853453566312041152487) (-109).
Definition f36 := Float2 (649037107316853453566312041152537) (-109).
Definition i19 := makepairF f35 f36.
Notation p20 := (BND r61 i19). (* BND(1 + d2, [1, 1]) *)
Lemma l18 : s1 -> s5.
Proof.
 intros h0.
 assert (h1 := l15 h0).
 exact (proj1 h1).
Qed.
Lemma l17 : s1 -> p7 (* BND(d2, [-3.85186e-32, 3.85186e-32]) *).
Proof.
 intros h0.
 assert (h1 := l18 h0).
 exact (proj2 h1).
Qed.
Lemma t5 : p18 -> p7 -> p20.
Proof.
 intros h0 h1.
 refine (add r6 _d2 i17 i7 i19 h0 h1 _) ; finalize.
Qed.
Lemma l16 : s1 -> p20 (* BND(1 + d2, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l9 h0).
 assert (h2 := l17 h0).
 apply t5. exact h1. exact h2.
Qed.
Lemma t6 : p16 -> p20 -> p15.
Proof.
 intros h0 h1.
 refine (mul_pp r69 r61 i15 i19 i14 h0 h1 _) ; finalize.
Qed.
Lemma l6 : s1 -> p15 (* BND((1 + d4) * (1 + d3) * (1 + d2), [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 assert (h2 := l16 h0).
 apply t6. exact h1. exact h2.
Qed.
Definition f37 := Float2 (161390617380431786853252391754112930326820533775669098034554954261911788491597726902299834268266221998395867837708370583) (-396).
Definition f38 := Float2 (161390617380431786853737504746263553964392690327983841069277465305669164260507422426405834891751006931092028658885066089) (-396).
Definition i20 := makepairF f37 f38.
Notation p21 := (BND r70 i20). (* BND(1 + (1 + P - expR) / expR, [1, 1]) *)
Definition f39 := Float2 (-242556496075311818786078276157371517361255521878687884454847762053000311742392466348080410588347753) (-396).
Definition f40 := Float2 (242556496075311818786078276157371517361255521878687884454847762053000311742392466348080410588347753) (-396).
Definition i21 := makepairF f39 f40.
Notation p22 := (BND r71 i21). (* BND((1 + P - expR) / expR, [-1.50292e-21, 1.50292e-21]) *)
Definition f41 := Float2 (-3870395613614219150745492735270272549989029114659051879308337466083502100422346818893474299725094893) (-400).
Definition f42 := Float2 (3870395613614219150745492735270272549989029114659051879308337466083502100422346818893474299725094893) (-400).
Definition i22 := makepairF f41 f42.
Notation p23 := (BND r72 i22). (* BND(1 + P - expR, [-1.49885e-21, 1.49885e-21]) *)
Notation p24 := (BND r73 i22). (* BND(dr + (q - Q) - m - a + (rhi + rlo + q) * d1, [-1.49885e-21, 1.49885e-21]) *)
Definition f43 := Float2 (-3870395613614046552105992187368340662460378964670547204044479226683744321934569124546580498900639359) (-400).
Definition f44 := Float2 (3870395613614046552105992187368340662460378964670547204044479226683744321934569124546580498900639359) (-400).
Definition i23 := makepairF f43 f44.
Notation p25 := (BND r74 i23). (* BND(dr + (q - Q) - m - a, [-1.49885e-21, 1.49885e-21]) *)
Definition f45 := Float2 (-3856027481136257418680868143329115376876880013081198507085700340179649105285692453522812195293945471) (-400).
Definition f46 := Float2 (3856027481136257418680868143329115376876880013081198507085700340179649105285692453522812195293945471) (-400).
Definition i24 := makepairF f45 f46.
Notation p26 := (BND r75 i24). (* BND(dr + (q - Q) - m, [-1.49328e-21, 1.49328e-21]) *)
Definition f47 := Float2 (-2147237852399529352764850778393473685194716395195876291128067053921873324661180013504442525744684671) (-400).
Definition f48 := Float2 (2147237852399529352764850778393473685194716395195876291128067053921873324661180013504442525744684671) (-400).
Definition i25 := makepairF f47 f48.
Notation p27 := (BND r76 i25). (* BND(dr + (q - Q), [-8.31538e-22, 8.31538e-22]) *)
Lemma l30 : s1 -> s6.
Proof.
 intros h0.
 assert (h1 := l18 h0).
 exact (proj1 h1).
Qed.
Lemma l29 : s1 -> s7.
Proof.
 intros h0.
 assert (h1 := l30 h0).
 exact (proj1 h1).
Qed.
Lemma l28 : s1 -> s8.
Proof.
 intros h0.
 assert (h1 := l29 h0).
 exact (proj1 h1).
Qed.
Lemma l27 : s1 -> s9.
Proof.
 intros h0.
 assert (h1 := l28 h0).
 exact (proj1 h1).
Qed.
Lemma l26 : s1 -> p3 (* BND(dr, [-9.62965e-35, 9.62965e-35]) *).
Proof.
 intros h0.
 assert (h1 := l27 h0).
 exact (proj2 h1).
Qed.
Definition f49 := Float2 (-2147237852399280691146645885072395994070642984775826063052668380063153092672733433755936259056918143) (-400).
Definition f50 := Float2 (2147237852399280691146645885072395994070642984775826063052668380063153092672733433755936259056918143) (-400).
Definition i26 := makepairF f49 f50.
Notation p28 := (BND r77 i26). (* BND(q - Q, [-8.31538e-22, 8.31538e-22]) *)
Notation r80 := ((_q - r42)%R).
Notation r81 := ((r42 - _Q)%R).
Notation r79 := ((r80 + r81)%R).
Notation p29 := (BND r79 i26). (* BND(q - r2 * h + (r2 * h - Q), [-8.31538e-22, 8.31538e-22]) *)
Definition f51 := Float2 (-1) (-72).
Definition f52 := Float2 (1) (-72).
Definition i27 := makepairF f51 f52.
Notation p30 := (BND r80 i27). (* BND(q - r2 * h, [-2.11758e-22, 2.11758e-22]) *)
Definition f53 := Float2 (0) (0).
Definition f54 := Float2 (1) (-18).
Definition i28 := makepairF f53 f54.
Notation p31 := (ABS r42 i28). (* ABS(r2 * h, [0, 3.8147e-06]) *)
Definition f55 := Float2 (31) (-22).
Definition i29 := makepairF f53 f55.
Notation p32 := (ABS _r2 i29). (* ABS(r2, [0, 7.39098e-06]) *)
Definition f56 := Float2 (8655671911896551) (-70).
Definition i30 := makepairF f53 f56.
Notation p33 := (BND _r2 i30). (* BND(r2, [0, 7.33164e-06]) *)
Notation p34 := (BND r14 i30). (* BND(rhi * rhi, [0, 7.33164e-06]) *)
Definition f57 := Float2 (49948248928383353) (-64).
Definition i31 := makepairF f53 f57.
Notation p35 := (ABS _rhi i31). (* ABS(rhi, [0, 0.0027077]) *)
Lemma l40 : s1 -> s10.
Proof.
 intros h0.
 assert (h1 := l27 h0).
 exact (proj1 h1).
Qed.
Lemma l39 : s1 -> p1 (* BND(rhi, [-0.0027077, 0.0027077]) *).
Proof.
 intros h0.
 assert (h1 := l40 h0).
 exact (proj1 h1).
Qed.
Definition f58 := Float2 (-49948248928383353) (-64).
Definition i32 := makepairF f58 f57.
Notation p36 := (BND _rhi i32). (* BND(rhi, [-0.0027077, 0.0027077]) *)
Lemma t7 : p36 -> p35.
Proof.
 intros h0.
 refine (abs_of_bnd_o _rhi i32 i31 h0 _) ; finalize.
Qed.
Lemma l38 : s1 -> p35 (* ABS(rhi, [0, 0.0027077]) *).
Proof.
 intros h0.
 assert (h1 := l39 h0).
 apply t7. refine (subset _rhi i1 i32 h1 _) ; finalize.
Qed.
Lemma t8 : p35 -> p34.
Proof.
 intros h0.
 refine (square _rhi i31 i30 h0 _) ; finalize.
Qed.
Lemma l37 : s1 -> p34 (* BND(rhi * rhi, [0, 7.33164e-06]) *).
Proof.
 intros h0.
 assert (h1 := l38 h0).
 apply t8. exact h1.
Qed.
Lemma t9 : p34 -> p33.
Proof.
 intros h0.
 refine (float_round_ne _ _ r14 i30 i30 h0 _) ; finalize.
Qed.
Lemma l36 : s1 -> p33 (* BND(r2, [0, 7.33164e-06]) *).
Proof.
 intros h0.
 assert (h1 := l37 h0).
 apply t9. exact h1.
Qed.
Notation p37 := (BND _r2 i29). (* BND(r2, [0, 7.39098e-06]) *)
Lemma t10 : p37 -> p32.
Proof.
 intros h0.
 refine (abs_of_bnd_p _r2 i29 i29 h0 _) ; finalize.
Qed.
Lemma l35 : s1 -> p32 (* ABS(r2, [0, 7.39098e-06]) *).
Proof.
 intros h0.
 assert (h1 := l36 h0).
 apply t10. refine (subset _r2 i30 i29 h1 _) ; finalize.
Qed.
Definition f59 := Float2 (1) (-2).
Definition f60 := Float2 (33) (-6).
Definition i33 := makepairF f59 f60.
Notation p38 := (ABS _h i33). (* ABS(h, [0.25, 0.515625]) *)
Definition f61 := Float2 (2253833589664463) (-52).
Definition i34 := makepairF f59 f61.
Notation p39 := (BND _h i34). (* BND(h, [0.25, 0.500452]) *)
Definition f62 := Float2 (2307925595816409893) (-62).
Definition i35 := makepairF f59 f62.
Notation p40 := (BND r45 i35). (* BND(5e-1 + float<53,-1074,ne>(rhi * t3), [0.25, 0.500452]) *)
Definition f63 := Float2 (1) (-1).
Definition i36 := makepairF f63 f63.
Notation p41 := (BND r16 i36). (* BND(5e-1, [0.5, 0.5]) *)
Lemma t11 : p41.
Proof.
 refine (constant10 _ i36 _) ; finalize.
Qed.
Lemma l44 : s1 -> p41 (* BND(5e-1, [0.5, 0.5]) *).
Proof.
 intros h0.
 apply t11.
Qed.
Definition f64 := Float2 (-1) (-2).
Definition f65 := Float2 (2082586602715941) (-62).
Definition i37 := makepairF f64 f65.
Notation p42 := (BND r46 i37). (* BND(float<53,-1074,ne>(rhi * t3), [-0.25, 0.000451589]) *)
Notation p43 := (BND r47 i37). (* BND(rhi * t3, [-0.25, 0.000451589]) *)
Definition f66 := Float2 (1) (-3).
Definition f67 := Float2 (6008866504309299) (-55).
Definition i38 := makepairF f66 f67.
Notation p44 := (BND _t3 i38). (* BND(t3, [0.125, 0.16678]) *)
Notation p45 := (BND r49 i38). (* BND(c3 + float<53,-1074,ne>(rhi * t4), [0.125, 0.16678]) *)
Definition f68 := Float2 (5) (-5).
Definition f69 := Float2 (375299968947529) (-51).
Definition i39 := makepairF f68 f69.
Notation p46 := (BND _c3 i39). (* BND(c3, [0.15625, 0.166667]) *)
Lemma t12 : p46.
Proof.
 refine (constant2 _ i39 _) ; finalize.
Qed.
Lemma l49 : s1 -> p46 (* BND(c3, [0.15625, 0.166667]) *).
Proof.
 intros h0.
 apply t12.
Qed.
Definition f70 := Float2 (-1) (-5).
Definition f71 := Float2 (4067001148835) (-55).
Definition i40 := makepairF f70 f71.
Notation p47 := (BND r50 i40). (* BND(float<53,-1074,ne>(rhi * t4), [-0.03125, 0.000112882]) *)
Notation p48 := (BND r51 i40). (* BND(rhi * t4, [-0.03125, 0.000112882]) *)
Definition f72 := Float2 (1) (-5).
Definition f73 := Float2 (23468956291519) (-49).
Definition i41 := makepairF f72 f73.
Notation p49 := (BND _t4 i41). (* BND(t4, [0.03125, 0.0416892]) *)
Notation p50 := (BND r53 i41). (* BND(c4 + float<53,-1074,ne>(rhi * t5), [0.03125, 0.0416892]) *)
Definition f74 := Float2 (5) (-7).
Definition f75 := Float2 (6004799503160511) (-57).
Definition i42 := makepairF f74 f75.
Notation p51 := (BND _c4 i42). (* BND(c4, [0.0390625, 0.0416667]) *)
Lemma t13 : p51.
Proof.
 refine (constant2 _ i42 _) ; finalize.
Qed.
Lemma l54 : s1 -> p51 (* BND(c4, [0.0390625, 0.0416667]) *).
Proof.
 intros h0.
 apply t13.
Qed.
Definition f76 := Float2 (-1) (-7).
Definition f77 := Float2 (50832929193) (-51).
Definition i43 := makepairF f76 f77.
Notation p52 := (BND r54 i43). (* BND(float<53,-1074,ne>(rhi * t5), [-0.0078125, 2.25744e-05]) *)
Notation p53 := (BND r55 i43). (* BND(rhi * t5, [-0.0078125, 2.25744e-05]) *)
Definition f78 := Float2 (1) (-7).
Definition f79 := Float2 (146667747283) (-44).
Definition i44 := makepairF f78 f79.
Notation p54 := (BND _t5 i44). (* BND(t5, [0.0078125, 0.0083371]) *)
Notation p55 := (BND r57 i44). (* BND(c5 + float<53,-1074,ne>(rhi * c6), [0.0078125, 0.0083371]) *)
Definition f80 := Float2 (17) (-11).
Definition f81 := Float2 (4803840849707593) (-59).
Definition i45 := makepairF f80 f81.
Notation p56 := (BND _c5 i45). (* BND(c5, [0.00830078, 0.00833334]) *)
Lemma t14 : p56.
Proof.
 refine (constant2 _ i45 _) ; finalize.
Qed.
Lemma l59 : s1 -> p56 (* BND(c5, [0.00830078, 0.00833334]) *).
Proof.
 intros h0.
 apply t14.
Qed.
Definition f82 := Float2 (-1) (-11).
Definition f83 := Float2 (529270815) (-47).
Definition i46 := makepairF f82 f83.
Notation p57 := (BND r58 i46). (* BND(float<53,-1074,ne>(rhi * c6), [-0.000488281, 3.7607e-06]) *)
Definition f84 := Float2 (-1) (-18).
Definition f85 := Float2 (1004099556744647183256910140498600410973725863954556380920948745858744193193165997405500839) (-317).
Definition i47 := makepairF f84 f85.
Notation p58 := (BND r26 i47). (* BND(rhi * c6, [-3.8147e-06, 3.7607e-06]) *)
Definition f86 := Float2 (1) (-10).
Definition f87 := Float2 (3202560482380763) (-61).
Definition i48 := makepairF f86 f87.
Notation p59 := (BND _c6 i48). (* BND(c6, [0.000976562, 0.00138889]) *)
Lemma t15 : p59.
Proof.
 refine (constant2 _ i48 _) ; finalize.
Qed.
Lemma l62 : s1 -> p59 (* BND(c6, [0.000976562, 0.00138889]) *).
Proof.
 intros h0.
 apply t15.
Qed.
Definition f88 := Float2 (-89) (-15).
Definition f89 := Float2 (5648058688635789287208008079878219004599358432797957719907816954590062843258047282516771917) (-310).
Definition i49 := makepairF f88 f89.
Notation p60 := (BND _rhi i49). (* BND(rhi, [-0.00271606, 0.0027077]) *)
Lemma t16 : p60 -> p59 -> p58.
Proof.
 intros h0 h1.
 refine (mul_op _rhi _c6 i49 i48 i47 h0 h1 _) ; finalize.
Qed.
Lemma l61 : s1 -> p58 (* BND(rhi * c6, [-3.8147e-06, 3.7607e-06]) *).
Proof.
 intros h0.
 assert (h1 := l39 h0).
 assert (h2 := l62 h0).
 apply t16. refine (subset _rhi i1 i49 h1 _) ; finalize. exact h2.
Qed.
Notation p61 := (BND r26 i46). (* BND(rhi * c6, [-0.000488281, 3.7607e-06]) *)
Lemma t17 : p61 -> p57.
Proof.
 intros h0.
 refine (float_round_ne _ _ r26 i46 i46 h0 _) ; finalize.
Qed.
Lemma l60 : s1 -> p57 (* BND(float<53,-1074,ne>(rhi * c6), [-0.000488281, 3.7607e-06]) *).
Proof.
 intros h0.
 assert (h1 := l61 h0).
 apply t17. refine (subset r26 i47 i46 h1 _) ; finalize.
Qed.
Definition f90 := Float2 (1172812707449) (-47).
Definition i50 := makepairF f80 f90.
Notation p62 := (BND _c5 i50). (* BND(c5, [0.00830078, 0.00833334]) *)
Lemma t18 : p62 -> p57 -> p55.
Proof.
 intros h0 h1.
 refine (add _c5 r58 i50 i46 i44 h0 h1 _) ; finalize.
Qed.
Lemma l58 : s1 -> p55 (* BND(c5 + float<53,-1074,ne>(rhi * c6), [0.0078125, 0.0083371]) *).
Proof.
 intros h0.
 assert (h1 := l59 h0).
 assert (h2 := l60 h0).
 apply t18. refine (subset _c5 i45 i50 h1 _) ; finalize. exact h2.
Qed.
Lemma t19 : p55 -> p54.
Proof.
 intros h0.
 refine (float_round_ne _ _ r57 i44 i44 h0 _) ; finalize.
Qed.
Lemma l57 : s1 -> p54 (* BND(t5, [0.0078125, 0.0083371]) *).
Proof.
 intros h0.
 assert (h1 := l58 h0).
 apply t19. exact h1.
Qed.
Definition f91 := Float2 (-1) (-1).
Definition f92 := Float2 (95268724305) (-45).
Definition i51 := makepairF f91 f92.
Notation p63 := (BND _rhi i51). (* BND(rhi, [-0.5, 0.0027077]) *)
Lemma t20 : p63 -> p54 -> p53.
Proof.
 intros h0 h1.
 refine (mul_op _rhi _t5 i51 i44 i43 h0 h1 _) ; finalize.
Qed.
Lemma l56 : s1 -> p53 (* BND(rhi * t5, [-0.0078125, 2.25744e-05]) *).
Proof.
 intros h0.
 assert (h1 := l39 h0).
 assert (h2 := l57 h0).
 apply t20. refine (subset _rhi i1 i51 h1 _) ; finalize. exact h2.
Qed.
Lemma t21 : p53 -> p52.
Proof.
 intros h0.
 refine (float_round_ne _ _ r55 i43 i43 h0 _) ; finalize.
Qed.
Lemma l55 : s1 -> p52 (* BND(float<53,-1074,ne>(rhi * t5), [-0.0078125, 2.25744e-05]) *).
Proof.
 intros h0.
 assert (h1 := l56 h0).
 apply t21. exact h1.
Qed.
Definition f93 := Float2 (93824992236883) (-51).
Definition i52 := makepairF f74 f93.
Notation p64 := (BND _c4 i52). (* BND(c4, [0.0390625, 0.0416667]) *)
Lemma t22 : p64 -> p52 -> p50.
Proof.
 intros h0 h1.
 refine (add _c4 r54 i52 i43 i41 h0 h1 _) ; finalize.
Qed.
Lemma l53 : s1 -> p50 (* BND(c4 + float<53,-1074,ne>(rhi * t5), [0.03125, 0.0416892]) *).
Proof.
 intros h0.
 assert (h1 := l54 h0).
 assert (h2 := l55 h0).
 apply t22. refine (subset _c4 i42 i52 h1 _) ; finalize. exact h2.
Qed.
Lemma t23 : p50 -> p49.
Proof.
 intros h0.
 refine (float_round_ne _ _ r53 i41 i41 h0 _) ; finalize.
Qed.
Lemma l52 : s1 -> p49 (* BND(t4, [0.03125, 0.0416892]) *).
Proof.
 intros h0.
 assert (h1 := l53 h0).
 apply t23. exact h1.
Qed.
Definition f94 := Float2 (48777586844125) (-54).
Definition i53 := makepairF f91 f94.
Notation p65 := (BND _rhi i53). (* BND(rhi, [-0.5, 0.0027077]) *)
Lemma t24 : p65 -> p49 -> p48.
Proof.
 intros h0 h1.
 refine (mul_op _rhi _t4 i53 i41 i40 h0 h1 _) ; finalize.
Qed.
Lemma l51 : s1 -> p48 (* BND(rhi * t4, [-0.03125, 0.000112882]) *).
Proof.
 intros h0.
 assert (h1 := l39 h0).
 assert (h2 := l52 h0).
 apply t24. refine (subset _rhi i1 i53 h1 _) ; finalize. exact h2.
Qed.
Lemma t25 : p48 -> p47.
Proof.
 intros h0.
 refine (float_round_ne _ _ r51 i40 i40 h0 _) ; finalize.
Qed.
Lemma l50 : s1 -> p47 (* BND(float<53,-1074,ne>(rhi * t4), [-0.03125, 0.000112882]) *).
Proof.
 intros h0.
 assert (h1 := l51 h0).
 apply t25. exact h1.
Qed.
Lemma t26 : p46 -> p47 -> p45.
Proof.
 intros h0 h1.
 refine (add _c3 r50 i39 i40 i38 h0 h1 _) ; finalize.
Qed.
Lemma l48 : s1 -> p45 (* BND(c3 + float<53,-1074,ne>(rhi * t4), [0.125, 0.16678]) *).
Proof.
 intros h0.
 assert (h1 := l49 h0).
 assert (h2 := l50 h0).
 apply t26. exact h1. exact h2.
Qed.
Lemma t27 : p45 -> p44.
Proof.
 intros h0.
 refine (float_round_ne _ _ r49 i38 i38 h0 _) ; finalize.
Qed.
Lemma l47 : s1 -> p44 (* BND(t3, [0.125, 0.16678]) *).
Proof.
 intros h0.
 assert (h1 := l48 h0).
 apply t27. exact h1.
Qed.
Definition f95 := Float2 (-1) (0).
Definition i54 := makepairF f95 f57.
Notation p66 := (BND _rhi i54). (* BND(rhi, [-1, 0.0027077]) *)
Lemma t28 : p66 -> p44 -> p43.
Proof.
 intros h0 h1.
 refine (mul_op _rhi _t3 i54 i38 i37 h0 h1 _) ; finalize.
Qed.
Lemma l46 : s1 -> p43 (* BND(rhi * t3, [-0.25, 0.000451589]) *).
Proof.
 intros h0.
 assert (h1 := l39 h0).
 assert (h2 := l47 h0).
 apply t28. refine (subset _rhi i1 i54 h1 _) ; finalize. exact h2.
Qed.
Lemma t29 : p43 -> p42.
Proof.
 intros h0.
 refine (float_round_ne _ _ r47 i37 i37 h0 _) ; finalize.
Qed.
Lemma l45 : s1 -> p42 (* BND(float<53,-1074,ne>(rhi * t3), [-0.25, 0.000451589]) *).
Proof.
 intros h0.
 assert (h1 := l46 h0).
 apply t29. exact h1.
Qed.
Lemma t30 : p41 -> p42 -> p40.
Proof.
 intros h0 h1.
 refine (add r16 r46 i36 i37 i35 h0 h1 _) ; finalize.
Qed.
Lemma l43 : s1 -> p40 (* BND(5e-1 + float<53,-1074,ne>(rhi * t3), [0.25, 0.500452]) *).
Proof.
 intros h0.
 assert (h1 := l44 h0).
 assert (h2 := l45 h0).
 apply t30. exact h1. exact h2.
Qed.
Notation p67 := (BND r45 i34). (* BND(5e-1 + float<53,-1074,ne>(rhi * t3), [0.25, 0.500452]) *)
Lemma t31 : p67 -> p39.
Proof.
 intros h0.
 refine (float_round_ne _ _ r45 i34 i34 h0 _) ; finalize.
Qed.
Lemma l42 : s1 -> p39 (* BND(h, [0.25, 0.500452]) *).
Proof.
 intros h0.
 assert (h1 := l43 h0).
 apply t31. refine (subset r45 i35 i34 h1 _) ; finalize.
Qed.
Notation p68 := (BND _h i33). (* BND(h, [0.25, 0.515625]) *)
Lemma t32 : p68 -> p38.
Proof.
 intros h0.
 refine (abs_of_bnd_p _h i33 i33 h0 _) ; finalize.
Qed.
Lemma l41 : s1 -> p38 (* ABS(h, [0.25, 0.515625]) *).
Proof.
 intros h0.
 assert (h1 := l42 h0).
 apply t32. refine (subset _h i34 i33 h1 _) ; finalize.
Qed.
Lemma t33 : p32 -> p38 -> p31.
Proof.
 intros h0 h1.
 refine (mul_aa _r2 _h i29 i33 i28 h0 h1 _) ; finalize.
Qed.
Lemma l34 : s1 -> p31 (* ABS(r2 * h, [0, 3.8147e-06]) *).
Proof.
 intros h0.
 assert (h1 := l35 h0).
 assert (h2 := l41 h0).
 apply t33. exact h1. exact h2.
Qed.
Lemma t34 : p31 -> p30.
Proof.
 intros h0.
 refine (float_absolute_wide_ne _ _ r42 i28 i27 h0 _) ; finalize.
Qed.
Lemma l33 : s1 -> p30 (* BND(q - r2 * h, [-2.11758e-22, 2.11758e-22]) *).
Proof.
 intros h0.
 assert (h1 := l34 h0).
 apply t34. exact h1.
Qed.
Definition f96 := Float2 (-1600425171203527710053520328292990652732350627052522953946225728460664842872889452950057964801154687) (-400).
Definition f97 := Float2 (1600425171203527710053520328292990652732350627052522953946225728460664842872889452950057964801154687) (-400).
Definition i55 := makepairF f96 f97.
Notation p69 := (BND r81 i55). (* BND(r2 * h - Q, [-6.19779e-22, 6.19779e-22]) *)
Notation r84 := ((_h - r15)%R).
Notation r83 := ((_r2 * r84)%R).
Notation r86 := ((_r2 - r14)%R).
Notation r85 := ((r86 * r15)%R).
Notation r82 := ((r83 + r85)%R).
Notation p70 := (BND r82 i55). (* BND(r2 * (h - (5e-1 + rhi * (c3 + rhi * (c4 + rhi * (c5 + rhi * c6))))) + (r2 - rhi * rhi) * (5e-1 + rhi * (c3 + rhi * (c4 + rhi * (c5 + rhi * c6)))), [-6.19779e-22, 6.19779e-22]) *)
Definition f98 := Float2 (-16849897933467242691601081027000920975229188578212229012330612243688235640001673004689349592929211159) (-404).
Definition f99 := Float2 (16849897933467242691601081027000920975229188578212229012330612243688235640001673004689349592929211159) (-404).
Definition i56 := makepairF f98 f99.
Notation p71 := (BND r83 i56). (* BND(r2 * (h - (5e-1 + rhi * (c3 + rhi * (c4 + rhi * (c5 + rhi * c6))))), [-4.0783e-22, 4.0783e-22]) *)
Definition f100 := Float2 (-140273697666558992185128424342108808242432946817505915148789067993080107706121505089420065149777494939) (-390).
Definition f101 := Float2 (140273697666558992185128424342108808242432946817505915148789067993080107706121505089420065149777494939) (-390).
Definition i57 := makepairF f100 f101.
Notation p72 := (BND r84 i57). (* BND(h - (5e-1 + rhi * (c3 + rhi * (c4 + rhi * (c5 + rhi * c6)))), [-5.5626e-17, 5.5626e-17]) *)
Notation r88 := ((_h - r45)%R).
Notation r89 := ((r45 - r15)%R).
Notation r87 := ((r88 + r89)%R).
Notation p73 := (BND r87 i57). (* BND(h - (5e-1 + float<53,-1074,ne>(rhi * t3)) + (5e-1 + float<53,-1074,ne>(rhi * t3) - (5e-1 + rhi * (c3 + rhi * (c4 + rhi * (c5 + rhi * c6))))), [-5.5626e-17, 5.5626e-17]) *)
Definition f102 := Float2 (-2307925595816409893) (-115).
Definition f103 := Float2 (2307925595816409893) (-115).
Definition i58 := makepairF f102 f103.
Notation p74 := (BND r88 i58). (* BND(h - (5e-1 + float<53,-1074,ne>(rhi * t3)), [-5.55613e-17, 5.55613e-17]) *)
Definition f104 := Float2 (-1) (-53).
Definition f105 := Float2 (1) (-53).
Definition i59 := makepairF f104 f105.
Notation p75 := (REL _h r45 i59). (* REL(h, 5e-1 + float<53,-1074,ne>(rhi * t3), [-1.11022e-16, 1.11022e-16]) *)
Notation p76 := (FIX r45 (-1074)). (* FIX(5e-1 + float<53,-1074,ne>(rhi * t3), -1074) *)
Notation p77 := (FIX r16 (-1)). (* FIX(5e-1, -1) *)
Notation p78 := (ABS r16 i36). (* ABS(5e-1, [0.5, 0.5]) *)
Lemma t35 : p41 -> p78.
Proof.
 intros h0.
 refine (abs_of_bnd_p r16 i36 i36 h0 _) ; finalize.
Qed.
Lemma l72 : s1 -> p78 (* ABS(5e-1, [0.5, 0.5]) *).
Proof.
 intros h0.
 assert (h1 := l44 h0).
 apply t35. exact h1.
Qed.
Lemma t36 : p78 -> p77.
Proof.
 intros h0.
 refine (fix_of_singleton_bnd r16 i36 (-1) h0 _) ; finalize.
Qed.
Lemma l71 : s1 -> p77 (* FIX(5e-1, -1) *).
Proof.
 intros h0.
 assert (h1 := l72 h0).
 apply t36. exact h1.
Qed.
Notation p79 := (FIX r46 (-1074)). (* FIX(float<53,-1074,ne>(rhi * t3), -1074) *)
Lemma t37 : p79.
Proof.
 refine (fix_of_float _ _ _ _ (-1074) _) ; finalize.
Qed.
Lemma l73 : s1 -> p79 (* FIX(float<53,-1074,ne>(rhi * t3), -1074) *).
Proof.
 intros h0.
 apply t37.
Qed.
Lemma t38 : p77 -> p79 -> p76.
Proof.
 intros h0 h1.
 refine (add_fix r16 r46 (-1) (-1074) (-1074) h0 h1 _) ; finalize.
Qed.
Lemma l70 : s1 -> p76 (* FIX(5e-1 + float<53,-1074,ne>(rhi * t3), -1074) *).
Proof.
 intros h0.
 assert (h1 := l71 h0).
 assert (h2 := l73 h0).
 apply t38. exact h1. exact h2.
Qed.
Lemma t39 : p76 -> p75.
Proof.
 intros h0.
 refine (rel_of_fix_float_ne _ _ (-1074) r45 i59 h0 _) ; finalize.
Qed.
Lemma l69 : s1 -> p75 (* REL(h, 5e-1 + float<53,-1074,ne>(rhi * t3), [-1.11022e-16, 1.11022e-16]) *).
Proof.
 intros h0.
 assert (h1 := l70 h0).
 apply t39. exact h1.
Qed.
Lemma t40 : p75 -> p40 -> p74.
Proof.
 intros h0 h1.
 refine (error_of_rel_op _h r45 i59 i35 i58 h0 h1 _) ; finalize.
Qed.
Lemma l68 : s1 -> p74 (* BND(h - (5e-1 + float<53,-1074,ne>(rhi * t3)), [-5.55613e-17, 5.55613e-17]) *).
Proof.
 intros h0.
 assert (h1 := l69 h0).
 assert (h2 := l43 h0).
 apply t40. exact h1. exact h2.
Qed.
Definition f106 := Float2 (-163220773931781474283664310175941380751968795415830856878763351164237000768644912122347407322530715) (-390).
Definition f107 := Float2 (163220773931781474283664310175941380751968795415830856878763351164237000768644912122347407322530715) (-390).
Definition i60 := makepairF f106 f107.
Notation p80 := (BND r89 i60). (* BND(5e-1 + float<53,-1074,ne>(rhi * t3) - (5e-1 + rhi * (c3 + rhi * (c4 + rhi * (c5 + rhi * c6)))), [-6.47258e-20, 6.47258e-20]) *)
Notation r90 := ((r46 - r17)%R).
Notation p81 := (BND r90 i60). (* BND(float<53,-1074,ne>(rhi * t3) - rhi * (c3 + rhi * (c4 + rhi * (c5 + rhi * c6))), [-6.47258e-20, 6.47258e-20]) *)
Notation r92 := ((r46 - r47)%R).
Notation r93 := ((r47 - r17)%R).
Notation r91 := ((r92 + r93)%R).
Notation p82 := (BND r91 i60). (* BND(float<53,-1074,ne>(rhi * t3) - rhi * t3 + (rhi * t3 - rhi * (c3 + rhi * (c4 + rhi * (c5 + rhi * c6)))), [-6.47258e-20, 6.47258e-20]) *)
Definition f108 := Float2 (-1) (-65).
Definition f109 := Float2 (1) (-65).
Definition i61 := makepairF f108 f109.
Notation p83 := (BND r92 i61). (* BND(float<53,-1074,ne>(rhi * t3) - rhi * t3, [-2.71051e-20, 2.71051e-20]) *)
Definition f110 := Float2 (1) (-11).
Definition i62 := makepairF f53 f110.
Notation p84 := (ABS r47 i62). (* ABS(rhi * t3, [0, 0.000488281]) *)
Definition f111 := Float2 (11) (-6).
Definition i63 := makepairF f66 f111.
Notation p85 := (ABS _t3 i63). (* ABS(t3, [0.125, 0.171875]) *)
Notation p86 := (BND _t3 i63). (* BND(t3, [0.125, 0.171875]) *)
Lemma t41 : p86 -> p85.
Proof.
 intros h0.
 refine (abs_of_bnd_p _t3 i63 i63 h0 _) ; finalize.
Qed.
Lemma l79 : s1 -> p85 (* ABS(t3, [0.125, 0.171875]) *).
Proof.
 intros h0.
 assert (h1 := l47 h0).
 apply t41. refine (subset _t3 i38 i63 h1 _) ; finalize.
Qed.
Definition f112 := Float2 (23) (-13).
Definition i64 := makepairF f53 f112.
Notation p87 := (ABS _rhi i64). (* ABS(rhi, [0, 0.00280762]) *)
Lemma t42 : p87 -> p85 -> p84.
Proof.
 intros h0 h1.
 refine (mul_aa _rhi _t3 i64 i63 i62 h0 h1 _) ; finalize.
Qed.
Lemma l78 : s1 -> p84 (* ABS(rhi * t3, [0, 0.000488281]) *).
Proof.
 intros h0.
 assert (h1 := l38 h0).
 assert (h2 := l79 h0).
 apply t42. refine (abs_subset _rhi i31 i64 h1 _) ; finalize. exact h2.
Qed.
Lemma t43 : p84 -> p83.
Proof.
 intros h0.
 refine (float_absolute_wide_ne _ _ r47 i62 i61 h0 _) ; finalize.
Qed.
Lemma l77 : s1 -> p83 (* BND(float<53,-1074,ne>(rhi * t3) - rhi * t3, [-2.71051e-20, 2.71051e-20]) *).
Proof.
 intros h0.
 assert (h1 := l78 h0).
 apply t43. exact h1.
Qed.
Definition f113 := Float2 (-94869188782312351647023615578515713084682250700417968240458019713925969543664414521612620540560283) (-390).
Definition f114 := Float2 (94869188782312351647023615578515713084682250700417968240458019713925969543664414521612620540560283) (-390).
Definition i65 := makepairF f113 f114.
Notation p88 := (BND r93 i65). (* BND(rhi * t3 - rhi * (c3 + rhi * (c4 + rhi * (c5 + rhi * c6))), [-3.76207e-20, 3.76207e-20]) *)
Notation r95 := ((_t3 - r18)%R).
Notation r94 := ((_rhi * r95)%R).
Notation p89 := (BND r94 i65). (* BND(rhi * (t3 - (c3 + rhi * (c4 + rhi * (c5 + rhi * c6)))), [-3.76207e-20, 3.76207e-20]) *)
Definition f115 := Float2 (-273725131056548084072228089045002773008117621448836790219957262257652855582183490951766664687050711) (-383).
Definition f116 := Float2 (273725131056548084072228089045002773008117621448836790219957262257652855582183490951766664687050711) (-383).
Definition i66 := makepairF f115 f116.
Notation p90 := (BND r95 i66). (* BND(t3 - (c3 + rhi * (c4 + rhi * (c5 + rhi * c6))), [-1.3894e-17, 1.3894e-17]) *)
Notation r97 := ((_t3 - r49)%R).
Notation r98 := ((r49 - r18)%R).
Notation r96 := ((r97 + r98)%R).
Notation p91 := (BND r96 i66). (* BND(t3 - (c3 + float<53,-1074,ne>(rhi * t4)) + (c3 + float<53,-1074,ne>(rhi * t4) - (c3 + rhi * (c4 + rhi * (c5 + rhi * c6)))), [-1.3894e-17, 1.3894e-17]) *)
Definition f117 := Float2 (-1) (-56).
Definition f118 := Float2 (1) (-56).
Definition i67 := makepairF f117 f118.
Notation p92 := (BND r97 i67). (* BND(t3 - (c3 + float<53,-1074,ne>(rhi * t4)), [-1.38778e-17, 1.38778e-17]) *)
Definition i68 := makepairF f66 f59.
Notation p93 := (ABS r49 i68). (* ABS(c3 + float<53,-1074,ne>(rhi * t4), [0.125, 0.25]) *)
Definition f119 := Float2 (3) (-4).
Definition i69 := makepairF f68 f119.
Notation p94 := (ABS _c3 i69). (* ABS(c3, [0.15625, 0.1875]) *)
Notation p95 := (BND _c3 i69). (* BND(c3, [0.15625, 0.1875]) *)
Lemma t44 : p95 -> p94.
Proof.
 intros h0.
 refine (abs_of_bnd_p _c3 i69 i69 h0 _) ; finalize.
Qed.
Lemma l86 : s1 -> p94 (* ABS(c3, [0.15625, 0.1875]) *).
Proof.
 intros h0.
 assert (h1 := l49 h0).
 apply t44. refine (subset _c3 i39 i69 h1 _) ; finalize.
Qed.
Definition i70 := makepairF f53 f72.
Notation p96 := (ABS r50 i70). (* ABS(float<53,-1074,ne>(rhi * t4), [0, 0.03125]) *)
Definition i71 := makepairF f70 f72.
Notation p97 := (BND r50 i71). (* BND(float<53,-1074,ne>(rhi * t4), [-0.03125, 0.03125]) *)
Lemma t45 : p97 -> p96.
Proof.
 intros h0.
 refine (abs_of_bnd_o r50 i71 i70 h0 _) ; finalize.
Qed.
Lemma l87 : s1 -> p96 (* ABS(float<53,-1074,ne>(rhi * t4), [0, 0.03125]) *).
Proof.
 intros h0.
 assert (h1 := l50 h0).
 apply t45. refine (subset r50 i40 i71 h1 _) ; finalize.
Qed.
Lemma t46 : p94 -> p96 -> p93.
Proof.
 intros h0 h1.
 refine (add_aa_p _c3 r50 i69 i70 i68 h0 h1 _) ; finalize.
Qed.
Lemma l85 : s1 -> p93 (* ABS(c3 + float<53,-1074,ne>(rhi * t4), [0.125, 0.25]) *).
Proof.
 intros h0.
 assert (h1 := l86 h0).
 assert (h2 := l87 h0).
 apply t46. exact h1. exact h2.
Qed.
Lemma t47 : p93 -> p92.
Proof.
 intros h0.
 refine (float_absolute_wide_ne _ _ r49 i68 i67 h0 _) ; finalize.
Qed.
Lemma l84 : s1 -> p92 (* BND(t3 - (c3 + float<53,-1074,ne>(rhi * t4)), [-1.38778e-17, 1.38778e-17]) *).
Proof.
 intros h0.
 assert (h1 := l85 h0).
 apply t47. exact h1.
Qed.
Definition f120 := Float2 (-318790458671593525665310655300102338971442587185235666735936456408730682261500548827517559168983) (-383).
Definition f121 := Float2 (318790458671593525665310655300102338971442587185235666735936456408730682261500548827517559168983) (-383).
Definition i72 := makepairF f120 f121.
Notation p98 := (BND r98 i72). (* BND(c3 + float<53,-1074,ne>(rhi * t4) - (c3 + rhi * (c4 + rhi * (c5 + rhi * c6))), [-1.61814e-20, 1.61814e-20]) *)
Notation r99 := ((r50 - r20)%R).
Notation p99 := (BND r99 i72). (* BND(float<53,-1074,ne>(rhi * t4) - rhi * (c4 + rhi * (c5 + rhi * c6)), [-1.61814e-20, 1.61814e-20]) *)
Notation r101 := ((r50 - r51)%R).
Notation r102 := ((r51 - r20)%R).
Notation r100 := ((r101 + r102)%R).
Notation p100 := (BND r100 i72). (* BND(float<53,-1074,ne>(rhi * t4) - rhi * t4 + (rhi * t4 - rhi * (c4 + rhi * (c5 + rhi * c6))), [-1.61814e-20, 1.61814e-20]) *)
Definition f122 := Float2 (-1) (-67).
Definition f123 := Float2 (1) (-67).
Definition i73 := makepairF f122 f123.
Notation p101 := (BND r101 i73). (* BND(float<53,-1074,ne>(rhi * t4) - rhi * t4, [-6.77626e-21, 6.77626e-21]) *)
Definition f124 := Float2 (1) (-13).
Definition i74 := makepairF f53 f124.
Notation p102 := (ABS r51 i74). (* ABS(rhi * t4, [0, 0.00012207]) *)
Definition f125 := Float2 (11) (-8).
Definition i75 := makepairF f72 f125.
Notation p103 := (ABS _t4 i75). (* ABS(t4, [0.03125, 0.0429688]) *)
Notation p104 := (BND _t4 i75). (* BND(t4, [0.03125, 0.0429688]) *)
Lemma t48 : p104 -> p103.
Proof.
 intros h0.
 refine (abs_of_bnd_p _t4 i75 i75 h0 _) ; finalize.
Qed.
Lemma l93 : s1 -> p103 (* ABS(t4, [0.03125, 0.0429688]) *).
Proof.
 intros h0.
 assert (h1 := l52 h0).
 apply t48. refine (subset _t4 i41 i75 h1 _) ; finalize.
Qed.
Lemma t49 : p87 -> p103 -> p102.
Proof.
 intros h0 h1.
 refine (mul_aa _rhi _t4 i64 i75 i74 h0 h1 _) ; finalize.
Qed.
Lemma l92 : s1 -> p102 (* ABS(rhi * t4, [0, 0.00012207]) *).
Proof.
 intros h0.
 assert (h1 := l38 h0).
 assert (h2 := l93 h0).
 apply t49. refine (abs_subset _rhi i31 i64 h1 _) ; finalize. exact h2.
Qed.
Lemma t50 : p102 -> p101.
Proof.
 intros h0.
 refine (float_absolute_wide_ne _ _ r51 i74 i73 h0 _) ; finalize.
Qed.
Lemma l91 : s1 -> p101 (* BND(float<53,-1074,ne>(rhi * t4) - rhi * t4, [-6.77626e-21, 6.77626e-21]) *).
Proof.
 intros h0.
 assert (h1 := l92 h0).
 apply t50. exact h1.
Qed.
Definition f126 := Float2 (-185291268926536645515621798664505331808773554537944868614246355919841949400210514451082428735447) (-383).
Definition f127 := Float2 (185291268926536645515621798664505331808773554537944868614246355919841949400210514451082428735447) (-383).
Definition i76 := makepairF f126 f127.
Notation p105 := (BND r102 i76). (* BND(rhi * t4 - rhi * (c4 + rhi * (c5 + rhi * c6)), [-9.40517e-21, 9.40517e-21]) *)
Notation r104 := ((_t4 - r21)%R).
Notation r103 := ((_rhi * r104)%R).
Notation p106 := (BND r103 i76). (* BND(rhi * (t4 - (c4 + rhi * (c5 + rhi * c6))), [-9.40517e-21, 9.40517e-21]) *)
Definition f128 := Float2 (-4276952508737504282131093701861943065350056194785816112712042414222447773945842284297614874604065) (-379).
Definition f129 := Float2 (4276952508737504282131093701861943065350056194785816112712042414222447773945842284297614874604065) (-379).
Definition i77 := makepairF f128 f129.
Notation p107 := (BND r104 i77). (* BND(t4 - (c4 + rhi * (c5 + rhi * c6)), [-3.47349e-18, 3.47349e-18]) *)
Notation r106 := ((_t4 - r53)%R).
Notation r107 := ((r53 - r21)%R).
Notation r105 := ((r106 + r107)%R).
Notation p108 := (BND r105 i77). (* BND(t4 - (c4 + float<53,-1074,ne>(rhi * t5)) + (c4 + float<53,-1074,ne>(rhi * t5) - (c4 + rhi * (c5 + rhi * c6))), [-3.47349e-18, 3.47349e-18]) *)
Definition f130 := Float2 (-1) (-58).
Definition f131 := Float2 (1) (-58).
Definition i78 := makepairF f130 f131.
Notation p109 := (BND r106 i78). (* BND(t4 - (c4 + float<53,-1074,ne>(rhi * t5)), [-3.46945e-18, 3.46945e-18]) *)
Definition f132 := Float2 (1) (-4).
Definition i79 := makepairF f72 f132.
Notation p110 := (ABS r53 i79). (* ABS(c4 + float<53,-1074,ne>(rhi * t5), [0.03125, 0.0625]) *)
Notation p111 := (BND r53 i79). (* BND(c4 + float<53,-1074,ne>(rhi * t5), [0.03125, 0.0625]) *)
Lemma t51 : p111 -> p110.
Proof.
 intros h0.
 refine (abs_of_bnd_p r53 i79 i79 h0 _) ; finalize.
Qed.
Lemma l99 : s1 -> p110 (* ABS(c4 + float<53,-1074,ne>(rhi * t5), [0.03125, 0.0625]) *).
Proof.
 intros h0.
 assert (h1 := l53 h0).
 apply t51. refine (subset r53 i41 i79 h1 _) ; finalize.
Qed.
Lemma t52 : p110 -> p109.
Proof.
 intros h0.
 refine (float_absolute_wide_ne _ _ r53 i79 i78 h0 _) ; finalize.
Qed.
Lemma l98 : s1 -> p109 (* BND(t4 - (c4 + float<53,-1074,ne>(rhi * t5)), [-3.46945e-18, 3.46945e-18]) *).
Proof.
 intros h0.
 assert (h1 := l99 h0).
 apply t52. exact h1.
Qed.
Definition f133 := Float2 (-4978436895684117341050289522838836144647150072510572817959198578008322384561184251690700730913) (-379).
Definition f134 := Float2 (4978436895684117341050289522838836144647150072510572817959198578008322384561184251690700730913) (-379).
Definition i80 := makepairF f133 f134.
Notation p112 := (BND r107 i80). (* BND(c4 + float<53,-1074,ne>(rhi * t5) - (c4 + rhi * (c5 + rhi * c6)), [-4.04319e-21, 4.04319e-21]) *)
Notation r108 := ((r54 - r23)%R).
Notation p113 := (BND r108 i80). (* BND(float<53,-1074,ne>(rhi * t5) - rhi * (c5 + rhi * c6), [-4.04319e-21, 4.04319e-21]) *)
Notation r110 := ((r54 - r55)%R).
Notation r111 := ((r55 - r23)%R).
Notation r109 := ((r110 + r111)%R).
Notation p114 := (BND r109 i80). (* BND(float<53,-1074,ne>(rhi * t5) - rhi * t5 + (rhi * t5 - rhi * (c5 + rhi * c6)), [-4.04319e-21, 4.04319e-21]) *)
Notation p115 := (BND r110 i11). (* BND(float<53,-1074,ne>(rhi * t5) - rhi * t5, [-1.69407e-21, 1.69407e-21]) *)
Definition f135 := Float2 (1) (-15).
Definition i81 := makepairF f53 f135.
Notation p116 := (ABS r55 i81). (* ABS(rhi * t5, [0, 3.05176e-05]) *)
Definition f136 := Float2 (5) (-9).
Definition i82 := makepairF f78 f136.
Notation p117 := (ABS _t5 i82). (* ABS(t5, [0.0078125, 0.00976562]) *)
Notation p118 := (BND _t5 i82). (* BND(t5, [0.0078125, 0.00976562]) *)
Lemma t53 : p118 -> p117.
Proof.
 intros h0.
 refine (abs_of_bnd_p _t5 i82 i82 h0 _) ; finalize.
Qed.
Lemma l105 : s1 -> p117 (* ABS(t5, [0.0078125, 0.00976562]) *).
Proof.
 intros h0.
 assert (h1 := l57 h0).
 apply t53. refine (subset _t5 i44 i82 h1 _) ; finalize.
Qed.
Definition f137 := Float2 (3) (-10).
Definition i83 := makepairF f53 f137.
Notation p119 := (ABS _rhi i83). (* ABS(rhi, [0, 0.00292969]) *)
Lemma t54 : p119 -> p117 -> p116.
Proof.
 intros h0 h1.
 refine (mul_aa _rhi _t5 i83 i82 i81 h0 h1 _) ; finalize.
Qed.
Lemma l104 : s1 -> p116 (* ABS(rhi * t5, [0, 3.05176e-05]) *).
Proof.
 intros h0.
 assert (h1 := l38 h0).
 assert (h2 := l105 h0).
 apply t54. refine (abs_subset _rhi i31 i83 h1 _) ; finalize. exact h2.
Qed.
Lemma t55 : p116 -> p115.
Proof.
 intros h0.
 refine (float_absolute_wide_ne _ _ r55 i81 i11 h0 _) ; finalize.
Qed.
Lemma l103 : s1 -> p115 (* BND(float<53,-1074,ne>(rhi * t5) - rhi * t5, [-1.69407e-21, 1.69407e-21]) *).
Proof.
 intros h0.
 assert (h1 := l104 h0).
 apply t55. exact h1.
Qed.
Definition f138 := Float2 (-2892512055917603588711401137907632907730446437396654097307790757869435933603527464558901817889) (-379).
Definition f139 := Float2 (2892512055917603588711401137907632907730446437396654097307790757869435933603527464558901817889) (-379).
Definition i84 := makepairF f138 f139.
Notation p120 := (BND r111 i84). (* BND(rhi * t5 - rhi * (c5 + rhi * c6), [-2.34913e-21, 2.34913e-21]) *)
Notation r113 := ((_t5 - r24)%R).
Notation r112 := ((_rhi * r113)%R).
Notation p121 := (BND r112 i84). (* BND(rhi * (t5 - (c5 + rhi * c6)), [-2.34913e-21, 2.34913e-21]) *)
Definition f140 := Float2 (-4097) (-72).
Definition f141 := Float2 (4097) (-72).
Definition i85 := makepairF f140 f141.
Notation p122 := (BND r113 i85). (* BND(t5 - (c5 + rhi * c6), [-8.67573e-19, 8.67573e-19]) *)
Notation r115 := ((_t5 - r57)%R).
Notation r116 := ((r57 - r24)%R).
Notation r114 := ((r115 + r116)%R).
Notation p123 := (BND r114 i85). (* BND(t5 - (c5 + float<53,-1074,ne>(rhi * c6)) + (c5 + float<53,-1074,ne>(rhi * c6) - (c5 + rhi * c6)), [-8.67573e-19, 8.67573e-19]) *)
Definition f142 := Float2 (-1) (-60).
Definition f143 := Float2 (1) (-60).
Definition i86 := makepairF f142 f143.
Notation p124 := (BND r115 i86). (* BND(t5 - (c5 + float<53,-1074,ne>(rhi * c6)), [-8.67362e-19, 8.67362e-19]) *)
Definition f144 := Float2 (1) (-6).
Definition i87 := makepairF f78 f144.
Notation p125 := (ABS r57 i87). (* ABS(c5 + float<53,-1074,ne>(rhi * c6), [0.0078125, 0.015625]) *)
Notation p126 := (BND r57 i87). (* BND(c5 + float<53,-1074,ne>(rhi * c6), [0.0078125, 0.015625]) *)
Lemma t56 : p126 -> p125.
Proof.
 intros h0.
 refine (abs_of_bnd_p r57 i87 i87 h0 _) ; finalize.
Qed.
Lemma l111 : s1 -> p125 (* ABS(c5 + float<53,-1074,ne>(rhi * c6), [0.0078125, 0.015625]) *).
Proof.
 intros h0.
 assert (h1 := l58 h0).
 apply t56. refine (subset r57 i44 i87 h1 _) ; finalize.
Qed.
Lemma t57 : p125 -> p124.
Proof.
 intros h0.
 refine (float_absolute_wide_ne _ _ r57 i87 i86 h0 _) ; finalize.
Qed.
Lemma l110 : s1 -> p124 (* BND(t5 - (c5 + float<53,-1074,ne>(rhi * c6)), [-8.67362e-19, 8.67362e-19]) *).
Proof.
 intros h0.
 assert (h1 := l111 h0).
 apply t57. exact h1.
Qed.
Notation p127 := (BND r116 i27). (* BND(c5 + float<53,-1074,ne>(rhi * c6) - (c5 + rhi * c6), [-2.11758e-22, 2.11758e-22]) *)
Notation r117 := ((r58 - r26)%R).
Notation p128 := (BND r117 i27). (* BND(float<53,-1074,ne>(rhi * c6) - rhi * c6, [-2.11758e-22, 2.11758e-22]) *)
Notation p129 := (ABS r26 i28). (* ABS(rhi * c6, [0, 3.8147e-06]) *)
Definition i88 := makepairF f84 f54.
Notation p130 := (BND r26 i88). (* BND(rhi * c6, [-3.8147e-06, 3.8147e-06]) *)
Lemma t58 : p130 -> p129.
Proof.
 intros h0.
 refine (abs_of_bnd_o r26 i88 i28 h0 _) ; finalize.
Qed.
Lemma l114 : s1 -> p129 (* ABS(rhi * c6, [0, 3.8147e-06]) *).
Proof.
 intros h0.
 assert (h1 := l61 h0).
 apply t58. refine (subset r26 i47 i88 h1 _) ; finalize.
Qed.
Lemma t59 : p129 -> p128.
Proof.
 intros h0.
 refine (float_absolute_wide_ne _ _ r26 i28 i27 h0 _) ; finalize.
Qed.
Lemma l113 : s1 -> p128 (* BND(float<53,-1074,ne>(rhi * c6) - rhi * c6, [-2.11758e-22, 2.11758e-22]) *).
Proof.
 intros h0.
 assert (h1 := l114 h0).
 apply t59. exact h1.
Qed.
Lemma t60 : p128 -> p127.
Proof.
 intros h0.
 refine (add_fils _ _ _ i27 h0) ; finalize.
Qed.
Lemma l112 : s1 -> p127 (* BND(c5 + float<53,-1074,ne>(rhi * c6) - (c5 + rhi * c6), [-2.11758e-22, 2.11758e-22]) *).
Proof.
 intros h0.
 assert (h1 := l113 h0).
 apply t60. exact h1.
Qed.
Lemma t61 : p124 -> p127 -> p123.
Proof.
 intros h0 h1.
 refine (add r115 r116 i86 i27 i85 h0 h1 _) ; finalize.
Qed.
Lemma l109 : s1 -> p123 (* BND(t5 - (c5 + float<53,-1074,ne>(rhi * c6)) + (c5 + float<53,-1074,ne>(rhi * c6) - (c5 + rhi * c6)), [-8.67573e-19, 8.67573e-19]) *).
Proof.
 intros h0.
 assert (h1 := l110 h0).
 assert (h2 := l112 h0).
 apply t61. exact h1. exact h2.
Qed.
Lemma t62 : p123 -> p122.
Proof.
 intros h0.
 refine (sub_xals _ _ _ i85 h0) ; finalize.
Qed.
Lemma l108 : s1 -> p122 (* BND(t5 - (c5 + rhi * c6), [-8.67573e-19, 8.67573e-19]) *).
Proof.
 intros h0.
 assert (h1 := l109 h0).
 apply t62. exact h1.
Qed.
Definition f145 := Float2 (-11567224194326096460202000547590592521419486070370217410371209123000448702992480834594348885597) (-321).
Definition f146 := Float2 (11567224194326096460202000547590592521419486070370217410371209123000448702992480834594348885597) (-321).
Definition i89 := makepairF f145 f146.
Notation p131 := (BND _rhi i89). (* BND(rhi, [-0.0027077, 0.0027077]) *)
Lemma t63 : p131 -> p122 -> p121.
Proof.
 intros h0 h1.
 refine (mul_oo _rhi r113 i89 i85 i84 h0 h1 _) ; finalize.
Qed.
Lemma l107 : s1 -> p121 (* BND(rhi * (t5 - (c5 + rhi * c6)), [-2.34913e-21, 2.34913e-21]) *).
Proof.
 intros h0.
 assert (h1 := l39 h0).
 assert (h2 := l108 h0).
 apply t63. refine (subset _rhi i1 i89 h1 _) ; finalize. exact h2.
Qed.
Lemma t64 : p121 -> p120.
Proof.
 intros h0.
 refine (mul_fils _ _ _ i84 h0) ; finalize.
Qed.
Lemma l106 : s1 -> p120 (* BND(rhi * t5 - rhi * (c5 + rhi * c6), [-2.34913e-21, 2.34913e-21]) *).
Proof.
 intros h0.
 assert (h1 := l107 h0).
 apply t64. exact h1.
Qed.
Lemma t65 : p115 -> p120 -> p114.
Proof.
 intros h0 h1.
 refine (add r110 r111 i11 i84 i80 h0 h1 _) ; finalize.
Qed.
Lemma l102 : s1 -> p114 (* BND(float<53,-1074,ne>(rhi * t5) - rhi * t5 + (rhi * t5 - rhi * (c5 + rhi * c6)), [-4.04319e-21, 4.04319e-21]) *).
Proof.
 intros h0.
 assert (h1 := l103 h0).
 assert (h2 := l106 h0).
 apply t65. exact h1. exact h2.
Qed.
Lemma t66 : p114 -> p113.
Proof.
 intros h0.
 refine (sub_xals _ _ _ i80 h0) ; finalize.
Qed.
Lemma l101 : s1 -> p113 (* BND(float<53,-1074,ne>(rhi * t5) - rhi * (c5 + rhi * c6), [-4.04319e-21, 4.04319e-21]) *).
Proof.
 intros h0.
 assert (h1 := l102 h0).
 apply t66. exact h1.
Qed.
Lemma t67 : p113 -> p112.
Proof.
 intros h0.
 refine (add_fils _ _ _ i80 h0) ; finalize.
Qed.
Lemma l100 : s1 -> p112 (* BND(c4 + float<53,-1074,ne>(rhi * t5) - (c4 + rhi * (c5 + rhi * c6)), [-4.04319e-21, 4.04319e-21]) *).
Proof.
 intros h0.
 assert (h1 := l101 h0).
 apply t67. exact h1.
Qed.
Lemma t68 : p109 -> p112 -> p108.
Proof.
 intros h0 h1.
 refine (add r106 r107 i78 i80 i77 h0 h1 _) ; finalize.
Qed.
Lemma l97 : s1 -> p108 (* BND(t4 - (c4 + float<53,-1074,ne>(rhi * t5)) + (c4 + float<53,-1074,ne>(rhi * t5) - (c4 + rhi * (c5 + rhi * c6))), [-3.47349e-18, 3.47349e-18]) *).
Proof.
 intros h0.
 assert (h1 := l98 h0).
 assert (h2 := l100 h0).
 apply t68. exact h1. exact h2.
Qed.
Lemma t69 : p108 -> p107.
Proof.
 intros h0.
 refine (sub_xals _ _ _ i77 h0) ; finalize.
Qed.
Lemma l96 : s1 -> p107 (* BND(t4 - (c4 + rhi * (c5 + rhi * c6)), [-3.47349e-18, 3.47349e-18]) *).
Proof.
 intros h0.
 assert (h1 := l97 h0).
 apply t69. exact h1.
Qed.
Definition f147 := Float2 (-370151174218435086726464017522898960685423554251846957131878691936014358495759386707019164339083) (-326).
Definition f148 := Float2 (370151174218435086726464017522898960685423554251846957131878691936014358495759386707019164339083) (-326).
Definition i90 := makepairF f147 f148.
Notation p132 := (BND _rhi i90). (* BND(rhi, [-0.0027077, 0.0027077]) *)
Lemma t70 : p132 -> p107 -> p106.
Proof.
 intros h0 h1.
 refine (mul_oo _rhi r104 i90 i77 i76 h0 h1 _) ; finalize.
Qed.
Lemma l95 : s1 -> p106 (* BND(rhi * (t4 - (c4 + rhi * (c5 + rhi * c6))), [-9.40517e-21, 9.40517e-21]) *).
Proof.
 intros h0.
 assert (h1 := l39 h0).
 assert (h2 := l96 h0).
 apply t70. refine (subset _rhi i1 i90 h1 _) ; finalize. exact h2.
Qed.
Lemma t71 : p106 -> p105.
Proof.
 intros h0.
 refine (mul_fils _ _ _ i76 h0) ; finalize.
Qed.
Lemma l94 : s1 -> p105 (* BND(rhi * t4 - rhi * (c4 + rhi * (c5 + rhi * c6)), [-9.40517e-21, 9.40517e-21]) *).
Proof.
 intros h0.
 assert (h1 := l95 h0).
 apply t71. exact h1.
Qed.
Lemma t72 : p101 -> p105 -> p100.
Proof.
 intros h0 h1.
 refine (add r101 r102 i73 i76 i72 h0 h1 _) ; finalize.
Qed.
Lemma l90 : s1 -> p100 (* BND(float<53,-1074,ne>(rhi * t4) - rhi * t4 + (rhi * t4 - rhi * (c4 + rhi * (c5 + rhi * c6))), [-1.61814e-20, 1.61814e-20]) *).
Proof.
 intros h0.
 assert (h1 := l91 h0).
 assert (h2 := l94 h0).
 apply t72. exact h1. exact h2.
Qed.
Lemma t73 : p100 -> p99.
Proof.
 intros h0.
 refine (sub_xals _ _ _ i72 h0) ; finalize.
Qed.
Lemma l89 : s1 -> p99 (* BND(float<53,-1074,ne>(rhi * t4) - rhi * (c4 + rhi * (c5 + rhi * c6)), [-1.61814e-20, 1.61814e-20]) *).
Proof.
 intros h0.
 assert (h1 := l90 h0).
 apply t73. exact h1.
Qed.
Lemma t74 : p99 -> p98.
Proof.
 intros h0.
 refine (add_fils _ _ _ i72 h0) ; finalize.
Qed.
Lemma l88 : s1 -> p98 (* BND(c3 + float<53,-1074,ne>(rhi * t4) - (c3 + rhi * (c4 + rhi * (c5 + rhi * c6))), [-1.61814e-20, 1.61814e-20]) *).
Proof.
 intros h0.
 assert (h1 := l89 h0).
 apply t74. exact h1.
Qed.
Lemma t75 : p92 -> p98 -> p91.
Proof.
 intros h0 h1.
 refine (add r97 r98 i67 i72 i66 h0 h1 _) ; finalize.
Qed.
Lemma l83 : s1 -> p91 (* BND(t3 - (c3 + float<53,-1074,ne>(rhi * t4)) + (c3 + float<53,-1074,ne>(rhi * t4) - (c3 + rhi * (c4 + rhi * (c5 + rhi * c6)))), [-1.3894e-17, 1.3894e-17]) *).
Proof.
 intros h0.
 assert (h1 := l84 h0).
 assert (h2 := l88 h0).
 apply t75. exact h1. exact h2.
Qed.
Lemma t76 : p91 -> p90.
Proof.
 intros h0.
 refine (sub_xals _ _ _ i66 h0) ; finalize.
Qed.
Lemma l82 : s1 -> p90 (* BND(t3 - (c3 + rhi * (c4 + rhi * (c5 + rhi * c6))), [-1.3894e-17, 1.3894e-17]) *).
Proof.
 intros h0.
 assert (h1 := l83 h0).
 apply t76. exact h1.
Qed.
Definition f149 := Float2 (-189517401199838764403949576971724267870936859776945642051521890271239351549828805993993812141610331) (-335).
Definition f150 := Float2 (189517401199838764403949576971724267870936859776945642051521890271239351549828805993993812141610331) (-335).
Definition i91 := makepairF f149 f150.
Notation p133 := (BND _rhi i91). (* BND(rhi, [-0.0027077, 0.0027077]) *)
Lemma t77 : p133 -> p90 -> p89.
Proof.
 intros h0 h1.
 refine (mul_oo _rhi r95 i91 i66 i65 h0 h1 _) ; finalize.
Qed.
Lemma l81 : s1 -> p89 (* BND(rhi * (t3 - (c3 + rhi * (c4 + rhi * (c5 + rhi * c6)))), [-3.76207e-20, 3.76207e-20]) *).
Proof.
 intros h0.
 assert (h1 := l39 h0).
 assert (h2 := l82 h0).
 apply t77. refine (subset _rhi i1 i91 h1 _) ; finalize. exact h2.
Qed.
Lemma t78 : p89 -> p88.
Proof.
 intros h0.
 refine (mul_fils _ _ _ i65 h0) ; finalize.
Qed.
Lemma l80 : s1 -> p88 (* BND(rhi * t3 - rhi * (c3 + rhi * (c4 + rhi * (c5 + rhi * c6))), [-3.76207e-20, 3.76207e-20]) *).
Proof.
 intros h0.
 assert (h1 := l81 h0).
 apply t78. exact h1.
Qed.
Lemma t79 : p83 -> p88 -> p82.
Proof.
 intros h0 h1.
 refine (add r92 r93 i61 i65 i60 h0 h1 _) ; finalize.
Qed.
Lemma l76 : s1 -> p82 (* BND(float<53,-1074,ne>(rhi * t3) - rhi * t3 + (rhi * t3 - rhi * (c3 + rhi * (c4 + rhi * (c5 + rhi * c6)))), [-6.47258e-20, 6.47258e-20]) *).
Proof.
 intros h0.
 assert (h1 := l77 h0).
 assert (h2 := l80 h0).
 apply t79. exact h1. exact h2.
Qed.
Lemma t80 : p82 -> p81.
Proof.
 intros h0.
 refine (sub_xals _ _ _ i60 h0) ; finalize.
Qed.
Lemma l75 : s1 -> p81 (* BND(float<53,-1074,ne>(rhi * t3) - rhi * (c3 + rhi * (c4 + rhi * (c5 + rhi * c6))), [-6.47258e-20, 6.47258e-20]) *).
Proof.
 intros h0.
 assert (h1 := l76 h0).
 apply t80. exact h1.
Qed.
Lemma t81 : p81 -> p80.
Proof.
 intros h0.
 refine (add_fils _ _ _ i60 h0) ; finalize.
Qed.
Lemma l74 : s1 -> p80 (* BND(5e-1 + float<53,-1074,ne>(rhi * t3) - (5e-1 + rhi * (c3 + rhi * (c4 + rhi * (c5 + rhi * c6)))), [-6.47258e-20, 6.47258e-20]) *).
Proof.
 intros h0.
 assert (h1 := l75 h0).
 apply t81. exact h1.
Qed.
Lemma t82 : p74 -> p80 -> p73.
Proof.
 intros h0 h1.
 refine (add r88 r89 i58 i60 i57 h0 h1 _) ; finalize.
Qed.
Lemma l67 : s1 -> p73 (* BND(h - (5e-1 + float<53,-1074,ne>(rhi * t3)) + (5e-1 + float<53,-1074,ne>(rhi * t3) - (5e-1 + rhi * (c3 + rhi * (c4 + rhi * (c5 + rhi * c6))))), [-5.5626e-17, 5.5626e-17]) *).
Proof.
 intros h0.
 assert (h1 := l68 h0).
 assert (h2 := l74 h0).
 apply t82. exact h1. exact h2.
Qed.
Lemma t83 : p73 -> p72.
Proof.
 intros h0.
 refine (sub_xals _ _ _ i57 h0) ; finalize.
Qed.
Lemma l66 : s1 -> p72 (* BND(h - (5e-1 + rhi * (c3 + rhi * (c4 + rhi * (c5 + rhi * c6)))), [-5.5626e-17, 5.5626e-17]) *).
Proof.
 intros h0.
 assert (h1 := l67 h0).
 apply t83. exact h1.
Qed.
Lemma t84 : p33 -> p72 -> p71.
Proof.
 intros h0 h1.
 refine (mul_po _r2 r84 i30 i57 i56 h0 h1 _) ; finalize.
Qed.
Lemma l65 : s1 -> p71 (* BND(r2 * (h - (5e-1 + rhi * (c3 + rhi * (c4 + rhi * (c5 + rhi * c6))))), [-4.0783e-22, 4.0783e-22]) *).
Proof.
 intros h0.
 assert (h1 := l36 h0).
 assert (h2 := l66 h0).
 apply t84. exact h1. exact h2.
Qed.
Definition f151 := Float2 (-8756904805789200669255244225686929468488421454628138250808999411682401845964558242511577843889263833) (-404).
Definition f152 := Float2 (8756904805789200669255244225686929468488421454628138250808999411682401845964558242511577843889263833) (-404).
Definition i92 := makepairF f151 f152.
Notation p134 := (BND r85 i92). (* BND((r2 - rhi * rhi) * (5e-1 + rhi * (c3 + rhi * (c4 + rhi * (c5 + rhi * c6)))), [-2.11949e-22, 2.11949e-22]) *)
Definition f153 := Float2 (-1) (-71).
Definition f154 := Float2 (1) (-71).
Definition i93 := makepairF f153 f154.
Notation p135 := (BND r86 i93). (* BND(r2 - rhi * rhi, [-4.23516e-22, 4.23516e-22]) *)
Definition f155 := Float2 (1) (-17).
Definition i94 := makepairF f53 f155.
Notation p136 := (ABS r14 i94). (* ABS(rhi * rhi, [0, 7.62939e-06]) *)
Definition f156 := Float2 (45) (-14).
Definition i95 := makepairF f53 f156.
Notation p137 := (ABS _rhi i95). (* ABS(rhi, [0, 0.00274658]) *)
Lemma t85 : p137 -> p137 -> p136.
Proof.
 intros h0 h1.
 refine (mul_aa _rhi _rhi i95 i95 i94 h0 h1 _) ; finalize.
Qed.
Lemma l117 : s1 -> p136 (* ABS(rhi * rhi, [0, 7.62939e-06]) *).
Proof.
 intros h0.
 assert (h1 := l38 h0).
 apply t85. refine (abs_subset _rhi i31 i95 h1 _) ; finalize. refine (abs_subset _rhi i31 i95 h1 _) ; finalize.
Qed.
Lemma t86 : p136 -> p135.
Proof.
 intros h0.
 refine (float_absolute_wide_ne _ _ r14 i94 i93 h0 _) ; finalize.
Qed.
Lemma l116 : s1 -> p135 (* BND(r2 - rhi * rhi, [-4.23516e-22, 4.23516e-22]) *).
Proof.
 intros h0.
 assert (h1 := l117 h0).
 apply t86. exact h1.
Qed.
Definition f157 := Float2 (8756904805789200669255244225686929468488421454628138250808999411682401845964558242511577843889263833) (-333).
Definition i96 := makepairF f59 f157.
Notation p138 := (BND r15 i96). (* BND(5e-1 + rhi * (c3 + rhi * (c4 + rhi * (c5 + rhi * c6))), [0.25, 0.500452]) *)
Definition f158 := Float2 (7901906657152971765235317216444007075743731055288505105916986042589849167054549617525135797048537) (-333).
Definition i97 := makepairF f64 f158.
Notation p139 := (BND r17 i97). (* BND(rhi * (c3 + rhi * (c4 + rhi * (c5 + rhi * c6))), [-0.25, 0.000451589]) *)
Definition f159 := Float2 (1459154754432354353369154119075969840776993584091388467318570381244201567207325334698292978736295933) (-332).
Definition i98 := makepairF f66 f159.
Notation p140 := (BND r18 i98). (* BND(c3 + rhi * (c4 + rhi * (c5 + rhi * c6)), [0.125, 0.16678]) *)
Definition f160 := Float2 (987604577060989620160868981304943935248943628944022403419929745757112447181612188319255863881725) (-332).
Definition i99 := makepairF f70 f160.
Notation p141 := (BND r20 i99). (* BND(rhi * (c4 + rhi * (c5 + rhi * c6)), [-0.03125, 0.000112882]) *)
Definition f161 := Float2 (2849525707533693321825456629776147466164040366778141975373269246492388740852511438211096663801741) (-325).
Definition i100 := makepairF f72 f161.
Notation p142 := (BND r21 i100). (* BND(c4 + rhi * (c5 + rhi * c6), [0.03125, 0.0416892]) *)
Definition f162 := Float2 (1542992972551179386520933969591707022541873348413520187078069113225051090693198811390992957325) (-325).
Definition i101 := makepairF f76 f162.
Notation p143 := (BND r23 i101). (* BND(rhi * (c5 + rhi * c6), [-0.0078125, 2.25744e-05]) *)
Definition f163 := Float2 (2225991172961570513202126645757508422943528739240061022555566522707595310787867140745306437031) (-317).
Definition i102 := makepairF f78 f163.
Notation p144 := (BND r24 i102). (* BND(c5 + rhi * c6, [0.0078125, 0.0083371]) *)
Definition i103 := makepairF f82 f85.
Notation p145 := (BND r26 i103). (* BND(rhi * c6, [-0.000488281, 3.7607e-06]) *)
Lemma t87 : p56 -> p145 -> p144.
Proof.
 intros h0 h1.
 refine (add _c5 r26 i45 i103 i102 h0 h1 _) ; finalize.
Qed.
Lemma l124 : s1 -> p144 (* BND(c5 + rhi * c6, [0.0078125, 0.0083371]) *).
Proof.
 intros h0.
 assert (h1 := l59 h0).
 assert (h2 := l61 h0).
 apply t87. exact h1. refine (subset r26 i47 i103 h2 _) ; finalize.
Qed.
Definition f164 := Float2 (361475756072690514381312517112206016294358939699069294074100285093764021968515026081073402675) (-316).
Definition i104 := makepairF f91 f164.
Notation p146 := (BND _rhi i104). (* BND(rhi, [-0.5, 0.0027077]) *)
Lemma t88 : p146 -> p144 -> p143.
Proof.
 intros h0 h1.
 refine (mul_op _rhi r24 i104 i102 i101 h0 h1 _) ; finalize.
Qed.
Lemma l123 : s1 -> p143 (* BND(rhi * (c5 + rhi * c6), [-0.0078125, 2.25744e-05]) *).
Proof.
 intros h0.
 assert (h1 := l39 h0).
 assert (h2 := l124 h0).
 apply t88. refine (subset _rhi i1 i104 h1 _) ; finalize. exact h2.
Qed.
Lemma t89 : p51 -> p143 -> p142.
Proof.
 intros h0 h1.
 refine (add _c4 r23 i42 i101 i100 h0 h1 _) ; finalize.
Qed.
Lemma l122 : s1 -> p142 (* BND(c4 + rhi * (c5 + rhi * c6), [0.03125, 0.0416892]) *).
Proof.
 intros h0.
 assert (h1 := l54 h0).
 assert (h2 := l123 h0).
 apply t89. exact h1. exact h2.
Qed.
Definition f165 := Float2 (1480604696873740346905856070091595842741694217007387828527514767744057433983037546828076657356331) (-328).
Definition i105 := makepairF f91 f165.
Notation p147 := (BND _rhi i105). (* BND(rhi, [-0.5, 0.0027077]) *)
Lemma t90 : p147 -> p142 -> p141.
Proof.
 intros h0 h1.
 refine (mul_op _rhi r21 i105 i100 i99 h0 h1 _) ; finalize.
Qed.
Lemma l121 : s1 -> p141 (* BND(rhi * (c4 + rhi * (c5 + rhi * c6)), [-0.03125, 0.000112882]) *).
Proof.
 intros h0.
 assert (h1 := l39 h0).
 assert (h2 := l122 h0).
 apply t90. refine (subset _rhi i1 i105 h1 _) ; finalize. exact h2.
Qed.
Lemma t91 : p46 -> p141 -> p140.
Proof.
 intros h0 h1.
 refine (add _c3 r20 i39 i99 i98 h0 h1 _) ; finalize.
Qed.
Lemma l120 : s1 -> p140 (* BND(c3 + rhi * (c4 + rhi * (c5 + rhi * c6)), [0.125, 0.16678]) *).
Proof.
 intros h0.
 assert (h1 := l49 h0).
 assert (h2 := l121 h0).
 apply t91. exact h1. exact h2.
Qed.
Definition f166 := Float2 (1516139209598710115231596615773794142967494878215565136412175122169914812398630447951950497132882647) (-338).
Definition i106 := makepairF f95 f166.
Notation p148 := (BND _rhi i106). (* BND(rhi, [-1, 0.0027077]) *)
Lemma t92 : p148 -> p140 -> p139.
Proof.
 intros h0 h1.
 refine (mul_op _rhi r18 i106 i98 i97 h0 h1 _) ; finalize.
Qed.
Lemma l119 : s1 -> p139 (* BND(rhi * (c3 + rhi * (c4 + rhi * (c5 + rhi * c6))), [-0.25, 0.000451589]) *).
Proof.
 intros h0.
 assert (h1 := l39 h0).
 assert (h2 := l120 h0).
 apply t92. refine (subset _rhi i1 i106 h1 _) ; finalize. exact h2.
Qed.
Lemma t93 : p41 -> p139 -> p138.
Proof.
 intros h0 h1.
 refine (add r16 r17 i36 i97 i96 h0 h1 _) ; finalize.
Qed.
Lemma l118 : s1 -> p138 (* BND(5e-1 + rhi * (c3 + rhi * (c4 + rhi * (c5 + rhi * c6))), [0.25, 0.500452]) *).
Proof.
 intros h0.
 assert (h1 := l44 h0).
 assert (h2 := l119 h0).
 apply t93. exact h1. exact h2.
Qed.
Lemma t94 : p135 -> p138 -> p134.
Proof.
 intros h0 h1.
 refine (mul_op r86 r15 i93 i96 i92 h0 h1 _) ; finalize.
Qed.
Lemma l115 : s1 -> p134 (* BND((r2 - rhi * rhi) * (5e-1 + rhi * (c3 + rhi * (c4 + rhi * (c5 + rhi * c6)))), [-2.11949e-22, 2.11949e-22]) *).
Proof.
 intros h0.
 assert (h1 := l116 h0).
 assert (h2 := l118 h0).
 apply t94. exact h1. exact h2.
Qed.
Lemma t95 : p71 -> p134 -> p70.
Proof.
 intros h0 h1.
 refine (add r83 r85 i56 i92 i55 h0 h1 _) ; finalize.
Qed.
Lemma l64 : s1 -> p70 (* BND(r2 * (h - (5e-1 + rhi * (c3 + rhi * (c4 + rhi * (c5 + rhi * c6))))) + (r2 - rhi * rhi) * (5e-1 + rhi * (c3 + rhi * (c4 + rhi * (c5 + rhi * c6)))), [-6.19779e-22, 6.19779e-22]) *).
Proof.
 intros h0.
 assert (h1 := l65 h0).
 assert (h2 := l115 h0).
 apply t95. exact h1. exact h2.
Qed.
Lemma t96 : p70 -> p69.
Proof.
 intros h0.
 refine (mul_mars _ _ _ _ i55 h0) ; finalize.
Qed.
Lemma l63 : s1 -> p69 (* BND(r2 * h - Q, [-6.19779e-22, 6.19779e-22]) *).
Proof.
 intros h0.
 assert (h1 := l64 h0).
 apply t96. exact h1.
Qed.
Lemma t97 : p30 -> p69 -> p29.
Proof.
 intros h0 h1.
 refine (add r80 r81 i27 i55 i26 h0 h1 _) ; finalize.
Qed.
Lemma l32 : s1 -> p29 (* BND(q - r2 * h + (r2 * h - Q), [-8.31538e-22, 8.31538e-22]) *).
Proof.
 intros h0.
 assert (h1 := l33 h0).
 assert (h2 := l63 h0).
 apply t97. exact h1. exact h2.
Qed.
Lemma t98 : p29 -> p28.
Proof.
 intros h0.
 refine (sub_xals _ _ _ i26 h0) ; finalize.
Qed.
Lemma l31 : s1 -> p28 (* BND(q - Q, [-8.31538e-22, 8.31538e-22]) *).
Proof.
 intros h0.
 assert (h1 := l32 h0).
 apply t98. exact h1.
Qed.
Lemma t99 : p3 -> p28 -> p27.
Proof.
 intros h0 h1.
 refine (add _dr r77 i3 i26 i25 h0 h1 _) ; finalize.
Qed.
Lemma l25 : s1 -> p27 (* BND(dr + (q - Q), [-8.31538e-22, 8.31538e-22]) *).
Proof.
 intros h0.
 assert (h1 := l26 h0).
 assert (h2 := l31 h0).
 apply t99. exact h1. exact h2.
Qed.
Lemma l125 : s1 -> p5 (* BND(m, [-6.61744e-22, 6.61744e-22]) *).
Proof.
 intros h0.
 assert (h1 := l29 h0).
 exact (proj2 h1).
Qed.
Lemma t100 : p27 -> p5 -> p26.
Proof.
 intros h0 h1.
 refine (sub r76 _m i25 i5 i24 h0 h1 _) ; finalize.
Qed.
Lemma l24 : s1 -> p26 (* BND(dr + (q - Q) - m, [-1.49328e-21, 1.49328e-21]) *).
Proof.
 intros h0.
 assert (h1 := l25 h0).
 assert (h2 := l125 h0).
 apply t100. exact h1. exact h2.
Qed.
Lemma l126 : s1 -> p4 (* BND(a, [-5.56419e-24, 5.56419e-24]) *).
Proof.
 intros h0.
 assert (h1 := l28 h0).
 exact (proj2 h1).
Qed.
Lemma t101 : p26 -> p4 -> p25.
Proof.
 intros h0 h1.
 refine (sub r75 _a i24 i4 i23 h0 h1 _) ; finalize.
Qed.
Lemma l23 : s1 -> p25 (* BND(dr + (q - Q) - m - a, [-1.49885e-21, 1.49885e-21]) *).
Proof.
 intros h0.
 assert (h1 := l24 h0).
 assert (h2 := l126 h0).
 apply t101. exact h1. exact h2.
Qed.
Definition f167 := Float2 (-86299319750273950965943764325074994252337631929119699878889243888847173446900412227767) (-399).
Definition f168 := Float2 (86299319750273950965943764325074994252337631929119699878889243888847173446900412227767) (-399).
Definition i107 := makepairF f167 f168.
Notation p149 := (BND r78 i107). (* BND((rhi + rlo + q) * d1, [-6.68404e-35, 6.68404e-35]) *)
Definition f169 := Float2 (-355) (-17).
Definition f170 := Float2 (86299319750273950965943764325074994252337631929119699878889243888847173446900412227767) (-294).
Definition i108 := makepairF f169 f170.
Notation p150 := (BND r40 i108). (* BND(rhi + rlo + q, [-0.00270844, 0.00271137]) *)
Definition f171 := Float2 (-5922418787494961861907821796413519825913531463615221881103916261439980041550414283724485634603179) (-330).
Definition f172 := Float2 (86182536142513881523450571642221181914116189925920070979975808025337465246417767538871) (-294).
Definition i109 := makepairF f171 f172.
Notation p151 := (BND r8 i109). (* BND(rhi + rlo, [-0.0027077, 0.0027077]) *)
Lemma l130 : s1 -> p2 (* BND(rlo, [-2.1684e-19, 2.1684e-19]) *).
Proof.
 intros h0.
 assert (h1 := l40 h0).
 exact (proj2 h1).
Qed.
Definition f173 := Float2 (-5922418787494961387623424280366383370966776868029551314110059070976229735932150187312306629425323) (-330).
Definition f174 := Float2 (86182536142513874621704224851657394479360327648894618528866835854950910083893543739575) (-294).
Definition i110 := makepairF f173 f174.
Notation p152 := (BND _rhi i110). (* BND(rhi, [-0.0027077, 0.0027077]) *)
Lemma t102 : p152 -> p2 -> p151.
Proof.
 intros h0 h1.
 refine (add _rhi _rlo i110 i2 i109 h0 h1 _) ; finalize.
Qed.
Lemma l129 : s1 -> p151 (* BND(rhi + rlo, [-0.0027077, 0.0027077]) *).
Proof.
 intros h0.
 assert (h1 := l39 h0).
 assert (h2 := l130 h0).
 apply t102. refine (subset _rhi i1 i110 h1 _) ; finalize. exact h2.
Qed.
Definition f175 := Float2 (8663489524062337) (-71).
Definition i111 := makepairF f53 f175.
Notation p153 := (BND _q i111). (* BND(q, [0, 3.66913e-06]) *)
Definition f176 := Float2 (69307916192498699) (-74).
Definition i112 := makepairF f53 f176.
Notation p154 := (BND r42 i112). (* BND(r2 * h, [0, 3.66913e-06]) *)
Lemma t103 : p33 -> p39 -> p154.
Proof.
 intros h0 h1.
 refine (mul_pp _r2 _h i30 i34 i112 h0 h1 _) ; finalize.
Qed.
Lemma l132 : s1 -> p154 (* BND(r2 * h, [0, 3.66913e-06]) *).
Proof.
 intros h0.
 assert (h1 := l36 h0).
 assert (h2 := l42 h0).
 apply t103. exact h1. exact h2.
Qed.
Lemma t104 : p154 -> p153.
Proof.
 intros h0.
 refine (float_round_ne _ _ r42 i112 i111 h0 _) ; finalize.
Qed.
Lemma l131 : s1 -> p153 (* BND(q, [0, 3.66913e-06]) *).
Proof.
 intros h0.
 assert (h1 := l132 h0).
 apply t104. exact h1.
Qed.
Definition i113 := makepairF f169 f172.
Notation p155 := (BND r8 i113). (* BND(rhi + rlo, [-0.00270844, 0.0027077]) *)
Lemma t105 : p155 -> p153 -> p150.
Proof.
 intros h0 h1.
 refine (add r8 _q i113 i111 i108 h0 h1 _) ; finalize.
Qed.
Lemma l128 : s1 -> p150 (* BND(rhi + rlo + q, [-0.00270844, 0.00271137]) *).
Proof.
 intros h0.
 assert (h1 := l129 h0).
 assert (h2 := l131 h0).
 apply t105. refine (subset r8 i109 i113 h1 _) ; finalize. exact h2.
Qed.
Lemma l133 : s1 -> p6 (* BND(d1, [-2.46519e-32, 2.46519e-32]) *).
Proof.
 intros h0.
 assert (h1 := l30 h0).
 exact (proj2 h1).
Qed.
Lemma t106 : p150 -> p6 -> p149.
Proof.
 intros h0 h1.
 refine (mul_oo r40 _d1 i108 i6 i107 h0 h1 _) ; finalize.
Qed.
Lemma l127 : s1 -> p149 (* BND((rhi + rlo + q) * d1, [-6.68404e-35, 6.68404e-35]) *).
Proof.
 intros h0.
 assert (h1 := l128 h0).
 assert (h2 := l133 h0).
 apply t106. exact h1. exact h2.
Qed.
Lemma t107 : p25 -> p149 -> p24.
Proof.
 intros h0 h1.
 refine (add r74 r78 i23 i107 i22 h0 h1 _) ; finalize.
Qed.
Lemma l22 : s1 -> p24 (* BND(dr + (q - Q) - m - a + (rhi + rlo + q) * d1, [-1.49885e-21, 1.49885e-21]) *).
Proof.
 intros h0.
 assert (h1 := l23 h0).
 assert (h2 := l127 h0).
 apply t107. exact h1. exact h2.
Qed.
Definition i114 := makepairF f53 f53.
Notation p156 := (REL r72 r73 i114). (* REL(1 + P - expR, dr + (q - Q) - m - a + (rhi + rlo + q) * d1, [0, 0]) *)
Notation p157 := (r72 = r73). (* EQL(1 + P - expR, dr + (q - Q) - m - a + (rhi + rlo + q) * d1) *)
Lemma t108 : p157.
Proof.
 refine (b2) ; finalize.
Qed.
Lemma l135 : s1 -> p157 (* EQL(1 + P - expR, dr + (q - Q) - m - a + (rhi + rlo + q) * d1) *).
Proof.
 intros h0.
 apply t108.
Qed.
Notation p158 := (REL r73 r73 i114). (* REL(dr + (q - Q) - m - a + (rhi + rlo + q) * d1, dr + (q - Q) - m - a + (rhi + rlo + q) * d1, [0, 0]) *)
Lemma t109 : p158.
Proof.
 refine (rel_refl r73 i114 _) ; finalize.
Qed.
Lemma l136 : s1 -> p158 (* REL(dr + (q - Q) - m - a + (rhi + rlo + q) * d1, dr + (q - Q) - m - a + (rhi + rlo + q) * d1, [0, 0]) *).
Proof.
 intros h0.
 apply t109.
Qed.
Lemma t110 : p157 -> p158 -> p156.
Proof.
 intros h0 h1.
 refine (rel_rewrite_1 r72 r73 r73 i114 h0 h1) ; finalize.
Qed.
Lemma l134 : s1 -> p156 (* REL(1 + P - expR, dr + (q - Q) - m - a + (rhi + rlo + q) * d1, [0, 0]) *).
Proof.
 intros h0.
 assert (h1 := l135 h0).
 assert (h2 := l136 h0).
 apply t110. exact h1. exact h2.
Qed.
Lemma t111 : p24 -> p156 -> p23.
Proof.
 intros h0 h1.
 refine (bnd_of_bnd_rel_o r72 r73 i22 i114 i22 h0 h1 _) ; finalize.
Qed.
Lemma l21 : s1 -> p23 (* BND(1 + P - expR, [-1.49885e-21, 1.49885e-21]) *).
Proof.
 intros h0.
 assert (h1 := l22 h0).
 assert (h2 := l134 h0).
 apply t111. exact h1. exact h2.
Qed.
Definition f177 := Float2 (2181328305995516962509134833924141980497187385626410612873867857381468785550366219450312155219576661) (-330).
Definition i115 := makepairF f177 f20.
Notation p159 := (BND _expR i115). (* BND(expR, [0.997292, 2]) *)
Definition f178 := Float2 (2181328305995516962509147004205741182459877925002615219860445447999327874317141488041467268645996373) (-330).
Definition f179 := Float2 (3) (-1).
Definition i116 := makepairF f178 f179.
Notation p160 := (BND r3 i116). (* BND(1 + R + Q + m, [0.997292, 1.5]) *)
Definition f180 := Float2 (2181328305995516962510594405321207634902672562315223818708611322807648381367634707841566182766495573) (-330).
Definition f181 := Float2 (5) (-2).
Definition i117 := makepairF f180 f181.
Notation p161 := (BND r4 i117). (* BND(1 + R + Q, [0.997292, 1.25]) *)
Definition f182 := Float2 (9) (-3).
Definition i118 := makepairF f180 f182.
Notation p162 := (BND r5 i118). (* BND(1 + R, [0.997292, 1.125]) *)
Definition f183 := Float2 (-5922418787494961861907821796413730450496868577988617717159283602304617831741215381946994256558251) (-330).
Definition i119 := makepairF f183 f66.
Notation p163 := (BND _R i119). (* BND(R, [-0.0027077, 0.125]) *)
Definition i120 := makepairF f171 f132.
Notation p164 := (BND r8 i120). (* BND(rhi + rlo, [-0.0027077, 0.0625]) *)
Definition f184 := Float2 (-1) (-4).
Definition i121 := makepairF f184 f6.
Notation p165 := (BND _dr i121). (* BND(dr, [-0.0625, 9.62965e-35]) *)
Lemma t112 : p164 -> p165 -> p163.
Proof.
 intros h0 h1.
 refine (sub r8 _dr i120 i121 i119 h0 h1 _) ; finalize.
Qed.
Lemma l141 : s1 -> p163 (* BND(R, [-0.0027077, 0.125]) *).
Proof.
 intros h0.
 assert (h1 := l129 h0).
 assert (h2 := l26 h0).
 apply t112. refine (subset r8 i109 i120 h1 _) ; finalize. refine (subset _dr i3 i121 h2 _) ; finalize.
Qed.
Lemma t113 : p18 -> p163 -> p162.
Proof.
 intros h0 h1.
 refine (add r6 _R i17 i119 i118 h0 h1 _) ; finalize.
Qed.
Lemma l140 : s1 -> p162 (* BND(1 + R, [0.997292, 1.125]) *).
Proof.
 intros h0.
 assert (h1 := l9 h0).
 assert (h2 := l141 h0).
 apply t113. exact h1. exact h2.
Qed.
Definition i122 := makepairF f53 f66.
Notation p166 := (BND _Q i122). (* BND(Q, [0, 0.125]) *)
Notation p167 := (BND r14 i122). (* BND(rhi * rhi, [0, 0.125]) *)
Definition i123 := makepairF f59 f19.
Notation p168 := (BND r15 i123). (* BND(5e-1 + rhi * (c3 + rhi * (c4 + rhi * (c5 + rhi * c6))), [0.25, 1]) *)
Lemma t114 : p167 -> p168 -> p166.
Proof.
 intros h0 h1.
 refine (mul_pp r14 r15 i122 i123 i122 h0 h1 _) ; finalize.
Qed.
Lemma l142 : s1 -> p166 (* BND(Q, [0, 0.125]) *).
Proof.
 intros h0.
 assert (h1 := l37 h0).
 assert (h2 := l118 h0).
 apply t114. refine (subset r14 i30 i122 h1 _) ; finalize. refine (subset r15 i96 i123 h2 _) ; finalize.
Qed.
Lemma t115 : p162 -> p166 -> p161.
Proof.
 intros h0 h1.
 refine (add r5 _Q i118 i122 i117 h0 h1 _) ; finalize.
Qed.
Lemma l139 : s1 -> p161 (* BND(1 + R + Q, [0.997292, 1.25]) *).
Proof.
 intros h0.
 assert (h1 := l140 h0).
 assert (h2 := l142 h0).
 apply t115. exact h1. exact h2.
Qed.
Definition i124 := makepairF f9 f59.
Notation p169 := (BND _m i124). (* BND(m, [-6.61744e-22, 0.25]) *)
Lemma t116 : p161 -> p169 -> p160.
Proof.
 intros h0 h1.
 refine (add r4 _m i117 i124 i116 h0 h1 _) ; finalize.
Qed.
Lemma l138 : s1 -> p160 (* BND(1 + R + Q + m, [0.997292, 1.5]) *).
Proof.
 intros h0.
 assert (h1 := l139 h0).
 assert (h2 := l125 h0).
 apply t116. exact h1. refine (subset _m i5 i124 h2 _) ; finalize.
Qed.
Definition i125 := makepairF f7 f63.
Notation p170 := (BND _a i125). (* BND(a, [-5.56419e-24, 0.5]) *)
Lemma t117 : p160 -> p170 -> p159.
Proof.
 intros h0 h1.
 refine (add r3 _a i116 i125 i115 h0 h1 _) ; finalize.
Qed.
Lemma l137 : s1 -> p159 (* BND(expR, [0.997292, 2]) *).
Proof.
 intros h0.
 assert (h1 := l138 h0).
 assert (h2 := l126 h0).
 apply t117. exact h1. refine (subset _a i4 i125 h2 _) ; finalize.
Qed.
Lemma t118 : p23 -> p159 -> p22.
Proof.
 intros h0 h1.
 refine (div_op r72 _expR i22 i115 i21 h0 h1 _) ; finalize.
Qed.
Lemma l20 : s1 -> p22 (* BND((1 + P - expR) / expR, [-1.50292e-21, 1.50292e-21]) *).
Proof.
 intros h0.
 assert (h1 := l21 h0).
 assert (h2 := l137 h0).
 apply t118. exact h1. exact h2.
Qed.
Lemma t119 : p18 -> p22 -> p21.
Proof.
 intros h0 h1.
 refine (add r6 r71 i17 i21 i20 h0 h1 _) ; finalize.
Qed.
Lemma l19 : s1 -> p21 (* BND(1 + (1 + P - expR) / expR, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l9 h0).
 assert (h2 := l20 h0).
 apply t119. exact h1. exact h2.
Qed.
Lemma t120 : p15 -> p21 -> p14.
Proof.
 intros h0 h1.
 refine (mul_pp r68 r70 i14 i20 i13 h0 h1 _) ; finalize.
Qed.
Lemma l5 : s1 -> p14 (* BND((1 + d4) * (1 + d3) * (1 + d2) * (1 + (1 + P - expR) / expR), [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l6 h0).
 assert (h2 := l19 h0).
 apply t120. exact h1. exact h2.
Qed.
Lemma t121 : p14 -> p18 -> p13.
Proof.
 intros h0 h1.
 refine (sub r67 r6 i13 i17 i12 h0 h1 _) ; finalize.
Qed.
Lemma l4 : s1 -> p13 (* BND((1 + d4) * (1 + d3) * (1 + d2) * (1 + (1 + P - expR) / expR) - 1, [-1.50292e-21, 1.50292e-21]) *).
Proof.
 intros h0.
 assert (h1 := l5 h0).
 assert (h2 := l9 h0).
 apply t121. exact h1. exact h2.
Qed.
Notation p171 := (REL r30 r66 i114). (* REL((Y - Tj * expR) / (Tj * expR), (1 + d4) * (1 + d3) * (1 + d2) * (1 + (1 + P - expR) / expR) - 1, [0, 0]) *)
Notation p172 := (r30 = r66). (* EQL((Y - Tj * expR) / (Tj * expR), (1 + d4) * (1 + d3) * (1 + d2) * (1 + (1 + P - expR) / expR) - 1) *)
Notation p173 := (NZR _Tj). (* NZR(Tj) *)
Notation p174 := (ABS _Tj i10). (* ABS(Tj, [1, 2]) *)
Lemma l147 : s1 -> p10 (* BND(Tj, [1, 2]) *).
Proof.
 intros h0.
 assert (h1 := l12 h0).
 exact (proj2 h1).
Qed.
Lemma t122 : p10 -> p174.
Proof.
 intros h0.
 refine (abs_of_bnd_p _Tj i10 i10 h0 _) ; finalize.
Qed.
Lemma l146 : s1 -> p174 (* ABS(Tj, [1, 2]) *).
Proof.
 intros h0.
 assert (h1 := l147 h0).
 apply t122. exact h1.
Qed.
Lemma t123 : p174 -> p173.
Proof.
 intros h0.
 refine (nzr_of_abs _Tj i10 h0 _) ; finalize.
Qed.
Lemma l145 : s1 -> p173 (* NZR(Tj) *).
Proof.
 intros h0.
 assert (h1 := l146 h0).
 apply t123. exact h1.
Qed.
Notation p175 := (NZR _expR). (* NZR(expR) *)
Definition i126 := makepairF f63 f20.
Notation p176 := (ABS _expR i126). (* ABS(expR, [0.5, 2]) *)
Definition f185 := Float2 (3) (-2).
Definition i127 := makepairF f185 f179.
Notation p177 := (ABS r3 i127). (* ABS(1 + R + Q + m, [0.75, 1.5]) *)
Definition f186 := Float2 (7) (-3).
Definition i128 := makepairF f186 f181.
Notation p178 := (ABS r4 i128). (* ABS(1 + R + Q, [0.875, 1.25]) *)
Definition f187 := Float2 (15) (-4).
Definition i129 := makepairF f187 f182.
Notation p179 := (ABS r5 i129). (* ABS(1 + R, [0.9375, 1.125]) *)
Notation p180 := (ABS r6 i17). (* ABS(1, [1, 1]) *)
Lemma t124 : p18 -> p180.
Proof.
 intros h0.
 refine (abs_of_bnd_p r6 i17 i17 h0 _) ; finalize.
Qed.
Lemma l153 : s1 -> p180 (* ABS(1, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l9 h0).
 apply t124. exact h1.
Qed.
Definition i130 := makepairF f53 f132.
Notation p181 := (ABS _R i130). (* ABS(R, [0, 0.0625]) *)
Notation p182 := (ABS r8 i70). (* ABS(rhi + rlo, [0, 0.03125]) *)
Notation p183 := (BND r8 i71). (* BND(rhi + rlo, [-0.03125, 0.03125]) *)
Lemma t125 : p183 -> p182.
Proof.
 intros h0.
 refine (abs_of_bnd_o r8 i71 i70 h0 _) ; finalize.
Qed.
Lemma l155 : s1 -> p182 (* ABS(rhi + rlo, [0, 0.03125]) *).
Proof.
 intros h0.
 assert (h1 := l129 h0).
 apply t125. refine (subset r8 i109 i71 h1 _) ; finalize.
Qed.
Notation p184 := (ABS _dr i70). (* ABS(dr, [0, 0.03125]) *)
Notation p185 := (BND _dr i71). (* BND(dr, [-0.03125, 0.03125]) *)
Lemma t126 : p185 -> p184.
Proof.
 intros h0.
 refine (abs_of_bnd_o _dr i71 i70 h0 _) ; finalize.
Qed.
Lemma l156 : s1 -> p184 (* ABS(dr, [0, 0.03125]) *).
Proof.
 intros h0.
 assert (h1 := l26 h0).
 apply t126. refine (subset _dr i3 i71 h1 _) ; finalize.
Qed.
Lemma t127 : p182 -> p184 -> p181.
Proof.
 intros h0 h1.
 refine (sub_aa_o r8 _dr i70 i70 i130 h0 h1 _) ; finalize.
Qed.
Lemma l154 : s1 -> p181 (* ABS(R, [0, 0.0625]) *).
Proof.
 intros h0.
 assert (h1 := l155 h0).
 assert (h2 := l156 h0).
 apply t127. exact h1. exact h2.
Qed.
Lemma t128 : p180 -> p181 -> p179.
Proof.
 intros h0 h1.
 refine (add_aa_p r6 _R i17 i130 i129 h0 h1 _) ; finalize.
Qed.
Lemma l152 : s1 -> p179 (* ABS(1 + R, [0.9375, 1.125]) *).
Proof.
 intros h0.
 assert (h1 := l153 h0).
 assert (h2 := l154 h0).
 apply t128. exact h1. exact h2.
Qed.
Notation p186 := (ABS _Q i130). (* ABS(Q, [0, 0.0625]) *)
Notation p187 := (ABS r15 i123). (* ABS(5e-1 + rhi * (c3 + rhi * (c4 + rhi * (c5 + rhi * c6))), [0.25, 1]) *)
Definition i131 := makepairF f53 f59.
Notation p188 := (ABS r17 i131). (* ABS(rhi * (c3 + rhi * (c4 + rhi * (c5 + rhi * c6))), [0, 0.25]) *)
Definition i132 := makepairF f66 f19.
Notation p189 := (ABS r18 i132). (* ABS(c3 + rhi * (c4 + rhi * (c5 + rhi * c6)), [0.125, 1]) *)
Notation p190 := (ABS r20 i70). (* ABS(rhi * (c4 + rhi * (c5 + rhi * c6)), [0, 0.03125]) *)
Definition i133 := makepairF f72 f19.
Notation p191 := (ABS r21 i133). (* ABS(c4 + rhi * (c5 + rhi * c6), [0.03125, 1]) *)
Definition i134 := makepairF f74 f63.
Notation p192 := (ABS _c4 i134). (* ABS(c4, [0.0390625, 0.5]) *)
Notation p193 := (BND _c4 i134). (* BND(c4, [0.0390625, 0.5]) *)
Lemma t129 : p193 -> p192.
Proof.
 intros h0.
 refine (abs_of_bnd_p _c4 i134 i134 h0 _) ; finalize.
Qed.
Lemma l163 : s1 -> p192 (* ABS(c4, [0.0390625, 0.5]) *).
Proof.
 intros h0.
 assert (h1 := l54 h0).
 apply t129. refine (subset _c4 i42 i134 h1 _) ; finalize.
Qed.
Definition i135 := makepairF f53 f78.
Notation p194 := (ABS r23 i135). (* ABS(rhi * (c5 + rhi * c6), [0, 0.0078125]) *)
Definition i136 := makepairF f78 f59.
Notation p195 := (ABS r24 i136). (* ABS(c5 + rhi * c6, [0.0078125, 0.25]) *)
Definition i137 := makepairF f80 f66.
Notation p196 := (ABS _c5 i137). (* ABS(c5, [0.00830078, 0.125]) *)
Notation p197 := (BND _c5 i137). (* BND(c5, [0.00830078, 0.125]) *)
Lemma t130 : p197 -> p196.
Proof.
 intros h0.
 refine (abs_of_bnd_p _c5 i137 i137 h0 _) ; finalize.
Qed.
Lemma l166 : s1 -> p196 (* ABS(c5, [0.00830078, 0.125]) *).
Proof.
 intros h0.
 assert (h1 := l59 h0).
 apply t130. refine (subset _c5 i45 i137 h1 _) ; finalize.
Qed.
Notation p198 := (ABS r26 i62). (* ABS(rhi * c6, [0, 0.000488281]) *)
Lemma t131 : p196 -> p198 -> p195.
Proof.
 intros h0 h1.
 refine (add_aa_p _c5 r26 i137 i62 i136 h0 h1 _) ; finalize.
Qed.
Lemma l165 : s1 -> p195 (* ABS(c5 + rhi * c6, [0.0078125, 0.25]) *).
Proof.
 intros h0.
 assert (h1 := l166 h0).
 assert (h2 := l114 h0).
 apply t131. exact h1. refine (abs_subset r26 i28 i62 h2 _) ; finalize.
Qed.
Notation p199 := (ABS _rhi i70). (* ABS(rhi, [0, 0.03125]) *)
Lemma t132 : p199 -> p195 -> p194.
Proof.
 intros h0 h1.
 refine (mul_aa _rhi r24 i70 i136 i135 h0 h1 _) ; finalize.
Qed.
Lemma l164 : s1 -> p194 (* ABS(rhi * (c5 + rhi * c6), [0, 0.0078125]) *).
Proof.
 intros h0.
 assert (h1 := l38 h0).
 assert (h2 := l165 h0).
 apply t132. refine (abs_subset _rhi i31 i70 h1 _) ; finalize. exact h2.
Qed.
Lemma t133 : p192 -> p194 -> p191.
Proof.
 intros h0 h1.
 refine (add_aa_p _c4 r23 i134 i135 i133 h0 h1 _) ; finalize.
Qed.
Lemma l162 : s1 -> p191 (* ABS(c4 + rhi * (c5 + rhi * c6), [0.03125, 1]) *).
Proof.
 intros h0.
 assert (h1 := l163 h0).
 assert (h2 := l164 h0).
 apply t133. exact h1. exact h2.
Qed.
Lemma t134 : p199 -> p191 -> p190.
Proof.
 intros h0 h1.
 refine (mul_aa _rhi r21 i70 i133 i70 h0 h1 _) ; finalize.
Qed.
Lemma l161 : s1 -> p190 (* ABS(rhi * (c4 + rhi * (c5 + rhi * c6)), [0, 0.03125]) *).
Proof.
 intros h0.
 assert (h1 := l38 h0).
 assert (h2 := l162 h0).
 apply t134. refine (abs_subset _rhi i31 i70 h1 _) ; finalize. exact h2.
Qed.
Definition i138 := makepairF f68 f63.
Notation p200 := (ABS _c3 i138). (* ABS(c3, [0.15625, 0.5]) *)
Lemma t135 : p200 -> p190 -> p189.
Proof.
 intros h0 h1.
 refine (add_aa_p _c3 r20 i138 i70 i132 h0 h1 _) ; finalize.
Qed.
Lemma l160 : s1 -> p189 (* ABS(c3 + rhi * (c4 + rhi * (c5 + rhi * c6)), [0.125, 1]) *).
Proof.
 intros h0.
 assert (h1 := l86 h0).
 assert (h2 := l161 h0).
 apply t135. refine (abs_subset _c3 i69 i138 h1 _) ; finalize. exact h2.
Qed.
Notation p201 := (ABS _rhi i131). (* ABS(rhi, [0, 0.25]) *)
Lemma t136 : p201 -> p189 -> p188.
Proof.
 intros h0 h1.
 refine (mul_aa _rhi r18 i131 i132 i131 h0 h1 _) ; finalize.
Qed.
Lemma l159 : s1 -> p188 (* ABS(rhi * (c3 + rhi * (c4 + rhi * (c5 + rhi * c6))), [0, 0.25]) *).
Proof.
 intros h0.
 assert (h1 := l38 h0).
 assert (h2 := l160 h0).
 apply t136. refine (abs_subset _rhi i31 i131 h1 _) ; finalize. exact h2.
Qed.
Lemma t137 : p78 -> p188 -> p187.
Proof.
 intros h0 h1.
 refine (add_aa_p r16 r17 i36 i131 i123 h0 h1 _) ; finalize.
Qed.
Lemma l158 : s1 -> p187 (* ABS(5e-1 + rhi * (c3 + rhi * (c4 + rhi * (c5 + rhi * c6))), [0.25, 1]) *).
Proof.
 intros h0.
 assert (h1 := l72 h0).
 assert (h2 := l159 h0).
 apply t137. exact h1. exact h2.
Qed.
Notation p202 := (ABS r14 i130). (* ABS(rhi * rhi, [0, 0.0625]) *)
Lemma t138 : p202 -> p187 -> p186.
Proof.
 intros h0 h1.
 refine (mul_aa r14 r15 i130 i123 i130 h0 h1 _) ; finalize.
Qed.
Lemma l157 : s1 -> p186 (* ABS(Q, [0, 0.0625]) *).
Proof.
 intros h0.
 assert (h1 := l117 h0).
 assert (h2 := l158 h0).
 apply t138. refine (abs_subset r14 i94 i130 h1 _) ; finalize. exact h2.
Qed.
Lemma t139 : p179 -> p186 -> p178.
Proof.
 intros h0 h1.
 refine (add_aa_p r5 _Q i129 i130 i128 h0 h1 _) ; finalize.
Qed.
Lemma l151 : s1 -> p178 (* ABS(1 + R + Q, [0.875, 1.25]) *).
Proof.
 intros h0.
 assert (h1 := l152 h0).
 assert (h2 := l157 h0).
 apply t139. exact h1. exact h2.
Qed.
Notation p203 := (ABS _m i122). (* ABS(m, [0, 0.125]) *)
Definition f188 := Float2 (-1) (-3).
Definition i139 := makepairF f188 f66.
Notation p204 := (BND _m i139). (* BND(m, [-0.125, 0.125]) *)
Lemma t140 : p204 -> p203.
Proof.
 intros h0.
 refine (abs_of_bnd_o _m i139 i122 h0 _) ; finalize.
Qed.
Lemma l167 : s1 -> p203 (* ABS(m, [0, 0.125]) *).
Proof.
 intros h0.
 assert (h1 := l125 h0).
 apply t140. refine (subset _m i5 i139 h1 _) ; finalize.
Qed.
Lemma t141 : p178 -> p203 -> p177.
Proof.
 intros h0 h1.
 refine (add_aa_p r4 _m i128 i122 i127 h0 h1 _) ; finalize.
Qed.
Lemma l150 : s1 -> p177 (* ABS(1 + R + Q + m, [0.75, 1.5]) *).
Proof.
 intros h0.
 assert (h1 := l151 h0).
 assert (h2 := l167 h0).
 apply t141. exact h1. exact h2.
Qed.
Notation p205 := (ABS _a i131). (* ABS(a, [0, 0.25]) *)
Definition i140 := makepairF f64 f59.
Notation p206 := (BND _a i140). (* BND(a, [-0.25, 0.25]) *)
Lemma t142 : p206 -> p205.
Proof.
 intros h0.
 refine (abs_of_bnd_o _a i140 i131 h0 _) ; finalize.
Qed.
Lemma l168 : s1 -> p205 (* ABS(a, [0, 0.25]) *).
Proof.
 intros h0.
 assert (h1 := l126 h0).
 apply t142. refine (subset _a i4 i140 h1 _) ; finalize.
Qed.
Lemma t143 : p177 -> p205 -> p176.
Proof.
 intros h0 h1.
 refine (add_aa_p r3 _a i127 i131 i126 h0 h1 _) ; finalize.
Qed.
Lemma l149 : s1 -> p176 (* ABS(expR, [0.5, 2]) *).
Proof.
 intros h0.
 assert (h1 := l150 h0).
 assert (h2 := l168 h0).
 apply t143. exact h1. exact h2.
Qed.
Lemma t144 : p176 -> p175.
Proof.
 intros h0.
 refine (nzr_of_abs _expR i126 h0 _) ; finalize.
Qed.
Lemma l148 : s1 -> p175 (* NZR(expR) *).
Proof.
 intros h0.
 assert (h1 := l149 h0).
 apply t144. exact h1.
Qed.
Lemma t145 : p173 -> p175 -> p172.
Proof.
 intros h0 h1.
 refine (b1 h0 h1) ; finalize.
Qed.
Lemma l144 : s1 -> p172 (* EQL((Y - Tj * expR) / (Tj * expR), (1 + d4) * (1 + d3) * (1 + d2) * (1 + (1 + P - expR) / expR) - 1) *).
Proof.
 intros h0.
 assert (h1 := l145 h0).
 assert (h2 := l148 h0).
 apply t145. exact h1. exact h2.
Qed.
Notation p207 := (REL r66 r66 i114). (* REL((1 + d4) * (1 + d3) * (1 + d2) * (1 + (1 + P - expR) / expR) - 1, (1 + d4) * (1 + d3) * (1 + d2) * (1 + (1 + P - expR) / expR) - 1, [0, 0]) *)
Lemma t146 : p207.
Proof.
 refine (rel_refl r66 i114 _) ; finalize.
Qed.
Lemma l169 : s1 -> p207 (* REL((1 + d4) * (1 + d3) * (1 + d2) * (1 + (1 + P - expR) / expR) - 1, (1 + d4) * (1 + d3) * (1 + d2) * (1 + (1 + P - expR) / expR) - 1, [0, 0]) *).
Proof.
 intros h0.
 apply t146.
Qed.
Lemma t147 : p172 -> p207 -> p171.
Proof.
 intros h0 h1.
 refine (rel_rewrite_1 r30 r66 r66 i114 h0 h1) ; finalize.
Qed.
Lemma l143 : s1 -> p171 (* REL((Y - Tj * expR) / (Tj * expR), (1 + d4) * (1 + d3) * (1 + d2) * (1 + (1 + P - expR) / expR) - 1, [0, 0]) *).
Proof.
 intros h0.
 assert (h1 := l144 h0).
 assert (h2 := l169 h0).
 apply t147. exact h1. exact h2.
Qed.
Lemma t148 : p13 -> p171 -> p12.
Proof.
 intros h0 h1.
 refine (bnd_of_bnd_rel_o r30 r66 i12 i114 i12 h0 h1 _) ; finalize.
Qed.
Lemma l3 : s1 -> p12 (* BND((Y - Tj * expR) / (Tj * expR), [-1.50292e-21, 1.50292e-21]) *).
Proof.
 intros h0.
 assert (h1 := l4 h0).
 assert (h2 := l143 h0).
 apply t148. exact h1. exact h2.
Qed.
Lemma l1 : s1 -> False.
Proof.
 intros h0.
 assert (h1 := l2 h0).
 assert (h2 := l3 h0).
 refine (simplify (Tatom false (Abnd 0%nat i11)) Tfalse (Abnd 0%nat i12) (List.cons r30 List.nil) h2 h1 _) ; finalize.
Qed.
End Generated_by_Gappa.
