Require Import Gappa.Gappa_library.
Section Generated_by_Gappa.
Variable _th_ : R.
Notation _th := ((rounding_float rndNE (53)%positive (-1074)%Z) _th_).
Notation r3 := ((_th * _th)%R).
Notation r2 := ((r3 * _th)%R).
Notation _s0 := (float2R (Float2 (-6004799503160661) (-55))).
Notation _s1 := (float2R (Float2 (600479950272053) (-56))).
Notation _s2 := (float2R (Float2 (-3659917331012787) (-64))).
Notation r11 := ((r3 * _s2)%R).
Notation r9 := ((_s1 + r11)%R).
Notation r8 := ((r3 * r9)%R).
Notation _P := ((_s0 + r8)%R).
Notation _T := ((r2 * _P)%R).
Notation _uh := ((rounding_float rndNE (53)%positive (-1074)%Z) r3).
Notation r14 := ((_th * _uh)%R).
Notation _a3 := ((rounding_float rndNE (53)%positive (-1074)%Z) r14).
Notation r23 := ((_uh * _s2)%R).
Notation r22 := ((rounding_float rndNE (53)%positive (-1074)%Z) r23).
Notation r21 := ((_s1 + r22)%R).
Notation _p2 := ((rounding_float rndNE (53)%positive (-1074)%Z) r21).
Notation r19 := ((_uh * _p2)%R).
Notation r18 := ((rounding_float rndNE (53)%positive (-1074)%Z) r19).
Notation r17 := ((_s0 + r18)%R).
Notation _ps := ((rounding_float rndNE (53)%positive (-1074)%Z) r17).
Notation r27 := ((_a3 * _ps)%R).
Notation _tail := ((rounding_float rndNE (53)%positive (-1074)%Z) r27).
Notation r25 := ((_tail - _T)%R).
Notation r24 := ((r25 / _T)%R).
Notation r32 := (Float1 (1)).
Notation r34 := ((_a3 - r2)%R).
Notation r33 := ((r34 / r2)%R).
Notation r31 := ((r32 + r33)%R).
Notation r37 := ((_ps - _P)%R).
Notation r36 := ((r37 / _P)%R).
Notation r35 := ((r32 + r36)%R).
Notation r30 := ((r31 * r35)%R).
Notation r40 := ((_tail - r27)%R).
Notation r39 := ((r40 / r27)%R).
Notation r38 := ((r32 + r39)%R).
Notation r29 := ((r30 * r38)%R).
Notation r28 := ((r29 - r32)%R).
Hypothesis a1 : (_T <> 0)%R -> (_th <> 0)%R -> (_P <> 0)%R -> (_a3 <> 0)%R -> (_ps <> 0)%R -> r24 = r28.
Lemma b1 : NZR _T -> NZR _th -> NZR _P -> NZR _a3 -> NZR _ps -> r24 = r28.
 intros h0 h1 h2 h3 h4.
 apply a1.
 exact h0.
 exact h1.
 exact h2.
 exact h3.
 exact h4.
Qed.
Notation r45 := ((_uh - r3)%R).
Notation r44 := ((r45 / r3)%R).
Notation r43 := ((r32 + r44)%R).
Notation r48 := ((_a3 - r14)%R).
Notation r47 := ((r48 / r14)%R).
Notation r46 := ((r32 + r47)%R).
Notation r42 := ((r43 * r46)%R).
Notation r41 := ((r42 - r32)%R).
Hypothesis a2 : (_th <> 0)%R -> (_uh <> 0)%R -> r33 = r41.
Lemma b2 : NZR _th -> NZR _uh -> r33 = r41.
 intros h0 h1.
 apply a2.
 exact h0.
 exact h1.
Qed.
Notation r49 := ((Rabs _th)%R).
Definition f1 := Float2 (1) (-60).
Definition f2 := Float2 (80696341590167128190183336492762922277553037908230366465363237155637854447075094068654269148145619287504548485417148267) (-402).
Definition i1 := makepairF f1 f2.
Notation p1 := (BND r49 i1). (* BND(|th|, [8.67362e-19, 0.0078126]) *)
Definition f3 := Float2 (-1) (-50).
Definition f4 := Float2 (1) (-50).
Definition i2 := makepairF f3 f4.
Notation p2 := (BND r24 i2). (* BND((tail - T) / T, [-8.88178e-16, 8.88178e-16]) *)
Definition s2 := (not p2).
Definition s1 := (p1 /\ s2).
Lemma l2 : s1 -> s2.
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj2 h1).
Qed.
Definition f5 := Float2 (-2420866402485848720065916205948702023189480775708388356875015403998520177260158005485136010971145517194833902201303898685) (-451).
Definition f6 := Float2 (2420866402485849472625440110049679517814151487756135096312451689447599133166092993581336944731759229675779679844339014301) (-451).
Definition i3 := makepairF f5 f6.
Notation p3 := (BND r24 i3). (* BND((tail - T) / T, [-4.16335e-16, 4.16335e-16]) *)
Notation p4 := (NZR _T). (* NZR(T) *)
Notation p5 := (NZR r2). (* NZR(th * th * th) *)
Notation p6 := (NZR r3). (* NZR(th * th) *)
Definition f7 := Float2 (1) (-120).
Definition f8 := Float2 (1) (0).
Definition i4 := makepairF f7 f8.
Notation p7 := (ABS r3 i4). (* ABS(th * th, [7.52316e-37, 1]) *)
Definition f9 := Float2 (630440168673180688985807316349710330293383108658049738010650290278420737867774172411361477719887650683629285042321471) (-395).
Definition i5 := makepairF f1 f9.
Notation p8 := (ABS _th i5). (* ABS(th, [8.67362e-19, 0.0078126]) *)
Lemma l9 : s1 -> p1 (* BND(|th|, [8.67362e-19, 0.0078126]) *).
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj1 h1).
Qed.
Notation p9 := (BND r49 i5). (* BND(|th|, [8.67362e-19, 0.0078126]) *)
Lemma t1 : p9 -> p8.
Proof.
 intros h0.
 refine (abs_of_uabs _th i5 h0 _) ; finalize.
Qed.
Lemma l8 : s1 -> p8 (* ABS(th, [8.67362e-19, 0.0078126]) *).
Proof.
 intros h0.
 assert (h1 := l9 h0).
 apply t1. refine (subset r49 i1 i5 h1 _) ; finalize.
Qed.
Definition i6 := makepairF f1 f8.
Notation p10 := (ABS _th i6). (* ABS(th, [8.67362e-19, 1]) *)
Lemma t2 : p10 -> p10 -> p7.
Proof.
 intros h0 h1.
 refine (mul_aa _th _th i6 i6 i4 h0 h1 _) ; finalize.
Qed.
Lemma l7 : s1 -> p7 (* ABS(th * th, [7.52316e-37, 1]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 apply t2. refine (abs_subset _th i5 i6 h1 _) ; finalize. refine (abs_subset _th i5 i6 h1 _) ; finalize.
Qed.
Lemma t3 : p7 -> p6.
Proof.
 intros h0.
 refine (nzr_of_abs r3 i4 h0 _) ; finalize.
Qed.
Lemma l6 : s1 -> p6 (* NZR(th * th) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 apply t3. exact h1.
Qed.
Notation p11 := (NZR _th). (* NZR(th) *)
Lemma t4 : p10 -> p11.
Proof.
 intros h0.
 refine (nzr_of_abs _th i6 h0 _) ; finalize.
Qed.
Lemma l10 : s1 -> p11 (* NZR(th) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 apply t4. refine (abs_subset _th i5 i6 h1 _) ; finalize.
Qed.
Lemma t5 : p6 -> p11 -> p5.
Proof.
 intros h0 h1.
 refine (mul_nzr r3 _th h0 h1) ; finalize.
Qed.
Lemma l5 : s1 -> p5 (* NZR(th * th * th) *).
Proof.
 intros h0.
 assert (h1 := l6 h0).
 assert (h2 := l10 h0).
 apply t5. exact h1. exact h2.
Qed.
Notation p12 := (NZR _P). (* NZR(P) *)
Definition f10 := Float2 (1) (-3).
Definition i7 := makepairF f10 f8.
Notation p13 := (ABS _P i7). (* ABS(P, [0.125, 1]) *)
Definition f11 := Float2 (-6004799503160661) (-55).
Definition f12 := Float2 (-1721494664989286788124845307901986960002173545774584563379567055879969408983001116710810045385859313950959688360338622479) (-402).
Definition i8 := makepairF f11 f12.
Notation p14 := (BND _P i8). (* BND(P, [-0.166667, -0.166666]) *)
Definition i9 := makepairF f11 f11.
Notation p15 := (BND _s0 i9). (* BND(s0, [-0.166667, -0.166667]) *)
Lemma t6 : p15.
Proof.
 refine (constant2 _ i9 _) ; finalize.
Qed.
Lemma l14 : s1 -> p15 (* BND(s0, [-0.166667, -0.166667]) *).
Proof.
 intros h0.
 apply t6.
Qed.
Definition f13 := Float2 (1) (-127).
Definition f14 := Float2 (84059765101483999868914885994225601488189727070591743967463499981599392395284061338983157849132088576747193430933263) (-406).
Definition i10 := makepairF f13 f14.
Notation p16 := (BND r8 i10). (* BND(th * th * (s1 + th * th * s2), [5.87747e-39, 5.08639e-07]) *)
Definition f15 := Float2 (630448238307339705698626334683359606585610863961840561047296826602136301653218879920768343146802465245558035497170013) (-402).
Definition i11 := makepairF f7 f15.
Notation p17 := (BND r3 i11). (* BND(th * th, [7.52316e-37, 6.10367e-05]) *)
Lemma t7 : p8 -> p17.
Proof.
 intros h0.
 refine (square _th i5 i11 h0 _) ; finalize.
Qed.
Lemma l16 : s1 -> p17 (* BND(th * th, [7.52316e-37, 6.10367e-05]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 apply t7. exact h1.
Qed.
Definition f16 := Float2 (344299483384574615805899266577269158490928065587148694741429816132992163812105584381891942228338403909385475126408087167) (-404).
Definition f17 := Float2 (204332738767141621261506082902499256098663227100226381) (-184).
Definition i12 := makepairF f16 f17.
Notation p18 := (BND r9 i12). (* BND(s1 + th * th * s2, [0.00833332, 0.00833333]) *)
Definition f18 := Float2 (600479950272053) (-56).
Definition i13 := makepairF f18 f18.
Notation p19 := (BND _s1 i13). (* BND(s1, [0.00833333, 0.00833333]) *)
Lemma t8 : p19.
Proof.
 refine (constant2 _ i13 _) ; finalize.
Qed.
Lemma l18 : s1 -> p19 (* BND(s1, [0.00833333, 0.00833333]) *).
Proof.
 intros h0.
 apply t8.
Qed.
Definition f19 := Float2 (-500335110514385210002327283606042770175255863276700092569854957770140194436201644281461789939636940853671853193601) (-404).
Definition f20 := Float2 (-3659917331012787) (-184).
Definition i14 := makepairF f19 f20.
Notation p20 := (BND r11 i14). (* BND(th * th * s2, [-1.211e-08, -1.49263e-40]) *)
Definition f21 := Float2 (-3659917331012787) (-64).
Definition i15 := makepairF f21 f21.
Notation p21 := (BND _s2 i15). (* BND(s2, [-0.000198405, -0.000198405]) *)
Lemma t9 : p21.
Proof.
 refine (constant2 _ i15 _) ; finalize.
Qed.
Lemma l20 : s1 -> p21 (* BND(s2, [-0.000198405, -0.000198405]) *).
Proof.
 intros h0.
 apply t9.
Qed.
Definition f22 := Float2 (4925376861776091450770518239713746926450084874701879383182006457829189856665772499381002680834394259730922152321641) (-395).
Definition i16 := makepairF f7 f22.
Notation p22 := (BND r3 i16). (* BND(th * th, [7.52316e-37, 6.10367e-05]) *)
Lemma t10 : p22 -> p21 -> p20.
Proof.
 intros h0 h1.
 refine (mul_pn r3 _s2 i16 i15 i14 h0 h1 _) ; finalize.
Qed.
Lemma l19 : s1 -> p20 (* BND(th * th * s2, [-1.211e-08, -1.49263e-40]) *).
Proof.
 intros h0.
 assert (h1 := l16 h0).
 assert (h2 := l20 h0).
 apply t10. refine (subset r3 i11 i16 h1 _) ; finalize. exact h2.
Qed.
Lemma t11 : p19 -> p20 -> p18.
Proof.
 intros h0 h1.
 refine (add _s1 r11 i13 i14 i12 h0 h1 _) ; finalize.
Qed.
Lemma l17 : s1 -> p18 (* BND(s1 + th * th * s2, [0.00833332, 0.00833333]) *).
Proof.
 intros h0.
 assert (h1 := l18 h0).
 assert (h2 := l19 h0).
 apply t11. exact h1. exact h2.
Qed.
Definition f23 := Float2 (1) (-7).
Definition i17 := makepairF f23 f17.
Notation p23 := (BND r9 i17). (* BND(s1 + th * th * s2, [0.0078125, 0.00833333]) *)
Lemma t12 : p17 -> p23 -> p16.
Proof.
 intros h0 h1.
 refine (mul_pp r3 r9 i11 i17 i10 h0 h1 _) ; finalize.
Qed.
Lemma l15 : s1 -> p16 (* BND(th * th * (s1 + th * th * s2), [5.87747e-39, 5.08639e-07]) *).
Proof.
 intros h0.
 assert (h1 := l16 h0).
 assert (h2 := l17 h0).
 apply t12. exact h1. refine (subset r9 i12 i17 h2 _) ; finalize.
Qed.
Definition f24 := Float2 (5253735318842749991807180374639100093011857941911983997966468748849962024705253833686447365570755536046699589433329) (-402).
Definition i18 := makepairF f13 f24.
Notation p24 := (BND r8 i18). (* BND(th * th * (s1 + th * th * s2), [5.87747e-39, 5.08639e-07]) *)
Lemma t13 : p15 -> p24 -> p14.
Proof.
 intros h0 h1.
 refine (add _s0 r8 i9 i18 i8 h0 h1 _) ; finalize.
Qed.
Lemma l13 : s1 -> p14 (* BND(P, [-0.166667, -0.166666]) *).
Proof.
 intros h0.
 assert (h1 := l14 h0).
 assert (h2 := l15 h0).
 apply t13. exact h1. refine (subset r8 i10 i18 h2 _) ; finalize.
Qed.
Definition f25 := Float2 (-1) (0).
Definition f26 := Float2 (-1) (-3).
Definition i19 := makepairF f25 f26.
Notation p25 := (BND _P i19). (* BND(P, [-1, -0.125]) *)
Lemma t14 : p25 -> p13.
Proof.
 intros h0.
 refine (abs_of_bnd_n _P i19 i7 h0 _) ; finalize.
Qed.
Lemma l12 : s1 -> p13 (* ABS(P, [0.125, 1]) *).
Proof.
 intros h0.
 assert (h1 := l13 h0).
 apply t14. refine (subset _P i8 i19 h1 _) ; finalize.
Qed.
Lemma t15 : p13 -> p12.
Proof.
 intros h0.
 refine (nzr_of_abs _P i7 h0 _) ; finalize.
Qed.
Lemma l11 : s1 -> p12 (* NZR(P) *).
Proof.
 intros h0.
 assert (h1 := l12 h0).
 apply t15. exact h1.
Qed.
Lemma t16 : p5 -> p12 -> p4.
Proof.
 intros h0 h1.
 refine (mul_nzr r2 _P h0 h1) ; finalize.
Qed.
Lemma l4 : s1 -> p4 (* NZR(T) *).
Proof.
 intros h0.
 assert (h1 := l5 h0).
 assert (h2 := l11 h0).
 apply t16. exact h1. exact h2.
Qed.
Notation p26 := (REL _tail _T i3). (* REL(tail, T, [-4.16335e-16, 4.16335e-16]) *)
Definition f27 := Float2 (-1) (-53).
Definition f28 := Float2 (1) (-53).
Definition i20 := makepairF f27 f28.
Notation p27 := (REL _tail r27 i20). (* REL(tail, a3 * ps, [-1.11022e-16, 1.11022e-16]) *)
Notation p28 := (FIX r27 (-641)). (* FIX(a3 * ps, -641) *)
Notation p29 := (FIX _a3 (-284)). (* FIX(a3, -284) *)
Notation p30 := (FIX r14 (-284)). (* FIX(th * uh, -284) *)
Notation p31 := (FIX _th (-112)). (* FIX(th, -112) *)
Notation p32 := (FLT _th (53)). (* FLT(th, 53) *)
Lemma t17 : p32.
Proof.
 refine (flt_of_float _ _ _ (53) _ _) ; finalize.
Qed.
Lemma l27 : s1 -> p32 (* FLT(th, 53) *).
Proof.
 intros h0.
 apply t17.
Qed.
Lemma t18 : p32 -> p10 -> p31.
Proof.
 intros h0 h1.
 refine (fix_of_flt_bnd _th i6 (-112) (53) h0 h1 _) ; finalize.
Qed.
Lemma l26 : s1 -> p31 (* FIX(th, -112) *).
Proof.
 intros h0.
 assert (h1 := l27 h0).
 assert (h2 := l8 h0).
 apply t18. exact h1. refine (abs_subset _th i5 i6 h2 _) ; finalize.
Qed.
Notation p33 := (FIX _uh (-172)). (* FIX(uh, -172) *)
Notation p34 := (FLT _uh (53)). (* FLT(uh, 53) *)
Lemma t19 : p34.
Proof.
 refine (flt_of_float _ _ _ (53) _ _) ; finalize.
Qed.
Lemma l29 : s1 -> p34 (* FLT(uh, 53) *).
Proof.
 intros h0.
 apply t19.
Qed.
Definition f29 := Float2 (3) (-15).
Definition i21 := makepairF f7 f29.
Notation p35 := (ABS _uh i21). (* ABS(uh, [7.52316e-37, 9.15527e-05]) *)
Definition f30 := Float2 (2251857460129413) (-65).
Definition i22 := makepairF f7 f30.
Notation p36 := (BND _uh i22). (* BND(uh, [7.52316e-37, 6.10367e-05]) *)
Definition f31 := Float2 (9007429840517653) (-67).
Definition i23 := makepairF f7 f31.
Notation p37 := (BND r3 i23). (* BND(th * th, [7.52316e-37, 6.10367e-05]) *)
Lemma t20 : p37 -> p36.
Proof.
 intros h0.
 refine (float_round_ne _ _ r3 i23 i22 h0 _) ; finalize.
Qed.
Lemma l31 : s1 -> p36 (* BND(uh, [7.52316e-37, 6.10367e-05]) *).
Proof.
 intros h0.
 assert (h1 := l16 h0).
 apply t20. refine (subset r3 i11 i23 h1 _) ; finalize.
Qed.
Notation p38 := (BND _uh i21). (* BND(uh, [7.52316e-37, 9.15527e-05]) *)
Lemma t21 : p38 -> p35.
Proof.
 intros h0.
 refine (abs_of_bnd_p _uh i21 i21 h0 _) ; finalize.
Qed.
Lemma l30 : s1 -> p35 (* ABS(uh, [7.52316e-37, 9.15527e-05]) *).
Proof.
 intros h0.
 assert (h1 := l31 h0).
 apply t21. refine (subset _uh i22 i21 h1 _) ; finalize.
Qed.
Notation p39 := (ABS _uh i4). (* ABS(uh, [7.52316e-37, 1]) *)
Lemma t22 : p34 -> p39 -> p33.
Proof.
 intros h0 h1.
 refine (fix_of_flt_bnd _uh i4 (-172) (53) h0 h1 _) ; finalize.
Qed.
Lemma l28 : s1 -> p33 (* FIX(uh, -172) *).
Proof.
 intros h0.
 assert (h1 := l29 h0).
 assert (h2 := l30 h0).
 apply t22. exact h1. refine (abs_subset _uh i21 i4 h2 _) ; finalize.
Qed.
Lemma t23 : p31 -> p33 -> p30.
Proof.
 intros h0 h1.
 refine (mul_fix _th _uh (-112) (-172) (-284) h0 h1 _) ; finalize.
Qed.
Lemma l25 : s1 -> p30 (* FIX(th * uh, -284) *).
Proof.
 intros h0.
 assert (h1 := l26 h0).
 assert (h2 := l28 h0).
 apply t23. exact h1. exact h2.
Qed.
Lemma t24 : p30 -> p29.
Proof.
 intros h0.
 refine (fix_float_of_fix _ _ _ (-284) (-284) r14 h0 _) ; finalize.
Qed.
Lemma l24 : s1 -> p29 (* FIX(a3, -284) *).
Proof.
 intros h0.
 assert (h1 := l25 h0).
 apply t24. exact h1.
Qed.
Notation p40 := (FIX _ps (-357)). (* FIX(ps, -357) *)
Notation p41 := (FIX r17 (-357)). (* FIX(s0 + float<53,-1074,ne>(uh * p2), -357) *)
Notation p42 := (FIX _s0 (-55)). (* FIX(s0, -55) *)
Definition f32 := Float2 (6004799503160661) (-55).
Definition i24 := makepairF f32 f32.
Notation p43 := (ABS _s0 i24). (* ABS(s0, [0.166667, 0.166667]) *)
Lemma t25 : p15 -> p43.
Proof.
 intros h0.
 refine (abs_of_bnd_n _s0 i9 i24 h0 _) ; finalize.
Qed.
Lemma l35 : s1 -> p43 (* ABS(s0, [0.166667, 0.166667]) *).
Proof.
 intros h0.
 assert (h1 := l14 h0).
 apply t25. exact h1.
Qed.
Lemma t26 : p43 -> p42.
Proof.
 intros h0.
 refine (fix_of_singleton_bnd _s0 i24 (-55) h0 _) ; finalize.
Qed.
Lemma l34 : s1 -> p42 (* FIX(s0, -55) *).
Proof.
 intros h0.
 assert (h1 := l35 h0).
 apply t26. exact h1.
Qed.
Notation p44 := (FIX r18 (-357)). (* FIX(float<53,-1074,ne>(uh * p2), -357) *)
Notation p45 := (FIX r19 (-357)). (* FIX(uh * p2, -357) *)
Notation p46 := (FIX _p2 (-185)). (* FIX(p2, -185) *)
Notation p47 := (FIX r21 (-185)). (* FIX(s1 + float<53,-1074,ne>(uh * s2), -185) *)
Notation p48 := (FIX _s1 (-56)). (* FIX(s1, -56) *)
Notation p49 := (ABS _s1 i13). (* ABS(s1, [0.00833333, 0.00833333]) *)
Lemma t27 : p19 -> p49.
Proof.
 intros h0.
 refine (abs_of_bnd_p _s1 i13 i13 h0 _) ; finalize.
Qed.
Lemma l41 : s1 -> p49 (* ABS(s1, [0.00833333, 0.00833333]) *).
Proof.
 intros h0.
 assert (h1 := l18 h0).
 apply t27. exact h1.
Qed.
Lemma t28 : p49 -> p48.
Proof.
 intros h0.
 refine (fix_of_singleton_bnd _s1 i13 (-56) h0 _) ; finalize.
Qed.
Lemma l40 : s1 -> p48 (* FIX(s1, -56) *).
Proof.
 intros h0.
 assert (h1 := l41 h0).
 apply t28. exact h1.
Qed.
Notation p50 := (FIX r22 (-185)). (* FIX(float<53,-1074,ne>(uh * s2), -185) *)
Notation p51 := (FLT r22 (53)). (* FLT(float<53,-1074,ne>(uh * s2), 53) *)
Lemma t29 : p51.
Proof.
 refine (flt_of_float _ _ _ (53) _ _) ; finalize.
Qed.
Lemma l43 : s1 -> p51 (* FLT(float<53,-1074,ne>(uh * s2), 53) *).
Proof.
 intros h0.
 apply t29.
Qed.
Definition f33 := Float2 (1) (-133).
Definition i25 := makepairF f33 f8.
Notation p52 := (ABS r22 i25). (* ABS(float<53,-1074,ne>(uh * s2), [9.18355e-41, 1]) *)
Definition f34 := Float2 (-7320022050992203) (-79).
Definition f35 := Float2 (-1) (-133).
Definition i26 := makepairF f34 f35.
Notation p53 := (BND r22 i26). (* BND(float<53,-1074,ne>(uh * s2), [-1.211e-08, -9.18355e-41]) *)
Notation p54 := (BND r23 i26). (* BND(uh * s2, [-1.211e-08, -9.18355e-41]) *)
Definition f36 := Float2 (-1) (-13).
Definition i27 := makepairF f21 f36.
Notation p55 := (BND _s2 i27). (* BND(s2, [-0.000198405, -0.00012207]) *)
Lemma t30 : p36 -> p55 -> p54.
Proof.
 intros h0 h1.
 refine (mul_pn _uh _s2 i22 i27 i26 h0 h1 _) ; finalize.
Qed.
Lemma l46 : s1 -> p54 (* BND(uh * s2, [-1.211e-08, -9.18355e-41]) *).
Proof.
 intros h0.
 assert (h1 := l31 h0).
 assert (h2 := l20 h0).
 apply t30. exact h1. refine (subset _s2 i15 i27 h2 _) ; finalize.
Qed.
Lemma t31 : p54 -> p53.
Proof.
 intros h0.
 refine (float_round_ne _ _ r23 i26 i26 h0 _) ; finalize.
Qed.
Lemma l45 : s1 -> p53 (* BND(float<53,-1074,ne>(uh * s2), [-1.211e-08, -9.18355e-41]) *).
Proof.
 intros h0.
 assert (h1 := l46 h0).
 apply t31. exact h1.
Qed.
Definition i28 := makepairF f25 f35.
Notation p56 := (BND r22 i28). (* BND(float<53,-1074,ne>(uh * s2), [-1, -9.18355e-41]) *)
Lemma t32 : p56 -> p52.
Proof.
 intros h0.
 refine (abs_of_bnd_n r22 i28 i25 h0 _) ; finalize.
Qed.
Lemma l44 : s1 -> p52 (* ABS(float<53,-1074,ne>(uh * s2), [9.18355e-41, 1]) *).
Proof.
 intros h0.
 assert (h1 := l45 h0).
 apply t32. refine (subset r22 i26 i28 h1 _) ; finalize.
Qed.
Lemma t33 : p51 -> p52 -> p50.
Proof.
 intros h0 h1.
 refine (fix_of_flt_bnd r22 i25 (-185) (53) h0 h1 _) ; finalize.
Qed.
Lemma l42 : s1 -> p50 (* FIX(float<53,-1074,ne>(uh * s2), -185) *).
Proof.
 intros h0.
 assert (h1 := l43 h0).
 assert (h2 := l44 h0).
 apply t33. exact h1. exact h2.
Qed.
Lemma t34 : p48 -> p50 -> p47.
Proof.
 intros h0 h1.
 refine (add_fix _s1 r22 (-56) (-185) (-185) h0 h1 _) ; finalize.
Qed.
Lemma l39 : s1 -> p47 (* FIX(s1 + float<53,-1074,ne>(uh * s2), -185) *).
Proof.
 intros h0.
 assert (h1 := l40 h0).
 assert (h2 := l42 h0).
 apply t34. exact h1. exact h2.
Qed.
Lemma t35 : p47 -> p46.
Proof.
 intros h0.
 refine (fix_float_of_fix _ _ _ (-185) (-185) r21 h0 _) ; finalize.
Qed.
Lemma l38 : s1 -> p46 (* FIX(p2, -185) *).
Proof.
 intros h0.
 assert (h1 := l39 h0).
 apply t35. exact h1.
Qed.
Lemma t36 : p33 -> p46 -> p45.
Proof.
 intros h0 h1.
 refine (mul_fix _uh _p2 (-172) (-185) (-357) h0 h1 _) ; finalize.
Qed.
Lemma l37 : s1 -> p45 (* FIX(uh * p2, -357) *).
Proof.
 intros h0.
 assert (h1 := l28 h0).
 assert (h2 := l38 h0).
 apply t36. exact h1. exact h2.
Qed.
Lemma t37 : p45 -> p44.
Proof.
 intros h0.
 refine (fix_float_of_fix _ _ _ (-357) (-357) r19 h0 _) ; finalize.
Qed.
Lemma l36 : s1 -> p44 (* FIX(float<53,-1074,ne>(uh * p2), -357) *).
Proof.
 intros h0.
 assert (h1 := l37 h0).
 apply t37. exact h1.
Qed.
Lemma t38 : p42 -> p44 -> p41.
Proof.
 intros h0 h1.
 refine (add_fix _s0 r18 (-55) (-357) (-357) h0 h1 _) ; finalize.
Qed.
Lemma l33 : s1 -> p41 (* FIX(s0 + float<53,-1074,ne>(uh * p2), -357) *).
Proof.
 intros h0.
 assert (h1 := l34 h0).
 assert (h2 := l36 h0).
 apply t38. exact h1. exact h2.
Qed.
Lemma t39 : p41 -> p40.
Proof.
 intros h0.
 refine (fix_float_of_fix _ _ _ (-357) (-357) r17 h0 _) ; finalize.
Qed.
Lemma l32 : s1 -> p40 (* FIX(ps, -357) *).
Proof.
 intros h0.
 assert (h1 := l33 h0).
 apply t39. exact h1.
Qed.
Lemma t40 : p29 -> p40 -> p28.
Proof.
 intros h0 h1.
 refine (mul_fix _a3 _ps (-284) (-357) (-641) h0 h1 _) ; finalize.
Qed.
Lemma l23 : s1 -> p28 (* FIX(a3 * ps, -641) *).
Proof.
 intros h0.
 assert (h1 := l24 h0).
 assert (h2 := l32 h0).
 apply t40. exact h1. exact h2.
Qed.
Lemma t41 : p28 -> p27.
Proof.
 intros h0.
 refine (rel_of_fix_float_ne _ _ (-641) r27 i20 h0 _) ; finalize.
Qed.
Lemma l22 : s1 -> p27 (* REL(tail, a3 * ps, [-1.11022e-16, 1.11022e-16]) *).
Proof.
 intros h0.
 assert (h1 := l23 h0).
 apply t41. exact h1.
Qed.
Definition f37 := Float2 (-887651966482060884875133310692145509738027634003977953810692382740205291138329918738517513180253302928668887222541052417) (-450).
Definition f38 := Float2 (887651966482061064056565054306272399046251343389715778736088685613921878654735144315588922860336453431463878724636998633) (-450).
Definition i29 := makepairF f37 f38.
Notation p57 := (REL r27 _T i29). (* REL(a3 * ps, T, [-3.05313e-16, 3.05313e-16]) *)
Definition f39 := Float2 (-18014398509481983) (-106).
Definition f40 := Float2 (18014398509481985) (-106).
Definition i30 := makepairF f39 f40.
Notation p58 := (REL _a3 r2 i30). (* REL(a3, th * th * th, [-2.22045e-16, 2.22045e-16]) *)
Notation p59 := (BND r33 i30). (* BND((a3 - th * th * th) / (th * th * th), [-2.22045e-16, 2.22045e-16]) *)
Notation p60 := (BND r41 i30). (* BND((1 + (uh - th * th) / (th * th)) * (1 + (a3 - th * uh) / (th * uh)) - 1, [-2.22045e-16, 2.22045e-16]) *)
Definition f41 := Float2 (81129638414606663681390495662081) (-106).
Definition f42 := Float2 (81129638414606699710187514626049) (-106).
Definition i31 := makepairF f41 f42.
Notation p61 := (BND r42 i31). (* BND((1 + (uh - th * th) / (th * th)) * (1 + (a3 - th * uh) / (th * uh)), [1, 1]) *)
Definition f43 := Float2 (9007199254740991) (-53).
Definition f44 := Float2 (9007199254740993) (-53).
Definition i32 := makepairF f43 f44.
Notation p62 := (BND r43 i32). (* BND(1 + (uh - th * th) / (th * th), [1, 1]) *)
Definition i33 := makepairF f8 f8.
Notation p63 := (BND r32 i33). (* BND(1, [1, 1]) *)
Lemma t42 : p63.
Proof.
 refine (constant1 _ i33 _) ; finalize.
Qed.
Lemma l53 : s1 -> p63 (* BND(1, [1, 1]) *).
Proof.
 intros h0.
 apply t42.
Qed.
Notation p64 := (BND r44 i20). (* BND((uh - th * th) / (th * th), [-1.11022e-16, 1.11022e-16]) *)
Notation p65 := (REL _uh r3 i20). (* REL(uh, th * th, [-1.11022e-16, 1.11022e-16]) *)
Notation p66 := (FIX r3 (-224)). (* FIX(th * th, -224) *)
Lemma t43 : p31 -> p31 -> p66.
Proof.
 intros h0 h1.
 refine (mul_fix _th _th (-112) (-112) (-224) h0 h1 _) ; finalize.
Qed.
Lemma l56 : s1 -> p66 (* FIX(th * th, -224) *).
Proof.
 intros h0.
 assert (h1 := l26 h0).
 apply t43. exact h1. exact h1.
Qed.
Lemma t44 : p66 -> p65.
Proof.
 intros h0.
 refine (rel_of_fix_float_ne _ _ (-224) r3 i20 h0 _) ; finalize.
Qed.
Lemma l55 : s1 -> p65 (* REL(uh, th * th, [-1.11022e-16, 1.11022e-16]) *).
Proof.
 intros h0.
 assert (h1 := l56 h0).
 apply t44. exact h1.
Qed.
Lemma t45 : p6 -> p65 -> p64.
Proof.
 intros h0 h1.
 refine (bnd_of_nzr_rel _uh r3 i20 h0 h1) ; finalize.
Qed.
Lemma l54 : s1 -> p64 (* BND((uh - th * th) / (th * th), [-1.11022e-16, 1.11022e-16]) *).
Proof.
 intros h0.
 assert (h1 := l6 h0).
 assert (h2 := l55 h0).
 apply t45. exact h1. exact h2.
Qed.
Lemma t46 : p63 -> p64 -> p62.
Proof.
 intros h0 h1.
 refine (add r32 r44 i33 i20 i32 h0 h1 _) ; finalize.
Qed.
Lemma l52 : s1 -> p62 (* BND(1 + (uh - th * th) / (th * th), [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l53 h0).
 assert (h2 := l54 h0).
 apply t46. exact h1. exact h2.
Qed.
Notation p67 := (BND r46 i32). (* BND(1 + (a3 - th * uh) / (th * uh), [1, 1]) *)
Notation p68 := (BND r47 i20). (* BND((a3 - th * uh) / (th * uh), [-1.11022e-16, 1.11022e-16]) *)
Notation p69 := (NZR r14). (* NZR(th * uh) *)
Notation p70 := (NZR _uh). (* NZR(uh) *)
Definition f45 := Float2 (-1) (-1).
Definition i34 := makepairF f45 f8.
Notation p71 := (REL _uh r3 i34). (* REL(uh, th * th, [-0.5, 1]) *)
Lemma t47 : p6 -> p71 -> p70.
Proof.
 intros h0 h1.
 refine (nzr_of_nzr_rel _uh r3 i34 h0 h1 _) ; finalize.
Qed.
Lemma l60 : s1 -> p70 (* NZR(uh) *).
Proof.
 intros h0.
 assert (h1 := l6 h0).
 assert (h2 := l55 h0).
 apply t47. exact h1. refine (rel_subset _uh r3 i20 i34 h2 _) ; finalize.
Qed.
Lemma t48 : p11 -> p70 -> p69.
Proof.
 intros h0 h1.
 refine (mul_nzr _th _uh h0 h1) ; finalize.
Qed.
Lemma l59 : s1 -> p69 (* NZR(th * uh) *).
Proof.
 intros h0.
 assert (h1 := l10 h0).
 assert (h2 := l60 h0).
 apply t48. exact h1. exact h2.
Qed.
Notation p72 := (REL _a3 r14 i20). (* REL(a3, th * uh, [-1.11022e-16, 1.11022e-16]) *)
Notation p73 := (FIX r14 (-336)). (* FIX(th * uh, -336) *)
Notation p74 := (FIX _uh (-224)). (* FIX(uh, -224) *)
Lemma t49 : p66 -> p74.
Proof.
 intros h0.
 refine (fix_float_of_fix _ _ _ (-224) (-224) r3 h0 _) ; finalize.
Qed.
Lemma l63 : s1 -> p74 (* FIX(uh, -224) *).
Proof.
 intros h0.
 assert (h1 := l56 h0).
 apply t49. exact h1.
Qed.
Lemma t50 : p31 -> p74 -> p73.
Proof.
 intros h0 h1.
 refine (mul_fix _th _uh (-112) (-224) (-336) h0 h1 _) ; finalize.
Qed.
Lemma l62 : s1 -> p73 (* FIX(th * uh, -336) *).
Proof.
 intros h0.
 assert (h1 := l26 h0).
 assert (h2 := l63 h0).
 apply t50. exact h1. exact h2.
Qed.
Lemma t51 : p73 -> p72.
Proof.
 intros h0.
 refine (rel_of_fix_float_ne _ _ (-336) r14 i20 h0 _) ; finalize.
Qed.
Lemma l61 : s1 -> p72 (* REL(a3, th * uh, [-1.11022e-16, 1.11022e-16]) *).
Proof.
 intros h0.
 assert (h1 := l62 h0).
 apply t51. exact h1.
Qed.
Lemma t52 : p69 -> p72 -> p68.
Proof.
 intros h0 h1.
 refine (bnd_of_nzr_rel _a3 r14 i20 h0 h1) ; finalize.
Qed.
Lemma l58 : s1 -> p68 (* BND((a3 - th * uh) / (th * uh), [-1.11022e-16, 1.11022e-16]) *).
Proof.
 intros h0.
 assert (h1 := l59 h0).
 assert (h2 := l61 h0).
 apply t52. exact h1. exact h2.
Qed.
Lemma t53 : p63 -> p68 -> p67.
Proof.
 intros h0 h1.
 refine (add r32 r47 i33 i20 i32 h0 h1 _) ; finalize.
Qed.
Lemma l57 : s1 -> p67 (* BND(1 + (a3 - th * uh) / (th * uh), [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l53 h0).
 assert (h2 := l58 h0).
 apply t53. exact h1. exact h2.
Qed.
Lemma t54 : p62 -> p67 -> p61.
Proof.
 intros h0 h1.
 refine (mul_pp r43 r46 i32 i32 i31 h0 h1 _) ; finalize.
Qed.
Lemma l51 : s1 -> p61 (* BND((1 + (uh - th * th) / (th * th)) * (1 + (a3 - th * uh) / (th * uh)), [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l52 h0).
 assert (h2 := l57 h0).
 apply t54. exact h1. exact h2.
Qed.
Lemma t55 : p61 -> p63 -> p60.
Proof.
 intros h0 h1.
 refine (sub r42 r32 i31 i33 i30 h0 h1 _) ; finalize.
Qed.
Lemma l50 : s1 -> p60 (* BND((1 + (uh - th * th) / (th * th)) * (1 + (a3 - th * uh) / (th * uh)) - 1, [-2.22045e-16, 2.22045e-16]) *).
Proof.
 intros h0.
 assert (h1 := l51 h0).
 assert (h2 := l53 h0).
 apply t55. exact h1. exact h2.
Qed.
Definition f46 := Float2 (0) (0).
Definition i35 := makepairF f46 f46.
Notation p75 := (REL r33 r41 i35). (* REL((a3 - th * th * th) / (th * th * th), (1 + (uh - th * th) / (th * th)) * (1 + (a3 - th * uh) / (th * uh)) - 1, [0, 0]) *)
Notation p76 := (r33 = r41). (* EQL((a3 - th * th * th) / (th * th * th), (1 + (uh - th * th) / (th * th)) * (1 + (a3 - th * uh) / (th * uh)) - 1) *)
Lemma t56 : p11 -> p70 -> p76.
Proof.
 intros h0 h1.
 refine (b2 h0 h1) ; finalize.
Qed.
Lemma l65 : s1 -> p76 (* EQL((a3 - th * th * th) / (th * th * th), (1 + (uh - th * th) / (th * th)) * (1 + (a3 - th * uh) / (th * uh)) - 1) *).
Proof.
 intros h0.
 assert (h1 := l10 h0).
 assert (h2 := l60 h0).
 apply t56. exact h1. exact h2.
Qed.
Notation p77 := (REL r41 r41 i35). (* REL((1 + (uh - th * th) / (th * th)) * (1 + (a3 - th * uh) / (th * uh)) - 1, (1 + (uh - th * th) / (th * th)) * (1 + (a3 - th * uh) / (th * uh)) - 1, [0, 0]) *)
Lemma t57 : p77.
Proof.
 refine (rel_refl r41 i35 _) ; finalize.
Qed.
Lemma l66 : s1 -> p77 (* REL((1 + (uh - th * th) / (th * th)) * (1 + (a3 - th * uh) / (th * uh)) - 1, (1 + (uh - th * th) / (th * th)) * (1 + (a3 - th * uh) / (th * uh)) - 1, [0, 0]) *).
Proof.
 intros h0.
 apply t57.
Qed.
Lemma t58 : p76 -> p77 -> p75.
Proof.
 intros h0 h1.
 refine (rel_rewrite_1 r33 r41 r41 i35 h0 h1) ; finalize.
Qed.
Lemma l64 : s1 -> p75 (* REL((a3 - th * th * th) / (th * th * th), (1 + (uh - th * th) / (th * th)) * (1 + (a3 - th * uh) / (th * uh)) - 1, [0, 0]) *).
Proof.
 intros h0.
 assert (h1 := l65 h0).
 assert (h2 := l66 h0).
 apply t58. exact h1. exact h2.
Qed.
Lemma t59 : p60 -> p75 -> p59.
Proof.
 intros h0 h1.
 refine (bnd_of_bnd_rel_o r33 r41 i30 i35 i30 h0 h1 _) ; finalize.
Qed.
Lemma l49 : s1 -> p59 (* BND((a3 - th * th * th) / (th * th * th), [-2.22045e-16, 2.22045e-16]) *).
Proof.
 intros h0.
 assert (h1 := l50 h0).
 assert (h2 := l64 h0).
 apply t59. exact h1. exact h2.
Qed.
Lemma t60 : p5 -> p59 -> p58.
Proof.
 intros h0 h1.
 refine (rel_of_nzr_bnd _a3 r2 i30 h0 h1) ; finalize.
Qed.
Lemma l48 : s1 -> p58 (* REL(a3, th * th * th, [-2.22045e-16, 2.22045e-16]) *).
Proof.
 intros h0.
 assert (h1 := l5 h0).
 assert (h2 := l49 h0).
 apply t60. exact h1. exact h2.
Qed.
Definition f47 := Float2 (-484178993920667654103472203186298616778908865113480179939663006512289344083043365272819527461546189885354151447973432141) (-451).
Definition f48 := Float2 (242089496960333827052002677403756695203913783238182689688952276779949894883569609143278624714789269319319044465064657661) (-450).
Definition i36 := makepairF f47 f48.
Notation p78 := (REL _ps _P i36). (* REL(ps, P, [-8.3268e-17, 8.3268e-17]) *)
Definition f49 := Float2 (-484173329758863258356693988183925993017847576236158439694005836209453573001165045084171808867526891277265364254482042719) (-451).
Definition f50 := Float2 (968346659517726516713387976367851986035695152472316879388011672418907146002330090168343617735053782554530728508964085437) (-452).
Definition i37 := makepairF f49 f50.
Notation p79 := (REL _ps r17 i37). (* REL(ps, s0 + float<53,-1074,ne>(uh * p2), [-8.3267e-17, 8.3267e-17]) *)
Notation p80 := (NZR r17). (* NZR(s0 + float<53,-1074,ne>(uh * p2)) *)
Definition f51 := Float2 (-11328323608791494499705311033106141104256855103001730003887405310628370228685553004206914022484266970257536663211437) (-452).
Definition f52 := Float2 (22656647217582987358915881773872458555647071457883186093658699937445426259685962466056173793836383638811907643361497) (-453).
Definition i38 := makepairF f51 f52.
Notation p81 := (REL r17 _P i38). (* REL(s0 + float<53,-1074,ne>(uh * p2), P, [-9.74109e-22, 9.74109e-22]) *)
Notation r51 := ((r17 - _P)%R).
Notation r50 := ((r51 / _P)%R).
Notation p82 := (BND r50 i38). (* BND((s0 + float<53,-1074,ne>(uh * p2) - P) / P, [-9.74109e-22, 9.74109e-22]) *)
Definition f53 := Float2 (-3776096345535462993633269519880118537351059768298917126900378769887652394127531043972234877836436193113527716951259) (-453).
Definition f54 := Float2 (7552192691070926534096450296938762210943093017623860335884131906285426034921018963538090541900506924102125221871731) (-454).
Definition i39 := makepairF f53 f54.
Notation p83 := (BND r51 i39). (* BND(s0 + float<53,-1074,ne>(uh * p2) - P, [-1.62351e-22, 1.62351e-22]) *)
Notation r52 := ((r18 - r8)%R).
Notation p84 := (BND r52 i39). (* BND(float<53,-1074,ne>(uh * p2) - th * th * (s1 + th * th * s2), [-1.62351e-22, 1.62351e-22]) *)
Notation r54 := ((r18 - r19)%R).
Notation r55 := ((r19 - r8)%R).
Notation r53 := ((r54 + r55)%R).
Notation p85 := (BND r53 i39). (* BND(float<53,-1074,ne>(uh * p2) - uh * p2 + (uh * p2 - th * th * (s1 + th * th * s2)), [-1.62351e-22, 1.62351e-22]) *)
Definition f55 := Float2 (-1) (-74).
Definition f56 := Float2 (1) (-74).
Definition i40 := makepairF f55 f56.
Notation p86 := (BND r54 i40). (* BND(float<53,-1074,ne>(uh * p2) - uh * p2, [-5.29396e-23, 5.29396e-23]) *)
Definition f57 := Float2 (1) (-20).
Definition i41 := makepairF f13 f57.
Notation p87 := (ABS r19 i41). (* ABS(uh * p2, [5.87747e-39, 9.53674e-07]) *)
Definition f58 := Float2 (5) (-9).
Definition i42 := makepairF f23 f58.
Notation p88 := (ABS _p2 i42). (* ABS(p2, [0.0078125, 0.00976562]) *)
Definition i43 := makepairF f23 f18.
Notation p89 := (BND _p2 i43). (* BND(p2, [0.0078125, 0.00833333]) *)
Definition f59 := Float2 (5037183594669694980021) (-79).
Definition i44 := makepairF f59 f18.
Notation p90 := (BND r21 i44). (* BND(s1 + float<53,-1074,ne>(uh * s2), [0.00833332, 0.00833333]) *)
Lemma t61 : p19 -> p53 -> p90.
Proof.
 intros h0 h1.
 refine (add _s1 r22 i13 i26 i44 h0 h1 _) ; finalize.
Qed.
Lemma l79 : s1 -> p90 (* BND(s1 + float<53,-1074,ne>(uh * s2), [0.00833332, 0.00833333]) *).
Proof.
 intros h0.
 assert (h1 := l18 h0).
 assert (h2 := l45 h0).
 apply t61. exact h1. exact h2.
Qed.
Notation p91 := (BND r21 i43). (* BND(s1 + float<53,-1074,ne>(uh * s2), [0.0078125, 0.00833333]) *)
Lemma t62 : p91 -> p89.
Proof.
 intros h0.
 refine (float_round_ne _ _ r21 i43 i43 h0 _) ; finalize.
Qed.
Lemma l78 : s1 -> p89 (* BND(p2, [0.0078125, 0.00833333]) *).
Proof.
 intros h0.
 assert (h1 := l79 h0).
 apply t62. refine (subset r21 i44 i43 h1 _) ; finalize.
Qed.
Notation p92 := (BND _p2 i42). (* BND(p2, [0.0078125, 0.00976562]) *)
Lemma t63 : p92 -> p88.
Proof.
 intros h0.
 refine (abs_of_bnd_p _p2 i42 i42 h0 _) ; finalize.
Qed.
Lemma l77 : s1 -> p88 (* ABS(p2, [0.0078125, 0.00976562]) *).
Proof.
 intros h0.
 assert (h1 := l78 h0).
 apply t63. refine (subset _p2 i43 i42 h1 _) ; finalize.
Qed.
Lemma t64 : p35 -> p88 -> p87.
Proof.
 intros h0 h1.
 refine (mul_aa _uh _p2 i21 i42 i41 h0 h1 _) ; finalize.
Qed.
Lemma l76 : s1 -> p87 (* ABS(uh * p2, [5.87747e-39, 9.53674e-07]) *).
Proof.
 intros h0.
 assert (h1 := l30 h0).
 assert (h2 := l77 h0).
 apply t64. exact h1. exact h2.
Qed.
Lemma t65 : p87 -> p86.
Proof.
 intros h0.
 refine (float_absolute_wide_ne _ _ r19 i41 i40 h0 _) ; finalize.
Qed.
Lemma l75 : s1 -> p86 (* BND(float<53,-1074,ne>(uh * p2) - uh * p2, [-5.29396e-23, 5.29396e-23]) *).
Proof.
 intros h0.
 assert (h1 := l76 h0).
 apply t65. exact h1.
Qed.
Definition f60 := Float2 (-2544783651898135518249549516750630605942317916096871918526994601004973588768243212365539057371282579338320592254171) (-453).
Definition f61 := Float2 (5089567303796271583329010290679786348125609313219769919137363568520068424202443300324698900970199696551710972477555) (-454).
Definition i45 := makepairF f60 f61.
Notation p93 := (BND r55 i45). (* BND(uh * p2 - th * th * (s1 + th * th * s2), [-1.09411e-22, 1.09411e-22]) *)
Definition f62 := Float2 (-625390020249343630876687714937778087797401864075371921214201598010496932473848431838639261683576202673976385142491709085) (-450).
Definition f63 := Float2 (78173752531167962258678383751081480369351438366408817705472516294645174517443068119232307142322486685335041471544064019) (-447).
Definition i46 := makepairF f62 f63.
Notation p94 := (REL r19 r8 i46). (* REL(uh * p2, th * th * (s1 + th * th * s2), [-2.15106e-16, 2.15106e-16]) *)
Definition f64 := Float2 (-605217570976960181532043857507912201376863313768228506784593864385303377751783718197097878033918800095074159622931742309) (-451).
Definition f65 := Float2 (605217570976960181532226126383441722942474621601903501166125731150479587872683800744830453903256338146288429022654603529) (-451).
Definition i47 := makepairF f64 f65.
Notation p95 := (REL _p2 r9 i47). (* REL(p2, s1 + th * th * s2, [-1.04084e-16, 1.04084e-16]) *)
Definition f66 := Float2 (-605215694717569043777107364395559289531339509987383938485154696892368247666207359403732091036468949657716974808331163429) (-451).
Definition f67 := Float2 (605215694717569043777107364395559289531339509987383938485154696892368247666207359403732091036468949657716974808331163429) (-451).
Definition i48 := makepairF f66 f67.
Notation p96 := (REL _p2 r21 i48). (* REL(p2, s1 + float<53,-1074,ne>(uh * s2), [-1.04084e-16, 1.04084e-16]) *)
Notation p97 := (NZR r21). (* NZR(s1 + float<53,-1074,ne>(uh * s2)) *)
Notation p98 := (NZR r9). (* NZR(s1 + th * th * s2) *)
Definition i49 := makepairF f23 f8.
Notation p99 := (ABS r9 i49). (* ABS(s1 + th * th * s2, [0.0078125, 1]) *)
Notation p100 := (BND r9 i49). (* BND(s1 + th * th * s2, [0.0078125, 1]) *)
Lemma t66 : p100 -> p99.
Proof.
 intros h0.
 refine (abs_of_bnd_p r9 i49 i49 h0 _) ; finalize.
Qed.
Lemma l86 : s1 -> p99 (* ABS(s1 + th * th * s2, [0.0078125, 1]) *).
Proof.
 intros h0.
 assert (h1 := l17 h0).
 apply t66. refine (subset r9 i12 i49 h1 _) ; finalize.
Qed.
Lemma t67 : p99 -> p98.
Proof.
 intros h0.
 refine (nzr_of_abs r9 i49 h0 _) ; finalize.
Qed.
Lemma l85 : s1 -> p98 (* NZR(s1 + th * th * s2) *).
Proof.
 intros h0.
 assert (h1 := l86 h0).
 apply t67. exact h1.
Qed.
Definition f68 := Float2 (-3752518782275510263561737856376580064700846033808490060385645731601316871103864815217588916321272167953892095036301) (-452).
Definition f69 := Float2 (7505037564551019693896925228627953231445400294788585680745892248260430339330349190991962104436838162385249844374599) (-453).
Definition i50 := makepairF f68 f69.
Notation p101 := (REL r21 r9 i50). (* REL(s1 + float<53,-1074,ne>(uh * s2), s1 + th * th * s2, [-3.22675e-22, 3.22675e-22]) *)
Notation p102 := (REL _s1 _s1 i35). (* REL(s1, s1, [0, 0]) *)
Lemma t68 : p102.
Proof.
 refine (rel_refl _s1 i35 _) ; finalize.
Qed.
Lemma l88 : s1 -> p102 (* REL(s1, s1, [0, 0]) *).
Proof.
 intros h0.
 apply t68.
Qed.
Notation p103 := (REL r22 r11 i30). (* REL(float<53,-1074,ne>(uh * s2), th * th * s2, [-2.22045e-16, 2.22045e-16]) *)
Notation p104 := (REL r22 r23 i20). (* REL(float<53,-1074,ne>(uh * s2), uh * s2, [-1.11022e-16, 1.11022e-16]) *)
Notation p105 := (FIX r23 (-288)). (* FIX(uh * s2, -288) *)
Notation p106 := (FIX _s2 (-64)). (* FIX(s2, -64) *)
Definition f70 := Float2 (3659917331012787) (-64).
Definition i51 := makepairF f70 f70.
Notation p107 := (ABS _s2 i51). (* ABS(s2, [0.000198405, 0.000198405]) *)
Lemma t69 : p21 -> p107.
Proof.
 intros h0.
 refine (abs_of_bnd_n _s2 i15 i51 h0 _) ; finalize.
Qed.
Lemma l93 : s1 -> p107 (* ABS(s2, [0.000198405, 0.000198405]) *).
Proof.
 intros h0.
 assert (h1 := l20 h0).
 apply t69. exact h1.
Qed.
Lemma t70 : p107 -> p106.
Proof.
 intros h0.
 refine (fix_of_singleton_bnd _s2 i51 (-64) h0 _) ; finalize.
Qed.
Lemma l92 : s1 -> p106 (* FIX(s2, -64) *).
Proof.
 intros h0.
 assert (h1 := l93 h0).
 apply t70. exact h1.
Qed.
Lemma t71 : p74 -> p106 -> p105.
Proof.
 intros h0 h1.
 refine (mul_fix _uh _s2 (-224) (-64) (-288) h0 h1 _) ; finalize.
Qed.
Lemma l91 : s1 -> p105 (* FIX(uh * s2, -288) *).
Proof.
 intros h0.
 assert (h1 := l63 h0).
 assert (h2 := l92 h0).
 apply t71. exact h1. exact h2.
Qed.
Lemma t72 : p105 -> p104.
Proof.
 intros h0.
 refine (rel_of_fix_float_ne _ _ (-288) r23 i20 h0 _) ; finalize.
Qed.
Lemma l90 : s1 -> p104 (* REL(float<53,-1074,ne>(uh * s2), uh * s2, [-1.11022e-16, 1.11022e-16]) *).
Proof.
 intros h0.
 assert (h1 := l91 h0).
 apply t72. exact h1.
Qed.
Notation p108 := (REL r23 r11 i20). (* REL(uh * s2, th * th * s2, [-1.11022e-16, 1.11022e-16]) *)
Lemma t73 : p65 -> p108.
Proof.
 intros h0.
 refine (mul_firq _uh _ r3 i20 h0) ; finalize.
Qed.
Lemma l94 : s1 -> p108 (* REL(uh * s2, th * th * s2, [-1.11022e-16, 1.11022e-16]) *).
Proof.
 intros h0.
 assert (h1 := l55 h0).
 apply t73. exact h1.
Qed.
Lemma t74 : p104 -> p108 -> p103.
Proof.
 intros h0 h1.
 refine (compose r22 r23 r11 i20 i20 i30 h0 h1 _) ; finalize.
Qed.
Lemma l89 : s1 -> p103 (* REL(float<53,-1074,ne>(uh * s2), th * th * s2, [-2.22045e-16, 2.22045e-16]) *).
Proof.
 intros h0.
 assert (h1 := l90 h0).
 assert (h2 := l94 h0).
 apply t74. exact h1. exact h2.
Qed.
Notation r56 := ((_s1 / r9)%R).
Definition f71 := Float2 (322781703825711358145746803387905902451005750575289264277763716979571935972857697393668838758140262660190968153907013147) (-397).
Definition i52 := makepairF f8 f71.
Notation p109 := (BND r56 i52). (* BND(s1 / (s1 + th * th * s2), [1, 1]) *)
Definition i53 := makepairF f16 f18.
Notation p110 := (BND r9 i53). (* BND(s1 + th * th * s2, [0.00833332, 0.00833333]) *)
Lemma t75 : p19 -> p110 -> p109.
Proof.
 intros h0 h1.
 refine (div_pp _s1 r9 i13 i53 i52 h0 h1 _) ; finalize.
Qed.
Lemma l95 : s1 -> p109 (* BND(s1 / (s1 + th * th * s2), [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l18 h0).
 assert (h2 := l17 h0).
 apply t75. exact h1. refine (subset r9 i12 i53 h2 _) ; finalize.
Qed.
Lemma t76 : p102 -> p103 -> p109 -> p98 -> p101.
Proof.
 intros h0 h1 h2 h3.
 refine (add_rr _s1 _s1 r22 r11 i35 i30 i52 i50 h0 h1 h2 h3 _) ; finalize.
Qed.
Lemma l87 : s1 -> p101 (* REL(s1 + float<53,-1074,ne>(uh * s2), s1 + th * th * s2, [-3.22675e-22, 3.22675e-22]) *).
Proof.
 intros h0.
 assert (h1 := l88 h0).
 assert (h2 := l89 h0).
 assert (h3 := l95 h0).
 assert (h4 := l85 h0).
 apply t76. exact h1. exact h2. exact h3. exact h4.
Qed.
Notation p111 := (REL r21 r9 i34). (* REL(s1 + float<53,-1074,ne>(uh * s2), s1 + th * th * s2, [-0.5, 1]) *)
Lemma t77 : p98 -> p111 -> p97.
Proof.
 intros h0 h1.
 refine (nzr_of_nzr_rel r21 r9 i34 h0 h1 _) ; finalize.
Qed.
Lemma l84 : s1 -> p97 (* NZR(s1 + float<53,-1074,ne>(uh * s2)) *).
Proof.
 intros h0.
 assert (h1 := l85 h0).
 assert (h2 := l87 h0).
 apply t77. exact h1. refine (rel_subset r21 r9 i50 i34 h2 _) ; finalize.
Qed.
Notation r58 := ((_p2 - r21)%R).
Notation r57 := ((r58 / r21)%R).
Notation p112 := (BND r57 i48). (* BND((p2 - (s1 + float<53,-1074,ne>(uh * s2))) / (s1 + float<53,-1074,ne>(uh * s2)), [-1.04084e-16, 1.04084e-16]) *)
Definition f72 := Float2 (-1) (-60).
Definition i54 := makepairF f72 f1.
Notation p113 := (BND r58 i54). (* BND(p2 - (s1 + float<53,-1074,ne>(uh * s2)), [-8.67362e-19, 8.67362e-19]) *)
Definition f73 := Float2 (1) (-6).
Definition i55 := makepairF f23 f73.
Notation p114 := (ABS r21 i55). (* ABS(s1 + float<53,-1074,ne>(uh * s2), [0.0078125, 0.015625]) *)
Notation p115 := (BND r21 i55). (* BND(s1 + float<53,-1074,ne>(uh * s2), [0.0078125, 0.015625]) *)
Lemma t78 : p115 -> p114.
Proof.
 intros h0.
 refine (abs_of_bnd_p r21 i55 i55 h0 _) ; finalize.
Qed.
Lemma l98 : s1 -> p114 (* ABS(s1 + float<53,-1074,ne>(uh * s2), [0.0078125, 0.015625]) *).
Proof.
 intros h0.
 assert (h1 := l79 h0).
 apply t78. refine (subset r21 i44 i55 h1 _) ; finalize.
Qed.
Lemma t79 : p114 -> p113.
Proof.
 intros h0.
 refine (float_absolute_wide_ne _ _ r21 i55 i54 h0 _) ; finalize.
Qed.
Lemma l97 : s1 -> p113 (* BND(p2 - (s1 + float<53,-1074,ne>(uh * s2)), [-8.67362e-19, 8.67362e-19]) *).
Proof.
 intros h0.
 assert (h1 := l98 h0).
 apply t79. exact h1.
Qed.
Definition i56 := makepairF f59 f8.
Notation p116 := (BND r21 i56). (* BND(s1 + float<53,-1074,ne>(uh * s2), [0.00833332, 1]) *)
Lemma t80 : p113 -> p116 -> p112.
Proof.
 intros h0 h1.
 refine (div_op r58 r21 i54 i56 i48 h0 h1 _) ; finalize.
Qed.
Lemma l96 : s1 -> p112 (* BND((p2 - (s1 + float<53,-1074,ne>(uh * s2))) / (s1 + float<53,-1074,ne>(uh * s2)), [-1.04084e-16, 1.04084e-16]) *).
Proof.
 intros h0.
 assert (h1 := l97 h0).
 assert (h2 := l79 h0).
 apply t80. exact h1. refine (subset r21 i44 i56 h2 _) ; finalize.
Qed.
Lemma t81 : p97 -> p112 -> p96.
Proof.
 intros h0 h1.
 refine (rel_of_nzr_bnd _p2 r21 i48 h0 h1) ; finalize.
Qed.
Lemma l83 : s1 -> p96 (* REL(p2, s1 + float<53,-1074,ne>(uh * s2), [-1.04084e-16, 1.04084e-16]) *).
Proof.
 intros h0.
 assert (h1 := l84 h0).
 assert (h2 := l96 h0).
 apply t81. exact h1. exact h2.
Qed.
Lemma t82 : p96 -> p101 -> p95.
Proof.
 intros h0 h1.
 refine (compose _p2 r21 r9 i48 i50 i47 h0 h1 _) ; finalize.
Qed.
Lemma l82 : s1 -> p95 (* REL(p2, s1 + th * th * s2, [-1.04084e-16, 1.04084e-16]) *).
Proof.
 intros h0.
 assert (h1 := l83 h0).
 assert (h2 := l87 h0).
 apply t82. exact h1. exact h2.
Qed.
Lemma t83 : p65 -> p95 -> p94.
Proof.
 intros h0 h1.
 refine (mul_rr _uh r3 _p2 r9 i20 i47 i46 h0 h1 _) ; finalize.
Qed.
Lemma l81 : s1 -> p94 (* REL(uh * p2, th * th * (s1 + th * th * s2), [-2.15106e-16, 2.15106e-16]) *).
Proof.
 intros h0.
 assert (h1 := l55 h0).
 assert (h2 := l82 h0).
 apply t83. exact h1. exact h2.
Qed.
Definition f74 := Float2 (-2385673600194334529406309947730171538533790069867599186760717765848148088355439879755551382765106974311738529748885) (-432).
Definition f75 := Float2 (76341555206218713143240609131915508173194764029696111040500504193989428239690496210187799943674303403647501437054751) (-437).
Definition i57 := makepairF f74 f75.
Notation p117 := (REL r19 r8 i57). (* REL(uh * p2, th * th * (s1 + th * th * s2), [-2.15106e-16, 2.15106e-16]) *)
Lemma t84 : p117 -> p16 -> p93.
Proof.
 intros h0 h1.
 refine (error_of_rel_op r19 r8 i57 i10 i45 h0 h1 _) ; finalize.
Qed.
Lemma l80 : s1 -> p93 (* BND(uh * p2 - th * th * (s1 + th * th * s2), [-1.09411e-22, 1.09411e-22]) *).
Proof.
 intros h0.
 assert (h1 := l81 h0).
 assert (h2 := l15 h0).
 apply t84. refine (rel_subset r19 r8 i46 i57 h1 _) ; finalize. exact h2.
Qed.
Lemma t85 : p86 -> p93 -> p85.
Proof.
 intros h0 h1.
 refine (add r54 r55 i40 i45 i39 h0 h1 _) ; finalize.
Qed.
Lemma l74 : s1 -> p85 (* BND(float<53,-1074,ne>(uh * p2) - uh * p2 + (uh * p2 - th * th * (s1 + th * th * s2)), [-1.62351e-22, 1.62351e-22]) *).
Proof.
 intros h0.
 assert (h1 := l75 h0).
 assert (h2 := l80 h0).
 apply t85. exact h1. exact h2.
Qed.
Lemma t86 : p85 -> p84.
Proof.
 intros h0.
 refine (sub_xals _ _ _ i39 h0) ; finalize.
Qed.
Lemma l73 : s1 -> p84 (* BND(float<53,-1074,ne>(uh * p2) - th * th * (s1 + th * th * s2), [-1.62351e-22, 1.62351e-22]) *).
Proof.
 intros h0.
 assert (h1 := l74 h0).
 apply t86. exact h1.
Qed.
Lemma t87 : p84 -> p83.
Proof.
 intros h0.
 refine (add_fils _ _ _ i39 h0) ; finalize.
Qed.
Lemma l72 : s1 -> p83 (* BND(s0 + float<53,-1074,ne>(uh * p2) - P, [-1.62351e-22, 1.62351e-22]) *).
Proof.
 intros h0.
 assert (h1 := l73 h0).
 apply t87. exact h1.
Qed.
Definition f76 := Float2 (-26267923965290630922315144468719283447298790676492074026177475828246603530624406688092194296048878691878657354131143) (-386).
Definition i58 := makepairF f25 f76.
Notation p118 := (BND _P i58). (* BND(P, [-1, -0.166666]) *)
Lemma t88 : p83 -> p118 -> p82.
Proof.
 intros h0 h1.
 refine (div_on r51 _P i39 i58 i38 h0 h1 _) ; finalize.
Qed.
Lemma l71 : s1 -> p82 (* BND((s0 + float<53,-1074,ne>(uh * p2) - P) / P, [-9.74109e-22, 9.74109e-22]) *).
Proof.
 intros h0.
 assert (h1 := l72 h0).
 assert (h2 := l13 h0).
 apply t88. exact h1. refine (subset _P i8 i58 h2 _) ; finalize.
Qed.
Lemma t89 : p12 -> p82 -> p81.
Proof.
 intros h0 h1.
 refine (rel_of_nzr_bnd r17 _P i38 h0 h1) ; finalize.
Qed.
Lemma l70 : s1 -> p81 (* REL(s0 + float<53,-1074,ne>(uh * p2), P, [-9.74109e-22, 9.74109e-22]) *).
Proof.
 intros h0.
 assert (h1 := l11 h0).
 assert (h2 := l71 h0).
 apply t89. exact h1. exact h2.
Qed.
Notation p119 := (REL r17 _P i34). (* REL(s0 + float<53,-1074,ne>(uh * p2), P, [-0.5, 1]) *)
Lemma t90 : p12 -> p119 -> p80.
Proof.
 intros h0 h1.
 refine (nzr_of_nzr_rel r17 _P i34 h0 h1 _) ; finalize.
Qed.
Lemma l69 : s1 -> p80 (* NZR(s0 + float<53,-1074,ne>(uh * p2)) *).
Proof.
 intros h0.
 assert (h1 := l11 h0).
 assert (h2 := l70 h0).
 apply t90. exact h1. refine (rel_subset r17 _P i38 i34 h2 _) ; finalize.
Qed.
Notation r60 := ((_ps - r17)%R).
Notation r59 := ((r60 / r17)%R).
Notation p120 := (BND r59 i37). (* BND((ps - (s0 + float<53,-1074,ne>(uh * p2))) / (s0 + float<53,-1074,ne>(uh * p2)), [-8.3267e-17, 8.3267e-17]) *)
Definition f77 := Float2 (-1) (-56).
Definition f78 := Float2 (1) (-56).
Definition i59 := makepairF f77 f78.
Notation p121 := (BND r60 i59). (* BND(ps - (s0 + float<53,-1074,ne>(uh * p2)), [-1.38778e-17, 1.38778e-17]) *)
Definition f79 := Float2 (1) (-2).
Definition i60 := makepairF f10 f79.
Notation p122 := (ABS r17 i60). (* ABS(s0 + float<53,-1074,ne>(uh * p2), [0.125, 0.25]) *)
Definition f80 := Float2 (-1) (-2).
Definition f81 := Float2 (-393529339248491764971) (-71).
Definition i61 := makepairF f80 f81.
Notation p123 := (BND r17 i61). (* BND(s0 + float<53,-1074,ne>(uh * p2), [-0.25, -0.166666]) *)
Definition f82 := Float2 (1200990645314325) (-71).
Definition i62 := makepairF f13 f82.
Notation p124 := (BND r18 i62). (* BND(float<53,-1074,ne>(uh * p2), [5.87747e-39, 5.08639e-07]) *)
Definition f83 := Float2 (9607925162514601) (-74).
Definition i63 := makepairF f13 f83.
Notation p125 := (BND r19 i63). (* BND(uh * p2, [5.87747e-39, 5.08639e-07]) *)
Lemma t91 : p36 -> p89 -> p125.
Proof.
 intros h0 h1.
 refine (mul_pp _uh _p2 i22 i43 i63 h0 h1 _) ; finalize.
Qed.
Lemma l104 : s1 -> p125 (* BND(uh * p2, [5.87747e-39, 5.08639e-07]) *).
Proof.
 intros h0.
 assert (h1 := l31 h0).
 assert (h2 := l78 h0).
 apply t91. exact h1. exact h2.
Qed.
Lemma t92 : p125 -> p124.
Proof.
 intros h0.
 refine (float_round_ne _ _ r19 i63 i62 h0 _) ; finalize.
Qed.
Lemma l103 : s1 -> p124 (* BND(float<53,-1074,ne>(uh * p2), [5.87747e-39, 5.08639e-07]) *).
Proof.
 intros h0.
 assert (h1 := l104 h0).
 apply t92. exact h1.
Qed.
Definition i64 := makepairF f80 f11.
Notation p126 := (BND _s0 i64). (* BND(s0, [-0.25, -0.166667]) *)
Lemma t93 : p126 -> p124 -> p123.
Proof.
 intros h0 h1.
 refine (add _s0 r18 i64 i62 i61 h0 h1 _) ; finalize.
Qed.
Lemma l102 : s1 -> p123 (* BND(s0 + float<53,-1074,ne>(uh * p2), [-0.25, -0.166666]) *).
Proof.
 intros h0.
 assert (h1 := l14 h0).
 assert (h2 := l103 h0).
 apply t93. refine (subset _s0 i9 i64 h1 _) ; finalize. exact h2.
Qed.
Definition i65 := makepairF f80 f26.
Notation p127 := (BND r17 i65). (* BND(s0 + float<53,-1074,ne>(uh * p2), [-0.25, -0.125]) *)
Lemma t94 : p127 -> p122.
Proof.
 intros h0.
 refine (abs_of_bnd_n r17 i65 i60 h0 _) ; finalize.
Qed.
Lemma l101 : s1 -> p122 (* ABS(s0 + float<53,-1074,ne>(uh * p2), [0.125, 0.25]) *).
Proof.
 intros h0.
 assert (h1 := l102 h0).
 apply t94. refine (subset r17 i61 i65 h1 _) ; finalize.
Qed.
Lemma t95 : p122 -> p121.
Proof.
 intros h0.
 refine (float_absolute_wide_ne _ _ r17 i60 i59 h0 _) ; finalize.
Qed.
Lemma l100 : s1 -> p121 (* BND(ps - (s0 + float<53,-1074,ne>(uh * p2)), [-1.38778e-17, 1.38778e-17]) *).
Proof.
 intros h0.
 assert (h1 := l101 h0).
 apply t95. exact h1.
Qed.
Definition i66 := makepairF f25 f81.
Notation p128 := (BND r17 i66). (* BND(s0 + float<53,-1074,ne>(uh * p2), [-1, -0.166666]) *)
Lemma t96 : p121 -> p128 -> p120.
Proof.
 intros h0 h1.
 refine (div_on r60 r17 i59 i66 i37 h0 h1 _) ; finalize.
Qed.
Lemma l99 : s1 -> p120 (* BND((ps - (s0 + float<53,-1074,ne>(uh * p2))) / (s0 + float<53,-1074,ne>(uh * p2)), [-8.3267e-17, 8.3267e-17]) *).
Proof.
 intros h0.
 assert (h1 := l100 h0).
 assert (h2 := l102 h0).
 apply t96. exact h1. refine (subset r17 i61 i66 h2 _) ; finalize.
Qed.
Lemma t97 : p80 -> p120 -> p79.
Proof.
 intros h0 h1.
 refine (rel_of_nzr_bnd _ps r17 i37 h0 h1) ; finalize.
Qed.
Lemma l68 : s1 -> p79 (* REL(ps, s0 + float<53,-1074,ne>(uh * p2), [-8.3267e-17, 8.3267e-17]) *).
Proof.
 intros h0.
 assert (h1 := l69 h0).
 assert (h2 := l99 h0).
 apply t97. exact h1. exact h2.
Qed.
Lemma t98 : p79 -> p81 -> p78.
Proof.
 intros h0 h1.
 refine (compose _ps r17 _P i37 i38 i36 h0 h1 _) ; finalize.
Qed.
Lemma l67 : s1 -> p78 (* REL(ps, P, [-8.3268e-17, 8.3268e-17]) *).
Proof.
 intros h0.
 assert (h1 := l68 h0).
 assert (h2 := l70 h0).
 apply t98. exact h1. exact h2.
Qed.
Lemma t99 : p58 -> p78 -> p57.
Proof.
 intros h0 h1.
 refine (mul_rr _a3 r2 _ps _P i30 i36 i29 h0 h1 _) ; finalize.
Qed.
Lemma l47 : s1 -> p57 (* REL(a3 * ps, T, [-3.05313e-16, 3.05313e-16]) *).
Proof.
 intros h0.
 assert (h1 := l48 h0).
 assert (h2 := l67 h0).
 apply t99. exact h1. exact h2.
Qed.
Lemma t100 : p27 -> p57 -> p26.
Proof.
 intros h0 h1.
 refine (compose _tail r27 _T i20 i29 i3 h0 h1 _) ; finalize.
Qed.
Lemma l21 : s1 -> p26 (* REL(tail, T, [-4.16335e-16, 4.16335e-16]) *).
Proof.
 intros h0.
 assert (h1 := l22 h0).
 assert (h2 := l47 h0).
 apply t100. exact h1. exact h2.
Qed.
Lemma t101 : p4 -> p26 -> p3.
Proof.
 intros h0 h1.
 refine (bnd_of_nzr_rel _tail _T i3 h0 h1) ; finalize.
Qed.
Lemma l3 : s1 -> p3 (* BND((tail - T) / T, [-4.16335e-16, 4.16335e-16]) *).
Proof.
 intros h0.
 assert (h1 := l4 h0).
 assert (h2 := l21 h0).
 apply t101. exact h1. exact h2.
Qed.
Lemma l1 : s1 -> False.
Proof.
 intros h0.
 assert (h1 := l2 h0).
 assert (h2 := l3 h0).
 refine (simplify (Tatom false (Abnd 0%nat i2)) Tfalse (Abnd 0%nat i3) (List.cons r24 List.nil) h2 h1 _) ; finalize.
Qed.
End Generated_by_Gappa.
