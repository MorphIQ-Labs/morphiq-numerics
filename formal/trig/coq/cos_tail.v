Require Import Gappa.Gappa_library.
Section Generated_by_Gappa.
Variable _th_ : R.
Notation _th := ((rounding_float rndNE (53)%positive (-1074)%Z) _th_).
Notation r4 := ((_th * _th)%R).
Notation r3 := ((r4 * _th)%R).
Notation r2 := ((r3 * _th)%R).
Notation _c0 := (float2R (Float2 (6004799503160661) (-57))).
Notation _c1 := (float2R (Float2 (-6405119469336935) (-62))).
Notation _c2 := (float2R (Float2 (3659771605655355) (-67))).
Notation r12 := ((r4 * _c2)%R).
Notation r10 := ((_c1 + r12)%R).
Notation r9 := ((r4 * r10)%R).
Notation _P := ((_c0 + r9)%R).
Notation _T := ((r2 * _P)%R).
Notation _uh := ((rounding_float rndNE (53)%positive (-1074)%Z) r4).
Notation r15 := ((_uh * _uh)%R).
Notation _a4 := ((rounding_float rndNE (53)%positive (-1074)%Z) r15).
Notation r24 := ((_uh * _c2)%R).
Notation r23 := ((rounding_float rndNE (53)%positive (-1074)%Z) r24).
Notation r22 := ((_c1 + r23)%R).
Notation _p2 := ((rounding_float rndNE (53)%positive (-1074)%Z) r22).
Notation r20 := ((_uh * _p2)%R).
Notation r19 := ((rounding_float rndNE (53)%positive (-1074)%Z) r20).
Notation r18 := ((_c0 + r19)%R).
Notation _pc := ((rounding_float rndNE (53)%positive (-1074)%Z) r18).
Notation r28 := ((_a4 * _pc)%R).
Notation _tail := ((rounding_float rndNE (53)%positive (-1074)%Z) r28).
Notation r26 := ((_tail - _T)%R).
Notation r25 := ((r26 / _T)%R).
Notation r33 := (Float1 (1)).
Notation r35 := ((_a4 - r2)%R).
Notation r34 := ((r35 / r2)%R).
Notation r32 := ((r33 + r34)%R).
Notation r38 := ((_pc - _P)%R).
Notation r37 := ((r38 / _P)%R).
Notation r36 := ((r33 + r37)%R).
Notation r31 := ((r32 * r36)%R).
Notation r41 := ((_tail - r28)%R).
Notation r40 := ((r41 / r28)%R).
Notation r39 := ((r33 + r40)%R).
Notation r30 := ((r31 * r39)%R).
Notation r29 := ((r30 - r33)%R).
Hypothesis a1 : (_T <> 0)%R -> (_th <> 0)%R -> (_P <> 0)%R -> (_a4 <> 0)%R -> (_pc <> 0)%R -> r25 = r29.
Lemma b1 : NZR _T -> NZR _th -> NZR _P -> NZR _a4 -> NZR _pc -> r25 = r29.
 intros h0 h1 h2 h3 h4.
 apply a1.
 exact h0.
 exact h1.
 exact h2.
 exact h3.
 exact h4.
Qed.
Notation r47 := ((_uh - r4)%R).
Notation r46 := ((r47 / r4)%R).
Notation r45 := ((r33 + r46)%R).
Notation r44 := ((r45 * r45)%R).
Notation r50 := ((_a4 - r15)%R).
Notation r49 := ((r50 / r15)%R).
Notation r48 := ((r33 + r49)%R).
Notation r43 := ((r44 * r48)%R).
Notation r42 := ((r43 - r33)%R).
Hypothesis a2 : (_th <> 0)%R -> (_uh <> 0)%R -> r34 = r42.
Lemma b2 : NZR _th -> NZR _uh -> r34 = r42.
 intros h0 h1.
 apply a2.
 exact h0.
 exact h1.
Qed.
Notation r51 := ((Rabs _th)%R).
Definition f1 := Float2 (1) (-60).
Definition f2 := Float2 (80696341590167128190183336492762922277553037908230366465363237155637854447075094068654269148145619287504548485417148267) (-402).
Definition i1 := makepairF f1 f2.
Notation p1 := (BND r51 i1). (* BND(|th|, [8.67362e-19, 0.0078126]) *)
Definition f3 := Float2 (-1) (-50).
Definition f4 := Float2 (1) (-50).
Definition i2 := makepairF f3 f4.
Notation p2 := (BND r25 i2). (* BND((tail - T) / T, [-8.88178e-16, 8.88178e-16]) *)
Definition s2 := (not p2).
Definition s1 := (p1 /\ s2).
Lemma l2 : s1 -> s2.
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj2 h1).
Qed.
Definition f5 := Float2 (-383303234467798841491983082896210368584999208258406138353570115857779618831421516451704386412426101958073999601946145033) (-448).
Definition f6 := Float2 (1533212937871196011016419685971241019535804621628568665802225682472638638221788634515160782134459424256040246036581297553) (-450).
Definition i3 := makepairF f5 f6.
Notation p3 := (BND r25 i3). (* BND((tail - T) / T, [-5.27357e-16, 5.27357e-16]) *)
Notation p4 := (NZR _T). (* NZR(T) *)
Notation p5 := (NZR r2). (* NZR(th * th * th * th) *)
Notation p6 := (NZR r3). (* NZR(th * th * th) *)
Notation p7 := (NZR r4). (* NZR(th * th) *)
Notation p8 := (NZR _th). (* NZR(th) *)
Definition f7 := Float2 (630440168673180688985807316349710330293383108658049738010650290278420737867774172411361477719887650683629285042321471) (-395).
Definition i4 := makepairF f1 f7.
Notation p9 := (ABS _th i4). (* ABS(th, [8.67362e-19, 0.0078126]) *)
Lemma l10 : s1 -> p1 (* BND(|th|, [8.67362e-19, 0.0078126]) *).
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj1 h1).
Qed.
Notation p10 := (BND r51 i4). (* BND(|th|, [8.67362e-19, 0.0078126]) *)
Lemma t1 : p10 -> p9.
Proof.
 intros h0.
 refine (abs_of_uabs _th i4 h0 _) ; finalize.
Qed.
Lemma l9 : s1 -> p9 (* ABS(th, [8.67362e-19, 0.0078126]) *).
Proof.
 intros h0.
 assert (h1 := l10 h0).
 apply t1. refine (subset r51 i1 i4 h1 _) ; finalize.
Qed.
Definition f8 := Float2 (1) (0).
Definition i5 := makepairF f1 f8.
Notation p11 := (ABS _th i5). (* ABS(th, [8.67362e-19, 1]) *)
Lemma t2 : p11 -> p8.
Proof.
 intros h0.
 refine (nzr_of_abs _th i5 h0 _) ; finalize.
Qed.
Lemma l8 : s1 -> p8 (* NZR(th) *).
Proof.
 intros h0.
 assert (h1 := l9 h0).
 apply t2. refine (abs_subset _th i4 i5 h1 _) ; finalize.
Qed.
Lemma t3 : p8 -> p8 -> p7.
Proof.
 intros h0 h1.
 refine (mul_nzr _th _th h0 h1) ; finalize.
Qed.
Lemma l7 : s1 -> p7 (* NZR(th * th) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 apply t3. exact h1. exact h1.
Qed.
Lemma t4 : p7 -> p8 -> p6.
Proof.
 intros h0 h1.
 refine (mul_nzr r4 _th h0 h1) ; finalize.
Qed.
Lemma l6 : s1 -> p6 (* NZR(th * th * th) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 assert (h2 := l8 h0).
 apply t4. exact h1. exact h2.
Qed.
Lemma t5 : p6 -> p8 -> p5.
Proof.
 intros h0 h1.
 refine (mul_nzr r3 _th h0 h1) ; finalize.
Qed.
Lemma l5 : s1 -> p5 (* NZR(th * th * th * th) *).
Proof.
 intros h0.
 assert (h1 := l6 h0).
 assert (h2 := l8 h0).
 apply t5. exact h1. exact h2.
Qed.
Notation p12 := (NZR _P). (* NZR(P) *)
Definition f9 := Float2 (1) (-5).
Definition i6 := makepairF f9 f8.
Notation p13 := (ABS _P i6). (* ABS(P, [0.03125, 1]) *)
Definition f10 := Float2 (1721496416234393195703155335779062692589092384303358402358891111223159388918801703128367313834723441262909094340189346901) (-404).
Definition f11 := Float2 (6004799503160661) (-57).
Definition i7 := makepairF f10 f11.
Notation p14 := (BND _P i7). (* BND(P, [0.0416666, 0.0416667]) *)
Definition i8 := makepairF f11 f11.
Notation p15 := (BND _c0 i8). (* BND(c0, [0.0416667, 0.0416667]) *)
Lemma t6 : p15.
Proof.
 refine (constant2 _ i8 _) ; finalize.
Qed.
Lemma l14 : s1 -> p15 (* BND(c0, [0.0416667, 0.0416667]) *).
Proof.
 intros h0.
 apply t6.
Qed.
Definition f12 := Float2 (-224159373595850987633875411130016843147093066756672299130312035767681678343605521690751904092380389545006063277370015) (-410).
Definition f13 := Float2 (-1) (-130).
Definition i9 := makepairF f12 f13.
Notation p16 := (BND r9 i9). (* BND(th * th * (c1 + th * th * c2), [-8.47732e-08, -7.34684e-40]) *)
Definition f14 := Float2 (1) (-120).
Definition f15 := Float2 (630448238307339705698626334683359606585610863961840561047296826602136301653218879920768343146802465245558035497170013) (-402).
Definition i10 := makepairF f14 f15.
Notation p17 := (BND r4 i10). (* BND(th * th, [7.52316e-37, 6.10367e-05]) *)
Lemma t7 : p9 -> p17.
Proof.
 intros h0.
 refine (square _th i4 i10 h0 _) ; finalize.
Qed.
Lemma l16 : s1 -> p17 (* BND(th * th, [7.52316e-37, 6.10367e-05]) *).
Proof.
 intros h0.
 assert (h1 := l9 h0).
 apply t7. exact h1.
Qed.
Definition f16 := Float2 (-272443651679669696922339033461060347952234885793210565) (-187).
Definition f17 := Float2 (-229533072313894958630969275510310271405085893166630021637247302594824876054183464797255289428799936349431196572047249653) (-406).
Definition i11 := makepairF f16 f17.
Notation p18 := (BND r10 i11). (* BND(c1 + th * th * c2, [-0.00138889, -0.00138889]) *)
Definition f18 := Float2 (-6405119469336935) (-62).
Definition i12 := makepairF f18 f18.
Notation p19 := (BND _c1 i12). (* BND(c1, [-0.00138889, -0.00138889]) *)
Lemma t8 : p19.
Proof.
 refine (constant2 _ i12 _) ; finalize.
Qed.
Lemma l18 : s1 -> p19 (* BND(c1, [-0.00138889, -0.00138889]) *).
Proof.
 intros h0.
 apply t8.
Qed.
Definition f19 := Float2 (3659771605655355) (-187).
Definition f20 := Float2 (250157594443023707962182439722957185004393414074730600246197375408840108120673602175860636754856509020811920535307) (-406).
Definition i13 := makepairF f19 f20.
Notation p20 := (BND r12 i13). (* BND(th * th * c2, [1.86571e-41, 1.51368e-09]) *)
Definition f21 := Float2 (3659771605655355) (-67).
Definition i14 := makepairF f21 f21.
Notation p21 := (BND _c2 i14). (* BND(c2, [2.47996e-05, 2.47996e-05]) *)
Lemma t9 : p21.
Proof.
 refine (constant2 _ i14 _) ; finalize.
Qed.
Lemma l20 : s1 -> p21 (* BND(c2, [2.47996e-05, 2.47996e-05]) *).
Proof.
 intros h0.
 apply t9.
Qed.
Definition f22 := Float2 (2462688430888045725385259119856873463225042437350939691591003228914594928332886249690501340417197129865461076160821) (-394).
Definition i15 := makepairF f14 f22.
Notation p22 := (BND r4 i15). (* BND(th * th, [7.52316e-37, 6.10367e-05]) *)
Lemma t10 : p22 -> p21 -> p20.
Proof.
 intros h0 h1.
 refine (mul_pp r4 _c2 i15 i14 i13 h0 h1 _) ; finalize.
Qed.
Lemma l19 : s1 -> p20 (* BND(th * th * c2, [1.86571e-41, 1.51368e-09]) *).
Proof.
 intros h0.
 assert (h1 := l16 h0).
 assert (h2 := l20 h0).
 apply t10. refine (subset r4 i10 i15 h1 _) ; finalize. exact h2.
Qed.
Lemma t11 : p19 -> p20 -> p18.
Proof.
 intros h0 h1.
 refine (add _c1 r12 i12 i13 i11 h0 h1 _) ; finalize.
Qed.
Lemma l17 : s1 -> p18 (* BND(c1 + th * th * c2, [-0.00138889, -0.00138889]) *).
Proof.
 intros h0.
 assert (h1 := l18 h0).
 assert (h2 := l19 h0).
 apply t11. exact h1. exact h2.
Qed.
Definition f23 := Float2 (-1) (-10).
Definition i16 := makepairF f16 f23.
Notation p23 := (BND r10 i16). (* BND(c1 + th * th * c2, [-0.00138889, -0.000976562]) *)
Lemma t12 : p17 -> p23 -> p16.
Proof.
 intros h0 h1.
 refine (mul_pn r4 r10 i10 i16 i9 h0 h1 _) ; finalize.
Qed.
Lemma l15 : s1 -> p16 (* BND(th * th * (c1 + th * th * c2), [-8.47732e-08, -7.34684e-40]) *).
Proof.
 intros h0.
 assert (h1 := l16 h0).
 assert (h2 := l17 h0).
 apply t12. exact h1. refine (subset r10 i11 i16 h2 _) ; finalize.
Qed.
Definition f24 := Float2 (-3502490212435171681779303298906513174173329168073004673911125558870026224118836276417998501443443586640719738708907) (-404).
Definition i17 := makepairF f24 f13.
Notation p24 := (BND r9 i17). (* BND(th * th * (c1 + th * th * c2), [-8.47732e-08, -7.34684e-40]) *)
Lemma t13 : p15 -> p24 -> p14.
Proof.
 intros h0 h1.
 refine (add _c0 r9 i8 i17 i7 h0 h1 _) ; finalize.
Qed.
Lemma l13 : s1 -> p14 (* BND(P, [0.0416666, 0.0416667]) *).
Proof.
 intros h0.
 assert (h1 := l14 h0).
 assert (h2 := l15 h0).
 apply t13. exact h1. refine (subset r9 i9 i17 h2 _) ; finalize.
Qed.
Notation p25 := (BND _P i6). (* BND(P, [0.03125, 1]) *)
Lemma t14 : p25 -> p13.
Proof.
 intros h0.
 refine (abs_of_bnd_p _P i6 i6 h0 _) ; finalize.
Qed.
Lemma l12 : s1 -> p13 (* ABS(P, [0.03125, 1]) *).
Proof.
 intros h0.
 assert (h1 := l13 h0).
 apply t14. refine (subset _P i7 i6 h1 _) ; finalize.
Qed.
Lemma t15 : p13 -> p12.
Proof.
 intros h0.
 refine (nzr_of_abs _P i6 h0 _) ; finalize.
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
Notation p26 := (REL _tail _T i3). (* REL(tail, T, [-5.27357e-16, 5.27357e-16]) *)
Definition f25 := Float2 (-1) (-53).
Definition f26 := Float2 (1) (-53).
Definition i18 := makepairF f25 f26.
Notation p27 := (REL _tail r28 i18). (* REL(tail, a4 * pc, [-1.11022e-16, 1.11022e-16]) *)
Notation p28 := (FIX r28 (-652)). (* FIX(a4 * pc, -652) *)
Notation p29 := (FIX _a4 (-292)). (* FIX(a4, -292) *)
Notation p30 := (FLT _a4 (53)). (* FLT(a4, 53) *)
Lemma t17 : p30.
Proof.
 refine (flt_of_float _ _ _ (53) _ _) ; finalize.
Qed.
Lemma l25 : s1 -> p30 (* FLT(a4, 53) *).
Proof.
 intros h0.
 apply t17.
Qed.
Definition f27 := Float2 (1) (-240).
Definition i19 := makepairF f27 f8.
Notation p31 := (ABS _a4 i19). (* ABS(a4, [5.6598e-73, 1]) *)
Notation p32 := (BND _a4 i19). (* BND(a4, [5.6598e-73, 1]) *)
Notation p33 := (BND r15 i19). (* BND(uh * uh, [5.6598e-73, 1]) *)
Definition f28 := Float2 (5) (-16).
Definition i20 := makepairF f14 f28.
Notation p34 := (ABS _uh i20). (* ABS(uh, [7.52316e-37, 7.62939e-05]) *)
Definition f29 := Float2 (2251857460129413) (-65).
Definition i21 := makepairF f14 f29.
Notation p35 := (BND _uh i21). (* BND(uh, [7.52316e-37, 6.10367e-05]) *)
Definition f30 := Float2 (9007429840517653) (-67).
Definition i22 := makepairF f14 f30.
Notation p36 := (BND r4 i22). (* BND(th * th, [7.52316e-37, 6.10367e-05]) *)
Lemma t18 : p36 -> p35.
Proof.
 intros h0.
 refine (float_round_ne _ _ r4 i22 i21 h0 _) ; finalize.
Qed.
Lemma l30 : s1 -> p35 (* BND(uh, [7.52316e-37, 6.10367e-05]) *).
Proof.
 intros h0.
 assert (h1 := l16 h0).
 apply t18. refine (subset r4 i10 i22 h1 _) ; finalize.
Qed.
Notation p37 := (BND _uh i20). (* BND(uh, [7.52316e-37, 7.62939e-05]) *)
Lemma t19 : p37 -> p34.
Proof.
 intros h0.
 refine (abs_of_bnd_p _uh i20 i20 h0 _) ; finalize.
Qed.
Lemma l29 : s1 -> p34 (* ABS(uh, [7.52316e-37, 7.62939e-05]) *).
Proof.
 intros h0.
 assert (h1 := l30 h0).
 apply t19. refine (subset _uh i21 i20 h1 _) ; finalize.
Qed.
Definition i23 := makepairF f14 f8.
Notation p38 := (ABS _uh i23). (* ABS(uh, [7.52316e-37, 1]) *)
Lemma t20 : p38 -> p33.
Proof.
 intros h0.
 refine (square _uh i23 i19 h0 _) ; finalize.
Qed.
Lemma l28 : s1 -> p33 (* BND(uh * uh, [5.6598e-73, 1]) *).
Proof.
 intros h0.
 assert (h1 := l29 h0).
 apply t20. refine (abs_subset _uh i20 i23 h1 _) ; finalize.
Qed.
Lemma t21 : p33 -> p32.
Proof.
 intros h0.
 refine (float_round_ne _ _ r15 i19 i19 h0 _) ; finalize.
Qed.
Lemma l27 : s1 -> p32 (* BND(a4, [5.6598e-73, 1]) *).
Proof.
 intros h0.
 assert (h1 := l28 h0).
 apply t21. exact h1.
Qed.
Lemma t22 : p32 -> p31.
Proof.
 intros h0.
 refine (abs_of_bnd_p _a4 i19 i19 h0 _) ; finalize.
Qed.
Lemma l26 : s1 -> p31 (* ABS(a4, [5.6598e-73, 1]) *).
Proof.
 intros h0.
 assert (h1 := l27 h0).
 apply t22. exact h1.
Qed.
Lemma t23 : p30 -> p31 -> p29.
Proof.
 intros h0 h1.
 refine (fix_of_flt_bnd _a4 i19 (-292) (53) h0 h1 _) ; finalize.
Qed.
Lemma l24 : s1 -> p29 (* FIX(a4, -292) *).
Proof.
 intros h0.
 assert (h1 := l25 h0).
 assert (h2 := l26 h0).
 apply t23. exact h1. exact h2.
Qed.
Notation p39 := (FIX _pc (-360)). (* FIX(pc, -360) *)
Notation p40 := (FIX r18 (-360)). (* FIX(c0 + float<53,-1074,ne>(uh * p2), -360) *)
Notation p41 := (FIX _c0 (-57)). (* FIX(c0, -57) *)
Notation p42 := (ABS _c0 i8). (* ABS(c0, [0.0416667, 0.0416667]) *)
Lemma t24 : p15 -> p42.
Proof.
 intros h0.
 refine (abs_of_bnd_p _c0 i8 i8 h0 _) ; finalize.
Qed.
Lemma l34 : s1 -> p42 (* ABS(c0, [0.0416667, 0.0416667]) *).
Proof.
 intros h0.
 assert (h1 := l14 h0).
 apply t24. exact h1.
Qed.
Lemma t25 : p42 -> p41.
Proof.
 intros h0.
 refine (fix_of_singleton_bnd _c0 i8 (-57) h0 _) ; finalize.
Qed.
Lemma l33 : s1 -> p41 (* FIX(c0, -57) *).
Proof.
 intros h0.
 assert (h1 := l34 h0).
 apply t25. exact h1.
Qed.
Notation p43 := (FIX r19 (-360)). (* FIX(float<53,-1074,ne>(uh * p2), -360) *)
Notation p44 := (FIX r20 (-360)). (* FIX(uh * p2, -360) *)
Notation p45 := (FIX _uh (-172)). (* FIX(uh, -172) *)
Notation p46 := (FLT _uh (53)). (* FLT(uh, 53) *)
Lemma t26 : p46.
Proof.
 refine (flt_of_float _ _ _ (53) _ _) ; finalize.
Qed.
Lemma l38 : s1 -> p46 (* FLT(uh, 53) *).
Proof.
 intros h0.
 apply t26.
Qed.
Lemma t27 : p46 -> p38 -> p45.
Proof.
 intros h0 h1.
 refine (fix_of_flt_bnd _uh i23 (-172) (53) h0 h1 _) ; finalize.
Qed.
Lemma l37 : s1 -> p45 (* FIX(uh, -172) *).
Proof.
 intros h0.
 assert (h1 := l38 h0).
 assert (h2 := l29 h0).
 apply t27. exact h1. refine (abs_subset _uh i20 i23 h2 _) ; finalize.
Qed.
Notation p47 := (FIX _p2 (-188)). (* FIX(p2, -188) *)
Notation p48 := (FIX r22 (-188)). (* FIX(c1 + float<53,-1074,ne>(uh * c2), -188) *)
Notation p49 := (FIX _c1 (-62)). (* FIX(c1, -62) *)
Definition f31 := Float2 (6405119469336935) (-62).
Definition i24 := makepairF f31 f31.
Notation p50 := (ABS _c1 i24). (* ABS(c1, [0.00138889, 0.00138889]) *)
Lemma t28 : p19 -> p50.
Proof.
 intros h0.
 refine (abs_of_bnd_n _c1 i12 i24 h0 _) ; finalize.
Qed.
Lemma l42 : s1 -> p50 (* ABS(c1, [0.00138889, 0.00138889]) *).
Proof.
 intros h0.
 assert (h1 := l18 h0).
 apply t28. exact h1.
Qed.
Lemma t29 : p50 -> p49.
Proof.
 intros h0.
 refine (fix_of_singleton_bnd _c1 i24 (-62) h0 _) ; finalize.
Qed.
Lemma l41 : s1 -> p49 (* FIX(c1, -62) *).
Proof.
 intros h0.
 assert (h1 := l42 h0).
 apply t29. exact h1.
Qed.
Notation p51 := (FIX r23 (-188)). (* FIX(float<53,-1074,ne>(uh * c2), -188) *)
Notation p52 := (FLT r23 (53)). (* FLT(float<53,-1074,ne>(uh * c2), 53) *)
Lemma t30 : p52.
Proof.
 refine (flt_of_float _ _ _ (53) _ _) ; finalize.
Qed.
Lemma l44 : s1 -> p52 (* FLT(float<53,-1074,ne>(uh * c2), 53) *).
Proof.
 intros h0.
 apply t30.
Qed.
Definition f32 := Float2 (1) (-136).
Definition i25 := makepairF f32 f8.
Notation p53 := (ABS r23 i25). (* ABS(float<53,-1074,ne>(uh * c2), [1.14794e-41, 1]) *)
Definition f33 := Float2 (7319730592816153) (-82).
Definition i26 := makepairF f32 f33.
Notation p54 := (BND r23 i26). (* BND(float<53,-1074,ne>(uh * c2), [1.14794e-41, 1.51368e-09]) *)
Notation p55 := (BND r24 i26). (* BND(uh * c2, [1.14794e-41, 1.51368e-09]) *)
Definition f34 := Float2 (1) (-16).
Definition i27 := makepairF f34 f21.
Notation p56 := (BND _c2 i27). (* BND(c2, [1.52588e-05, 2.47996e-05]) *)
Lemma t31 : p35 -> p56 -> p55.
Proof.
 intros h0 h1.
 refine (mul_pp _uh _c2 i21 i27 i26 h0 h1 _) ; finalize.
Qed.
Lemma l47 : s1 -> p55 (* BND(uh * c2, [1.14794e-41, 1.51368e-09]) *).
Proof.
 intros h0.
 assert (h1 := l30 h0).
 assert (h2 := l20 h0).
 apply t31. exact h1. refine (subset _c2 i14 i27 h2 _) ; finalize.
Qed.
Lemma t32 : p55 -> p54.
Proof.
 intros h0.
 refine (float_round_ne _ _ r24 i26 i26 h0 _) ; finalize.
Qed.
Lemma l46 : s1 -> p54 (* BND(float<53,-1074,ne>(uh * c2), [1.14794e-41, 1.51368e-09]) *).
Proof.
 intros h0.
 assert (h1 := l47 h0).
 apply t32. exact h1.
Qed.
Notation p57 := (BND r23 i25). (* BND(float<53,-1074,ne>(uh * c2), [1.14794e-41, 1]) *)
Lemma t33 : p57 -> p53.
Proof.
 intros h0.
 refine (abs_of_bnd_p r23 i25 i25 h0 _) ; finalize.
Qed.
Lemma l45 : s1 -> p53 (* ABS(float<53,-1074,ne>(uh * c2), [1.14794e-41, 1]) *).
Proof.
 intros h0.
 assert (h1 := l46 h0).
 apply t33. refine (subset r23 i26 i25 h1 _) ; finalize.
Qed.
Lemma t34 : p52 -> p53 -> p51.
Proof.
 intros h0 h1.
 refine (fix_of_flt_bnd r23 i25 (-188) (53) h0 h1 _) ; finalize.
Qed.
Lemma l43 : s1 -> p51 (* FIX(float<53,-1074,ne>(uh * c2), -188) *).
Proof.
 intros h0.
 assert (h1 := l44 h0).
 assert (h2 := l45 h0).
 apply t34. exact h1. exact h2.
Qed.
Lemma t35 : p49 -> p51 -> p48.
Proof.
 intros h0 h1.
 refine (add_fix _c1 r23 (-62) (-188) (-188) h0 h1 _) ; finalize.
Qed.
Lemma l40 : s1 -> p48 (* FIX(c1 + float<53,-1074,ne>(uh * c2), -188) *).
Proof.
 intros h0.
 assert (h1 := l41 h0).
 assert (h2 := l43 h0).
 apply t35. exact h1. exact h2.
Qed.
Lemma t36 : p48 -> p47.
Proof.
 intros h0.
 refine (fix_float_of_fix _ _ _ (-188) (-188) r22 h0 _) ; finalize.
Qed.
Lemma l39 : s1 -> p47 (* FIX(p2, -188) *).
Proof.
 intros h0.
 assert (h1 := l40 h0).
 apply t36. exact h1.
Qed.
Lemma t37 : p45 -> p47 -> p44.
Proof.
 intros h0 h1.
 refine (mul_fix _uh _p2 (-172) (-188) (-360) h0 h1 _) ; finalize.
Qed.
Lemma l36 : s1 -> p44 (* FIX(uh * p2, -360) *).
Proof.
 intros h0.
 assert (h1 := l37 h0).
 assert (h2 := l39 h0).
 apply t37. exact h1. exact h2.
Qed.
Lemma t38 : p44 -> p43.
Proof.
 intros h0.
 refine (fix_float_of_fix _ _ _ (-360) (-360) r20 h0 _) ; finalize.
Qed.
Lemma l35 : s1 -> p43 (* FIX(float<53,-1074,ne>(uh * p2), -360) *).
Proof.
 intros h0.
 assert (h1 := l36 h0).
 apply t38. exact h1.
Qed.
Lemma t39 : p41 -> p43 -> p40.
Proof.
 intros h0 h1.
 refine (add_fix _c0 r19 (-57) (-360) (-360) h0 h1 _) ; finalize.
Qed.
Lemma l32 : s1 -> p40 (* FIX(c0 + float<53,-1074,ne>(uh * p2), -360) *).
Proof.
 intros h0.
 assert (h1 := l33 h0).
 assert (h2 := l35 h0).
 apply t39. exact h1. exact h2.
Qed.
Lemma t40 : p40 -> p39.
Proof.
 intros h0.
 refine (fix_float_of_fix _ _ _ (-360) (-360) r18 h0 _) ; finalize.
Qed.
Lemma l31 : s1 -> p39 (* FIX(pc, -360) *).
Proof.
 intros h0.
 assert (h1 := l32 h0).
 apply t40. exact h1.
Qed.
Lemma t41 : p29 -> p39 -> p28.
Proof.
 intros h0 h1.
 refine (mul_fix _a4 _pc (-292) (-360) (-652) h0 h1 _) ; finalize.
Qed.
Lemma l23 : s1 -> p28 (* FIX(a4 * pc, -652) *).
Proof.
 intros h0.
 assert (h1 := l24 h0).
 assert (h2 := l31 h0).
 apply t41. exact h1. exact h2.
Qed.
Lemma t42 : p28 -> p27.
Proof.
 intros h0.
 refine (rel_of_fix_float_ne _ _ (-652) r28 i18 h0 _) ; finalize.
Qed.
Lemma l22 : s1 -> p27 (* REL(tail, a4 * pc, [-1.11022e-16, 1.11022e-16]) *).
Proof.
 intros h0.
 assert (h1 := l23 h0).
 apply t42. exact h1.
Qed.
Definition f35 := Float2 (-605215851555165963322928544008843154026850821611494234425927768145803732341416352110951734885163843746472485476232900693) (-449).
Definition f36 := Float2 (302607925777583075731128784134400360479172327738399593035526132822520959829479618213168038754609389029760698251191943321) (-448).
Definition i28 := makepairF f35 f36.
Notation p58 := (REL r28 _T i28). (* REL(a4 * pc, T, [-4.16334e-16, 4.16334e-16]) *)
Definition f37 := Float2 (-243388915243820018065769251209217) (-159).
Definition f38 := Float2 (243388915243820072108964779655169) (-159).
Definition i29 := makepairF f37 f38.
Notation p59 := (REL _a4 r2 i29). (* REL(a4, th * th * th * th, [-3.33067e-16, 3.33067e-16]) *)
Notation p60 := (BND r34 i29). (* BND((a4 - th * th * th * th) / (th * th * th * th), [-3.33067e-16, 3.33067e-16]) *)
Notation p61 := (BND r42 i29). (* BND((1 + (uh - th * th) / (th * th)) * (1 + (uh - th * th) / (th * th)) * (1 + (a4 - uh * uh) / (uh * uh)) - 1, [-3.33067e-16, 3.33067e-16]) *)
Definition f39 := Float2 (730750818665451215712927172538123444058715062271) (-159).
Definition f40 := Float2 (730750818665451702490757660178213618792745926657) (-159).
Definition i30 := makepairF f39 f40.
Notation p62 := (BND r43 i30). (* BND((1 + (uh - th * th) / (th * th)) * (1 + (uh - th * th) / (th * th)) * (1 + (a4 - uh * uh) / (uh * uh)), [1, 1]) *)
Definition f41 := Float2 (81129638414606663681390495662081) (-106).
Definition f42 := Float2 (81129638414606699710187514626049) (-106).
Definition i31 := makepairF f41 f42.
Notation p63 := (BND r44 i31). (* BND((1 + (uh - th * th) / (th * th)) * (1 + (uh - th * th) / (th * th)), [1, 1]) *)
Definition f43 := Float2 (9007199254740991) (-53).
Definition f44 := Float2 (9007199254740993) (-53).
Definition i32 := makepairF f43 f44.
Notation p64 := (ABS r45 i32). (* ABS(1 + (uh - th * th) / (th * th), [1, 1]) *)
Definition i33 := makepairF f8 f8.
Notation p65 := (ABS r33 i33). (* ABS(1, [1, 1]) *)
Notation p66 := (BND r33 i33). (* BND(1, [1, 1]) *)
Lemma t43 : p66.
Proof.
 refine (constant1 _ i33 _) ; finalize.
Qed.
Lemma l56 : s1 -> p66 (* BND(1, [1, 1]) *).
Proof.
 intros h0.
 apply t43.
Qed.
Lemma t44 : p66 -> p65.
Proof.
 intros h0.
 refine (abs_of_bnd_p r33 i33 i33 h0 _) ; finalize.
Qed.
Lemma l55 : s1 -> p65 (* ABS(1, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l56 h0).
 apply t44. exact h1.
Qed.
Definition f45 := Float2 (0) (0).
Definition i34 := makepairF f45 f26.
Notation p67 := (ABS r46 i34). (* ABS((uh - th * th) / (th * th), [0, 1.11022e-16]) *)
Notation p68 := (BND r46 i18). (* BND((uh - th * th) / (th * th), [-1.11022e-16, 1.11022e-16]) *)
Notation p69 := (REL _uh r4 i18). (* REL(uh, th * th, [-1.11022e-16, 1.11022e-16]) *)
Notation p70 := (FIX r4 (-224)). (* FIX(th * th, -224) *)
Notation p71 := (FIX _th (-112)). (* FIX(th, -112) *)
Notation p72 := (FLT _th (53)). (* FLT(th, 53) *)
Lemma t45 : p72.
Proof.
 refine (flt_of_float _ _ _ (53) _ _) ; finalize.
Qed.
Lemma l62 : s1 -> p72 (* FLT(th, 53) *).
Proof.
 intros h0.
 apply t45.
Qed.
Lemma t46 : p72 -> p11 -> p71.
Proof.
 intros h0 h1.
 refine (fix_of_flt_bnd _th i5 (-112) (53) h0 h1 _) ; finalize.
Qed.
Lemma l61 : s1 -> p71 (* FIX(th, -112) *).
Proof.
 intros h0.
 assert (h1 := l62 h0).
 assert (h2 := l9 h0).
 apply t46. exact h1. refine (abs_subset _th i4 i5 h2 _) ; finalize.
Qed.
Lemma t47 : p71 -> p71 -> p70.
Proof.
 intros h0 h1.
 refine (mul_fix _th _th (-112) (-112) (-224) h0 h1 _) ; finalize.
Qed.
Lemma l60 : s1 -> p70 (* FIX(th * th, -224) *).
Proof.
 intros h0.
 assert (h1 := l61 h0).
 apply t47. exact h1. exact h1.
Qed.
Lemma t48 : p70 -> p69.
Proof.
 intros h0.
 refine (rel_of_fix_float_ne _ _ (-224) r4 i18 h0 _) ; finalize.
Qed.
Lemma l59 : s1 -> p69 (* REL(uh, th * th, [-1.11022e-16, 1.11022e-16]) *).
Proof.
 intros h0.
 assert (h1 := l60 h0).
 apply t48. exact h1.
Qed.
Lemma t49 : p7 -> p69 -> p68.
Proof.
 intros h0 h1.
 refine (bnd_of_nzr_rel _uh r4 i18 h0 h1) ; finalize.
Qed.
Lemma l58 : s1 -> p68 (* BND((uh - th * th) / (th * th), [-1.11022e-16, 1.11022e-16]) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 assert (h2 := l59 h0).
 apply t49. exact h1. exact h2.
Qed.
Lemma t50 : p68 -> p67.
Proof.
 intros h0.
 refine (abs_of_bnd_o r46 i18 i34 h0 _) ; finalize.
Qed.
Lemma l57 : s1 -> p67 (* ABS((uh - th * th) / (th * th), [0, 1.11022e-16]) *).
Proof.
 intros h0.
 assert (h1 := l58 h0).
 apply t50. exact h1.
Qed.
Lemma t51 : p65 -> p67 -> p64.
Proof.
 intros h0 h1.
 refine (add_aa_p r33 r46 i33 i34 i32 h0 h1 _) ; finalize.
Qed.
Lemma l54 : s1 -> p64 (* ABS(1 + (uh - th * th) / (th * th), [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l55 h0).
 assert (h2 := l57 h0).
 apply t51. exact h1. exact h2.
Qed.
Lemma t52 : p64 -> p63.
Proof.
 intros h0.
 refine (square r45 i32 i31 h0 _) ; finalize.
Qed.
Lemma l53 : s1 -> p63 (* BND((1 + (uh - th * th) / (th * th)) * (1 + (uh - th * th) / (th * th)), [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l54 h0).
 apply t52. exact h1.
Qed.
Notation p73 := (BND r48 i32). (* BND(1 + (a4 - uh * uh) / (uh * uh), [1, 1]) *)
Notation p74 := (BND r49 i18). (* BND((a4 - uh * uh) / (uh * uh), [-1.11022e-16, 1.11022e-16]) *)
Notation p75 := (NZR r15). (* NZR(uh * uh) *)
Notation p76 := (NZR _uh). (* NZR(uh) *)
Definition f46 := Float2 (-1) (-1).
Definition i35 := makepairF f46 f8.
Notation p77 := (REL _uh r4 i35). (* REL(uh, th * th, [-0.5, 1]) *)
Lemma t53 : p7 -> p77 -> p76.
Proof.
 intros h0 h1.
 refine (nzr_of_nzr_rel _uh r4 i35 h0 h1 _) ; finalize.
Qed.
Lemma l66 : s1 -> p76 (* NZR(uh) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 assert (h2 := l59 h0).
 apply t53. exact h1. refine (rel_subset _uh r4 i18 i35 h2 _) ; finalize.
Qed.
Lemma t54 : p76 -> p76 -> p75.
Proof.
 intros h0 h1.
 refine (mul_nzr _uh _uh h0 h1) ; finalize.
Qed.
Lemma l65 : s1 -> p75 (* NZR(uh * uh) *).
Proof.
 intros h0.
 assert (h1 := l66 h0).
 apply t54. exact h1. exact h1.
Qed.
Notation p78 := (REL _a4 r15 i18). (* REL(a4, uh * uh, [-1.11022e-16, 1.11022e-16]) *)
Notation p79 := (FIX r15 (-448)). (* FIX(uh * uh, -448) *)
Notation p80 := (FIX _uh (-224)). (* FIX(uh, -224) *)
Lemma t55 : p70 -> p80.
Proof.
 intros h0.
 refine (fix_float_of_fix _ _ _ (-224) (-224) r4 h0 _) ; finalize.
Qed.
Lemma l69 : s1 -> p80 (* FIX(uh, -224) *).
Proof.
 intros h0.
 assert (h1 := l60 h0).
 apply t55. exact h1.
Qed.
Lemma t56 : p80 -> p80 -> p79.
Proof.
 intros h0 h1.
 refine (mul_fix _uh _uh (-224) (-224) (-448) h0 h1 _) ; finalize.
Qed.
Lemma l68 : s1 -> p79 (* FIX(uh * uh, -448) *).
Proof.
 intros h0.
 assert (h1 := l69 h0).
 apply t56. exact h1. exact h1.
Qed.
Lemma t57 : p79 -> p78.
Proof.
 intros h0.
 refine (rel_of_fix_float_ne _ _ (-448) r15 i18 h0 _) ; finalize.
Qed.
Lemma l67 : s1 -> p78 (* REL(a4, uh * uh, [-1.11022e-16, 1.11022e-16]) *).
Proof.
 intros h0.
 assert (h1 := l68 h0).
 apply t57. exact h1.
Qed.
Lemma t58 : p75 -> p78 -> p74.
Proof.
 intros h0 h1.
 refine (bnd_of_nzr_rel _a4 r15 i18 h0 h1) ; finalize.
Qed.
Lemma l64 : s1 -> p74 (* BND((a4 - uh * uh) / (uh * uh), [-1.11022e-16, 1.11022e-16]) *).
Proof.
 intros h0.
 assert (h1 := l65 h0).
 assert (h2 := l67 h0).
 apply t58. exact h1. exact h2.
Qed.
Lemma t59 : p66 -> p74 -> p73.
Proof.
 intros h0 h1.
 refine (add r33 r49 i33 i18 i32 h0 h1 _) ; finalize.
Qed.
Lemma l63 : s1 -> p73 (* BND(1 + (a4 - uh * uh) / (uh * uh), [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l56 h0).
 assert (h2 := l64 h0).
 apply t59. exact h1. exact h2.
Qed.
Lemma t60 : p63 -> p73 -> p62.
Proof.
 intros h0 h1.
 refine (mul_pp r44 r48 i31 i32 i30 h0 h1 _) ; finalize.
Qed.
Lemma l52 : s1 -> p62 (* BND((1 + (uh - th * th) / (th * th)) * (1 + (uh - th * th) / (th * th)) * (1 + (a4 - uh * uh) / (uh * uh)), [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l53 h0).
 assert (h2 := l63 h0).
 apply t60. exact h1. exact h2.
Qed.
Lemma t61 : p62 -> p66 -> p61.
Proof.
 intros h0 h1.
 refine (sub r43 r33 i30 i33 i29 h0 h1 _) ; finalize.
Qed.
Lemma l51 : s1 -> p61 (* BND((1 + (uh - th * th) / (th * th)) * (1 + (uh - th * th) / (th * th)) * (1 + (a4 - uh * uh) / (uh * uh)) - 1, [-3.33067e-16, 3.33067e-16]) *).
Proof.
 intros h0.
 assert (h1 := l52 h0).
 assert (h2 := l56 h0).
 apply t61. exact h1. exact h2.
Qed.
Definition i36 := makepairF f45 f45.
Notation p81 := (REL r34 r42 i36). (* REL((a4 - th * th * th * th) / (th * th * th * th), (1 + (uh - th * th) / (th * th)) * (1 + (uh - th * th) / (th * th)) * (1 + (a4 - uh * uh) / (uh * uh)) - 1, [0, 0]) *)
Notation p82 := (r34 = r42). (* EQL((a4 - th * th * th * th) / (th * th * th * th), (1 + (uh - th * th) / (th * th)) * (1 + (uh - th * th) / (th * th)) * (1 + (a4 - uh * uh) / (uh * uh)) - 1) *)
Lemma t62 : p8 -> p76 -> p82.
Proof.
 intros h0 h1.
 refine (b2 h0 h1) ; finalize.
Qed.
Lemma l71 : s1 -> p82 (* EQL((a4 - th * th * th * th) / (th * th * th * th), (1 + (uh - th * th) / (th * th)) * (1 + (uh - th * th) / (th * th)) * (1 + (a4 - uh * uh) / (uh * uh)) - 1) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 assert (h2 := l66 h0).
 apply t62. exact h1. exact h2.
Qed.
Notation p83 := (REL r42 r42 i36). (* REL((1 + (uh - th * th) / (th * th)) * (1 + (uh - th * th) / (th * th)) * (1 + (a4 - uh * uh) / (uh * uh)) - 1, (1 + (uh - th * th) / (th * th)) * (1 + (uh - th * th) / (th * th)) * (1 + (a4 - uh * uh) / (uh * uh)) - 1, [0, 0]) *)
Lemma t63 : p83.
Proof.
 refine (rel_refl r42 i36 _) ; finalize.
Qed.
Lemma l72 : s1 -> p83 (* REL((1 + (uh - th * th) / (th * th)) * (1 + (uh - th * th) / (th * th)) * (1 + (a4 - uh * uh) / (uh * uh)) - 1, (1 + (uh - th * th) / (th * th)) * (1 + (uh - th * th) / (th * th)) * (1 + (a4 - uh * uh) / (uh * uh)) - 1, [0, 0]) *).
Proof.
 intros h0.
 apply t63.
Qed.
Lemma t64 : p82 -> p83 -> p81.
Proof.
 intros h0 h1.
 refine (rel_rewrite_1 r34 r42 r42 i36 h0 h1) ; finalize.
Qed.
Lemma l70 : s1 -> p81 (* REL((a4 - th * th * th * th) / (th * th * th * th), (1 + (uh - th * th) / (th * th)) * (1 + (uh - th * th) / (th * th)) * (1 + (a4 - uh * uh) / (uh * uh)) - 1, [0, 0]) *).
Proof.
 intros h0.
 assert (h1 := l71 h0).
 assert (h2 := l72 h0).
 apply t64. exact h1. exact h2.
Qed.
Lemma t65 : p61 -> p81 -> p60.
Proof.
 intros h0 h1.
 refine (bnd_of_bnd_rel_o r34 r42 i29 i36 i29 h0 h1 _) ; finalize.
Qed.
Lemma l50 : s1 -> p60 (* BND((a4 - th * th * th * th) / (th * th * th * th), [-3.33067e-16, 3.33067e-16]) *).
Proof.
 intros h0.
 assert (h1 := l51 h0).
 assert (h2 := l70 h0).
 apply t65. exact h1. exact h2.
Qed.
Lemma t66 : p5 -> p60 -> p59.
Proof.
 intros h0 h1.
 refine (rel_of_nzr_bnd _a4 r2 i29 h0 h1) ; finalize.
Qed.
Lemma l49 : s1 -> p59 (* REL(a4, th * th * th * th, [-3.33067e-16, 3.33067e-16]) *).
Proof.
 intros h0.
 assert (h1 := l5 h0).
 assert (h2 := l50 h0).
 apply t66. exact h1. exact h2.
Qed.
Definition f47 := Float2 (-7565249963366918552004253382720822754915323128839325052055545725210195451264650391446150221494228459136302452876268781) (-445).
Definition f48 := Float2 (484175997655482787328593474611873310101471028819435892146853252049048657513797678720708480136038960226369274080057389307) (-451).
Definition i37 := makepairF f47 f48.
Notation p84 := (REL _pc _P i37). (* REL(pc, P, [-8.32674e-17, 8.32674e-17]) *)
Definition f49 := Float2 (-121043209304667957797163040272890848764834501927081883753757664435235536258296157075990812790576311322498113664706781375) (-449).
Definition f50 := Float2 (1936691348874687324754608644366253580237352030833310140060122630963768580132738513215853004649220981159969818635308501995) (-453).
Definition i38 := makepairF f49 f50.
Notation p85 := (REL _pc r18 i38). (* REL(pc, c0 + float<53,-1074,ne>(uh * p2), [-8.32669e-17, 8.32669e-17]) *)
Notation p86 := (NZR r18). (* NZR(c0 + float<53,-1074,ne>(uh * p2)) *)
Definition f51 := Float2 (-3160436810956139883215166637608884661464312728737354630133238086890446608435543793456765704129247975912270053832201) (-451).
Definition f52 := Float2 (6320873621912279356307512483134859578113043535141838128413852819762076386372649042235742300803681274617399059181907) (-452).
Definition i39 := makepairF f51 f52.
Notation p87 := (REL r18 _P i39). (* REL(c0 + float<53,-1074,ne>(uh * p2), P, [-5.43524e-22, 5.43524e-22]) *)
Notation r53 := ((r18 - _P)%R).
Notation r52 := ((r53 / _P)%R).
Notation p88 := (BND r52 i39). (* BND((c0 + float<53,-1074,ne>(uh * p2) - P) / P, [-5.43524e-22, 5.43524e-22]) *)
Definition f53 := Float2 (-33711257395908061606109763539827582538598764984511132625891950606513568144661605435022460461030166437724597116696979) (-459).
Definition f54 := Float2 (33711257395908059418792502880055208286437802066152863504449134562827253800553141981829298315584208325416275787059819) (-459).
Definition i40 := makepairF f53 f54.
Notation p89 := (BND r53 i40). (* BND(c0 + float<53,-1074,ne>(uh * p2) - P, [-2.26468e-23, 2.26468e-23]) *)
Notation r54 := ((r19 - r9)%R).
Notation p90 := (BND r54 i40). (* BND(float<53,-1074,ne>(uh * p2) - th * th * (c1 + th * th * c2), [-2.26468e-23, 2.26468e-23]) *)
Notation r56 := ((r19 - r20)%R).
Notation r57 := ((r20 - r9)%R).
Notation r55 := ((r56 + r57)%R).
Notation p91 := (BND r55 i40). (* BND(float<53,-1074,ne>(uh * p2) - uh * p2 + (uh * p2 - th * th * (c1 + th * th * c2)), [-2.26468e-23, 2.26468e-23]) *)
Definition f55 := Float2 (-1) (-77).
Definition f56 := Float2 (1) (-77).
Definition i41 := makepairF f55 f56.
Notation p92 := (BND r56 i41). (* BND(float<53,-1074,ne>(uh * p2) - uh * p2, [-6.61744e-24, 6.61744e-24]) *)
Definition f57 := Float2 (1) (-130).
Definition f58 := Float2 (1) (-23).
Definition i42 := makepairF f57 f58.
Notation p93 := (ABS r20 i42). (* ABS(uh * p2, [7.34684e-40, 1.19209e-07]) *)
Definition f59 := Float2 (1) (-10).
Definition f60 := Float2 (3) (-11).
Definition i43 := makepairF f59 f60.
Notation p94 := (ABS _p2 i43). (* ABS(p2, [0.000976562, 0.00146484]) *)
Definition i44 := makepairF f18 f23.
Notation p95 := (BND _p2 i44). (* BND(p2, [-0.00138889, -0.000976562]) *)
Definition f61 := Float2 (-6716247232948853138407) (-82).
Definition i45 := makepairF f18 f61.
Notation p96 := (BND r22 i45). (* BND(c1 + float<53,-1074,ne>(uh * c2), [-0.00138889, -0.00138889]) *)
Lemma t67 : p19 -> p54 -> p96.
Proof.
 intros h0 h1.
 refine (add _c1 r23 i12 i26 i45 h0 h1 _) ; finalize.
Qed.
Lemma l85 : s1 -> p96 (* BND(c1 + float<53,-1074,ne>(uh * c2), [-0.00138889, -0.00138889]) *).
Proof.
 intros h0.
 assert (h1 := l18 h0).
 assert (h2 := l46 h0).
 apply t67. exact h1. exact h2.
Qed.
Notation p97 := (BND r22 i44). (* BND(c1 + float<53,-1074,ne>(uh * c2), [-0.00138889, -0.000976562]) *)
Lemma t68 : p97 -> p95.
Proof.
 intros h0.
 refine (float_round_ne _ _ r22 i44 i44 h0 _) ; finalize.
Qed.
Lemma l84 : s1 -> p95 (* BND(p2, [-0.00138889, -0.000976562]) *).
Proof.
 intros h0.
 assert (h1 := l85 h0).
 apply t68. refine (subset r22 i45 i44 h1 _) ; finalize.
Qed.
Definition f62 := Float2 (-3) (-11).
Definition i46 := makepairF f62 f23.
Notation p98 := (BND _p2 i46). (* BND(p2, [-0.00146484, -0.000976562]) *)
Lemma t69 : p98 -> p94.
Proof.
 intros h0.
 refine (abs_of_bnd_n _p2 i46 i43 h0 _) ; finalize.
Qed.
Lemma l83 : s1 -> p94 (* ABS(p2, [0.000976562, 0.00146484]) *).
Proof.
 intros h0.
 assert (h1 := l84 h0).
 apply t69. refine (subset _p2 i44 i46 h1 _) ; finalize.
Qed.
Lemma t70 : p34 -> p94 -> p93.
Proof.
 intros h0 h1.
 refine (mul_aa _uh _p2 i20 i43 i42 h0 h1 _) ; finalize.
Qed.
Lemma l82 : s1 -> p93 (* ABS(uh * p2, [7.34684e-40, 1.19209e-07]) *).
Proof.
 intros h0.
 assert (h1 := l29 h0).
 assert (h2 := l83 h0).
 apply t70. exact h1. exact h2.
Qed.
Lemma t71 : p93 -> p92.
Proof.
 intros h0.
 refine (float_absolute_wide_ne _ _ r20 i42 i41 h0 _) ; finalize.
Qed.
Lemma l81 : s1 -> p92 (* BND(float<53,-1074,ne>(uh * p2) - uh * p2, [-6.61744e-24, 6.61744e-24]) *).
Proof.
 intros h0.
 assert (h1 := l82 h0).
 apply t71. exact h1.
Qed.
Definition f63 := Float2 (-23860755846809441803040003514791679087328830166894770958904877255452137701787302782168893897308937527522940119120275) (-459).
Definition f64 := Float2 (23860755846809439615722742855019304835167867248536501837462061211765823357678839328975731751862979415214618789483115) (-459).
Definition i47 := makepairF f63 f64.
Notation p99 := (BND r57 i47). (* BND(uh * p2 - th * th * (c1 + th * th * c2), [-1.60294e-23, 1.60294e-23]) *)
Definition f65 := Float2 (-1099475482788833080845195101727662378754172857656232841732144899851194272710329056445239859492376182962881378405531164285) (-451).
Definition f66 := Float2 (549737741394416590817097134535328138573228218009165249317816031822659265636160029891900060303871804543284315121312755133) (-450).
Definition i48 := makepairF f65 f66.
Notation p100 := (REL r20 r9 i48). (* REL(uh * p2, th * th * (c1 + th * th * c2), [-1.89085e-16, 1.89085e-16]) *)
Definition f67 := Float2 (-907826026534211967651366318678861644098501952484161106413548823880389755306044715736393191324652660944250595799648197875) (-452).
Definition f68 := Float2 (453913013267105983825746625457381896679479266474585128870258257804888823373229155384585792812139001504744135210991603437) (-451).
Definition i49 := makepairF f67 f68.
Notation p101 := (REL _p2 r10 i49). (* REL(p2, c1 + th * th * c2, [-7.80629e-17, 7.80629e-17]) *)
Definition f69 := Float2 (-907823212258207028261948627002342465240364378937233371109312320997873095946800523280147431880769245534796868774862832549) (-452).
Definition f70 := Float2 (453911606129103514130974313501171232620182189468616685554656160498936547973400261640073715940384622767398434387431416275) (-451).
Definition i50 := makepairF f69 f70.
Notation p102 := (REL _p2 r22 i50). (* REL(p2, c1 + float<53,-1074,ne>(uh * c2), [-7.80626e-17, 7.80626e-17]) *)
Notation p103 := (NZR r22). (* NZR(c1 + float<53,-1074,ne>(uh * c2)) *)
Notation p104 := (NZR r10). (* NZR(c1 + th * th * c2) *)
Definition i51 := makepairF f59 f8.
Notation p105 := (ABS r10 i51). (* ABS(c1 + th * th * c2, [0.000976562, 1]) *)
Definition f71 := Float2 (-1) (0).
Definition i52 := makepairF f71 f23.
Notation p106 := (BND r10 i52). (* BND(c1 + th * th * c2, [-1, -0.000976562]) *)
Lemma t72 : p106 -> p105.
Proof.
 intros h0.
 refine (abs_of_bnd_n r10 i52 i51 h0 _) ; finalize.
Qed.
Lemma l92 : s1 -> p105 (* ABS(c1 + th * th * c2, [0.000976562, 1]) *).
Proof.
 intros h0.
 assert (h1 := l17 h0).
 apply t72. refine (subset r10 i11 i52 h1 _) ; finalize.
Qed.
Lemma t73 : p105 -> p104.
Proof.
 intros h0.
 refine (nzr_of_abs r10 i51 h0 _) ; finalize.
Qed.
Lemma l91 : s1 -> p104 (* NZR(c1 + th * th * c2) *).
Proof.
 intros h0.
 assert (h1 := l92 h0).
 apply t73. exact h1.
Qed.
Definition f72 := Float2 (-5628552009878779274762990773888098875191644549802440730985092460042559477229884755702244885249739504585145420696267) (-453).
Definition f73 := Float2 (2814276004939389324934093553562951684601254862024754803721993830355213747583112072410420231493557266514546470433459) (-452).
Definition i53 := makepairF f72 f73.
Notation p107 := (REL r22 r10 i53). (* REL(c1 + float<53,-1074,ne>(uh * c2), c1 + th * th * c2, [-2.41996e-22, 2.41996e-22]) *)
Notation p108 := (REL _c1 _c1 i36). (* REL(c1, c1, [0, 0]) *)
Lemma t74 : p108.
Proof.
 refine (rel_refl _c1 i36 _) ; finalize.
Qed.
Lemma l94 : s1 -> p108 (* REL(c1, c1, [0, 0]) *).
Proof.
 intros h0.
 apply t74.
Qed.
Definition f74 := Float2 (-18014398509481983) (-106).
Definition f75 := Float2 (18014398509481985) (-106).
Definition i54 := makepairF f74 f75.
Notation p109 := (REL r23 r12 i54). (* REL(float<53,-1074,ne>(uh * c2), th * th * c2, [-2.22045e-16, 2.22045e-16]) *)
Notation p110 := (REL r23 r24 i18). (* REL(float<53,-1074,ne>(uh * c2), uh * c2, [-1.11022e-16, 1.11022e-16]) *)
Notation p111 := (FIX r24 (-291)). (* FIX(uh * c2, -291) *)
Notation p112 := (FIX _c2 (-67)). (* FIX(c2, -67) *)
Notation p113 := (ABS _c2 i14). (* ABS(c2, [2.47996e-05, 2.47996e-05]) *)
Lemma t75 : p21 -> p113.
Proof.
 intros h0.
 refine (abs_of_bnd_p _c2 i14 i14 h0 _) ; finalize.
Qed.
Lemma l99 : s1 -> p113 (* ABS(c2, [2.47996e-05, 2.47996e-05]) *).
Proof.
 intros h0.
 assert (h1 := l20 h0).
 apply t75. exact h1.
Qed.
Lemma t76 : p113 -> p112.
Proof.
 intros h0.
 refine (fix_of_singleton_bnd _c2 i14 (-67) h0 _) ; finalize.
Qed.
Lemma l98 : s1 -> p112 (* FIX(c2, -67) *).
Proof.
 intros h0.
 assert (h1 := l99 h0).
 apply t76. exact h1.
Qed.
Lemma t77 : p80 -> p112 -> p111.
Proof.
 intros h0 h1.
 refine (mul_fix _uh _c2 (-224) (-67) (-291) h0 h1 _) ; finalize.
Qed.
Lemma l97 : s1 -> p111 (* FIX(uh * c2, -291) *).
Proof.
 intros h0.
 assert (h1 := l69 h0).
 assert (h2 := l98 h0).
 apply t77. exact h1. exact h2.
Qed.
Lemma t78 : p111 -> p110.
Proof.
 intros h0.
 refine (rel_of_fix_float_ne _ _ (-291) r24 i18 h0 _) ; finalize.
Qed.
Lemma l96 : s1 -> p110 (* REL(float<53,-1074,ne>(uh * c2), uh * c2, [-1.11022e-16, 1.11022e-16]) *).
Proof.
 intros h0.
 assert (h1 := l97 h0).
 apply t78. exact h1.
Qed.
Notation p114 := (REL r24 r12 i18). (* REL(uh * c2, th * th * c2, [-1.11022e-16, 1.11022e-16]) *)
Lemma t79 : p69 -> p114.
Proof.
 intros h0.
 refine (mul_firq _uh _ r4 i18 h0) ; finalize.
Qed.
Lemma l100 : s1 -> p114 (* REL(uh * c2, th * th * c2, [-1.11022e-16, 1.11022e-16]) *).
Proof.
 intros h0.
 assert (h1 := l59 h0).
 apply t79. exact h1.
Qed.
Lemma t80 : p110 -> p114 -> p109.
Proof.
 intros h0 h1.
 refine (compose r23 r24 r12 i18 i18 i54 h0 h1 _) ; finalize.
Qed.
Lemma l95 : s1 -> p109 (* REL(float<53,-1074,ne>(uh * c2), th * th * c2, [-2.22045e-16, 2.22045e-16]) *).
Proof.
 intros h0.
 assert (h1 := l96 h0).
 assert (h2 := l100 h0).
 apply t80. exact h1. exact h2.
Qed.
Notation r58 := ((_c1 / r10)%R).
Definition f76 := Float2 (645563173090728382261350082449370531957566722841947993954560990952669452565896073414217621012868722662353143883084471043) (-398).
Definition i55 := makepairF f8 f76.
Notation p115 := (BND r58 i55). (* BND(c1 / (c1 + th * th * c2), [1, 1]) *)
Definition i56 := makepairF f18 f17.
Notation p116 := (BND r10 i56). (* BND(c1 + th * th * c2, [-0.00138889, -0.00138889]) *)
Lemma t81 : p19 -> p116 -> p115.
Proof.
 intros h0 h1.
 refine (div_nn _c1 r10 i12 i56 i55 h0 h1 _) ; finalize.
Qed.
Lemma l101 : s1 -> p115 (* BND(c1 / (c1 + th * th * c2), [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l18 h0).
 assert (h2 := l17 h0).
 apply t81. exact h1. refine (subset r10 i11 i56 h2 _) ; finalize.
Qed.
Lemma t82 : p108 -> p109 -> p115 -> p104 -> p107.
Proof.
 intros h0 h1 h2 h3.
 refine (add_rr _c1 _c1 r23 r12 i36 i54 i55 i53 h0 h1 h2 h3 _) ; finalize.
Qed.
Lemma l93 : s1 -> p107 (* REL(c1 + float<53,-1074,ne>(uh * c2), c1 + th * th * c2, [-2.41996e-22, 2.41996e-22]) *).
Proof.
 intros h0.
 assert (h1 := l94 h0).
 assert (h2 := l95 h0).
 assert (h3 := l101 h0).
 assert (h4 := l91 h0).
 apply t82. exact h1. exact h2. exact h3. exact h4.
Qed.
Notation p117 := (REL r22 r10 i35). (* REL(c1 + float<53,-1074,ne>(uh * c2), c1 + th * th * c2, [-0.5, 1]) *)
Lemma t83 : p104 -> p117 -> p103.
Proof.
 intros h0 h1.
 refine (nzr_of_nzr_rel r22 r10 i35 h0 h1 _) ; finalize.
Qed.
Lemma l90 : s1 -> p103 (* NZR(c1 + float<53,-1074,ne>(uh * c2)) *).
Proof.
 intros h0.
 assert (h1 := l91 h0).
 assert (h2 := l93 h0).
 apply t83. exact h1. refine (rel_subset r22 r10 i53 i35 h2 _) ; finalize.
Qed.
Notation r60 := ((_p2 - r22)%R).
Notation r59 := ((r60 / r22)%R).
Notation p118 := (BND r59 i50). (* BND((p2 - (c1 + float<53,-1074,ne>(uh * c2))) / (c1 + float<53,-1074,ne>(uh * c2)), [-7.80626e-17, 7.80626e-17]) *)
Definition f77 := Float2 (-1) (-63).
Definition f78 := Float2 (1) (-63).
Definition i57 := makepairF f77 f78.
Notation p119 := (BND r60 i57). (* BND(p2 - (c1 + float<53,-1074,ne>(uh * c2)), [-1.0842e-19, 1.0842e-19]) *)
Definition f79 := Float2 (1) (-9).
Definition i58 := makepairF f59 f79.
Notation p120 := (ABS r22 i58). (* ABS(c1 + float<53,-1074,ne>(uh * c2), [0.000976562, 0.00195312]) *)
Definition f80 := Float2 (-1) (-9).
Definition i59 := makepairF f80 f23.
Notation p121 := (BND r22 i59). (* BND(c1 + float<53,-1074,ne>(uh * c2), [-0.00195312, -0.000976562]) *)
Lemma t84 : p121 -> p120.
Proof.
 intros h0.
 refine (abs_of_bnd_n r22 i59 i58 h0 _) ; finalize.
Qed.
Lemma l104 : s1 -> p120 (* ABS(c1 + float<53,-1074,ne>(uh * c2), [0.000976562, 0.00195312]) *).
Proof.
 intros h0.
 assert (h1 := l85 h0).
 apply t84. refine (subset r22 i45 i59 h1 _) ; finalize.
Qed.
Lemma t85 : p120 -> p119.
Proof.
 intros h0.
 refine (float_absolute_wide_ne _ _ r22 i58 i57 h0 _) ; finalize.
Qed.
Lemma l103 : s1 -> p119 (* BND(p2 - (c1 + float<53,-1074,ne>(uh * c2)), [-1.0842e-19, 1.0842e-19]) *).
Proof.
 intros h0.
 assert (h1 := l104 h0).
 apply t85. exact h1.
Qed.
Definition i60 := makepairF f71 f61.
Notation p122 := (BND r22 i60). (* BND(c1 + float<53,-1074,ne>(uh * c2), [-1, -0.00138889]) *)
Lemma t86 : p119 -> p122 -> p118.
Proof.
 intros h0 h1.
 refine (div_on r60 r22 i57 i60 i50 h0 h1 _) ; finalize.
Qed.
Lemma l102 : s1 -> p118 (* BND((p2 - (c1 + float<53,-1074,ne>(uh * c2))) / (c1 + float<53,-1074,ne>(uh * c2)), [-7.80626e-17, 7.80626e-17]) *).
Proof.
 intros h0.
 assert (h1 := l103 h0).
 assert (h2 := l85 h0).
 apply t86. exact h1. refine (subset r22 i45 i60 h2 _) ; finalize.
Qed.
Lemma t87 : p103 -> p118 -> p102.
Proof.
 intros h0 h1.
 refine (rel_of_nzr_bnd _p2 r22 i50 h0 h1) ; finalize.
Qed.
Lemma l89 : s1 -> p102 (* REL(p2, c1 + float<53,-1074,ne>(uh * c2), [-7.80626e-17, 7.80626e-17]) *).
Proof.
 intros h0.
 assert (h1 := l90 h0).
 assert (h2 := l102 h0).
 apply t87. exact h1. exact h2.
Qed.
Lemma t88 : p102 -> p107 -> p101.
Proof.
 intros h0 h1.
 refine (compose _p2 r22 r10 i50 i53 i49 h0 h1 _) ; finalize.
Qed.
Lemma l88 : s1 -> p101 (* REL(p2, c1 + th * th * c2, [-7.80629e-17, 7.80629e-17]) *).
Proof.
 intros h0.
 assert (h1 := l89 h0).
 assert (h2 := l93 h0).
 apply t88. exact h1. exact h2.
Qed.
Lemma t89 : p69 -> p101 -> p100.
Proof.
 intros h0 h1.
 refine (mul_rr _uh r4 _p2 r10 i18 i49 i48 h0 h1 _) ; finalize.
Qed.
Lemma l87 : s1 -> p100 (* REL(uh * p2, th * th * (c1 + th * th * c2), [-1.89085e-16, 1.89085e-16]) *).
Proof.
 intros h0.
 assert (h1 := l59 h0).
 assert (h2 := l88 h0).
 apply t89. exact h1. exact h2.
Qed.
Definition f81 := Float2 (-67106657885060612844555365095682518234507620706557180281502984610058244183980044949050284392845226010918052881196971) (-437).
Definition f82 := Float2 (16776664471265154749056919388895512041419318176549232462091553705525490284306641537228395395015619035134409030801781) (-435).
Definition i61 := makepairF f81 f82.
Notation p123 := (REL r20 r9 i61). (* REL(uh * p2, th * th * (c1 + th * th * c2), [-1.89085e-16, 1.89085e-16]) *)
Lemma t90 : p123 -> p16 -> p99.
Proof.
 intros h0 h1.
 refine (error_of_rel_on r20 r9 i61 i9 i47 h0 h1 _) ; finalize.
Qed.
Lemma l86 : s1 -> p99 (* BND(uh * p2 - th * th * (c1 + th * th * c2), [-1.60294e-23, 1.60294e-23]) *).
Proof.
 intros h0.
 assert (h1 := l87 h0).
 assert (h2 := l15 h0).
 apply t90. refine (rel_subset r20 r9 i48 i61 h1 _) ; finalize. exact h2.
Qed.
Lemma t91 : p92 -> p99 -> p91.
Proof.
 intros h0 h1.
 refine (add r56 r57 i41 i47 i40 h0 h1 _) ; finalize.
Qed.
Lemma l80 : s1 -> p91 (* BND(float<53,-1074,ne>(uh * p2) - uh * p2 + (uh * p2 - th * th * (c1 + th * th * c2)), [-2.26468e-23, 2.26468e-23]) *).
Proof.
 intros h0.
 assert (h1 := l81 h0).
 assert (h2 := l86 h0).
 apply t91. exact h1. exact h2.
Qed.
Lemma t92 : p91 -> p90.
Proof.
 intros h0.
 refine (sub_xals _ _ _ i40 h0) ; finalize.
Qed.
Lemma l79 : s1 -> p90 (* BND(float<53,-1074,ne>(uh * p2) - th * th * (c1 + th * th * c2), [-2.26468e-23, 2.26468e-23]) *).
Proof.
 intros h0.
 assert (h1 := l80 h0).
 apply t92. exact h1.
Qed.
Lemma t93 : p90 -> p89.
Proof.
 intros h0.
 refine (add_fils _ _ _ i40 h0) ; finalize.
Qed.
Lemma l78 : s1 -> p89 (* BND(c0 + float<53,-1074,ne>(uh * p2) - P, [-2.26468e-23, 2.26468e-23]) *).
Proof.
 intros h0.
 assert (h1 := l79 h0).
 apply t93. exact h1.
Qed.
Definition f83 := Float2 (420287210994724901294715658149185227682883882886562109950901150200966647685254322052824051229180527652077415610397789) (-392).
Definition i62 := makepairF f83 f8.
Notation p124 := (BND _P i62). (* BND(P, [0.0416666, 1]) *)
Lemma t94 : p89 -> p124 -> p88.
Proof.
 intros h0 h1.
 refine (div_op r53 _P i40 i62 i39 h0 h1 _) ; finalize.
Qed.
Lemma l77 : s1 -> p88 (* BND((c0 + float<53,-1074,ne>(uh * p2) - P) / P, [-5.43524e-22, 5.43524e-22]) *).
Proof.
 intros h0.
 assert (h1 := l78 h0).
 assert (h2 := l13 h0).
 apply t94. exact h1. refine (subset _P i7 i62 h2 _) ; finalize.
Qed.
Lemma t95 : p12 -> p88 -> p87.
Proof.
 intros h0 h1.
 refine (rel_of_nzr_bnd r18 _P i39 h0 h1) ; finalize.
Qed.
Lemma l76 : s1 -> p87 (* REL(c0 + float<53,-1074,ne>(uh * p2), P, [-5.43524e-22, 5.43524e-22]) *).
Proof.
 intros h0.
 assert (h1 := l11 h0).
 assert (h2 := l77 h0).
 apply t95. exact h1. exact h2.
Qed.
Notation p125 := (REL r18 _P i35). (* REL(c0 + float<53,-1074,ne>(uh * p2), P, [-0.5, 1]) *)
Lemma t96 : p12 -> p125 -> p86.
Proof.
 intros h0 h1.
 refine (nzr_of_nzr_rel r18 _P i35 h0 h1 _) ; finalize.
Qed.
Lemma l75 : s1 -> p86 (* NZR(c0 + float<53,-1074,ne>(uh * p2)) *).
Proof.
 intros h0.
 assert (h1 := l11 h0).
 assert (h2 := l76 h0).
 apply t96. exact h1. refine (rel_subset r18 _P i39 i35 h2 _) ; finalize.
Qed.
Notation r62 := ((_pc - r18)%R).
Notation r61 := ((r62 / r18)%R).
Notation p126 := (BND r61 i38). (* BND((pc - (c0 + float<53,-1074,ne>(uh * p2))) / (c0 + float<53,-1074,ne>(uh * p2)), [-8.32669e-17, 8.32669e-17]) *)
Definition f84 := Float2 (-1) (-58).
Definition f85 := Float2 (1) (-58).
Definition i63 := makepairF f84 f85.
Notation p127 := (BND r62 i63). (* BND(pc - (c0 + float<53,-1074,ne>(uh * p2)), [-3.46945e-18, 3.46945e-18]) *)
Definition f86 := Float2 (1) (-4).
Definition i64 := makepairF f9 f86.
Notation p128 := (ABS r18 i64). (* ABS(c0 + float<53,-1074,ne>(uh * p2), [0.03125, 0.0625]) *)
Definition f87 := Float2 (787059479157413797401) (-74).
Definition i65 := makepairF f87 f86.
Notation p129 := (BND r18 i65). (* BND(c0 + float<53,-1074,ne>(uh * p2), [0.0416666, 0.0625]) *)
Definition f88 := Float2 (-1601320860361191) (-74).
Definition i66 := makepairF f88 f13.
Notation p130 := (BND r19 i66). (* BND(float<53,-1074,ne>(uh * p2), [-8.47732e-08, -7.34684e-40]) *)
Definition f89 := Float2 (-12810566882889529) (-77).
Definition i67 := makepairF f89 f13.
Notation p131 := (BND r20 i67). (* BND(uh * p2, [-8.47732e-08, -7.34684e-40]) *)
Lemma t97 : p35 -> p95 -> p131.
Proof.
 intros h0 h1.
 refine (mul_pn _uh _p2 i21 i44 i67 h0 h1 _) ; finalize.
Qed.
Lemma l110 : s1 -> p131 (* BND(uh * p2, [-8.47732e-08, -7.34684e-40]) *).
Proof.
 intros h0.
 assert (h1 := l30 h0).
 assert (h2 := l84 h0).
 apply t97. exact h1. exact h2.
Qed.
Lemma t98 : p131 -> p130.
Proof.
 intros h0.
 refine (float_round_ne _ _ r20 i67 i66 h0 _) ; finalize.
Qed.
Lemma l109 : s1 -> p130 (* BND(float<53,-1074,ne>(uh * p2), [-8.47732e-08, -7.34684e-40]) *).
Proof.
 intros h0.
 assert (h1 := l110 h0).
 apply t98. exact h1.
Qed.
Definition i68 := makepairF f11 f86.
Notation p132 := (BND _c0 i68). (* BND(c0, [0.0416667, 0.0625]) *)
Lemma t99 : p132 -> p130 -> p129.
Proof.
 intros h0 h1.
 refine (add _c0 r19 i68 i66 i65 h0 h1 _) ; finalize.
Qed.
Lemma l108 : s1 -> p129 (* BND(c0 + float<53,-1074,ne>(uh * p2), [0.0416666, 0.0625]) *).
Proof.
 intros h0.
 assert (h1 := l14 h0).
 assert (h2 := l109 h0).
 apply t99. refine (subset _c0 i8 i68 h1 _) ; finalize. exact h2.
Qed.
Notation p133 := (BND r18 i64). (* BND(c0 + float<53,-1074,ne>(uh * p2), [0.03125, 0.0625]) *)
Lemma t100 : p133 -> p128.
Proof.
 intros h0.
 refine (abs_of_bnd_p r18 i64 i64 h0 _) ; finalize.
Qed.
Lemma l107 : s1 -> p128 (* ABS(c0 + float<53,-1074,ne>(uh * p2), [0.03125, 0.0625]) *).
Proof.
 intros h0.
 assert (h1 := l108 h0).
 apply t100. refine (subset r18 i65 i64 h1 _) ; finalize.
Qed.
Lemma t101 : p128 -> p127.
Proof.
 intros h0.
 refine (float_absolute_wide_ne _ _ r18 i64 i63 h0 _) ; finalize.
Qed.
Lemma l106 : s1 -> p127 (* BND(pc - (c0 + float<53,-1074,ne>(uh * p2)), [-3.46945e-18, 3.46945e-18]) *).
Proof.
 intros h0.
 assert (h1 := l107 h0).
 apply t101. exact h1.
Qed.
Definition i69 := makepairF f87 f8.
Notation p134 := (BND r18 i69). (* BND(c0 + float<53,-1074,ne>(uh * p2), [0.0416666, 1]) *)
Lemma t102 : p127 -> p134 -> p126.
Proof.
 intros h0 h1.
 refine (div_op r62 r18 i63 i69 i38 h0 h1 _) ; finalize.
Qed.
Lemma l105 : s1 -> p126 (* BND((pc - (c0 + float<53,-1074,ne>(uh * p2))) / (c0 + float<53,-1074,ne>(uh * p2)), [-8.32669e-17, 8.32669e-17]) *).
Proof.
 intros h0.
 assert (h1 := l106 h0).
 assert (h2 := l108 h0).
 apply t102. exact h1. refine (subset r18 i65 i69 h2 _) ; finalize.
Qed.
Lemma t103 : p86 -> p126 -> p85.
Proof.
 intros h0 h1.
 refine (rel_of_nzr_bnd _pc r18 i38 h0 h1) ; finalize.
Qed.
Lemma l74 : s1 -> p85 (* REL(pc, c0 + float<53,-1074,ne>(uh * p2), [-8.32669e-17, 8.32669e-17]) *).
Proof.
 intros h0.
 assert (h1 := l75 h0).
 assert (h2 := l105 h0).
 apply t103. exact h1. exact h2.
Qed.
Lemma t104 : p85 -> p87 -> p84.
Proof.
 intros h0 h1.
 refine (compose _pc r18 _P i38 i39 i37 h0 h1 _) ; finalize.
Qed.
Lemma l73 : s1 -> p84 (* REL(pc, P, [-8.32674e-17, 8.32674e-17]) *).
Proof.
 intros h0.
 assert (h1 := l74 h0).
 assert (h2 := l76 h0).
 apply t104. exact h1. exact h2.
Qed.
Lemma t105 : p59 -> p84 -> p58.
Proof.
 intros h0 h1.
 refine (mul_rr _a4 r2 _pc _P i29 i37 i28 h0 h1 _) ; finalize.
Qed.
Lemma l48 : s1 -> p58 (* REL(a4 * pc, T, [-4.16334e-16, 4.16334e-16]) *).
Proof.
 intros h0.
 assert (h1 := l49 h0).
 assert (h2 := l73 h0).
 apply t105. exact h1. exact h2.
Qed.
Lemma t106 : p27 -> p58 -> p26.
Proof.
 intros h0 h1.
 refine (compose _tail r28 _T i18 i28 i3 h0 h1 _) ; finalize.
Qed.
Lemma l21 : s1 -> p26 (* REL(tail, T, [-5.27357e-16, 5.27357e-16]) *).
Proof.
 intros h0.
 assert (h1 := l22 h0).
 assert (h2 := l48 h0).
 apply t106. exact h1. exact h2.
Qed.
Lemma t107 : p4 -> p26 -> p3.
Proof.
 intros h0 h1.
 refine (bnd_of_nzr_rel _tail _T i3 h0 h1) ; finalize.
Qed.
Lemma l3 : s1 -> p3 (* BND((tail - T) / T, [-5.27357e-16, 5.27357e-16]) *).
Proof.
 intros h0.
 assert (h1 := l4 h0).
 assert (h2 := l21 h0).
 apply t107. exact h1. exact h2.
Qed.
Lemma l1 : s1 -> False.
Proof.
 intros h0.
 assert (h1 := l2 h0).
 assert (h2 := l3 h0).
 refine (simplify (Tatom false (Abnd 0%nat i2)) Tfalse (Abnd 0%nat i3) (List.cons r25 List.nil) h2 h1 _) ; finalize.
Qed.
End Generated_by_Gappa.
