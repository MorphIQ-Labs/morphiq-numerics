Require Import Gappa.Gappa_library.
Section Generated_by_Gappa.
Notation r4 := (Float1 (1)).
Variable _s : R.
Notation r12 := (Float1 (132)).
Notation r11 := ((r4 / r12)%R).
Notation r9 := ((_s * r11)%R).
Variable _kk : R.
Notation r13 := ((r4 + _kk)%R).
Notation r8 := ((r9 * r13)%R).
Variable _ma : R.
Notation r15 := ((r4 + _ma)%R).
Notation r7 := ((r8 * r15)%R).
Variable _Xn : R.
Variable _En : R.
Notation _Hn := ((_Xn + _En)%R).
Notation r6 := ((r7 * _Hn)%R).
Variable _mb : R.
Notation r20 := ((r4 + _mb)%R).
Notation _b := ((r6 * r20)%R).
Notation r3 := ((r4 - _b)%R).
Variable _sa : R.
Notation _H := ((r3 + _sa)%R).
Notation r24 := ((r9 * _Xn)%R).
Notation _X := ((r4 - r24)%R).
Notation r1 := ((_H - _X)%R).
Notation r32 := ((r13 * r15)%R).
Notation r31 := ((r32 * r20)%R).
Notation r30 := ((r31 - r4)%R).
Notation r29 := ((_Hn * r30)%R).
Notation r28 := ((_En + r29)%R).
Notation r27 := ((r9 * r28)%R).
Notation r26 := ((- r27)%R).
Notation r25 := ((r26 + _sa)%R).
Hypothesis a1 : r1 = r25.
Lemma b1 : r1 = r25.
 apply a1.
Qed.
Definition f1 := Float2 (0) (0).
Definition f2 := Float2 (1592860837297909563529253741250057874680279018306706523889592224082098485641088490907296736170853021321236871631389291289) (-400).
Definition i1 := makepairF f1 f2.
Notation p1 := (BND _s i1). (* BND(s, [0, 0.61685]) *)
Definition f3 := Float2 (79617591129401744915187144896396157923886436262237895341623917449528754767196588370524279691764304737590904087534527041) (-395).
Definition f4 := Float2 (1) (0).
Definition i2 := makepairF f3 f4.
Notation p2 := (BND _Xn i2). (* BND(Xn, [0.986645, 1]) *)
Definition s7 := (p1 /\ p2).
Definition f5 := Float2 (-261) (-262).
Definition f6 := Float2 (261) (-262).
Definition i3 := makepairF f5 f6.
Notation p3 := (BND _En i3). (* BND(En, [-3.52194e-77, 3.52194e-77]) *)
Definition s6 := (s7 /\ p3).
Definition f7 := Float2 (-1) (-255).
Definition f8 := Float2 (1) (-255).
Definition i4 := makepairF f7 f8.
Notation p4 := (BND _kk i4). (* BND(kk, [-1.72723e-77, 1.72723e-77]) *)
Definition s5 := (s6 /\ p4).
Definition i5 := makepairF f7 f1.
Notation p5 := (BND _ma i5). (* BND(ma, [-1.72723e-77, 0]) *)
Definition s4 := (s5 /\ p5).
Notation p6 := (BND _mb i5). (* BND(mb, [-1.72723e-77, 0]) *)
Definition s3 := (s4 /\ p6).
Definition f9 := Float2 (-1) (-254).
Definition f10 := Float2 (1) (-254).
Definition i6 := makepairF f9 f10.
Notation p7 := (BND _sa i6). (* BND(sa, [-3.45447e-77, 3.45447e-77]) *)
Definition s2 := (s3 /\ p7).
Definition f11 := Float2 (-131) (-261).
Definition f12 := Float2 (131) (-261).
Definition i7 := makepairF f11 f12.
Notation p8 := (BND r1 i7). (* BND(H - X, [-3.53543e-77, 3.53543e-77]) *)
Definition s8 := (not p8).
Definition s1 := (s2 /\ s8).
Lemma l2 : s1 -> s8.
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj2 h1).
Qed.
Definition f13 := Float2 (-325073281938112947893975276565725799636748515511831312823178164770468974735542022714814064463925815726239499491624166599) (-651).
Definition f14 := Float2 (1306326691530095388407451309828244326860176937116668836610476265991277787145354244611037587896447790654774478901890688665) (-653).
Definition i8 := makepairF f13 f14.
Notation p9 := (BND r1 i8). (* BND(H - X, [-3.479e-77, 3.49514e-77]) *)
Notation p10 := (BND r25 i8). (* BND(-(s * (1 / 132) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1))) + sa, [-3.479e-77, 3.49514e-77]) *)
Definition f15 := Float2 (-2292047177249374186985380065349315345535291408178373719345745202888021983436873386108395303908586796751602995030729927) (-651).
Definition f16 := Float2 (15201752486641093579491723826738389695324040702057080195146587720953976136933647296214911256378874936822892915516941977) (-653).
Definition i9 := makepairF f15 f16.
Notation p11 := (BND r26 i9). (* BND(-(s * (1 / 132) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1))), [-2.45299e-79, 4.0673e-79]) *)
Definition f17 := Float2 (-15201752486641093579491723826738389695324040702057080195146587720953976136933647296214911256378874936822892915516941977) (-653).
Definition f18 := Float2 (2292047177249374186985380065349315345535291408178373719345745202888021983436873386108395303908586796751602995030729927) (-651).
Definition i10 := makepairF f17 f18.
Notation p12 := (BND r27 i10). (* BND(s * (1 / 132) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1)), [-4.0673e-79, 2.45299e-79]) *)
Definition f19 := Float2 (1508390944410899207887550891335282078295718767335896329440901727350472050796485313359182515313307785342080370863058041) (-397).
Definition i11 := makepairF f1 f19.
Notation p13 := (BND r9 i11). (* BND(s * (1 / 132), [0, 0.00467311]) *)
Lemma l14 : s1 -> s2.
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj1 h1).
Qed.
Lemma l13 : s1 -> s3.
Proof.
 intros h0.
 assert (h1 := l14 h0).
 exact (proj1 h1).
Qed.
Lemma l12 : s1 -> s4.
Proof.
 intros h0.
 assert (h1 := l13 h0).
 exact (proj1 h1).
Qed.
Lemma l11 : s1 -> s5.
Proof.
 intros h0.
 assert (h1 := l12 h0).
 exact (proj1 h1).
Qed.
Lemma l10 : s1 -> s6.
Proof.
 intros h0.
 assert (h1 := l11 h0).
 exact (proj1 h1).
Qed.
Lemma l9 : s1 -> s7.
Proof.
 intros h0.
 assert (h1 := l10 h0).
 exact (proj1 h1).
Qed.
Lemma l8 : s1 -> p1 (* BND(s, [0, 0.61685]) *).
Proof.
 intros h0.
 assert (h1 := l9 h0).
 exact (proj1 h1).
Qed.
Definition f20 := Float2 (1) (-8).
Definition f21 := Float2 (625999970445311173249919799273457424079928677049508730383190147040156999276809986576883722007306140954158344720666059001) (-405).
Definition i12 := makepairF f20 f21.
Notation p14 := (BND r11 i12). (* BND(1 / 132, [0.00390625, 0.00757576]) *)
Definition i13 := makepairF f4 f4.
Notation p15 := (BND r4 i13). (* BND(1, [1, 1]) *)
Lemma t1 : p15.
Proof.
 refine (constant1 _ i13 _) ; finalize.
Qed.
Lemma l16 : s1 -> p15 (* BND(1, [1, 1]) *).
Proof.
 intros h0.
 apply t1.
Qed.
Definition f22 := Float2 (33) (2).
Definition f23 := Float2 (1) (8).
Definition i14 := makepairF f22 f23.
Notation p16 := (BND r12 i14). (* BND(132, [132, 256]) *)
Lemma t2 : p16.
Proof.
 refine (constant1 _ i14 _) ; finalize.
Qed.
Lemma l17 : s1 -> p16 (* BND(132, [132, 256]) *).
Proof.
 intros h0.
 apply t2.
Qed.
Lemma t3 : p15 -> p16 -> p14.
Proof.
 intros h0 h1.
 refine (div_pp r4 r12 i13 i14 i12 h0 h1 _) ; finalize.
Qed.
Lemma l15 : s1 -> p14 (* BND(1 / 132, [0.00390625, 0.00757576]) *).
Proof.
 intros h0.
 assert (h1 := l16 h0).
 assert (h2 := l17 h0).
 apply t3. exact h1. exact h2.
Qed.
Definition f24 := Float2 (398215209324477390882313435312514468670069754576676630972398056020524621410272122726824184042713255330309217907847322823) (-398).
Definition i15 := makepairF f1 f24.
Notation p17 := (BND _s i15). (* BND(s, [0, 0.61685]) *)
Lemma t4 : p17 -> p14 -> p13.
Proof.
 intros h0 h1.
 refine (mul_pp _s r11 i15 i12 i11 h0 h1 _) ; finalize.
Qed.
Lemma l7 : s1 -> p13 (* BND(s * (1 / 132), [0, 0.00467311]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 assert (h2 := l15 h0).
 apply t4. refine (subset _s i1 i15 h1 _) ; finalize. exact h2.
Qed.
Definition f25 := Float2 (-37342948779034473024101642665301850282679570054669081902725070842551984308880143) (-517).
Definition f26 := Float2 (22521561356658000009884556584189798077461012017467089705674500089539103714967813) (-517).
Definition i16 := makepairF f25 f26.
Notation p18 := (BND r28 i16). (* BND(En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1), [-8.70364e-77, 5.24917e-77]) *)
Lemma l19 : s1 -> p3 (* BND(En, [-3.52194e-77, 3.52194e-77]) *).
Proof.
 intros h0.
 assert (h1 := l10 h0).
 exact (proj2 h1).
Qed.
Definition f27 := Float2 (-22232081133564709521325629121668078307827837055802988295575856129519320890868495) (-517).
Definition f28 := Float2 (7410693711188236507108543040556026102609279018600996098525285376506440296956165) (-517).
Definition i17 := makepairF f27 f28.
Notation p19 := (BND r29 i17). (* BND(Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1), [-5.1817e-77, 1.72723e-77]) *)
Definition f29 := Float2 (1) (-1).
Definition f30 := Float2 (7410693711188236507108543040556026102609279018600996098525285376506440296956165) (-262).
Definition i18 := makepairF f29 f30.
Notation p20 := (BND _Hn i18). (* BND(Hn, [0.5, 1]) *)
Lemma l22 : s1 -> p2 (* BND(Xn, [0.986645, 1]) *).
Proof.
 intros h0.
 assert (h1 := l9 h0).
 exact (proj2 h1).
Qed.
Definition f31 := Float2 (3) (-2).
Definition i19 := makepairF f31 f4.
Notation p21 := (BND _Xn i19). (* BND(Xn, [0.75, 1]) *)
Definition f32 := Float2 (-1) (-2).
Definition i20 := makepairF f32 f6.
Notation p22 := (BND _En i20). (* BND(En, [-0.25, 3.52194e-77]) *)
Lemma t5 : p21 -> p22 -> p20.
Proof.
 intros h0 h1.
 refine (add _Xn _En i19 i20 i18 h0 h1 _) ; finalize.
Qed.
Lemma l21 : s1 -> p20 (* BND(Hn, [0.5, 1]) *).
Proof.
 intros h0.
 assert (h1 := l22 h0).
 assert (h2 := l19 h0).
 apply t5. refine (subset _Xn i2 i19 h1 _) ; finalize. refine (subset _En i3 i20 h2 _) ; finalize.
Qed.
Definition f33 := Float2 (-3) (-255).
Definition i21 := makepairF f33 f8.
Notation p23 := (BND r30 i21). (* BND((1 + kk) * (1 + ma) * (1 + mb) - 1, [-5.1817e-77, 1.72723e-77]) *)
Definition f34 := Float2 (57896044618658097711785492504343953926634992332820282019728792003956564819965) (-255).
Definition f35 := Float2 (57896044618658097711785492504343953926634992332820282019728792003956564819969) (-255).
Definition i22 := makepairF f34 f35.
Notation p24 := (BND r31 i22). (* BND((1 + kk) * (1 + ma) * (1 + mb), [1, 1]) *)
Definition f36 := Float2 (28948022309329048855892746252171976963317496166410141009864396001978282409983) (-254).
Definition i23 := makepairF f36 f35.
Notation p25 := (BND r32 i23). (* BND((1 + kk) * (1 + ma), [1, 1]) *)
Definition f37 := Float2 (57896044618658097711785492504343953926634992332820282019728792003956564819967) (-255).
Definition i24 := makepairF f37 f35.
Notation p26 := (BND r13 i24). (* BND(1 + kk, [1, 1]) *)
Lemma l27 : s1 -> p4 (* BND(kk, [-1.72723e-77, 1.72723e-77]) *).
Proof.
 intros h0.
 assert (h1 := l11 h0).
 exact (proj2 h1).
Qed.
Lemma t6 : p15 -> p4 -> p26.
Proof.
 intros h0 h1.
 refine (add r4 _kk i13 i4 i24 h0 h1 _) ; finalize.
Qed.
Lemma l26 : s1 -> p26 (* BND(1 + kk, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l16 h0).
 assert (h2 := l27 h0).
 apply t6. exact h1. exact h2.
Qed.
Definition i25 := makepairF f37 f4.
Notation p27 := (BND r15 i25). (* BND(1 + ma, [1, 1]) *)
Lemma l29 : s1 -> p5 (* BND(ma, [-1.72723e-77, 0]) *).
Proof.
 intros h0.
 assert (h1 := l12 h0).
 exact (proj2 h1).
Qed.
Lemma t7 : p15 -> p5 -> p27.
Proof.
 intros h0 h1.
 refine (add r4 _ma i13 i5 i25 h0 h1 _) ; finalize.
Qed.
Lemma l28 : s1 -> p27 (* BND(1 + ma, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l16 h0).
 assert (h2 := l29 h0).
 apply t7. exact h1. exact h2.
Qed.
Lemma t8 : p26 -> p27 -> p25.
Proof.
 intros h0 h1.
 refine (mul_pp r13 r15 i24 i25 i23 h0 h1 _) ; finalize.
Qed.
Lemma l25 : s1 -> p25 (* BND((1 + kk) * (1 + ma), [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l26 h0).
 assert (h2 := l28 h0).
 apply t8. exact h1. exact h2.
Qed.
Notation p28 := (BND r20 i25). (* BND(1 + mb, [1, 1]) *)
Lemma l31 : s1 -> p6 (* BND(mb, [-1.72723e-77, 0]) *).
Proof.
 intros h0.
 assert (h1 := l13 h0).
 exact (proj2 h1).
Qed.
Lemma t9 : p15 -> p6 -> p28.
Proof.
 intros h0 h1.
 refine (add r4 _mb i13 i5 i25 h0 h1 _) ; finalize.
Qed.
Lemma l30 : s1 -> p28 (* BND(1 + mb, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l16 h0).
 assert (h2 := l31 h0).
 apply t9. exact h1. exact h2.
Qed.
Lemma t10 : p25 -> p28 -> p24.
Proof.
 intros h0 h1.
 refine (mul_pp r32 r20 i23 i25 i22 h0 h1 _) ; finalize.
Qed.
Lemma l24 : s1 -> p24 (* BND((1 + kk) * (1 + ma) * (1 + mb), [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l25 h0).
 assert (h2 := l30 h0).
 apply t10. exact h1. exact h2.
Qed.
Lemma t11 : p24 -> p15 -> p23.
Proof.
 intros h0 h1.
 refine (sub r31 r4 i22 i13 i21 h0 h1 _) ; finalize.
Qed.
Lemma l23 : s1 -> p23 (* BND((1 + kk) * (1 + ma) * (1 + mb) - 1, [-5.1817e-77, 1.72723e-77]) *).
Proof.
 intros h0.
 assert (h1 := l24 h0).
 assert (h2 := l16 h0).
 apply t11. exact h1. exact h2.
Qed.
Lemma t12 : p20 -> p23 -> p19.
Proof.
 intros h0 h1.
 refine (mul_po _Hn r30 i18 i21 i17 h0 h1 _) ; finalize.
Qed.
Lemma l20 : s1 -> p19 (* BND(Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1), [-5.1817e-77, 1.72723e-77]) *).
Proof.
 intros h0.
 assert (h1 := l21 h0).
 assert (h2 := l23 h0).
 apply t12. exact h1. exact h2.
Qed.
Lemma t13 : p3 -> p19 -> p18.
Proof.
 intros h0 h1.
 refine (add _En r29 i3 i17 i16 h0 h1 _) ; finalize.
Qed.
Lemma l18 : s1 -> p18 (* BND(En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1), [-8.70364e-77, 5.24917e-77]) *).
Proof.
 intros h0.
 assert (h1 := l19 h0).
 assert (h2 := l20 h0).
 apply t13. exact h1. exact h2.
Qed.
Lemma t14 : p13 -> p18 -> p12.
Proof.
 intros h0 h1.
 refine (mul_po r9 r28 i11 i16 i10 h0 h1 _) ; finalize.
Qed.
Lemma l6 : s1 -> p12 (* BND(s * (1 / 132) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1)), [-4.0673e-79, 2.45299e-79]) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 assert (h2 := l18 h0).
 apply t14. exact h1. exact h2.
Qed.
Lemma t15 : p12 -> p11.
Proof.
 intros h0.
 refine (neg r27 i10 i9 h0 _) ; finalize.
Qed.
Lemma l5 : s1 -> p11 (* BND(-(s * (1 / 132) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1))), [-2.45299e-79, 4.0673e-79]) *).
Proof.
 intros h0.
 assert (h1 := l6 h0).
 apply t15. exact h1.
Qed.
Lemma l32 : s1 -> p7 (* BND(sa, [-3.45447e-77, 3.45447e-77]) *).
Proof.
 intros h0.
 assert (h1 := l14 h0).
 exact (proj2 h1).
Qed.
Lemma t16 : p11 -> p7 -> p10.
Proof.
 intros h0 h1.
 refine (add r26 _sa i9 i6 i8 h0 h1 _) ; finalize.
Qed.
Lemma l4 : s1 -> p10 (* BND(-(s * (1 / 132) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1))) + sa, [-3.479e-77, 3.49514e-77]) *).
Proof.
 intros h0.
 assert (h1 := l5 h0).
 assert (h2 := l32 h0).
 apply t16. exact h1. exact h2.
Qed.
Definition i26 := makepairF f1 f1.
Notation p29 := (REL r1 r25 i26). (* REL(H - X, -(s * (1 / 132) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1))) + sa, [0, 0]) *)
Notation p30 := (r1 = r25). (* EQL(H - X, -(s * (1 / 132) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1))) + sa) *)
Lemma t17 : p30.
Proof.
 refine (b1) ; finalize.
Qed.
Lemma l34 : s1 -> p30 (* EQL(H - X, -(s * (1 / 132) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1))) + sa) *).
Proof.
 intros h0.
 apply t17.
Qed.
Notation p31 := (REL r25 r25 i26). (* REL(-(s * (1 / 132) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1))) + sa, -(s * (1 / 132) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1))) + sa, [0, 0]) *)
Lemma t18 : p31.
Proof.
 refine (rel_refl r25 i26 _) ; finalize.
Qed.
Lemma l35 : s1 -> p31 (* REL(-(s * (1 / 132) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1))) + sa, -(s * (1 / 132) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1))) + sa, [0, 0]) *).
Proof.
 intros h0.
 apply t18.
Qed.
Lemma t19 : p30 -> p31 -> p29.
Proof.
 intros h0 h1.
 refine (rel_rewrite_1 r1 r25 r25 i26 h0 h1) ; finalize.
Qed.
Lemma l33 : s1 -> p29 (* REL(H - X, -(s * (1 / 132) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1))) + sa, [0, 0]) *).
Proof.
 intros h0.
 assert (h1 := l34 h0).
 assert (h2 := l35 h0).
 apply t19. exact h1. exact h2.
Qed.
Lemma t20 : p10 -> p29 -> p9.
Proof.
 intros h0 h1.
 refine (bnd_of_bnd_rel_o r1 r25 i8 i26 i8 h0 h1 _) ; finalize.
Qed.
Lemma l3 : s1 -> p9 (* BND(H - X, [-3.479e-77, 3.49514e-77]) *).
Proof.
 intros h0.
 assert (h1 := l4 h0).
 assert (h2 := l33 h0).
 apply t20. exact h1. exact h2.
Qed.
Lemma l1 : s1 -> False.
Proof.
 intros h0.
 assert (h1 := l2 h0).
 assert (h2 := l3 h0).
 refine (simplify (Tatom false (Abnd 0%nat i7)) Tfalse (Abnd 0%nat i8) (List.cons r1 List.nil) h2 h1 _) ; finalize.
Qed.
End Generated_by_Gappa.
