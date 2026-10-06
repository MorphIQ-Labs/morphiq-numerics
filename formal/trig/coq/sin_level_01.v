Require Import Gappa.Gappa_library.
Section Generated_by_Gappa.
Notation r4 := (Float1 (1)).
Variable _s : R.
Notation r12 := (Float1 (6)).
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
Definition f3 := Float2 (2477580767859792980364661920091103890789734923494749304769817947883177270757438902383437711306879228566142915107266248523) (-400).
Definition f4 := Float2 (1) (0).
Definition i2 := makepairF f3 f4.
Notation p2 := (BND _Xn i2). (* BND(Xn, [0.959466, 1]) *)
Definition s7 := (p1 /\ p2).
Definition f5 := Float2 (-279) (-262).
Definition f6 := Float2 (279) (-262).
Definition i3 := makepairF f5 f6.
Notation p3 := (BND _En i3). (* BND(En, [-3.76483e-77, 3.76483e-77]) *)
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
Definition f11 := Float2 (-655) (-263).
Definition f12 := Float2 (655) (-263).
Definition i7 := makepairF f11 f12.
Notation p8 := (BND r1 i7). (* BND(H - X, [-4.41929e-77, 4.41929e-77]) *)
Definition s8 := (not p8).
Definition s1 := (s2 /\ s8).
Lemma l2 : s1 -> s8.
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj2 h1).
Qed.
Definition f13 := Float2 (-1502158259609941662131477252892382745431413300207199502256170835562450791365168869374412136216450077663753996255611061623) (-653).
Definition f14 := Float2 (1634896662718100792425581731329887568321436551732758379246970187569292331835264574324882859150678551979431025657915371003) (-653).
Definition i8 := makepairF f13 f14.
Notation p9 := (BND r1 i8). (* BND(H - X, [-4.0191e-77, 4.37425e-77]) *)
Notation p10 := (BND r25 i8). (* BND(-(s * (1 / 6) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1))) + sa, [-4.0191e-77, 4.37425e-77]) *)
Definition f15 := Float2 (-211033320566487367303517666890876808266560403792587745840841157292126980356748272059589459576381161945802410269237314935) (-653).
Definition f16 := Float2 (343771723674646497597622145328381631156583655318146622831640509298968520826843977010060182510609636261479439671541624315) (-653).
Definition i9 := makepairF f15 f16.
Notation p11 := (BND r26 i9). (* BND(-(s * (1 / 6) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1))), [-5.6463e-78, 9.19778e-78]) *)
Definition f17 := Float2 (-343771723674646497597622145328381631156583655318146622831640509298968520826843977010060182510609636261479439671541624315) (-653).
Definition f18 := Float2 (211033320566487367303517666890876808266560403792587745840841157292126980356748272059589459576381161945802410269237314935) (-653).
Definition i10 := makepairF f17 f18.
Notation p12 := (BND r27 i10). (* BND(s * (1 / 6) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1)), [-9.19778e-78, 5.6463e-78]) *)
Definition f19 := Float2 (265476806216318260588208956875009645780046503051117753981598704013683080940181415151216122695142170220206145271898215215) (-400).
Definition i11 := makepairF f1 f19.
Notation p13 := (BND r9 i11). (* BND(s * (1 / 6), [0, 0.102808]) *)
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
Definition f20 := Float2 (1) (-3).
Definition f21 := Float2 (1721499918724605726437279448002007916219803861886149008553772904360431748011227463086430235520091887623935447981831662251) (-402).
Definition i12 := makepairF f20 f21.
Notation p14 := (BND r11 i12). (* BND(1 / 6, [0.125, 0.166667]) *)
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
Definition f22 := Float2 (3) (1).
Definition f23 := Float2 (1) (3).
Definition i14 := makepairF f22 f23.
Notation p16 := (BND r12 i14). (* BND(6, [6, 8]) *)
Lemma t2 : p16.
Proof.
 refine (constant1 _ i14 _) ; finalize.
Qed.
Lemma l17 : s1 -> p16 (* BND(6, [6, 8]) *).
Proof.
 intros h0.
 apply t2.
Qed.
Lemma t3 : p15 -> p16 -> p14.
Proof.
 intros h0 h1.
 refine (div_pp r4 r12 i13 i14 i12 h0 h1 _) ; finalize.
Qed.
Lemma l15 : s1 -> p14 (* BND(1 / 6, [0.125, 0.166667]) *).
Proof.
 intros h0.
 assert (h1 := l16 h0).
 assert (h2 := l17 h0).
 apply t3. exact h1. exact h2.
Qed.
Lemma t4 : p1 -> p14 -> p13.
Proof.
 intros h0 h1.
 refine (mul_pp _s r11 i1 i12 i11 h0 h1 _) ; finalize.
Qed.
Lemma l7 : s1 -> p13 (* BND(s * (1 / 6), [0, 0.102808]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 assert (h2 := l15 h0).
 apply t4. exact h1. exact h2.
Qed.
Definition f24 := Float2 (-38385077582170318782913781530380041453358999916659846979080189098623202475639621) (-517).
Definition f25 := Float2 (23563690159793845768696695449267989248140441879457854782029618345610321881727255) (-517).
Definition i15 := makepairF f24 f25.
Notation p17 := (BND r28 i15). (* BND(En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1), [-8.94653e-77, 5.49206e-77]) *)
Lemma l19 : s1 -> p3 (* BND(En, [-3.76483e-77, 3.76483e-77]) *).
Proof.
 intros h0.
 assert (h1 := l10 h0).
 exact (proj2 h1).
Qed.
Definition f26 := Float2 (-22232081133564709521325629121668078307827837055802988295575856129519320890868549) (-517).
Definition f27 := Float2 (7410693711188236507108543040556026102609279018600996098525285376506440296956183) (-517).
Definition i16 := makepairF f26 f27.
Notation p18 := (BND r29 i16). (* BND(Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1), [-5.1817e-77, 1.72723e-77]) *)
Definition f28 := Float2 (1) (-1).
Definition f29 := Float2 (7410693711188236507108543040556026102609279018600996098525285376506440296956183) (-262).
Definition i17 := makepairF f28 f29.
Notation p19 := (BND _Hn i17). (* BND(Hn, [0.5, 1]) *)
Lemma l22 : s1 -> p2 (* BND(Xn, [0.959466, 1]) *).
Proof.
 intros h0.
 assert (h1 := l9 h0).
 exact (proj2 h1).
Qed.
Definition f30 := Float2 (3) (-2).
Definition i18 := makepairF f30 f4.
Notation p20 := (BND _Xn i18). (* BND(Xn, [0.75, 1]) *)
Definition f31 := Float2 (-1) (-2).
Definition i19 := makepairF f31 f6.
Notation p21 := (BND _En i19). (* BND(En, [-0.25, 3.76483e-77]) *)
Lemma t5 : p20 -> p21 -> p19.
Proof.
 intros h0 h1.
 refine (add _Xn _En i18 i19 i17 h0 h1 _) ; finalize.
Qed.
Lemma l21 : s1 -> p19 (* BND(Hn, [0.5, 1]) *).
Proof.
 intros h0.
 assert (h1 := l22 h0).
 assert (h2 := l19 h0).
 apply t5. refine (subset _Xn i2 i18 h1 _) ; finalize. refine (subset _En i3 i19 h2 _) ; finalize.
Qed.
Definition f32 := Float2 (-3) (-255).
Definition i20 := makepairF f32 f8.
Notation p22 := (BND r30 i20). (* BND((1 + kk) * (1 + ma) * (1 + mb) - 1, [-5.1817e-77, 1.72723e-77]) *)
Definition f33 := Float2 (57896044618658097711785492504343953926634992332820282019728792003956564819965) (-255).
Definition f34 := Float2 (57896044618658097711785492504343953926634992332820282019728792003956564819969) (-255).
Definition i21 := makepairF f33 f34.
Notation p23 := (BND r31 i21). (* BND((1 + kk) * (1 + ma) * (1 + mb), [1, 1]) *)
Definition f35 := Float2 (28948022309329048855892746252171976963317496166410141009864396001978282409983) (-254).
Definition i22 := makepairF f35 f34.
Notation p24 := (BND r32 i22). (* BND((1 + kk) * (1 + ma), [1, 1]) *)
Definition f36 := Float2 (57896044618658097711785492504343953926634992332820282019728792003956564819967) (-255).
Definition i23 := makepairF f36 f34.
Notation p25 := (BND r13 i23). (* BND(1 + kk, [1, 1]) *)
Lemma l27 : s1 -> p4 (* BND(kk, [-1.72723e-77, 1.72723e-77]) *).
Proof.
 intros h0.
 assert (h1 := l11 h0).
 exact (proj2 h1).
Qed.
Lemma t6 : p15 -> p4 -> p25.
Proof.
 intros h0 h1.
 refine (add r4 _kk i13 i4 i23 h0 h1 _) ; finalize.
Qed.
Lemma l26 : s1 -> p25 (* BND(1 + kk, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l16 h0).
 assert (h2 := l27 h0).
 apply t6. exact h1. exact h2.
Qed.
Definition i24 := makepairF f36 f4.
Notation p26 := (BND r15 i24). (* BND(1 + ma, [1, 1]) *)
Lemma l29 : s1 -> p5 (* BND(ma, [-1.72723e-77, 0]) *).
Proof.
 intros h0.
 assert (h1 := l12 h0).
 exact (proj2 h1).
Qed.
Lemma t7 : p15 -> p5 -> p26.
Proof.
 intros h0 h1.
 refine (add r4 _ma i13 i5 i24 h0 h1 _) ; finalize.
Qed.
Lemma l28 : s1 -> p26 (* BND(1 + ma, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l16 h0).
 assert (h2 := l29 h0).
 apply t7. exact h1. exact h2.
Qed.
Lemma t8 : p25 -> p26 -> p24.
Proof.
 intros h0 h1.
 refine (mul_pp r13 r15 i23 i24 i22 h0 h1 _) ; finalize.
Qed.
Lemma l25 : s1 -> p24 (* BND((1 + kk) * (1 + ma), [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l26 h0).
 assert (h2 := l28 h0).
 apply t8. exact h1. exact h2.
Qed.
Notation p27 := (BND r20 i24). (* BND(1 + mb, [1, 1]) *)
Lemma l31 : s1 -> p6 (* BND(mb, [-1.72723e-77, 0]) *).
Proof.
 intros h0.
 assert (h1 := l13 h0).
 exact (proj2 h1).
Qed.
Lemma t9 : p15 -> p6 -> p27.
Proof.
 intros h0 h1.
 refine (add r4 _mb i13 i5 i24 h0 h1 _) ; finalize.
Qed.
Lemma l30 : s1 -> p27 (* BND(1 + mb, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l16 h0).
 assert (h2 := l31 h0).
 apply t9. exact h1. exact h2.
Qed.
Lemma t10 : p24 -> p27 -> p23.
Proof.
 intros h0 h1.
 refine (mul_pp r32 r20 i22 i24 i21 h0 h1 _) ; finalize.
Qed.
Lemma l24 : s1 -> p23 (* BND((1 + kk) * (1 + ma) * (1 + mb), [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l25 h0).
 assert (h2 := l30 h0).
 apply t10. exact h1. exact h2.
Qed.
Lemma t11 : p23 -> p15 -> p22.
Proof.
 intros h0 h1.
 refine (sub r31 r4 i21 i13 i20 h0 h1 _) ; finalize.
Qed.
Lemma l23 : s1 -> p22 (* BND((1 + kk) * (1 + ma) * (1 + mb) - 1, [-5.1817e-77, 1.72723e-77]) *).
Proof.
 intros h0.
 assert (h1 := l24 h0).
 assert (h2 := l16 h0).
 apply t11. exact h1. exact h2.
Qed.
Lemma t12 : p19 -> p22 -> p18.
Proof.
 intros h0 h1.
 refine (mul_po _Hn r30 i17 i20 i16 h0 h1 _) ; finalize.
Qed.
Lemma l20 : s1 -> p18 (* BND(Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1), [-5.1817e-77, 1.72723e-77]) *).
Proof.
 intros h0.
 assert (h1 := l21 h0).
 assert (h2 := l23 h0).
 apply t12. exact h1. exact h2.
Qed.
Lemma t13 : p3 -> p18 -> p17.
Proof.
 intros h0 h1.
 refine (add _En r29 i3 i16 i15 h0 h1 _) ; finalize.
Qed.
Lemma l18 : s1 -> p17 (* BND(En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1), [-8.94653e-77, 5.49206e-77]) *).
Proof.
 intros h0.
 assert (h1 := l19 h0).
 assert (h2 := l20 h0).
 apply t13. exact h1. exact h2.
Qed.
Lemma t14 : p13 -> p17 -> p12.
Proof.
 intros h0 h1.
 refine (mul_po r9 r28 i11 i15 i10 h0 h1 _) ; finalize.
Qed.
Lemma l6 : s1 -> p12 (* BND(s * (1 / 6) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1)), [-9.19778e-78, 5.6463e-78]) *).
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
Lemma l5 : s1 -> p11 (* BND(-(s * (1 / 6) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1))), [-5.6463e-78, 9.19778e-78]) *).
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
Lemma l4 : s1 -> p10 (* BND(-(s * (1 / 6) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1))) + sa, [-4.0191e-77, 4.37425e-77]) *).
Proof.
 intros h0.
 assert (h1 := l5 h0).
 assert (h2 := l32 h0).
 apply t16. exact h1. exact h2.
Qed.
Definition i25 := makepairF f1 f1.
Notation p28 := (REL r1 r25 i25). (* REL(H - X, -(s * (1 / 6) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1))) + sa, [0, 0]) *)
Notation p29 := (r1 = r25). (* EQL(H - X, -(s * (1 / 6) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1))) + sa) *)
Lemma t17 : p29.
Proof.
 refine (b1) ; finalize.
Qed.
Lemma l34 : s1 -> p29 (* EQL(H - X, -(s * (1 / 6) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1))) + sa) *).
Proof.
 intros h0.
 apply t17.
Qed.
Notation p30 := (REL r25 r25 i25). (* REL(-(s * (1 / 6) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1))) + sa, -(s * (1 / 6) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1))) + sa, [0, 0]) *)
Lemma t18 : p30.
Proof.
 refine (rel_refl r25 i25 _) ; finalize.
Qed.
Lemma l35 : s1 -> p30 (* REL(-(s * (1 / 6) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1))) + sa, -(s * (1 / 6) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1))) + sa, [0, 0]) *).
Proof.
 intros h0.
 apply t18.
Qed.
Lemma t19 : p29 -> p30 -> p28.
Proof.
 intros h0 h1.
 refine (rel_rewrite_1 r1 r25 r25 i25 h0 h1) ; finalize.
Qed.
Lemma l33 : s1 -> p28 (* REL(H - X, -(s * (1 / 6) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1))) + sa, [0, 0]) *).
Proof.
 intros h0.
 assert (h1 := l34 h0).
 assert (h2 := l35 h0).
 apply t19. exact h1. exact h2.
Qed.
Lemma t20 : p10 -> p28 -> p9.
Proof.
 intros h0 h1.
 refine (bnd_of_bnd_rel_o r1 r25 i8 i25 i8 h0 h1 _) ; finalize.
Qed.
Lemma l3 : s1 -> p9 (* BND(H - X, [-4.0191e-77, 4.37425e-77]) *).
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
