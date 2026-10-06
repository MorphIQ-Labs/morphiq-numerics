Require Import Gappa.Gappa_library.
Section Generated_by_Gappa.
Notation r4 := (Float1 (1)).
Variable _s : R.
Notation r12 := (Float1 (2)).
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
Definition f3 := Float2 (1212508180114480982384098273314925990462642857945313994740730702244234010365641491091748459506620539431271049171715200955) (-399).
Definition f4 := Float2 (1) (0).
Definition i2 := makepairF f3 f4.
Notation p2 := (BND _Xn i2). (* BND(Xn, [0.93911, 1]) *)
Definition s7 := (p1 /\ p2).
Definition f5 := Float2 (-293) (-262).
Definition f6 := Float2 (293) (-262).
Definition i3 := makepairF f5 f6.
Notation p3 := (BND _En i3). (* BND(En, [-3.95375e-77, 3.95375e-77]) *)
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
Definition f11 := Float2 (-939) (-263).
Definition f12 := Float2 (939) (-263).
Definition i7 := makepairF f11 f12.
Notation p8 := (BND r1 i7). (* BND(H - X, [-6.33544e-77, 6.33544e-77]) *)
Definition s8 := (not p8).
Definition s1 := (s2 /\ s8).
Lemma l2 : s1 -> s8.
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj2 h1).
Qed.
Definition f13 := Float2 (-1946002295002848754052389102667789496969928547495786997194156168835327192312040046351709291978205290495901959109329548005) (-653).
Definition f14 := Float2 (146513594020457884058418908623768997852499893879528976760409639053490738357645494593506971179325295563891672577378711765) (-649).
Definition i8 := makepairF f13 f14.
Notation p9 := (BND r1 i8). (* BND(H - X, [-5.20662e-77, 6.27207e-77]) *)
Notation p10 := (BND r25 i8). (* BND(-(s * (1 / 2) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1))) + sa, [-5.20662e-77, 6.27207e-77]) *)
Definition f15 := Float2 (-654877355959394459224429516666283559805075651081175240778826490565003381303619449036886615338136374777950373122955801317) (-653).
Definition f16 := Float2 (65818285330241990631671434498674876779696587853615741984451534161595500169619207261330553889320988331519698453230352597) (-649).
Definition i9 := makepairF f15 f16.
Notation p11 := (BND r26 i9). (* BND(-(s * (1 / 2) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1))), [-1.75216e-77, 2.8176e-77]) *)
Definition f17 := Float2 (-65818285330241990631671434498674876779696587853615741984451534161595500169619207261330553889320988331519698453230352597) (-649).
Definition f18 := Float2 (654877355959394459224429516666283559805075651081175240778826490565003381303619449036886615338136374777950373122955801317) (-653).
Definition i10 := makepairF f17 f18.
Notation p12 := (BND r27 i10). (* BND(s * (1 / 2) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1)), [-2.8176e-77, 1.75216e-77]) *)
Definition f19 := Float2 (1592860837297909563529253741250057874680279018306706523889592224082098485641088490907296736170853021321236871631389291289) (-401).
Definition i11 := makepairF f1 f19.
Notation p13 := (BND r9 i11). (* BND(s * (1 / 2), [0, 0.308425]) *)
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
Definition f20 := Float2 (1) (-1).
Definition i12 := makepairF f20 f20.
Notation p14 := (BND r11 i12). (* BND(1 / 2, [0.5, 0.5]) *)
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
Definition f21 := Float2 (1) (1).
Definition i14 := makepairF f21 f21.
Notation p16 := (BND r12 i14). (* BND(2, [2, 2]) *)
Lemma t2 : p16.
Proof.
 refine (constant1 _ i14 _) ; finalize.
Qed.
Lemma l17 : s1 -> p16 (* BND(2, [2, 2]) *).
Proof.
 intros h0.
 apply t2.
Qed.
Lemma t3 : p15 -> p16 -> p14.
Proof.
 intros h0 h1.
 refine (div_pp r4 r12 i13 i14 i12 h0 h1 _) ; finalize.
Qed.
Lemma l15 : s1 -> p14 (* BND(1 / 2, [0.5, 0.5]) *).
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
Lemma l7 : s1 -> p13 (* BND(s * (1 / 2), [0, 0.308425]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 assert (h2 := l15 h0).
 apply t4. exact h1. exact h2.
Qed.
Definition f22 := Float2 (-39195622206831532150878778425440856808331889809319330927356392186678594383119215) (-517).
Definition f23 := Float2 (24374234784455059136661692344328804603113331772117338730305821433665713789206821) (-517).
Definition i15 := makepairF f22 f23.
Notation p17 := (BND r28 i15). (* BND(En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1), [-9.13545e-77, 5.68098e-77]) *)
Lemma l19 : s1 -> p3 (* BND(En, [-3.95375e-77, 3.95375e-77]) *).
Proof.
 intros h0.
 assert (h1 := l10 h0).
 exact (proj2 h1).
Qed.
Definition f24 := Float2 (-22232081133564709521325629121668078307827837055802988295575856129519320890868591) (-517).
Definition f25 := Float2 (7410693711188236507108543040556026102609279018600996098525285376506440296956197) (-517).
Definition i16 := makepairF f24 f25.
Notation p18 := (BND r29 i16). (* BND(Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1), [-5.1817e-77, 1.72723e-77]) *)
Definition f26 := Float2 (7410693711188236507108543040556026102609279018600996098525285376506440296956197) (-262).
Definition i17 := makepairF f20 f26.
Notation p19 := (BND _Hn i17). (* BND(Hn, [0.5, 1]) *)
Lemma l22 : s1 -> p2 (* BND(Xn, [0.93911, 1]) *).
Proof.
 intros h0.
 assert (h1 := l9 h0).
 exact (proj2 h1).
Qed.
Definition f27 := Float2 (3) (-2).
Definition i18 := makepairF f27 f4.
Notation p20 := (BND _Xn i18). (* BND(Xn, [0.75, 1]) *)
Definition f28 := Float2 (-1) (-2).
Definition i19 := makepairF f28 f6.
Notation p21 := (BND _En i19). (* BND(En, [-0.25, 3.95375e-77]) *)
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
Definition f29 := Float2 (-3) (-255).
Definition i20 := makepairF f29 f8.
Notation p22 := (BND r30 i20). (* BND((1 + kk) * (1 + ma) * (1 + mb) - 1, [-5.1817e-77, 1.72723e-77]) *)
Definition f30 := Float2 (57896044618658097711785492504343953926634992332820282019728792003956564819965) (-255).
Definition f31 := Float2 (57896044618658097711785492504343953926634992332820282019728792003956564819969) (-255).
Definition i21 := makepairF f30 f31.
Notation p23 := (BND r31 i21). (* BND((1 + kk) * (1 + ma) * (1 + mb), [1, 1]) *)
Definition f32 := Float2 (28948022309329048855892746252171976963317496166410141009864396001978282409983) (-254).
Definition i22 := makepairF f32 f31.
Notation p24 := (BND r32 i22). (* BND((1 + kk) * (1 + ma), [1, 1]) *)
Definition f33 := Float2 (57896044618658097711785492504343953926634992332820282019728792003956564819967) (-255).
Definition i23 := makepairF f33 f31.
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
Definition i24 := makepairF f33 f4.
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
Lemma l18 : s1 -> p17 (* BND(En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1), [-9.13545e-77, 5.68098e-77]) *).
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
Lemma l6 : s1 -> p12 (* BND(s * (1 / 2) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1)), [-2.8176e-77, 1.75216e-77]) *).
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
Lemma l5 : s1 -> p11 (* BND(-(s * (1 / 2) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1))), [-1.75216e-77, 2.8176e-77]) *).
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
Lemma l4 : s1 -> p10 (* BND(-(s * (1 / 2) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1))) + sa, [-5.20662e-77, 6.27207e-77]) *).
Proof.
 intros h0.
 assert (h1 := l5 h0).
 assert (h2 := l32 h0).
 apply t16. exact h1. exact h2.
Qed.
Definition i25 := makepairF f1 f1.
Notation p28 := (REL r1 r25 i25). (* REL(H - X, -(s * (1 / 2) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1))) + sa, [0, 0]) *)
Notation p29 := (r1 = r25). (* EQL(H - X, -(s * (1 / 2) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1))) + sa) *)
Lemma t17 : p29.
Proof.
 refine (b1) ; finalize.
Qed.
Lemma l34 : s1 -> p29 (* EQL(H - X, -(s * (1 / 2) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1))) + sa) *).
Proof.
 intros h0.
 apply t17.
Qed.
Notation p30 := (REL r25 r25 i25). (* REL(-(s * (1 / 2) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1))) + sa, -(s * (1 / 2) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1))) + sa, [0, 0]) *)
Lemma t18 : p30.
Proof.
 refine (rel_refl r25 i25 _) ; finalize.
Qed.
Lemma l35 : s1 -> p30 (* REL(-(s * (1 / 2) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1))) + sa, -(s * (1 / 2) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1))) + sa, [0, 0]) *).
Proof.
 intros h0.
 apply t18.
Qed.
Lemma t19 : p29 -> p30 -> p28.
Proof.
 intros h0 h1.
 refine (rel_rewrite_1 r1 r25 r25 i25 h0 h1) ; finalize.
Qed.
Lemma l33 : s1 -> p28 (* REL(H - X, -(s * (1 / 2) * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1))) + sa, [0, 0]) *).
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
Lemma l3 : s1 -> p9 (* BND(H - X, [-5.20662e-77, 6.27207e-77]) *).
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
