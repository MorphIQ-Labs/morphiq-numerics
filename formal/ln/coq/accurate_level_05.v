Require Import Gappa.Gappa_library.
Section Generated_by_Gappa.
Notation r6 := (Float1 (1)).
Notation r7 := (Float1 (5)).
Notation r5 := ((r6 / r7)%R).
Variable _kk : R.
Notation r8 := ((r6 + _kk)%R).
Notation r4 := ((r5 * r8)%R).
Variable _z : R.
Variable _Xn : R.
Variable _En : R.
Notation _Gn := ((_Xn + _En)%R).
Notation r11 := ((_z * _Gn)%R).
Variable _m : R.
Notation r16 := ((r6 + _m)%R).
Notation r10 := ((r11 * r16)%R).
Notation r3 := ((r4 - r10)%R).
Variable _s : R.
Notation _G := ((r3 + _s)%R).
Notation r20 := ((_z * _Xn)%R).
Notation _X := ((r5 - r20)%R).
Notation r1 := ((_G - _X)%R).
Notation r23 := ((r5 * _kk)%R).
Notation r26 := ((_Gn * _m)%R).
Notation r25 := ((_En + r26)%R).
Notation r24 := ((_z * r25)%R).
Notation r22 := ((r23 - r24)%R).
Notation r21 := ((r22 + _s)%R).
Hypothesis a1 : r1 = r21.
Lemma b1 : r1 = r21.
 apply a1.
Qed.
Definition f1 := Float2 (-80696341590167128190183336492762922277553037908230366465363237155637854447075094068654269148145619287504548485417148267) (-402).
Definition f2 := Float2 (80696341590167128190183336492762922277553037908230366465363237155637854447075094068654269148145619287504548485417148267) (-402).
Definition i1 := makepairF f1 f2.
Notation p1 := (BND _z i1). (* BND(z, [-0.0078126, 0.0078126]) *)
Definition f3 := Float2 (1692872149751178959279204387557486125476630822574720199308577510158724730236087355427661289596998743574098832252845393531) (-402).
Definition f4 := Float2 (1750358248182147280040296253283000615883196219528800229735683905367219758410378714439330347044628237580281537385366137685) (-402).
Definition i2 := makepairF f3 f4.
Notation p2 := (BND _Xn i2). (* BND(Xn, [0.163895, 0.169461]) *)
Definition s6 := (p1 /\ p2).
Definition f5 := Float2 (-565) (-135).
Definition f6 := Float2 (565) (-135).
Definition i3 := makepairF f5 f6.
Notation p3 := (BND _En i3). (* BND(En, [-1.29718e-38, 1.29718e-38]) *)
Definition s5 := (s6 /\ p3).
Definition f7 := Float2 (-1) (-127).
Definition f8 := Float2 (1) (-127).
Definition i4 := makepairF f7 f8.
Notation p4 := (BND _kk i4). (* BND(kk, [-5.87747e-39, 5.87747e-39]) *)
Definition s4 := (s5 /\ p4).
Definition f9 := Float2 (0) (0).
Definition i5 := makepairF f7 f9.
Notation p5 := (BND _m i5). (* BND(m, [-5.87747e-39, 0]) *)
Definition s3 := (s4 /\ p5).
Definition f10 := Float2 (-1) (-126).
Definition f11 := Float2 (1) (-126).
Definition i6 := makepairF f10 f11.
Notation p6 := (BND _s i6). (* BND(s, [-1.17549e-38, 1.17549e-38]) *)
Definition s2 := (s3 /\ p6).
Definition f12 := Float2 (-287) (-134).
Definition f13 := Float2 (287) (-134).
Definition i7 := makepairF f12 f13.
Notation p7 := (BND r1 i7). (* BND(G - X, [-1.31784e-38, 1.31784e-38]) *)
Definition s7 := (not p7).
Definition s1 := (s2 /\ s7).
Lemma l2 : s1 -> s7.
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj2 h1).
Qed.
Definition f14 := Float2 (-1432223320229044811090663881187731027063874221110187264800475295949821826830793399710654455932494980201008774333699984191) (-525).
Definition f15 := Float2 (1432223320229044811090663881187731027063874221110187264800475295949821826830793399710654455932494980201008774333699984191) (-525).
Definition i8 := makepairF f14 f15.
Notation p8 := (BND r1 i8). (* BND(G - X, [-1.30396e-38, 1.30396e-38]) *)
Notation p9 := (BND r21 i8). (* BND(1 / 5 * kk - z * (En + Gn * m) + s, [-1.30396e-38, 1.30396e-38]) *)
Definition f16 := Float2 (-141098381185590516262704295186225089899021324695575508385145617679498015822372802395831779292426064483057188347326237503) (-525).
Definition f17 := Float2 (141098381185590516262704295186225089899021324695575508385145617679498015822372802395831779292426064483057188347326237503) (-525).
Definition i9 := makepairF f16 f17.
Notation p10 := (BND r22 i9). (* BND(1 / 5 * kk - z * (En + Gn * m), [-1.28462e-39, 1.28462e-39]) *)
Definition f18 := Float2 (-129112493904345429482795958600150593716485289641461175641532967827032381100842059731482267664006891571795158598637374669) (-525).
Definition f19 := Float2 (129112493904345429482795958600150593716485289641461175641532967827032381100842059731482267664006891571795158598637374669) (-525).
Definition i10 := makepairF f18 f19.
Notation p11 := (BND r23 i10). (* BND(1 / 5 * kk, [-1.17549e-39, 1.17549e-39]) *)
Definition f20 := Float2 (1) (-3).
Definition f21 := Float2 (129112493904345429482795958600150593716485289641461175641532967827032381100842059731482267664006891571795158598637374669) (-398).
Definition i11 := makepairF f20 f21.
Notation p12 := (BND r5 i11). (* BND(1 / 5, [0.125, 0.2]) *)
Definition f22 := Float2 (1) (0).
Definition i12 := makepairF f22 f22.
Notation p13 := (BND r6 i12). (* BND(1, [1, 1]) *)
Lemma t1 : p13.
Proof.
 refine (constant1 _ i12 _) ; finalize.
Qed.
Lemma l8 : s1 -> p13 (* BND(1, [1, 1]) *).
Proof.
 intros h0.
 apply t1.
Qed.
Definition f23 := Float2 (5) (0).
Definition f24 := Float2 (1) (3).
Definition i13 := makepairF f23 f24.
Notation p14 := (BND r7 i13). (* BND(5, [5, 8]) *)
Lemma t2 : p14.
Proof.
 refine (constant1 _ i13 _) ; finalize.
Qed.
Lemma l9 : s1 -> p14 (* BND(5, [5, 8]) *).
Proof.
 intros h0.
 apply t2.
Qed.
Lemma t3 : p13 -> p14 -> p12.
Proof.
 intros h0 h1.
 refine (div_pp r6 r7 i12 i13 i11 h0 h1 _) ; finalize.
Qed.
Lemma l7 : s1 -> p12 (* BND(1 / 5, [0.125, 0.2]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 assert (h2 := l9 h0).
 apply t3. exact h1. exact h2.
Qed.
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
Lemma l10 : s1 -> p4 (* BND(kk, [-5.87747e-39, 5.87747e-39]) *).
Proof.
 intros h0.
 assert (h1 := l11 h0).
 exact (proj2 h1).
Qed.
Lemma t4 : p12 -> p4 -> p11.
Proof.
 intros h0 h1.
 refine (mul_po r5 _kk i11 i4 i10 h0 h1 _) ; finalize.
Qed.
Lemma l6 : s1 -> p11 (* BND(1 / 5 * kk, [-1.17549e-39, 1.17549e-39]) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 assert (h2 := l10 h0).
 apply t4. exact h1. exact h2.
Qed.
Definition f25 := Float2 (-5992943640622543389954168293037248091268017527057166371806324926232817360765371332174755814209586455631014874344431417) (-524).
Definition f26 := Float2 (5992943640622543389954168293037248091268017527057166371806324926232817360765371332174755814209586455631014874344431417) (-524).
Definition i14 := makepairF f25 f26.
Notation p15 := (BND r24 i14). (* BND(z * (En + Gn * m), [-1.09125e-40, 1.09125e-40]) *)
Lemma l17 : s1 -> s5.
Proof.
 intros h0.
 assert (h1 := l11 h0).
 exact (proj1 h1).
Qed.
Lemma l16 : s1 -> s6.
Proof.
 intros h0.
 assert (h1 := l17 h0).
 exact (proj1 h1).
Qed.
Lemma l15 : s1 -> p1 (* BND(z, [-0.0078126, 0.0078126]) *).
Proof.
 intros h0.
 assert (h1 := l16 h0).
 exact (proj1 h1).
Qed.
Definition f27 := Float2 (-23971467727703258958102009466427822088949331556784738642570674800293825682092754541440892813410334170246680339869375339) (-519).
Definition f28 := Float2 (9) (-129).
Definition i15 := makepairF f27 f28.
Notation p16 := (BND r25 i15). (* BND(En + Gn * m, [-1.39678e-38, 1.32243e-38]) *)
Lemma l19 : s1 -> p3 (* BND(En, [-1.29718e-38, 1.29718e-38]) *).
Proof.
 intros h0.
 assert (h1 := l17 h0).
 exact (proj2 h1).
Qed.
Definition f29 := Float2 (-1709334226740378203164351809846680289079278868971761275179889026894992881196830545991832379400356833190935525346024299) (-519).
Definition i16 := makepairF f29 f9.
Notation p17 := (BND r26 i16). (* BND(Gn * m, [-9.96e-40, 0]) *)
Definition f30 := Float2 (1709334226740378203164351809846680289079278868971761275179889026894992881196830545991832379400356833190935525346024299) (-392).
Definition i17 := makepairF f20 f30.
Notation p18 := (BND _Gn i17). (* BND(Gn, [0.125, 0.169461]) *)
Lemma l22 : s1 -> p2 (* BND(Xn, [0.163895, 0.169461]) *).
Proof.
 intros h0.
 assert (h1 := l16 h0).
 exact (proj2 h1).
Qed.
Definition f31 := Float2 (5) (-5).
Definition f32 := Float2 (1709334226740378203164351809846680288948433808133593974351253813835175545322635463319658542035769763261993688852896619) (-392).
Definition i18 := makepairF f31 f32.
Notation p19 := (BND _Xn i18). (* BND(Xn, [0.15625, 0.169461]) *)
Definition f33 := Float2 (-1) (-5).
Definition i19 := makepairF f33 f6.
Notation p20 := (BND _En i19). (* BND(En, [-0.03125, 1.29718e-38]) *)
Lemma t5 : p19 -> p20 -> p18.
Proof.
 intros h0 h1.
 refine (add _Xn _En i18 i19 i17 h0 h1 _) ; finalize.
Qed.
Lemma l21 : s1 -> p18 (* BND(Gn, [0.125, 0.169461]) *).
Proof.
 intros h0.
 assert (h1 := l22 h0).
 assert (h2 := l19 h0).
 apply t5. refine (subset _Xn i2 i18 h1 _) ; finalize. refine (subset _En i3 i19 h2 _) ; finalize.
Qed.
Lemma l23 : s1 -> p5 (* BND(m, [-5.87747e-39, 0]) *).
Proof.
 intros h0.
 assert (h1 := l12 h0).
 exact (proj2 h1).
Qed.
Lemma t6 : p18 -> p5 -> p17.
Proof.
 intros h0 h1.
 refine (mul_pn _Gn _m i17 i5 i16 h0 h1 _) ; finalize.
Qed.
Lemma l20 : s1 -> p17 (* BND(Gn * m, [-9.96e-40, 0]) *).
Proof.
 intros h0.
 assert (h1 := l21 h0).
 assert (h2 := l23 h0).
 apply t6. exact h1. exact h2.
Qed.
Definition i20 := makepairF f5 f28.
Notation p21 := (BND _En i20). (* BND(En, [-1.29718e-38, 1.32243e-38]) *)
Lemma t7 : p21 -> p17 -> p16.
Proof.
 intros h0 h1.
 refine (add _En r26 i20 i16 i15 h0 h1 _) ; finalize.
Qed.
Lemma l18 : s1 -> p16 (* BND(En + Gn * m, [-1.39678e-38, 1.32243e-38]) *).
Proof.
 intros h0.
 assert (h1 := l19 h0).
 assert (h2 := l20 h0).
 apply t7. refine (subset _En i3 i20 h1 _) ; finalize. exact h2.
Qed.
Definition f34 := Float2 (-20174085397541782047545834123190730569388259477057591616340809288909463611768773517163567287036404821876137121354287067) (-400).
Definition f35 := Float2 (20174085397541782047545834123190730569388259477057591616340809288909463611768773517163567287036404821876137121354287067) (-400).
Definition i21 := makepairF f34 f35.
Notation p22 := (BND _z i21). (* BND(z, [-0.0078126, 0.0078126]) *)
Lemma t8 : p22 -> p16 -> p15.
Proof.
 intros h0 h1.
 refine (mul_oo _z r25 i21 i15 i14 h0 h1 _) ; finalize.
Qed.
Lemma l14 : s1 -> p15 (* BND(z * (En + Gn * m), [-1.09125e-40, 1.09125e-40]) *).
Proof.
 intros h0.
 assert (h1 := l15 h0).
 assert (h2 := l18 h0).
 apply t8. refine (subset _z i1 i21 h1 _) ; finalize. exact h2.
Qed.
Lemma t9 : p11 -> p15 -> p10.
Proof.
 intros h0 h1.
 refine (sub r23 r24 i10 i14 i9 h0 h1 _) ; finalize.
Qed.
Lemma l5 : s1 -> p10 (* BND(1 / 5 * kk - z * (En + Gn * m), [-1.28462e-39, 1.28462e-39]) *).
Proof.
 intros h0.
 assert (h1 := l6 h0).
 assert (h2 := l14 h0).
 apply t9. exact h1. exact h2.
Qed.
Lemma l24 : s1 -> p6 (* BND(s, [-1.17549e-38, 1.17549e-38]) *).
Proof.
 intros h0.
 assert (h1 := l13 h0).
 exact (proj2 h1).
Qed.
Lemma t10 : p10 -> p6 -> p9.
Proof.
 intros h0 h1.
 refine (add r22 _s i9 i6 i8 h0 h1 _) ; finalize.
Qed.
Lemma l4 : s1 -> p9 (* BND(1 / 5 * kk - z * (En + Gn * m) + s, [-1.30396e-38, 1.30396e-38]) *).
Proof.
 intros h0.
 assert (h1 := l5 h0).
 assert (h2 := l24 h0).
 apply t10. exact h1. exact h2.
Qed.
Definition i22 := makepairF f9 f9.
Notation p23 := (REL r1 r21 i22). (* REL(G - X, 1 / 5 * kk - z * (En + Gn * m) + s, [0, 0]) *)
Notation p24 := (r1 = r21). (* EQL(G - X, 1 / 5 * kk - z * (En + Gn * m) + s) *)
Lemma t11 : p24.
Proof.
 refine (b1) ; finalize.
Qed.
Lemma l26 : s1 -> p24 (* EQL(G - X, 1 / 5 * kk - z * (En + Gn * m) + s) *).
Proof.
 intros h0.
 apply t11.
Qed.
Notation p25 := (REL r21 r21 i22). (* REL(1 / 5 * kk - z * (En + Gn * m) + s, 1 / 5 * kk - z * (En + Gn * m) + s, [0, 0]) *)
Lemma t12 : p25.
Proof.
 refine (rel_refl r21 i22 _) ; finalize.
Qed.
Lemma l27 : s1 -> p25 (* REL(1 / 5 * kk - z * (En + Gn * m) + s, 1 / 5 * kk - z * (En + Gn * m) + s, [0, 0]) *).
Proof.
 intros h0.
 apply t12.
Qed.
Lemma t13 : p24 -> p25 -> p23.
Proof.
 intros h0 h1.
 refine (rel_rewrite_1 r1 r21 r21 i22 h0 h1) ; finalize.
Qed.
Lemma l25 : s1 -> p23 (* REL(G - X, 1 / 5 * kk - z * (En + Gn * m) + s, [0, 0]) *).
Proof.
 intros h0.
 assert (h1 := l26 h0).
 assert (h2 := l27 h0).
 apply t13. exact h1. exact h2.
Qed.
Lemma t14 : p9 -> p23 -> p8.
Proof.
 intros h0 h1.
 refine (bnd_of_bnd_rel_o r1 r21 i8 i22 i8 h0 h1 _) ; finalize.
Qed.
Lemma l3 : s1 -> p8 (* BND(G - X, [-1.30396e-38, 1.30396e-38]) *).
Proof.
 intros h0.
 assert (h1 := l4 h0).
 assert (h2 := l25 h0).
 apply t14. exact h1. exact h2.
Qed.
Lemma l1 : s1 -> False.
Proof.
 intros h0.
 assert (h1 := l2 h0).
 assert (h2 := l3 h0).
 refine (simplify (Tatom false (Abnd 0%nat i7)) Tfalse (Abnd 0%nat i8) (List.cons r1 List.nil) h2 h1 _) ; finalize.
Qed.
End Generated_by_Gappa.
