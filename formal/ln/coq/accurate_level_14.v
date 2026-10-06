Require Import Gappa.Gappa_library.
Section Generated_by_Gappa.
Notation r6 := (Float1 (1)).
Notation r7 := (Float1 (14)).
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
Definition f3 := Float2 (676720877805677459482032182979426671002600923591784564218414450581736845157561870911466598417946847385457346309415394243) (-402).
Definition f4 := Float2 (350289963370122435607863120687077945812542574552308999819805536338083324194631534709824838145673363488877224474844491501) (-401).
Definition i2 := makepairF f3 f4.
Notation p2 := (BND _Xn i2). (* BND(Xn, [0.0655166, 0.0678265]) *)
Definition s6 := (p1 /\ p2).
Definition f5 := Float2 (-539) (-135).
Definition f6 := Float2 (539) (-135).
Definition i3 := makepairF f5 f6.
Notation p3 := (BND _En i3). (* BND(En, [-1.23748e-38, 1.23748e-38]) *)
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
Definition f12 := Float2 (-135) (-133).
Definition f13 := Float2 (135) (-133).
Definition i7 := makepairF f12 f13.
Notation p7 := (BND r1 i7). (* BND(G - X, [-1.23978e-38, 1.23978e-38]) *)
Definition s7 := (not p7).
Definition s1 := (s2 /\ s7).
Lemma l2 : s1 -> s7.
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj2 h1).
Qed.
Definition f14 := Float2 (-337049401255339753190582717317638248574689206309255508126140285392145627816837745348803986946304551729816139895323673387) (-523).
Definition f15 := Float2 (337049401255339753190582717317638248574689206309255508126140285392145627816837745348803986946304551729816139895323673387) (-523).
Definition i8 := makepairF f14 f15.
Notation p8 := (BND r1 i8). (* BND(G - X, [-1.22746e-38, 1.22746e-38]) *)
Notation p9 := (BND r21 i8). (* BND(1 / 14 * kk - z * (En + Gn * m) + s, [-1.22746e-38, 1.22746e-38]) *)
Definition f16 := Float2 (-14268166494476179483592820817261764283475982205602569022307865824564675064732596020098317786287322800328243398730236715) (-523).
Definition f17 := Float2 (14268166494476179483592820817261764283475982205602569022307865824564675064732596020098317786287322800328243398730236715) (-523).
Definition i9 := makepairF f16 f17.
Notation p10 := (BND r22 i9). (* BND(1 / 14 * kk - z * (En + Gn * m), [-5.19614e-40, 5.19614e-40]) *)
Definition f18 := Float2 (-368892839726701227093702738857573124904243684689889073261522765220092517430977313518520764754305404490843310281821070483) (-528).
Definition f19 := Float2 (368892839726701227093702738857573124904243684689889073261522765220092517430977313518520764754305404490843310281821070483) (-528).
Definition i10 := makepairF f18 f19.
Notation p11 := (BND r23 i10). (* BND(1 / 14 * kk, [-4.19819e-40, 4.19819e-40]) *)
Definition f20 := Float2 (1) (-4).
Definition f21 := Float2 (368892839726701227093702738857573124904243684689889073261522765220092517430977313518520764754305404490843310281821070483) (-401).
Definition i11 := makepairF f20 f21.
Notation p12 := (BND r5 i11). (* BND(1 / 14, [0.0625, 0.0714286]) *)
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
Definition f23 := Float2 (7) (1).
Definition f24 := Float2 (1) (4).
Definition i13 := makepairF f23 f24.
Notation p14 := (BND r7 i13). (* BND(14, [14, 16]) *)
Lemma t2 : p14.
Proof.
 refine (constant1 _ i13 _) ; finalize.
Qed.
Lemma l9 : s1 -> p14 (* BND(14, [14, 16]) *).
Proof.
 intros h0.
 apply t2.
Qed.
Lemma t3 : p13 -> p14 -> p12.
Proof.
 intros h0 h1.
 refine (div_pp r6 r7 i12 i13 i11 h0 h1 _) ; finalize.
Qed.
Lemma l7 : s1 -> p12 (* BND(1 / 14, [0.0625, 0.0714286]) *).
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
Lemma l6 : s1 -> p11 (* BND(1 / 14 * kk, [-4.19819e-40, 4.19819e-40]) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 assert (h2 := l10 h0).
 apply t4. exact h1. exact h2.
Qed.
Definition f25 := Float2 (-87688488096536516381267527294803332166987745889393135452328941165977084640465759124625404406888925119660478477546504397) (-528).
Definition f26 := Float2 (87688488096536516381267527294803332166987745889393135452328941165977084640465759124625404406888925119660478477546504397) (-528).
Definition i14 := makepairF f25 f26.
Notation p15 := (BND r24 i14). (* BND(z * (En + Gn * m), [-9.97941e-41, 9.97941e-41]) *)
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
Definition f27 := Float2 (-43843682849127789354930020543138713907955851109802362255927594709776257184140922558503953352841546188039032339159310959) (-520).
Definition f28 := Float2 (17) (-130).
Definition i15 := makepairF f27 f28.
Notation p16 := (BND r25 i15). (* BND(En + Gn * m, [-1.27735e-38, 1.24896e-38]) *)
Lemma l19 : s1 -> p3 (* BND(En, [-1.23748e-38, 1.23748e-38]) *).
Proof.
 intros h0.
 assert (h1 := l17 h0).
 exact (proj2 h1).
Qed.
Definition f29 := Float2 (-1368320169414540764093215315183898226079892176240610747879334419999369114466929519399374330075607127249487365608563311) (-520).
Definition i16 := makepairF f29 f9.
Notation p17 := (BND r26 i16). (* BND(Gn * m, [-3.98648e-40, 0]) *)
Definition f30 := Float2 (1368320169414540764093215315183898226079892176240610747879334419999369114466929519399374330075607127249487365608563311) (-393).
Definition i17 := makepairF f20 f30.
Notation p18 := (BND _Gn i17). (* BND(Gn, [0.0625, 0.0678265]) *)
Lemma l22 : s1 -> p2 (* BND(Xn, [0.0655166, 0.0678265]) *).
Proof.
 intros h0.
 assert (h1 := l16 h0).
 exact (proj2 h1).
Qed.
Definition f31 := Float2 (33) (-9).
Definition f32 := Float2 (1368320169414540764093215315183898225830244431844957030546115376320637985135279432460253274006536576128426658104861295) (-393).
Definition i18 := makepairF f31 f32.
Notation p19 := (BND _Xn i18). (* BND(Xn, [0.0644531, 0.0678265]) *)
Definition f33 := Float2 (-1) (-9).
Definition i19 := makepairF f33 f6.
Notation p20 := (BND _En i19). (* BND(En, [-0.00195312, 1.23748e-38]) *)
Lemma t5 : p19 -> p20 -> p18.
Proof.
 intros h0 h1.
 refine (add _Xn _En i18 i19 i17 h0 h1 _) ; finalize.
Qed.
Lemma l21 : s1 -> p18 (* BND(Gn, [0.0625, 0.0678265]) *).
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
Lemma l20 : s1 -> p17 (* BND(Gn * m, [-3.98648e-40, 0]) *).
Proof.
 intros h0.
 assert (h1 := l21 h0).
 assert (h2 := l23 h0).
 apply t6. exact h1. exact h2.
Qed.
Definition i20 := makepairF f5 f28.
Notation p21 := (BND _En i20). (* BND(En, [-1.23748e-38, 1.24896e-38]) *)
Lemma t7 : p21 -> p17 -> p16.
Proof.
 intros h0 h1.
 refine (add _En r26 i20 i16 i15 h0 h1 _) ; finalize.
Qed.
Lemma l18 : s1 -> p16 (* BND(En + Gn * m, [-1.27735e-38, 1.24896e-38]) *).
Proof.
 intros h0.
 assert (h1 := l19 h0).
 assert (h2 := l20 h0).
 apply t7. refine (subset _En i3 i20 h1 _) ; finalize. exact h2.
Qed.
Lemma t8 : p1 -> p16 -> p15.
Proof.
 intros h0 h1.
 refine (mul_oo _z r25 i1 i15 i14 h0 h1 _) ; finalize.
Qed.
Lemma l14 : s1 -> p15 (* BND(z * (En + Gn * m), [-9.97941e-41, 9.97941e-41]) *).
Proof.
 intros h0.
 assert (h1 := l15 h0).
 assert (h2 := l18 h0).
 apply t8. exact h1. exact h2.
Qed.
Lemma t9 : p11 -> p15 -> p10.
Proof.
 intros h0 h1.
 refine (sub r23 r24 i10 i14 i9 h0 h1 _) ; finalize.
Qed.
Lemma l5 : s1 -> p10 (* BND(1 / 14 * kk - z * (En + Gn * m), [-5.19614e-40, 5.19614e-40]) *).
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
Lemma l4 : s1 -> p9 (* BND(1 / 14 * kk - z * (En + Gn * m) + s, [-1.22746e-38, 1.22746e-38]) *).
Proof.
 intros h0.
 assert (h1 := l5 h0).
 assert (h2 := l24 h0).
 apply t10. exact h1. exact h2.
Qed.
Definition i21 := makepairF f9 f9.
Notation p22 := (REL r1 r21 i21). (* REL(G - X, 1 / 14 * kk - z * (En + Gn * m) + s, [0, 0]) *)
Notation p23 := (r1 = r21). (* EQL(G - X, 1 / 14 * kk - z * (En + Gn * m) + s) *)
Lemma t11 : p23.
Proof.
 refine (b1) ; finalize.
Qed.
Lemma l26 : s1 -> p23 (* EQL(G - X, 1 / 14 * kk - z * (En + Gn * m) + s) *).
Proof.
 intros h0.
 apply t11.
Qed.
Notation p24 := (REL r21 r21 i21). (* REL(1 / 14 * kk - z * (En + Gn * m) + s, 1 / 14 * kk - z * (En + Gn * m) + s, [0, 0]) *)
Lemma t12 : p24.
Proof.
 refine (rel_refl r21 i21 _) ; finalize.
Qed.
Lemma l27 : s1 -> p24 (* REL(1 / 14 * kk - z * (En + Gn * m) + s, 1 / 14 * kk - z * (En + Gn * m) + s, [0, 0]) *).
Proof.
 intros h0.
 apply t12.
Qed.
Lemma t13 : p23 -> p24 -> p22.
Proof.
 intros h0 h1.
 refine (rel_rewrite_1 r1 r21 r21 i21 h0 h1) ; finalize.
Qed.
Lemma l25 : s1 -> p22 (* REL(G - X, 1 / 14 * kk - z * (En + Gn * m) + s, [0, 0]) *).
Proof.
 intros h0.
 assert (h1 := l26 h0).
 assert (h2 := l27 h0).
 apply t13. exact h1. exact h2.
Qed.
Lemma t14 : p9 -> p22 -> p8.
Proof.
 intros h0 h1.
 refine (bnd_of_bnd_rel_o r1 r21 i8 i21 i8 h0 h1 _) ; finalize.
Qed.
Lemma l3 : s1 -> p8 (* BND(G - X, [-1.22746e-38, 1.22746e-38]) *).
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
