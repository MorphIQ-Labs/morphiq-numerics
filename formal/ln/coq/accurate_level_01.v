Require Import Gappa.Gappa_library.
Section Generated_by_Gappa.
Notation r6 := (Float1 (1)).
Notation r5 := ((r6 / r6)%R).
Variable _kk : R.
Notation r7 := ((r6 + _kk)%R).
Notation r4 := ((r5 * r7)%R).
Variable _z : R.
Variable _Xn : R.
Variable _En : R.
Notation _Gn := ((_Xn + _En)%R).
Notation r10 := ((_z * _Gn)%R).
Variable _m : R.
Notation r15 := ((r6 + _m)%R).
Notation r9 := ((r10 * r15)%R).
Notation r3 := ((r4 - r9)%R).
Variable _s : R.
Notation _G := ((r3 + _s)%R).
Notation r19 := ((_z * _Xn)%R).
Notation _X := ((r5 - r19)%R).
Notation r1 := ((_G - _X)%R).
Notation r22 := ((r5 * _kk)%R).
Notation r25 := ((_Gn * _m)%R).
Notation r24 := ((_En + r25)%R).
Notation r23 := ((_z * r24)%R).
Notation r21 := ((r22 - r23)%R).
Notation r20 := ((r21 + _s)%R).
Hypothesis a1 : r1 = r20.
Lemma b1 : r1 = r20.
 apply a1.
Qed.
Definition f1 := Float2 (-80696341590167128190183336492762922277553037908230366465363237155637854447075094068654269148145619287504548485417148267) (-402).
Definition f2 := Float2 (80696341590167128190183336492762922277553037908230366465363237155637854447075094068654269148145619287504548485417148267) (-402).
Definition i1 := makepairF f1 f2.
Notation p1 := (BND _z i1). (* BND(z, [-0.0078126, 0.0078126]) *)
Definition f3 := Float2 (1271556241471830963803989864880837936705306241823036633617783914422280449906452696081010472668946212969552944876463094489) (-400).
Definition f4 := Float2 (327707032629431976099728236504082135623715534850675149122579428545073308800283405926353992764942965291290683669273356867) (-398).
Definition i2 := makepairF f3 f4.
Notation p2 := (BND _Xn i2). (* BND(Xn, [0.492422, 0.50763]) *)
Definition s6 := (p1 /\ p2).
Definition f5 := Float2 (-163) (-133).
Definition f6 := Float2 (163) (-133).
Definition i3 := makepairF f5 f6.
Notation p3 := (BND _En i3). (* BND(En, [-1.49692e-38, 1.49692e-38]) *)
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
Definition f12 := Float2 (-391) (-134).
Definition f13 := Float2 (391) (-134).
Definition i7 := makepairF f12 f13.
Notation p7 := (BND r1 i7). (* BND(G - X, [-1.79538e-38, 1.79538e-38]) *)
Definition s7 := (not p7).
Definition s1 := (s2 /\ s7).
Lemma l2 : s1 -> s7.
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj2 h1).
Qed.
Definition f14 := Float2 (-244011608870627274879562742486674505727482045357117121600419848740317431972930753085313464993230636932838929464312192253) (-522).
Definition f15 := Float2 (244011608870627274879562742486674505727482045357117121600419848740317431972930753085313464993230636932838929464312192253) (-522).
Definition i8 := makepairF f14 f15.
Notation p8 := (BND r1 i8). (* BND(G - X, [-1.77727e-38, 1.77727e-38]) *)
Notation p9 := (BND r20 i8). (* BND(1 / 1 * kk - z * (En + Gn * m) + s, [-1.77727e-38, 1.77727e-38]) *)
Definition f16 := Float2 (-82620991490195488026067794236486263581875433305290652048503638956526955596878178420960630413222022468094981216015473917) (-522).
Definition f17 := Float2 (82620991490195488026067794236486263581875433305290652048503638956526955596878178420960630413222022468094981216015473917) (-522).
Definition i9 := makepairF f16 f17.
Notation p10 := (BND r21 i9). (* BND(1 / 1 * kk - z * (En + Gn * m), [-6.01773e-39, 6.01773e-39]) *)
Notation p11 := (BND r22 i4). (* BND(1 / 1 * kk, [-5.87747e-39, 5.87747e-39]) *)
Definition f18 := Float2 (1) (0).
Definition i10 := makepairF f18 f18.
Notation p12 := (BND r5 i10). (* BND(1 / 1, [1, 1]) *)
Notation p13 := (NZR r6). (* NZR(1) *)
Notation p14 := (ABS r6 i10). (* ABS(1, [1, 1]) *)
Notation p15 := (BND r6 i10). (* BND(1, [1, 1]) *)
Lemma t1 : p15.
Proof.
 refine (constant1 _ i10 _) ; finalize.
Qed.
Lemma l10 : s1 -> p15 (* BND(1, [1, 1]) *).
Proof.
 intros h0.
 apply t1.
Qed.
Lemma t2 : p15 -> p14.
Proof.
 intros h0.
 refine (abs_of_bnd_p r6 i10 i10 h0 _) ; finalize.
Qed.
Lemma l9 : s1 -> p14 (* ABS(1, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l10 h0).
 apply t2. exact h1.
Qed.
Lemma t3 : p14 -> p13.
Proof.
 intros h0.
 refine (nzr_of_abs r6 i10 h0 _) ; finalize.
Qed.
Lemma l8 : s1 -> p13 (* NZR(1) *).
Proof.
 intros h0.
 assert (h1 := l9 h0).
 apply t3. exact h1.
Qed.
Lemma t4 : p13 -> p12.
Proof.
 intros h0.
 refine (div_refl r6 i10 h0 _) ; finalize.
Qed.
Lemma l7 : s1 -> p12 (* BND(1 / 1, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 apply t4. exact h1.
Qed.
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
Lemma l11 : s1 -> p4 (* BND(kk, [-5.87747e-39, 5.87747e-39]) *).
Proof.
 intros h0.
 assert (h1 := l12 h0).
 exact (proj2 h1).
Qed.
Lemma t5 : p12 -> p4 -> p11.
Proof.
 intros h0 h1.
 refine (mul_po r5 _kk i10 i4 i4 h0 h1 _) ; finalize.
Qed.
Lemma l6 : s1 -> p11 (* BND(1 / 1 * kk, [-5.87747e-39, 5.87747e-39]) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 assert (h2 := l11 h0).
 apply t5. exact h1. exact h2.
Qed.
Definition f19 := Float2 (-1925682799979594599320320111392142509072127279377417272545534064631717408851891088784213123217715235723007091867114749) (-522).
Definition f20 := Float2 (1925682799979594599320320111392142509072127279377417272545534064631717408851891088784213123217715235723007091867114749) (-522).
Definition i11 := makepairF f19 f20.
Notation p16 := (BND r23 i11). (* BND(z * (En + Gn * m), [-1.40258e-40, 1.40258e-40]) *)
Lemma l18 : s1 -> s5.
Proof.
 intros h0.
 assert (h1 := l12 h0).
 exact (proj1 h1).
Qed.
Lemma l17 : s1 -> s6.
Proof.
 intros h0.
 assert (h1 := l18 h0).
 exact (proj1 h1).
Qed.
Lemma l16 : s1 -> p1 (* BND(z, [-0.0078126, 0.0078126]) *).
Proof.
 intros h0.
 assert (h1 := l17 h0).
 exact (proj1 h1).
Qed.
Definition f21 := Float2 (-15405265212442037536482093920334959785091769060375365375687463717518155038430636798122689015322325760014328551531458389) (-518).
Definition f22 := Float2 (3) (-127).
Definition i12 := makepairF f21 f22.
Notation p17 := (BND r24 i12). (* BND(En + Gn * m, [-1.79528e-38, 1.76324e-38]) *)
Lemma l20 : s1 -> p3 (* BND(En, [-1.49692e-38, 1.49692e-38]) *).
Proof.
 intros h0.
 assert (h1 := l18 h0).
 exact (proj2 h1).
Qed.
Definition f23 := Float2 (-2560211192417437313279126847688141684635774058203629761936320067734049740922546138801638216229843261111367826691436373) (-518).
Definition i13 := makepairF f23 f9.
Notation p18 := (BND r25 i13). (* BND(Gn * m, [-2.98358e-39, 0]) *)
Definition f24 := Float2 (1) (-2).
Definition f25 := Float2 (2560211192417437313279126847688141684635774058203629761936320067734049740922546138801638216229843261111367826691436373) (-391).
Definition i14 := makepairF f24 f25.
Notation p19 := (BND _Gn i14). (* BND(Gn, [0.25, 0.50763]) *)
Lemma l23 : s1 -> p2 (* BND(Xn, [0.492422, 0.50763]) *).
Proof.
 intros h0.
 assert (h1 := l17 h0).
 exact (proj2 h1).
Qed.
Definition f26 := Float2 (3) (-3).
Definition f27 := Float2 (2560211192417437313279126847688141684560277616020899602520151785508385225002214108799640568476116916338208466166198101) (-391).
Definition i15 := makepairF f26 f27.
Notation p20 := (BND _Xn i15). (* BND(Xn, [0.375, 0.50763]) *)
Definition f28 := Float2 (-1) (-3).
Definition i16 := makepairF f28 f6.
Notation p21 := (BND _En i16). (* BND(En, [-0.125, 1.49692e-38]) *)
Lemma t6 : p20 -> p21 -> p19.
Proof.
 intros h0 h1.
 refine (add _Xn _En i15 i16 i14 h0 h1 _) ; finalize.
Qed.
Lemma l22 : s1 -> p19 (* BND(Gn, [0.25, 0.50763]) *).
Proof.
 intros h0.
 assert (h1 := l23 h0).
 assert (h2 := l20 h0).
 apply t6. refine (subset _Xn i2 i15 h1 _) ; finalize. refine (subset _En i3 i16 h2 _) ; finalize.
Qed.
Lemma l24 : s1 -> p5 (* BND(m, [-5.87747e-39, 0]) *).
Proof.
 intros h0.
 assert (h1 := l13 h0).
 exact (proj2 h1).
Qed.
Lemma t7 : p19 -> p5 -> p18.
Proof.
 intros h0 h1.
 refine (mul_pn _Gn _m i14 i5 i13 h0 h1 _) ; finalize.
Qed.
Lemma l21 : s1 -> p18 (* BND(Gn * m, [-2.98358e-39, 0]) *).
Proof.
 intros h0.
 assert (h1 := l22 h0).
 assert (h2 := l24 h0).
 apply t7. exact h1. exact h2.
Qed.
Definition i17 := makepairF f5 f22.
Notation p22 := (BND _En i17). (* BND(En, [-1.49692e-38, 1.76324e-38]) *)
Lemma t8 : p22 -> p18 -> p17.
Proof.
 intros h0 h1.
 refine (add _En r25 i17 i13 i12 h0 h1 _) ; finalize.
Qed.
Lemma l19 : s1 -> p17 (* BND(En + Gn * m, [-1.79528e-38, 1.76324e-38]) *).
Proof.
 intros h0.
 assert (h1 := l20 h0).
 assert (h2 := l21 h0).
 apply t8. refine (subset _En i3 i17 h1 _) ; finalize. exact h2.
Qed.
Definition f29 := Float2 (-20174085397541782047545834123190730569388259477057591616340809288909463611768773517163567287036404821876137121354287067) (-400).
Definition f30 := Float2 (20174085397541782047545834123190730569388259477057591616340809288909463611768773517163567287036404821876137121354287067) (-400).
Definition i18 := makepairF f29 f30.
Notation p23 := (BND _z i18). (* BND(z, [-0.0078126, 0.0078126]) *)
Lemma t9 : p23 -> p17 -> p16.
Proof.
 intros h0 h1.
 refine (mul_oo _z r24 i18 i12 i11 h0 h1 _) ; finalize.
Qed.
Lemma l15 : s1 -> p16 (* BND(z * (En + Gn * m), [-1.40258e-40, 1.40258e-40]) *).
Proof.
 intros h0.
 assert (h1 := l16 h0).
 assert (h2 := l19 h0).
 apply t9. refine (subset _z i1 i18 h1 _) ; finalize. exact h2.
Qed.
Lemma t10 : p11 -> p16 -> p10.
Proof.
 intros h0 h1.
 refine (sub r22 r23 i4 i11 i9 h0 h1 _) ; finalize.
Qed.
Lemma l5 : s1 -> p10 (* BND(1 / 1 * kk - z * (En + Gn * m), [-6.01773e-39, 6.01773e-39]) *).
Proof.
 intros h0.
 assert (h1 := l6 h0).
 assert (h2 := l15 h0).
 apply t10. exact h1. exact h2.
Qed.
Lemma l25 : s1 -> p6 (* BND(s, [-1.17549e-38, 1.17549e-38]) *).
Proof.
 intros h0.
 assert (h1 := l14 h0).
 exact (proj2 h1).
Qed.
Lemma t11 : p10 -> p6 -> p9.
Proof.
 intros h0 h1.
 refine (add r21 _s i9 i6 i8 h0 h1 _) ; finalize.
Qed.
Lemma l4 : s1 -> p9 (* BND(1 / 1 * kk - z * (En + Gn * m) + s, [-1.77727e-38, 1.77727e-38]) *).
Proof.
 intros h0.
 assert (h1 := l5 h0).
 assert (h2 := l25 h0).
 apply t11. exact h1. exact h2.
Qed.
Definition i19 := makepairF f9 f9.
Notation p24 := (REL r1 r20 i19). (* REL(G - X, 1 / 1 * kk - z * (En + Gn * m) + s, [0, 0]) *)
Notation p25 := (r1 = r20). (* EQL(G - X, 1 / 1 * kk - z * (En + Gn * m) + s) *)
Lemma t12 : p25.
Proof.
 refine (b1) ; finalize.
Qed.
Lemma l27 : s1 -> p25 (* EQL(G - X, 1 / 1 * kk - z * (En + Gn * m) + s) *).
Proof.
 intros h0.
 apply t12.
Qed.
Notation p26 := (REL r20 r20 i19). (* REL(1 / 1 * kk - z * (En + Gn * m) + s, 1 / 1 * kk - z * (En + Gn * m) + s, [0, 0]) *)
Lemma t13 : p26.
Proof.
 refine (rel_refl r20 i19 _) ; finalize.
Qed.
Lemma l28 : s1 -> p26 (* REL(1 / 1 * kk - z * (En + Gn * m) + s, 1 / 1 * kk - z * (En + Gn * m) + s, [0, 0]) *).
Proof.
 intros h0.
 apply t13.
Qed.
Lemma t14 : p25 -> p26 -> p24.
Proof.
 intros h0 h1.
 refine (rel_rewrite_1 r1 r20 r20 i19 h0 h1) ; finalize.
Qed.
Lemma l26 : s1 -> p24 (* REL(G - X, 1 / 1 * kk - z * (En + Gn * m) + s, [0, 0]) *).
Proof.
 intros h0.
 assert (h1 := l27 h0).
 assert (h2 := l28 h0).
 apply t14. exact h1. exact h2.
Qed.
Lemma t15 : p9 -> p24 -> p8.
Proof.
 intros h0 h1.
 refine (bnd_of_bnd_rel_o r1 r20 i8 i19 i8 h0 h1 _) ; finalize.
Qed.
Lemma l3 : s1 -> p8 (* BND(G - X, [-1.77727e-38, 1.77727e-38]) *).
Proof.
 intros h0.
 assert (h1 := l4 h0).
 assert (h2 := l26 h0).
 apply t15. exact h1. exact h2.
Qed.
Lemma l1 : s1 -> False.
Proof.
 intros h0.
 assert (h1 := l2 h0).
 assert (h2 := l3 h0).
 refine (simplify (Tatom false (Abnd 0%nat i7)) Tfalse (Abnd 0%nat i8) (List.cons r1 List.nil) h2 h1 _) ; finalize.
Qed.
End Generated_by_Gappa.
