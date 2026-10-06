Require Import Gappa.Gappa_library.
Section Generated_by_Gappa.
Notation r4 := (Float1 (1)).
Variable _e : R.
Notation r3 := ((r4 + _e)%R).
Variable _m1 : R.
Notation r12 := ((r4 + _m1)%R).
Notation r11 := ((r3 * r12)%R).
Notation r10 := ((r4 - r11)%R).
Variable _s1 : R.
Notation _G := ((r10 + _s1)%R).
Variable _m2 : R.
Notation r15 := ((r4 + _m2)%R).
Notation r8 := ((_G * r15)%R).
Notation r7 := ((r4 + r8)%R).
Variable _s2 : R.
Notation r6 := ((r7 + _s2)%R).
Notation _P := ((r3 * r6)%R).
Notation r1 := ((_P - r4)%R).
Notation r22 := ((_e * _m2)%R).
Notation r21 := ((- r22)%R).
Notation r24 := ((_e * _e)%R).
Notation r23 := ((r24 * r15)%R).
Notation r20 := ((r21 - r23)%R).
Notation r26 := ((r3 * r15)%R).
Notation r28 := ((r3 * _m1)%R).
Notation r27 := ((_s1 - r28)%R).
Notation r25 := ((r26 * r27)%R).
Notation r19 := ((r20 + r25)%R).
Notation r29 := ((r3 * _s2)%R).
Notation r18 := ((r19 + r29)%R).
Hypothesis a1 : r1 = r18.
Lemma b1 : r1 = r18.
 apply a1.
Qed.
Definition f1 := Float2 (-555) (-217).
Definition f2 := Float2 (555) (-217).
Definition i1 := makepairF f1 f2.
Notation p1 := (BND _e i1). (* BND(e, [-2.63502e-63, 2.63502e-63]) *)
Definition f3 := Float2 (-1) (-255).
Definition f4 := Float2 (0) (0).
Definition i2 := makepairF f3 f4.
Notation p2 := (BND _m1 i2). (* BND(m1, [-1.72723e-77, 0]) *)
Definition s5 := (p1 /\ p2).
Notation p3 := (BND _m2 i2). (* BND(m2, [-1.72723e-77, 0]) *)
Definition s4 := (s5 /\ p3).
Definition f5 := Float2 (-259) (-262).
Definition f6 := Float2 (259) (-262).
Definition i3 := makepairF f5 f6.
Notation p4 := (BND _s1 i3). (* BND(s1, [-3.49495e-77, 3.49495e-77]) *)
Definition s3 := (s4 /\ p4).
Definition f7 := Float2 (-1) (-254).
Definition f8 := Float2 (1) (-254).
Definition i4 := makepairF f7 f8.
Notation p5 := (BND _s2 i4). (* BND(s2, [-3.45447e-77, 3.45447e-77]) *)
Definition s2 := (s3 /\ p5).
Definition f9 := Float2 (-325) (-261).
Definition f10 := Float2 (325) (-261).
Definition i5 := makepairF f9 f10.
Notation p6 := (BND r1 i5). (* BND(P - 1, [-8.77111e-77, 8.77111e-77]) *)
Definition s6 := (not p6).
Definition s1 := (s2 /\ s6).
Lemma l2 : s1 -> s6.
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj2 h1).
Qed.
Definition f11 := Float2 (-108471660418613902298855568514180545288461948262576422258152969695745) (-479).
Definition f12 := Float2 (1621471358994025608543707058201109995306641430458194061279408176145199533257300995718462521339078857986816474728179433473) (-652).
Definition i6 := makepairF f11 f12.
Notation p7 := (BND r1 i6). (* BND(P - 1, [-6.94942e-77, 8.67665e-77]) *)
Notation p8 := (BND r18 i6). (* BND(-(e * m2) - e * e * (1 + m2) + (1 + e) * (1 + m2) * (s1 - (1 + e) * m1) + (1 + e) * s2, [-6.94942e-77, 8.67665e-77]) *)
Definition f13 := Float2 (-54551767084312622709521538340141283941187659417495277295945749055233) (-479).
Definition f14 := Float2 (975908889472298461129727265200357026724214982250888183071743335308967577391954064283285982882201206311040256111194144769) (-652).
Definition i7 := makepairF f13 f14.
Notation p9 := (BND r19 i7). (* BND(-(e * m2) - e * e * (1 + m2) + (1 + e) * (1 + m2) * (s1 - (1 + e) * m1), [-3.49495e-77, 5.22218e-77]) *)
Definition f15 := Float2 (-84669267286426155) (-472).
Definition f16 := Float2 (555) (-472).
Definition i8 := makepairF f15 f16.
Notation p10 := (BND r20 i8). (* BND(-(e * m2) - e * e * (1 + m2), [-6.94333e-126, 4.5513e-140]) *)
Definition f17 := Float2 (-555) (-472).
Definition i9 := makepairF f17 f16.
Notation p11 := (BND r21 i9). (* BND(-(e * m2), [-4.5513e-140, 4.5513e-140]) *)
Notation p12 := (BND r22 i9). (* BND(e * m2, [-4.5513e-140, 4.5513e-140]) *)
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
Lemma l10 : s1 -> s5.
Proof.
 intros h0.
 assert (h1 := l11 h0).
 exact (proj1 h1).
Qed.
Lemma l9 : s1 -> p1 (* BND(e, [-2.63502e-63, 2.63502e-63]) *).
Proof.
 intros h0.
 assert (h1 := l10 h0).
 exact (proj1 h1).
Qed.
Lemma l14 : s1 -> p3 (* BND(m2, [-1.72723e-77, 0]) *).
Proof.
 intros h0.
 assert (h1 := l11 h0).
 exact (proj2 h1).
Qed.
Lemma t1 : p1 -> p3 -> p12.
Proof.
 intros h0 h1.
 refine (mul_on _e _m2 i1 i2 i9 h0 h1 _) ; finalize.
Qed.
Lemma l8 : s1 -> p12 (* BND(e * m2, [-4.5513e-140, 4.5513e-140]) *).
Proof.
 intros h0.
 assert (h1 := l9 h0).
 assert (h2 := l14 h0).
 apply t1. exact h1. exact h2.
Qed.
Lemma t2 : p12 -> p11.
Proof.
 intros h0.
 refine (neg r22 i9 i9 h0 _) ; finalize.
Qed.
Lemma l7 : s1 -> p11 (* BND(-(e * m2), [-4.5513e-140, 4.5513e-140]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 apply t2. exact h1.
Qed.
Definition f18 := Float2 (308025) (-434).
Definition i10 := makepairF f4 f18.
Notation p13 := (BND r23 i10). (* BND(e * e * (1 + m2), [0, 6.94333e-126]) *)
Notation p14 := (BND r24 i10). (* BND(e * e, [0, 6.94333e-126]) *)
Definition i11 := makepairF f4 f2.
Notation p15 := (ABS _e i11). (* ABS(e, [0, 2.63502e-63]) *)
Lemma t3 : p1 -> p15.
Proof.
 intros h0.
 refine (abs_of_bnd_o _e i1 i11 h0 _) ; finalize.
Qed.
Lemma l17 : s1 -> p15 (* ABS(e, [0, 2.63502e-63]) *).
Proof.
 intros h0.
 assert (h1 := l9 h0).
 apply t3. exact h1.
Qed.
Lemma t4 : p15 -> p14.
Proof.
 intros h0.
 refine (square _e i11 i10 h0 _) ; finalize.
Qed.
Lemma l16 : s1 -> p14 (* BND(e * e, [0, 6.94333e-126]) *).
Proof.
 intros h0.
 assert (h1 := l17 h0).
 apply t4. exact h1.
Qed.
Definition f19 := Float2 (3) (-2).
Definition f20 := Float2 (1) (0).
Definition i12 := makepairF f19 f20.
Notation p16 := (BND r15 i12). (* BND(1 + m2, [0.75, 1]) *)
Definition i13 := makepairF f20 f20.
Notation p17 := (BND r4 i13). (* BND(1, [1, 1]) *)
Lemma t5 : p17.
Proof.
 refine (constant1 _ i13 _) ; finalize.
Qed.
Lemma l19 : s1 -> p17 (* BND(1, [1, 1]) *).
Proof.
 intros h0.
 apply t5.
Qed.
Definition f21 := Float2 (-1) (-2).
Definition i14 := makepairF f21 f4.
Notation p18 := (BND _m2 i14). (* BND(m2, [-0.25, 0]) *)
Lemma t6 : p17 -> p18 -> p16.
Proof.
 intros h0 h1.
 refine (add r4 _m2 i13 i14 i12 h0 h1 _) ; finalize.
Qed.
Lemma l18 : s1 -> p16 (* BND(1 + m2, [0.75, 1]) *).
Proof.
 intros h0.
 assert (h1 := l19 h0).
 assert (h2 := l14 h0).
 apply t6. exact h1. refine (subset _m2 i2 i14 h2 _) ; finalize.
Qed.
Definition f22 := Float2 (1) (-1).
Definition i15 := makepairF f22 f20.
Notation p19 := (BND r15 i15). (* BND(1 + m2, [0.5, 1]) *)
Lemma t7 : p14 -> p19 -> p13.
Proof.
 intros h0 h1.
 refine (mul_pp r24 r15 i10 i15 i10 h0 h1 _) ; finalize.
Qed.
Lemma l15 : s1 -> p13 (* BND(e * e * (1 + m2), [0, 6.94333e-126]) *).
Proof.
 intros h0.
 assert (h1 := l16 h0).
 assert (h2 := l18 h0).
 apply t7. exact h1. refine (subset r15 i12 i15 h2 _) ; finalize.
Qed.
Lemma t8 : p11 -> p13 -> p10.
Proof.
 intros h0 h1.
 refine (sub r21 r23 i9 i10 i8 h0 h1 _) ; finalize.
Qed.
Lemma l6 : s1 -> p10 (* BND(-(e * m2) - e * e * (1 + m2), [-6.94333e-126, 4.5513e-140]) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 assert (h2 := l15 h0).
 apply t8. exact h1. exact h2.
Qed.
Definition f23 := Float2 (-54551767084312622709521538340141283941187659417484439629733086507393) (-479).
Definition f24 := Float2 (975908889472298461129727265200357026724214982250888183071743334458432552211385747894403382813779609402640043299294937089) (-652).
Definition i16 := makepairF f23 f24.
Notation p20 := (BND r25 i16). (* BND((1 + e) * (1 + m2) * (s1 - (1 + e) * m1), [-3.49495e-77, 5.22218e-77]) *)
Definition f25 := Float2 (210624583337114373395836055367340864637790190801098222508621955627) (-217).
Definition i17 := makepairF f22 f25.
Notation p21 := (BND r26 i17). (* BND((1 + e) * (1 + m2), [0.5, 1]) *)
Definition i18 := makepairF f19 f25.
Notation p22 := (BND r3 i18). (* BND(1 + e, [0.75, 1]) *)
Definition i19 := makepairF f21 f2.
Notation p23 := (BND _e i19). (* BND(e, [-0.25, 2.63502e-63]) *)
Lemma t9 : p17 -> p23 -> p22.
Proof.
 intros h0 h1.
 refine (add r4 _e i13 i19 i18 h0 h1 _) ; finalize.
Qed.
Lemma l22 : s1 -> p22 (* BND(1 + e, [0.75, 1]) *).
Proof.
 intros h0.
 assert (h1 := l19 h0).
 assert (h2 := l9 h0).
 apply t9. exact h1. refine (subset _e i1 i19 h2 _) ; finalize.
Qed.
Lemma t10 : p22 -> p16 -> p21.
Proof.
 intros h0 h1.
 refine (mul_pp r3 r15 i18 i12 i17 h0 h1 _) ; finalize.
Qed.
Lemma l21 : s1 -> p21 (* BND((1 + e) * (1 + m2), [0.5, 1]) *).
Proof.
 intros h0.
 assert (h1 := l22 h0).
 assert (h2 := l18 h0).
 apply t10. exact h1. exact h2.
Qed.
Definition f26 := Float2 (636810263683306738313973073649694645428318780000195407115911692843) (-472).
Definition i20 := makepairF f5 f26.
Notation p24 := (BND r27 i20). (* BND(s1 - (1 + e) * m1, [-3.49495e-77, 5.22218e-77]) *)
Lemma l24 : s1 -> p4 (* BND(s1, [-3.49495e-77, 3.49495e-77]) *).
Proof.
 intros h0.
 assert (h1 := l12 h0).
 exact (proj2 h1).
Qed.
Definition f27 := Float2 (-210624583337114373395836055367340864637790190801098222508621955627) (-472).
Definition i21 := makepairF f27 f4.
Notation p25 := (BND r28 i21). (* BND((1 + e) * m1, [-1.72723e-77, 0]) *)
Lemma l26 : s1 -> p2 (* BND(m1, [-1.72723e-77, 0]) *).
Proof.
 intros h0.
 assert (h1 := l10 h0).
 exact (proj2 h1).
Qed.
Notation p26 := (BND r3 i17). (* BND(1 + e, [0.5, 1]) *)
Lemma t11 : p26 -> p2 -> p25.
Proof.
 intros h0 h1.
 refine (mul_pn r3 _m1 i17 i2 i21 h0 h1 _) ; finalize.
Qed.
Lemma l25 : s1 -> p25 (* BND((1 + e) * m1, [-1.72723e-77, 0]) *).
Proof.
 intros h0.
 assert (h1 := l22 h0).
 assert (h2 := l26 h0).
 apply t11. refine (subset r3 i18 i17 h1 _) ; finalize. exact h2.
Qed.
Lemma t12 : p4 -> p25 -> p24.
Proof.
 intros h0 h1.
 refine (sub _s1 r28 i3 i21 i20 h0 h1 _) ; finalize.
Qed.
Lemma l23 : s1 -> p24 (* BND(s1 - (1 + e) * m1, [-3.49495e-77, 5.22218e-77]) *).
Proof.
 intros h0.
 assert (h1 := l24 h0).
 assert (h2 := l25 h0).
 apply t12. exact h1. exact h2.
Qed.
Lemma t13 : p21 -> p24 -> p20.
Proof.
 intros h0 h1.
 refine (mul_po r26 r27 i17 i20 i16 h0 h1 _) ; finalize.
Qed.
Lemma l20 : s1 -> p20 (* BND((1 + e) * (1 + m2) * (s1 - (1 + e) * m1), [-3.49495e-77, 5.22218e-77]) *).
Proof.
 intros h0.
 assert (h1 := l21 h0).
 assert (h2 := l23 h0).
 apply t13. exact h1. exact h2.
Qed.
Lemma t14 : p10 -> p20 -> p9.
Proof.
 intros h0 h1.
 refine (add r20 r25 i8 i16 i7 h0 h1 _) ; finalize.
Qed.
Lemma l5 : s1 -> p9 (* BND(-(e * m2) - e * e * (1 + m2) + (1 + e) * (1 + m2) * (s1 - (1 + e) * m1), [-3.49495e-77, 5.22218e-77]) *).
Proof.
 intros h0.
 assert (h1 := l6 h0).
 assert (h2 := l20 h0).
 apply t14. exact h1. exact h2.
Qed.
Definition f28 := Float2 (-210624583337114373395836055367340864637790190801098222508621955627) (-471).
Definition f29 := Float2 (210624583337114373395836055367340864637790190801098222508621955627) (-471).
Definition i22 := makepairF f28 f29.
Notation p27 := (BND r29 i22). (* BND((1 + e) * s2, [-3.45447e-77, 3.45447e-77]) *)
Lemma l28 : s1 -> p5 (* BND(s2, [-3.45447e-77, 3.45447e-77]) *).
Proof.
 intros h0.
 assert (h1 := l13 h0).
 exact (proj2 h1).
Qed.
Lemma t15 : p26 -> p5 -> p27.
Proof.
 intros h0 h1.
 refine (mul_po r3 _s2 i17 i4 i22 h0 h1 _) ; finalize.
Qed.
Lemma l27 : s1 -> p27 (* BND((1 + e) * s2, [-3.45447e-77, 3.45447e-77]) *).
Proof.
 intros h0.
 assert (h1 := l22 h0).
 assert (h2 := l28 h0).
 apply t15. refine (subset r3 i18 i17 h1 _) ; finalize. exact h2.
Qed.
Lemma t16 : p9 -> p27 -> p8.
Proof.
 intros h0 h1.
 refine (add r19 r29 i7 i22 i6 h0 h1 _) ; finalize.
Qed.
Lemma l4 : s1 -> p8 (* BND(-(e * m2) - e * e * (1 + m2) + (1 + e) * (1 + m2) * (s1 - (1 + e) * m1) + (1 + e) * s2, [-6.94942e-77, 8.67665e-77]) *).
Proof.
 intros h0.
 assert (h1 := l5 h0).
 assert (h2 := l27 h0).
 apply t16. exact h1. exact h2.
Qed.
Definition i23 := makepairF f4 f4.
Notation p28 := (REL r1 r18 i23). (* REL(P - 1, -(e * m2) - e * e * (1 + m2) + (1 + e) * (1 + m2) * (s1 - (1 + e) * m1) + (1 + e) * s2, [0, 0]) *)
Notation p29 := (r1 = r18). (* EQL(P - 1, -(e * m2) - e * e * (1 + m2) + (1 + e) * (1 + m2) * (s1 - (1 + e) * m1) + (1 + e) * s2) *)
Lemma t17 : p29.
Proof.
 refine (b1) ; finalize.
Qed.
Lemma l30 : s1 -> p29 (* EQL(P - 1, -(e * m2) - e * e * (1 + m2) + (1 + e) * (1 + m2) * (s1 - (1 + e) * m1) + (1 + e) * s2) *).
Proof.
 intros h0.
 apply t17.
Qed.
Notation p30 := (REL r18 r18 i23). (* REL(-(e * m2) - e * e * (1 + m2) + (1 + e) * (1 + m2) * (s1 - (1 + e) * m1) + (1 + e) * s2, -(e * m2) - e * e * (1 + m2) + (1 + e) * (1 + m2) * (s1 - (1 + e) * m1) + (1 + e) * s2, [0, 0]) *)
Lemma t18 : p30.
Proof.
 refine (rel_refl r18 i23 _) ; finalize.
Qed.
Lemma l31 : s1 -> p30 (* REL(-(e * m2) - e * e * (1 + m2) + (1 + e) * (1 + m2) * (s1 - (1 + e) * m1) + (1 + e) * s2, -(e * m2) - e * e * (1 + m2) + (1 + e) * (1 + m2) * (s1 - (1 + e) * m1) + (1 + e) * s2, [0, 0]) *).
Proof.
 intros h0.
 apply t18.
Qed.
Lemma t19 : p29 -> p30 -> p28.
Proof.
 intros h0 h1.
 refine (rel_rewrite_1 r1 r18 r18 i23 h0 h1) ; finalize.
Qed.
Lemma l29 : s1 -> p28 (* REL(P - 1, -(e * m2) - e * e * (1 + m2) + (1 + e) * (1 + m2) * (s1 - (1 + e) * m1) + (1 + e) * s2, [0, 0]) *).
Proof.
 intros h0.
 assert (h1 := l30 h0).
 assert (h2 := l31 h0).
 apply t19. exact h1. exact h2.
Qed.
Lemma t20 : p8 -> p28 -> p7.
Proof.
 intros h0 h1.
 refine (bnd_of_bnd_rel_o r1 r18 i6 i23 i6 h0 h1 _) ; finalize.
Qed.
Lemma l3 : s1 -> p7 (* BND(P - 1, [-6.94942e-77, 8.67665e-77]) *).
Proof.
 intros h0.
 assert (h1 := l4 h0).
 assert (h2 := l29 h0).
 apply t20. exact h1. exact h2.
Qed.
Lemma l1 : s1 -> False.
Proof.
 intros h0.
 assert (h1 := l2 h0).
 assert (h2 := l3 h0).
 refine (simplify (Tatom false (Abnd 0%nat i5)) Tfalse (Abnd 0%nat i6) (List.cons r1 List.nil) h2 h1 _) ; finalize.
Qed.
End Generated_by_Gappa.
