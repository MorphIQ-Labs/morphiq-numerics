Require Import Gappa.Gappa_library.
Section Generated_by_Gappa.
Notation r6 := (Float1 (1)).
Variable _kd : R.
Notation _kw := ((r6 - _kd)%R).
Variable _eh : R.
Notation r8 := ((r6 + _eh)%R).
Notation r4 := ((_kw * r8)%R).
Variable _rr : R.
Notation r11 := ((_kd + _rr)%R).
Variable _eq : R.
Notation r13 := ((r6 + _eq)%R).
Notation r10 := ((r11 * r13)%R).
Notation r3 := ((r4 + r10)%R).
Variable _e3 : R.
Notation r15 := ((r6 + _e3)%R).
Notation _Y := ((r3 * r15)%R).
Notation r1 := ((_Y - r6)%R).
Notation r21 := ((_kw * _eh)%R).
Notation r20 := ((r21 + _rr)%R).
Notation r22 := ((r11 * _eq)%R).
Notation r19 := ((r20 + r22)%R).
Notation r18 := ((r19 * r15)%R).
Notation r17 := ((r18 + _e3)%R).
Hypothesis a1 : r1 = r17.
Lemma b1 : r1 = r17.
 apply a1.
Qed.
Definition f1 := Float2 (-65) (-52).
Definition f2 := Float2 (65) (-52).
Definition i1 := makepairF f1 f2.
Notation p1 := (BND _kd i1). (* BND(kd, [-1.44329e-14, 1.44329e-14]) *)
Definition f3 := Float2 (-65) (-106).
Definition f4 := Float2 (65) (-106).
Definition i2 := makepairF f3 f4.
Notation p2 := (BND _rr i2). (* BND(rr, [-8.01187e-31, 8.01187e-31]) *)
Definition s5 := (p1 /\ p2).
Definition f5 := Float2 (-1) (-64).
Definition f6 := Float2 (1) (-64).
Definition i3 := makepairF f5 f6.
Notation p3 := (BND _eh i3). (* BND(eh, [-5.42101e-20, 5.42101e-20]) *)
Definition s4 := (s5 /\ p3).
Definition f7 := Float2 (-1) (-53).
Definition f8 := Float2 (1) (-53).
Definition i4 := makepairF f7 f8.
Notation p4 := (BND _eq i4). (* BND(eq, [-1.11022e-16, 1.11022e-16]) *)
Definition s3 := (s4 /\ p4).
Definition f9 := Float2 (-1) (-105).
Definition f10 := Float2 (1) (-105).
Definition i5 := makepairF f9 f10.
Notation p5 := (BND _e3 i5). (* BND(e3, [-2.46519e-32, 2.46519e-32]) *)
Definition s2 := (s3 /\ p5).
Definition f11 := Float2 (-1) (-63).
Definition f12 := Float2 (1) (-63).
Definition i6 := makepairF f11 f12.
Notation p6 := (BND r1 i6). (* BND(Y - 1, [-1.0842e-19, 1.0842e-19]) *)
Definition s6 := (not p6).
Definition s1 := (s2 /\ s6).
Lemma l2 : s1 -> s6.
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj2 h1).
Qed.
Definition f13 := Float2 (-1606938044330992423955515535547514140236459531054353892769857) (-264).
Definition f14 := Float2 (1606938044330992423955515535547514140236459531054353892769857) (-264).
Definition i7 := makepairF f13 f14.
Notation p7 := (BND r1 i7). (* BND(Y - 1, [-5.42101e-20, 5.42101e-20]) *)
Notation p8 := (BND r17 i7). (* BND((kw * eh + rr + (kd + rr) * eq) * (1 + e3) + e3, [-5.42101e-20, 5.42101e-20]) *)
Definition f15 := Float2 (-1606938044330261673136850084088412297820101389544525926498369) (-264).
Definition f16 := Float2 (1606938044330261673136850084088412297820101389544525926498369) (-264).
Definition i8 := makepairF f15 f16.
Notation p9 := (BND r18 i8). (* BND((kw * eh + rr + (kd + rr) * eq) * (1 + e3), [-5.42101e-20, 5.42101e-20]) *)
Definition f17 := Float2 (-39614081258889144397492912193) (-159).
Definition f18 := Float2 (39614081258889144397492912193) (-159).
Definition i9 := makepairF f17 f18.
Notation p10 := (BND r19 i9). (* BND(kw * eh + rr + (kd + rr) * eq, [-5.42101e-20, 5.42101e-20]) *)
Definition f19 := Float2 (-4503599627437121) (-116).
Definition f20 := Float2 (4503599627437121) (-116).
Definition i10 := makepairF f19 f20.
Notation p11 := (BND r20 i10). (* BND(kw * eh + rr, [-5.42101e-20, 5.42101e-20]) *)
Definition f21 := Float2 (-4503599627370561) (-116).
Definition f22 := Float2 (4503599627370561) (-116).
Definition i11 := makepairF f21 f22.
Notation p12 := (BND r21 i11). (* BND(kw * eh, [-5.42101e-20, 5.42101e-20]) *)
Definition f23 := Float2 (1) (-1).
Definition f24 := Float2 (4503599627370561) (-52).
Definition i12 := makepairF f23 f24.
Notation p13 := (BND _kw i12). (* BND(kw, [0.5, 1]) *)
Definition f25 := Float2 (1) (0).
Definition i13 := makepairF f25 f25.
Notation p14 := (BND r6 i13). (* BND(1, [1, 1]) *)
Lemma t1 : p14.
Proof.
 refine (constant1 _ i13 _) ; finalize.
Qed.
Lemma l10 : s1 -> p14 (* BND(1, [1, 1]) *).
Proof.
 intros h0.
 apply t1.
Qed.
Lemma l15 : s1 -> s2.
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj1 h1).
Qed.
Lemma l14 : s1 -> s3.
Proof.
 intros h0.
 assert (h1 := l15 h0).
 exact (proj1 h1).
Qed.
Lemma l13 : s1 -> s4.
Proof.
 intros h0.
 assert (h1 := l14 h0).
 exact (proj1 h1).
Qed.
Lemma l12 : s1 -> s5.
Proof.
 intros h0.
 assert (h1 := l13 h0).
 exact (proj1 h1).
Qed.
Lemma l11 : s1 -> p1 (* BND(kd, [-1.44329e-14, 1.44329e-14]) *).
Proof.
 intros h0.
 assert (h1 := l12 h0).
 exact (proj1 h1).
Qed.
Definition i14 := makepairF f1 f23.
Notation p15 := (BND _kd i14). (* BND(kd, [-1.44329e-14, 0.5]) *)
Lemma t2 : p14 -> p15 -> p13.
Proof.
 intros h0 h1.
 refine (sub r6 _kd i13 i14 i12 h0 h1 _) ; finalize.
Qed.
Lemma l9 : s1 -> p13 (* BND(kw, [0.5, 1]) *).
Proof.
 intros h0.
 assert (h1 := l10 h0).
 assert (h2 := l11 h0).
 apply t2. exact h1. refine (subset _kd i1 i14 h2 _) ; finalize.
Qed.
Lemma l16 : s1 -> p3 (* BND(eh, [-5.42101e-20, 5.42101e-20]) *).
Proof.
 intros h0.
 assert (h1 := l13 h0).
 exact (proj2 h1).
Qed.
Lemma t3 : p13 -> p3 -> p12.
Proof.
 intros h0 h1.
 refine (mul_po _kw _eh i12 i3 i11 h0 h1 _) ; finalize.
Qed.
Lemma l8 : s1 -> p12 (* BND(kw * eh, [-5.42101e-20, 5.42101e-20]) *).
Proof.
 intros h0.
 assert (h1 := l9 h0).
 assert (h2 := l16 h0).
 apply t3. exact h1. exact h2.
Qed.
Lemma l17 : s1 -> p2 (* BND(rr, [-8.01187e-31, 8.01187e-31]) *).
Proof.
 intros h0.
 assert (h1 := l12 h0).
 exact (proj2 h1).
Qed.
Lemma t4 : p12 -> p2 -> p11.
Proof.
 intros h0 h1.
 refine (add r21 _rr i11 i2 i10 h0 h1 _) ; finalize.
Qed.
Lemma l7 : s1 -> p11 (* BND(kw * eh + rr, [-5.42101e-20, 5.42101e-20]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 assert (h2 := l17 h0).
 apply t4. exact h1. exact h2.
Qed.
Definition f26 := Float2 (-1170935903116329025) (-159).
Definition f27 := Float2 (1170935903116329025) (-159).
Definition i15 := makepairF f26 f27.
Notation p16 := (BND r22 i15). (* BND((kd + rr) * eq, [-1.60237e-30, 1.60237e-30]) *)
Definition f28 := Float2 (-1170935903116329025) (-106).
Definition f29 := Float2 (1170935903116329025) (-106).
Definition i16 := makepairF f28 f29.
Notation p17 := (BND r11 i16). (* BND(kd + rr, [-1.44329e-14, 1.44329e-14]) *)
Lemma t5 : p1 -> p2 -> p17.
Proof.
 intros h0 h1.
 refine (add _kd _rr i1 i2 i16 h0 h1 _) ; finalize.
Qed.
Lemma l19 : s1 -> p17 (* BND(kd + rr, [-1.44329e-14, 1.44329e-14]) *).
Proof.
 intros h0.
 assert (h1 := l11 h0).
 assert (h2 := l17 h0).
 apply t5. exact h1. exact h2.
Qed.
Lemma l20 : s1 -> p4 (* BND(eq, [-1.11022e-16, 1.11022e-16]) *).
Proof.
 intros h0.
 assert (h1 := l14 h0).
 exact (proj2 h1).
Qed.
Lemma t6 : p17 -> p4 -> p16.
Proof.
 intros h0 h1.
 refine (mul_oo r11 _eq i16 i4 i15 h0 h1 _) ; finalize.
Qed.
Lemma l18 : s1 -> p16 (* BND((kd + rr) * eq, [-1.60237e-30, 1.60237e-30]) *).
Proof.
 intros h0.
 assert (h1 := l19 h0).
 assert (h2 := l20 h0).
 apply t6. exact h1. exact h2.
Qed.
Lemma t7 : p11 -> p16 -> p10.
Proof.
 intros h0 h1.
 refine (add r20 r22 i10 i15 i9 h0 h1 _) ; finalize.
Qed.
Lemma l6 : s1 -> p10 (* BND(kw * eh + rr + (kd + rr) * eq, [-5.42101e-20, 5.42101e-20]) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 assert (h2 := l18 h0).
 apply t7. exact h1. exact h2.
Qed.
Definition f30 := Float2 (40564819207303340847894502572033) (-105).
Definition i17 := makepairF f23 f30.
Notation p18 := (BND r15 i17). (* BND(1 + e3, [0.5, 1]) *)
Lemma l22 : s1 -> p5 (* BND(e3, [-2.46519e-32, 2.46519e-32]) *).
Proof.
 intros h0.
 assert (h1 := l15 h0).
 exact (proj2 h1).
Qed.
Definition f31 := Float2 (-1) (-1).
Definition i18 := makepairF f31 f10.
Notation p19 := (BND _e3 i18). (* BND(e3, [-0.5, 2.46519e-32]) *)
Lemma t8 : p14 -> p19 -> p18.
Proof.
 intros h0 h1.
 refine (add r6 _e3 i13 i18 i17 h0 h1 _) ; finalize.
Qed.
Lemma l21 : s1 -> p18 (* BND(1 + e3, [0.5, 1]) *).
Proof.
 intros h0.
 assert (h1 := l10 h0).
 assert (h2 := l22 h0).
 apply t8. exact h1. refine (subset _e3 i5 i18 h2 _) ; finalize.
Qed.
Lemma t9 : p10 -> p18 -> p9.
Proof.
 intros h0 h1.
 refine (mul_op r19 r15 i9 i17 i8 h0 h1 _) ; finalize.
Qed.
Lemma l5 : s1 -> p9 (* BND((kw * eh + rr + (kd + rr) * eq) * (1 + e3), [-5.42101e-20, 5.42101e-20]) *).
Proof.
 intros h0.
 assert (h1 := l6 h0).
 assert (h2 := l21 h0).
 apply t9. exact h1. exact h2.
Qed.
Lemma t10 : p9 -> p5 -> p8.
Proof.
 intros h0 h1.
 refine (add r18 _e3 i8 i5 i7 h0 h1 _) ; finalize.
Qed.
Lemma l4 : s1 -> p8 (* BND((kw * eh + rr + (kd + rr) * eq) * (1 + e3) + e3, [-5.42101e-20, 5.42101e-20]) *).
Proof.
 intros h0.
 assert (h1 := l5 h0).
 assert (h2 := l22 h0).
 apply t10. exact h1. exact h2.
Qed.
Definition f32 := Float2 (0) (0).
Definition i19 := makepairF f32 f32.
Notation p20 := (REL r1 r17 i19). (* REL(Y - 1, (kw * eh + rr + (kd + rr) * eq) * (1 + e3) + e3, [0, 0]) *)
Notation p21 := (r1 = r17). (* EQL(Y - 1, (kw * eh + rr + (kd + rr) * eq) * (1 + e3) + e3) *)
Lemma t11 : p21.
Proof.
 refine (b1) ; finalize.
Qed.
Lemma l24 : s1 -> p21 (* EQL(Y - 1, (kw * eh + rr + (kd + rr) * eq) * (1 + e3) + e3) *).
Proof.
 intros h0.
 apply t11.
Qed.
Notation p22 := (REL r17 r17 i19). (* REL((kw * eh + rr + (kd + rr) * eq) * (1 + e3) + e3, (kw * eh + rr + (kd + rr) * eq) * (1 + e3) + e3, [0, 0]) *)
Lemma t12 : p22.
Proof.
 refine (rel_refl r17 i19 _) ; finalize.
Qed.
Lemma l25 : s1 -> p22 (* REL((kw * eh + rr + (kd + rr) * eq) * (1 + e3) + e3, (kw * eh + rr + (kd + rr) * eq) * (1 + e3) + e3, [0, 0]) *).
Proof.
 intros h0.
 apply t12.
Qed.
Lemma t13 : p21 -> p22 -> p20.
Proof.
 intros h0 h1.
 refine (rel_rewrite_1 r1 r17 r17 i19 h0 h1) ; finalize.
Qed.
Lemma l23 : s1 -> p20 (* REL(Y - 1, (kw * eh + rr + (kd + rr) * eq) * (1 + e3) + e3, [0, 0]) *).
Proof.
 intros h0.
 assert (h1 := l24 h0).
 assert (h2 := l25 h0).
 apply t13. exact h1. exact h2.
Qed.
Lemma t14 : p8 -> p20 -> p7.
Proof.
 intros h0 h1.
 refine (bnd_of_bnd_rel_o r1 r17 i7 i19 i7 h0 h1 _) ; finalize.
Qed.
Lemma l3 : s1 -> p7 (* BND(Y - 1, [-5.42101e-20, 5.42101e-20]) *).
Proof.
 intros h0.
 assert (h1 := l4 h0).
 assert (h2 := l23 h0).
 apply t14. exact h1. exact h2.
Qed.
Lemma l1 : s1 -> False.
Proof.
 intros h0.
 assert (h1 := l2 h0).
 assert (h2 := l3 h0).
 refine (simplify (Tatom false (Abnd 0%nat i6)) Tfalse (Abnd 0%nat i7) (List.cons r1 List.nil) h2 h1 _) ; finalize.
Qed.
End Generated_by_Gappa.
