Require Import Gappa.Gappa_library.
Section Generated_by_Gappa.
Notation r5 := (Float1 (1)).
Variable _kw : R.
Notation _ke := ((r5 - _kw)%R).
Variable _eS : R.
Notation r10 := ((r5 + _eS)%R).
Notation r9 := ((_kw * r10)%R).
Variable _eC : R.
Notation r12 := ((r5 + _eC)%R).
Notation r8 := ((r9 * r12)%R).
Variable _em : R.
Notation r14 := ((r5 + _em)%R).
Notation r7 := ((r8 * r14)%R).
Notation r3 := ((_ke + r7)%R).
Variable _ea : R.
Notation r16 := ((r5 + _ea)%R).
Notation _Y := ((r3 * r16)%R).
Notation r1 := ((_Y - r5)%R).
Notation r23 := ((r10 * r12)%R).
Notation _Y0 := ((r23 * r14)%R).
Notation r21 := ((_Y0 - r5)%R).
Notation r20 := ((_kw * r21)%R).
Notation r19 := ((r20 * r16)%R).
Notation r18 := ((r19 + _ea)%R).
Hypothesis a1 : r1 = r18.
Lemma b1 : r1 = r18.
 apply a1.
Qed.
Definition f1 := Float2 (-259) (-8).
Definition f2 := Float2 (259) (-8).
Definition i1 := makepairF f1 f2.
Notation p1 := (BND _kw i1). (* BND(kw, [-1.01172, 1.01172]) *)
Definition f3 := Float2 (-1) (-64).
Definition f4 := Float2 (1) (-64).
Definition i2 := makepairF f3 f4.
Notation p2 := (BND _eS i2). (* BND(eS, [-5.42101e-20, 5.42101e-20]) *)
Definition s5 := (p1 /\ p2).
Definition f5 := Float2 (-247) (-118).
Definition f6 := Float2 (247) (-118).
Definition i3 := makepairF f5 f6.
Notation p3 := (BND _eC i3). (* BND(eC, [-7.43289e-34, 7.43289e-34]) *)
Definition s4 := (s5 /\ p3).
Definition f7 := Float2 (-5) (-106).
Definition f8 := Float2 (5) (-106).
Definition i4 := makepairF f7 f8.
Notation p4 := (BND _em i4). (* BND(em, [-6.16298e-32, 6.16298e-32]) *)
Definition s3 := (s4 /\ p4).
Definition f9 := Float2 (-97) (-111).
Definition f10 := Float2 (97) (-111).
Definition i5 := makepairF f9 f10.
Notation p5 := (BND _ea i5). (* BND(ea, [-3.7363e-32, 3.7363e-32]) *)
Definition s2 := (s3 /\ p5).
Definition f11 := Float2 (-1) (-63).
Definition f12 := Float2 (1) (-63).
Definition i6 := makepairF f11 f12.
Notation p6 := (BND r1 i6). (* BND(Y - 1, [-1.0842e-19, 1.0842e-19]) *)
Definition s7 := (not p6).
Notation p7 := (BND r21 i6). (* BND(Y0 - 1, [-1.0842e-19, 1.0842e-19]) *)
Definition s8 := (not p7).
Definition s6 := (s7 \/ s8).
Definition s1 := (s2 /\ s6).
Lemma l3 : s1 -> s6.
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj2 h1).
Qed.
Definition f13 := Float2 (-26959946667181659360170459694798411461762100294771305249512594867411) (-288).
Definition f14 := Float2 (26959946667181659360170459694801774609792939445717780348994429387987) (-288).
Definition i7 := makepairF f13 f14.
Notation p8 := (BND r21 i7). (* BND(Y0 - 1, [-5.42101e-20, 5.42101e-20]) *)
Definition f15 := Float2 (497323236409786642128422301479639180740285691102549305978701876598388191763020780665645) (-288).
Definition f16 := Float2 (497323236409786642182342194814002499460626610492149492050256916338877277361527804921043) (-288).
Definition i8 := makepairF f15 f16.
Notation p9 := (BND _Y0 i8). (* BND(Y0, [1, 1]) *)
Definition f17 := Float2 (6129982163463555433101081109655003209903218517405073655) (-182).
Definition f18 := Float2 (6129982163463555433765695107547470259046694460063744247) (-182).
Definition i9 := makepairF f17 f18.
Notation p10 := (BND r23 i9). (* BND((1 + eS) * (1 + eC), [1, 1]) *)
Definition f19 := Float2 (18446744073709551615) (-64).
Definition f20 := Float2 (18446744073709551617) (-64).
Definition i10 := makepairF f19 f20.
Notation p11 := (BND r10 i10). (* BND(1 + eS, [1, 1]) *)
Definition f21 := Float2 (1) (0).
Definition i11 := makepairF f21 f21.
Notation p12 := (BND r5 i11). (* BND(1, [1, 1]) *)
Lemma t1 : p12.
Proof.
 refine (constant1 _ i11 _) ; finalize.
Qed.
Lemma l8 : s1 -> p12 (* BND(1, [1, 1]) *).
Proof.
 intros h0.
 apply t1.
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
Lemma l10 : s1 -> s5.
Proof.
 intros h0.
 assert (h1 := l11 h0).
 exact (proj1 h1).
Qed.
Lemma l9 : s1 -> p2 (* BND(eS, [-5.42101e-20, 5.42101e-20]) *).
Proof.
 intros h0.
 assert (h1 := l10 h0).
 exact (proj2 h1).
Qed.
Lemma t2 : p12 -> p2 -> p11.
Proof.
 intros h0 h1.
 refine (add r5 _eS i11 i2 i10 h0 h1 _) ; finalize.
Qed.
Lemma l7 : s1 -> p11 (* BND(1 + eS, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 assert (h2 := l9 h0).
 apply t2. exact h1. exact h2.
Qed.
Definition f22 := Float2 (332306998946228968225951765070085897) (-118).
Definition f23 := Float2 (332306998946228968225951765070086391) (-118).
Definition i12 := makepairF f22 f23.
Notation p13 := (BND r12 i12). (* BND(1 + eC, [1, 1]) *)
Lemma l15 : s1 -> p3 (* BND(eC, [-7.43289e-34, 7.43289e-34]) *).
Proof.
 intros h0.
 assert (h1 := l11 h0).
 exact (proj2 h1).
Qed.
Lemma t3 : p12 -> p3 -> p13.
Proof.
 intros h0 h1.
 refine (add r5 _eC i11 i3 i12 h0 h1 _) ; finalize.
Qed.
Lemma l14 : s1 -> p13 (* BND(1 + eC, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 assert (h2 := l15 h0).
 apply t3. exact h1. exact h2.
Qed.
Lemma t4 : p11 -> p13 -> p10.
Proof.
 intros h0 h1.
 refine (mul_pp r10 r12 i10 i12 i9 h0 h1 _) ; finalize.
Qed.
Lemma l6 : s1 -> p10 (* BND((1 + eS) * (1 + eC), [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 assert (h2 := l14 h0).
 apply t4. exact h1. exact h2.
Qed.
Definition f24 := Float2 (81129638414606681695789005144059) (-106).
Definition f25 := Float2 (81129638414606681695789005144069) (-106).
Definition i13 := makepairF f24 f25.
Notation p14 := (BND r14 i13). (* BND(1 + em, [1, 1]) *)
Lemma l17 : s1 -> p4 (* BND(em, [-6.16298e-32, 6.16298e-32]) *).
Proof.
 intros h0.
 assert (h1 := l12 h0).
 exact (proj2 h1).
Qed.
Lemma t5 : p12 -> p4 -> p14.
Proof.
 intros h0 h1.
 refine (add r5 _em i11 i4 i13 h0 h1 _) ; finalize.
Qed.
Lemma l16 : s1 -> p14 (* BND(1 + em, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 assert (h2 := l17 h0).
 apply t5. exact h1. exact h2.
Qed.
Lemma t6 : p10 -> p14 -> p9.
Proof.
 intros h0 h1.
 refine (mul_pp r23 r14 i9 i13 i8 h0 h1 _) ; finalize.
Qed.
Lemma l5 : s1 -> p9 (* BND(Y0, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l6 h0).
 assert (h2 := l16 h0).
 apply t6. exact h1. exact h2.
Qed.
Lemma t7 : p9 -> p12 -> p8.
Proof.
 intros h0 h1.
 refine (sub _Y0 r5 i8 i11 i7 h0 h1 _) ; finalize.
Qed.
Lemma l4 : s1 -> p8 (* BND(Y0 - 1, [-5.42101e-20, 5.42101e-20]) *).
Proof.
 intros h0.
 assert (h1 := l5 h0).
 assert (h2 := l8 h0).
 apply t7. exact h1. exact h2.
Qed.
Lemma l2 : s1 -> s7.
Proof.
 intros h0.
 assert (h1 := l3 h0).
 assert (h2 := l4 h0).
 refine (simplify (Ttree false (Tatom false (Abnd 0%nat i6)) (Tatom false (Abnd 1%nat i6))) (Tatom false (Abnd 0%nat i6)) (Abnd 1%nat i7) (List.cons r1 (List.cons r21 List.nil)) h2 h1 _) ; finalize.
Qed.
Definition f26 := Float2 (-18127934007034809991436732551833283239085860963785607380987807208067549807376031328505033223704780828377) (-407).
Definition f27 := Float2 (18127934007034809991436732551833283239085860963785607380987807208067549807376031328505033223704780828377) (-407).
Definition i14 := makepairF f26 f27.
Notation p15 := (BND r1 i14). (* BND(Y - 1, [-5.48454e-20, 5.48454e-20]) *)
Notation p16 := (BND r18 i14). (* BND(kw * (Y0 - 1) * (1 + ea) + ea, [-5.48454e-20, 5.48454e-20]) *)
Definition f28 := Float2 (-18127934007022460460830204729935280787099879108684232853851207469548068205901820391875217994923543981785) (-407).
Definition f29 := Float2 (18127934007022460460830204729935280787099879108684232853851207469548068205901820391875217994923543981785) (-407).
Definition i15 := makepairF f28 f29.
Notation p17 := (BND r19 i15). (* BND(kw * (Y0 - 1) * (1 + ea), [-5.48454e-20, 5.48454e-20]) *)
Definition f30 := Float2 (-6982626186800049774284149060953659623936371316440905110389557211488633) (-296).
Definition f31 := Float2 (6982626186800049774284149060953659623936371316440905110389557211488633) (-296).
Definition i16 := makepairF f30 f31.
Notation p18 := (BND r20 i16). (* BND(kw * (Y0 - 1), [-5.48454e-20, 5.48454e-20]) *)
Lemma l22 : s1 -> p1 (* BND(kw, [-1.01172, 1.01172]) *).
Proof.
 intros h0.
 assert (h1 := l10 h0).
 exact (proj1 h1).
Qed.
Definition f32 := Float2 (-18014398509502711) (-118).
Definition i17 := makepairF f32 f14.
Notation p19 := (BND r21 i17). (* BND(Y0 - 1, [-5.42101e-20, 5.42101e-20]) *)
Lemma t8 : p1 -> p19 -> p18.
Proof.
 intros h0 h1.
 refine (mul_oo _kw r21 i1 i17 i16 h0 h1 _) ; finalize.
Qed.
Lemma l21 : s1 -> p18 (* BND(kw * (Y0 - 1), [-5.48454e-20, 5.48454e-20]) *).
Proof.
 intros h0.
 assert (h1 := l22 h0).
 assert (h2 := l4 h0).
 apply t8. exact h1. refine (subset r21 i7 i17 h2 _) ; finalize.
Qed.
Definition f33 := Float2 (1) (-1).
Definition f34 := Float2 (2596148429267413814265248164610145) (-111).
Definition i18 := makepairF f33 f34.
Notation p20 := (BND r16 i18). (* BND(1 + ea, [0.5, 1]) *)
Lemma l24 : s1 -> p5 (* BND(ea, [-3.7363e-32, 3.7363e-32]) *).
Proof.
 intros h0.
 assert (h1 := l13 h0).
 exact (proj2 h1).
Qed.
Definition f35 := Float2 (-1) (-1).
Definition i19 := makepairF f35 f10.
Notation p21 := (BND _ea i19). (* BND(ea, [-0.5, 3.7363e-32]) *)
Lemma t9 : p12 -> p21 -> p20.
Proof.
 intros h0 h1.
 refine (add r5 _ea i11 i19 i18 h0 h1 _) ; finalize.
Qed.
Lemma l23 : s1 -> p20 (* BND(1 + ea, [0.5, 1]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 assert (h2 := l24 h0).
 apply t9. exact h1. refine (subset _ea i5 i19 h2 _) ; finalize.
Qed.
Lemma t10 : p18 -> p20 -> p17.
Proof.
 intros h0 h1.
 refine (mul_op r20 r16 i16 i18 i15 h0 h1 _) ; finalize.
Qed.
Lemma l20 : s1 -> p17 (* BND(kw * (Y0 - 1) * (1 + ea), [-5.48454e-20, 5.48454e-20]) *).
Proof.
 intros h0.
 assert (h1 := l21 h0).
 assert (h2 := l23 h0).
 apply t10. exact h1. exact h2.
Qed.
Lemma t11 : p17 -> p5 -> p16.
Proof.
 intros h0 h1.
 refine (add r19 _ea i15 i5 i14 h0 h1 _) ; finalize.
Qed.
Lemma l19 : s1 -> p16 (* BND(kw * (Y0 - 1) * (1 + ea) + ea, [-5.48454e-20, 5.48454e-20]) *).
Proof.
 intros h0.
 assert (h1 := l20 h0).
 assert (h2 := l24 h0).
 apply t11. exact h1. exact h2.
Qed.
Definition f36 := Float2 (0) (0).
Definition i20 := makepairF f36 f36.
Notation p22 := (REL r1 r18 i20). (* REL(Y - 1, kw * (Y0 - 1) * (1 + ea) + ea, [0, 0]) *)
Notation p23 := (r1 = r18). (* EQL(Y - 1, kw * (Y0 - 1) * (1 + ea) + ea) *)
Lemma t12 : p23.
Proof.
 refine (b1) ; finalize.
Qed.
Lemma l26 : s1 -> p23 (* EQL(Y - 1, kw * (Y0 - 1) * (1 + ea) + ea) *).
Proof.
 intros h0.
 apply t12.
Qed.
Notation p24 := (REL r18 r18 i20). (* REL(kw * (Y0 - 1) * (1 + ea) + ea, kw * (Y0 - 1) * (1 + ea) + ea, [0, 0]) *)
Lemma t13 : p24.
Proof.
 refine (rel_refl r18 i20 _) ; finalize.
Qed.
Lemma l27 : s1 -> p24 (* REL(kw * (Y0 - 1) * (1 + ea) + ea, kw * (Y0 - 1) * (1 + ea) + ea, [0, 0]) *).
Proof.
 intros h0.
 apply t13.
Qed.
Lemma t14 : p23 -> p24 -> p22.
Proof.
 intros h0 h1.
 refine (rel_rewrite_1 r1 r18 r18 i20 h0 h1) ; finalize.
Qed.
Lemma l25 : s1 -> p22 (* REL(Y - 1, kw * (Y0 - 1) * (1 + ea) + ea, [0, 0]) *).
Proof.
 intros h0.
 assert (h1 := l26 h0).
 assert (h2 := l27 h0).
 apply t14. exact h1. exact h2.
Qed.
Lemma t15 : p16 -> p22 -> p15.
Proof.
 intros h0 h1.
 refine (bnd_of_bnd_rel_o r1 r18 i14 i20 i14 h0 h1 _) ; finalize.
Qed.
Lemma l18 : s1 -> p15 (* BND(Y - 1, [-5.48454e-20, 5.48454e-20]) *).
Proof.
 intros h0.
 assert (h1 := l19 h0).
 assert (h2 := l25 h0).
 apply t15. exact h1. exact h2.
Qed.
Lemma l1 : s1 -> False.
Proof.
 intros h0.
 assert (h1 := l2 h0).
 assert (h2 := l18 h0).
 refine (simplify (Tatom false (Abnd 0%nat i6)) Tfalse (Abnd 0%nat i14) (List.cons r1 List.nil) h2 h1 _) ; finalize.
Qed.
End Generated_by_Gappa.
