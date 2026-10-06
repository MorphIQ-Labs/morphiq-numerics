Require Import Gappa.Gappa_library.
Section Generated_by_Gappa.
Variable _r_ : R.
Notation _r := ((rounding_float rndNE (53)%positive (-1074)%Z) _r_).
Notation _H := (float2R (Float2 (6243314768165359) (-53))).
Notation r4 := ((_r * _H)%R).
Notation _p := ((rounding_float rndNE (53)%positive (-1074)%Z) r4).
Notation _e := ((r4 - _p)%R).
Notation _Lo := (float2R (Float2 (7525737178955839) (-108))).
Notation r12 := ((_r * _Lo)%R).
Notation _u := ((rounding_float rndNE (53)%positive (-1074)%Z) r12).
Notation r9 := ((_e + _u)%R).
Notation _v := ((rounding_float rndNE (53)%positive (-1074)%Z) r9).
Notation r2 := ((_p + _v)%R).
Notation r16 := ((_H + _Lo)%R).
Variable _dl : R.
Notation r15 := ((r16 + _dl)%R).
Notation _R := ((_r * r15)%R).
Notation r1 := ((r2 - _R)%R).
Notation r20 := ((_v - r9)%R).
Notation r21 := ((_u - r12)%R).
Notation r19 := ((r20 + r21)%R).
Notation r22 := ((_r * _dl)%R).
Notation r18 := ((r19 - r22)%R).
Hypothesis a1 : r1 = r18.
Lemma b1 : r1 = r18.
 apply a1.
Qed.
Definition f1 := Float2 (-1) (-8).
Definition f2 := Float2 (1) (-8).
Definition i1 := makepairF f1 f2.
Notation p1 := (BND _r i1). (* BND(r, [-0.00390625, 0.00390625]) *)
Definition f3 := Float2 (-767) (-120).
Definition f4 := Float2 (767) (-120).
Definition i2 := makepairF f3 f4.
Notation p2 := (BND _dl i2). (* BND(dl, [-5.77027e-34, 5.77027e-34]) *)
Definition s2 := (p1 /\ p2).
Definition f5 := Float2 (-1) (-113).
Definition f6 := Float2 (1) (-113).
Definition i3 := makepairF f5 f6.
Notation p3 := (BND r1 i3). (* BND(p + v - R, [-9.62965e-35, 9.62965e-35]) *)
Definition s3 := (not p3).
Definition s1 := (s2 /\ s3).
Lemma l2 : s1 -> s3.
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj2 h1).
Qed.
Definition f7 := Float2 (-11007) (-128).
Definition f8 := Float2 (11007) (-128).
Definition i4 := makepairF f7 f8.
Notation p4 := (BND r1 i4). (* BND(p + v - R, [-3.23467e-35, 3.23467e-35]) *)
Notation p5 := (BND r18 i4). (* BND(v - (e + u) + (u - r * Lo) - r * dl, [-3.23467e-35, 3.23467e-35]) *)
Definition f9 := Float2 (-5) (-117).
Definition f10 := Float2 (5) (-117).
Definition i5 := makepairF f9 f10.
Notation p6 := (BND r19 i5). (* BND(v - (e + u) + (u - r * Lo), [-3.00927e-35, 3.00927e-35]) *)
Definition f11 := Float2 (-1) (-115).
Definition f12 := Float2 (1) (-115).
Definition i6 := makepairF f11 f12.
Notation p7 := (BND r20 i6). (* BND(v - (e + u), [-2.40741e-35, 2.40741e-35]) *)
Definition f13 := Float2 (0) (0).
Definition f14 := Float2 (1) (-61).
Definition i7 := makepairF f13 f14.
Notation p8 := (ABS r9 i7). (* ABS(e + u, [0, 4.33681e-19]) *)
Definition f15 := Float2 (-1) (-61).
Definition i8 := makepairF f15 f14.
Notation p9 := (BND r9 i8). (* BND(e + u, [-4.33681e-19, 4.33681e-19]) *)
Definition f16 := Float2 (-1) (-62).
Definition f17 := Float2 (1) (-62).
Definition i9 := makepairF f16 f17.
Notation p10 := (BND _e i9). (* BND(e, [-2.1684e-19, 2.1684e-19]) *)
Notation r24 := ((r4 - r4)%R).
Notation r25 := ((_p - r4)%R).
Notation r23 := ((r24 - r25)%R).
Notation p11 := (BND r23 i9). (* BND(r * H - r * H - (p - r * H), [-2.1684e-19, 2.1684e-19]) *)
Definition i10 := makepairF f13 f13.
Notation p12 := (BND r24 i10). (* BND(r * H - r * H, [0, 0]) *)
Lemma t1 : p12.
Proof.
 refine (sub_refl _ i10 _) ; finalize.
Qed.
Lemma l11 : s1 -> p12 (* BND(r * H - r * H, [0, 0]) *).
Proof.
 intros h0.
 apply t1.
Qed.
Notation p13 := (BND r25 i9). (* BND(p - r * H, [-2.1684e-19, 2.1684e-19]) *)
Definition i11 := makepairF f13 f2.
Notation p14 := (ABS r4 i11). (* ABS(r * H, [0, 0.00390625]) *)
Notation p15 := (ABS _r i11). (* ABS(r, [0, 0.00390625]) *)
Lemma l16 : s1 -> s2.
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj1 h1).
Qed.
Lemma l15 : s1 -> p1 (* BND(r, [-0.00390625, 0.00390625]) *).
Proof.
 intros h0.
 assert (h1 := l16 h0).
 exact (proj1 h1).
Qed.
Lemma t2 : p1 -> p15.
Proof.
 intros h0.
 refine (abs_of_bnd_o _r i1 i11 h0 _) ; finalize.
Qed.
Lemma l14 : s1 -> p15 (* ABS(r, [0, 0.00390625]) *).
Proof.
 intros h0.
 assert (h1 := l15 h0).
 apply t2. exact h1.
Qed.
Definition f18 := Float2 (1) (-1).
Definition f19 := Float2 (1) (0).
Definition i12 := makepairF f18 f19.
Notation p16 := (ABS _H i12). (* ABS(H, [0.5, 1]) *)
Notation p17 := (BND _H i12). (* BND(H, [0.5, 1]) *)
Lemma t3 : p17.
Proof.
 refine (constant2 _ i12 _) ; finalize.
Qed.
Lemma l18 : s1 -> p17 (* BND(H, [0.5, 1]) *).
Proof.
 intros h0.
 apply t3.
Qed.
Lemma t4 : p17 -> p16.
Proof.
 intros h0.
 refine (abs_of_bnd_p _H i12 i12 h0 _) ; finalize.
Qed.
Lemma l17 : s1 -> p16 (* ABS(H, [0.5, 1]) *).
Proof.
 intros h0.
 assert (h1 := l18 h0).
 apply t4. exact h1.
Qed.
Lemma t5 : p15 -> p16 -> p14.
Proof.
 intros h0 h1.
 refine (mul_aa _r _H i11 i12 i11 h0 h1 _) ; finalize.
Qed.
Lemma l13 : s1 -> p14 (* ABS(r * H, [0, 0.00390625]) *).
Proof.
 intros h0.
 assert (h1 := l14 h0).
 assert (h2 := l17 h0).
 apply t5. exact h1. exact h2.
Qed.
Lemma t6 : p14 -> p13.
Proof.
 intros h0.
 refine (float_absolute_wide_ne _ _ r4 i11 i9 h0 _) ; finalize.
Qed.
Lemma l12 : s1 -> p13 (* BND(p - r * H, [-2.1684e-19, 2.1684e-19]) *).
Proof.
 intros h0.
 assert (h1 := l13 h0).
 apply t6. exact h1.
Qed.
Lemma t7 : p12 -> p13 -> p11.
Proof.
 intros h0 h1.
 refine (sub r24 r25 i10 i9 i9 h0 h1 _) ; finalize.
Qed.
Lemma l10 : s1 -> p11 (* BND(r * H - r * H - (p - r * H), [-2.1684e-19, 2.1684e-19]) *).
Proof.
 intros h0.
 assert (h1 := l11 h0).
 assert (h2 := l12 h0).
 apply t7. exact h1. exact h2.
Qed.
Lemma t8 : p11 -> p10.
Proof.
 intros h0.
 refine (sub_xars _ _ _ i9 h0) ; finalize.
Qed.
Lemma l9 : s1 -> p10 (* BND(e, [-2.1684e-19, 2.1684e-19]) *).
Proof.
 intros h0.
 assert (h1 := l10 h0).
 apply t8. exact h1.
Qed.
Notation p18 := (BND _u i9). (* BND(u, [-2.1684e-19, 2.1684e-19]) *)
Notation p19 := (BND r12 i9). (* BND(r * Lo, [-2.1684e-19, 2.1684e-19]) *)
Definition f20 := Float2 (1) (-56).
Definition f21 := Float2 (1) (-55).
Definition i13 := makepairF f20 f21.
Notation p20 := (BND _Lo i13). (* BND(Lo, [1.38778e-17, 2.77556e-17]) *)
Lemma t9 : p20.
Proof.
 refine (constant2 _ i13 _) ; finalize.
Qed.
Lemma l21 : s1 -> p20 (* BND(Lo, [1.38778e-17, 2.77556e-17]) *).
Proof.
 intros h0.
 apply t9.
Qed.
Definition f22 := Float2 (-1) (-7).
Definition f23 := Float2 (1) (-7).
Definition i14 := makepairF f22 f23.
Notation p21 := (BND _r i14). (* BND(r, [-0.0078125, 0.0078125]) *)
Lemma t10 : p21 -> p20 -> p19.
Proof.
 intros h0 h1.
 refine (mul_op _r _Lo i14 i13 i9 h0 h1 _) ; finalize.
Qed.
Lemma l20 : s1 -> p19 (* BND(r * Lo, [-2.1684e-19, 2.1684e-19]) *).
Proof.
 intros h0.
 assert (h1 := l15 h0).
 assert (h2 := l21 h0).
 apply t10. refine (subset _r i1 i14 h1 _) ; finalize. exact h2.
Qed.
Lemma t11 : p19 -> p18.
Proof.
 intros h0.
 refine (float_round_ne _ _ r12 i9 i9 h0 _) ; finalize.
Qed.
Lemma l19 : s1 -> p18 (* BND(u, [-2.1684e-19, 2.1684e-19]) *).
Proof.
 intros h0.
 assert (h1 := l20 h0).
 apply t11. exact h1.
Qed.
Lemma t12 : p10 -> p18 -> p9.
Proof.
 intros h0 h1.
 refine (add _e _u i9 i9 i8 h0 h1 _) ; finalize.
Qed.
Lemma l8 : s1 -> p9 (* BND(e + u, [-4.33681e-19, 4.33681e-19]) *).
Proof.
 intros h0.
 assert (h1 := l9 h0).
 assert (h2 := l19 h0).
 apply t12. exact h1. exact h2.
Qed.
Lemma t13 : p9 -> p8.
Proof.
 intros h0.
 refine (abs_of_bnd_o r9 i8 i7 h0 _) ; finalize.
Qed.
Lemma l7 : s1 -> p8 (* ABS(e + u, [0, 4.33681e-19]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 apply t13. exact h1.
Qed.
Lemma t14 : p8 -> p7.
Proof.
 intros h0.
 refine (float_absolute_wide_ne _ _ r9 i7 i6 h0 _) ; finalize.
Qed.
Lemma l6 : s1 -> p7 (* BND(v - (e + u), [-2.40741e-35, 2.40741e-35]) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 apply t14. exact h1.
Qed.
Definition f24 := Float2 (-1) (-117).
Definition f25 := Float2 (1) (-117).
Definition i15 := makepairF f24 f25.
Notation p22 := (BND r21 i15). (* BND(u - r * Lo, [-6.01853e-36, 6.01853e-36]) *)
Definition f26 := Float2 (1) (-63).
Definition i16 := makepairF f13 f26.
Notation p23 := (ABS r12 i16). (* ABS(r * Lo, [0, 1.0842e-19]) *)
Notation p24 := (ABS _Lo i13). (* ABS(Lo, [1.38778e-17, 2.77556e-17]) *)
Lemma t15 : p20 -> p24.
Proof.
 intros h0.
 refine (abs_of_bnd_p _Lo i13 i13 h0 _) ; finalize.
Qed.
Lemma l24 : s1 -> p24 (* ABS(Lo, [1.38778e-17, 2.77556e-17]) *).
Proof.
 intros h0.
 assert (h1 := l21 h0).
 apply t15. exact h1.
Qed.
Lemma t16 : p15 -> p24 -> p23.
Proof.
 intros h0 h1.
 refine (mul_aa _r _Lo i11 i13 i16 h0 h1 _) ; finalize.
Qed.
Lemma l23 : s1 -> p23 (* ABS(r * Lo, [0, 1.0842e-19]) *).
Proof.
 intros h0.
 assert (h1 := l14 h0).
 assert (h2 := l24 h0).
 apply t16. exact h1. exact h2.
Qed.
Lemma t17 : p23 -> p22.
Proof.
 intros h0.
 refine (float_absolute_wide_ne _ _ r12 i16 i15 h0 _) ; finalize.
Qed.
Lemma l22 : s1 -> p22 (* BND(u - r * Lo, [-6.01853e-36, 6.01853e-36]) *).
Proof.
 intros h0.
 assert (h1 := l23 h0).
 apply t17. exact h1.
Qed.
Lemma t18 : p7 -> p22 -> p6.
Proof.
 intros h0 h1.
 refine (add r20 r21 i6 i15 i5 h0 h1 _) ; finalize.
Qed.
Lemma l5 : s1 -> p6 (* BND(v - (e + u) + (u - r * Lo), [-3.00927e-35, 3.00927e-35]) *).
Proof.
 intros h0.
 assert (h1 := l6 h0).
 assert (h2 := l22 h0).
 apply t18. exact h1. exact h2.
Qed.
Definition f27 := Float2 (-767) (-128).
Definition f28 := Float2 (767) (-128).
Definition i17 := makepairF f27 f28.
Notation p25 := (BND r22 i17). (* BND(r * dl, [-2.25401e-36, 2.25401e-36]) *)
Lemma l26 : s1 -> p2 (* BND(dl, [-5.77027e-34, 5.77027e-34]) *).
Proof.
 intros h0.
 assert (h1 := l16 h0).
 exact (proj2 h1).
Qed.
Lemma t19 : p1 -> p2 -> p25.
Proof.
 intros h0 h1.
 refine (mul_oo _r _dl i1 i2 i17 h0 h1 _) ; finalize.
Qed.
Lemma l25 : s1 -> p25 (* BND(r * dl, [-2.25401e-36, 2.25401e-36]) *).
Proof.
 intros h0.
 assert (h1 := l15 h0).
 assert (h2 := l26 h0).
 apply t19. exact h1. exact h2.
Qed.
Lemma t20 : p6 -> p25 -> p5.
Proof.
 intros h0 h1.
 refine (sub r19 r22 i5 i17 i4 h0 h1 _) ; finalize.
Qed.
Lemma l4 : s1 -> p5 (* BND(v - (e + u) + (u - r * Lo) - r * dl, [-3.23467e-35, 3.23467e-35]) *).
Proof.
 intros h0.
 assert (h1 := l5 h0).
 assert (h2 := l25 h0).
 apply t20. exact h1. exact h2.
Qed.
Notation p26 := (REL r1 r18 i10). (* REL(p + v - R, v - (e + u) + (u - r * Lo) - r * dl, [0, 0]) *)
Notation p27 := (r1 = r18). (* EQL(p + v - R, v - (e + u) + (u - r * Lo) - r * dl) *)
Lemma t21 : p27.
Proof.
 refine (b1) ; finalize.
Qed.
Lemma l28 : s1 -> p27 (* EQL(p + v - R, v - (e + u) + (u - r * Lo) - r * dl) *).
Proof.
 intros h0.
 apply t21.
Qed.
Notation p28 := (REL r18 r18 i10). (* REL(v - (e + u) + (u - r * Lo) - r * dl, v - (e + u) + (u - r * Lo) - r * dl, [0, 0]) *)
Lemma t22 : p28.
Proof.
 refine (rel_refl r18 i10 _) ; finalize.
Qed.
Lemma l29 : s1 -> p28 (* REL(v - (e + u) + (u - r * Lo) - r * dl, v - (e + u) + (u - r * Lo) - r * dl, [0, 0]) *).
Proof.
 intros h0.
 apply t22.
Qed.
Lemma t23 : p27 -> p28 -> p26.
Proof.
 intros h0 h1.
 refine (rel_rewrite_1 r1 r18 r18 i10 h0 h1) ; finalize.
Qed.
Lemma l27 : s1 -> p26 (* REL(p + v - R, v - (e + u) + (u - r * Lo) - r * dl, [0, 0]) *).
Proof.
 intros h0.
 assert (h1 := l28 h0).
 assert (h2 := l29 h0).
 apply t23. exact h1. exact h2.
Qed.
Lemma t24 : p5 -> p26 -> p4.
Proof.
 intros h0 h1.
 refine (bnd_of_bnd_rel_o r1 r18 i4 i10 i4 h0 h1 _) ; finalize.
Qed.
Lemma l3 : s1 -> p4 (* BND(p + v - R, [-3.23467e-35, 3.23467e-35]) *).
Proof.
 intros h0.
 assert (h1 := l4 h0).
 assert (h2 := l27 h0).
 apply t24. exact h1. exact h2.
Qed.
Lemma l1 : s1 -> False.
Proof.
 intros h0.
 assert (h1 := l2 h0).
 assert (h2 := l3 h0).
 refine (simplify (Tatom false (Abnd 0%nat i3)) Tfalse (Abnd 0%nat i4) (List.cons r1 List.nil) h2 h1 _) ; finalize.
Qed.
End Generated_by_Gappa.
