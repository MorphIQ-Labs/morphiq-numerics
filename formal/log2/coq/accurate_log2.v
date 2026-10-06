Require Import Gappa.Gappa_library.
Section Generated_by_Gappa.
Notation r5 := (Float1 (1)).
Variable _kw : R.
Notation _ke := ((r5 - _kw)%R).
Variable _eA : R.
Notation r10 := ((r5 + _eA)%R).
Notation r9 := ((_kw * r10)%R).
Variable _eC : R.
Notation r12 := ((r5 + _eC)%R).
Notation r8 := ((r9 * r12)%R).
Variable _m : R.
Notation r14 := ((r5 + _m)%R).
Notation r7 := ((r8 * r14)%R).
Notation r3 := ((_ke + r7)%R).
Variable _s : R.
Notation _Y := ((r3 + _s)%R).
Notation r1 := ((_Y - r5)%R).
Notation r21 := ((r10 * r12)%R).
Notation _Y0 := ((r21 * r14)%R).
Notation r19 := ((_Y0 - r5)%R).
Notation r18 := ((_kw * r19)%R).
Notation r17 := ((r18 + _s)%R).
Hypothesis a1 : r1 = r17.
Lemma b1 : r1 = r17.
 apply a1.
Qed.
Definition f1 := Float2 (-259) (-8).
Definition f2 := Float2 (259) (-8).
Definition i1 := makepairF f1 f2.
Notation p1 := (BND _kw i1). (* BND(kw, [-1.01172, 1.01172]) *)
Definition f3 := Float2 (-1) (-123).
Definition f4 := Float2 (1) (-123).
Definition i2 := makepairF f3 f4.
Notation p2 := (BND _eA i2). (* BND(eA, [-9.40395e-38, 9.40395e-38]) *)
Definition s5 := (p1 /\ p2).
Definition f5 := Float2 (-463) (-140).
Definition f6 := Float2 (463) (-140).
Definition i3 := makepairF f5 f6.
Notation p3 := (BND _eC i3). (* BND(eC, [-3.32186e-40, 3.32186e-40]) *)
Definition s4 := (s5 /\ p3).
Definition f7 := Float2 (-1) (-127).
Definition f8 := Float2 (0) (0).
Definition i4 := makepairF f7 f8.
Notation p4 := (BND _m i4). (* BND(m, [-5.87747e-39, 0]) *)
Definition s3 := (s4 /\ p4).
Definition f9 := Float2 (-259) (-133).
Definition f10 := Float2 (259) (-133).
Definition i5 := makepairF f9 f10.
Notation p5 := (BND _s i5). (* BND(s, [-2.37854e-38, 2.37854e-38]) *)
Definition s2 := (s3 /\ p5).
Definition f11 := Float2 (-1) (-122).
Definition f12 := Float2 (1) (-122).
Definition i6 := makepairF f11 f12.
Notation p6 := (BND r1 i6). (* BND(Y - 1, [-1.88079e-37, 1.88079e-37]) *)
Definition s7 := (not p6).
Notation p7 := (BND r19 i6). (* BND(Y0 - 1, [-1.88079e-37, 1.88079e-37]) *)
Definition s8 := (not p7).
Definition s6 := (s7 \/ s8).
Definition s1 := (s2 /\ s6).
Lemma l3 : s1 -> s6.
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj2 h1).
Qed.
Definition f13 := Float2 (-252801269575976250592957859723577114070613991274402612276301664445513961312354767) (-390).
Definition f14 := Float2 (1398720035404551274739218093391800990433743) (-263).
Definition i7 := makepairF f13 f14.
Notation p8 := (BND r19 i7). (* BND(Y0 - 1, [-1.00249e-37, 9.43717e-38]) *)
Definition f15 := Float2 (2521728396569246669585858566409191283272302043733812336155732918148149079305207487856110428036332936566110230067281457) (-390).
Definition f16 := Float2 (14821387422376473014217086081112052206617278072606543471789788846404681584345551) (-263).
Definition i8 := makepairF f15 f16.
Notation p9 := (BND _Y0 i8). (* BND(Y0, [1, 1]) *)
Definition f17 := Float2 (14821387422376473014217086081112052203819838001797440922311352659621079603478991) (-263).
Definition i9 := makepairF f17 f16.
Notation p10 := (BND r21 i9). (* BND((1 + eA) * (1 + eC), [1, 1]) *)
Definition f18 := Float2 (10633823966279326983230456482242756607) (-123).
Definition f19 := Float2 (10633823966279326983230456482242756609) (-123).
Definition i10 := makepairF f18 f19.
Notation p11 := (BND r10 i10). (* BND(1 + eA, [1, 1]) *)
Definition f20 := Float2 (1) (0).
Definition i11 := makepairF f20 f20.
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
Lemma l9 : s1 -> p2 (* BND(eA, [-9.40395e-38, 9.40395e-38]) *).
Proof.
 intros h0.
 assert (h1 := l10 h0).
 exact (proj2 h1).
Qed.
Lemma t2 : p12 -> p2 -> p11.
Proof.
 intros h0 h1.
 refine (add r5 _eA i11 i2 i10 h0 h1 _) ; finalize.
Qed.
Lemma l7 : s1 -> p11 (* BND(1 + eA, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 assert (h2 := l9 h0).
 apply t2. exact h1. exact h2.
Qed.
Definition f21 := Float2 (1393796574908163946345982392040522594123313) (-140).
Definition f22 := Float2 (1393796574908163946345982392040522594124239) (-140).
Definition i12 := makepairF f21 f22.
Notation p13 := (BND r12 i12). (* BND(1 + eC, [1, 1]) *)
Lemma l15 : s1 -> p3 (* BND(eC, [-3.32186e-40, 3.32186e-40]) *).
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
Lemma l6 : s1 -> p10 (* BND((1 + eA) * (1 + eC), [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 assert (h2 := l14 h0).
 apply t4. exact h1. exact h2.
Qed.
Definition f23 := Float2 (170141183460469231731687303715884105727) (-127).
Definition i13 := makepairF f23 f20.
Notation p14 := (BND r14 i13). (* BND(1 + m, [1, 1]) *)
Lemma l17 : s1 -> p4 (* BND(m, [-5.87747e-39, 0]) *).
Proof.
 intros h0.
 assert (h1 := l12 h0).
 exact (proj2 h1).
Qed.
Lemma t5 : p12 -> p4 -> p14.
Proof.
 intros h0 h1.
 refine (add r5 _m i11 i4 i13 h0 h1 _) ; finalize.
Qed.
Lemma l16 : s1 -> p14 (* BND(1 + m, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 assert (h2 := l17 h0).
 apply t5. exact h1. exact h2.
Qed.
Lemma t6 : p10 -> p14 -> p9.
Proof.
 intros h0 h1.
 refine (mul_pp r21 r14 i9 i13 i8 h0 h1 _) ; finalize.
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
Lemma l4 : s1 -> p8 (* BND(Y0 - 1, [-1.00249e-37, 9.43717e-38]) *).
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
 refine (simplify (Ttree false (Tatom false (Abnd 0%nat i6)) (Tatom false (Abnd 1%nat i6))) (Tatom false (Abnd 0%nat i6)) (Abnd 1%nat i7) (List.cons r1 (List.cons r19 List.nil)) h2 h1 _) ; finalize.
Qed.
Definition f24 := Float2 (-80830486189759874946304986848438558628895449866611540495706522391509460275192517741) (-398).
Definition f25 := Float2 (80830486189759874946304986848438558628895449866611540495706522391509460275192517741) (-398).
Definition i14 := makepairF f24 f25.
Notation p15 := (BND r1 i14). (* BND(Y - 1, [-1.25209e-37, 1.25209e-37]) *)
Notation p16 := (BND r17 i14). (* BND(kw * (Y0 - 1) + s, [-1.25209e-37, 1.25209e-37]) *)
Definition f26 := Float2 (-65475528820177848903576085668406472544289023740070276579562131091388115979899884653) (-398).
Definition f27 := Float2 (65475528820177848903576085668406472544289023740070276579562131091388115979899884653) (-398).
Definition i15 := makepairF f26 f27.
Notation p17 := (BND r18 i15). (* BND(kw * (Y0 - 1), [-1.01424e-37, 1.01424e-37]) *)
Lemma l21 : s1 -> p1 (* BND(kw, [-1.01172, 1.01172]) *).
Proof.
 intros h0.
 assert (h1 := l10 h0).
 exact (proj1 h1).
Qed.
Definition f28 := Float2 (17) (-127).
Definition i16 := makepairF f13 f28.
Notation p18 := (BND r19 i16). (* BND(Y0 - 1, [-1.00249e-37, 9.9917e-38]) *)
Lemma t8 : p1 -> p18 -> p17.
Proof.
 intros h0 h1.
 refine (mul_oo _kw r19 i1 i16 i15 h0 h1 _) ; finalize.
Qed.
Lemma l20 : s1 -> p17 (* BND(kw * (Y0 - 1), [-1.01424e-37, 1.01424e-37]) *).
Proof.
 intros h0.
 assert (h1 := l21 h0).
 assert (h2 := l4 h0).
 apply t8. exact h1. refine (subset r19 i7 i16 h2 _) ; finalize.
Qed.
Lemma l22 : s1 -> p5 (* BND(s, [-2.37854e-38, 2.37854e-38]) *).
Proof.
 intros h0.
 assert (h1 := l13 h0).
 exact (proj2 h1).
Qed.
Lemma t9 : p17 -> p5 -> p16.
Proof.
 intros h0 h1.
 refine (add r18 _s i15 i5 i14 h0 h1 _) ; finalize.
Qed.
Lemma l19 : s1 -> p16 (* BND(kw * (Y0 - 1) + s, [-1.25209e-37, 1.25209e-37]) *).
Proof.
 intros h0.
 assert (h1 := l20 h0).
 assert (h2 := l22 h0).
 apply t9. exact h1. exact h2.
Qed.
Definition i17 := makepairF f8 f8.
Notation p19 := (REL r1 r17 i17). (* REL(Y - 1, kw * (Y0 - 1) + s, [0, 0]) *)
Notation p20 := (r1 = r17). (* EQL(Y - 1, kw * (Y0 - 1) + s) *)
Lemma t10 : p20.
Proof.
 refine (b1) ; finalize.
Qed.
Lemma l24 : s1 -> p20 (* EQL(Y - 1, kw * (Y0 - 1) + s) *).
Proof.
 intros h0.
 apply t10.
Qed.
Notation p21 := (REL r17 r17 i17). (* REL(kw * (Y0 - 1) + s, kw * (Y0 - 1) + s, [0, 0]) *)
Lemma t11 : p21.
Proof.
 refine (rel_refl r17 i17 _) ; finalize.
Qed.
Lemma l25 : s1 -> p21 (* REL(kw * (Y0 - 1) + s, kw * (Y0 - 1) + s, [0, 0]) *).
Proof.
 intros h0.
 apply t11.
Qed.
Lemma t12 : p20 -> p21 -> p19.
Proof.
 intros h0 h1.
 refine (rel_rewrite_1 r1 r17 r17 i17 h0 h1) ; finalize.
Qed.
Lemma l23 : s1 -> p19 (* REL(Y - 1, kw * (Y0 - 1) + s, [0, 0]) *).
Proof.
 intros h0.
 assert (h1 := l24 h0).
 assert (h2 := l25 h0).
 apply t12. exact h1. exact h2.
Qed.
Lemma t13 : p16 -> p19 -> p15.
Proof.
 intros h0 h1.
 refine (bnd_of_bnd_rel_o r1 r17 i14 i17 i14 h0 h1 _) ; finalize.
Qed.
Lemma l18 : s1 -> p15 (* BND(Y - 1, [-1.25209e-37, 1.25209e-37]) *).
Proof.
 intros h0.
 assert (h1 := l19 h0).
 assert (h2 := l23 h0).
 apply t13. exact h1. exact h2.
Qed.
Lemma l1 : s1 -> False.
Proof.
 intros h0.
 assert (h1 := l2 h0).
 assert (h2 := l18 h0).
 refine (simplify (Tatom false (Abnd 0%nat i6)) Tfalse (Abnd 0%nat i14) (List.cons r1 List.nil) h2 h1 _) ; finalize.
Qed.
End Generated_by_Gappa.
