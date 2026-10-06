Require Import Gappa.Gappa_library.
Section Generated_by_Gappa.
Variable _X1 : R.
Notation r8 := (Float1 (1)).
Variable _k3 : R.
Notation _k2 := ((r8 - _k3)%R).
Variable _eN : R.
Notation r10 := ((r8 + _eN)%R).
Notation r6 := ((_k2 * r10)%R).
Variable _E1 : R.
Notation _q := ((_E1 / _X1)%R).
Notation r14 := ((r8 + _q)%R).
Notation r13 := ((_k3 * r14)%R).
Variable _mz : R.
Notation r17 := ((r8 + _mz)%R).
Notation r12 := ((r13 * r17)%R).
Notation r5 := ((r6 + r12)%R).
Variable _dz : R.
Notation r4 := ((r5 + _dz)%R).
Variable _s2 : R.
Notation _Y := ((r4 + _s2)%R).
Notation r2 := ((_Y - r8)%R).
Notation r24 := ((_k2 * _eN)%R).
Notation r27 := ((r14 * _mz)%R).
Notation r26 := ((_q + r27)%R).
Notation r25 := ((_k3 * r26)%R).
Notation r23 := ((r24 + r25)%R).
Notation r22 := ((r23 + _dz)%R).
Notation r21 := ((r22 + _s2)%R).
Hypothesis a1 : (_X1 <> 0)%R -> r2 = r21.
Lemma b1 : NZR _X1 -> r2 = r21.
 intros h0.
 apply a1.
 exact h0.
Qed.
Definition f1 := Float2 (-533) (-10).
Definition f2 := Float2 (533) (-10).
Definition i1 := makepairF f1 f2.
Notation p1 := (BND _k3 i1). (* BND(k3, [-0.520508, 0.520508]) *)
Definition f3 := Float2 (-409) (-134).
Definition f4 := Float2 (409) (-134).
Definition i2 := makepairF f3 f4.
Notation p2 := (BND _E1 i2). (* BND(E1, [-1.87804e-38, 1.87804e-38]) *)
Definition s7 := (p1 /\ p2).
Definition f5 := Float2 (2569643334182088301921218974605293170359228169148631243641020077562016180326154975917463424665424198542833092687176540113) (-400).
Definition f6 := Float2 (1297491476117877567955756254720079362941012786046832206986213668913874777720503119280182067258581095541356805256872555633) (-399).
Definition i3 := makepairF f5 f6.
Notation p3 := (BND _X1 i3). (* BND(X1, [0.995118, 1.00493]) *)
Definition s6 := (s7 /\ p3).
Definition f7 := Float2 (-1) (-127).
Definition f8 := Float2 (0) (0).
Definition i4 := makepairF f7 f8.
Notation p4 := (BND _mz i4). (* BND(mz, [-5.87747e-39, 0]) *)
Definition s5 := (s6 /\ p4).
Definition f9 := Float2 (1) (-127).
Definition i5 := makepairF f7 f9.
Notation p5 := (BND _eN i5). (* BND(eN, [-5.87747e-39, 5.87747e-39]) *)
Definition s4 := (s5 /\ p5).
Definition f10 := Float2 (-49) (-131).
Definition f11 := Float2 (49) (-131).
Definition i6 := makepairF f10 f11.
Notation p6 := (BND _s2 i6). (* BND(s2, [-1.79998e-38, 1.79998e-38]) *)
Definition s3 := (s4 /\ p6).
Definition f12 := Float2 (-131) (-133).
Definition f13 := Float2 (131) (-133).
Definition i7 := makepairF f12 f13.
Notation p7 := (BND _dz i7). (* BND(dz, [-1.20304e-38, 1.20304e-38]) *)
Definition s2 := (s3 /\ p7).
Definition f14 := Float2 (-1) (-123).
Definition f15 := Float2 (1) (-123).
Definition i8 := makepairF f14 f15.
Notation p8 := (BND r2 i8). (* BND(Y - 1, [-9.40395e-38, 9.40395e-38]) *)
Definition s8 := (not p8).
Definition s1 := (s2 /\ s8).
Lemma l2 : s1 -> s8.
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj2 h1).
Qed.
Definition f16 := Float2 (-1423745298216332753967321626489603811436896131405118682118788619206329650997499542125451754963357741451531796129561883749) (-523).
Definition f17 := Float2 (1423745298216332753967321626489603811436896131405118682118788619206329650997499542125451754963357741451531796129561883749) (-523).
Definition i9 := makepairF f16 f17.
Notation p9 := (BND r2 i9). (* BND(Y - 1, [-5.18495e-38, 5.18495e-38]) *)
Notation p10 := (BND r21 i9). (* BND(k2 * eN + k3 * (q + (1 + q) * mz) + dz + s2, [-5.18495e-38, 5.18495e-38]) *)
Definition f18 := Float2 (-929486532488760406728493347473402319865975881996400119116045226743471317095838532215871199062081359653253454619153183845) (-523).
Definition f19 := Float2 (929486532488760406728493347473402319865975881996400119116045226743471317095838532215871199062081359653253454619153183845) (-523).
Definition i10 := makepairF f18 f19.
Notation p11 := (BND r22 i10). (* BND(k2 * eN + k3 * (q + (1 + q) * mz) + dz, [-3.38497e-38, 3.38497e-38]) *)
Definition f20 := Float2 (-599140112538189093012745875273798261724187347952817814251966734842275185763605918449773990781126226920730685548420838501) (-523).
Definition f21 := Float2 (599140112538189093012745875273798261724187347952817814251966734842275185763605918449773990781126226920730685548420838501) (-523).
Definition i11 := makepairF f20 f21.
Notation p12 := (BND r23 i11). (* BND(k2 * eN + k3 * (q + (1 + q) * mz), [-2.18193e-38, 2.18193e-38]) *)
Definition f22 := Float2 (-1557) (-137).
Definition f23 := Float2 (1557) (-137).
Definition i12 := makepairF f22 f23.
Notation p13 := (BND r24 i12). (* BND(k2 * eN, [-8.93674e-39, 8.93674e-39]) *)
Definition f24 := Float2 (1) (-2).
Definition f25 := Float2 (1557) (-10).
Definition i13 := makepairF f24 f25.
Notation p14 := (BND _k2 i13). (* BND(k2, [0.25, 1.52051]) *)
Definition f26 := Float2 (1) (0).
Definition i14 := makepairF f26 f26.
Notation p15 := (BND r8 i14). (* BND(1, [1, 1]) *)
Lemma t1 : p15.
Proof.
 refine (constant1 _ i14 _) ; finalize.
Qed.
Lemma l9 : s1 -> p15 (* BND(1, [1, 1]) *).
Proof.
 intros h0.
 apply t1.
Qed.
Lemma l16 : s1 -> s2.
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj1 h1).
Qed.
Lemma l15 : s1 -> s3.
Proof.
 intros h0.
 assert (h1 := l16 h0).
 exact (proj1 h1).
Qed.
Lemma l14 : s1 -> s4.
Proof.
 intros h0.
 assert (h1 := l15 h0).
 exact (proj1 h1).
Qed.
Lemma l13 : s1 -> s5.
Proof.
 intros h0.
 assert (h1 := l14 h0).
 exact (proj1 h1).
Qed.
Lemma l12 : s1 -> s6.
Proof.
 intros h0.
 assert (h1 := l13 h0).
 exact (proj1 h1).
Qed.
Lemma l11 : s1 -> s7.
Proof.
 intros h0.
 assert (h1 := l12 h0).
 exact (proj1 h1).
Qed.
Lemma l10 : s1 -> p1 (* BND(k3, [-0.520508, 0.520508]) *).
Proof.
 intros h0.
 assert (h1 := l11 h0).
 exact (proj1 h1).
Qed.
Definition f27 := Float2 (3) (-2).
Definition i15 := makepairF f1 f27.
Notation p16 := (BND _k3 i15). (* BND(k3, [-0.520508, 0.75]) *)
Lemma t2 : p15 -> p16 -> p14.
Proof.
 intros h0 h1.
 refine (sub r8 _k3 i14 i15 i13 h0 h1 _) ; finalize.
Qed.
Lemma l8 : s1 -> p14 (* BND(k2, [0.25, 1.52051]) *).
Proof.
 intros h0.
 assert (h1 := l9 h0).
 assert (h2 := l10 h0).
 apply t2. exact h1. refine (subset _k3 i1 i15 h2 _) ; finalize.
Qed.
Lemma l17 : s1 -> p5 (* BND(eN, [-5.87747e-39, 5.87747e-39]) *).
Proof.
 intros h0.
 assert (h1 := l14 h0).
 exact (proj2 h1).
Qed.
Lemma t3 : p14 -> p5 -> p13.
Proof.
 intros h0 h1.
 refine (mul_po _k2 _eN i13 i5 i12 h0 h1 _) ; finalize.
Qed.
Lemma l7 : s1 -> p13 (* BND(k2 * eN, [-8.93674e-39, 8.93674e-39]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 assert (h2 := l17 h0).
 apply t3. exact h1. exact h2.
Qed.
Definition f28 := Float2 (-353744417947044276478672013530103834946150731776359012403984763520632830570721290761885940545702972309787006424789988453) (-523).
Definition f29 := Float2 (353744417947044276478672013530103834946150731776359012403984763520632830570721290761885940545702972309787006424789988453) (-523).
Definition i16 := makepairF f28 f29.
Notation p17 := (BND r25 i16). (* BND(k3 * (q + (1 + q) * mz), [-1.28826e-38, 1.28826e-38]) *)
Definition f30 := Float2 (-1359228082468192642079400157053757324521044462810475154602928322120555416526899068443419148663414047449237878345159280209) (-524).
Definition f31 := Float2 (1) (-125).
Definition i17 := makepairF f30 f31.
Notation p18 := (BND r26 i17). (* BND(q + (1 + q) * mz, [-2.475e-38, 2.35099e-38]) *)
Definition f32 := Float2 (-2072893695414658136744820521106761680447479103269569100308133363379088737397396057481383782602400020527724941713990131053) (-525).
Definition f33 := Float2 (12183374144075330690058441726860190152191780748043176404393616511775021983141556021) (-398).
Definition i18 := makepairF f32 f33.
Notation p19 := (BND _q i18). (* BND(q, [-1.88725e-38, 1.88725e-38]) *)
Lemma l21 : s1 -> p2 (* BND(E1, [-1.87804e-38, 1.87804e-38]) *).
Proof.
 intros h0.
 assert (h1 := l11 h0).
 exact (proj2 h1).
Qed.
Lemma l22 : s1 -> p3 (* BND(X1, [0.995118, 1.00493]) *).
Proof.
 intros h0.
 assert (h1 := l12 h0).
 exact (proj2 h1).
Qed.
Definition f34 := Float2 (160602708386380518870076185912830823147451760571789452727563754847626011270384685994841464041589012408927068292948533757) (-396).
Definition f35 := Float2 (1) (1).
Definition i19 := makepairF f34 f35.
Notation p20 := (BND _X1 i19). (* BND(X1, [0.995118, 2]) *)
Lemma t4 : p2 -> p20 -> p19.
Proof.
 intros h0 h1.
 refine (div_op _E1 _X1 i2 i19 i18 h0 h1 _) ; finalize.
Qed.
Lemma l20 : s1 -> p19 (* BND(q, [-1.88725e-38, 1.88725e-38]) *).
Proof.
 intros h0.
 assert (h1 := l21 h0).
 assert (h2 := l22 h0).
 apply t4. exact h1. refine (subset _X1 i3 i19 h2 _) ; finalize.
Qed.
Definition f36 := Float2 (-645562469521727147413979793000752968594609822351381208897723280862022095656402079405454514724428074370750814976328429365) (-525).
Definition i20 := makepairF f36 f8.
Notation p21 := (BND r27 i20). (* BND((1 + q) * mz, [-5.87747e-39, 0]) *)
Definition f37 := Float2 (1) (-1).
Definition f38 := Float2 (645562469521727147413979793000752968594609822351381208897723280862022095656402079405454514724428074370750814976328429365) (-398).
Definition i21 := makepairF f37 f38.
Notation p22 := (BND r14 i21). (* BND(1 + q, [0.5, 1]) *)
Definition f39 := Float2 (-1) (-1).
Definition i22 := makepairF f39 f33.
Notation p23 := (BND _q i22). (* BND(q, [-0.5, 1.88725e-38]) *)
Lemma t5 : p15 -> p23 -> p22.
Proof.
 intros h0 h1.
 refine (add r8 _q i14 i22 i21 h0 h1 _) ; finalize.
Qed.
Lemma l24 : s1 -> p22 (* BND(1 + q, [0.5, 1]) *).
Proof.
 intros h0.
 assert (h1 := l9 h0).
 assert (h2 := l20 h0).
 apply t5. exact h1. refine (subset _q i18 i22 h2 _) ; finalize.
Qed.
Lemma l25 : s1 -> p4 (* BND(mz, [-5.87747e-39, 0]) *).
Proof.
 intros h0.
 assert (h1 := l13 h0).
 exact (proj2 h1).
Qed.
Lemma t6 : p22 -> p4 -> p21.
Proof.
 intros h0 h1.
 refine (mul_pn r14 _mz i21 i4 i20 h0 h1 _) ; finalize.
Qed.
Lemma l23 : s1 -> p21 (* BND((1 + q) * mz, [-5.87747e-39, 0]) *).
Proof.
 intros h0.
 assert (h1 := l24 h0).
 assert (h2 := l25 h0).
 apply t6. exact h1. exact h2.
Qed.
Definition i23 := makepairF f32 f31.
Notation p24 := (BND _q i23). (* BND(q, [-1.88725e-38, 2.35099e-38]) *)
Lemma t7 : p24 -> p21 -> p18.
Proof.
 intros h0 h1.
 refine (add _q r27 i23 i20 i17 h0 h1 _) ; finalize.
Qed.
Lemma l19 : s1 -> p18 (* BND(q + (1 + q) * mz, [-2.475e-38, 2.35099e-38]) *).
Proof.
 intros h0.
 assert (h1 := l20 h0).
 assert (h2 := l23 h0).
 apply t7. refine (subset _q i18 i23 h1 _) ; finalize. exact h2.
Qed.
Lemma t8 : p1 -> p18 -> p17.
Proof.
 intros h0 h1.
 refine (mul_oo _k3 r26 i1 i17 i16 h0 h1 _) ; finalize.
Qed.
Lemma l18 : s1 -> p17 (* BND(k3 * (q + (1 + q) * mz), [-1.28826e-38, 1.28826e-38]) *).
Proof.
 intros h0.
 assert (h1 := l10 h0).
 assert (h2 := l19 h0).
 apply t8. exact h1. exact h2.
Qed.
Lemma t9 : p13 -> p17 -> p12.
Proof.
 intros h0 h1.
 refine (add r24 r25 i12 i16 i11 h0 h1 _) ; finalize.
Qed.
Lemma l6 : s1 -> p12 (* BND(k2 * eN + k3 * (q + (1 + q) * mz), [-2.18193e-38, 2.18193e-38]) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 assert (h2 := l18 h0).
 apply t9. exact h1. exact h2.
Qed.
Lemma l26 : s1 -> p7 (* BND(dz, [-1.20304e-38, 1.20304e-38]) *).
Proof.
 intros h0.
 assert (h1 := l16 h0).
 exact (proj2 h1).
Qed.
Lemma t10 : p12 -> p7 -> p11.
Proof.
 intros h0 h1.
 refine (add r23 _dz i11 i7 i10 h0 h1 _) ; finalize.
Qed.
Lemma l5 : s1 -> p11 (* BND(k2 * eN + k3 * (q + (1 + q) * mz) + dz, [-3.38497e-38, 3.38497e-38]) *).
Proof.
 intros h0.
 assert (h1 := l6 h0).
 assert (h2 := l26 h0).
 apply t10. exact h1. exact h2.
Qed.
Lemma l27 : s1 -> p6 (* BND(s2, [-1.79998e-38, 1.79998e-38]) *).
Proof.
 intros h0.
 assert (h1 := l15 h0).
 exact (proj2 h1).
Qed.
Lemma t11 : p11 -> p6 -> p10.
Proof.
 intros h0 h1.
 refine (add r22 _s2 i10 i6 i9 h0 h1 _) ; finalize.
Qed.
Lemma l4 : s1 -> p10 (* BND(k2 * eN + k3 * (q + (1 + q) * mz) + dz + s2, [-5.18495e-38, 5.18495e-38]) *).
Proof.
 intros h0.
 assert (h1 := l5 h0).
 assert (h2 := l27 h0).
 apply t11. exact h1. exact h2.
Qed.
Definition i24 := makepairF f8 f8.
Notation p25 := (REL r2 r21 i24). (* REL(Y - 1, k2 * eN + k3 * (q + (1 + q) * mz) + dz + s2, [0, 0]) *)
Notation p26 := (r2 = r21). (* EQL(Y - 1, k2 * eN + k3 * (q + (1 + q) * mz) + dz + s2) *)
Notation p27 := (NZR _X1). (* NZR(X1) *)
Definition i25 := makepairF f37 f35.
Notation p28 := (ABS _X1 i25). (* ABS(X1, [0.5, 2]) *)
Notation p29 := (BND _X1 i25). (* BND(X1, [0.5, 2]) *)
Lemma t12 : p29 -> p28.
Proof.
 intros h0.
 refine (abs_of_bnd_p _X1 i25 i25 h0 _) ; finalize.
Qed.
Lemma l31 : s1 -> p28 (* ABS(X1, [0.5, 2]) *).
Proof.
 intros h0.
 assert (h1 := l22 h0).
 apply t12. refine (subset _X1 i3 i25 h1 _) ; finalize.
Qed.
Lemma t13 : p28 -> p27.
Proof.
 intros h0.
 refine (nzr_of_abs _X1 i25 h0 _) ; finalize.
Qed.
Lemma l30 : s1 -> p27 (* NZR(X1) *).
Proof.
 intros h0.
 assert (h1 := l31 h0).
 apply t13. exact h1.
Qed.
Lemma t14 : p27 -> p26.
Proof.
 intros h0.
 refine (b1 h0) ; finalize.
Qed.
Lemma l29 : s1 -> p26 (* EQL(Y - 1, k2 * eN + k3 * (q + (1 + q) * mz) + dz + s2) *).
Proof.
 intros h0.
 assert (h1 := l30 h0).
 apply t14. exact h1.
Qed.
Notation p30 := (REL r21 r21 i24). (* REL(k2 * eN + k3 * (q + (1 + q) * mz) + dz + s2, k2 * eN + k3 * (q + (1 + q) * mz) + dz + s2, [0, 0]) *)
Lemma t15 : p30.
Proof.
 refine (rel_refl r21 i24 _) ; finalize.
Qed.
Lemma l32 : s1 -> p30 (* REL(k2 * eN + k3 * (q + (1 + q) * mz) + dz + s2, k2 * eN + k3 * (q + (1 + q) * mz) + dz + s2, [0, 0]) *).
Proof.
 intros h0.
 apply t15.
Qed.
Lemma t16 : p26 -> p30 -> p25.
Proof.
 intros h0 h1.
 refine (rel_rewrite_1 r2 r21 r21 i24 h0 h1) ; finalize.
Qed.
Lemma l28 : s1 -> p25 (* REL(Y - 1, k2 * eN + k3 * (q + (1 + q) * mz) + dz + s2, [0, 0]) *).
Proof.
 intros h0.
 assert (h1 := l29 h0).
 assert (h2 := l32 h0).
 apply t16. exact h1. exact h2.
Qed.
Lemma t17 : p10 -> p25 -> p9.
Proof.
 intros h0 h1.
 refine (bnd_of_bnd_rel_o r2 r21 i9 i24 i9 h0 h1 _) ; finalize.
Qed.
Lemma l3 : s1 -> p9 (* BND(Y - 1, [-5.18495e-38, 5.18495e-38]) *).
Proof.
 intros h0.
 assert (h1 := l4 h0).
 assert (h2 := l28 h0).
 apply t17. exact h1. exact h2.
Qed.
Lemma l1 : s1 -> False.
Proof.
 intros h0.
 assert (h1 := l2 h0).
 assert (h2 := l3 h0).
 refine (simplify (Tatom false (Abnd 0%nat i8)) Tfalse (Abnd 0%nat i9) (List.cons r2 List.nil) h2 h1 _) ; finalize.
Qed.
End Generated_by_Gappa.
