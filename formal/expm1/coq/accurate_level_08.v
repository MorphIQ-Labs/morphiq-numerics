Require Import Gappa.Gappa_library.
Section Generated_by_Gappa.
Notation r4 := (Float1 (1)).
Variable _x : R.
Notation r12 := (Float1 (8)).
Notation r11 := ((r4 / r12)%R).
Variable _kk : R.
Notation r13 := ((r4 + _kk)%R).
Notation r10 := ((r11 * r13)%R).
Notation r8 := ((_x * r10)%R).
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
Notation r3 := ((r4 + _b)%R).
Variable _s : R.
Notation _H := ((r3 + _s)%R).
Notation r25 := ((_x / r12)%R).
Notation r24 := ((r25 * _Xn)%R).
Notation _X := ((r4 + r24)%R).
Notation r1 := ((_H - _X)%R).
Notation r32 := ((r13 * r15)%R).
Notation r31 := ((r32 * r20)%R).
Notation r30 := ((r31 - r4)%R).
Notation r29 := ((_Hn * r30)%R).
Notation r28 := ((_En + r29)%R).
Notation r27 := ((r25 * r28)%R).
Notation r26 := ((r27 + _s)%R).
Hypothesis a1 : r1 = r26.
Lemma b1 : r1 = r26.
 apply a1.
Qed.
Definition f1 := Float2 (-322782267660814808470425758868045285495962955985970070793237551831323569011153956065183521018158540984620470857862225771) (-402).
Definition f2 := Float2 (322782267660814808470425758868045285495962955985970070793237551831323569011153956065183521018158540984620470857862225771) (-402).
Definition i1 := makepairF f1 f2.
Notation p1 := (BND _x i1). (* BND(x, [-0.0312501, 0.0312501]) *)
Definition f3 := Float2 (2547264526420885795406733506348965440254549081195361853818647964145151668315355845405166260805402565320614812873495093209) (-400).
Definition f4 := Float2 (654355084583860510986838580555725836077768457355711033682547003688029298010777705278790367970505746057909503447720689987) (-398).
Definition i2 := makepairF f3 f4.
Notation p2 := (BND _Xn i2). (* BND(Xn, [0.986452, 1.01362]) *)
Definition s7 := (p1 /\ p2).
Definition f5 := Float2 (-261) (-134).
Definition f6 := Float2 (261) (-134).
Definition i3 := makepairF f5 f6.
Notation p3 := (BND _En i3). (* BND(En, [-1.19845e-38, 1.19845e-38]) *)
Definition s6 := (s7 /\ p3).
Definition f7 := Float2 (-1) (-127).
Definition f8 := Float2 (1) (-127).
Definition i4 := makepairF f7 f8.
Notation p4 := (BND _kk i4). (* BND(kk, [-5.87747e-39, 5.87747e-39]) *)
Definition s5 := (s6 /\ p4).
Definition f9 := Float2 (0) (0).
Definition i5 := makepairF f7 f9.
Notation p5 := (BND _ma i5). (* BND(ma, [-5.87747e-39, 0]) *)
Definition s4 := (s5 /\ p5).
Notation p6 := (BND _mb i5). (* BND(mb, [-5.87747e-39, 0]) *)
Definition s3 := (s4 /\ p6).
Definition f10 := Float2 (-1) (-126).
Definition f11 := Float2 (1) (-126).
Definition i6 := makepairF f10 f11.
Notation p7 := (BND _s i6). (* BND(s, [-1.17549e-38, 1.17549e-38]) *)
Definition s2 := (s3 /\ p7).
Definition f12 := Float2 (-523) (-135).
Definition f13 := Float2 (523) (-135).
Definition i7 := makepairF f12 f13.
Notation p8 := (BND r1 i7). (* BND(H - X, [-1.20075e-38, 1.20075e-38]) *)
Definition s8 := (not p8).
Definition s1 := (s2 /\ s8).
Lemma l2 : s1 -> s8.
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj2 h1).
Qed.
Definition f14 := Float2 (-651967582746072174618696348202318003783844862500273514416917137457969052024636740678072537923610601458996738928186407903) (-524).
Definition f15 := Float2 (651967582746072174618696348202318003783844862500273514416917137457969052024636740678072537923610601458996738928186407903) (-524).
Definition i8 := makepairF f14 f15.
Notation p9 := (BND r1 i8). (* BND(H - X, [-1.18716e-38, 1.18716e-38]) *)
Notation p10 := (BND r26 i8). (* BND(x / 8 * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1)) + s, [-1.18716e-38, 1.18716e-38]) *)
Definition f16 := Float2 (-6405113224345027204716555201565035201418414292967636209252298322807146520426442020661199603576143600020945934999534559) (-524).
Definition f17 := Float2 (6405113224345027204716555201565035201418414292967636209252298322807146520426442020661199603576143600020945934999534559) (-524).
Definition i9 := makepairF f16 f17.
Notation p11 := (BND r27 i9). (* BND(x / 8 * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1)), [-1.1663e-40, 1.1663e-40]) *)
Definition f18 := Float2 (-20173891728800925529401609929252830343497684749123129424577346989457723063197122254073970063634908811538779428616389111) (-401).
Definition f19 := Float2 (20173891728800925529401609929252830343497684749123129424577346989457723063197122254073970063634908811538779428616389111) (-401).
Definition i10 := makepairF f18 f19.
Notation p12 := (BND r25 i10). (* BND(x / 8, [-0.00390626, 0.00390626]) *)
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
Lemma l9 : s1 -> s6.
Proof.
 intros h0.
 assert (h1 := l10 h0).
 exact (proj1 h1).
Qed.
Lemma l8 : s1 -> s7.
Proof.
 intros h0.
 assert (h1 := l9 h0).
 exact (proj1 h1).
Qed.
Lemma l7 : s1 -> p1 (* BND(x, [-0.0312501, 0.0312501]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 exact (proj1 h1).
Qed.
Definition f20 := Float2 (1) (3).
Definition i11 := makepairF f20 f20.
Notation p13 := (BND r12 i11). (* BND(8, [8, 8]) *)
Lemma t1 : p13.
Proof.
 refine (constant1 _ i11 _) ; finalize.
Qed.
Lemma l14 : s1 -> p13 (* BND(8, [8, 8]) *).
Proof.
 intros h0.
 apply t1.
Qed.
Definition f21 := Float2 (-20173891728800925529401609929252830343497684749123129424577346989457723063197122254073970063634908811538779428616389111) (-398).
Definition f22 := Float2 (20173891728800925529401609929252830343497684749123129424577346989457723063197122254073970063634908811538779428616389111) (-398).
Definition i12 := makepairF f21 f22.
Notation p14 := (BND _x i12). (* BND(x, [-0.0312501, 0.0312501]) *)
Lemma t2 : p14 -> p13 -> p12.
Proof.
 intros h0 h1.
 refine (div_op _x r12 i12 i11 i10 h0 h1 _) ; finalize.
Qed.
Lemma l6 : s1 -> p12 (* BND(x / 8, [-0.00390626, 0.00390626]) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 assert (h2 := l14 h0).
 apply t2. refine (subset _x i1 i12 h1 _) ; finalize. exact h2.
Qed.
Definition f23 := Float2 (-51240741824386379601317717395824614972579402089654402779929490808086586286335419891945942601592823703131717458500409269) (-519).
Definition f24 := Float2 (1) (-125).
Definition i13 := makepairF f23 f24.
Notation p15 := (BND r28 i13). (* BND(En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1), [-2.98571e-38, 2.35099e-38]) *)
Lemma l16 : s1 -> p3 (* BND(En, [-1.19845e-38, 1.19845e-38]) *).
Proof.
 intros h0.
 assert (h1 := l9 h0).
 exact (proj2 h1).
Qed.
Definition f25 := Float2 (-30672894589868461452508058463549648566327778190471439619260481651070319521613875952787695616542897738630657647560251317) (-519).
Definition f26 := Float2 (3) (-128).
Definition i14 := makepairF f25 f26.
Notation p16 := (BND r29 i14). (* BND(Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1), [-1.78726e-38, 8.81621e-39]) *)
Definition f27 := Float2 (1) (-1).
Definition f28 := Float2 (81794385572982563873354822569465729510688152698773944074496040327796223657737724071776225987170767998872778389717831721) (-395).
Definition i15 := makepairF f27 f28.
Notation p17 := (BND _Hn i15). (* BND(Hn, [0.5, 1.01362]) *)
Lemma l19 : s1 -> p2 (* BND(Xn, [0.986452, 1.01362]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 exact (proj2 h1).
Qed.
Definition f29 := Float2 (3) (-2).
Definition f30 := Float2 (81794385572982563873354822569465729509721057169463879210318375461003662251347213159848795996313218257238687930965086249) (-395).
Definition i16 := makepairF f29 f30.
Notation p18 := (BND _Xn i16). (* BND(Xn, [0.75, 1.01362]) *)
Definition f31 := Float2 (-1) (-2).
Definition i17 := makepairF f31 f6.
Notation p19 := (BND _En i17). (* BND(En, [-0.25, 1.19845e-38]) *)
Lemma t3 : p18 -> p19 -> p17.
Proof.
 intros h0 h1.
 refine (add _Xn _En i16 i17 i15 h0 h1 _) ; finalize.
Qed.
Lemma l18 : s1 -> p17 (* BND(Hn, [0.5, 1.01362]) *).
Proof.
 intros h0.
 assert (h1 := l19 h0).
 assert (h2 := l16 h0).
 apply t3. refine (subset _Xn i2 i16 h1 _) ; finalize. refine (subset _En i3 i17 h2 _) ; finalize.
Qed.
Definition f32 := Float2 (-86844066927987146567678238756515930889442064948849015334398126094787194912769) (-381).
Definition i18 := makepairF f32 f8.
Notation p20 := (BND r30 i18). (* BND((1 + kk) * (1 + ma) * (1 + mb) - 1, [-1.76324e-38, 5.87747e-39]) *)
Definition f33 := Float2 (4925250774549309901534880012517951725548123341880193686925858436774199290547709261477934266526216329006041303875583) (-381).
Definition f34 := Float2 (170141183460469231731687303715884105729) (-127).
Definition i19 := makepairF f33 f34.
Notation p21 := (BND r31 i19). (* BND((1 + kk) * (1 + ma) * (1 + mb), [1, 1]) *)
Definition f35 := Float2 (28948022309329048855892746252171976962977213799489202546401021394546514198529) (-254).
Definition i20 := makepairF f35 f34.
Notation p22 := (BND r32 i20). (* BND((1 + kk) * (1 + ma), [1, 1]) *)
Definition f36 := Float2 (170141183460469231731687303715884105727) (-127).
Definition i21 := makepairF f36 f34.
Notation p23 := (BND r13 i21). (* BND(1 + kk, [1, 1]) *)
Definition f37 := Float2 (1) (0).
Definition i22 := makepairF f37 f37.
Notation p24 := (BND r4 i22). (* BND(1, [1, 1]) *)
Lemma t4 : p24.
Proof.
 refine (constant1 _ i22 _) ; finalize.
Qed.
Lemma l24 : s1 -> p24 (* BND(1, [1, 1]) *).
Proof.
 intros h0.
 apply t4.
Qed.
Lemma l25 : s1 -> p4 (* BND(kk, [-5.87747e-39, 5.87747e-39]) *).
Proof.
 intros h0.
 assert (h1 := l10 h0).
 exact (proj2 h1).
Qed.
Lemma t5 : p24 -> p4 -> p23.
Proof.
 intros h0 h1.
 refine (add r4 _kk i22 i4 i21 h0 h1 _) ; finalize.
Qed.
Lemma l23 : s1 -> p23 (* BND(1 + kk, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l24 h0).
 assert (h2 := l25 h0).
 apply t5. exact h1. exact h2.
Qed.
Definition i23 := makepairF f36 f37.
Notation p25 := (BND r15 i23). (* BND(1 + ma, [1, 1]) *)
Lemma l27 : s1 -> p5 (* BND(ma, [-5.87747e-39, 0]) *).
Proof.
 intros h0.
 assert (h1 := l11 h0).
 exact (proj2 h1).
Qed.
Lemma t6 : p24 -> p5 -> p25.
Proof.
 intros h0 h1.
 refine (add r4 _ma i22 i5 i23 h0 h1 _) ; finalize.
Qed.
Lemma l26 : s1 -> p25 (* BND(1 + ma, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l24 h0).
 assert (h2 := l27 h0).
 apply t6. exact h1. exact h2.
Qed.
Lemma t7 : p23 -> p25 -> p22.
Proof.
 intros h0 h1.
 refine (mul_pp r13 r15 i21 i23 i20 h0 h1 _) ; finalize.
Qed.
Lemma l22 : s1 -> p22 (* BND((1 + kk) * (1 + ma), [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l23 h0).
 assert (h2 := l26 h0).
 apply t7. exact h1. exact h2.
Qed.
Notation p26 := (BND r20 i23). (* BND(1 + mb, [1, 1]) *)
Lemma l29 : s1 -> p6 (* BND(mb, [-5.87747e-39, 0]) *).
Proof.
 intros h0.
 assert (h1 := l12 h0).
 exact (proj2 h1).
Qed.
Lemma t8 : p24 -> p6 -> p26.
Proof.
 intros h0 h1.
 refine (add r4 _mb i22 i5 i23 h0 h1 _) ; finalize.
Qed.
Lemma l28 : s1 -> p26 (* BND(1 + mb, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l24 h0).
 assert (h2 := l29 h0).
 apply t8. exact h1. exact h2.
Qed.
Lemma t9 : p22 -> p26 -> p21.
Proof.
 intros h0 h1.
 refine (mul_pp r32 r20 i20 i23 i19 h0 h1 _) ; finalize.
Qed.
Lemma l21 : s1 -> p21 (* BND((1 + kk) * (1 + ma) * (1 + mb), [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l22 h0).
 assert (h2 := l28 h0).
 apply t9. exact h1. exact h2.
Qed.
Lemma t10 : p21 -> p24 -> p20.
Proof.
 intros h0 h1.
 refine (sub r31 r4 i19 i22 i18 h0 h1 _) ; finalize.
Qed.
Lemma l20 : s1 -> p20 (* BND((1 + kk) * (1 + ma) * (1 + mb) - 1, [-1.76324e-38, 5.87747e-39]) *).
Proof.
 intros h0.
 assert (h1 := l21 h0).
 assert (h2 := l24 h0).
 apply t10. exact h1. exact h2.
Qed.
Lemma t11 : p17 -> p20 -> p16.
Proof.
 intros h0 h1.
 refine (mul_po _Hn r30 i15 i18 i14 h0 h1 _) ; finalize.
Qed.
Lemma l17 : s1 -> p16 (* BND(Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1), [-1.78726e-38, 8.81621e-39]) *).
Proof.
 intros h0.
 assert (h1 := l18 h0).
 assert (h2 := l20 h0).
 apply t11. exact h1. exact h2.
Qed.
Definition f38 := Float2 (5) (-128).
Definition i24 := makepairF f5 f38.
Notation p27 := (BND _En i24). (* BND(En, [-1.19845e-38, 1.46937e-38]) *)
Lemma t12 : p27 -> p16 -> p15.
Proof.
 intros h0 h1.
 refine (add _En r29 i24 i14 i13 h0 h1 _) ; finalize.
Qed.
Lemma l15 : s1 -> p15 (* BND(En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1), [-2.98571e-38, 2.35099e-38]) *).
Proof.
 intros h0.
 assert (h1 := l16 h0).
 assert (h2 := l17 h0).
 apply t12. refine (subset _En i3 i24 h1 _) ; finalize. exact h2.
Qed.
Lemma t13 : p12 -> p15 -> p11.
Proof.
 intros h0 h1.
 refine (mul_oo r25 r28 i10 i13 i9 h0 h1 _) ; finalize.
Qed.
Lemma l5 : s1 -> p11 (* BND(x / 8 * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1)), [-1.1663e-40, 1.1663e-40]) *).
Proof.
 intros h0.
 assert (h1 := l6 h0).
 assert (h2 := l15 h0).
 apply t13. exact h1. exact h2.
Qed.
Lemma l30 : s1 -> p7 (* BND(s, [-1.17549e-38, 1.17549e-38]) *).
Proof.
 intros h0.
 assert (h1 := l13 h0).
 exact (proj2 h1).
Qed.
Lemma t14 : p11 -> p7 -> p10.
Proof.
 intros h0 h1.
 refine (add r27 _s i9 i6 i8 h0 h1 _) ; finalize.
Qed.
Lemma l4 : s1 -> p10 (* BND(x / 8 * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1)) + s, [-1.18716e-38, 1.18716e-38]) *).
Proof.
 intros h0.
 assert (h1 := l5 h0).
 assert (h2 := l30 h0).
 apply t14. exact h1. exact h2.
Qed.
Definition i25 := makepairF f9 f9.
Notation p28 := (REL r1 r26 i25). (* REL(H - X, x / 8 * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1)) + s, [0, 0]) *)
Notation p29 := (r1 = r26). (* EQL(H - X, x / 8 * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1)) + s) *)
Lemma t15 : p29.
Proof.
 refine (b1) ; finalize.
Qed.
Lemma l32 : s1 -> p29 (* EQL(H - X, x / 8 * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1)) + s) *).
Proof.
 intros h0.
 apply t15.
Qed.
Notation p30 := (REL r26 r26 i25). (* REL(x / 8 * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1)) + s, x / 8 * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1)) + s, [0, 0]) *)
Lemma t16 : p30.
Proof.
 refine (rel_refl r26 i25 _) ; finalize.
Qed.
Lemma l33 : s1 -> p30 (* REL(x / 8 * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1)) + s, x / 8 * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1)) + s, [0, 0]) *).
Proof.
 intros h0.
 apply t16.
Qed.
Lemma t17 : p29 -> p30 -> p28.
Proof.
 intros h0 h1.
 refine (rel_rewrite_1 r1 r26 r26 i25 h0 h1) ; finalize.
Qed.
Lemma l31 : s1 -> p28 (* REL(H - X, x / 8 * (En + Hn * ((1 + kk) * (1 + ma) * (1 + mb) - 1)) + s, [0, 0]) *).
Proof.
 intros h0.
 assert (h1 := l32 h0).
 assert (h2 := l33 h0).
 apply t17. exact h1. exact h2.
Qed.
Lemma t18 : p10 -> p28 -> p9.
Proof.
 intros h0 h1.
 refine (bnd_of_bnd_rel_o r1 r26 i8 i25 i8 h0 h1 _) ; finalize.
Qed.
Lemma l3 : s1 -> p9 (* BND(H - X, [-1.18716e-38, 1.18716e-38]) *).
Proof.
 intros h0.
 assert (h1 := l4 h0).
 assert (h2 := l31 h0).
 apply t18. exact h1. exact h2.
Qed.
Lemma l1 : s1 -> False.
Proof.
 intros h0.
 assert (h1 := l2 h0).
 assert (h2 := l3 h0).
 refine (simplify (Tatom false (Abnd 0%nat i7)) Tfalse (Abnd 0%nat i8) (List.cons r1 List.nil) h2 h1 _) ; finalize.
Qed.
End Generated_by_Gappa.
