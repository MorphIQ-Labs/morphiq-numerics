Require Import Gappa.Gappa_library.
Section Generated_by_Gappa.
Notation r4 := (Float1 (1)).
Variable _r : R.
Notation r12 := (Float1 (12)).
Notation r11 := ((r4 / r12)%R).
Variable _k : R.
Notation r13 := ((r4 + _k)%R).
Notation r10 := ((r11 * r13)%R).
Notation r8 := ((_r * r10)%R).
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
Notation r25 := ((_r / r12)%R).
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
Definition f1 := Float2 (-1790007352290235156241996271091137421647354200530680685578972007844036001509683862225447344028661048310307483921358249617) (-408).
Definition f2 := Float2 (1790007352290235156241996271091137421647354200530680685578972007844036001509683862225447344028661048310307483921358249617) (-408).
Definition i1 := makepairF f1 f2.
Notation p1 := (BND _r i1). (* BND(r, [-0.0027078, 0.0027078]) *)
Definition f3 := Float2 (1278213689653019751879679990141490877793204367450465638851176381487620572898336391341674449873668226560772070126510009221) (-399).
Definition f4 := Float2 (1304036188433888837776239181861520996536501425378757873979482975053027049118504803287970903406469604875131101846237484155) (-399).
Definition i2 := makepairF f3 f4.
Notation p2 := (BND _Xn i2). (* BND(Xn, [0.99, 1.01]) *)
Definition s7 := (p1 /\ p2).
Definition f5 := Float2 (0) (0).
Definition i3 := makepairF f5 f5.
Notation p3 := (BND _En i3). (* BND(En, [0, 0]) *)
Definition s6 := (s7 /\ p3).
Definition f6 := Float2 (-1) (-127).
Definition f7 := Float2 (1) (-127).
Definition i4 := makepairF f6 f7.
Notation p4 := (BND _k i4). (* BND(k, [-5.87747e-39, 5.87747e-39]) *)
Definition s5 := (s6 /\ p4).
Definition i5 := makepairF f6 f5.
Notation p5 := (BND _ma i5). (* BND(ma, [-5.87747e-39, 0]) *)
Definition s4 := (s5 /\ p5).
Notation p6 := (BND _mb i5). (* BND(mb, [-5.87747e-39, 0]) *)
Definition s3 := (s4 /\ p6).
Definition f8 := Float2 (-1) (-126).
Definition f9 := Float2 (1) (-126).
Definition i6 := makepairF f8 f9.
Notation p7 := (BND _s i6). (* BND(s, [-1.17549e-38, 1.17549e-38]) *)
Definition s2 := (s3 /\ p7).
Definition f10 := Float2 (-259) (-134).
Definition f11 := Float2 (259) (-134).
Definition i7 := makepairF f10 f11.
Notation p8 := (BND r1 i7). (* BND(H - X, [-1.18927e-38, 1.18927e-38]) *)
Definition s8 := (not p8).
Definition s1 := (s2 /\ s8).
Lemma l2 : s1 -> s8.
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj2 h1).
Qed.
Definition f12 := Float2 (-645783161346167227676162949279293257742076497257318905851401988253282127303287945236274013749138933433269060778155183419) (-524).
Definition f13 := Float2 (645783161346167227676162949279293257742076497257318905851401988253282127303287945236274013749138933433269060778155183419) (-524).
Definition i8 := makepairF f12 f13.
Notation p9 := (BND r1 i8). (* BND(H - X, [-1.1759e-38, 1.1759e-38]) *)
Notation p10 := (BND r26 i8). (* BND(r / 12 * (En + Hn * ((1 + k) * (1 + ma) * (1 + mb) - 1)) + s, [-1.1759e-38, 1.1759e-38]) *)
Definition f14 := Float2 (-220691824440080262183156278540289159650049050013027643737149118120221799077646578862675429104475574293267784968310075) (-524).
Definition f15 := Float2 (220691824440080262183156278540289159650049050013027643737149118120221799077646578862675429104475574293267784968310075) (-524).
Definition i9 := makepairF f14 f15.
Notation p11 := (BND r27 i9). (* BND(r / 12 * (En + Hn * ((1 + k) * (1 + ma) * (1 + mb) - 1)), [-4.01854e-42, 4.01854e-42]) *)
Definition f16 := Float2 (-72835585623788865406982270145309953680312264018989285708779785475424641988512526946022434245957887707938943844456309) (-397).
Definition f17 := Float2 (72835585623788865406982270145309953680312264018989285708779785475424641988512526946022434245957887707938943844456309) (-397).
Definition i10 := makepairF f16 f17.
Notation p12 := (BND r25 i10). (* BND(r / 12, [-0.00022565, 0.00022565]) *)
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
Lemma l7 : s1 -> p1 (* BND(r, [-0.0027078, 0.0027078]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 exact (proj1 h1).
Qed.
Definition f18 := Float2 (3) (2).
Definition f19 := Float2 (1) (4).
Definition i11 := makepairF f18 f19.
Notation p13 := (BND r12 i11). (* BND(12, [12, 16]) *)
Lemma t1 : p13.
Proof.
 refine (constant1 _ i11 _) ; finalize.
Qed.
Lemma l14 : s1 -> p13 (* BND(12, [12, 16]) *).
Proof.
 intros h0.
 apply t1.
Qed.
Definition f20 := Float2 (-218506756871366596220946810435929861040936792056967857126339356426273925965537580838067302737873663123816831533368927) (-395).
Definition f21 := Float2 (218506756871366596220946810435929861040936792056967857126339356426273925965537580838067302737873663123816831533368927) (-395).
Definition i12 := makepairF f20 f21.
Notation p14 := (BND _r i12). (* BND(r, [-0.0027078, 0.0027078]) *)
Lemma t2 : p14 -> p13 -> p12.
Proof.
 intros h0 h1.
 refine (div_op _r r12 i12 i11 i10 h0 h1 _) ; finalize.
Qed.
Lemma l6 : s1 -> p12 (* BND(r / 12, [-0.00022565, 0.00022565]) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 assert (h2 := l14 h0).
 apply t2. refine (subset _r i1 i12 h1 _) ; finalize. exact h2.
Qed.
Definition f22 := Float2 (-955104630200602176105643932027481198629519279429857338076931910765695105968376854290190444204916587727761228708687381) (-514).
Definition i13 := makepairF f22 f9.
Notation p15 := (BND r28 i13). (* BND(En + Hn * ((1 + k) * (1 + ma) * (1 + mb) - 1), [-1.78087e-38, 1.17549e-38]) *)
Lemma l16 : s1 -> p3 (* BND(En, [0, 0]) *).
Proof.
 intros h0.
 assert (h1 := l9 h0).
 exact (proj2 h1).
Qed.
Notation p16 := (BND r29 i13). (* BND(Hn * ((1 + k) * (1 + ma) * (1 + mb) - 1), [-1.78087e-38, 1.17549e-38]) *)
Definition f23 := Float2 (1) (-1).
Definition f24 := Float2 (2546945680534939136281717152073283196360354346442886472616177685650443455309579693921818170715760947021740433293432587) (-390).
Definition i14 := makepairF f23 f24.
Notation p17 := (BND _Hn i14). (* BND(Hn, [0.5, 1.01]) *)
Lemma l19 : s1 -> p2 (* BND(Xn, [0.99, 1.01]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 exact (proj2 h1).
Qed.
Notation p18 := (BND _Xn i14). (* BND(Xn, [0.5, 1.01]) *)
Lemma t3 : p18 -> p3 -> p17.
Proof.
 intros h0 h1.
 refine (add _Xn _En i14 i3 i14 h0 h1 _) ; finalize.
Qed.
Lemma l18 : s1 -> p17 (* BND(Hn, [0.5, 1.01]) *).
Proof.
 intros h0.
 assert (h1 := l19 h0).
 assert (h2 := l16 h0).
 apply t3. refine (subset _Xn i2 i14 h1 _) ; finalize. exact h2.
Qed.
Definition f25 := Float2 (-86844066927987146567678238756515930889442064948849015334398126094787194912769) (-381).
Definition i15 := makepairF f25 f7.
Notation p19 := (BND r30 i15). (* BND((1 + k) * (1 + ma) * (1 + mb) - 1, [-1.76324e-38, 5.87747e-39]) *)
Definition f26 := Float2 (4925250774549309901534880012517951725548123341880193686925858436774199290547709261477934266526216329006041303875583) (-381).
Definition f27 := Float2 (170141183460469231731687303715884105729) (-127).
Definition i16 := makepairF f26 f27.
Notation p20 := (BND r31 i16). (* BND((1 + k) * (1 + ma) * (1 + mb), [1, 1]) *)
Definition f28 := Float2 (28948022309329048855892746252171976962977213799489202546401021394546514198529) (-254).
Definition i17 := makepairF f28 f27.
Notation p21 := (BND r32 i17). (* BND((1 + k) * (1 + ma), [1, 1]) *)
Definition f29 := Float2 (170141183460469231731687303715884105727) (-127).
Definition i18 := makepairF f29 f27.
Notation p22 := (BND r13 i18). (* BND(1 + k, [1, 1]) *)
Definition f30 := Float2 (1) (0).
Definition i19 := makepairF f30 f30.
Notation p23 := (BND r4 i19). (* BND(1, [1, 1]) *)
Lemma t4 : p23.
Proof.
 refine (constant1 _ i19 _) ; finalize.
Qed.
Lemma l24 : s1 -> p23 (* BND(1, [1, 1]) *).
Proof.
 intros h0.
 apply t4.
Qed.
Lemma l25 : s1 -> p4 (* BND(k, [-5.87747e-39, 5.87747e-39]) *).
Proof.
 intros h0.
 assert (h1 := l10 h0).
 exact (proj2 h1).
Qed.
Lemma t5 : p23 -> p4 -> p22.
Proof.
 intros h0 h1.
 refine (add r4 _k i19 i4 i18 h0 h1 _) ; finalize.
Qed.
Lemma l23 : s1 -> p22 (* BND(1 + k, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l24 h0).
 assert (h2 := l25 h0).
 apply t5. exact h1. exact h2.
Qed.
Definition i20 := makepairF f29 f30.
Notation p24 := (BND r15 i20). (* BND(1 + ma, [1, 1]) *)
Lemma l27 : s1 -> p5 (* BND(ma, [-5.87747e-39, 0]) *).
Proof.
 intros h0.
 assert (h1 := l11 h0).
 exact (proj2 h1).
Qed.
Lemma t6 : p23 -> p5 -> p24.
Proof.
 intros h0 h1.
 refine (add r4 _ma i19 i5 i20 h0 h1 _) ; finalize.
Qed.
Lemma l26 : s1 -> p24 (* BND(1 + ma, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l24 h0).
 assert (h2 := l27 h0).
 apply t6. exact h1. exact h2.
Qed.
Lemma t7 : p22 -> p24 -> p21.
Proof.
 intros h0 h1.
 refine (mul_pp r13 r15 i18 i20 i17 h0 h1 _) ; finalize.
Qed.
Lemma l22 : s1 -> p21 (* BND((1 + k) * (1 + ma), [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l23 h0).
 assert (h2 := l26 h0).
 apply t7. exact h1. exact h2.
Qed.
Notation p25 := (BND r20 i20). (* BND(1 + mb, [1, 1]) *)
Lemma l29 : s1 -> p6 (* BND(mb, [-5.87747e-39, 0]) *).
Proof.
 intros h0.
 assert (h1 := l12 h0).
 exact (proj2 h1).
Qed.
Lemma t8 : p23 -> p6 -> p25.
Proof.
 intros h0 h1.
 refine (add r4 _mb i19 i5 i20 h0 h1 _) ; finalize.
Qed.
Lemma l28 : s1 -> p25 (* BND(1 + mb, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l24 h0).
 assert (h2 := l29 h0).
 apply t8. exact h1. exact h2.
Qed.
Lemma t9 : p21 -> p25 -> p20.
Proof.
 intros h0 h1.
 refine (mul_pp r32 r20 i17 i20 i16 h0 h1 _) ; finalize.
Qed.
Lemma l21 : s1 -> p20 (* BND((1 + k) * (1 + ma) * (1 + mb), [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l22 h0).
 assert (h2 := l28 h0).
 apply t9. exact h1. exact h2.
Qed.
Lemma t10 : p20 -> p23 -> p19.
Proof.
 intros h0 h1.
 refine (sub r31 r4 i16 i19 i15 h0 h1 _) ; finalize.
Qed.
Lemma l20 : s1 -> p19 (* BND((1 + k) * (1 + ma) * (1 + mb) - 1, [-1.76324e-38, 5.87747e-39]) *).
Proof.
 intros h0.
 assert (h1 := l21 h0).
 assert (h2 := l24 h0).
 apply t10. exact h1. exact h2.
Qed.
Lemma t11 : p17 -> p19 -> p16.
Proof.
 intros h0 h1.
 refine (mul_po _Hn r30 i14 i15 i13 h0 h1 _) ; finalize.
Qed.
Lemma l17 : s1 -> p16 (* BND(Hn * ((1 + k) * (1 + ma) * (1 + mb) - 1), [-1.78087e-38, 1.17549e-38]) *).
Proof.
 intros h0.
 assert (h1 := l18 h0).
 assert (h2 := l20 h0).
 apply t11. exact h1. exact h2.
Qed.
Lemma t12 : p3 -> p16 -> p15.
Proof.
 intros h0 h1.
 refine (add _En r29 i3 i13 i13 h0 h1 _) ; finalize.
Qed.
Lemma l15 : s1 -> p15 (* BND(En + Hn * ((1 + k) * (1 + ma) * (1 + mb) - 1), [-1.78087e-38, 1.17549e-38]) *).
Proof.
 intros h0.
 assert (h1 := l16 h0).
 assert (h2 := l17 h0).
 apply t12. exact h1. exact h2.
Qed.
Lemma t13 : p12 -> p15 -> p11.
Proof.
 intros h0 h1.
 refine (mul_oo r25 r28 i10 i13 i9 h0 h1 _) ; finalize.
Qed.
Lemma l5 : s1 -> p11 (* BND(r / 12 * (En + Hn * ((1 + k) * (1 + ma) * (1 + mb) - 1)), [-4.01854e-42, 4.01854e-42]) *).
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
Lemma l4 : s1 -> p10 (* BND(r / 12 * (En + Hn * ((1 + k) * (1 + ma) * (1 + mb) - 1)) + s, [-1.1759e-38, 1.1759e-38]) *).
Proof.
 intros h0.
 assert (h1 := l5 h0).
 assert (h2 := l30 h0).
 apply t14. exact h1. exact h2.
Qed.
Notation p26 := (REL r1 r26 i3). (* REL(H - X, r / 12 * (En + Hn * ((1 + k) * (1 + ma) * (1 + mb) - 1)) + s, [0, 0]) *)
Notation p27 := (r1 = r26). (* EQL(H - X, r / 12 * (En + Hn * ((1 + k) * (1 + ma) * (1 + mb) - 1)) + s) *)
Lemma t15 : p27.
Proof.
 refine (b1) ; finalize.
Qed.
Lemma l32 : s1 -> p27 (* EQL(H - X, r / 12 * (En + Hn * ((1 + k) * (1 + ma) * (1 + mb) - 1)) + s) *).
Proof.
 intros h0.
 apply t15.
Qed.
Notation p28 := (REL r26 r26 i3). (* REL(r / 12 * (En + Hn * ((1 + k) * (1 + ma) * (1 + mb) - 1)) + s, r / 12 * (En + Hn * ((1 + k) * (1 + ma) * (1 + mb) - 1)) + s, [0, 0]) *)
Lemma t16 : p28.
Proof.
 refine (rel_refl r26 i3 _) ; finalize.
Qed.
Lemma l33 : s1 -> p28 (* REL(r / 12 * (En + Hn * ((1 + k) * (1 + ma) * (1 + mb) - 1)) + s, r / 12 * (En + Hn * ((1 + k) * (1 + ma) * (1 + mb) - 1)) + s, [0, 0]) *).
Proof.
 intros h0.
 apply t16.
Qed.
Lemma t17 : p27 -> p28 -> p26.
Proof.
 intros h0 h1.
 refine (rel_rewrite_1 r1 r26 r26 i3 h0 h1) ; finalize.
Qed.
Lemma l31 : s1 -> p26 (* REL(H - X, r / 12 * (En + Hn * ((1 + k) * (1 + ma) * (1 + mb) - 1)) + s, [0, 0]) *).
Proof.
 intros h0.
 assert (h1 := l32 h0).
 assert (h2 := l33 h0).
 apply t17. exact h1. exact h2.
Qed.
Lemma t18 : p10 -> p26 -> p9.
Proof.
 intros h0 h1.
 refine (bnd_of_bnd_rel_o r1 r26 i8 i3 i8 h0 h1 _) ; finalize.
Qed.
Lemma l3 : s1 -> p9 (* BND(H - X, [-1.1759e-38, 1.1759e-38]) *).
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
