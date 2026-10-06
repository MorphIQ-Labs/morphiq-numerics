Require Import Gappa.Gappa_library.
Section Generated_by_Gappa.
Notation r4 := (Float1 (1)).
Variable _r : R.
Notation r11 := ((r4 / r4)%R).
Variable _k : R.
Notation r12 := ((r4 + _k)%R).
Notation r10 := ((r11 * r12)%R).
Notation r8 := ((_r * r10)%R).
Variable _ma : R.
Notation r14 := ((r4 + _ma)%R).
Notation r7 := ((r8 * r14)%R).
Variable _Xn : R.
Variable _En : R.
Notation _Hn := ((_Xn + _En)%R).
Notation r6 := ((r7 * _Hn)%R).
Variable _mb : R.
Notation r19 := ((r4 + _mb)%R).
Notation _b := ((r6 * r19)%R).
Notation r3 := ((r4 + _b)%R).
Variable _s : R.
Notation _H := ((r3 + _s)%R).
Notation r24 := ((_r / r4)%R).
Notation r23 := ((r24 * _Xn)%R).
Notation _X := ((r4 + r23)%R).
Notation r1 := ((_H - _X)%R).
Notation r31 := ((r12 * r14)%R).
Notation r30 := ((r31 * r19)%R).
Notation r29 := ((r30 - r4)%R).
Notation r28 := ((_Hn * r29)%R).
Notation r27 := ((_En + r28)%R).
Notation r26 := ((r24 * r27)%R).
Notation r25 := ((r26 + _s)%R).
Hypothesis a1 : r1 = r25.
Lemma b1 : r1 = r25.
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
Definition f5 := Float2 (-519) (-135).
Definition f6 := Float2 (519) (-135).
Definition i3 := makepairF f5 f6.
Notation p3 := (BND _En i3). (* BND(En, [-1.19157e-38, 1.19157e-38]) *)
Definition s6 := (s7 /\ p3).
Definition f7 := Float2 (-1) (-127).
Definition f8 := Float2 (1) (-127).
Definition i4 := makepairF f7 f8.
Notation p4 := (BND _k i4). (* BND(k, [-5.87747e-39, 5.87747e-39]) *)
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
Definition f12 := Float2 (-521) (-135).
Definition f13 := Float2 (521) (-135).
Definition i7 := makepairF f12 f13.
Notation p8 := (BND r1 i7). (* BND(H - X, [-1.19616e-38, 1.19616e-38]) *)
Definition s8 := (not p8).
Definition s1 := (s2 /\ s8).
Lemma l2 : s1 -> s8.
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj2 h1).
Qed.
Definition f14 := Float2 (-324991362323255924525703454442057653607568563710376246386501927302811943013183010092723531702352866500682461588871728703) (-523).
Definition f15 := Float2 (324991362323255924525703454442057653607568563710376246386501927302811943013183010092723531702352866500682461588871728703) (-523).
Definition i8 := makepairF f14 f15.
Notation p9 := (BND r1 i8). (* BND(H - X, [-1.18354e-38, 1.18354e-38]) *)
Notation p10 := (BND r25 i8). (* BND(r / 1 * (En + Hn * ((1 + k) * (1 + ma) * (1 + mb) - 1)) + s, [-1.18354e-38, 1.18354e-38]) *)
Definition f16 := Float2 (-2210127562392350818713557941681169316355339606723307282669507735230990261077860764017862542335637571194565092278292031) (-523).
Definition f17 := Float2 (2210127562392350818713557941681169316355339606723307282669507735230990261077860764017862542335637571194565092278292031) (-523).
Definition i9 := makepairF f16 f17.
Notation p11 := (BND r26 i9). (* BND(r / 1 * (En + Hn * ((1 + k) * (1 + ma) * (1 + mb) - 1)), [-8.04877e-41, 8.04877e-41]) *)
Definition f18 := Float2 (-6992216219883731079070297933949755553309977345822971428042859405640765630897202586818153687611957219962138609067805663) (-400).
Definition f19 := Float2 (6992216219883731079070297933949755553309977345822971428042859405640765630897202586818153687611957219962138609067805663) (-400).
Definition i10 := makepairF f18 f19.
Notation p12 := (BND r24 i10). (* BND(r / 1, [-0.0027078, 0.0027078]) *)
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
Definition f20 := Float2 (1) (0).
Definition i11 := makepairF f20 f20.
Notation p13 := (BND r4 i11). (* BND(1, [1, 1]) *)
Lemma t1 : p13.
Proof.
 refine (constant1 _ i11 _) ; finalize.
Qed.
Lemma l14 : s1 -> p13 (* BND(1, [1, 1]) *).
Proof.
 intros h0.
 apply t1.
Qed.
Notation p14 := (BND _r i10). (* BND(r, [-0.0027078, 0.0027078]) *)
Lemma t2 : p14 -> p13 -> p12.
Proof.
 intros h0 h1.
 refine (div_op _r r4 i10 i11 i10 h0 h1 _) ; finalize.
Qed.
Lemma l6 : s1 -> p12 (* BND(r / 1, [-0.0027078, 0.0027078]) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 assert (h2 := l14 h0).
 apply t2. refine (subset _r i1 i10 h1 _) ; finalize. exact h2.
Qed.
Definition f21 := Float2 (-6376623672793500543319178454606741740167697273626500533959498183577853391931009387284714939063877880551569459865631321) (-516).
Definition f22 := Float2 (1) (-125).
Definition i12 := makepairF f21 f22.
Notation p15 := (BND r27 i12). (* BND(En + Hn * ((1 + k) * (1 + ma) * (1 + mb) - 1), [-2.97244e-38, 2.35099e-38]) *)
Lemma l16 : s1 -> p3 (* BND(En, [-1.19157e-38, 1.19157e-38]) *).
Proof.
 intros h0.
 assert (h1 := l9 h0).
 exact (proj2 h1).
Qed.
Definition f23 := Float2 (-3820418520802408704422575728109924794563149188455054681376352648977412192005127848869214415778218978354239468994476633) (-516).
Definition f24 := Float2 (3) (-128).
Definition i13 := makepairF f23 f24.
Notation p16 := (BND r28 i13). (* BND(Hn * ((1 + k) * (1 + ma) * (1 + mb) - 1), [-1.78087e-38, 8.81621e-39]) *)
Definition f25 := Float2 (1) (-1).
Definition f26 := Float2 (10187782722139756545126868608293132785561609574399880101314377425040791869590013019770207588336000760287175561739983913) (-392).
Definition i14 := makepairF f25 f26.
Notation p17 := (BND _Hn i14). (* BND(Hn, [0.5, 1.01]) *)
Lemma l19 : s1 -> p2 (* BND(Xn, [0.99, 1.01]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 exact (proj2 h1).
Qed.
Definition f27 := Float2 (3) (-2).
Definition f28 := Float2 (10187782722139756545126868608293132785441417385771545890464710742601773821238318775687272682863043788086961733173730345) (-392).
Definition i15 := makepairF f27 f28.
Notation p18 := (BND _Xn i15). (* BND(Xn, [0.75, 1.01]) *)
Definition f29 := Float2 (-1) (-2).
Definition i16 := makepairF f29 f6.
Notation p19 := (BND _En i16). (* BND(En, [-0.25, 1.19157e-38]) *)
Lemma t3 : p18 -> p19 -> p17.
Proof.
 intros h0 h1.
 refine (add _Xn _En i15 i16 i14 h0 h1 _) ; finalize.
Qed.
Lemma l18 : s1 -> p17 (* BND(Hn, [0.5, 1.01]) *).
Proof.
 intros h0.
 assert (h1 := l19 h0).
 assert (h2 := l16 h0).
 apply t3. refine (subset _Xn i2 i15 h1 _) ; finalize. refine (subset _En i3 i16 h2 _) ; finalize.
Qed.
Definition f30 := Float2 (-86844066927987146567678238756515930889442064948849015334398126094787194912769) (-381).
Definition i17 := makepairF f30 f8.
Notation p20 := (BND r29 i17). (* BND((1 + k) * (1 + ma) * (1 + mb) - 1, [-1.76324e-38, 5.87747e-39]) *)
Definition f31 := Float2 (4925250774549309901534880012517951725548123341880193686925858436774199290547709261477934266526216329006041303875583) (-381).
Definition f32 := Float2 (170141183460469231731687303715884105729) (-127).
Definition i18 := makepairF f31 f32.
Notation p21 := (BND r30 i18). (* BND((1 + k) * (1 + ma) * (1 + mb), [1, 1]) *)
Definition f33 := Float2 (28948022309329048855892746252171976962977213799489202546401021394546514198529) (-254).
Definition i19 := makepairF f33 f32.
Notation p22 := (BND r31 i19). (* BND((1 + k) * (1 + ma), [1, 1]) *)
Definition f34 := Float2 (170141183460469231731687303715884105727) (-127).
Definition i20 := makepairF f34 f32.
Notation p23 := (BND r12 i20). (* BND(1 + k, [1, 1]) *)
Lemma l24 : s1 -> p4 (* BND(k, [-5.87747e-39, 5.87747e-39]) *).
Proof.
 intros h0.
 assert (h1 := l10 h0).
 exact (proj2 h1).
Qed.
Lemma t4 : p13 -> p4 -> p23.
Proof.
 intros h0 h1.
 refine (add r4 _k i11 i4 i20 h0 h1 _) ; finalize.
Qed.
Lemma l23 : s1 -> p23 (* BND(1 + k, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l14 h0).
 assert (h2 := l24 h0).
 apply t4. exact h1. exact h2.
Qed.
Definition i21 := makepairF f34 f20.
Notation p24 := (BND r14 i21). (* BND(1 + ma, [1, 1]) *)
Lemma l26 : s1 -> p5 (* BND(ma, [-5.87747e-39, 0]) *).
Proof.
 intros h0.
 assert (h1 := l11 h0).
 exact (proj2 h1).
Qed.
Lemma t5 : p13 -> p5 -> p24.
Proof.
 intros h0 h1.
 refine (add r4 _ma i11 i5 i21 h0 h1 _) ; finalize.
Qed.
Lemma l25 : s1 -> p24 (* BND(1 + ma, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l14 h0).
 assert (h2 := l26 h0).
 apply t5. exact h1. exact h2.
Qed.
Lemma t6 : p23 -> p24 -> p22.
Proof.
 intros h0 h1.
 refine (mul_pp r12 r14 i20 i21 i19 h0 h1 _) ; finalize.
Qed.
Lemma l22 : s1 -> p22 (* BND((1 + k) * (1 + ma), [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l23 h0).
 assert (h2 := l25 h0).
 apply t6. exact h1. exact h2.
Qed.
Notation p25 := (BND r19 i21). (* BND(1 + mb, [1, 1]) *)
Lemma l28 : s1 -> p6 (* BND(mb, [-5.87747e-39, 0]) *).
Proof.
 intros h0.
 assert (h1 := l12 h0).
 exact (proj2 h1).
Qed.
Lemma t7 : p13 -> p6 -> p25.
Proof.
 intros h0 h1.
 refine (add r4 _mb i11 i5 i21 h0 h1 _) ; finalize.
Qed.
Lemma l27 : s1 -> p25 (* BND(1 + mb, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l14 h0).
 assert (h2 := l28 h0).
 apply t7. exact h1. exact h2.
Qed.
Lemma t8 : p22 -> p25 -> p21.
Proof.
 intros h0 h1.
 refine (mul_pp r31 r19 i19 i21 i18 h0 h1 _) ; finalize.
Qed.
Lemma l21 : s1 -> p21 (* BND((1 + k) * (1 + ma) * (1 + mb), [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l22 h0).
 assert (h2 := l27 h0).
 apply t8. exact h1. exact h2.
Qed.
Lemma t9 : p21 -> p13 -> p20.
Proof.
 intros h0 h1.
 refine (sub r30 r4 i18 i11 i17 h0 h1 _) ; finalize.
Qed.
Lemma l20 : s1 -> p20 (* BND((1 + k) * (1 + ma) * (1 + mb) - 1, [-1.76324e-38, 5.87747e-39]) *).
Proof.
 intros h0.
 assert (h1 := l21 h0).
 assert (h2 := l14 h0).
 apply t9. exact h1. exact h2.
Qed.
Lemma t10 : p17 -> p20 -> p16.
Proof.
 intros h0 h1.
 refine (mul_po _Hn r29 i14 i17 i13 h0 h1 _) ; finalize.
Qed.
Lemma l17 : s1 -> p16 (* BND(Hn * ((1 + k) * (1 + ma) * (1 + mb) - 1), [-1.78087e-38, 8.81621e-39]) *).
Proof.
 intros h0.
 assert (h1 := l18 h0).
 assert (h2 := l20 h0).
 apply t10. exact h1. exact h2.
Qed.
Definition f35 := Float2 (5) (-128).
Definition i22 := makepairF f5 f35.
Notation p26 := (BND _En i22). (* BND(En, [-1.19157e-38, 1.46937e-38]) *)
Lemma t11 : p26 -> p16 -> p15.
Proof.
 intros h0 h1.
 refine (add _En r28 i22 i13 i12 h0 h1 _) ; finalize.
Qed.
Lemma l15 : s1 -> p15 (* BND(En + Hn * ((1 + k) * (1 + ma) * (1 + mb) - 1), [-2.97244e-38, 2.35099e-38]) *).
Proof.
 intros h0.
 assert (h1 := l16 h0).
 assert (h2 := l17 h0).
 apply t11. refine (subset _En i3 i22 h1 _) ; finalize. exact h2.
Qed.
Lemma t12 : p12 -> p15 -> p11.
Proof.
 intros h0 h1.
 refine (mul_oo r24 r27 i10 i12 i9 h0 h1 _) ; finalize.
Qed.
Lemma l5 : s1 -> p11 (* BND(r / 1 * (En + Hn * ((1 + k) * (1 + ma) * (1 + mb) - 1)), [-8.04877e-41, 8.04877e-41]) *).
Proof.
 intros h0.
 assert (h1 := l6 h0).
 assert (h2 := l15 h0).
 apply t12. exact h1. exact h2.
Qed.
Lemma l29 : s1 -> p7 (* BND(s, [-1.17549e-38, 1.17549e-38]) *).
Proof.
 intros h0.
 assert (h1 := l13 h0).
 exact (proj2 h1).
Qed.
Lemma t13 : p11 -> p7 -> p10.
Proof.
 intros h0 h1.
 refine (add r26 _s i9 i6 i8 h0 h1 _) ; finalize.
Qed.
Lemma l4 : s1 -> p10 (* BND(r / 1 * (En + Hn * ((1 + k) * (1 + ma) * (1 + mb) - 1)) + s, [-1.18354e-38, 1.18354e-38]) *).
Proof.
 intros h0.
 assert (h1 := l5 h0).
 assert (h2 := l29 h0).
 apply t13. exact h1. exact h2.
Qed.
Definition i23 := makepairF f9 f9.
Notation p27 := (REL r1 r25 i23). (* REL(H - X, r / 1 * (En + Hn * ((1 + k) * (1 + ma) * (1 + mb) - 1)) + s, [0, 0]) *)
Notation p28 := (r1 = r25). (* EQL(H - X, r / 1 * (En + Hn * ((1 + k) * (1 + ma) * (1 + mb) - 1)) + s) *)
Lemma t14 : p28.
Proof.
 refine (b1) ; finalize.
Qed.
Lemma l31 : s1 -> p28 (* EQL(H - X, r / 1 * (En + Hn * ((1 + k) * (1 + ma) * (1 + mb) - 1)) + s) *).
Proof.
 intros h0.
 apply t14.
Qed.
Notation p29 := (REL r25 r25 i23). (* REL(r / 1 * (En + Hn * ((1 + k) * (1 + ma) * (1 + mb) - 1)) + s, r / 1 * (En + Hn * ((1 + k) * (1 + ma) * (1 + mb) - 1)) + s, [0, 0]) *)
Lemma t15 : p29.
Proof.
 refine (rel_refl r25 i23 _) ; finalize.
Qed.
Lemma l32 : s1 -> p29 (* REL(r / 1 * (En + Hn * ((1 + k) * (1 + ma) * (1 + mb) - 1)) + s, r / 1 * (En + Hn * ((1 + k) * (1 + ma) * (1 + mb) - 1)) + s, [0, 0]) *).
Proof.
 intros h0.
 apply t15.
Qed.
Lemma t16 : p28 -> p29 -> p27.
Proof.
 intros h0 h1.
 refine (rel_rewrite_1 r1 r25 r25 i23 h0 h1) ; finalize.
Qed.
Lemma l30 : s1 -> p27 (* REL(H - X, r / 1 * (En + Hn * ((1 + k) * (1 + ma) * (1 + mb) - 1)) + s, [0, 0]) *).
Proof.
 intros h0.
 assert (h1 := l31 h0).
 assert (h2 := l32 h0).
 apply t16. exact h1. exact h2.
Qed.
Lemma t17 : p10 -> p27 -> p9.
Proof.
 intros h0 h1.
 refine (bnd_of_bnd_rel_o r1 r25 i8 i23 i8 h0 h1 _) ; finalize.
Qed.
Lemma l3 : s1 -> p9 (* BND(H - X, [-1.18354e-38, 1.18354e-38]) *).
Proof.
 intros h0.
 assert (h1 := l4 h0).
 assert (h2 := l30 h0).
 apply t17. exact h1. exact h2.
Qed.
Lemma l1 : s1 -> False.
Proof.
 intros h0.
 assert (h1 := l2 h0).
 assert (h2 := l3 h0).
 refine (simplify (Tatom false (Abnd 0%nat i7)) Tfalse (Abnd 0%nat i8) (List.cons r1 List.nil) h2 h1 _) ; finalize.
Qed.
End Generated_by_Gappa.
