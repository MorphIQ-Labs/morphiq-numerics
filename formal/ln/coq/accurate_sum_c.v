Require Import Gappa.Gappa_library.
Section Generated_by_Gappa.
Variable _X1 : R.
Notation r12 := (Float1 (1)).
Variable _k2 : R.
Notation r11 := ((r12 - _k2)%R).
Variable _k3 : R.
Notation _k1 := ((r11 - _k3)%R).
Variable _eL : R.
Notation r15 := ((r12 + _eL)%R).
Notation r9 := ((_k1 * r15)%R).
Variable _mL : R.
Notation r17 := ((r12 + _mL)%R).
Notation r8 := ((r9 * r17)%R).
Variable _eN : R.
Notation r20 := ((r12 + _eN)%R).
Notation r19 := ((_k2 * r20)%R).
Notation r7 := ((r8 + r19)%R).
Variable _s1 : R.
Notation r6 := ((r7 + _s1)%R).
Variable _E1 : R.
Notation _q := ((_E1 / _X1)%R).
Notation r25 := ((r12 + _q)%R).
Notation r24 := ((_k3 * r25)%R).
Variable _mz : R.
Notation r28 := ((r12 + _mz)%R).
Notation r23 := ((r24 * r28)%R).
Notation r5 := ((r6 + r23)%R).
Variable _dz : R.
Notation r4 := ((r5 + _dz)%R).
Variable _s2 : R.
Notation _Y := ((r4 + _s2)%R).
Notation r2 := ((_Y - r12)%R).
Notation r39 := ((r15 * r17)%R).
Notation r38 := ((r39 - r12)%R).
Notation r37 := ((_k1 * r38)%R).
Notation r40 := ((_k2 * _eN)%R).
Notation r36 := ((r37 + r40)%R).
Notation r43 := ((r25 * _mz)%R).
Notation r42 := ((_q + r43)%R).
Notation r41 := ((_k3 * r42)%R).
Notation r35 := ((r36 + r41)%R).
Notation r34 := ((r35 + _dz)%R).
Notation r33 := ((r34 + _s1)%R).
Notation r32 := ((r33 + _s2)%R).
Hypothesis a1 : (_X1 <> 0)%R -> r2 = r32.
Lemma b1 : NZR _X1 -> r2 = r32.
 intros h0.
 apply a1.
 exact h0.
Qed.
Definition f1 := Float2 (-257) (-8).
Definition f2 := Float2 (257) (-8).
Definition i1 := makepairF f1 f2.
Notation p1 := (BND _k2 i1). (* BND(k2, [-1.00391, 1.00391]) *)
Definition f3 := Float2 (-47) (-12).
Definition f4 := Float2 (47) (-12).
Definition i2 := makepairF f3 f4.
Notation p2 := (BND _k3 i2). (* BND(k3, [-0.0114746, 0.0114746]) *)
Definition s11 := (p1 /\ p2).
Definition f5 := Float2 (-409) (-134).
Definition f6 := Float2 (409) (-134).
Definition i3 := makepairF f5 f6.
Notation p3 := (BND _E1 i3). (* BND(E1, [-1.87804e-38, 1.87804e-38]) *)
Definition s10 := (s11 /\ p3).
Definition f7 := Float2 (2569643334182088301921218974605293170359228169148631243641020077562016180326154975917463424665424198542833092687176540113) (-400).
Definition f8 := Float2 (1297491476117877567955756254720079362941012786046832206986213668913874777720503119280182067258581095541356805256872555633) (-399).
Definition i4 := makepairF f7 f8.
Notation p4 := (BND _X1 i4). (* BND(X1, [0.995118, 1.00493]) *)
Definition s9 := (s10 /\ p4).
Definition f9 := Float2 (-1) (-127).
Definition f10 := Float2 (0) (0).
Definition i5 := makepairF f9 f10.
Notation p5 := (BND _mz i5). (* BND(mz, [-5.87747e-39, 0]) *)
Definition s8 := (s9 /\ p5).
Definition f11 := Float2 (1) (-127).
Definition i6 := makepairF f9 f11.
Notation p6 := (BND _eN i6). (* BND(eN, [-5.87747e-39, 5.87747e-39]) *)
Definition s7 := (s8 /\ p6).
Notation p7 := (BND _eL i6). (* BND(eL, [-5.87747e-39, 5.87747e-39]) *)
Definition s6 := (s7 /\ p7).
Notation p8 := (BND _mL i5). (* BND(mL, [-5.87747e-39, 0]) *)
Definition s5 := (s6 /\ p8).
Definition f12 := Float2 (-259) (-133).
Definition f13 := Float2 (259) (-133).
Definition i7 := makepairF f12 f13.
Notation p9 := (BND _s1 i7). (* BND(s1, [-2.37854e-38, 2.37854e-38]) *)
Definition s4 := (s5 /\ p9).
Definition f14 := Float2 (-523) (-135).
Definition f15 := Float2 (523) (-135).
Definition i8 := makepairF f14 f15.
Notation p10 := (BND _s2 i8). (* BND(s2, [-1.20075e-38, 1.20075e-38]) *)
Definition s3 := (s4 /\ p10).
Definition f16 := Float2 (-131) (-133).
Definition f17 := Float2 (131) (-133).
Definition i9 := makepairF f16 f17.
Notation p11 := (BND _dz i9). (* BND(dz, [-1.20304e-38, 1.20304e-38]) *)
Definition s2 := (s3 /\ p11).
Definition f18 := Float2 (-1) (-123).
Definition f19 := Float2 (1) (-123).
Definition i10 := makepairF f18 f19.
Notation p12 := (BND r2 i10). (* BND(Y - 1, [-9.40395e-38, 9.40395e-38]) *)
Definition s12 := (not p12).
Definition s1 := (s2 /\ s12).
Lemma l2 : s1 -> s12.
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj2 h1).
Qed.
Definition f20 := Float2 (-1066768269972204275858754682835500361434801126668590607938986470030146012372480159017094875374451809441865397102214808461) (-522).
Definition f21 := Float2 (904136489396586062910072944822157595455290366526398522010251467485368514439954165941897354263560042490421362957401097101) (-522).
Definition i11 := makepairF f20 f21.
Notation p13 := (BND r2 i11). (* BND(Y - 1, [-7.76984e-38, 6.58531e-38]) *)
Notation p14 := (BND r32 i11). (* BND(k1 * ((1 + eL) * (1 + mL) - 1) + k2 * eN + k3 * (q + (1 + q) * mz) + dz + s1 + s2, [-7.76984e-38, 6.58531e-38]) *)
Definition f22 := Float2 (-901910276046489774834579179056499481274347497560963179080290810426781912480535829818937585364013322400730465590771090317) (-522).
Definition f23 := Float2 (739278495470871561885897441043156715294836737418771093151555807882004414548009836743740064253121555449286431445957378957) (-522).
Definition i12 := makepairF f22 f23.
Notation p15 := (BND r33 i12). (* BND(k1 * ((1 + eL) * (1 + mL) - 1) + k2 * eN + k3 * (q + (1 + q) * mz) + dz + s1, [-6.5691e-38, 5.38456e-38]) *)
Definition f24 := Float2 (-575346448690772331123210494706509210057846618487345557096335354692393370438366948271536146643527141569725132807108199309) (-522).
Definition f25 := Float2 (412714668115154118174528756693166444078335858345153471167600352147615872505840955196338625532635374618281098662294487949) (-522).
Definition i13 := makepairF f24 f25.
Notation p16 := (BND r34 i13). (* BND(k1 * ((1 + eL) * (1 + mL) - 1) + k2 * eN + k3 * (q + (1 + q) * mz) + dz, [-4.19056e-38, 3.00602e-38]) *)
Definition f26 := Float2 (-410173238715486674265336758606707180986952351465554404664296108741795304772250641388487542503049575203463748271742026637) (-522).
Definition f27 := Float2 (247541458139868461316655020593364415007441591323362318735561106197017806839724648313290021392157808252019714126928315277) (-522).
Definition i14 := makepairF f26 f27.
Notation p17 := (BND r35 i14). (* BND(k1 * ((1 + eL) * (1 + mL) - 1) + k2 * eN + k3 * (q + (1 + q) * mz), [-2.98751e-38, 1.80298e-38]) *)
Definition f28 := Float2 (-3508651485321796496770855577228962028314561) (-266).
Definition f29 := Float2 (12367) (-139).
Definition i15 := makepairF f28 f29.
Notation p18 := (BND r36 i15). (* BND(k1 * ((1 + eL) * (1 + mL) - 1) + k2 * eN, [-2.95911e-38, 1.77458e-38]) *)
Definition f30 := Float2 (-2809030938932347015890157384349246585561025) (-266).
Definition f31 := Float2 (8255) (-139).
Definition i16 := makepairF f30 f31.
Notation p19 := (BND r37 i16). (* BND(k1 * ((1 + eL) * (1 + mL) - 1), [-2.36907e-38, 1.18453e-38]) *)
Definition f32 := Float2 (-1) (0).
Definition f33 := Float2 (8255) (-12).
Definition i17 := makepairF f32 f33.
Notation p20 := (BND _k1 i17). (* BND(k1, [-1, 2.01538]) *)
Definition f34 := Float2 (-1) (-1).
Definition f35 := Float2 (513) (-8).
Definition i18 := makepairF f34 f35.
Notation p21 := (BND r11 i18). (* BND(1 - k2, [-0.5, 2.00391]) *)
Definition f36 := Float2 (1) (0).
Definition i19 := makepairF f36 f36.
Notation p22 := (BND r12 i19). (* BND(1, [1, 1]) *)
Lemma t1 : p22.
Proof.
 refine (constant1 _ i19 _) ; finalize.
Qed.
Lemma l12 : s1 -> p22 (* BND(1, [1, 1]) *).
Proof.
 intros h0.
 apply t1.
Qed.
Lemma l23 : s1 -> s2.
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj1 h1).
Qed.
Lemma l22 : s1 -> s3.
Proof.
 intros h0.
 assert (h1 := l23 h0).
 exact (proj1 h1).
Qed.
Lemma l21 : s1 -> s4.
Proof.
 intros h0.
 assert (h1 := l22 h0).
 exact (proj1 h1).
Qed.
Lemma l20 : s1 -> s5.
Proof.
 intros h0.
 assert (h1 := l21 h0).
 exact (proj1 h1).
Qed.
Lemma l19 : s1 -> s6.
Proof.
 intros h0.
 assert (h1 := l20 h0).
 exact (proj1 h1).
Qed.
Lemma l18 : s1 -> s7.
Proof.
 intros h0.
 assert (h1 := l19 h0).
 exact (proj1 h1).
Qed.
Lemma l17 : s1 -> s8.
Proof.
 intros h0.
 assert (h1 := l18 h0).
 exact (proj1 h1).
Qed.
Lemma l16 : s1 -> s9.
Proof.
 intros h0.
 assert (h1 := l17 h0).
 exact (proj1 h1).
Qed.
Lemma l15 : s1 -> s10.
Proof.
 intros h0.
 assert (h1 := l16 h0).
 exact (proj1 h1).
Qed.
Lemma l14 : s1 -> s11.
Proof.
 intros h0.
 assert (h1 := l15 h0).
 exact (proj1 h1).
Qed.
Lemma l13 : s1 -> p1 (* BND(k2, [-1.00391, 1.00391]) *).
Proof.
 intros h0.
 assert (h1 := l14 h0).
 exact (proj1 h1).
Qed.
Definition f37 := Float2 (3) (-1).
Definition i20 := makepairF f1 f37.
Notation p23 := (BND _k2 i20). (* BND(k2, [-1.00391, 1.5]) *)
Lemma t2 : p22 -> p23 -> p21.
Proof.
 intros h0 h1.
 refine (sub r12 _k2 i19 i20 i18 h0 h1 _) ; finalize.
Qed.
Lemma l11 : s1 -> p21 (* BND(1 - k2, [-0.5, 2.00391]) *).
Proof.
 intros h0.
 assert (h1 := l12 h0).
 assert (h2 := l13 h0).
 apply t2. exact h1. refine (subset _k2 i1 i20 h2 _) ; finalize.
Qed.
Lemma l24 : s1 -> p2 (* BND(k3, [-0.0114746, 0.0114746]) *).
Proof.
 intros h0.
 assert (h1 := l14 h0).
 exact (proj2 h1).
Qed.
Definition f38 := Float2 (1) (-1).
Definition i21 := makepairF f3 f38.
Notation p24 := (BND _k3 i21). (* BND(k3, [-0.0114746, 0.5]) *)
Lemma t3 : p21 -> p24 -> p20.
Proof.
 intros h0 h1.
 refine (sub r11 _k3 i18 i21 i17 h0 h1 _) ; finalize.
Qed.
Lemma l10 : s1 -> p20 (* BND(k1, [-1, 2.01538]) *).
Proof.
 intros h0.
 assert (h1 := l11 h0).
 assert (h2 := l24 h0).
 apply t3. exact h1. refine (subset _k3 i2 i21 h2 _) ; finalize.
Qed.
Definition f39 := Float2 (-340282366920938463463374607431768211455) (-254).
Definition i22 := makepairF f39 f11.
Notation p25 := (BND r38 i22). (* BND((1 + eL) * (1 + mL) - 1, [-1.17549e-38, 5.87747e-39]) *)
Definition f40 := Float2 (28948022309329048855892746252171976962977213799489202546401021394546514198529) (-254).
Definition f41 := Float2 (170141183460469231731687303715884105729) (-127).
Definition i23 := makepairF f40 f41.
Notation p26 := (BND r39 i23). (* BND((1 + eL) * (1 + mL), [1, 1]) *)
Definition f42 := Float2 (170141183460469231731687303715884105727) (-127).
Definition i24 := makepairF f42 f41.
Notation p27 := (BND r15 i24). (* BND(1 + eL, [1, 1]) *)
Lemma l28 : s1 -> p7 (* BND(eL, [-5.87747e-39, 5.87747e-39]) *).
Proof.
 intros h0.
 assert (h1 := l19 h0).
 exact (proj2 h1).
Qed.
Lemma t4 : p22 -> p7 -> p27.
Proof.
 intros h0 h1.
 refine (add r12 _eL i19 i6 i24 h0 h1 _) ; finalize.
Qed.
Lemma l27 : s1 -> p27 (* BND(1 + eL, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l12 h0).
 assert (h2 := l28 h0).
 apply t4. exact h1. exact h2.
Qed.
Definition i25 := makepairF f42 f36.
Notation p28 := (BND r17 i25). (* BND(1 + mL, [1, 1]) *)
Lemma l30 : s1 -> p8 (* BND(mL, [-5.87747e-39, 0]) *).
Proof.
 intros h0.
 assert (h1 := l20 h0).
 exact (proj2 h1).
Qed.
Lemma t5 : p22 -> p8 -> p28.
Proof.
 intros h0 h1.
 refine (add r12 _mL i19 i5 i25 h0 h1 _) ; finalize.
Qed.
Lemma l29 : s1 -> p28 (* BND(1 + mL, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l12 h0).
 assert (h2 := l30 h0).
 apply t5. exact h1. exact h2.
Qed.
Lemma t6 : p27 -> p28 -> p26.
Proof.
 intros h0 h1.
 refine (mul_pp r15 r17 i24 i25 i23 h0 h1 _) ; finalize.
Qed.
Lemma l26 : s1 -> p26 (* BND((1 + eL) * (1 + mL), [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l27 h0).
 assert (h2 := l29 h0).
 apply t6. exact h1. exact h2.
Qed.
Lemma t7 : p26 -> p22 -> p25.
Proof.
 intros h0 h1.
 refine (sub r39 r12 i23 i19 i22 h0 h1 _) ; finalize.
Qed.
Lemma l25 : s1 -> p25 (* BND((1 + eL) * (1 + mL) - 1, [-1.17549e-38, 5.87747e-39]) *).
Proof.
 intros h0.
 assert (h1 := l26 h0).
 assert (h2 := l12 h0).
 apply t7. exact h1. exact h2.
Qed.
Lemma t8 : p20 -> p25 -> p19.
Proof.
 intros h0 h1.
 refine (mul_oo _k1 r38 i17 i22 i16 h0 h1 _) ; finalize.
Qed.
Lemma l9 : s1 -> p19 (* BND(k1 * ((1 + eL) * (1 + mL) - 1), [-2.36907e-38, 1.18453e-38]) *).
Proof.
 intros h0.
 assert (h1 := l10 h0).
 assert (h2 := l25 h0).
 apply t8. exact h1. exact h2.
Qed.
Definition f43 := Float2 (-257) (-135).
Definition f44 := Float2 (257) (-135).
Definition i26 := makepairF f43 f44.
Notation p29 := (BND r40 i26). (* BND(k2 * eN, [-5.90043e-39, 5.90043e-39]) *)
Lemma l32 : s1 -> p6 (* BND(eN, [-5.87747e-39, 5.87747e-39]) *).
Proof.
 intros h0.
 assert (h1 := l18 h0).
 exact (proj2 h1).
Qed.
Lemma t9 : p1 -> p6 -> p29.
Proof.
 intros h0 h1.
 refine (mul_oo _k2 _eN i1 i6 i26 h0 h1 _) ; finalize.
Qed.
Lemma l31 : s1 -> p29 (* BND(k2 * eN, [-5.90043e-39, 5.90043e-39]) *).
Proof.
 intros h0.
 assert (h1 := l13 h0).
 assert (h2 := l32 h0).
 apply t9. exact h1. exact h2.
Qed.
Lemma t10 : p19 -> p29 -> p18.
Proof.
 intros h0 h1.
 refine (add r37 r40 i16 i26 i15 h0 h1 _) ; finalize.
Qed.
Lemma l8 : s1 -> p18 (* BND(k1 * ((1 + eL) * (1 + mL) - 1) + k2 * eN, [-2.95911e-38, 1.77458e-38]) *).
Proof.
 intros h0.
 assert (h1 := l9 h0).
 assert (h2 := l31 h0).
 apply t10. exact h1. exact h2.
Qed.
Definition f45 := Float2 (-3899152824463199107527576134126379043731023544439229264302833931864386265671646497609906005076932387091929948866118541) (-522).
Definition f46 := Float2 (3899152824463199107527576134126379043731023544439229264302833931864386265671646497609906005076932387091929948866118541) (-522).
Definition i27 := makepairF f45 f46.
Notation p30 := (BND r41 i27). (* BND(k3 * (q + (1 + q) * mz), [-2.83996e-40, 2.83996e-40]) *)
Definition f47 := Float2 (-10618969394282755016245313726982479097820659865706837145335377516566839191616398972214212098932922245697170924571556877) (-517).
Definition f48 := Float2 (1) (-125).
Definition i28 := makepairF f47 f48.
Notation p31 := (BND r42 i28). (* BND(q + (1 + q) * mz, [-2.475e-38, 2.35099e-38]) *)
Definition f49 := Float2 (-16194481995427016693318910321146575628495930494293508596157291901399130760917156699073310801581250160372851107140547899) (-518).
Definition f50 := Float2 (95182610500588521016081575991095235563998287094087315659325128998242359243293407) (-391).
Definition i29 := makepairF f49 f50.
Notation p32 := (BND _q i29). (* BND(q, [-1.88725e-38, 1.88725e-38]) *)
Lemma l36 : s1 -> p3 (* BND(E1, [-1.87804e-38, 1.87804e-38]) *).
Proof.
 intros h0.
 assert (h1 := l15 h0).
 exact (proj2 h1).
Qed.
Lemma l37 : s1 -> p4 (* BND(X1, [0.995118, 1.00493]) *).
Proof.
 intros h0.
 assert (h1 := l16 h0).
 exact (proj2 h1).
Qed.
Definition f51 := Float2 (40150677096595129717519046478207705786862940142947363181890938711906502817596171498710366010397253102231767073237133439) (-394).
Definition f52 := Float2 (1) (1).
Definition i30 := makepairF f51 f52.
Notation p33 := (BND _X1 i30). (* BND(X1, [0.995118, 2]) *)
Lemma t11 : p3 -> p33 -> p32.
Proof.
 intros h0 h1.
 refine (div_op _E1 _X1 i3 i30 i29 h0 h1 _) ; finalize.
Qed.
Lemma l35 : s1 -> p32 (* BND(q, [-1.88725e-38, 1.88725e-38]) *).
Proof.
 intros h0.
 assert (h1 := l36 h0).
 assert (h2 := l37 h0).
 apply t11. exact h1. refine (subset _X1 i4 i30 h2 _) ; finalize.
Qed.
Definition f53 := Float2 (-5043456793138493339171717132818382567145389237120165694513463131734547622315641245355113396284594331021490742002565855) (-518).
Definition i31 := makepairF f53 f10.
Notation p34 := (BND r43 i31). (* BND((1 + q) * mz, [-5.87747e-39, 0]) *)
Definition f54 := Float2 (5043456793138493339171717132818382567145389237120165694513463131734547622315641245355113396284594331021490742002565855) (-391).
Definition i32 := makepairF f38 f54.
Notation p35 := (BND r25 i32). (* BND(1 + q, [0.5, 1]) *)
Definition i33 := makepairF f34 f50.
Notation p36 := (BND _q i33). (* BND(q, [-0.5, 1.88725e-38]) *)
Lemma t12 : p22 -> p36 -> p35.
Proof.
 intros h0 h1.
 refine (add r12 _q i19 i33 i32 h0 h1 _) ; finalize.
Qed.
Lemma l39 : s1 -> p35 (* BND(1 + q, [0.5, 1]) *).
Proof.
 intros h0.
 assert (h1 := l12 h0).
 assert (h2 := l35 h0).
 apply t12. exact h1. refine (subset _q i29 i33 h2 _) ; finalize.
Qed.
Lemma l40 : s1 -> p5 (* BND(mz, [-5.87747e-39, 0]) *).
Proof.
 intros h0.
 assert (h1 := l17 h0).
 exact (proj2 h1).
Qed.
Lemma t13 : p35 -> p5 -> p34.
Proof.
 intros h0 h1.
 refine (mul_pn r25 _mz i32 i5 i31 h0 h1 _) ; finalize.
Qed.
Lemma l38 : s1 -> p34 (* BND((1 + q) * mz, [-5.87747e-39, 0]) *).
Proof.
 intros h0.
 assert (h1 := l39 h0).
 assert (h2 := l40 h0).
 apply t13. exact h1. exact h2.
Qed.
Definition i34 := makepairF f49 f48.
Notation p37 := (BND _q i34). (* BND(q, [-1.88725e-38, 2.35099e-38]) *)
Lemma t14 : p37 -> p34 -> p31.
Proof.
 intros h0 h1.
 refine (add _q r43 i34 i31 i28 h0 h1 _) ; finalize.
Qed.
Lemma l34 : s1 -> p31 (* BND(q + (1 + q) * mz, [-2.475e-38, 2.35099e-38]) *).
Proof.
 intros h0.
 assert (h1 := l35 h0).
 assert (h2 := l38 h0).
 apply t14. refine (subset _q i29 i34 h1 _) ; finalize. exact h2.
Qed.
Lemma t15 : p2 -> p31 -> p30.
Proof.
 intros h0 h1.
 refine (mul_oo _k3 r42 i2 i28 i27 h0 h1 _) ; finalize.
Qed.
Lemma l33 : s1 -> p30 (* BND(k3 * (q + (1 + q) * mz), [-2.83996e-40, 2.83996e-40]) *).
Proof.
 intros h0.
 assert (h1 := l24 h0).
 assert (h2 := l34 h0).
 apply t15. exact h1. exact h2.
Qed.
Lemma t16 : p18 -> p30 -> p17.
Proof.
 intros h0 h1.
 refine (add r36 r41 i15 i27 i14 h0 h1 _) ; finalize.
Qed.
Lemma l7 : s1 -> p17 (* BND(k1 * ((1 + eL) * (1 + mL) - 1) + k2 * eN + k3 * (q + (1 + q) * mz), [-2.98751e-38, 1.80298e-38]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 assert (h2 := l33 h0).
 apply t16. exact h1. exact h2.
Qed.
Lemma l41 : s1 -> p11 (* BND(dz, [-1.20304e-38, 1.20304e-38]) *).
Proof.
 intros h0.
 assert (h1 := l23 h0).
 exact (proj2 h1).
Qed.
Lemma t17 : p17 -> p11 -> p16.
Proof.
 intros h0 h1.
 refine (add r35 _dz i14 i9 i13 h0 h1 _) ; finalize.
Qed.
Lemma l6 : s1 -> p16 (* BND(k1 * ((1 + eL) * (1 + mL) - 1) + k2 * eN + k3 * (q + (1 + q) * mz) + dz, [-4.19056e-38, 3.00602e-38]) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 assert (h2 := l41 h0).
 apply t17. exact h1. exact h2.
Qed.
Lemma l42 : s1 -> p9 (* BND(s1, [-2.37854e-38, 2.37854e-38]) *).
Proof.
 intros h0.
 assert (h1 := l21 h0).
 exact (proj2 h1).
Qed.
Lemma t18 : p16 -> p9 -> p15.
Proof.
 intros h0 h1.
 refine (add r34 _s1 i13 i7 i12 h0 h1 _) ; finalize.
Qed.
Lemma l5 : s1 -> p15 (* BND(k1 * ((1 + eL) * (1 + mL) - 1) + k2 * eN + k3 * (q + (1 + q) * mz) + dz + s1, [-6.5691e-38, 5.38456e-38]) *).
Proof.
 intros h0.
 assert (h1 := l6 h0).
 assert (h2 := l42 h0).
 apply t18. exact h1. exact h2.
Qed.
Lemma l43 : s1 -> p10 (* BND(s2, [-1.20075e-38, 1.20075e-38]) *).
Proof.
 intros h0.
 assert (h1 := l22 h0).
 exact (proj2 h1).
Qed.
Lemma t19 : p15 -> p10 -> p14.
Proof.
 intros h0 h1.
 refine (add r33 _s2 i12 i8 i11 h0 h1 _) ; finalize.
Qed.
Lemma l4 : s1 -> p14 (* BND(k1 * ((1 + eL) * (1 + mL) - 1) + k2 * eN + k3 * (q + (1 + q) * mz) + dz + s1 + s2, [-7.76984e-38, 6.58531e-38]) *).
Proof.
 intros h0.
 assert (h1 := l5 h0).
 assert (h2 := l43 h0).
 apply t19. exact h1. exact h2.
Qed.
Definition i35 := makepairF f10 f10.
Notation p38 := (REL r2 r32 i35). (* REL(Y - 1, k1 * ((1 + eL) * (1 + mL) - 1) + k2 * eN + k3 * (q + (1 + q) * mz) + dz + s1 + s2, [0, 0]) *)
Notation p39 := (r2 = r32). (* EQL(Y - 1, k1 * ((1 + eL) * (1 + mL) - 1) + k2 * eN + k3 * (q + (1 + q) * mz) + dz + s1 + s2) *)
Notation p40 := (NZR _X1). (* NZR(X1) *)
Definition i36 := makepairF f38 f52.
Notation p41 := (ABS _X1 i36). (* ABS(X1, [0.5, 2]) *)
Notation p42 := (BND _X1 i36). (* BND(X1, [0.5, 2]) *)
Lemma t20 : p42 -> p41.
Proof.
 intros h0.
 refine (abs_of_bnd_p _X1 i36 i36 h0 _) ; finalize.
Qed.
Lemma l47 : s1 -> p41 (* ABS(X1, [0.5, 2]) *).
Proof.
 intros h0.
 assert (h1 := l37 h0).
 apply t20. refine (subset _X1 i4 i36 h1 _) ; finalize.
Qed.
Lemma t21 : p41 -> p40.
Proof.
 intros h0.
 refine (nzr_of_abs _X1 i36 h0 _) ; finalize.
Qed.
Lemma l46 : s1 -> p40 (* NZR(X1) *).
Proof.
 intros h0.
 assert (h1 := l47 h0).
 apply t21. exact h1.
Qed.
Lemma t22 : p40 -> p39.
Proof.
 intros h0.
 refine (b1 h0) ; finalize.
Qed.
Lemma l45 : s1 -> p39 (* EQL(Y - 1, k1 * ((1 + eL) * (1 + mL) - 1) + k2 * eN + k3 * (q + (1 + q) * mz) + dz + s1 + s2) *).
Proof.
 intros h0.
 assert (h1 := l46 h0).
 apply t22. exact h1.
Qed.
Notation p43 := (REL r32 r32 i35). (* REL(k1 * ((1 + eL) * (1 + mL) - 1) + k2 * eN + k3 * (q + (1 + q) * mz) + dz + s1 + s2, k1 * ((1 + eL) * (1 + mL) - 1) + k2 * eN + k3 * (q + (1 + q) * mz) + dz + s1 + s2, [0, 0]) *)
Lemma t23 : p43.
Proof.
 refine (rel_refl r32 i35 _) ; finalize.
Qed.
Lemma l48 : s1 -> p43 (* REL(k1 * ((1 + eL) * (1 + mL) - 1) + k2 * eN + k3 * (q + (1 + q) * mz) + dz + s1 + s2, k1 * ((1 + eL) * (1 + mL) - 1) + k2 * eN + k3 * (q + (1 + q) * mz) + dz + s1 + s2, [0, 0]) *).
Proof.
 intros h0.
 apply t23.
Qed.
Lemma t24 : p39 -> p43 -> p38.
Proof.
 intros h0 h1.
 refine (rel_rewrite_1 r2 r32 r32 i35 h0 h1) ; finalize.
Qed.
Lemma l44 : s1 -> p38 (* REL(Y - 1, k1 * ((1 + eL) * (1 + mL) - 1) + k2 * eN + k3 * (q + (1 + q) * mz) + dz + s1 + s2, [0, 0]) *).
Proof.
 intros h0.
 assert (h1 := l45 h0).
 assert (h2 := l48 h0).
 apply t24. exact h1. exact h2.
Qed.
Lemma t25 : p14 -> p38 -> p13.
Proof.
 intros h0 h1.
 refine (bnd_of_bnd_rel_o r2 r32 i11 i35 i11 h0 h1 _) ; finalize.
Qed.
Lemma l3 : s1 -> p13 (* BND(Y - 1, [-7.76984e-38, 6.58531e-38]) *).
Proof.
 intros h0.
 assert (h1 := l4 h0).
 assert (h2 := l44 h0).
 apply t25. exact h1. exact h2.
Qed.
Lemma l1 : s1 -> False.
Proof.
 intros h0.
 assert (h1 := l2 h0).
 assert (h2 := l3 h0).
 refine (simplify (Tatom false (Abnd 0%nat i10)) Tfalse (Abnd 0%nat i11) (List.cons r2 List.nil) h2 h1 _) ; finalize.
Qed.
End Generated_by_Gappa.
