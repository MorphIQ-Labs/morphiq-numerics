Require Import Gappa.Gappa_library.
Section Generated_by_Gappa.
Variable _zh : R.
Variable _dl : R.
Notation _zl := ((_zh * _dl)%R).
Notation _z := ((_zh + _zl)%R).
Notation r9 := ((_z * _z)%R).
Notation r10 := (Float1 (2)).
Notation r8 := ((r9 / r10)%R).
Notation r4 := ((_z - r8)%R).
Notation r12 := ((r9 * _z)%R).
Notation _c3 := (float2R (Float2 (6004799503160661) (-54))).
Notation _c4 := (float2R (Float2 (-4503599627370541) (-54))).
Notation _c5 := (float2R (Float2 (7205759403880275) (-55))).
Notation _c6 := (float2R (Float2 (-750599936424355) (-52))).
Notation _c7 := (float2R (Float2 (643371015971573) (-52))).
Notation _c8 := (float2R (Float2 (-4503984727172023) (-55))).
Notation _c9 := (float2R (Float2 (8060734871950603) (-56))).
Notation r30 := ((_z * _c9)%R).
Notation r28 := ((_c8 + r30)%R).
Notation r27 := ((_z * r28)%R).
Notation r25 := ((_c7 + r27)%R).
Notation r24 := ((_z * r25)%R).
Notation r22 := ((_c6 + r24)%R).
Notation r21 := ((_z * r22)%R).
Notation r19 := ((_c5 + r21)%R).
Notation r18 := ((_z * r19)%R).
Notation r16 := ((_c4 + r18)%R).
Notation r15 := ((_z * r16)%R).
Notation _Wz := ((_c3 + r15)%R).
Notation _Tz := ((r12 * _Wz)%R).
Notation r3 := ((r4 + _Tz)%R).
Variable _al : R.
Notation _a := ((_al * _Tz)%R).
Notation _L := ((r3 + _a)%R).
Notation r42 := ((_zh * _zh)%R).
Notation r41 := ((r42 / r10)%R).
Notation _B := ((- r41)%R).
Notation r39 := ((_z + _B)%R).
Notation r44 := (Float1 (1)).
Variable _d1 : R.
Notation r43 := ((r44 + _d1)%R).
Notation _P1 := ((r39 * r43)%R).
Notation r50 := ((r42 * _zh)%R).
Notation r62 := ((_zh * _c9)%R).
Notation r61 := ((_c8 + r62)%R).
Notation r60 := ((_zh * r61)%R).
Notation r59 := ((_c7 + r60)%R).
Notation r58 := ((_zh * r59)%R).
Notation r57 := ((_c6 + r58)%R).
Notation r56 := ((_zh * r57)%R).
Notation r55 := ((_c5 + r56)%R).
Notation r54 := ((_zh * r55)%R).
Notation r53 := ((_c4 + r54)%R).
Notation r52 := ((_zh * r53)%R).
Notation _W := ((_c3 + r52)%R).
Notation _T := ((r50 * _W)%R).
Variable _et : R.
Notation r63 := ((r44 + _et)%R).
Notation _t := ((_T * r63)%R).
Notation r66 := ((_zh * _zl)%R).
Variable _ec : R.
Notation r67 := ((r44 + _ec)%R).
Notation _c := ((r66 * r67)%R).
Notation r47 := ((_t - _c)%R).
Variable _eu : R.
Notation r69 := ((r44 + _eu)%R).
Notation _u := ((r47 * r69)%R).
Notation r37 := ((_P1 + _u)%R).
Variable _d2 : R.
Notation r71 := ((r44 + _d2)%R).
Notation _P := ((r37 * r71)%R).
Notation r35 := ((_P - _L)%R).
Notation r34 := ((r35 / _L)%R).
Notation r74 := ((r35 / _zh)%R).
Notation r75 := ((_L / _zh)%R).
Notation r73 := ((r74 / r75)%R).
Hypothesis a1 : (_zh <> 0)%R -> (_L <> 0)%R -> r34 = r73.
Lemma b1 : NZR _zh -> NZR _L -> r34 = r73.
 intros h0 h1.
 apply a1.
 exact h0.
 exact h1.
Qed.
Notation r79 := ((r44 + _dl)%R).
Notation r82 := ((_zh * r79)%R).
Notation r81 := ((r82 * r79)%R).
Notation r80 := ((r81 / r10)%R).
Notation r78 := ((r79 - r80)%R).
Notation r83 := ((_Tz / _zh)%R).
Notation r77 := ((r78 + r83)%R).
Notation r84 := ((_al * r83)%R).
Notation r76 := ((r77 + r84)%R).
Hypothesis a2 : (_zh <> 0)%R -> r75 = r76.
Lemma b2 : NZR _zh -> r75 = r76.
 intros h0.
 apply a2.
 exact h0.
Qed.
Notation r93 := ((_zl * _dl)%R).
Notation r92 := ((r93 / r10)%R).
Notation r95 := ((_T - _Tz)%R).
Notation r94 := ((r95 / _zh)%R).
Notation r91 := ((r92 + r94)%R).
Notation r97 := ((r42 * _W)%R).
Notation r96 := ((r97 * _et)%R).
Notation r90 := ((r91 + r96)%R).
Notation r98 := ((_zl * _ec)%R).
Notation r89 := ((r90 - r98)%R).
Notation r100 := ((r47 / _zh)%R).
Notation r99 := ((r100 * _eu)%R).
Notation r88 := ((r89 + r99)%R).
Notation r87 := ((r88 - r84)%R).
Notation r102 := ((r39 / _zh)%R).
Notation r101 := ((r102 * _d1)%R).
Notation r86 := ((r87 + r101)%R).
Notation r104 := ((r37 / _zh)%R).
Notation r103 := ((r104 * _d2)%R).
Notation r85 := ((r86 + r103)%R).
Hypothesis a3 : (_zh <> 0)%R -> r74 = r85.
Lemma b3 : NZR _zh -> r74 = r85.
 intros h0.
 apply a3.
 exact h0.
Qed.
Notation r111 := ((_z * _zh)%R).
Notation r110 := ((r9 + r111)%R).
Notation r109 := ((r110 + r42)%R).
Notation r108 := ((r109 * _Wz)%R).
Notation r118 := ((_c4 * r44)%R).
Notation r120 := ((_zh + _z)%R).
Notation r119 := ((_c5 * r120)%R).
Notation r117 := ((r118 + r119)%R).
Notation r123 := ((r42 + r111)%R).
Notation r122 := ((r123 + r9)%R).
Notation r121 := ((_c6 * r122)%R).
Notation r116 := ((r117 + r121)%R).
Notation r128 := ((r111 * _zh)%R).
Notation r127 := ((r50 + r128)%R).
Notation r129 := ((r9 * _zh)%R).
Notation r126 := ((r127 + r129)%R).
Notation r125 := ((r126 + r12)%R).
Notation r124 := ((_c7 * r125)%R).
Notation r115 := ((r116 + r124)%R).
Notation r135 := ((r50 * _zh)%R).
Notation r136 := ((r128 * _zh)%R).
Notation r134 := ((r135 + r136)%R).
Notation r137 := ((r129 * _zh)%R).
Notation r133 := ((r134 + r137)%R).
Notation r138 := ((r12 * _zh)%R).
Notation r132 := ((r133 + r138)%R).
Notation r139 := ((r12 * _z)%R).
Notation r131 := ((r132 + r139)%R).
Notation r130 := ((_c8 * r131)%R).
Notation r114 := ((r115 + r130)%R).
Notation r146 := ((r135 * _zh)%R).
Notation r147 := ((r136 * _zh)%R).
Notation r145 := ((r146 + r147)%R).
Notation r148 := ((r137 * _zh)%R).
Notation r144 := ((r145 + r148)%R).
Notation r149 := ((r138 * _zh)%R).
Notation r143 := ((r144 + r149)%R).
Notation r150 := ((r139 * _zh)%R).
Notation r142 := ((r143 + r150)%R).
Notation r151 := ((r139 * _z)%R).
Notation r141 := ((r142 + r151)%R).
Notation r140 := ((_c9 * r141)%R).
Notation _D := ((r114 + r140)%R).
Notation r112 := ((r50 * _D)%R).
Notation r107 := ((r108 + r112)%R).
Notation r106 := ((_dl * r107)%R).
Notation r105 := ((- r106)%R).
Hypothesis a4 : (_zh <> 0)%R -> r94 = r105.
Lemma b4 : NZR _zh -> r94 = r105.
 intros h0.
 apply a4.
 exact h0.
Qed.
Notation r154 := ((r79 * _z)%R).
Notation r153 := ((r154 * _z)%R).
Notation r152 := ((r153 * _Wz)%R).
Hypothesis a5 : (_zh <> 0)%R -> r83 = r152.
Lemma b5 : NZR _zh -> r83 = r152.
 intros h0.
 apply a5.
 exact h0.
Qed.
Notation r156 := ((r97 * r63)%R).
Notation r157 := ((_zl * r67)%R).
Notation r155 := ((r156 - r157)%R).
Hypothesis a6 : (_zh <> 0)%R -> r100 = r155.
Lemma b6 : NZR _zh -> r100 = r155.
 intros h0.
 apply a6.
 exact h0.
Qed.
Notation r159 := ((_zh / r10)%R).
Notation r158 := ((r79 - r159)%R).
Hypothesis a7 : (_zh <> 0)%R -> r102 = r158.
Lemma b7 : NZR _zh -> r102 = r158.
 intros h0.
 apply a7.
 exact h0.
Qed.
Notation r160 := ((_u / _zh)%R).
Notation r161 := ((r100 * r69)%R).
Hypothesis a8 : (_zh <> 0)%R -> r160 = r161.
Lemma b8 : NZR _zh -> r160 = r161.
 intros h0.
 apply a8.
 exact h0.
Qed.
Notation r163 := ((r102 * r43)%R).
Notation r162 := ((r163 + r160)%R).
Hypothesis a9 : (_zh <> 0)%R -> r104 = r162.
Lemma b9 : NZR _zh -> r104 = r162.
 intros h0.
 apply a9.
 exact h0.
Qed.
Notation r164 := ((Rabs _zh)%R).
Definition f1 := Float2 (1) (-64).
Definition f2 := Float2 (80696341590167128190183336492762922277553037908230366465363237155637854447075094068654269148145619287504548485417148267) (-402).
Definition i1 := makepairF f1 f2.
Notation p1 := (BND r164 i1). (* BND(|zh|, [5.42101e-20, 0.0078126]) *)
Definition f3 := Float2 (-1) (-53).
Definition f4 := Float2 (1) (-53).
Definition i2 := makepairF f3 f4.
Notation p2 := (BND _dl i2). (* BND(dl, [-1.11022e-16, 1.11022e-16]) *)
Definition s8 := (p1 /\ p2).
Definition f5 := Float2 (-1) (-50).
Definition f6 := Float2 (1) (-50).
Definition i3 := makepairF f5 f6.
Notation p3 := (BND _et i3). (* BND(et, [-8.88178e-16, 8.88178e-16]) *)
Definition s7 := (s8 /\ p3).
Notation p4 := (BND _ec i2). (* BND(ec, [-1.11022e-16, 1.11022e-16]) *)
Definition s6 := (s7 /\ p4).
Notation p5 := (BND _eu i2). (* BND(eu, [-1.11022e-16, 1.11022e-16]) *)
Definition s5 := (s6 /\ p5).
Definition f7 := Float2 (-535) (-63).
Definition f8 := Float2 (535) (-63).
Definition i4 := makepairF f7 f8.
Notation p6 := (BND _al i4). (* BND(al, [-5.80048e-17, 5.80048e-17]) *)
Definition s4 := (s5 /\ p6).
Definition f9 := Float2 (-97) (-111).
Definition f10 := Float2 (97) (-111).
Definition i5 := makepairF f9 f10.
Notation p7 := (BND _d1 i5). (* BND(d1, [-3.7363e-32, 3.7363e-32]) *)
Definition s3 := (s4 /\ p7).
Definition f11 := Float2 (-1) (-105).
Definition f12 := Float2 (1) (-105).
Definition i6 := makepairF f11 f12.
Notation p8 := (BND _d2 i6). (* BND(d2, [-2.46519e-32, 2.46519e-32]) *)
Definition s2 := (s3 /\ p8).
Definition f13 := Float2 (-3) (-66).
Definition f14 := Float2 (3) (-66).
Definition i7 := makepairF f13 f14.
Notation p9 := (BND r34 i7). (* BND((P - L) / L, [-4.06576e-20, 4.06576e-20]) *)
Definition s9 := (not p9).
Definition s1 := (s2 /\ s9).
Definition f15 := Float2 (0) (0).
Notation p10 := ((_zh <= f15)%R). (* BND(zh, [-inf, 0]) *)
Lemma l3 : s1 -> s9.
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj2 h1).
Qed.
Definition f16 := Float2 (-340325354418537011692887619021102722212027825942325591898892496702456432518811370396699142277808627268178651500916906493) (-462).
Definition f17 := Float2 (340325354418537011692887619021102722212027825942325591898892496702456432518811370396699142277808627268178651500916906493) (-462).
Definition i8 := makepairF f16 f17.
Notation p11 := (BND r34 i8). (* BND((P - L) / L, [-2.85783e-20, 2.85783e-20]) *)
Notation p12 := (r34 = r73). (* EQL((P - L) / L, (P - L) / zh / (L / zh)) *)
Notation p13 := (NZR _zh). (* NZR(zh) *)
Notation p14 := (ABS _zh i1). (* ABS(zh, [5.42101e-20, 0.0078126]) *)
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
Lemma l11 : s1 -> s6.
Proof.
 intros h0.
 assert (h1 := l12 h0).
 exact (proj1 h1).
Qed.
Lemma l10 : s1 -> s7.
Proof.
 intros h0.
 assert (h1 := l11 h0).
 exact (proj1 h1).
Qed.
Lemma l9 : s1 -> s8.
Proof.
 intros h0.
 assert (h1 := l10 h0).
 exact (proj1 h1).
Qed.
Lemma l8 : s1 -> p1 (* BND(|zh|, [5.42101e-20, 0.0078126]) *).
Proof.
 intros h0.
 assert (h1 := l9 h0).
 exact (proj1 h1).
Qed.
Lemma t1 : p1 -> p14.
Proof.
 intros h0.
 refine (abs_of_uabs _zh i1 h0 _) ; finalize.
Qed.
Lemma l7 : s1 -> p14 (* ABS(zh, [5.42101e-20, 0.0078126]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 apply t1. exact h1.
Qed.
Definition f18 := Float2 (1) (0).
Definition i9 := makepairF f1 f18.
Notation p15 := (ABS _zh i9). (* ABS(zh, [5.42101e-20, 1]) *)
Lemma t2 : p15 -> p13.
Proof.
 intros h0.
 refine (nzr_of_abs _zh i9 h0 _) ; finalize.
Qed.
Lemma l6 : s1 -> p13 (* NZR(zh) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 apply t2. refine (abs_subset _zh i1 i9 h1 _) ; finalize.
Qed.
Notation p16 := (NZR _L). (* NZR(L) *)
Definition f19 := Float2 (1) (-65).
Definition i10 := makepairF f19 f18.
Notation p17 := (ABS _L i10). (* ABS(L, [2.71051e-20, 1]) *)
Definition f20 := Float2 (-1) (0).
Definition f21 := Float2 (-1) (-65).
Definition i11 := makepairF f20 f21.
Notation p18 := (BND _L i11). (* BND(L, [-1, -2.71051e-20]) *)
Notation r165 := ((r75 * _zh)%R).
Notation p19 := (BND r165 i11). (* BND(L / zh * zh, [-1, -2.71051e-20]) *)
Definition f22 := Float2 (160756874266144722229268768581460652361576037686250967545141391414466170448827619073450156918313164651133981454274135149) (-396).
Definition f23 := Float2 (1) (1).
Definition i12 := makepairF f22 f23.
Notation p20 := (BND r75 i12). (* BND(L / zh, [0.996073, 2]) *)
Notation p21 := (BND r76 i12). (* BND(1 + dl - zh * (1 + dl) * (1 + dl) / 2 + Tz / zh + al * (Tz / zh), [0.996073, 2]) *)
Definition f24 := Float2 (2572109988258315555671365685356862991109846249318396898270523693833495322869984119259772683163888587915071657382728144497) (-400).
Definition f25 := Float2 (3) (-1).
Definition i13 := makepairF f24 f25.
Notation p22 := (BND r77 i13). (* BND(1 + dl - zh * (1 + dl) * (1 + dl) / 2 + Tz / zh, [0.996073, 1.5]) *)
Definition f26 := Float2 (2572162835388137409705045845271973346908661797697019707143000591664758432795956904661938978048102860815735232619054548101) (-400).
Definition f27 := Float2 (5) (-2).
Definition i14 := makepairF f26 f27.
Notation p23 := (BND r78 i14). (* BND(1 + dl - zh * (1 + dl) * (1 + dl) / 2, [0.996094, 1.25]) *)
Definition f28 := Float2 (9007199254740991) (-53).
Definition f29 := Float2 (9007199254740993) (-53).
Definition i15 := makepairF f28 f29.
Notation p24 := (BND r79 i15). (* BND(1 + dl, [1, 1]) *)
Definition i16 := makepairF f18 f18.
Notation p25 := (BND r44 i16). (* BND(1, [1, 1]) *)
Lemma t3 : p25.
Proof.
 refine (constant1 _ i16 _) ; finalize.
Qed.
Lemma l25 : s1 -> p25 (* BND(1, [1, 1]) *).
Proof.
 intros h0.
 apply t3.
Qed.
Lemma l26 : s1 -> p2 (* BND(dl, [-1.11022e-16, 1.11022e-16]) *).
Proof.
 intros h0.
 assert (h1 := l9 h0).
 exact (proj2 h1).
Qed.
Lemma t4 : p25 -> p2 -> p24.
Proof.
 intros h0 h1.
 refine (add r44 _dl i16 i2 i15 h0 h1 _) ; finalize.
Qed.
Lemma l24 : s1 -> p24 (* BND(1 + dl, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l25 h0).
 assert (h2 := l26 h0).
 apply t4. exact h1. exact h2.
Qed.
Definition f30 := Float2 (-1) (-3).
Definition f31 := Float2 (10087042698770893263546327972099576068432082371336206117035118840748722022279366602346864171433961867848800587982125947) (-400).
Definition i17 := makepairF f30 f31.
Notation p26 := (BND r80 i17). (* BND(zh * (1 + dl) * (1 + dl) / 2, [-0.125, 0.0039063]) *)
Definition f32 := Float2 (-1) (-2).
Definition f33 := Float2 (10087042698770893263546327972099576068432082371336206117035118840748722022279366602346864171433961867848800587982125947) (-399).
Definition i18 := makepairF f32 f33.
Notation p27 := (BND r81 i18). (* BND(zh * (1 + dl) * (1 + dl), [-0.25, 0.0078126]) *)
Definition f34 := Float2 (10087042698770892143659622516847408510362837653346572912373131792961801012902297170723887501574228131427252812437639707) (-399).
Definition i19 := makepairF f30 f34.
Notation p28 := (BND r82 i19). (* BND(zh * (1 + dl), [-0.125, 0.0078126]) *)
Definition f35 := Float2 (-5043521349385445511886458530797682642347064869264397904085202322227365902942193379290891821759101205469034280338571767) (-398).
Definition i20 := makepairF f35 f2.
Notation p29 := (BND _zh i20). (* BND(zh, [-0.0078126, 0.0078126]) *)
Lemma t5 : p14 -> p29.
Proof.
 intros h0.
 refine (bnd_of_abs _zh i1 i20 h0 _) ; finalize.
Qed.
Lemma l30 : s1 -> p29 (* BND(zh, [-0.0078126, 0.0078126]) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 apply t5. exact h1.
Qed.
Definition f36 := Float2 (-1) (-4).
Definition i21 := makepairF f36 f2.
Notation p30 := (BND _zh i21). (* BND(zh, [-0.0625, 0.0078126]) *)
Definition f37 := Float2 (1) (-1).
Definition i22 := makepairF f37 f29.
Notation p31 := (BND r79 i22). (* BND(1 + dl, [0.5, 1]) *)
Lemma t6 : p30 -> p31 -> p28.
Proof.
 intros h0 h1.
 refine (mul_op _zh r79 i21 i22 i19 h0 h1 _) ; finalize.
Qed.
Lemma l29 : s1 -> p28 (* BND(zh * (1 + dl), [-0.125, 0.0078126]) *).
Proof.
 intros h0.
 assert (h1 := l30 h0).
 assert (h2 := l24 h0).
 apply t6. refine (subset _zh i20 i21 h1 _) ; finalize. refine (subset r79 i15 i22 h2 _) ; finalize.
Qed.
Lemma t7 : p28 -> p31 -> p27.
Proof.
 intros h0 h1.
 refine (mul_op r82 r79 i19 i22 i18 h0 h1 _) ; finalize.
Qed.
Lemma l28 : s1 -> p27 (* BND(zh * (1 + dl) * (1 + dl), [-0.25, 0.0078126]) *).
Proof.
 intros h0.
 assert (h1 := l29 h0).
 assert (h2 := l24 h0).
 apply t7. exact h1. refine (subset r79 i15 i22 h2 _) ; finalize.
Qed.
Definition i23 := makepairF f23 f23.
Notation p32 := (BND r10 i23). (* BND(2, [2, 2]) *)
Lemma t8 : p32.
Proof.
 refine (constant1 _ i23 _) ; finalize.
Qed.
Lemma l31 : s1 -> p32 (* BND(2, [2, 2]) *).
Proof.
 intros h0.
 apply t8.
Qed.
Lemma t9 : p27 -> p32 -> p26.
Proof.
 intros h0 h1.
 refine (div_op r81 r10 i18 i23 i17 h0 h1 _) ; finalize.
Qed.
Lemma l27 : s1 -> p26 (* BND(zh * (1 + dl) * (1 + dl) / 2, [-0.125, 0.0039063]) *).
Proof.
 intros h0.
 assert (h1 := l28 h0).
 assert (h2 := l31 h0).
 apply t9. exact h1. exact h2.
Qed.
Definition f38 := Float2 (9) (-3).
Definition i24 := makepairF f28 f38.
Notation p33 := (BND r79 i24). (* BND(1 + dl, [1, 1.125]) *)
Lemma t10 : p33 -> p26 -> p23.
Proof.
 intros h0 h1.
 refine (sub r79 r80 i24 i17 i14 h0 h1 _) ; finalize.
Qed.
Lemma l23 : s1 -> p23 (* BND(1 + dl - zh * (1 + dl) * (1 + dl) / 2, [0.996094, 1.25]) *).
Proof.
 intros h0.
 assert (h1 := l24 h0).
 assert (h2 := l27 h0).
 apply t10. refine (subset r79 i15 i24 h1 _) ; finalize. exact h2.
Qed.
Definition f39 := Float2 (-13211782455463508420039978777588949703887094655702218119224457815777481493196350541573721053568225165893809081600901) (-398).
Definition f40 := Float2 (2933605015678854770486689579908945391981033225126611201188810488411080944092546150331051414099242695) (-346).
Definition i25 := makepairF f39 f40.
Notation p34 := (BND r83 i25). (* BND(Tz / zh, [-2.04655e-05, 2.04655e-05]) *)
Notation p35 := (BND r152 i25). (* BND((1 + dl) * z * z * Wz, [-2.04655e-05, 2.04655e-05]) *)
Definition f41 := Float2 (-78806029788417489460008916954529203615716701846635337802523633099939301817776494323101204229480801520243499586390581) (-399).
Definition f42 := Float2 (17498453750079410053965593297882020443915585394075792936013609835108462546355066874048934495329455157) (-347).
Definition i26 := makepairF f41 f42.
Notation p36 := (BND r153 i26). (* BND((1 + dl) * z * z, [-6.10367e-05, 6.10367e-05]) *)
Definition f43 := Float2 (-78805021084147603621455687282027938034625643526064110289336865943349390799057551580834876339327827092568754593610359) (-392).
Definition f44 := Float2 (78805021084147603621455687282027938034625643526064110289336865943349390799057551580834876339327827092568754593610359) (-392).
Definition i27 := makepairF f43 f44.
Notation p37 := (BND r154 i27). (* BND((1 + dl) * z, [-0.0078126, 0.0078126]) *)
Definition f45 := Float2 (-315220084336590379489363203651481515948838676667080403511660368530056281653196786585121484424194629107101650388676241) (-394).
Definition f46 := Float2 (645570732721337097194215841078234144663221609814180666391880434749555264825747018926328800100750600411344179996008941243) (-405).
Definition i28 := makepairF f45 f46.
Notation p38 := (BND _z i28). (* BND(z, [-0.0078126, 0.0078126]) *)
Definition f47 := Float2 (-69992919090953252701604294244676111069012670446781691825438619400758881491128501607530574015735031011) (-395).
Definition f48 := Float2 (71672749149136130766442797306548337734668974537504452429249146266377094646915585646111307792112671755107) (-405).
Definition i29 := makepairF f47 f48.
Notation p39 := (BND _zl i29). (* BND(zl, [-8.67373e-19, 8.67373e-19]) *)
Definition f49 := Float2 (-71672749149136130766442797306548337734668974537504452429249146266377094646915585646111307792112671755107) (-352).
Definition f50 := Float2 (71672749149136130766442797306548337734668974537504452429249146266377094646915585646111307792112671755107) (-352).
Definition i30 := makepairF f49 f50.
Notation p40 := (BND _zh i30). (* BND(zh, [-0.0078126, 0.0078126]) *)
Lemma t11 : p40 -> p2 -> p39.
Proof.
 intros h0 h1.
 refine (mul_oo _zh _dl i30 i2 i29 h0 h1 _) ; finalize.
Qed.
Lemma l37 : s1 -> p39 (* BND(zl, [-8.67373e-19, 8.67373e-19]) *).
Proof.
 intros h0.
 assert (h1 := l30 h0).
 assert (h2 := l26 h0).
 apply t11. refine (subset _zh i20 i30 h1 _) ; finalize. exact h2.
Qed.
Definition f51 := Float2 (-630440168673180688985807316349710330293383108658049738010650290278420737867774172411361477719887650683629285042321471) (-395).
Definition i31 := makepairF f51 f2.
Notation p41 := (BND _zh i31). (* BND(zh, [-0.0078126, 0.0078126]) *)
Lemma t12 : p41 -> p39 -> p38.
Proof.
 intros h0 h1.
 refine (add _zh _zl i31 i29 i28 h0 h1 _) ; finalize.
Qed.
Lemma l36 : s1 -> p38 (* BND(z, [-0.0078126, 0.0078126]) *).
Proof.
 intros h0.
 assert (h1 := l30 h0).
 assert (h2 := l37 h0).
 apply t12. refine (subset _zh i20 i31 h1 _) ; finalize. exact h2.
Qed.
Definition f52 := Float2 (315220084336590379489363203651481515948838676667080403511660368530056281653196786585121484424194629107101650388676241) (-394).
Definition i32 := makepairF f45 f52.
Notation p42 := (BND _z i32). (* BND(z, [-0.0078126, 0.0078126]) *)
Lemma t13 : p31 -> p42 -> p37.
Proof.
 intros h0 h1.
 refine (mul_po r79 _z i22 i32 i27 h0 h1 _) ; finalize.
Qed.
Lemma l35 : s1 -> p37 (* BND((1 + dl) * z, [-0.0078126, 0.0078126]) *).
Proof.
 intros h0.
 assert (h1 := l24 h0).
 assert (h2 := l36 h0).
 apply t13. refine (subset r79 i15 i22 h1 _) ; finalize. refine (subset _z i28 i32 h2 _) ; finalize.
Qed.
Lemma t14 : p37 -> p42 -> p36.
Proof.
 intros h0 h1.
 refine (mul_oo r154 _z i27 i32 i26 h0 h1 _) ; finalize.
Qed.
Lemma l34 : s1 -> p36 (* BND((1 + dl) * z * z, [-6.10367e-05, 6.10367e-05]) *).
Proof.
 intros h0.
 assert (h1 := l35 h0).
 assert (h2 := l36 h0).
 apply t14. exact h1. refine (subset _z i28 i32 h2 _) ; finalize.
Qed.
Definition f53 := Float2 (1) (-2).
Definition f54 := Float2 (13211444240326388639748202190595346372828507584960550436545976436349139922644552811912208827707301940210038566333383) (-384).
Definition i33 := makepairF f53 f54.
Notation p43 := (BND _Wz i33). (* BND(Wz, [0.25, 0.335299]) *)
Definition f55 := Float2 (21) (-6).
Definition f56 := Float2 (6004799503160661) (-54).
Definition i34 := makepairF f55 f56.
Notation p44 := (BND _c3 i34). (* BND(c3, [0.328125, 0.333333]) *)
Lemma t15 : p44.
Proof.
 refine (constant2 _ i34 _) ; finalize.
Qed.
Lemma l39 : s1 -> p44 (* BND(c3, [0.328125, 0.333333]) *).
Proof.
 intros h0.
 apply t15.
Qed.
Definition f57 := Float2 (77442174861562964738763751551449895302670200679189998286355599338044807402351411425119809204304467778888243915719) (-384).
Definition i35 := makepairF f36 f57.
Notation p45 := (BND r15 i35). (* BND(z * (c4 + z * (c5 + z * (c6 + z * (c7 + z * (c8 + z * c9))))), [-0.0625, 0.00196544]) *)
Definition f58 := Float2 (-619529468915301533268015695126950615431662915644687454023112906440409296838779329025655749942498957478777970647081) (-380).
Definition i36 := makepairF f58 f30.
Notation p46 := (BND r16 i36). (* BND(c4 + z * (c5 + z * (c6 + z * (c7 + z * (c8 + z * c9)))), [-0.251573, -0.125]) *)
Definition f59 := Float2 (-4503599627370541) (-54).
Definition i37 := makepairF f59 f32.
Notation p47 := (BND _c4 i37). (* BND(c4, [-0.25, -0.25]) *)
Lemma t16 : p47.
Proof.
 refine (constant2 _ i37 _) ; finalize.
Qed.
Lemma l42 : s1 -> p47 (* BND(c4, [-0.25, -0.25]) *).
Proof.
 intros h0.
 apply t16.
Qed.
Definition f60 := Float2 (-3873122096631643933492241341169352064778221233574794047396434839092446679304885229497591465138084460364030959657) (-380).
Definition f61 := Float2 (1) (-3).
Definition i38 := makepairF f60 f61.
Notation p48 := (BND r18 i38). (* BND(z * (c5 + z * (c6 + z * (c7 + z * (c8 + z * c9)))), [-0.00157276, 0.125]) *)
Definition f62 := Float2 (1936536260651685410171404033367495173330108696797073271165524585383748703418529519052239220563332830089285027325) (-372).
Definition i39 := makepairF f61 f62.
Notation p49 := (BND r19 i39). (* BND(c5 + z * (c6 + z * (c7 + z * (c8 + z * c9))), [0.125, 0.201311]) *)
Definition f63 := Float2 (3) (-4).
Definition f64 := Float2 (7205759403880275) (-55).
Definition i40 := makepairF f63 f64.
Notation p50 := (BND _c5 i40). (* BND(c5, [0.1875, 0.2]) *)
Lemma t17 : p50.
Proof.
 refine (constant2 _ i40 _) ; finalize.
Qed.
Lemma l45 : s1 -> p50 (* BND(c5, [0.1875, 0.2]) *).
Proof.
 intros h0.
 apply t17.
Qed.
Definition f65 := Float2 (12610176820003837848815090567416299018186920686577003656850411050957429330824940576913685059932964126507222525) (-372).
Definition i41 := makepairF f36 f65.
Notation p51 := (BND r21 i41). (* BND(z * (c6 + z * (c7 + z * (c8 + z * c9))), [-0.0625, 0.00131088]) *)
Definition f66 := Float2 (-807040986355620180785156385271647604287620697687227699930868160847184354786607579500406401121326842083599241937) (-371).
Definition i42 := makepairF f66 f30.
Notation p52 := (BND r22 i42). (* BND(c6 + z * (c7 + z * (c8 + z * c9)), [-0.16779, -0.125]) *)
Definition f67 := Float2 (-750599936424355) (-52).
Definition f68 := Float2 (-5) (-5).
Definition i43 := makepairF f67 f68.
Notation p53 := (BND _c6 i43). (* BND(c6, [-0.166667, -0.15625]) *)
Lemma t18 : p53.
Proof.
 refine (constant2 _ i43 _) ; finalize.
Qed.
Lemma l48 : s1 -> p53 (* BND(c6, [-0.166667, -0.15625]) *).
Proof.
 intros h0.
 apply t18.
Qed.
Definition f69 := Float2 (-5405119672879387017318476579539575042103213937205291990303390641398321268465380190464470326319613053045887697) (-371).
Definition f70 := Float2 (1) (-5).
Definition i44 := makepairF f69 f70.
Notation p54 := (BND r24 i44). (* BND(z * (c7 + z * (c8 + z * c9)), [-0.00112377, 0.03125]) *)
Definition f71 := Float2 (21620201952932548132302488172274058790775716278503229411647156421648408509243821977516764026887234300395221259) (-366).
Definition i45 := makepairF f61 f71.
Notation p55 := (BND r25 i45). (* BND(c7 + z * (c8 + z * c9), [0.125, 0.143841]) *)
Definition f72 := Float2 (9) (-6).
Definition f73 := Float2 (643371015971573) (-52).
Definition i46 := makepairF f72 f73.
Notation p56 := (BND _c7 i46). (* BND(c7, [0.140625, 0.142857]) *)
Lemma t19 : p56.
Proof.
 refine (constant2 _ i46 _) ; finalize.
Qed.
Lemma l51 : s1 -> p56 (* BND(c7, [0.140625, 0.142857]) *).
Proof.
 intros h0.
 apply t19.
Qed.
Definition f74 := Float2 (-1) (-6).
Definition f75 := Float2 (147824618517787009099283210897263006469332107650364950662627404030119437913042857918237897412820465459753227) (-366).
Definition i47 := makepairF f74 f75.
Notation p57 := (BND r27 i47). (* BND(z * (c8 + z * c9), [-0.015625, 0.000983486]) *)
Definition f76 := Float2 (-147822726386889240505175236166500084132898118337464639107276486773930746340046616826490624528052913184476485) (-359).
Definition i48 := makepairF f76 f36.
Notation p58 := (BND r28 i48). (* BND(c8 + z * c9, [-0.125885, -0.0625]) *)
Definition f77 := Float2 (-4503984727172023) (-55).
Definition i49 := makepairF f77 f30.
Notation p59 := (BND _c8 i49). (* BND(c8, [-0.125011, -0.125]) *)
Lemma t20 : p59.
Proof.
 refine (constant2 _ i49 _) ; finalize.
Qed.
Lemma l54 : s1 -> p59 (* BND(c8, [-0.125011, -0.125]) *).
Proof.
 intros h0.
 apply t20.
Qed.
Definition f78 := Float2 (-1026263569121627453910098524212132235291616491174124539205831257735047569042361249887477125114306483490117) (-359).
Definition f79 := Float2 (1) (-4).
Definition i50 := makepairF f78 f79.
Notation p60 := (BND r30 i50). (* BND(z * c9, [-0.000873958, 0.0625]) *)
Definition f80 := Float2 (8060734871950603) (-56).
Definition i51 := makepairF f79 f80.
Notation p61 := (BND _c9 i51). (* BND(c9, [0.0625, 0.111865]) *)
Lemma t21 : p61.
Proof.
 refine (constant2 _ i51 _) ; finalize.
Qed.
Lemma l56 : s1 -> p61 (* BND(c9, [0.0625, 0.111865]) *).
Proof.
 intros h0.
 apply t21.
Qed.
Definition f81 := Float2 (-18348223782178851513271406505459542150425181995790940913817633905567710849758981877537530638754520862543819) (-360).
Definition i52 := makepairF f81 f37.
Notation p62 := (BND _z i52). (* BND(z, [-0.0078126, 0.5]) *)
Lemma t22 : p62 -> p61 -> p60.
Proof.
 intros h0 h1.
 refine (mul_op _z _c9 i52 i51 i50 h0 h1 _) ; finalize.
Qed.
Lemma l55 : s1 -> p60 (* BND(z * c9, [-0.000873958, 0.0625]) *).
Proof.
 intros h0.
 assert (h1 := l36 h0).
 assert (h2 := l56 h0).
 apply t22. refine (subset _z i28 i52 h1 _) ; finalize. exact h2.
Qed.
Lemma t23 : p59 -> p60 -> p58.
Proof.
 intros h0 h1.
 refine (add _c8 r30 i49 i50 i48 h0 h1 _) ; finalize.
Qed.
Lemma l53 : s1 -> p58 (* BND(c8 + z * c9, [-0.125885, -0.0625]) *).
Proof.
 intros h0.
 assert (h1 := l54 h0).
 assert (h2 := l55 h0).
 apply t23. exact h1. exact h2.
Qed.
Definition f82 := Float2 (-4697145288237785987397480065397642790508846590922480873937314279825333977538299360649607843521157340811217583) (-368).
Definition i53 := makepairF f82 f79.
Notation p63 := (BND _z i53). (* BND(z, [-0.0078126, 0.0625]) *)
Lemma t24 : p63 -> p58 -> p57.
Proof.
 intros h0 h1.
 refine (mul_on _z r28 i53 i48 i47 h0 h1 _) ; finalize.
Qed.
Lemma l52 : s1 -> p57 (* BND(z * (c8 + z * c9), [-0.015625, 0.000983486]) *).
Proof.
 intros h0.
 assert (h1 := l36 h0).
 assert (h2 := l53 h0).
 apply t24. refine (subset _z i28 i53 h1 _) ; finalize. exact h2.
Qed.
Lemma t25 : p56 -> p57 -> p55.
Proof.
 intros h0 h1.
 refine (add _c7 r27 i46 i47 i45 h0 h1 _) ; finalize.
Qed.
Lemma l50 : s1 -> p55 (* BND(c7 + z * (c8 + z * c9), [0.125, 0.143841]) *).
Proof.
 intros h0.
 assert (h1 := l51 h0).
 assert (h2 := l52 h0).
 apply t25. exact h1. exact h2.
Qed.
Definition f83 := Float2 (-75154324611804575798359681046362284648141545454759693982997028477205343640612789770393725496338517452979481313) (-372).
Definition i54 := makepairF f83 f61.
Notation p64 := (BND _z i54). (* BND(z, [-0.0078126, 0.125]) *)
Lemma t26 : p64 -> p55 -> p54.
Proof.
 intros h0 h1.
 refine (mul_op _z r25 i54 i45 i44 h0 h1 _) ; finalize.
Qed.
Lemma l49 : s1 -> p54 (* BND(z * (c7 + z * (c8 + z * c9)), [-0.00112377, 0.03125]) *).
Proof.
 intros h0.
 assert (h1 := l36 h0).
 assert (h2 := l50 h0).
 apply t26. refine (subset _z i28 i54 h1 _) ; finalize. exact h2.
Qed.
Lemma t27 : p53 -> p54 -> p52.
Proof.
 intros h0 h1.
 refine (add _c6 r24 i43 i44 i42 h0 h1 _) ; finalize.
Qed.
Lemma l47 : s1 -> p52 (* BND(c6 + z * (c7 + z * (c8 + z * c9)), [-0.16779, -0.125]) *).
Proof.
 intros h0.
 assert (h1 := l48 h0).
 assert (h2 := l49 h0).
 apply t27. exact h1. exact h2.
Qed.
Definition f84 := Float2 (-1202469193788873212773754896741796554370264727276155103727952455635285498249804636326299607941416279247671701007) (-376).
Definition i55 := makepairF f84 f53.
Notation p65 := (BND _z i55). (* BND(z, [-0.0078126, 0.25]) *)
Lemma t28 : p65 -> p52 -> p51.
Proof.
 intros h0 h1.
 refine (mul_on _z r22 i55 i42 i41 h0 h1 _) ; finalize.
Qed.
Lemma l46 : s1 -> p51 (* BND(z * (c6 + z * (c7 + z * (c8 + z * c9))), [-0.0625, 0.00131088]) *).
Proof.
 intros h0.
 assert (h1 := l36 h0).
 assert (h2 := l47 h0).
 apply t28. refine (subset _z i28 i55 h1 _) ; finalize. exact h2.
Qed.
Lemma t29 : p50 -> p51 -> p49.
Proof.
 intros h0 h1.
 refine (add _c5 r21 i40 i41 i39 h0 h1 _) ; finalize.
Qed.
Lemma l44 : s1 -> p49 (* BND(c5 + z * (c6 + z * (c7 + z * (c8 + z * c9))), [0.125, 0.201311]) *).
Proof.
 intros h0.
 assert (h1 := l45 h0).
 assert (h2 := l46 h0).
 apply t29. exact h1. exact h2.
Qed.
Definition f85 := Float2 (-9619753550310985702190039173934372434962117818209240829823619645082283985998437090610396863531330233981373608053) (-379).
Definition i56 := makepairF f85 f37.
Notation p66 := (BND _z i56). (* BND(z, [-0.0078126, 0.5]) *)
Lemma t30 : p66 -> p49 -> p48.
Proof.
 intros h0 h1.
 refine (mul_op _z r19 i56 i39 i38 h0 h1 _) ; finalize.
Qed.
Lemma l43 : s1 -> p48 (* BND(z * (c5 + z * (c6 + z * (c7 + z * (c8 + z * c9)))), [-0.00157276, 0.125]) *).
Proof.
 intros h0.
 assert (h1 := l36 h0).
 assert (h2 := l44 h0).
 apply t30. refine (subset _z i28 i56 h1 _) ; finalize. exact h2.
Qed.
Lemma t31 : p47 -> p48 -> p46.
Proof.
 intros h0 h1.
 refine (add _c4 r18 i37 i38 i36 h0 h1 _) ; finalize.
Qed.
Lemma l41 : s1 -> p46 (* BND(c4 + z * (c5 + z * (c6 + z * (c7 + z * (c8 + z * c9)))), [-0.251573, -0.125]) *).
Proof.
 intros h0.
 assert (h1 := l42 h0).
 assert (h2 := l43 h0).
 apply t31. exact h1. exact h2.
Qed.
Definition f86 := Float2 (-1231328454439806169880325014263599671675151080730782826217423314570532350207799947598130798532010269949615821830767) (-386).
Definition i57 := makepairF f86 f61.
Notation p67 := (BND _z i57). (* BND(z, [-0.0078126, 0.125]) *)
Lemma t32 : p67 -> p46 -> p45.
Proof.
 intros h0 h1.
 refine (mul_on _z r16 i57 i36 i35 h0 h1 _) ; finalize.
Qed.
Lemma l40 : s1 -> p45 (* BND(z * (c4 + z * (c5 + z * (c6 + z * (c7 + z * (c8 + z * c9))))), [-0.0625, 0.00196544]) *).
Proof.
 intros h0.
 assert (h1 := l36 h0).
 assert (h2 := l41 h0).
 apply t32. refine (subset _z i28 i57 h1 _) ; finalize. exact h2.
Qed.
Definition f87 := Float2 (5) (-4).
Definition i58 := makepairF f87 f56.
Notation p68 := (BND _c3 i58). (* BND(c3, [0.3125, 0.333333]) *)
Lemma t33 : p68 -> p45 -> p43.
Proof.
 intros h0 h1.
 refine (add _c3 r15 i58 i35 i33 h0 h1 _) ; finalize.
Qed.
Lemma l38 : s1 -> p43 (* BND(Wz, [0.25, 0.335299]) *).
Proof.
 intros h0.
 assert (h1 := l39 h0).
 assert (h2 := l40 h0).
 apply t33. refine (subset _c3 i34 i58 h1 _) ; finalize. exact h2.
Qed.
Lemma t34 : p36 -> p43 -> p35.
Proof.
 intros h0 h1.
 refine (mul_op r153 _Wz i26 i33 i25 h0 h1 _) ; finalize.
Qed.
Lemma l33 : s1 -> p35 (* BND((1 + dl) * z * z * Wz, [-2.04655e-05, 2.04655e-05]) *).
Proof.
 intros h0.
 assert (h1 := l34 h0).
 assert (h2 := l38 h0).
 apply t34. exact h1. exact h2.
Qed.
Definition i59 := makepairF f15 f15.
Notation p69 := (REL r83 r152 i59). (* REL(Tz / zh, (1 + dl) * z * z * Wz, [0, 0]) *)
Notation p70 := (r83 = r152). (* EQL(Tz / zh, (1 + dl) * z * z * Wz) *)
Lemma t35 : p13 -> p70.
Proof.
 intros h0.
 refine (b5 h0) ; finalize.
Qed.
Lemma l58 : s1 -> p70 (* EQL(Tz / zh, (1 + dl) * z * z * Wz) *).
Proof.
 intros h0.
 assert (h1 := l6 h0).
 apply t35. exact h1.
Qed.
Notation p71 := (REL r152 r152 i59). (* REL((1 + dl) * z * z * Wz, (1 + dl) * z * z * Wz, [0, 0]) *)
Lemma t36 : p71.
Proof.
 refine (rel_refl r152 i59 _) ; finalize.
Qed.
Lemma l59 : s1 -> p71 (* REL((1 + dl) * z * z * Wz, (1 + dl) * z * z * Wz, [0, 0]) *).
Proof.
 intros h0.
 apply t36.
Qed.
Lemma t37 : p70 -> p71 -> p69.
Proof.
 intros h0 h1.
 refine (rel_rewrite_1 r83 r152 r152 i59 h0 h1) ; finalize.
Qed.
Lemma l57 : s1 -> p69 (* REL(Tz / zh, (1 + dl) * z * z * Wz, [0, 0]) *).
Proof.
 intros h0.
 assert (h1 := l58 h0).
 assert (h2 := l59 h0).
 apply t37. exact h1. exact h2.
Qed.
Lemma t38 : p35 -> p69 -> p34.
Proof.
 intros h0 h1.
 refine (bnd_of_bnd_rel_o r83 r152 i25 i59 i25 h0 h1 _) ; finalize.
Qed.
Lemma l32 : s1 -> p34 (* BND(Tz / zh, [-2.04655e-05, 2.04655e-05]) *).
Proof.
 intros h0.
 assert (h1 := l33 h0).
 assert (h2 := l57 h0).
 apply t38. exact h1. exact h2.
Qed.
Definition i60 := makepairF f39 f53.
Notation p72 := (BND r83 i60). (* BND(Tz / zh, [-2.04655e-05, 0.25]) *)
Lemma t39 : p23 -> p72 -> p22.
Proof.
 intros h0 h1.
 refine (add r78 r83 i14 i60 i13 h0 h1 _) ; finalize.
Qed.
Lemma l22 : s1 -> p22 (* BND(1 + dl - zh * (1 + dl) * (1 + dl) / 2 + Tz / zh, [0.996073, 1.5]) *).
Proof.
 intros h0.
 assert (h1 := l23 h0).
 assert (h2 := l32 h0).
 apply t39. exact h1. refine (subset r83 i25 i60 h2 _) ; finalize.
Qed.
Definition f88 := Float2 (-3065388053492553324629646338381417548261431202036595688742214084570172470877953496927954114341982113) (-400).
Definition f89 := Float2 (1532694026746276662314823169190708774130715601018297844371107042285086235438976748463977057170991057) (-399).
Definition i61 := makepairF f88 f89.
Notation p73 := (BND r84 i61). (* BND(al * (Tz / zh), [-1.1871e-21, 1.1871e-21]) *)
Lemma l61 : s1 -> p6 (* BND(al, [-5.80048e-17, 5.80048e-17]) *).
Proof.
 intros h0.
 assert (h1 := l13 h0).
 exact (proj2 h1).
Qed.
Definition f90 := Float2 (-2933605015678854770486689579908945391981033225126611201188810488411080944092546150331051414099242695) (-346).
Definition i62 := makepairF f90 f40.
Notation p74 := (BND r83 i62). (* BND(Tz / zh, [-2.04655e-05, 2.04655e-05]) *)
Lemma t40 : p6 -> p74 -> p73.
Proof.
 intros h0 h1.
 refine (mul_oo _al r83 i4 i62 i61 h0 h1 _) ; finalize.
Qed.
Lemma l60 : s1 -> p73 (* BND(al * (Tz / zh), [-1.1871e-21, 1.1871e-21]) *).
Proof.
 intros h0.
 assert (h1 := l61 h0).
 assert (h2 := l32 h0).
 apply t40. exact h1. refine (subset r83 i25 i62 h2 _) ; finalize.
Qed.
Definition i63 := makepairF f88 f37.
Notation p75 := (BND r84 i63). (* BND(al * (Tz / zh), [-1.1871e-21, 0.5]) *)
Lemma t41 : p22 -> p75 -> p21.
Proof.
 intros h0 h1.
 refine (add r77 r84 i13 i63 i12 h0 h1 _) ; finalize.
Qed.
Lemma l21 : s1 -> p21 (* BND(1 + dl - zh * (1 + dl) * (1 + dl) / 2 + Tz / zh + al * (Tz / zh), [0.996073, 2]) *).
Proof.
 intros h0.
 assert (h1 := l22 h0).
 assert (h2 := l60 h0).
 apply t41. exact h1. refine (subset r84 i61 i63 h2 _) ; finalize.
Qed.
Notation p76 := (REL r75 r76 i59). (* REL(L / zh, 1 + dl - zh * (1 + dl) * (1 + dl) / 2 + Tz / zh + al * (Tz / zh), [0, 0]) *)
Notation p77 := (r75 = r76). (* EQL(L / zh, 1 + dl - zh * (1 + dl) * (1 + dl) / 2 + Tz / zh + al * (Tz / zh)) *)
Lemma t42 : p13 -> p77.
Proof.
 intros h0.
 refine (b2 h0) ; finalize.
Qed.
Lemma l63 : s1 -> p77 (* EQL(L / zh, 1 + dl - zh * (1 + dl) * (1 + dl) / 2 + Tz / zh + al * (Tz / zh)) *).
Proof.
 intros h0.
 assert (h1 := l6 h0).
 apply t42. exact h1.
Qed.
Notation p78 := (REL r76 r76 i59). (* REL(1 + dl - zh * (1 + dl) * (1 + dl) / 2 + Tz / zh + al * (Tz / zh), 1 + dl - zh * (1 + dl) * (1 + dl) / 2 + Tz / zh + al * (Tz / zh), [0, 0]) *)
Lemma t43 : p78.
Proof.
 refine (rel_refl r76 i59 _) ; finalize.
Qed.
Lemma l64 : s1 -> p78 (* REL(1 + dl - zh * (1 + dl) * (1 + dl) / 2 + Tz / zh + al * (Tz / zh), 1 + dl - zh * (1 + dl) * (1 + dl) / 2 + Tz / zh + al * (Tz / zh), [0, 0]) *).
Proof.
 intros h0.
 apply t43.
Qed.
Lemma t44 : p77 -> p78 -> p76.
Proof.
 intros h0 h1.
 refine (rel_rewrite_1 r75 r76 r76 i59 h0 h1) ; finalize.
Qed.
Lemma l62 : s1 -> p76 (* REL(L / zh, 1 + dl - zh * (1 + dl) * (1 + dl) / 2 + Tz / zh + al * (Tz / zh), [0, 0]) *).
Proof.
 intros h0.
 assert (h1 := l63 h0).
 assert (h2 := l64 h0).
 apply t44. exact h1. exact h2.
Qed.
Lemma t45 : p21 -> p76 -> p20.
Proof.
 intros h0 h1.
 refine (bnd_of_bnd_rel_p r75 r76 i12 i59 i12 h0 h1 _) ; finalize.
Qed.
Lemma l20 : s1 -> p20 (* BND(L / zh, [0.996073, 2]) *).
Proof.
 intros h0.
 assert (h1 := l21 h0).
 assert (h2 := l62 h0).
 apply t45. exact h1. exact h2.
Qed.
Definition f91 := Float2 (-1) (-1).
Definition f92 := Float2 (-1) (-64).
Definition i64 := makepairF f91 f92.
Notation p79 := (BND _zh i64). (* BND(zh, [-0.5, -5.42101e-20]) *)
Definition i65 := makepairF f35 f15.
Notation p80 := (BND _zh i65). (* BND(zh, [-0.0078126, 0]) *)
Lemma l67 : p10 -> s1 -> p10 (* BND(zh, [-inf, 0]) *).
Proof.
 intros h0 h1.
 assert (h2 := h0).
 exact (h2).
Qed.
Lemma l66 : p10 -> s1 -> p80 (* BND(zh, [-0.0078126, 0]) *).
Proof.
 intros h0 h1.
 assert (h2 := l67 h0 h1).
 assert (h3 := l30 h1).
 apply intersect_hb with (1 := h2) (2 := h3). finalize.
Qed.
Definition i66 := makepairF f91 f15.
Notation p81 := (BND _zh i66). (* BND(zh, [-0.5, 0]) *)
Lemma t46 : p81 -> p15 -> p79.
Proof.
 intros h0 h1.
 refine (bnd_of_bnd_abs_n _zh i66 i9 i64 h0 h1 _) ; finalize.
Qed.
Lemma l65 : p10 -> s1 -> p79 (* BND(zh, [-0.5, -5.42101e-20]) *).
Proof.
 intros h0 h1.
 assert (h2 := l66 h0 h1).
 assert (h3 := l7 h1).
 apply t46. refine (subset _zh i65 i66 h2 _) ; finalize. refine (abs_subset _zh i1 i9 h3 _) ; finalize.
Qed.
Definition i67 := makepairF f37 f23.
Notation p82 := (BND r75 i67). (* BND(L / zh, [0.5, 2]) *)
Lemma t47 : p82 -> p79 -> p19.
Proof.
 intros h0 h1.
 refine (mul_pn r75 _zh i67 i64 i11 h0 h1 _) ; finalize.
Qed.
Lemma l19 : p10 -> s1 -> p19 (* BND(L / zh * zh, [-1, -2.71051e-20]) *).
Proof.
 intros h0 h1.
 assert (h2 := l20 h1).
 assert (h3 := l65 h0 h1).
 apply t47. refine (subset r75 i12 i67 h2 _) ; finalize. exact h3.
Qed.
Lemma t48 : p13 -> p19 -> p18.
Proof.
 intros h0 h1.
 refine (div_xilu _L _ i11 h0 h1) ; finalize.
Qed.
Lemma l18 : p10 -> s1 -> p18 (* BND(L, [-1, -2.71051e-20]) *).
Proof.
 intros h0 h1.
 assert (h2 := l6 h1).
 assert (h3 := l19 h0 h1).
 apply t48. exact h2. exact h3.
Qed.
Lemma t49 : p18 -> p17.
Proof.
 intros h0.
 refine (abs_of_bnd_n _L i11 i10 h0 _) ; finalize.
Qed.
Lemma l17 : p10 -> s1 -> p17 (* ABS(L, [2.71051e-20, 1]) *).
Proof.
 intros h0 h1.
 assert (h2 := l18 h0 h1).
 apply t49. exact h2.
Qed.
Lemma t50 : p17 -> p16.
Proof.
 intros h0.
 refine (nzr_of_abs _L i10 h0 _) ; finalize.
Qed.
Lemma l16 : p10 -> s1 -> p16 (* NZR(L) *).
Proof.
 intros h0 h1.
 assert (h2 := l17 h0 h1).
 apply t50. exact h2.
Qed.
Lemma t51 : p13 -> p16 -> p12.
Proof.
 intros h0 h1.
 refine (b1 h0 h1) ; finalize.
Qed.
Lemma l5 : p10 -> s1 -> p12 (* EQL((P - L) / L, (P - L) / zh / (L / zh)) *).
Proof.
 intros h0 h1.
 assert (h2 := l6 h1).
 assert (h3 := l16 h0 h1).
 apply t51. exact h2. exact h3.
Qed.
Notation p83 := (BND r73 i8). (* BND((P - L) / zh / (L / zh), [-2.85783e-20, 2.85783e-20]) *)
Definition f93 := Float2 (-1355955906182072840120564364260305132079911843213836005049088871130286904934940523279426844117699165192143998899691120207) (-464).
Definition f94 := Float2 (1355955906182072840120564364260305132079911843213836005049088871130286904934940523279426844117699165192143998899691120207) (-464).
Definition i68 := makepairF f93 f94.
Notation p84 := (BND r74 i68). (* BND((P - L) / zh, [-2.84661e-20, 2.84661e-20]) *)
Definition i69 := makepairF f15 f94.
Notation p85 := (ABS r74 i69). (* ABS((P - L) / zh, [0, 2.84661e-20]) *)
Notation p86 := (r74 = r85). (* EQL((P - L) / zh, zl * dl / 2 + (T - Tz) / zh + zh * zh * W * et - zl * ec + (t - c) / zh * eu - al * (Tz / zh) + (z + B) / zh * d1 + (P1 + u) / zh * d2) *)
Lemma t52 : p13 -> p86.
Proof.
 intros h0.
 refine (b3 h0) ; finalize.
Qed.
Lemma l71 : s1 -> p86 (* EQL((P - L) / zh, zl * dl / 2 + (T - Tz) / zh + zh * zh * W * et - zl * ec + (t - c) / zh * eu - al * (Tz / zh) + (z + B) / zh * d1 + (P1 + u) / zh * d2) *).
Proof.
 intros h0.
 assert (h1 := l6 h0).
 apply t52. exact h1.
Qed.
Notation p87 := (ABS r85 i69). (* ABS(zl * dl / 2 + (T - Tz) / zh + zh * zh * W * et - zl * ec + (t - c) / zh * eu - al * (Tz / zh) + (z + B) / zh * d1 + (P1 + u) / zh * d2, [0, 2.84661e-20]) *)
Definition f95 := Float2 (1355955906180893957741139614361408233253749859395863292280728619217868797877125846505295428146333765315003533350951371723) (-464).
Definition i70 := makepairF f15 f95.
Notation p88 := (ABS r86 i70). (* ABS(zl * dl / 2 + (T - Tz) / zh + zh * zh * W * et - zl * ec + (t - c) / zh * eu - al * (Tz / zh) + (z + B) / zh * d1, [0, 2.84661e-20]) *)
Definition f96 := Float2 (338988976544776812639615963116530350395802888593251415795723553377992589396244484865891097384022193010972645097308798171) (-462).
Definition i71 := makepairF f15 f96.
Notation p89 := (ABS r87 i71). (* ABS(zl * dl / 2 + (T - Tz) / zh + zh * zh * W * et - zl * ec + (t - c) / zh * eu - al * (Tz / zh), [0, 2.84661e-20]) *)
Definition f97 := Float2 (1299409477269723434520692743298040696850574789246600169632613534060442736794097559145628863426816768333865077519983336973) (-464).
Definition i72 := makepairF f15 f97.
Notation p90 := (ABS r88 i72). (* ABS(zl * dl / 2 + (T - Tz) / zh + zh * zh * W * et - zl * ec + (t - c) / zh * eu, [0, 2.7279e-20]) *)
Definition f98 := Float2 (595589277697280863239213624393258755342435821865759171630147902254601192279675958749554463522911735413115717488372978981) (-463).
Definition i73 := makepairF f15 f98.
Notation p91 := (ABS r89 i73). (* ABS(zl * dl / 2 + (T - Tz) / zh + zh * zh * W * et - zl * ec, [0, 2.50068e-20]) *)
Definition f99 := Float2 (595589277697278569711240852037074229172922012318951662222962702112123456306995434682525762224171059851266369882876815569) (-463).
Definition i74 := makepairF f15 f99.
Notation p92 := (ABS r90 i74). (* ABS(zl * dl / 2 + (T - Tz) / zh + zh * zh * W * et, [0, 2.50068e-20]) *)
Definition f100 := Float2 (650662360786601881117750671604875650493042674787925748528304880316731834859196820655481943889818201986334059015479182265) (-465).
Definition i75 := makepairF f15 f100.
Notation p93 := (ABS r91 i75). (* ABS(zl * dl / 2 + (T - Tz) / zh, [0, 6.8298e-21]) *)
Definition f101 := Float2 (573381993193089046131542378452386701877351796300035619433993170131016757175324685168890462336901374040853) (-462).
Definition i76 := makepairF f15 f101.
Notation p94 := (ABS r92 i76). (* ABS(zl * dl / 2, [0, 4.81489e-35]) *)
Definition f102 := Float2 (573381993193089046131542378452386701877351796300035619433993170131016757175324685168890462336901374040853) (-461).
Definition i77 := makepairF f15 f102.
Notation p95 := (ABS r93 i77). (* ABS(zl * dl, [0, 9.62977e-35]) *)
Definition f103 := Float2 (573381993193089046131542378452386701877351796300035619433993170131016757175324685168890462336901374040853) (-408).
Definition i78 := makepairF f15 f103.
Notation p96 := (ABS _zl i78). (* ABS(zl, [0, 8.67373e-19]) *)
Definition i79 := makepairF f15 f4.
Notation p97 := (ABS _dl i79). (* ABS(dl, [0, 1.11022e-16]) *)
Lemma t53 : p2 -> p97.
Proof.
 intros h0.
 refine (abs_of_bnd_o _dl i2 i79 h0 _) ; finalize.
Qed.
Lemma l82 : s1 -> p97 (* ABS(dl, [0, 1.11022e-16]) *).
Proof.
 intros h0.
 assert (h1 := l26 h0).
 apply t53. exact h1.
Qed.
Definition f104 := Float2 (573381993193089046131542378452386701877351796300035619433993170131016757175324685168890462336901374040853) (-355).
Definition i80 := makepairF f1 f104.
Notation p98 := (ABS _zh i80). (* ABS(zh, [5.42101e-20, 0.0078126]) *)
Lemma t54 : p98 -> p97 -> p96.
Proof.
 intros h0 h1.
 refine (mul_aa _zh _dl i80 i79 i78 h0 h1 _) ; finalize.
Qed.
Lemma l81 : s1 -> p96 (* ABS(zl, [0, 8.67373e-19]) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 assert (h2 := l82 h0).
 apply t54. refine (abs_subset _zh i1 i80 h1 _) ; finalize. exact h2.
Qed.
Lemma t55 : p96 -> p97 -> p95.
Proof.
 intros h0 h1.
 refine (mul_aa _zl _dl i78 i79 i77 h0 h1 _) ; finalize.
Qed.
Lemma l80 : s1 -> p95 (* ABS(zl * dl, [0, 9.62977e-35]) *).
Proof.
 intros h0.
 assert (h1 := l81 h0).
 assert (h2 := l82 h0).
 apply t55. exact h1. exact h2.
Qed.
Notation p99 := (ABS r10 i23). (* ABS(2, [2, 2]) *)
Lemma t56 : p32 -> p99.
Proof.
 intros h0.
 refine (abs_of_bnd_p r10 i23 i23 h0 _) ; finalize.
Qed.
Lemma l83 : s1 -> p99 (* ABS(2, [2, 2]) *).
Proof.
 intros h0.
 assert (h1 := l31 h0).
 apply t56. exact h1.
Qed.
Lemma t57 : p95 -> p99 -> p94.
Proof.
 intros h0 h1.
 refine (div_aa r93 r10 i77 i23 i76 h0 h1 _) ; finalize.
Qed.
Lemma l79 : s1 -> p94 (* ABS(zl * dl / 2, [0, 4.81489e-35]) *).
Proof.
 intros h0.
 assert (h1 := l80 h0).
 assert (h2 := l83 h0).
 apply t57. exact h1. exact h2.
Qed.
Definition f105 := Float2 (650662360786597294061805126892506598154015055694310729713934480031776362913835772521424541292336850862635363804486855441) (-465).
Definition i81 := makepairF f15 f105.
Notation p100 := (ABS r94 i81). (* ABS((T - Tz) / zh, [0, 6.8298e-21]) *)
Notation p101 := (r94 = r105). (* EQL((T - Tz) / zh, -(dl * ((z * z + z * zh + zh * zh) * Wz + zh * zh * zh * D))) *)
Lemma t58 : p13 -> p101.
Proof.
 intros h0.
 refine (b4 h0) ; finalize.
Qed.
Lemma l85 : s1 -> p101 (* EQL((T - Tz) / zh, -(dl * ((z * z + z * zh + zh * zh) * Wz + zh * zh * zh * D))) *).
Proof.
 intros h0.
 assert (h1 := l6 h0).
 apply t58. exact h1.
Qed.
Notation p102 := (ABS r105 i81). (* ABS(-(dl * ((z * z + z * zh + zh * zh) * Wz + zh * zh * zh * D)), [0, 6.8298e-21]) *)
Notation p103 := (ABS r106 i81). (* ABS(dl * ((z * z + z * zh + zh * zh) * Wz + zh * zh * zh * D), [0, 6.8298e-21]) *)
Definition f106 := Float2 (650662360786597294061805126892506598154015055694310729713934480031776362913835772521424541292336850862635363804486855441) (-412).
Definition i82 := makepairF f15 f106.
Notation p104 := (ABS r107 i82). (* ABS((z * z + z * zh + zh * zh) * Wz + zh * zh * zh * D, [0, 6.15173e-05]) *)
Definition f107 := Float2 (649385531250942221669251306229009057865880788893018378163806996727661769955517151434816854552265129604296675411263531839) (-412).
Definition i83 := makepairF f15 f107.
Notation p105 := (ABS r108 i83). (* ABS((z * z + z * zh + zh * zh) * Wz, [0, 6.13966e-05]) *)
Definition f108 := Float2 (484184247020036947731794945280751948889076838768776703131785220559245045701248258833589447503655103168591563229728179631) (-410).
Definition i84 := makepairF f15 f108.
Notation p106 := (ABS r109 i84). (* ABS(z * z + z * zh + zh * zh, [0, 0.00018311]) *)
Definition f109 := Float2 (1291157992053431932291786414407247558412641830378182078014708931796392609912096902295491006632294688262914824569810625671) (-412).
Definition i85 := makepairF f15 f109.
Notation p107 := (ABS r110 i85). (* ABS(z * z + z * zh, [0, 0.000122073]) *)
Definition f110 := Float2 (645578996026716001982726487366247612352368531327395790110298680977272550778960113807319949522902798243885379368297735513) (-412).
Definition i86 := makepairF f15 f110.
Notation p108 := (ABS r9 i86). (* ABS(z * z, [0, 6.10367e-05]) *)
Definition i87 := makepairF f15 f46.
Notation p109 := (ABS _z i87). (* ABS(z, [0, 0.0078126]) *)
Definition i88 := makepairF f15 f48.
Notation p110 := (ABS _zl i88). (* ABS(zl, [0, 8.67373e-19]) *)
Lemma t59 : p14 -> p110 -> p109.
Proof.
 intros h0 h1.
 refine (add_aa_o _zh _zl i1 i88 i87 h0 h1 _) ; finalize.
Qed.
Lemma l93 : s1 -> p109 (* ABS(z, [0, 0.0078126]) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 assert (h2 := l81 h0).
 apply t59. exact h1. refine (abs_subset _zl i78 i88 h2 _) ; finalize.
Qed.
Lemma t60 : p109 -> p109 -> p108.
Proof.
 intros h0 h1.
 refine (mul_aa _z _z i87 i87 i86 h0 h1 _) ; finalize.
Qed.
Lemma l92 : s1 -> p108 (* ABS(z * z, [0, 6.10367e-05]) *).
Proof.
 intros h0.
 assert (h1 := l93 h0).
 apply t60. exact h1. exact h1.
Qed.
Definition f111 := Float2 (322789498013357965154529963520499973030136649525393143952205125409560029566568394244085528554695945009514722600756445079) (-411).
Definition i89 := makepairF f15 f111.
Notation p111 := (ABS r111 i89). (* ABS(z * zh, [0, 6.10367e-05]) *)
Lemma t61 : p109 -> p14 -> p111.
Proof.
 intros h0 h1.
 refine (mul_aa _z _zh i87 i1 i89 h0 h1 _) ; finalize.
Qed.
Lemma l94 : s1 -> p111 (* ABS(z * zh, [0, 6.10367e-05]) *).
Proof.
 intros h0.
 assert (h1 := l93 h0).
 assert (h2 := l7 h0).
 apply t61. exact h1. exact h2.
Qed.
Lemma t62 : p108 -> p111 -> p107.
Proof.
 intros h0 h1.
 refine (add_aa_o r9 r111 i86 i89 i85 h0 h1 _) ; finalize.
Qed.
Lemma l91 : s1 -> p107 (* ABS(z * z + z * zh, [0, 0.000122073]) *).
Proof.
 intros h0.
 assert (h1 := l92 h0).
 assert (h2 := l94 h0).
 apply t62. exact h1. exact h2.
Qed.
Definition f112 := Float2 (1) (-128).
Definition f113 := Float2 (1291157992053431717270786733431520474287331049393849469024863900881175145785792266077733566764651448822902856698204185705) (-413).
Definition i90 := makepairF f112 f113.
Notation p112 := (ABS r42 i90). (* ABS(zh * zh, [2.93874e-39, 6.10367e-05]) *)
Lemma t63 : p14 -> p14 -> p112.
Proof.
 intros h0 h1.
 refine (mul_aa _zh _zh i1 i1 i90 h0 h1 _) ; finalize.
Qed.
Lemma l95 : s1 -> p112 (* ABS(zh * zh, [2.93874e-39, 6.10367e-05]) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 apply t63. exact h1. exact h1.
Qed.
Definition f114 := Float2 (645578996026715858635393366715760237143665524696924734512431950440587572892896133038866783382325724411451428349102092853) (-412).
Definition i91 := makepairF f112 f114.
Notation p113 := (ABS r42 i91). (* ABS(zh * zh, [2.93874e-39, 6.10367e-05]) *)
Lemma t64 : p107 -> p113 -> p106.
Proof.
 intros h0 h1.
 refine (add_aa_o r110 r42 i85 i91 i84 h0 h1 _) ; finalize.
Qed.
Lemma l90 : s1 -> p106 (* ABS(z * z + z * zh + zh * zh, [0, 0.00018311]) *).
Proof.
 intros h0.
 assert (h1 := l91 h0).
 assert (h2 := l95 h0).
 apply t64. exact h1. refine (abs_subset r42 i90 i91 h2 _) ; finalize.
Qed.
Definition f115 := Float2 (1731650419468060411789076357525713239779378146175949266818954223465154467940866826162957035465251479907210174966449165291) (-401).
Definition i92 := makepairF f53 f115.
Notation p114 := (ABS _Wz i92). (* ABS(Wz, [0.25, 0.335299]) *)
Notation p115 := (ABS _c3 i34). (* ABS(c3, [0.328125, 0.333333]) *)
Lemma t65 : p44 -> p115.
Proof.
 intros h0.
 refine (abs_of_bnd_p _c3 i34 i34 h0 _) ; finalize.
Qed.
Lemma l97 : s1 -> p115 (* ABS(c3, [0.328125, 0.333333]) *).
Proof.
 intros h0.
 assert (h1 := l39 h0).
 apply t65. exact h1.
Qed.
Definition f116 := Float2 (10150500743454780914239242443351640677111588543422791455389201116436208995841004198313303632026595200714439906521109483) (-401).
Definition i93 := makepairF f15 f116.
Notation p116 := (ABS r15 i93). (* ABS(z * (c4 + z * (c5 + z * (c6 + z * (c7 + z * (c8 + z * c9))))), [0, 0.00196544]) *)
Definition f117 := Float2 (40601483274833201284252676595839835532929460839690236986858727436478663677626242107025375228231611677329193084327087505) (-396).
Definition i94 := makepairF f61 f117.
Notation p117 := (ABS r16 i94). (* ABS(c4 + z * (c5 + z * (c6 + z * (c7 + z * (c8 + z * c9)))), [0.125, 0.251573]) *)
Definition f118 := Float2 (4503599627370541) (-54).
Definition i95 := makepairF f53 f118.
Notation p118 := (ABS _c4 i95). (* ABS(c4, [0.25, 0.25]) *)
Lemma t66 : p47 -> p118.
Proof.
 intros h0.
 refine (abs_of_bnd_n _c4 i37 i95 h0 _) ; finalize.
Qed.
Lemma l100 : s1 -> p118 (* ABS(c4, [0.25, 0.25]) *).
Proof.
 intros h0.
 assert (h1 := l42 h0).
 apply t66. exact h1.
Qed.
Definition f119 := Float2 (253828929724851416825347528534874656917305506763557702690172753614762585574924958400354154259289503194417132972068241) (-396).
Definition i96 := makepairF f15 f119.
Notation p119 := (ABS r18 i96). (* ABS(z * (c5 + z * (c6 + z * (c7 + z * (c8 + z * c9)))), [0, 0.00157276]) *)
Definition f120 := Float2 (1015302723024550840327945077846177309434896028426343951192830553821674840217894004484860396470708642821851068406166761) (-391).
Definition i97 := makepairF f61 f120.
Notation p120 := (ABS r19 i97). (* ABS(c5 + z * (c6 + z * (c7 + z * (c8 + z * c9))), [0.125, 0.201311]) *)
Notation p121 := (ABS _c5 i40). (* ABS(c5, [0.1875, 0.2]) *)
Lemma t67 : p50 -> p121.
Proof.
 intros h0.
 refine (abs_of_bnd_p _c5 i40 i40 h0 _) ; finalize.
Qed.
Lemma l103 : s1 -> p121 (* ABS(c5, [0.1875, 0.2]) *).
Proof.
 intros h0.
 assert (h1 := l45 h0).
 apply t67. exact h1.
Qed.
Definition f121 := Float2 (6611364384606172138079566203409556579647184272924084093242788309084368708999546445188922112702133895958218683184361) (-391).
Definition i98 := makepairF f15 f121.
Notation p122 := (ABS r21 i98). (* ABS(z * (c6 + z * (c7 + z * (c8 + z * c9))), [0, 0.00131088]) *)
Definition f122 := Float2 (423121904654415393343488070921301579156748080349041236341355006314248591002360914641109071231098207382326079356642417) (-390).
Definition i99 := makepairF f61 f122.
Notation p123 := (ABS r22 i99). (* ABS(c6 + z * (c7 + z * (c8 + z * c9)), [0.125, 0.16779]) *)
Definition f123 := Float2 (5) (-5).
Definition f124 := Float2 (750599936424355) (-52).
Definition i100 := makepairF f123 f124.
Notation p124 := (ABS _c6 i100). (* ABS(c6, [0.15625, 0.166667]) *)
Lemma t68 : p53 -> p124.
Proof.
 intros h0.
 refine (abs_of_bnd_n _c6 i43 i100 h0 _) ; finalize.
Qed.
Lemma l106 : s1 -> p124 (* ABS(c6, [0.15625, 0.166667]) *).
Proof.
 intros h0.
 assert (h1 := l48 h0).
 apply t68. exact h1.
Qed.
Definition f125 := Float2 (2833839383054588060535869448933644719674209828709488127012184072597443061201177249298236218445457288355322368861297) (-390).
Definition i101 := makepairF f15 f125.
Notation p125 := (ABS r24 i101). (* ABS(z * (c7 + z * (c8 + z * c9)), [0, 0.00112377]) *)
Definition f126 := Float2 (11607257540095078190273133484917987056945375985893274769176232290297037619706291135435068598403742000010864397719753231) (-395).
Definition i102 := makepairF f61 f126.
Notation p126 := (ABS r25 i102). (* ABS(c7 + z * (c8 + z * c9), [0.125, 0.143841]) *)
Notation p127 := (ABS _c7 i46). (* ABS(c7, [0.140625, 0.142857]) *)
Lemma t69 : p56 -> p127.
Proof.
 intros h0.
 refine (abs_of_bnd_p _c7 i46 i46 h0 _) ; finalize.
Qed.
Lemma l109 : s1 -> p127 (* ABS(c7, [0.140625, 0.142857]) *).
Proof.
 intros h0.
 assert (h1 := l51 h0).
 apply t69. exact h1.
Qed.
Definition f127 := Float2 (79362737759696399796884475980701928587052228665133608195079778717842698101302695825650801416983363783642214233068047) (-395).
Definition i103 := makepairF f15 f127.
Notation p128 := (ABS r27 i103). (* ABS(z * (c8 + z * c9), [0, 0.000983486]) *)
Definition f128 := Float2 (317446887718622765572003079042097136066022967979674258261097573161904550449685957192610269399301348342426858906741439) (-390).
Definition i104 := makepairF f79 f128.
Notation p129 := (ABS r28 i104). (* ABS(c8 + z * c9, [0.0625, 0.125885]) *)
Definition f129 := Float2 (4503984727172023) (-55).
Definition i105 := makepairF f61 f129.
Notation p130 := (ABS _c8 i105). (* ABS(c8, [0.125, 0.125011]) *)
Lemma t70 : p59 -> p130.
Proof.
 intros h0.
 refine (abs_of_bnd_n _c8 i49 i105 h0 _) ; finalize.
Qed.
Lemma l112 : s1 -> p130 (* ABS(c8, [0.125, 0.125011]) *).
Proof.
 intros h0.
 assert (h1 := l54 h0).
 apply t70. exact h1.
Qed.
Definition f130 := Float2 (2203884233226812680419810242814486058502434926283568768660057532233288171020621803442198966157023304155408155830975) (-390).
Definition i106 := makepairF f15 f130.
Notation p131 := (ABS r30 i106). (* ABS(z * c9, [0, 0.000873958]) *)
Notation p132 := (ABS _c9 i51). (* ABS(c9, [0.0625, 0.111865]) *)
Lemma t71 : p61 -> p132.
Proof.
 intros h0.
 refine (abs_of_bnd_p _c9 i51 i51 h0 _) ; finalize.
Qed.
Lemma l114 : s1 -> p132 (* ABS(c9, [0.0625, 0.111865]) *).
Proof.
 intros h0.
 assert (h1 := l56 h0).
 apply t71. exact h1.
Qed.
Definition f131 := Float2 (9850627635518449359042600114108797373401208645846262609739386516564258801662399580785046388256082159596926574646133) (-389).
Definition i107 := makepairF f15 f131.
Notation p133 := (ABS _z i107). (* ABS(z, [0, 0.0078126]) *)
Lemma t72 : p133 -> p132 -> p131.
Proof.
 intros h0 h1.
 refine (mul_aa _z _c9 i107 i51 i106 h0 h1 _) ; finalize.
Qed.
Lemma l113 : s1 -> p131 (* ABS(z * c9, [0, 0.000873958]) *).
Proof.
 intros h0.
 assert (h1 := l93 h0).
 assert (h2 := l114 h0).
 apply t72. refine (abs_subset _z i87 i107 h1 _) ; finalize. exact h2.
Qed.
Lemma t73 : p130 -> p131 -> p129.
Proof.
 intros h0 h1.
 refine (add_aa_p _c8 r30 i105 i106 i104 h0 h1 _) ; finalize.
Qed.
Lemma l111 : s1 -> p129 (* ABS(c8 + z * c9, [0.0625, 0.125885]) *).
Proof.
 intros h0.
 assert (h1 := l112 h0).
 assert (h2 := l113 h0).
 apply t73. exact h1. exact h2.
Qed.
Definition f132 := Float2 (157610042168295189744681601825740757974419338333540201755830184265028140826598393292560742212097314553550825194338121) (-393).
Definition i108 := makepairF f15 f132.
Notation p134 := (ABS _z i108). (* ABS(z, [0, 0.0078126]) *)
Lemma t74 : p134 -> p129 -> p128.
Proof.
 intros h0 h1.
 refine (mul_aa _z r28 i108 i104 i103 h0 h1 _) ; finalize.
Qed.
Lemma l110 : s1 -> p128 (* ABS(z * (c8 + z * c9), [0, 0.000983486]) *).
Proof.
 intros h0.
 assert (h1 := l93 h0).
 assert (h2 := l111 h0).
 apply t74. refine (abs_subset _z i87 i108 h1 _) ; finalize. exact h2.
Qed.
Lemma t75 : p127 -> p128 -> p126.
Proof.
 intros h0 h1.
 refine (add_aa_p _c7 r27 i46 i103 i102 h0 h1 _) ; finalize.
Qed.
Lemma l108 : s1 -> p126 (* ABS(c7 + z * (c8 + z * c9), [0.125, 0.143841]) *).
Proof.
 intros h0.
 assert (h1 := l109 h0).
 assert (h2 := l110 h0).
 apply t75. exact h1. exact h2.
Qed.
Lemma t76 : p134 -> p126 -> p125.
Proof.
 intros h0 h1.
 refine (mul_aa _z r25 i108 i102 i101 h0 h1 _) ; finalize.
Qed.
Lemma l107 : s1 -> p125 (* ABS(z * (c7 + z * (c8 + z * c9)), [0, 0.00112377]) *).
Proof.
 intros h0.
 assert (h1 := l93 h0).
 assert (h2 := l108 h0).
 apply t76. refine (abs_subset _z i87 i108 h1 _) ; finalize. exact h2.
Qed.
Lemma t77 : p124 -> p125 -> p123.
Proof.
 intros h0 h1.
 refine (add_aa_p _c6 r24 i100 i101 i99 h0 h1 _) ; finalize.
Qed.
Lemma l105 : s1 -> p123 (* ABS(c6 + z * (c7 + z * (c8 + z * c9)), [0.125, 0.16779]) *).
Proof.
 intros h0.
 assert (h1 := l106 h0).
 assert (h2 := l107 h0).
 apply t77. exact h1. exact h2.
Qed.
Definition f133 := Float2 (2521760674692723035914905629211852127590709413336643228093282948240450253225574292680971875393557032856813203109409927) (-397).
Definition i109 := makepairF f15 f133.
Notation p135 := (ABS _z i109). (* ABS(z, [0, 0.0078126]) *)
Lemma t78 : p135 -> p123 -> p122.
Proof.
 intros h0 h1.
 refine (mul_aa _z r22 i109 i99 i98 h0 h1 _) ; finalize.
Qed.
Lemma l104 : s1 -> p122 (* ABS(z * (c6 + z * (c7 + z * (c8 + z * c9))), [0, 0.00131088]) *).
Proof.
 intros h0.
 assert (h1 := l93 h0).
 assert (h2 := l105 h0).
 apply t78. refine (abs_subset _z i87 i109 h1 _) ; finalize. exact h2.
Qed.
Lemma t79 : p121 -> p122 -> p120.
Proof.
 intros h0 h1.
 refine (add_aa_p _c5 r21 i40 i98 i97 h0 h1 _) ; finalize.
Qed.
Lemma l102 : s1 -> p120 (* ABS(c5 + z * (c6 + z * (c7 + z * (c8 + z * c9))), [0.125, 0.201311]) *).
Proof.
 intros h0.
 assert (h1 := l103 h0).
 assert (h2 := l104 h0).
 apply t79. exact h1. exact h2.
Qed.
Definition i110 := makepairF f15 f34.
Notation p136 := (ABS _z i110). (* ABS(z, [0, 0.0078126]) *)
Lemma t80 : p136 -> p120 -> p119.
Proof.
 intros h0 h1.
 refine (mul_aa _z r19 i110 i97 i96 h0 h1 _) ; finalize.
Qed.
Lemma l101 : s1 -> p119 (* ABS(z * (c5 + z * (c6 + z * (c7 + z * (c8 + z * c9)))), [0, 0.00157276]) *).
Proof.
 intros h0.
 assert (h1 := l93 h0).
 assert (h2 := l102 h0).
 apply t80. refine (abs_subset _z i87 i110 h1 _) ; finalize. exact h2.
Qed.
Lemma t81 : p118 -> p119 -> p117.
Proof.
 intros h0 h1.
 refine (add_aa_p _c4 r18 i95 i96 i94 h0 h1 _) ; finalize.
Qed.
Lemma l99 : s1 -> p117 (* ABS(c4 + z * (c5 + z * (c6 + z * (c7 + z * (c8 + z * c9)))), [0.125, 0.251573]) *).
Proof.
 intros h0.
 assert (h1 := l100 h0).
 assert (h2 := l101 h0).
 apply t81. exact h1. exact h2.
Qed.
Lemma t82 : p136 -> p117 -> p116.
Proof.
 intros h0 h1.
 refine (mul_aa _z r16 i110 i94 i93 h0 h1 _) ; finalize.
Qed.
Lemma l98 : s1 -> p116 (* ABS(z * (c4 + z * (c5 + z * (c6 + z * (c7 + z * (c8 + z * c9))))), [0, 0.00196544]) *).
Proof.
 intros h0.
 assert (h1 := l93 h0).
 assert (h2 := l99 h0).
 apply t82. refine (abs_subset _z i87 i110 h1 _) ; finalize. exact h2.
Qed.
Notation p137 := (ABS _c3 i58). (* ABS(c3, [0.3125, 0.333333]) *)
Lemma t83 : p137 -> p116 -> p114.
Proof.
 intros h0 h1.
 refine (add_aa_p _c3 r15 i58 i93 i92 h0 h1 _) ; finalize.
Qed.
Lemma l96 : s1 -> p114 (* ABS(Wz, [0.25, 0.335299]) *).
Proof.
 intros h0.
 assert (h1 := l97 h0).
 assert (h2 := l98 h0).
 apply t83. refine (abs_subset _c3 i34 i58 h1 _) ; finalize. exact h2.
Qed.
Lemma t84 : p106 -> p114 -> p105.
Proof.
 intros h0 h1.
 refine (mul_aa r109 _Wz i84 i92 i83 h0 h1 _) ; finalize.
Qed.
Lemma l89 : s1 -> p105 (* ABS((z * z + z * zh + zh * zh) * Wz, [0, 6.13966e-05]) *).
Proof.
 intros h0.
 assert (h1 := l90 h0).
 assert (h2 := l96 h0).
 apply t84. exact h1. exact h2.
Qed.
Definition f134 := Float2 (1) (-195).
Definition f135 := Float2 (638414767827536196276910331748770144067133400646175775063741652057296479159310543303843370035860629169344196611661801) (-411).
Definition i111 := makepairF f134 f135.
Notation p138 := (ABS r112 i111). (* ABS(zh * zh * zh * D, [1.99136e-59, 1.20719e-07]) *)
Definition f136 := Float2 (1) (-192).
Definition f137 := Float2 (1260912616089580079293718554200887107177150319561798545212956464003033617995760082244862657963189488634226357280048753) (-410).
Definition i112 := makepairF f136 f137.
Notation p139 := (ABS r50 i112). (* ABS(zh * zh * zh, [1.59309e-58, 4.76855e-07]) *)
Definition f138 := Float2 (80697374503339482329424170839470029642958190587115591814053993805073446611612016629858347922790715551431428543637761607) (-409).
Definition i113 := makepairF f112 f138.
Notation p140 := (ABS r42 i113). (* ABS(zh * zh, [2.93874e-39, 6.10367e-05]) *)
Definition f139 := Float2 (630440168673180688985807316349710330293383108658049738010650290278420737867774172411361477719887650683629285042321471) (-395).
Definition i114 := makepairF f1 f139.
Notation p141 := (ABS _zh i114). (* ABS(zh, [5.42101e-20, 0.0078126]) *)
Lemma t85 : p140 -> p141 -> p139.
Proof.
 intros h0 h1.
 refine (mul_aa r42 _zh i113 i114 i112 h0 h1 _) ; finalize.
Qed.
Lemma l116 : s1 -> p139 (* ABS(zh * zh * zh, [1.59309e-58, 4.76855e-07]) *).
Proof.
 intros h0.
 assert (h1 := l95 h0).
 assert (h2 := l7 h0).
 apply t85. refine (abs_subset r42 i90 i113 h1 _) ; finalize. refine (abs_subset _zh i1 i114 h2 _) ; finalize.
Qed.
Definition f140 := Float2 (2553561013312101935924551291178664736857911569400927179016385059719523773801027127556273191144800548531385459930079353) (-392).
Definition i115 := makepairF f61 f140.
Notation p142 := (ABS _D i115). (* ABS(D, [0.125, 0.253156]) *)
Definition f141 := Float2 (5107122026230098483756212956722245255300886346794749067216773908126773958726048906941663766656730680811542925443822661) (-393).
Definition i116 := makepairF f63 f141.
Notation p143 := (ABS r114 i116). (* ABS(c4 * 1 + c5 * (zh + z) + c6 * (zh * zh + z * zh + z * z) + c7 * (zh * zh * zh + z * zh * zh + z * z * zh + z * z * z) + c8 * (zh * zh * zh * zh + z * zh * zh * zh + z * z * zh * zh + z * z * z * zh + z * z * z * z), [0.1875, 0.253156]) *)
Definition f142 := Float2 (7) (-5).
Definition f143 := Float2 (2553560989626412611322595825499355508692595773835454456357619305432015694677001107207398454789427657460994885764203279) (-392).
Definition i117 := makepairF f142 f143.
Notation p144 := (ABS r115 i117). (* ABS(c4 * 1 + c5 * (zh + z) + c6 * (zh * zh + z * zh + z * z) + c7 * (zh * zh * zh + z * zh * zh + z * z * zh + z * z * z), [0.21875, 0.253156]) *)
Definition f144 := Float2 (15) (-6).
Definition f145 := Float2 (319194780132071428278457849588657462101282546812954896027805105762211870121516526333736638933558087091360148936519651) (-389).
Definition i118 := makepairF f144 f145.
Notation p145 := (ABS r116 i118). (* ABS(c4 * 1 + c5 * (zh + z) + c6 * (zh * zh + z * zh + z * z), [0.234375, 0.253156]) *)
Definition f146 := Float2 (31) (-7).
Definition f147 := Float2 (2553250405003313595322831617186676217894070305166676222631713028661433159641525781738204894712710171477964572304572049) (-392).
Definition i119 := makepairF f146 f147.
Notation p146 := (ABS r117 i119). (* ABS(c4 * 1 + c5 * (zh + z), [0.242188, 0.253125]) *)
Notation p147 := (ABS r118 i95). (* ABS(c4 * 1, [0.25, 0.25]) *)
Notation p148 := (BND r118 i37). (* BND(c4 * 1, [-0.25, -0.25]) *)
Lemma t86 : p47 -> p25 -> p148.
Proof.
 intros h0 h1.
 refine (mul_np _c4 r44 i37 i16 i37 h0 h1 _) ; finalize.
Qed.
Lemma l123 : s1 -> p148 (* BND(c4 * 1, [-0.25, -0.25]) *).
Proof.
 intros h0.
 assert (h1 := l42 h0).
 assert (h2 := l25 h0).
 apply t86. exact h1. exact h2.
Qed.
Lemma t87 : p148 -> p147.
Proof.
 intros h0.
 refine (abs_of_bnd_n r118 i37 i95 h0 _) ; finalize.
Qed.
Lemma l122 : s1 -> p147 (* ABS(c4 * 1, [0.25, 0.25]) *).
Proof.
 intros h0.
 assert (h1 := l123 h0).
 apply t87. exact h1.
Qed.
Definition f148 := Float2 (31522008434041728608623550480116163143310596858758767371178360982439341388318459949141077589440035594541075344883345) (-392).
Definition i120 := makepairF f15 f148.
Notation p149 := (ABS r119 i120). (* ABS(c5 * (zh + z), [0, 0.00312504]) *)
Definition f149 := Float2 (20174085397541783167432539578442773795056967391875368720543536437416532818786683929305671145092430542365321373114783241) (-399).
Definition i121 := makepairF f15 f149.
Notation p150 := (ABS r120 i121). (* ABS(zh + z, [0, 0.0156252]) *)
Definition f150 := Float2 (5043521349385445511886458530797682642347064869264397904085202322227365902942193379290891821759101205469034280338571767) (-398).
Definition i122 := makepairF f1 f150.
Notation p151 := (ABS _zh i122). (* ABS(zh, [5.42101e-20, 0.0078126]) *)
Lemma t88 : p151 -> p136 -> p150.
Proof.
 intros h0 h1.
 refine (add_aa_o _zh _z i122 i110 i121 h0 h1 _) ; finalize.
Qed.
Lemma l125 : s1 -> p150 (* ABS(zh + z, [0, 0.0156252]) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 assert (h2 := l93 h0).
 apply t88. refine (abs_subset _zh i1 i122 h1 _) ; finalize. refine (abs_subset _z i87 i110 h2 _) ; finalize.
Qed.
Definition i123 := makepairF f61 f64.
Notation p152 := (ABS _c5 i123). (* ABS(c5, [0.125, 0.2]) *)
Lemma t89 : p152 -> p150 -> p149.
Proof.
 intros h0 h1.
 refine (mul_aa _c5 r120 i123 i121 i120 h0 h1 _) ; finalize.
Qed.
Lemma l124 : s1 -> p149 (* ABS(c5 * (zh + z), [0, 0.00312504]) *).
Proof.
 intros h0.
 assert (h1 := l103 h0).
 assert (h2 := l125 h0).
 apply t89. refine (abs_subset _c5 i40 i123 h1 _) ; finalize. exact h2.
Qed.
Lemma t90 : p147 -> p149 -> p146.
Proof.
 intros h0 h1.
 refine (add_aa_p r118 r119 i95 i120 i119 h0 h1 _) ; finalize.
Qed.
Lemma l121 : s1 -> p146 (* ABS(c4 * 1 + c5 * (zh + z), [0.242188, 0.253125]) *).
Proof.
 intros h0.
 assert (h1 := l122 h0).
 assert (h2 := l124 h0).
 apply t90. exact h1. exact h2.
Qed.
Definition f151 := Float2 (307836053257830904831179522583478916190069336962945590727817436261801330606428931688216755754525252916619187585159) (-392).
Definition i124 := makepairF f15 f151.
Notation p153 := (ABS r121 i124). (* ABS(c6 * (zh * zh + z * zh + z * z), [0, 3.05184e-05]) *)
Definition f152 := Float2 (1847016323166034499098949223635680957371051173281771481063023454892139609150879893621785917296047604250303509634889) (-392).
Definition i125 := makepairF f15 f152.
Notation p154 := (ABS r122 i125). (* ABS(zh * zh + z * zh + z * z, [0, 0.00018311]) *)
Definition f153 := Float2 (2462688430888045862091929042352218977363469741340086026033100512046256317188325732282710724814830044613801714993697) (-393).
Definition i126 := makepairF f15 f153.
Notation p155 := (ABS r123 i126). (* ABS(zh * zh + z * zh, [0, 0.000122073]) *)
Definition f154 := Float2 (1231344215444022862692629559928436731612521218675469845795501614457297464166443124845250670208598564932730538080411) (-393).
Definition i127 := makepairF f112 f154.
Notation p156 := (ABS r42 i127). (* ABS(zh * zh, [2.93874e-39, 6.10367e-05]) *)
Definition f155 := Float2 (615672107722011499699649741211891122875474261332308090118799448794479426510941303718730027303115739840535588456643) (-392).
Definition i128 := makepairF f15 f155.
Notation p157 := (ABS r111 i128). (* ABS(z * zh, [0, 6.10367e-05]) *)
Lemma t91 : p156 -> p157 -> p155.
Proof.
 intros h0 h1.
 refine (add_aa_o r42 r111 i127 i128 i126 h0 h1 _) ; finalize.
Qed.
Lemma l128 : s1 -> p155 (* ABS(zh * zh + z * zh, [0, 0.000122073]) *).
Proof.
 intros h0.
 assert (h1 := l95 h0).
 assert (h2 := l94 h0).
 apply t91. refine (abs_subset r42 i90 i127 h1 _) ; finalize. refine (abs_subset r111 i89 i128 h2 _) ; finalize.
Qed.
Definition f156 := Float2 (1231344215444023136105969404919142937378632605223456936092946397738022901113434054960861109777265163886805304276081) (-393).
Definition i129 := makepairF f15 f156.
Notation p158 := (ABS r9 i129). (* ABS(z * z, [0, 6.10367e-05]) *)
Lemma t92 : p155 -> p158 -> p154.
Proof.
 intros h0 h1.
 refine (add_aa_o r123 r9 i126 i129 i125 h0 h1 _) ; finalize.
Qed.
Lemma l127 : s1 -> p154 (* ABS(zh * zh + z * zh + z * z, [0, 0.00018311]) *).
Proof.
 intros h0.
 assert (h1 := l128 h0).
 assert (h2 := l92 h0).
 apply t92. exact h1. refine (abs_subset r9 i86 i129 h2 _) ; finalize.
Qed.
Definition i130 := makepairF f61 f124.
Notation p159 := (ABS _c6 i130). (* ABS(c6, [0.125, 0.166667]) *)
Lemma t93 : p159 -> p154 -> p153.
Proof.
 intros h0 h1.
 refine (mul_aa _c6 r122 i130 i125 i124 h0 h1 _) ; finalize.
Qed.
Lemma l126 : s1 -> p153 (* ABS(c6 * (zh * zh + z * zh + z * z), [0, 3.05184e-05]) *).
Proof.
 intros h0.
 assert (h1 := l106 h0).
 assert (h2 := l127 h0).
 apply t93. refine (abs_subset _c6 i100 i130 h1 _) ; finalize. exact h2.
Qed.
Lemma t94 : p146 -> p153 -> p145.
Proof.
 intros h0 h1.
 refine (add_aa_p r117 r121 i119 i124 i118 h0 h1 _) ; finalize.
Qed.
Lemma l120 : s1 -> p145 (* ABS(c4 * 1 + c5 * (zh + z) + c6 * (zh * zh + z * zh + z * z), [0.234375, 0.253156]) *).
Proof.
 intros h0.
 assert (h1 := l121 h0).
 assert (h2 := l126 h0).
 apply t94. exact h1. exact h2.
Qed.
Definition f157 := Float2 (2748569841185094933028790095811882335399331815288135178459334320733704868896537505343320962960730113694272046071) (-392).
Definition i131 := makepairF f15 f157.
Notation p160 := (ABS r124 i131). (* ABS(c7 * (zh * zh * zh + z * zh * zh + z * z * zh + z * z * z), [0, 2.72489e-07]) *)
Definition f158 := Float2 (76959998540623796952993854837021823445482932111994147745436787423404625559982427013533898259969709488021633699639) (-394).
Definition i132 := makepairF f15 f158.
Notation p161 := (ABS r125 i132). (* ABS(zh * zh * zh + z * zh * zh + z * z * zh + z * z * z, [0, 1.90742e-06]) *)
Definition f159 := Float2 (461759991243742756085134422546435873521826380684197371934495265398090557134469256221106069038947248414909478379953) (-397).
Definition i133 := makepairF f15 f159.
Notation p162 := (ABS r126 i133). (* ABS(zh * zh * zh + z * zh * zh + z * z * zh, [0, 1.43057e-06]) *)
Definition f160 := Float2 (4925439906599922458157927638087922171532759987505550358268467471465621018538371485704167887024215348876745543311297) (-401).
Definition i134 := makepairF f15 f160.
Notation p163 := (ABS r127 i134). (* ABS(zh * zh * zh + z * zh * zh, [0, 9.53711e-07]) *)
Definition f161 := Float2 (2462719953299961365787383586914314540327388269611412574649411877709695983390402575069670508189860878888022189248701) (-401).
Definition i135 := makepairF f15 f161.
Notation p164 := (ABS r128 i135). (* ABS(z * zh * zh, [0, 4.76855e-07]) *)
Definition f162 := Float2 (9850627635518448265403239317964223910834111072782027156416410785600324029183971443927523089373244541931707578786273) (-389).
Definition i136 := makepairF f1 f162.
Notation p165 := (ABS _zh i136). (* ABS(zh, [5.42101e-20, 0.0078126]) *)
Lemma t95 : p157 -> p165 -> p164.
Proof.
 intros h0 h1.
 refine (mul_aa r111 _zh i128 i136 i135 h0 h1 _) ; finalize.
Qed.
Lemma l133 : s1 -> p164 (* ABS(z * zh * zh, [0, 4.76855e-07]) *).
Proof.
 intros h0.
 assert (h1 := l94 h0).
 assert (h2 := l7 h0).
 apply t95. refine (abs_subset r111 i89 i128 h1 _) ; finalize. refine (abs_subset _zh i1 i136 h2 _) ; finalize.
Qed.
Definition f163 := Float2 (615679988324990273092636012793401907801342929473534445904763898438981258786992227658624344708588617497180838515649) (-399).
Definition i137 := makepairF f136 f163.
Notation p166 := (ABS r50 i137). (* ABS(zh * zh * zh, [1.59309e-58, 4.76855e-07]) *)
Lemma t96 : p166 -> p164 -> p163.
Proof.
 intros h0 h1.
 refine (add_aa_o r50 r128 i137 i135 i134 h0 h1 _) ; finalize.
Qed.
Lemma l132 : s1 -> p163 (* ABS(zh * zh * zh + z * zh * zh, [0, 9.53711e-07]) *).
Proof.
 intros h0.
 assert (h1 := l116 h0).
 assert (h2 := l133 h0).
 apply t96. refine (abs_subset r50 i112 i137 h1 _) ; finalize. exact h2.
Qed.
Definition f164 := Float2 (2462719953299961639204223122655051804816462103441607592683456774903827895613136613833529217598940625761806110767951) (-401).
Definition i138 := makepairF f15 f164.
Notation p167 := (ABS r129 i138). (* ABS(z * z * zh, [0, 4.76855e-07]) *)
Definition f165 := Float2 (9850753723552185088847755239353143499029060841787655488743571181904183208907472439686888878218121311094442434208645) (-396).
Definition i139 := makepairF f15 f165.
Notation p168 := (ABS r9 i139). (* ABS(z * z, [0, 6.10367e-05]) *)
Definition f166 := Float2 (4925313817759224132701619658982111955417055536391013578208205392800162014591985721963761544686622270965853789393137) (-388).
Definition i140 := makepairF f1 f166.
Notation p169 := (ABS _zh i140). (* ABS(zh, [5.42101e-20, 0.0078126]) *)
Lemma t97 : p168 -> p169 -> p167.
Proof.
 intros h0 h1.
 refine (mul_aa r9 _zh i139 i140 i138 h0 h1 _) ; finalize.
Qed.
Lemma l134 : s1 -> p167 (* ABS(z * z * zh, [0, 4.76855e-07]) *).
Proof.
 intros h0.
 assert (h1 := l92 h0).
 assert (h2 := l7 h0).
 apply t97. refine (abs_subset r9 i86 i139 h1 _) ; finalize. refine (abs_subset _zh i1 i140 h2 _) ; finalize.
Qed.
Lemma t98 : p163 -> p167 -> p162.
Proof.
 intros h0 h1.
 refine (add_aa_o r127 r129 i134 i138 i133 h0 h1 _) ; finalize.
Qed.
Lemma l131 : s1 -> p162 (* ABS(zh * zh * zh + z * zh * zh + z * z * zh, [0, 1.43057e-06]) *).
Proof.
 intros h0.
 assert (h1 := l132 h0).
 assert (h2 := l134 h0).
 apply t98. exact h1. exact h2.
Qed.
Definition f167 := Float2 (153919997081247619538816416149738714042037076211755810028999033989146447345390159887165117040810427489263591217159) (-397).
Definition i141 := makepairF f15 f167.
Notation p170 := (ABS r12 i141). (* ABS(z * z * z, [0, 4.76855e-07]) *)
Definition f168 := Float2 (76958028402487885617520313391474979479696942545673926638588957160658271887987496724883174908250641871850988864423) (-382).
Definition i142 := makepairF f15 f168.
Notation p171 := (ABS _z i142). (* ABS(z, [0, 0.0078126]) *)
Lemma t99 : p158 -> p171 -> p170.
Proof.
 intros h0 h1.
 refine (mul_aa r9 _z i129 i142 i141 h0 h1 _) ; finalize.
Qed.
Lemma l135 : s1 -> p170 (* ABS(z * z * z, [0, 4.76855e-07]) *).
Proof.
 intros h0.
 assert (h1 := l92 h0).
 assert (h2 := l93 h0).
 apply t99. refine (abs_subset r9 i86 i129 h1 _) ; finalize. refine (abs_subset _z i87 i142 h2 _) ; finalize.
Qed.
Lemma t100 : p162 -> p170 -> p161.
Proof.
 intros h0 h1.
 refine (add_aa_o r126 r12 i133 i141 i132 h0 h1 _) ; finalize.
Qed.
Lemma l130 : s1 -> p161 (* ABS(zh * zh * zh + z * zh * zh + z * z * zh + z * z * z, [0, 1.90742e-06]) *).
Proof.
 intros h0.
 assert (h1 := l131 h0).
 assert (h2 := l135 h0).
 apply t100. exact h1. exact h2.
Qed.
Definition i143 := makepairF f61 f73.
Notation p172 := (ABS _c7 i143). (* ABS(c7, [0.125, 0.142857]) *)
Lemma t101 : p172 -> p161 -> p160.
Proof.
 intros h0 h1.
 refine (mul_aa _c7 r125 i143 i132 i131 h0 h1 _) ; finalize.
Qed.
Lemma l129 : s1 -> p160 (* ABS(c7 * (zh * zh * zh + z * zh * zh + z * z * zh + z * z * z), [0, 2.72489e-07]) *).
Proof.
 intros h0.
 assert (h1 := l109 h0).
 assert (h2 := l130 h0).
 apply t101. refine (abs_subset _c7 i46 i143 h1 _) ; finalize. exact h2.
Qed.
Lemma t102 : p145 -> p160 -> p144.
Proof.
 intros h0 h1.
 refine (add_aa_p r116 r124 i118 i131 i117 h0 h1 _) ; finalize.
Qed.
Lemma l119 : s1 -> p144 (* ABS(c4 * 1 + c5 * (zh + z) + c6 * (zh * zh + z * zh + z * z) + c7 * (zh * zh * zh + z * zh * zh + z * z * zh + z * z * z), [0.21875, 0.253156]) *).
Proof.
 intros h0.
 assert (h1 := l120 h0).
 assert (h2 := l129 h0).
 apply t102. exact h1. exact h2.
Qed.
Definition f169 := Float2 (46977273261111021305723534237915694799123840154501535297262742569372046692526866857077875365889553153915416103) (-393).
Definition i144 := makepairF f15 f169.
Notation p173 := (ABS r130 i144). (* ABS(c8 * (zh * zh * zh * zh + z * zh * zh * zh + z * z * zh * zh + z * z * z * zh + z * z * z * z), [0, 2.32862e-09]) *)
Definition f170 := Float2 (93946513218512110851791570156519017991453923591843913403457746503239473447845581518087437171768911736112623671) (-391).
Definition i145 := makepairF f15 f170.
Notation p174 := (ABS r131 i145). (* ABS(zh * zh * zh * zh + z * zh * zh * zh + z * z * zh * zh + z * z * z * zh + z * z * z * z, [0, 1.86274e-08]) *)
Definition f171 := Float2 (150314421149619369018739947574929174462544988854541369668999861356022744412479677321483733386459838086529453861) (-392).
Definition i146 := makepairF f15 f171.
Notation p175 := (ABS r132 i146). (* ABS(zh * zh * zh * zh + z * zh * zh * zh + z * z * zh * zh + z * z * z * zh, [0, 1.49019e-08]) *)
Definition f172 := Float2 (225471631724429041011920074349142806592288798858335024248464856903070142916797156947063329685854954560395111925) (-393).
Definition i147 := makepairF f15 f172.
Notation p176 := (ABS r133 i147). (* ABS(zh * zh * zh * zh + z * zh * zh * zh + z * z * zh * zh, [0, 1.11764e-08]) *)
Definition f173 := Float2 (150314421149619352330486818223928518583268908899944776285188394404579338943097191676610867320958534510290868093) (-393).
Definition i148 := makepairF f15 f173.
Notation p177 := (ABS r134 i148). (* ABS(zh * zh * zh * zh + z * zh * zh * zh, [0, 7.45096e-09]) *)
Definition f174 := Float2 (1) (-256).
Definition f175 := Float2 (300628842299238687972720507096858234055548235675308450754722402059024061399953467362860534716894964566154688687) (-395).
Definition i149 := makepairF f174 f175.
Notation p178 := (ABS r135 i149). (* ABS(zh * zh * zh * zh, [8.63617e-78, 3.72548e-09]) *)
Definition f176 := Float2 (601249988598623313567027356243556550587248954563998482328870994569317635534172097322875336629481071774590662613) (-389).
Definition i150 := makepairF f136 f176.
Notation p179 := (ABS r50 i150). (* ABS(zh * zh * zh, [1.59309e-58, 4.76855e-07]) *)
Definition f177 := Float2 (601234596894436539636428181028089838307746037157106149683618822363301027171873257075654485435378695186261448901) (-375).
Definition i151 := makepairF f1 f177.
Notation p180 := (ABS _zh i151). (* ABS(zh, [5.42101e-20, 0.0078126]) *)
Lemma t103 : p179 -> p180 -> p178.
Proof.
 intros h0 h1.
 refine (mul_aa r50 _zh i150 i151 i149 h0 h1 _) ; finalize.
Qed.
Lemma l141 : s1 -> p178 (* ABS(zh * zh * zh * zh, [8.63617e-78, 3.72548e-09]) *).
Proof.
 intros h0.
 assert (h1 := l116 h0).
 assert (h2 := l7 h0).
 apply t103. refine (abs_subset r50 i112 i150 h1 _) ; finalize. refine (abs_subset _zh i1 i151 h2 _) ; finalize.
Qed.
Definition f178 := Float2 (1202515369196954885396907063195423361110109599697882617544124702237173177489741197374331738267756693900035134733) (-397).
Definition i152 := makepairF f15 f178.
Notation p181 := (ABS r136 i152). (* ABS(z * zh * zh * zh, [0, 3.72548e-09]) *)
Definition f179 := Float2 (4809999908788987042553483568192020586576930214084790184862132573651749967559380029432950211308322029078168338377) (-392).
Definition i153 := makepairF f15 f179.
Notation p182 := (ABS r128 i153). (* ABS(z * zh * zh, [0, 4.76855e-07]) *)
Definition f180 := Float2 (9619753550310984634182850896449437412923936594513698394937901157812816434749972113210471766966059122980183182409) (-379).
Definition i154 := makepairF f1 f180.
Notation p183 := (ABS _zh i154). (* ABS(zh, [5.42101e-20, 0.0078126]) *)
Lemma t104 : p182 -> p183 -> p181.
Proof.
 intros h0 h1.
 refine (mul_aa r128 _zh i153 i154 i152 h0 h1 _) ; finalize.
Qed.
Lemma l142 : s1 -> p181 (* ABS(z * zh * zh * zh, [0, 3.72548e-09]) *).
Proof.
 intros h0.
 assert (h1 := l133 h0).
 assert (h2 := l7 h0).
 apply t104. refine (abs_subset r128 i135 i153 h1 _) ; finalize. refine (abs_subset _zh i1 i154 h2 _) ; finalize.
Qed.
Definition f181 := Float2 (18789302643702417998295031693553639628471764729706778172170150128689003837497091710178783419805935285384668043) (-391).
Definition i155 := makepairF f174 f181.
Notation p184 := (ABS r135 i155). (* ABS(zh * zh * zh * zh, [8.63617e-78, 3.72548e-09]) *)
Definition f182 := Float2 (75157210574809680337306691449713960069381849981117663596507793889823323593108824835895733641734793368752195921) (-393).
Definition i156 := makepairF f15 f182.
Notation p185 := (ABS r136 i156). (* ABS(z * zh * zh * zh, [0, 3.72548e-09]) *)
Lemma t105 : p184 -> p185 -> p177.
Proof.
 intros h0 h1.
 refine (add_aa_o r135 r136 i155 i156 i148 h0 h1 _) ; finalize.
Qed.
Lemma l140 : s1 -> p177 (* ABS(zh * zh * zh * zh + z * zh * zh * zh, [0, 7.45096e-09]) *).
Proof.
 intros h0.
 assert (h1 := l141 h0).
 assert (h2 := l142 h0).
 apply t105. refine (abs_subset r135 i149 i155 h1 _) ; finalize. refine (abs_subset r136 i152 i156 h2 _) ; finalize.
Qed.
Definition f183 := Float2 (9394651321851211085179157015651786001127486244798780995409557812311350496712495658806557795612052506263030479) (-390).
Definition i157 := makepairF f15 f183.
Notation p186 := (ABS r137 i157). (* ABS(z * z * zh * zh, [0, 3.72548e-09]) *)
Definition f184 := Float2 (2404999954394493788285374143217824028141076272892194914729938256742019429309703724446805876561465454845513780047) (-391).
Definition i158 := makepairF f15 f184.
Notation p187 := (ABS r129 i158). (* ABS(z * z * zh, [0, 4.76855e-07]) *)
Definition f185 := Float2 (4809876775155492317091425448224718706461968297256849197468950578906408217374986056605235883483029561490091591205) (-378).
Definition i159 := makepairF f1 f185.
Notation p188 := (ABS _zh i159). (* ABS(zh, [5.42101e-20, 0.0078126]) *)
Lemma t106 : p187 -> p188 -> p186.
Proof.
 intros h0 h1.
 refine (mul_aa r129 _zh i158 i159 i157 h0 h1 _) ; finalize.
Qed.
Lemma l143 : s1 -> p186 (* ABS(z * z * zh * zh, [0, 3.72548e-09]) *).
Proof.
 intros h0.
 assert (h1 := l134 h0).
 assert (h2 := l7 h0).
 apply t106. refine (abs_subset r129 i138 i158 h1 _) ; finalize. refine (abs_subset _zh i1 i159 h2 _) ; finalize.
Qed.
Lemma t107 : p177 -> p186 -> p176.
Proof.
 intros h0 h1.
 refine (add_aa_o r134 r137 i148 i157 i147 h0 h1 _) ; finalize.
Qed.
Lemma l139 : s1 -> p176 (* ABS(zh * zh * zh * zh + z * zh * zh * zh + z * z * zh * zh, [0, 1.11764e-08]) *).
Proof.
 intros h0.
 assert (h1 := l140 h0).
 assert (h2 := l143 h0).
 apply t107. exact h1. exact h2.
Qed.
Definition f186 := Float2 (75157210574809697025559820800715542332801178850747715089534865808975345908162197695904137087064721612663795797) (-393).
Definition i160 := makepairF f15 f186.
Notation p189 := (ABS r138 i160). (* ABS(z * z * z * zh, [0, 3.72548e-09]) *)
Definition f187 := Float2 (1202499977197247027647003251169833703453414657904342265851554953040206619885860624118477476881331464759871806385) (-390).
Definition i161 := makepairF f15 f187.
Notation p190 := (ABS r12 i161). (* ABS(z * z * z, [0, 4.76855e-07]) *)
Definition f188 := Float2 (75154324611804567454553522628511229788468254644638268710452352795412628396484157134456810679422336898282681113) (-372).
Definition i162 := makepairF f1 f188.
Notation p191 := (ABS _zh i162). (* ABS(zh, [5.42101e-20, 0.0078126]) *)
Lemma t108 : p190 -> p191 -> p189.
Proof.
 intros h0 h1.
 refine (mul_aa r12 _zh i161 i162 i160 h0 h1 _) ; finalize.
Qed.
Lemma l144 : s1 -> p189 (* ABS(z * z * z * zh, [0, 3.72548e-09]) *).
Proof.
 intros h0.
 assert (h1 := l135 h0).
 assert (h2 := l7 h0).
 apply t108. refine (abs_subset r12 i141 i161 h1 _) ; finalize. refine (abs_subset _zh i1 i162 h2 _) ; finalize.
Qed.
Lemma t109 : p176 -> p189 -> p175.
Proof.
 intros h0 h1.
 refine (add_aa_o r133 r138 i147 i160 i146 h0 h1 _) ; finalize.
Qed.
Lemma l138 : s1 -> p175 (* ABS(zh * zh * zh * zh + z * zh * zh * zh + z * z * zh * zh + z * z * z * zh, [0, 1.49019e-08]) *).
Proof.
 intros h0.
 assert (h1 := l139 h0).
 assert (h2 := l144 h0).
 apply t109. exact h1. exact h2.
Qed.
Definition f189 := Float2 (37578605287404852684843192738108861520362858329146457137915631650456202483211485714691140957077985385695793481) (-392).
Definition i163 := makepairF f15 f189.
Notation p192 := (ABS r139 i163). (* ABS(z * z * z * z, [0, 3.72548e-09]) *)
Definition f190 := Float2 (150312497149655878455875406396229212931676832238042783231444369130025827485732578014809684610166433094983975799) (-387).
Definition i164 := makepairF f15 f190.
Notation p193 := (ABS r12 i164). (* ABS(z * z * z, [0, 4.76855e-07]) *)
Definition f191 := Float2 (75154324611804575798359681046362284648141545454759693982997028477205343640612789770393725496338517452979481313) (-372).
Definition i165 := makepairF f15 f191.
Notation p194 := (ABS _z i165). (* ABS(z, [0, 0.0078126]) *)
Lemma t110 : p193 -> p194 -> p192.
Proof.
 intros h0 h1.
 refine (mul_aa r12 _z i164 i165 i163 h0 h1 _) ; finalize.
Qed.
Lemma l145 : s1 -> p192 (* ABS(z * z * z * z, [0, 3.72548e-09]) *).
Proof.
 intros h0.
 assert (h1 := l135 h0).
 assert (h2 := l93 h0).
 apply t110. refine (abs_subset r12 i141 i164 h1 _) ; finalize. refine (abs_subset _z i87 i165 h2 _) ; finalize.
Qed.
Lemma t111 : p175 -> p192 -> p174.
Proof.
 intros h0 h1.
 refine (add_aa_o r132 r139 i146 i163 i145 h0 h1 _) ; finalize.
Qed.
Lemma l137 : s1 -> p174 (* ABS(zh * zh * zh * zh + z * zh * zh * zh + z * z * zh * zh + z * z * z * zh + z * z * z * z, [0, 1.86274e-08]) *).
Proof.
 intros h0.
 assert (h1 := l138 h0).
 assert (h2 := l145 h0).
 apply t111. exact h1. exact h2.
Qed.
Lemma t112 : p130 -> p174 -> p173.
Proof.
 intros h0 h1.
 refine (mul_aa _c8 r131 i105 i145 i144 h0 h1 _) ; finalize.
Qed.
Lemma l136 : s1 -> p173 (* ABS(c8 * (zh * zh * zh * zh + z * zh * zh * zh + z * z * zh * zh + z * z * z * zh + z * z * z * z), [0, 2.32862e-09]) *).
Proof.
 intros h0.
 assert (h1 := l112 h0).
 assert (h2 := l137 h0).
 apply t112. exact h1. exact h2.
Qed.
Lemma t113 : p144 -> p173 -> p143.
Proof.
 intros h0 h1.
 refine (add_aa_p r115 r130 i117 i144 i116 h0 h1 _) ; finalize.
Qed.
Lemma l118 : s1 -> p143 (* ABS(c4 * 1 + c5 * (zh + z) + c6 * (zh * zh + z * zh + z * z) + c7 * (zh * zh * zh + z * zh * zh + z * z * zh + z * z * z) + c8 * (zh * zh * zh * zh + z * zh * zh * zh + z * z * zh * zh + z * z * z * zh + z * z * z * z), [0.1875, 0.253156]) *).
Proof.
 intros h0.
 assert (h1 := l119 h0).
 assert (h2 := l136 h0).
 apply t113. exact h1. exact h2.
Qed.
Definition f192 := Float2 (394105388092889625635084218414936792007105290815996211312273588876005348170882615632870416251227994416336045) (-393).
Definition i166 := makepairF f15 f192.
Notation p195 := (ABS r140 i166). (* ABS(c9 * (zh * zh * zh * zh * zh + z * zh * zh * zh * zh + z * z * zh * zh * zh + z * z * z * zh * zh + z * z * z * z * zh + z * z * z * z * z), [0, 1.95355e-11]) *)
Definition f193 := Float2 (6880936210977635231100317067137922026046082457675713032412794315384521775530950826693930374229902371839893) (-384).
Definition i167 := makepairF f15 f193.
Notation p196 := (ABS r141 i167). (* ABS(zh * zh * zh * zh * zh + z * zh * zh * zh * zh + z * z * zh * zh * zh + z * z * z * zh * zh + z * z * z * z * zh + z * z * z * z * z, [0, 1.74634e-10]) *)
Definition f194 := Float2 (2935866116683790868962827284019281919840131693814559031423415961324834841034553560672839646592647199318213935) (-393).
Definition i168 := makepairF f15 f194.
Notation p197 := (ABS r142 i168). (* ABS(zh * zh * zh * zh * zh + z * zh * zh * zh * zh + z * z * zh * zh * zh + z * z * z * zh * zh + z * z * z * z * zh, [0, 1.45528e-10]) *)
Definition f195 := Float2 (4697385786694065129583230857695566673624315919699959618704113267320253171987754908167295261820224524139280045) (-394).
Definition i169 := makepairF f15 f195.
Notation p198 := (ABS r143 i169). (* ABS(zh * zh * zh * zh * zh + z * zh * zh * zh * zh + z * z * zh * zh * zh + z * z * z * zh * zh, [0, 1.16423e-10]) *)
Definition f196 := Float2 (28184314720164389212955628365761809452526647519370051367096904656654812776828311493834031512059366687976685623) (-397).
Definition i170 := makepairF f15 f196.
Notation p199 := (ABS r144 i170). (* ABS(zh * zh * zh * zh * zh + z * zh * zh * zh * zh + z * z * zh * zh * zh, [0, 8.73171e-11]) *)
Definition f197 := Float2 (18789543146776258432274581056900223108538346842747336947290605602003464694829457915083040992507530347441574977) (-397).
Definition i171 := makepairF f15 f197.
Notation p200 := (ABS r145 i171). (* ABS(zh * zh * zh * zh * zh + z * zh * zh * zh * zh, [0, 5.82114e-11]) *)
Definition f198 := Float2 (1) (-320).
Definition f199 := Float2 (75158172587105029556981639479837268460236036673181273675723015626442604226984846691810694832934835205425283867) (-400).
Definition i172 := makepairF f198 f199.
Notation p201 := (ABS r146 i172). (* ABS(zh * zh * zh * zh * zh, [4.68168e-97, 2.91057e-11]) *)
Definition f200 := Float2 (300617298447218269818214090514044919153873018578553074841809411181650513585936628537827242717689347593130724451) (-374).
Definition i173 := makepairF f1 f200.
Notation p202 := (ABS _zh i173). (* ABS(zh, [5.42101e-20, 0.0078126]) *)
Lemma t114 : p178 -> p202 -> p201.
Proof.
 intros h0 h1.
 refine (mul_aa r135 _zh i149 i173 i172 h0 h1 _) ; finalize.
Qed.
Lemma l152 : s1 -> p201 (* ABS(zh * zh * zh * zh * zh, [4.68168e-97, 2.91057e-11]) *).
Proof.
 intros h0.
 assert (h1 := l141 h0).
 assert (h2 := l7 h0).
 apply t114. exact h1. refine (abs_subset _zh i1 i173 h2 _) ; finalize.
Qed.
Definition f201 := Float2 (75158172587105037901215008975364516408070738068797421902601829189585113331650816628853633107125407574107315949) (-400).
Definition i174 := makepairF f15 f201.
Notation p203 := (ABS r147 i174). (* ABS(z * zh * zh * zh * zh, [0, 2.91057e-11]) *)
Lemma t115 : p181 -> p180 -> p203.
Proof.
 intros h0 h1.
 refine (mul_aa r136 _zh i152 i151 i174 h0 h1 _) ; finalize.
Qed.
Lemma l153 : s1 -> p203 (* ABS(z * zh * zh * zh * zh, [0, 2.91057e-11]) *).
Proof.
 intros h0.
 assert (h1 := l142 h0).
 assert (h2 := l7 h0).
 apply t115. exact h1. refine (abs_subset _zh i1 i151 h2 _) ; finalize.
Qed.
Lemma t116 : p201 -> p203 -> p200.
Proof.
 intros h0 h1.
 refine (add_aa_o r146 r147 i172 i174 i171 h0 h1 _) ; finalize.
Qed.
Lemma l151 : s1 -> p200 (* ABS(zh * zh * zh * zh * zh + z * zh * zh * zh * zh, [0, 5.82114e-11]) *).
Proof.
 intros h0.
 assert (h1 := l152 h0).
 assert (h2 := l153 h0).
 apply t116. exact h1. exact h2.
Qed.
Definition f202 := Float2 (4697385786694065390340523654430793171994150338311357209903149527325674040999426789375495259775918170267555323) (-396).
Definition i175 := makepairF f15 f202.
Notation p204 := (ABS r148 i175). (* ABS(z * z * zh * zh * zh, [0, 2.91057e-11]) *)
Definition f203 := Float2 (37577162305902283727276761314255614894234127322319134355226176397706314198242078567228405339711168449141340557) (-371).
Definition i176 := makepairF f1 f203.
Notation p205 := (ABS _zh i176). (* ABS(zh, [5.42101e-20, 0.0078126]) *)
Lemma t117 : p186 -> p205 -> p204.
Proof.
 intros h0 h1.
 refine (mul_aa r137 _zh i157 i176 i175 h0 h1 _) ; finalize.
Qed.
Lemma l154 : s1 -> p204 (* ABS(z * z * zh * zh * zh, [0, 2.91057e-11]) *).
Proof.
 intros h0.
 assert (h1 := l143 h0).
 assert (h2 := l7 h0).
 apply t117. exact h1. refine (abs_subset _zh i1 i176 h2 _) ; finalize.
Qed.
Lemma t118 : p200 -> p204 -> p199.
Proof.
 intros h0 h1.
 refine (add_aa_o r145 r148 i171 i175 i170 h0 h1 _) ; finalize.
Qed.
Lemma l150 : s1 -> p199 (* ABS(zh * zh * zh * zh * zh + z * zh * zh * zh * zh + z * z * zh * zh * zh, [0, 8.73171e-11]) *).
Proof.
 intros h0.
 assert (h1 := l151 h0).
 assert (h2 := l154 h0).
 apply t118. exact h1. exact h2.
Qed.
Definition f204 := Float2 (9394771573388131823710218495802723936467879838229625582536001481907212599073727771504330582502429505137554737) (-397).
Definition i177 := makepairF f15 f204.
Notation p206 := (ABS r149 i177). (* ABS(z * z * z * zh * zh, [0, 2.91057e-11]) *)
Definition f205 := Float2 (37578605287404848512779910400357771166400589425373857544767432904487672954081098847952068543532360806331897899) (-392).
Definition i178 := makepairF f15 f205.
Notation p207 := (ABS r138 i178). (* ABS(z * z * z * zh, [0, 3.72548e-09]) *)
Lemma t119 : p207 -> p191 -> p206.
Proof.
 intros h0 h1.
 refine (mul_aa r138 _zh i178 i162 i177 h0 h1 _) ; finalize.
Qed.
Lemma l155 : s1 -> p206 (* ABS(z * z * z * zh * zh, [0, 2.91057e-11]) *).
Proof.
 intros h0.
 assert (h1 := l144 h0).
 assert (h2 := l7 h0).
 apply t119. refine (abs_subset r138 i160 i178 h1 _) ; finalize. refine (abs_subset _zh i1 i162 h2 _) ; finalize.
Qed.
Lemma t120 : p199 -> p206 -> p198.
Proof.
 intros h0 h1.
 refine (add_aa_o r144 r149 i170 i177 i169 h0 h1 _) ; finalize.
Qed.
Lemma l149 : s1 -> p198 (* ABS(zh * zh * zh * zh * zh + z * zh * zh * zh * zh + z * z * zh * zh * zh + z * z * z * zh * zh, [0, 1.16423e-10]) *).
Proof.
 intros h0.
 assert (h1 := l150 h0).
 assert (h2 := l155 h0).
 apply t120. exact h1. exact h2.
Qed.
Definition f206 := Float2 (1174346446673516608342423710342997166055947467929158444142718655329416510081352213178384031365069874497147825) (-394).
Definition i179 := makepairF f15 f206.
Notation p208 := (ABS r150 i179). (* ABS(z * z * z * z * zh, [0, 2.91057e-11]) *)
Definition f207 := Float2 (2348662830462803292802699546131803845022678645571653571119726978153512655200717857168196309817374086605987093) (-388).
Definition i180 := makepairF f15 f207.
Notation p209 := (ABS r139 i180). (* ABS(z * z * z * z, [0, 3.72548e-09]) *)
Definition f208 := Float2 (2348572644118892732954797582140975930889632957644945897201636024856644637390129910451775333731948028071333785) (-367).
Definition i181 := makepairF f1 f208.
Notation p210 := (ABS _zh i181). (* ABS(zh, [5.42101e-20, 0.0078126]) *)
Lemma t121 : p209 -> p210 -> p208.
Proof.
 intros h0 h1.
 refine (mul_aa r139 _zh i180 i181 i179 h0 h1 _) ; finalize.
Qed.
Lemma l156 : s1 -> p208 (* ABS(z * z * z * z * zh, [0, 2.91057e-11]) *).
Proof.
 intros h0.
 assert (h1 := l145 h0).
 assert (h2 := l7 h0).
 apply t121. refine (abs_subset r139 i163 i180 h1 _) ; finalize. refine (abs_subset _zh i1 i181 h2 _) ; finalize.
Qed.
Lemma t122 : p198 -> p208 -> p197.
Proof.
 intros h0 h1.
 refine (add_aa_o r143 r150 i169 i179 i168 h0 h1 _) ; finalize.
Qed.
Lemma l148 : s1 -> p197 (* ABS(zh * zh * zh * zh * zh + z * zh * zh * zh * zh + z * z * zh * zh * zh + z * z * z * zh * zh + z * z * z * z * zh, [0, 1.45528e-10]) *).
Proof.
 intros h0.
 assert (h1 := l149 h0).
 assert (h2 := l156 h0).
 apply t122. exact h1. exact h2.
Qed.
Definition f209 := Float2 (587173223336758369360535054355334157495462524515406041171934728152040308037293262594452705013062815063811281) (-393).
Definition i182 := makepairF f15 f209.
Notation p211 := (ABS r151 i182). (* ABS(z * z * z * z * z, [0, 2.91057e-11]) *)
Definition f210 := Float2 (1174331415231401646401349773065901922511339322785826785559863489076756327600358928584098154908687043302993547) (-387).
Definition i183 := makepairF f15 f210.
Notation p212 := (ABS r139 i183). (* ABS(z * z * z * z, [0, 3.72548e-09]) *)
Definition f211 := Float2 (293571580514861624212342504087352674406802911932655054621082142489083373596143710040600490220072333800701099) (-364).
Definition i184 := makepairF f15 f211.
Notation p213 := (ABS _z i184). (* ABS(z, [0, 0.0078126]) *)
Lemma t123 : p212 -> p213 -> p211.
Proof.
 intros h0 h1.
 refine (mul_aa r139 _z i183 i184 i182 h0 h1 _) ; finalize.
Qed.
Lemma l157 : s1 -> p211 (* ABS(z * z * z * z * z, [0, 2.91057e-11]) *).
Proof.
 intros h0.
 assert (h1 := l145 h0).
 assert (h2 := l93 h0).
 apply t123. refine (abs_subset r139 i163 i183 h1 _) ; finalize. refine (abs_subset _z i87 i184 h2 _) ; finalize.
Qed.
Lemma t124 : p197 -> p211 -> p196.
Proof.
 intros h0 h1.
 refine (add_aa_o r142 r151 i168 i182 i167 h0 h1 _) ; finalize.
Qed.
Lemma l147 : s1 -> p196 (* ABS(zh * zh * zh * zh * zh + z * zh * zh * zh * zh + z * z * zh * zh * zh + z * z * z * zh * zh + z * z * z * z * zh + z * z * z * z * z, [0, 1.74634e-10]) *).
Proof.
 intros h0.
 assert (h1 := l148 h0).
 assert (h2 := l157 h0).
 apply t124. exact h1. exact h2.
Qed.
Lemma t125 : p132 -> p196 -> p195.
Proof.
 intros h0 h1.
 refine (mul_aa _c9 r141 i51 i167 i166 h0 h1 _) ; finalize.
Qed.
Lemma l146 : s1 -> p195 (* ABS(c9 * (zh * zh * zh * zh * zh + z * zh * zh * zh * zh + z * z * zh * zh * zh + z * z * z * zh * zh + z * z * z * z * zh + z * z * z * z * z), [0, 1.95355e-11]) *).
Proof.
 intros h0.
 assert (h1 := l114 h0).
 assert (h2 := l147 h0).
 apply t125. exact h1. exact h2.
Qed.
Lemma t126 : p143 -> p195 -> p142.
Proof.
 intros h0 h1.
 refine (add_aa_p r114 r140 i116 i166 i115 h0 h1 _) ; finalize.
Qed.
Lemma l117 : s1 -> p142 (* ABS(D, [0.125, 0.253156]) *).
Proof.
 intros h0.
 assert (h1 := l118 h0).
 assert (h2 := l146 h0).
 apply t126. exact h1. exact h2.
Qed.
Lemma t127 : p139 -> p142 -> p138.
Proof.
 intros h0 h1.
 refine (mul_aa r50 _D i112 i115 i111 h0 h1 _) ; finalize.
Qed.
Lemma l115 : s1 -> p138 (* ABS(zh * zh * zh * D, [1.99136e-59, 1.20719e-07]) *).
Proof.
 intros h0.
 assert (h1 := l116 h0).
 assert (h2 := l117 h0).
 apply t127. exact h1. exact h2.
Qed.
Lemma t128 : p105 -> p138 -> p104.
Proof.
 intros h0 h1.
 refine (add_aa_o r108 r112 i83 i111 i82 h0 h1 _) ; finalize.
Qed.
Lemma l88 : s1 -> p104 (* ABS((z * z + z * zh + zh * zh) * Wz + zh * zh * zh * D, [0, 6.15173e-05]) *).
Proof.
 intros h0.
 assert (h1 := l89 h0).
 assert (h2 := l115 h0).
 apply t128. exact h1. exact h2.
Qed.
Lemma t129 : p97 -> p104 -> p103.
Proof.
 intros h0 h1.
 refine (mul_aa _dl r107 i79 i82 i81 h0 h1 _) ; finalize.
Qed.
Lemma l87 : s1 -> p103 (* ABS(dl * ((z * z + z * zh + zh * zh) * Wz + zh * zh * zh * D), [0, 6.8298e-21]) *).
Proof.
 intros h0.
 assert (h1 := l82 h0).
 assert (h2 := l88 h0).
 apply t129. exact h1. exact h2.
Qed.
Lemma t130 : p103 -> p102.
Proof.
 intros h0.
 refine (neg_a r106 i81 h0) ; finalize.
Qed.
Lemma l86 : s1 -> p102 (* ABS(-(dl * ((z * z + z * zh + zh * zh) * Wz + zh * zh * zh * D)), [0, 6.8298e-21]) *).
Proof.
 intros h0.
 assert (h1 := l87 h0).
 apply t130. exact h1.
Qed.
Lemma t131 : p101 -> p102 -> p100.
Proof.
 intros h0 h1.
 refine (abs_rewrite r94 r105 i81 h0 h1) ; finalize.
Qed.
Lemma l84 : s1 -> p100 (* ABS((T - Tz) / zh, [0, 6.8298e-21]) *).
Proof.
 intros h0.
 assert (h1 := l85 h0).
 assert (h2 := l86 h0).
 apply t131. exact h1. exact h2.
Qed.
Lemma t132 : p94 -> p100 -> p93.
Proof.
 intros h0 h1.
 refine (add_aa_o r92 r94 i76 i81 i75 h0 h1 _) ; finalize.
Qed.
Lemma l78 : s1 -> p93 (* ABS(zl * dl / 2 + (T - Tz) / zh, [0, 6.8298e-21]) *).
Proof.
 intros h0.
 assert (h1 := l79 h0).
 assert (h2 := l84 h0).
 apply t132. exact h1. exact h2.
Qed.
Definition f212 := Float2 (1731694750002512397727212736543421266198645374487880900363545928131761990368784918074621105006866037418731420516028080011) (-465).
Definition i185 := makepairF f15 f212.
Notation p214 := (ABS r96 i185). (* ABS(zh * zh * W * et, [0, 1.8177e-20]) *)
Definition f213 := Float2 (5) (-132).
Definition f214 := Float2 (1731694750002512397727212736543421266198645374487880900363545928131761990368784918074621105006866037418731420516028080011) (-415).
Definition i186 := makepairF f213 f214.
Notation p215 := (ABS r97 i186). (* ABS(zh * zh * W, [9.18355e-40, 2.04655e-05]) *)
Definition f215 := Float2 (1731650419468060410655052949506190032486719539545044417867388445564162624884355474113431000294513962773031263254955310981) (-401).
Definition i187 := makepairF f87 f215.
Notation p216 := (ABS _W i187). (* ABS(W, [0.3125, 0.335299]) *)
Definition f216 := Float2 (1) (-67).
Definition f217 := Float2 (10150500743454779780215834423828433384452981912517942503823423215444365939329652148787268461289078066535528195027255173) (-401).
Definition i188 := makepairF f216 f217.
Notation p217 := (ABS r52 i188). (* ABS(zh * (c4 + zh * (c5 + zh * (c6 + zh * (c7 + zh * (c8 + zh * c9))))), [6.77626e-21, 0.00196544]) *)
Definition f218 := Float2 (162405933099332805023549049353423210334155433410739422596565535408256629344418825819625804170331868816647598031181283645) (-398).
Definition i189 := makepairF f61 f218.
Notation p218 := (ABS r53 i189). (* ABS(c4 + zh * (c5 + zh * (c6 + zh * (c7 + zh * (c8 + zh * c9)))), [0.125, 0.251573]) *)
Definition f219 := Float2 (1015315718899405553839733084203366830106812079032705459891316676801024976213557225125719874442580120108494225761206589) (-398).
Definition i190 := makepairF f216 f219.
Notation p219 := (ABS r54 i190). (* ABS(zh * (c5 + zh * (c6 + zh * (c7 + zh * (c8 + zh * c9)))), [6.77626e-21, 0.00157276]) *)
Definition f220 := Float2 (8122421784196406716711890761425188398442996561905651286794062450408834576625876989780289807831100722778702238700997337) (-394).
Definition i191 := makepairF f61 f220.
Notation p220 := (ABS r55 i191). (* ABS(c5 + zh * (c6 + zh * (c7 + zh * (c8 + zh * c9))), [0.125, 0.201311]) *)
Definition f221 := Float2 (52890915076849371192966668283046375601005808678292349997360326308110804554721325462918012967048651371559440917138137) (-394).
Definition i192 := makepairF f216 f221.
Notation p221 := (ABS r56 i192). (* ABS(zh * (c6 + zh * (c7 + zh * (c8 + zh * c9))), [6.77626e-21, 0.00131088]) *)
Definition f222 := Float2 (52890238081801924128337825558879221946964887527731995027823970161292740007649227552805337058734299572524912598256879) (-387).
Definition i193 := makepairF f61 f222.
Notation p222 := (ABS r57 i193). (* ABS(c6 + zh * (c7 + zh * (c8 + zh * c9)), [0.125, 0.16779]) *)
Definition f223 := Float2 (354229922881823467968800374833230142330653712690526501031117381086346515004260378828982682152705810778567974784239) (-387).
Definition i194 := makepairF f216 f223.
Notation p223 := (ABS r58 i194). (* ABS(zh * (c7 + zh * (c8 + zh * c9)), [6.77626e-21, 0.00112377]) *)
Definition f224 := Float2 (5667606220749549893262172241526990731809092246667666670364497431814417015530367272562634112726650071336174493514307) (-384).
Definition i195 := makepairF f61 f224.
Notation p224 := (ABS r59 i195). (* ABS(c7 + zh * (c8 + zh * c9), [0.125, 0.143841]) *)
Definition f225 := Float2 (1) (-68).
Definition f226 := Float2 (38751336796726753381191280131831977727879474583613369104169057019888245215431511034598079041709330990851161733699) (-384).
Definition i196 := makepairF f225 f226.
Notation p225 := (ABS r60 i196). (* ABS(zh * (c8 + zh * c9), [3.38813e-21, 0.000983486]) *)
Definition f227 := Float2 (155003363143858772132481824759970983282931876806430354108143643840911817190466006173513295196658806730678494250069) (-379).
Definition i197 := makepairF f79 f227.
Notation p226 := (ABS r61 i197). (* ABS(c8 + zh * c9, [0.0625, 0.125885]) *)
Definition f228 := Float2 (1076115348255279509638431791571251833947241526454431504414388162361396155961447878021073305475054270585012438101) (-379).
Definition i198 := makepairF f225 f228.
Notation p227 := (ABS r62 i198). (* ABS(zh * c9, [3.38813e-21, 0.000873958]) *)
Lemma t133 : p188 -> p132 -> p227.
Proof.
 intros h0 h1.
 refine (mul_aa _zh _c9 i159 i51 i198 h0 h1 _) ; finalize.
Qed.
Lemma l171 : s1 -> p227 (* ABS(zh * c9, [3.38813e-21, 0.000873958]) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 assert (h2 := l114 h0).
 apply t133. refine (abs_subset _zh i1 i159 h1 _) ; finalize. exact h2.
Qed.
Lemma t134 : p130 -> p227 -> p226.
Proof.
 intros h0 h1.
 refine (add_aa_p _c8 r62 i105 i198 i197 h0 h1 _) ; finalize.
Qed.
Lemma l170 : s1 -> p226 (* ABS(c8 + zh * c9, [0.0625, 0.125885]) *).
Proof.
 intros h0.
 assert (h1 := l112 h0).
 assert (h2 := l171 h0).
 apply t134. exact h1. exact h2.
Qed.
Definition f229 := Float2 (19239507100621969268365701792898874825847873189027396789875802315625632869499944226420943533932118245960366364817) (-380).
Definition i199 := makepairF f1 f229.
Notation p228 := (ABS _zh i199). (* ABS(zh, [5.42101e-20, 0.0078126]) *)
Lemma t135 : p228 -> p226 -> p225.
Proof.
 intros h0 h1.
 refine (mul_aa _zh r61 i199 i197 i196 h0 h1 _) ; finalize.
Qed.
Lemma l169 : s1 -> p225 (* ABS(zh * (c8 + zh * c9), [3.38813e-21, 0.000983486]) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 assert (h2 := l170 h0).
 apply t135. refine (abs_subset _zh i1 i199 h1 _) ; finalize. exact h2.
Qed.
Lemma t136 : p127 -> p225 -> p224.
Proof.
 intros h0 h1.
 refine (add_aa_p _c7 r60 i46 i196 i195 h0 h1 _) ; finalize.
Qed.
Lemma l168 : s1 -> p224 (* ABS(c7 + zh * (c8 + zh * c9), [0.125, 0.143841]) *).
Proof.
 intros h0.
 assert (h1 := l109 h0).
 assert (h2 := l169 h0).
 apply t136. exact h1. exact h2.
Qed.
Lemma t137 : p165 -> p224 -> p223.
Proof.
 intros h0 h1.
 refine (mul_aa _zh r59 i136 i195 i194 h0 h1 _) ; finalize.
Qed.
Lemma l167 : s1 -> p223 (* ABS(zh * (c7 + zh * (c8 + zh * c9)), [6.77626e-21, 0.00112377]) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 assert (h2 := l168 h0).
 apply t137. refine (abs_subset _zh i1 i136 h1 _) ; finalize. exact h2.
Qed.
Lemma t138 : p124 -> p223 -> p222.
Proof.
 intros h0 h1.
 refine (add_aa_p _c6 r58 i100 i194 i193 h0 h1 _) ; finalize.
Qed.
Lemma l166 : s1 -> p222 (* ABS(c6 + zh * (c7 + zh * (c8 + zh * c9)), [0.125, 0.16779]) *).
Proof.
 intros h0.
 assert (h1 := l106 h0).
 assert (h2 := l167 h0).
 apply t138. exact h1. exact h2.
Qed.
Lemma t139 : p165 -> p222 -> p221.
Proof.
 intros h0 h1.
 refine (mul_aa _zh r57 i136 i193 i192 h0 h1 _) ; finalize.
Qed.
Lemma l165 : s1 -> p221 (* ABS(zh * (c6 + zh * (c7 + zh * (c8 + zh * c9))), [6.77626e-21, 0.00131088]) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 assert (h2 := l166 h0).
 apply t139. refine (abs_subset _zh i1 i136 h1 _) ; finalize. exact h2.
Qed.
Lemma t140 : p121 -> p221 -> p220.
Proof.
 intros h0 h1.
 refine (add_aa_p _c5 r56 i40 i192 i191 h0 h1 _) ; finalize.
Qed.
Lemma l164 : s1 -> p220 (* ABS(c5 + zh * (c6 + zh * (c7 + zh * (c8 + zh * c9))), [0.125, 0.201311]) *).
Proof.
 intros h0.
 assert (h1 := l103 h0).
 assert (h2 := l165 h0).
 apply t140. exact h1. exact h2.
Qed.
Lemma t141 : p141 -> p220 -> p219.
Proof.
 intros h0 h1.
 refine (mul_aa _zh r55 i114 i191 i190 h0 h1 _) ; finalize.
Qed.
Lemma l163 : s1 -> p219 (* ABS(zh * (c5 + zh * (c6 + zh * (c7 + zh * (c8 + zh * c9)))), [6.77626e-21, 0.00157276]) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 assert (h2 := l164 h0).
 apply t141. refine (abs_subset _zh i1 i114 h1 _) ; finalize. exact h2.
Qed.
Lemma t142 : p118 -> p219 -> p218.
Proof.
 intros h0 h1.
 refine (add_aa_p _c4 r54 i95 i190 i189 h0 h1 _) ; finalize.
Qed.
Lemma l162 : s1 -> p218 (* ABS(c4 + zh * (c5 + zh * (c6 + zh * (c7 + zh * (c8 + zh * c9)))), [0.125, 0.251573]) *).
Proof.
 intros h0.
 assert (h1 := l100 h0).
 assert (h2 := l163 h0).
 apply t142. exact h1. exact h2.
Qed.
Definition f230 := Float2 (20174085397541782047545834123190730569388259477057591616340809288909463611768773517163567287036404821876137121354287067) (-400).
Definition i200 := makepairF f1 f230.
Notation p229 := (ABS _zh i200). (* ABS(zh, [5.42101e-20, 0.0078126]) *)
Lemma t143 : p229 -> p218 -> p217.
Proof.
 intros h0 h1.
 refine (mul_aa _zh r53 i200 i189 i188 h0 h1 _) ; finalize.
Qed.
Lemma l161 : s1 -> p217 (* ABS(zh * (c4 + zh * (c5 + zh * (c6 + zh * (c7 + zh * (c8 + zh * c9))))), [6.77626e-21, 0.00196544]) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 assert (h2 := l162 h0).
 apply t143. refine (abs_subset _zh i1 i200 h1 _) ; finalize. exact h2.
Qed.
Lemma t144 : p115 -> p217 -> p216.
Proof.
 intros h0 h1.
 refine (add_aa_p _c3 r52 i34 i188 i187 h0 h1 _) ; finalize.
Qed.
Lemma l160 : s1 -> p216 (* ABS(W, [0.3125, 0.335299]) *).
Proof.
 intros h0.
 assert (h1 := l97 h0).
 assert (h2 := l161 h0).
 apply t144. exact h1. exact h2.
Qed.
Lemma t145 : p112 -> p216 -> p215.
Proof.
 intros h0 h1.
 refine (mul_aa r42 _W i90 i187 i186 h0 h1 _) ; finalize.
Qed.
Lemma l159 : s1 -> p215 (* ABS(zh * zh * W, [9.18355e-40, 2.04655e-05]) *).
Proof.
 intros h0.
 assert (h1 := l95 h0).
 assert (h2 := l160 h0).
 apply t145. exact h1. exact h2.
Qed.
Definition i201 := makepairF f15 f6.
Notation p230 := (ABS _et i201). (* ABS(et, [0, 8.88178e-16]) *)
Lemma l173 : s1 -> p3 (* BND(et, [-8.88178e-16, 8.88178e-16]) *).
Proof.
 intros h0.
 assert (h1 := l10 h0).
 exact (proj2 h1).
Qed.
Lemma t146 : p3 -> p230.
Proof.
 intros h0.
 refine (abs_of_bnd_o _et i3 i201 h0 _) ; finalize.
Qed.
Lemma l172 : s1 -> p230 (* ABS(et, [0, 8.88178e-16]) *).
Proof.
 intros h0.
 assert (h1 := l173 h0).
 apply t146. exact h1.
Qed.
Definition f231 := Float2 (1) (-130).
Definition i202 := makepairF f231 f214.
Notation p231 := (ABS r97 i202). (* ABS(zh * zh * W, [7.34684e-40, 2.04655e-05]) *)
Lemma t147 : p231 -> p230 -> p214.
Proof.
 intros h0 h1.
 refine (mul_aa r97 _et i202 i201 i185 h0 h1 _) ; finalize.
Qed.
Lemma l158 : s1 -> p214 (* ABS(zh * zh * W * et, [0, 1.8177e-20]) *).
Proof.
 intros h0.
 assert (h1 := l159 h0).
 assert (h2 := l172 h0).
 apply t147. refine (abs_subset r97 i186 i202 h1 _) ; finalize. exact h2.
Qed.
Lemma t148 : p93 -> p214 -> p92.
Proof.
 intros h0 h1.
 refine (add_aa_o r91 r96 i75 i185 i74 h0 h1 _) ; finalize.
Qed.
Lemma l77 : s1 -> p92 (* ABS(zl * dl / 2 + (T - Tz) / zh + zh * zh * W * et, [0, 2.50068e-20]) *).
Proof.
 intros h0.
 assert (h1 := l78 h0).
 assert (h2 := l158 h0).
 apply t148. exact h1. exact h2.
Qed.
Notation p232 := (ABS r98 i77). (* ABS(zl * ec, [0, 9.62977e-35]) *)
Notation p233 := (ABS _ec i79). (* ABS(ec, [0, 1.11022e-16]) *)
Lemma l176 : s1 -> p4 (* BND(ec, [-1.11022e-16, 1.11022e-16]) *).
Proof.
 intros h0.
 assert (h1 := l11 h0).
 exact (proj2 h1).
Qed.
Lemma t149 : p4 -> p233.
Proof.
 intros h0.
 refine (abs_of_bnd_o _ec i2 i79 h0 _) ; finalize.
Qed.
Lemma l175 : s1 -> p233 (* ABS(ec, [0, 1.11022e-16]) *).
Proof.
 intros h0.
 assert (h1 := l176 h0).
 apply t149. exact h1.
Qed.
Lemma t150 : p96 -> p233 -> p232.
Proof.
 intros h0 h1.
 refine (mul_aa _zl _ec i78 i79 i77 h0 h1 _) ; finalize.
Qed.
Lemma l174 : s1 -> p232 (* ABS(zl * ec, [0, 9.62977e-35]) *).
Proof.
 intros h0.
 assert (h1 := l81 h0).
 assert (h2 := l175 h0).
 apply t150. exact h1. exact h2.
Qed.
Lemma t151 : p92 -> p232 -> p91.
Proof.
 intros h0 h1.
 refine (sub_aa_o r90 r98 i74 i77 i73 h0 h1 _) ; finalize.
Qed.
Lemma l76 : s1 -> p91 (* ABS(zl * dl / 2 + (T - Tz) / zh + zh * zh * W * et - zl * ec, [0, 2.50068e-20]) *).
Proof.
 intros h0.
 assert (h1 := l77 h0).
 assert (h2 := l174 h0).
 apply t151. exact h1. exact h2.
Qed.
Definition f232 := Float2 (108230921875161708042265494511523186165703145515081826372317729551240352234745641646519936380993297507633642543237379011) (-464).
Definition i203 := makepairF f15 f232.
Notation p234 := (ABS r99 i203). (* ABS((t - c) / zh * eu, [0, 2.27213e-21]) *)
Definition f233 := Float2 (108230921875161708042265494511523186165703145515081826372317729551240352234745641646519936380993297507633642543237379011) (-411).
Definition i204 := makepairF f15 f233.
Notation p235 := (ABS r100 i204). (* ABS((t - c) / zh, [0, 2.04655e-05]) *)
Notation p236 := (r100 = r155). (* EQL((t - c) / zh, zh * zh * W * (1 + et) - zl * (1 + ec)) *)
Lemma t152 : p13 -> p236.
Proof.
 intros h0.
 refine (b6 h0) ; finalize.
Qed.
Lemma l179 : s1 -> p236 (* EQL((t - c) / zh, zh * zh * W * (1 + et) - zl * (1 + ec)) *).
Proof.
 intros h0.
 assert (h1 := l6 h0).
 apply t152. exact h1.
Qed.
Notation p237 := (ABS r155 i204). (* ABS(zh * zh * W * (1 + et) - zl * (1 + ec), [0, 2.04655e-05]) *)
Definition f234 := Float2 (6764432617197320061644996862415304269629798789346513754801173863500743614141828107425468539720244570310872119563858941) (-407).
Definition i205 := makepairF f231 f234.
Notation p238 := (ABS r156 i205). (* ABS(zh * zh * W * (1 + et), [7.34684e-40, 2.04655e-05]) *)
Definition f235 := Float2 (7) (-3).
Definition f236 := Float2 (1125899906842625) (-50).
Definition i206 := makepairF f235 f236.
Notation p239 := (ABS r63 i206). (* ABS(1 + et, [0.875, 1]) *)
Notation p240 := (ABS r44 i16). (* ABS(1, [1, 1]) *)
Lemma t153 : p25 -> p240.
Proof.
 intros h0.
 refine (abs_of_bnd_p r44 i16 i16 h0 _) ; finalize.
Qed.
Lemma l183 : s1 -> p240 (* ABS(1, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l25 h0).
 apply t153. exact h1.
Qed.
Lemma t154 : p240 -> p230 -> p239.
Proof.
 intros h0 h1.
 refine (add_aa_p r44 _et i16 i201 i206 h0 h1 _) ; finalize.
Qed.
Lemma l182 : s1 -> p239 (* ABS(1 + et, [0.875, 1]) *).
Proof.
 intros h0.
 assert (h1 := l183 h0).
 assert (h2 := l172 h0).
 apply t154. exact h1. exact h2.
Qed.
Definition f237 := Float2 (432923687500628099431803184135855316549661343621970225090886482032940497592196229518655276251716509354682855129007020003) (-413).
Definition i207 := makepairF f213 f237.
Notation p241 := (ABS r97 i207). (* ABS(zh * zh * W, [9.18355e-40, 2.04655e-05]) *)
Lemma t155 : p241 -> p239 -> p238.
Proof.
 intros h0 h1.
 refine (mul_aa r97 r63 i207 i206 i205 h0 h1 _) ; finalize.
Qed.
Lemma l181 : s1 -> p238 (* ABS(zh * zh * W * (1 + et), [7.34684e-40, 2.04655e-05]) *).
Proof.
 intros h0.
 assert (h1 := l159 h0).
 assert (h2 := l182 h0).
 apply t155. refine (abs_subset r97 i186 i207 h1 _) ; finalize. exact h2.
Qed.
Definition f238 := Float2 (4587055945544712878317851626364885537606295498947735228454408476391927712439745469384382659688630215635955) (-411).
Definition i208 := makepairF f15 f238.
Notation p242 := (ABS r157 i208). (* ABS(zl * (1 + ec), [0, 8.67373e-19]) *)
Notation p243 := (ABS r67 i22). (* ABS(1 + ec, [0.5, 1]) *)
Lemma t156 : p240 -> p233 -> p243.
Proof.
 intros h0 h1.
 refine (add_aa_p r44 _ec i16 i79 i22 h0 h1 _) ; finalize.
Qed.
Lemma l185 : s1 -> p243 (* ABS(1 + ec, [0.5, 1]) *).
Proof.
 intros h0.
 assert (h1 := l183 h0).
 assert (h2 := l175 h0).
 apply t156. exact h1. exact h2.
Qed.
Lemma t157 : p96 -> p243 -> p242.
Proof.
 intros h0 h1.
 refine (mul_aa _zl r67 i78 i22 i208 h0 h1 _) ; finalize.
Qed.
Lemma l184 : s1 -> p242 (* ABS(zl * (1 + ec), [0, 8.67373e-19]) *).
Proof.
 intros h0.
 assert (h1 := l81 h0).
 assert (h2 := l185 h0).
 apply t157. exact h1. exact h2.
Qed.
Lemma t158 : p238 -> p242 -> p237.
Proof.
 intros h0 h1.
 refine (sub_aa_o r156 r157 i205 i208 i204 h0 h1 _) ; finalize.
Qed.
Lemma l180 : s1 -> p237 (* ABS(zh * zh * W * (1 + et) - zl * (1 + ec), [0, 2.04655e-05]) *).
Proof.
 intros h0.
 assert (h1 := l181 h0).
 assert (h2 := l184 h0).
 apply t158. exact h1. exact h2.
Qed.
Lemma t159 : p236 -> p237 -> p235.
Proof.
 intros h0 h1.
 refine (abs_rewrite r100 r155 i204 h0 h1) ; finalize.
Qed.
Lemma l178 : s1 -> p235 (* ABS((t - c) / zh, [0, 2.04655e-05]) *).
Proof.
 intros h0.
 assert (h1 := l179 h0).
 assert (h2 := l180 h0).
 apply t159. exact h1. exact h2.
Qed.
Notation p244 := (ABS _eu i79). (* ABS(eu, [0, 1.11022e-16]) *)
Lemma l187 : s1 -> p5 (* BND(eu, [-1.11022e-16, 1.11022e-16]) *).
Proof.
 intros h0.
 assert (h1 := l12 h0).
 exact (proj2 h1).
Qed.
Lemma t160 : p5 -> p244.
Proof.
 intros h0.
 refine (abs_of_bnd_o _eu i2 i79 h0 _) ; finalize.
Qed.
Lemma l186 : s1 -> p244 (* ABS(eu, [0, 1.11022e-16]) *).
Proof.
 intros h0.
 assert (h1 := l187 h0).
 apply t160. exact h1.
Qed.
Lemma t161 : p235 -> p244 -> p234.
Proof.
 intros h0 h1.
 refine (mul_aa r100 _eu i204 i79 i203 h0 h1 _) ; finalize.
Qed.
Lemma l177 : s1 -> p234 (* ABS((t - c) / zh * eu, [0, 2.27213e-21]) *).
Proof.
 intros h0.
 assert (h1 := l178 h0).
 assert (h2 := l186 h0).
 apply t161. exact h1. exact h2.
Qed.
Lemma t162 : p91 -> p234 -> p90.
Proof.
 intros h0 h1.
 refine (add_aa_o r89 r99 i73 i203 i72 h0 h1 _) ; finalize.
Qed.
Lemma l75 : s1 -> p90 (* ABS(zl * dl / 2 + (T - Tz) / zh + zh * zh * W * et - zl * ec + (t - c) / zh * eu, [0, 2.7279e-20]) *).
Proof.
 intros h0.
 assert (h1 := l76 h0).
 assert (h2 := l177 h0).
 apply t162. exact h1. exact h2.
Qed.
Definition f239 := Float2 (56546428909383816037771109168080704732636765126405493550280679451527620790880380317935526109272003710025502869251855711) (-464).
Definition i209 := makepairF f15 f239.
Notation p245 := (ABS r84 i209). (* ABS(al * (Tz / zh), [0, 1.1871e-21]) *)
Definition i210 := makepairF f15 f8.
Notation p246 := (ABS _al i210). (* ABS(al, [0, 5.80048e-17]) *)
Lemma t163 : p6 -> p246.
Proof.
 intros h0.
 refine (abs_of_bnd_o _al i4 i210 h0 _) ; finalize.
Qed.
Lemma l189 : s1 -> p246 (* ABS(al, [0, 5.80048e-17]) *).
Proof.
 intros h0.
 assert (h1 := l61 h0).
 apply t163. exact h1.
Qed.
Definition f240 := Float2 (54115460937578530488483753073004337987121539709756285416343379213424564196132251818285961435415450279501041998237289951) (-410).
Definition i211 := makepairF f15 f240.
Notation p247 := (ABS r83 i211). (* ABS(Tz / zh, [0, 2.04655e-05]) *)
Notation p248 := (ABS r152 i211). (* ABS((1 + dl) * z * z * Wz, [0, 2.04655e-05]) *)
Definition f241 := Float2 (1291157992053432147312786095383006472039902443055273374556547204709405520982450082989690130095813452107669497223423274663) (-413).
Definition i212 := makepairF f15 f241.
Notation p249 := (ABS r153 i212). (* ABS((1 + dl) * z * z, [0, 6.10367e-05]) *)
Definition f242 := Float2 (645570732721337168866964990214372868379653271765517191490247605807918209425879462550199306971773559542323237630856060555) (-405).
Definition i213 := makepairF f15 f242.
Notation p250 := (ABS r154 i213). (* ABS((1 + dl) * z, [0, 0.0078126]) *)
Definition f243 := Float2 (15) (-4).
Definition i214 := makepairF f243 f29.
Notation p251 := (ABS r79 i214). (* ABS(1 + dl, [0.9375, 1]) *)
Lemma t164 : p240 -> p97 -> p251.
Proof.
 intros h0 h1.
 refine (add_aa_p r44 _dl i16 i79 i214 h0 h1 _) ; finalize.
Qed.
Lemma l194 : s1 -> p251 (* ABS(1 + dl, [0.9375, 1]) *).
Proof.
 intros h0.
 assert (h1 := l183 h0).
 assert (h2 := l82 h0).
 apply t164. exact h1. exact h2.
Qed.
Notation p252 := (ABS r79 i22). (* ABS(1 + dl, [0.5, 1]) *)
Lemma t165 : p252 -> p109 -> p250.
Proof.
 intros h0 h1.
 refine (mul_aa r79 _z i22 i87 i213 h0 h1 _) ; finalize.
Qed.
Lemma l193 : s1 -> p250 (* ABS((1 + dl) * z, [0, 0.0078126]) *).
Proof.
 intros h0.
 assert (h1 := l194 h0).
 assert (h2 := l93 h0).
 apply t165. refine (abs_subset r79 i214 i22 h1 _) ; finalize. exact h2.
Qed.
Lemma t166 : p250 -> p109 -> p249.
Proof.
 intros h0 h1.
 refine (mul_aa r154 _z i213 i87 i212 h0 h1 _) ; finalize.
Qed.
Lemma l192 : s1 -> p249 (* ABS((1 + dl) * z * z, [0, 6.10367e-05]) *).
Proof.
 intros h0.
 assert (h1 := l193 h0).
 assert (h2 := l93 h0).
 apply t166. exact h1. exact h2.
Qed.
Lemma t167 : p249 -> p114 -> p248.
Proof.
 intros h0 h1.
 refine (mul_aa r153 _Wz i212 i92 i211 h0 h1 _) ; finalize.
Qed.
Lemma l191 : s1 -> p248 (* ABS((1 + dl) * z * z * Wz, [0, 2.04655e-05]) *).
Proof.
 intros h0.
 assert (h1 := l192 h0).
 assert (h2 := l96 h0).
 apply t167. exact h1. exact h2.
Qed.
Lemma t168 : p70 -> p248 -> p247.
Proof.
 intros h0 h1.
 refine (abs_rewrite r83 r152 i211 h0 h1) ; finalize.
Qed.
Lemma l190 : s1 -> p247 (* ABS(Tz / zh, [0, 2.04655e-05]) *).
Proof.
 intros h0.
 assert (h1 := l58 h0).
 assert (h2 := l191 h0).
 apply t168. exact h1. exact h2.
Qed.
Lemma t169 : p246 -> p247 -> p245.
Proof.
 intros h0 h1.
 refine (mul_aa _al r83 i210 i211 i209 h0 h1 _) ; finalize.
Qed.
Lemma l188 : s1 -> p245 (* ABS(al * (Tz / zh), [0, 1.1871e-21]) *).
Proof.
 intros h0.
 assert (h1 := l189 h0).
 assert (h2 := l190 h0).
 apply t169. exact h1. exact h2.
Qed.
Lemma t170 : p90 -> p245 -> p89.
Proof.
 intros h0 h1.
 refine (sub_aa_o r88 r84 i72 i209 i71 h0 h1 _) ; finalize.
Qed.
Lemma l74 : s1 -> p89 (* ABS(zl * dl / 2 + (T - Tz) / zh + zh * zh * W * et - zl * ec + (t - c) / zh * eu - al * (Tz / zh), [0, 2.84661e-20]) *).
Proof.
 intros h0.
 assert (h1 := l75 h0).
 assert (h2 := l188 h0).
 apply t170. exact h1. exact h2.
Qed.
Definition f244 := Float2 (1786707182675761895286831670538305022857629097834405705898440292147907041731038610244993271112952961716179039) (-464).
Definition i215 := makepairF f15 f244.
Notation p253 := (ABS r101 i215). (* ABS((z + B) / zh * d1, [0, 3.7509e-32]) *)
Definition f245 := Float2 (147357293416557682085511890353674641060423018378095315950386828218384085915961947236700475968078594780715797) (-356).
Definition i216 := makepairF f235 f245.
Notation p254 := (ABS r102 i216). (* ABS((z + B) / zh, [0.875, 1.00391]) *)
Notation p255 := (r102 = r158). (* EQL((z + B) / zh, 1 + dl - zh / 2) *)
Lemma t171 : p13 -> p255.
Proof.
 intros h0.
 refine (b7 h0) ; finalize.
Qed.
Lemma l197 : s1 -> p255 (* EQL((z + B) / zh, 1 + dl - zh / 2) *).
Proof.
 intros h0.
 assert (h1 := l6 h0).
 apply t171. exact h1.
Qed.
Notation p256 := (ABS r158 i216). (* ABS(1 + dl - zh / 2, [0.875, 1.00391]) *)
Definition f246 := Float2 (573381993193089046131542378452386701877351796300035619433993170131016757175324685168890462336901374040853) (-356).
Definition i217 := makepairF f19 f246.
Notation p257 := (ABS r159 i217). (* ABS(zh / 2, [2.71051e-20, 0.0039063]) *)
Lemma t172 : p98 -> p99 -> p257.
Proof.
 intros h0 h1.
 refine (div_aa _zh r10 i80 i23 i217 h0 h1 _) ; finalize.
Qed.
Lemma l199 : s1 -> p257 (* ABS(zh / 2, [2.71051e-20, 0.0039063]) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 assert (h2 := l83 h0).
 apply t172. refine (abs_subset _zh i1 i80 h1 _) ; finalize. exact h2.
Qed.
Lemma t173 : p251 -> p257 -> p256.
Proof.
 intros h0 h1.
 refine (sub_aa_p r79 r159 i214 i217 i216 h0 h1 _) ; finalize.
Qed.
Lemma l198 : s1 -> p256 (* ABS(1 + dl - zh / 2, [0.875, 1.00391]) *).
Proof.
 intros h0.
 assert (h1 := l194 h0).
 assert (h2 := l199 h0).
 apply t173. exact h1. exact h2.
Qed.
Lemma t174 : p255 -> p256 -> p254.
Proof.
 intros h0 h1.
 refine (abs_rewrite r102 r158 i216 h0 h1) ; finalize.
Qed.
Lemma l196 : s1 -> p254 (* ABS((z + B) / zh, [0.875, 1.00391]) *).
Proof.
 intros h0.
 assert (h1 := l197 h0).
 assert (h2 := l198 h0).
 apply t174. exact h1. exact h2.
Qed.
Definition i218 := makepairF f15 f10.
Notation p258 := (ABS _d1 i218). (* ABS(d1, [0, 3.7363e-32]) *)
Lemma l201 : s1 -> p7 (* BND(d1, [-3.7363e-32, 3.7363e-32]) *).
Proof.
 intros h0.
 assert (h1 := l14 h0).
 exact (proj2 h1).
Qed.
Lemma t175 : p7 -> p258.
Proof.
 intros h0.
 refine (abs_of_bnd_o _d1 i5 i218 h0 _) ; finalize.
Qed.
Lemma l200 : s1 -> p258 (* ABS(d1, [0, 3.7363e-32]) *).
Proof.
 intros h0.
 assert (h1 := l201 h0).
 apply t175. exact h1.
Qed.
Definition i219 := makepairF f37 f245.
Notation p259 := (ABS r102 i219). (* ABS((z + B) / zh, [0.5, 1.00391]) *)
Lemma t176 : p259 -> p258 -> p253.
Proof.
 intros h0 h1.
 refine (mul_aa r102 _d1 i219 i218 i215 h0 h1 _) ; finalize.
Qed.
Lemma l195 : s1 -> p253 (* ABS((z + B) / zh * d1, [0, 3.7509e-32]) *).
Proof.
 intros h0.
 assert (h1 := l196 h0).
 assert (h2 := l200 h0).
 apply t176. refine (abs_subset r102 i216 i219 h1 _) ; finalize. exact h2.
Qed.
Lemma t177 : p89 -> p253 -> p88.
Proof.
 intros h0 h1.
 refine (add_aa_o r87 r101 i71 i215 i70 h0 h1 _) ; finalize.
Qed.
Lemma l73 : s1 -> p88 (* ABS(zl * dl / 2 + (T - Tz) / zh + zh * zh * W * et - zl * ec + (t - c) / zh * eu - al * (Tz / zh) + (z + B) / zh * d1, [0, 2.84661e-20]) *).
Proof.
 intros h0.
 assert (h1 := l74 h0).
 assert (h2 := l195 h0).
 apply t177. exact h1. exact h2.
Qed.
Definition f247 := Float2 (294720594856187474724224706540495954493178192090062978104526764453669193532853992841349969285116387184937121) (-462).
Definition i220 := makepairF f15 f247.
Notation p260 := (ABS r103 i220). (* ABS((P1 + u) / zh * d2, [0, 2.47487e-32]) *)
Definition f248 := Float2 (294720594856187474724224706540495954493178192090062978104526764453669193532853992841349969285116387184937121) (-357).
Definition i221 := makepairF f37 f248.
Notation p261 := (ABS r104 i221). (* ABS((P1 + u) / zh, [0.5, 1.00393]) *)
Notation p262 := (r104 = r162). (* EQL((P1 + u) / zh, (z + B) / zh * (1 + d1) + u / zh) *)
Lemma t178 : p13 -> p262.
Proof.
 intros h0.
 refine (b9 h0) ; finalize.
Qed.
Lemma l204 : s1 -> p262 (* EQL((P1 + u) / zh, (z + B) / zh * (1 + d1) + u / zh) *).
Proof.
 intros h0.
 assert (h1 := l6 h0).
 apply t178. exact h1.
Qed.
Notation p263 := (ABS r162 i221). (* ABS((z + B) / zh * (1 + d1) + u / zh, [0.5, 1.00393]) *)
Definition f249 := Float2 (3) (-2).
Definition f250 := Float2 (1178858347332461456684095122829441174216055724688214582556761332412412730895421343343867017588928659005654493) (-359).
Definition i222 := makepairF f249 f250.
Notation p264 := (ABS r163 i222). (* ABS((z + B) / zh * (1 + d1), [0.75, 1.00391]) *)
Definition f251 := Float2 (2596148429267413814265248164610145) (-111).
Definition i223 := makepairF f235 f251.
Notation p265 := (ABS r43 i223). (* ABS(1 + d1, [0.875, 1]) *)
Lemma t179 : p240 -> p258 -> p265.
Proof.
 intros h0 h1.
 refine (add_aa_p r44 _d1 i16 i218 i223 h0 h1 _) ; finalize.
Qed.
Lemma l207 : s1 -> p265 (* ABS(1 + d1, [0.875, 1]) *).
Proof.
 intros h0.
 assert (h1 := l183 h0).
 assert (h2 := l200 h0).
 apply t179. exact h1. exact h2.
Qed.
Lemma t180 : p254 -> p265 -> p264.
Proof.
 intros h0 h1.
 refine (mul_aa r102 r43 i216 i223 i222 h0 h1 _) ; finalize.
Qed.
Lemma l206 : s1 -> p264 (* ABS((z + B) / zh * (1 + d1), [0.75, 1.00391]) *).
Proof.
 intros h0.
 assert (h1 := l196 h0).
 assert (h2 := l207 h0).
 apply t180. exact h1. exact h2.
Qed.
Definition f252 := Float2 (24032092288442212803703332542643756657043672037329861345725402264043235994628021532859551536889734093991) (-359).
Definition i224 := makepairF f15 f252.
Notation p266 := (ABS r160 i224). (* ABS(u / zh, [0, 2.04655e-05]) *)
Notation p267 := (r160 = r161). (* EQL(u / zh, (t - c) / zh * (1 + eu)) *)
Lemma t181 : p13 -> p267.
Proof.
 intros h0.
 refine (b8 h0) ; finalize.
Qed.
Lemma l209 : s1 -> p267 (* EQL(u / zh, (t - c) / zh * (1 + eu)) *).
Proof.
 intros h0.
 assert (h1 := l6 h0).
 apply t181. exact h1.
Qed.
Notation p268 := (ABS r161 i224). (* ABS((t - c) / zh * (1 + eu), [0, 2.04655e-05]) *)
Notation p269 := (ABS r69 i22). (* ABS(1 + eu, [0.5, 1]) *)
Lemma t182 : p240 -> p244 -> p269.
Proof.
 intros h0 h1.
 refine (add_aa_p r44 _eu i16 i79 i22 h0 h1 _) ; finalize.
Qed.
Lemma l211 : s1 -> p269 (* ABS(1 + eu, [0.5, 1]) *).
Proof.
 intros h0.
 assert (h1 := l183 h0).
 assert (h2 := l186 h0).
 apply t182. exact h1. exact h2.
Qed.
Definition f253 := Float2 (24032092288442210135605113688122710639150790948877351199079506105791360023259537836208807078051851726127) (-359).
Definition i225 := makepairF f15 f253.
Notation p270 := (ABS r100 i225). (* ABS((t - c) / zh, [0, 2.04655e-05]) *)
Lemma t183 : p270 -> p269 -> p268.
Proof.
 intros h0 h1.
 refine (mul_aa r100 r69 i225 i22 i224 h0 h1 _) ; finalize.
Qed.
Lemma l210 : s1 -> p268 (* ABS((t - c) / zh * (1 + eu), [0, 2.04655e-05]) *).
Proof.
 intros h0.
 assert (h1 := l178 h0).
 assert (h2 := l211 h0).
 apply t183. refine (abs_subset r100 i204 i225 h1 _) ; finalize. exact h2.
Qed.
Lemma t184 : p267 -> p268 -> p266.
Proof.
 intros h0 h1.
 refine (abs_rewrite r160 r161 i224 h0 h1) ; finalize.
Qed.
Lemma l208 : s1 -> p266 (* ABS(u / zh, [0, 2.04655e-05]) *).
Proof.
 intros h0.
 assert (h1 := l209 h0).
 assert (h2 := l210 h0).
 apply t184. exact h1. exact h2.
Qed.
Lemma t185 : p264 -> p266 -> p263.
Proof.
 intros h0 h1.
 refine (add_aa_p r163 r160 i222 i224 i221 h0 h1 _) ; finalize.
Qed.
Lemma l205 : s1 -> p263 (* ABS((z + B) / zh * (1 + d1) + u / zh, [0.5, 1.00393]) *).
Proof.
 intros h0.
 assert (h1 := l206 h0).
 assert (h2 := l208 h0).
 apply t185. exact h1. exact h2.
Qed.
Lemma t186 : p262 -> p263 -> p261.
Proof.
 intros h0 h1.
 refine (abs_rewrite r104 r162 i221 h0 h1) ; finalize.
Qed.
Lemma l203 : s1 -> p261 (* ABS((P1 + u) / zh, [0.5, 1.00393]) *).
Proof.
 intros h0.
 assert (h1 := l204 h0).
 assert (h2 := l205 h0).
 apply t186. exact h1. exact h2.
Qed.
Definition i226 := makepairF f15 f12.
Notation p271 := (ABS _d2 i226). (* ABS(d2, [0, 2.46519e-32]) *)
Lemma l213 : s1 -> p8 (* BND(d2, [-2.46519e-32, 2.46519e-32]) *).
Proof.
 intros h0.
 assert (h1 := l15 h0).
 exact (proj2 h1).
Qed.
Lemma t187 : p8 -> p271.
Proof.
 intros h0.
 refine (abs_of_bnd_o _d2 i6 i226 h0 _) ; finalize.
Qed.
Lemma l212 : s1 -> p271 (* ABS(d2, [0, 2.46519e-32]) *).
Proof.
 intros h0.
 assert (h1 := l213 h0).
 apply t187. exact h1.
Qed.
Lemma t188 : p261 -> p271 -> p260.
Proof.
 intros h0 h1.
 refine (mul_aa r104 _d2 i221 i226 i220 h0 h1 _) ; finalize.
Qed.
Lemma l202 : s1 -> p260 (* ABS((P1 + u) / zh * d2, [0, 2.47487e-32]) *).
Proof.
 intros h0.
 assert (h1 := l203 h0).
 assert (h2 := l212 h0).
 apply t188. exact h1. exact h2.
Qed.
Lemma t189 : p88 -> p260 -> p87.
Proof.
 intros h0 h1.
 refine (add_aa_o r86 r103 i70 i220 i69 h0 h1 _) ; finalize.
Qed.
Lemma l72 : s1 -> p87 (* ABS(zl * dl / 2 + (T - Tz) / zh + zh * zh * W * et - zl * ec + (t - c) / zh * eu - al * (Tz / zh) + (z + B) / zh * d1 + (P1 + u) / zh * d2, [0, 2.84661e-20]) *).
Proof.
 intros h0.
 assert (h1 := l73 h0).
 assert (h2 := l202 h0).
 apply t189. exact h1. exact h2.
Qed.
Lemma t190 : p86 -> p87 -> p85.
Proof.
 intros h0 h1.
 refine (abs_rewrite r74 r85 i69 h0 h1) ; finalize.
Qed.
Lemma l70 : s1 -> p85 (* ABS((P - L) / zh, [0, 2.84661e-20]) *).
Proof.
 intros h0.
 assert (h1 := l71 h0).
 assert (h2 := l72 h0).
 apply t190. exact h1. exact h2.
Qed.
Lemma t191 : p85 -> p84.
Proof.
 intros h0.
 refine (bnd_of_abs r74 i69 i68 h0 _) ; finalize.
Qed.
Lemma l69 : s1 -> p84 (* BND((P - L) / zh, [-2.84661e-20, 2.84661e-20]) *).
Proof.
 intros h0.
 assert (h1 := l70 h0).
 apply t191. exact h1.
Qed.
Lemma t192 : p84 -> p20 -> p83.
Proof.
 intros h0 h1.
 refine (div_op r74 r75 i68 i12 i8 h0 h1 _) ; finalize.
Qed.
Lemma l68 : s1 -> p83 (* BND((P - L) / zh / (L / zh), [-2.85783e-20, 2.85783e-20]) *).
Proof.
 intros h0.
 assert (h1 := l69 h0).
 assert (h2 := l20 h0).
 apply t192. exact h1. exact h2.
Qed.
Lemma t193 : p12 -> p83 -> p11.
Proof.
 intros h0 h1.
 refine (bnd_rewrite r34 r73 i8 h0 h1) ; finalize.
Qed.
Lemma l4 : p10 -> s1 -> p11 (* BND((P - L) / L, [-2.85783e-20, 2.85783e-20]) *).
Proof.
 intros h0 h1.
 assert (h2 := l5 h0 h1).
 assert (h3 := l68 h1).
 apply t193. exact h2. exact h3.
Qed.
Lemma l2 : p10 -> s1 -> False.
Proof.
 intros h0 h1.
 assert (h2 := l3 h1).
 assert (h3 := l4 h0 h1).
 refine (simplify (Tatom false (Abnd 0%nat i7)) Tfalse (Abnd 0%nat i8) (List.cons r34 List.nil) h3 h2 _) ; finalize.
Qed.
Notation p272 := ((f15 <= _zh)%R). (* BND(zh, [0, inf]) *)
Definition f254 := Float2 (160756874266144722229268768581460652361576037686250967545141391414466170448827619073450156918313164651133981454274135149) (-460).
Definition i227 := makepairF f254 f18.
Notation p273 := (BND _L i227). (* BND(L, [5.39972e-20, 1]) *)
Notation p274 := (BND r165 i227). (* BND(L / zh * zh, [5.39972e-20, 1]) *)
Definition i228 := makepairF f1 f37.
Notation p275 := (BND _zh i228). (* BND(zh, [5.42101e-20, 0.5]) *)
Definition i229 := makepairF f15 f37.
Notation p276 := (BND _zh i229). (* BND(zh, [0, 0.5]) *)
Lemma l223 : p272 -> s1 -> p272 (* BND(zh, [0, inf]) *).
Proof.
 intros h0 h1.
 assert (h2 := h0).
 exact (h2).
Qed.
Lemma l222 : p272 -> s1 -> p276 (* BND(zh, [0, 0.5]) *).
Proof.
 intros h0 h1.
 assert (h2 := l30 h1).
 assert (h3 := l223 h0 h1).
 apply intersect_bh with (1 := h2) (2 := h3). finalize.
Qed.
Lemma t194 : p276 -> p15 -> p275.
Proof.
 intros h0 h1.
 refine (bnd_of_bnd_abs_p _zh i229 i9 i228 h0 h1 _) ; finalize.
Qed.
Lemma l221 : p272 -> s1 -> p275 (* BND(zh, [5.42101e-20, 0.5]) *).
Proof.
 intros h0 h1.
 assert (h2 := l222 h0 h1).
 assert (h3 := l7 h1).
 apply t194. exact h2. refine (abs_subset _zh i1 i9 h3 _) ; finalize.
Qed.
Lemma t195 : p20 -> p275 -> p274.
Proof.
 intros h0 h1.
 refine (mul_pp r75 _zh i12 i228 i227 h0 h1 _) ; finalize.
Qed.
Lemma l220 : p272 -> s1 -> p274 (* BND(L / zh * zh, [5.39972e-20, 1]) *).
Proof.
 intros h0 h1.
 assert (h2 := l20 h1).
 assert (h3 := l221 h0 h1).
 apply t195. exact h2. exact h3.
Qed.
Lemma t196 : p13 -> p274 -> p273.
Proof.
 intros h0 h1.
 refine (div_xilu _L _ i227 h0 h1) ; finalize.
Qed.
Lemma l219 : p272 -> s1 -> p273 (* BND(L, [5.39972e-20, 1]) *).
Proof.
 intros h0 h1.
 assert (h2 := l6 h1).
 assert (h3 := l220 h0 h1).
 apply t196. exact h2. exact h3.
Qed.
Notation p277 := (BND _L i10). (* BND(L, [2.71051e-20, 1]) *)
Lemma t197 : p277 -> p17.
Proof.
 intros h0.
 refine (abs_of_bnd_p _L i10 i10 h0 _) ; finalize.
Qed.
Lemma l218 : p272 -> s1 -> p17 (* ABS(L, [2.71051e-20, 1]) *).
Proof.
 intros h0 h1.
 assert (h2 := l219 h0 h1).
 apply t197. refine (subset _L i227 i10 h2 _) ; finalize.
Qed.
Lemma t198 : p17 -> p16.
Proof.
 intros h0.
 refine (nzr_of_abs _L i10 h0 _) ; finalize.
Qed.
Lemma l217 : p272 -> s1 -> p16 (* NZR(L) *).
Proof.
 intros h0 h1.
 assert (h2 := l218 h0 h1).
 apply t198. exact h2.
Qed.
Lemma t199 : p13 -> p16 -> p12.
Proof.
 intros h0 h1.
 refine (b1 h0 h1) ; finalize.
Qed.
Lemma l216 : p272 -> s1 -> p12 (* EQL((P - L) / L, (P - L) / zh / (L / zh)) *).
Proof.
 intros h0 h1.
 assert (h2 := l6 h1).
 assert (h3 := l217 h0 h1).
 apply t199. exact h2. exact h3.
Qed.
Lemma t200 : p12 -> p83 -> p11.
Proof.
 intros h0 h1.
 refine (bnd_rewrite r34 r73 i8 h0 h1) ; finalize.
Qed.
Lemma l215 : p272 -> s1 -> p11 (* BND((P - L) / L, [-2.85783e-20, 2.85783e-20]) *).
Proof.
 intros h0 h1.
 assert (h2 := l216 h0 h1).
 assert (h3 := l68 h1).
 apply t200. exact h2. exact h3.
Qed.
Lemma l214 : p272 -> s1 -> False.
Proof.
 intros h0 h1.
 assert (h2 := l3 h1).
 assert (h3 := l215 h0 h1).
 refine (simplify (Tatom false (Abnd 0%nat i7)) Tfalse (Abnd 0%nat i8) (List.cons r34 List.nil) h3 h2 _) ; finalize.
Qed.
Lemma l1 : s1 -> False.
Proof.
 intros h0.
 apply (union _zh f15).
 intro h1. (* [-inf, 0] *)
 apply (l2 h1 h0).
 intro h1. (* [0, inf] *)
 apply (l214 h1 h0).
Qed.
End Generated_by_Gappa.
