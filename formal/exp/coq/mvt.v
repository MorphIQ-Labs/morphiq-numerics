Require Import Gappa.Gappa_library.
Section Generated_by_Gappa.
Variable _rhi : R.
Variable _delta : R.
Notation _R := ((_rhi + _delta)%R).
Notation r3 := ((_R * _R)%R).
Notation r8 := (float10R (Float10 (5) (-1))).
Notation _c3 := (float2R (Float2 (375299968947529) (-51))).
Notation _c4 := (float2R (Float2 (6004799503160511) (-57))).
Notation _c5 := (float2R (Float2 (4803840849707593) (-59))).
Notation _c6 := (float2R (Float2 (3202560482380763) (-61))).
Notation r18 := ((_R * _c6)%R).
Notation r16 := ((_c5 + r18)%R).
Notation r15 := ((_R * r16)%R).
Notation r13 := ((_c4 + r15)%R).
Notation r12 := ((_R * r13)%R).
Notation r10 := ((_c3 + r12)%R).
Notation r9 := ((_R * r10)%R).
Notation r7 := ((r8 + r9)%R).
Notation _QR := ((r3 * r7)%R).
Notation r21 := ((_rhi * _rhi)%R).
Notation r29 := ((_rhi * _c6)%R).
Notation r28 := ((_c5 + r29)%R).
Notation r27 := ((_rhi * r28)%R).
Notation r26 := ((_c4 + r27)%R).
Notation r25 := ((_rhi * r26)%R).
Notation r24 := ((_c3 + r25)%R).
Notation r23 := ((_rhi * r24)%R).
Notation r22 := ((r8 + r23)%R).
Notation _QH := ((r21 * r22)%R).
Notation r1 := ((_QR - _QH)%R).
Notation r36 := ((_R + _rhi)%R).
Notation r35 := ((r8 * r36)%R).
Notation r40 := ((_R * _rhi)%R).
Notation r39 := ((r3 + r40)%R).
Notation r38 := ((r39 + r21)%R).
Notation r37 := ((_c3 * r38)%R).
Notation r34 := ((r35 + r37)%R).
Notation r45 := ((r3 * _R)%R).
Notation r46 := ((r3 * _rhi)%R).
Notation r44 := ((r45 + r46)%R).
Notation r47 := ((r40 * _rhi)%R).
Notation r43 := ((r44 + r47)%R).
Notation r48 := ((r21 * _rhi)%R).
Notation r42 := ((r43 + r48)%R).
Notation r41 := ((_c4 * r42)%R).
Notation r33 := ((r34 + r41)%R).
Notation r54 := ((r45 * _R)%R).
Notation r55 := ((r45 * _rhi)%R).
Notation r53 := ((r54 + r55)%R).
Notation r56 := ((r46 * _rhi)%R).
Notation r52 := ((r53 + r56)%R).
Notation r57 := ((r47 * _rhi)%R).
Notation r51 := ((r52 + r57)%R).
Notation r58 := ((r48 * _rhi)%R).
Notation r50 := ((r51 + r58)%R).
Notation r49 := ((_c5 * r50)%R).
Notation r32 := ((r33 + r49)%R).
Notation r65 := ((r54 * _R)%R).
Notation r66 := ((r54 * _rhi)%R).
Notation r64 := ((r65 + r66)%R).
Notation r67 := ((r55 * _rhi)%R).
Notation r63 := ((r64 + r67)%R).
Notation r68 := ((r56 * _rhi)%R).
Notation r62 := ((r63 + r68)%R).
Notation r69 := ((r57 * _rhi)%R).
Notation r61 := ((r62 + r69)%R).
Notation r70 := ((r58 * _rhi)%R).
Notation r60 := ((r61 + r70)%R).
Notation r59 := ((_c6 * r60)%R).
Notation r31 := ((r32 + r59)%R).
Notation r30 := ((_delta * r31)%R).
Hypothesis a1 : r1 = r30.
Lemma b1 : r1 = r30.
 apply a1.
Qed.
Definition f1 := Float2 (-1789941246693356131382101079560334144543371360062384257457043542964508560930560231090864825107617076781822724800155747281) (-408).
Definition f2 := Float2 (1789941246693356131382101079560334144543371360062384257457043542964508560930560231090864825107617076781822724800155747281) (-408).
Definition i1 := makepairF f1 f2.
Notation p1 := (BND _rhi i1). (* BND(rhi, [-0.0027077, 0.0027077]) *)
Definition f3 := Float2 (-4503599627370497) (-114).
Definition f4 := Float2 (4503599627370497) (-114).
Definition i2 := makepairF f3 f4.
Notation p2 := (BND _delta i2). (* BND(delta, [-2.1684e-19, 2.1684e-19]) *)
Definition s2 := (p1 /\ p2).
Definition f5 := Float2 (-25) (-75).
Definition f6 := Float2 (25) (-75).
Definition i3 := makepairF f5 f6.
Notation p3 := (BND r1 i3). (* BND(QR - QH, [-6.61744e-22, 6.61744e-22]) *)
Definition s3 := (not p3).
Definition s1 := (s2 /\ s3).
Lemma l2 : s1 -> s3.
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj2 h1).
Qed.
Definition f7 := Float2 (-448091686833040108065206859093347433378681941017117071287260693734617657728419347776792587822864537961089254895785308615) (-468).
Definition f8 := Float2 (448091686833040108065206859093347433378681941017117071287260693734617657728419347776792587822864537961089254895785308615) (-468).
Definition i4 := makepairF f7 f8.
Notation p4 := (BND r1 i4). (* BND(QR - QH, [-5.87934e-22, 5.87934e-22]) *)
Notation p5 := (BND r30 i4). (* BND(delta * (5e-1 * (R + rhi) + c3 * (R * R + R * rhi + rhi * rhi) + c4 * (R * R * R + R * R * rhi + R * rhi * rhi + rhi * rhi * rhi) + c5 * (R * R * R * R + R * R * R * rhi + R * R * rhi * rhi + R * rhi * rhi * rhi + rhi * rhi * rhi * rhi) + c6 * (R * R * R * R * R + R * R * R * R * rhi + R * R * R * rhi * rhi + R * R * rhi * rhi * rhi + R * rhi * rhi * rhi * rhi + rhi * rhi * rhi * rhi * rhi)), [-5.87934e-22, 5.87934e-22]) *)
Lemma l6 : s1 -> s2.
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj1 h1).
Qed.
Lemma l5 : s1 -> p2 (* BND(delta, [-2.1684e-19, 2.1684e-19]) *).
Proof.
 intros h0.
 assert (h1 := l6 h0).
 exact (proj2 h1).
Qed.
Definition f9 := Float2 (-1421) (-19).
Definition f10 := Float2 (1792366747332160034275461144240501605959361102076591174497581311309734383318122857381470505549904072214213482932248232141) (-408).
Definition i5 := makepairF f9 f10.
Notation p6 := (BND r31 i5). (* BND(5e-1 * (R + rhi) + c3 * (R * R + R * rhi + rhi * rhi) + c4 * (R * R * R + R * R * rhi + R * rhi * rhi + rhi * rhi * rhi) + c5 * (R * R * R * R + R * R * R * rhi + R * R * rhi * rhi + R * rhi * rhi * rhi + rhi * rhi * rhi * rhi) + c6 * (R * R * R * R * R + R * R * R * R * rhi + R * R * R * rhi * rhi + R * R * rhi * rhi * rhi + R * rhi * rhi * rhi * rhi + rhi * rhi * rhi * rhi * rhi), [-0.00271034, 0.00271137]) *)
Definition f11 := Float2 (-2841) (-20).
Definition f12 := Float2 (896183373665679122898708994187175073262055166753638940819464118216355713990519313904266985611882393036979919417402507057) (-407).
Definition i6 := makepairF f11 f12.
Notation p7 := (BND r32 i6). (* BND(5e-1 * (R + rhi) + c3 * (R * R + R * rhi + rhi * rhi) + c4 * (R * R * R + R * R * rhi + R * rhi * rhi + rhi * rhi * rhi) + c5 * (R * R * R * R + R * R * R * rhi + R * R * rhi * rhi + R * rhi * rhi * rhi + rhi * rhi * rhi * rhi), [-0.00270939, 0.00271137]) *)
Definition f13 := Float2 (-11363) (-22).
Definition f14 := Float2 (1792366745850787098521039233433088380154716338038479867520643036567750961167398677174267878525383976453708070798917381517) (-408).
Definition i7 := makepairF f13 f14.
Notation p8 := (BND r33 i7). (* BND(5e-1 * (R + rhi) + c3 * (R * R + R * rhi + rhi * rhi) + c4 * (R * R * R + R * R * rhi + R * rhi * rhi + rhi * rhi * rhi), [-0.00270915, 0.00271137]) *)
Definition f15 := Float2 (-22725) (-23).
Definition f16 := Float2 (1792364558650191923810135087900229062173434055908009051979664453738613701659714141155048507777485529668258887266186310693) (-408).
Definition i8 := makepairF f15 f16.
Notation p9 := (BND r34 i8). (* BND(5e-1 * (R + rhi) + c3 * (R * R + R * rhi + rhi * rhi), [-0.00270903, 0.00271137]) *)
Definition f17 := Float2 (-11357) (-22).
Definition f18 := Float2 (1789941246693356203053932829250084796725089451425150129581640152740176892327036977059162797720027910073806910559600509905) (-408).
Definition i9 := makepairF f17 f18.
Notation p10 := (BND r35 i9). (* BND(5e-1 * (R + rhi), [-0.00270772, 0.0027077]) *)
Definition f19 := Float2 (1) (-1).
Definition i10 := makepairF f19 f19.
Notation p11 := (BND r8 i10). (* BND(5e-1, [0.5, 0.5]) *)
Lemma t1 : p11.
Proof.
 refine (constant10 _ i10 _) ; finalize.
Qed.
Lemma l12 : s1 -> p11 (* BND(5e-1, [0.5, 0.5]) *).
Proof.
 intros h0.
 apply t1.
Qed.
Definition f20 := Float2 (-11357) (-21).
Definition f21 := Float2 (1789941246693356203053932829250084796725089451425150129581640152740176892327036977059162797720027910073806910559600509905) (-407).
Definition i11 := makepairF f20 f21.
Notation p12 := (BND r36 i11). (* BND(R + rhi, [-0.00541544, 0.0054154]) *)
Definition f22 := Float2 (-1747989498723980737036879471620933055573054241003824220416246838394380101292493870144004658527772210318155367499067649) (-398).
Definition f23 := Float2 (1789941246693356274725764578939835448906807542787916001706236762515845223723513723027460770332438743365791096319045272529) (-408).
Definition i12 := makepairF f22 f23.
Notation p13 := (BND _R i12). (* BND(R, [-0.0027077, 0.0027077]) *)
Lemma l15 : s1 -> p1 (* BND(rhi, [-0.0027077, 0.0027077]) *).
Proof.
 intros h0.
 assert (h1 := l6 h0).
 exact (proj1 h1).
Qed.
Definition f24 := Float2 (-1747989498723980597052833085508138813030636093810922126422894084926277891533750225674672680769157301544748754687652097) (-398).
Definition i13 := makepairF f24 f2.
Notation p14 := (BND _rhi i13). (* BND(rhi, [-0.0027077, 0.0027077]) *)
Lemma t2 : p14 -> p2 -> p13.
Proof.
 intros h0 h1.
 refine (add _rhi _delta i13 i2 i12 h0 h1 _) ; finalize.
Qed.
Lemma l14 : s1 -> p13 (* BND(R, [-0.0027077, 0.0027077]) *).
Proof.
 intros h0.
 assert (h1 := l15 h0).
 assert (h2 := l5 h0).
 apply t2. refine (subset _rhi i1 i13 h1 _) ; finalize. exact h2.
Qed.
Definition i14 := makepairF f17 f23.
Notation p15 := (BND _R i14). (* BND(R, [-0.00270772, 0.0027077]) *)
Definition i15 := makepairF f17 f2.
Notation p16 := (BND _rhi i15). (* BND(rhi, [-0.00270772, 0.0027077]) *)
Lemma t3 : p15 -> p16 -> p12.
Proof.
 intros h0 h1.
 refine (add _R _rhi i14 i15 i11 h0 h1 _) ; finalize.
Qed.
Lemma l13 : s1 -> p12 (* BND(R + rhi, [-0.00541544, 0.0054154]) *).
Proof.
 intros h0.
 assert (h1 := l14 h0).
 assert (h2 := l15 h0).
 apply t3. refine (subset _R i12 i14 h1 _) ; finalize. refine (subset _rhi i1 i15 h2 _) ; finalize.
Qed.
Lemma t4 : p11 -> p12 -> p10.
Proof.
 intros h0 h1.
 refine (mul_po r8 r36 i10 i11 i9 h0 h1 _) ; finalize.
Qed.
Lemma l11 : s1 -> p10 (* BND(5e-1 * (R + rhi), [-0.00270772, 0.0027077]) *).
Proof.
 intros h0.
 assert (h1 := l12 h0).
 assert (h2 := l13 h0).
 apply t4. exact h1. exact h2.
Qed.
Definition f25 := Float2 (-11) (-23).
Definition f26 := Float2 (605827989208930189050564662536066362086151120714730599506075249609202333169291023971427514364404898612994176646450197) (-406).
Definition i16 := makepairF f25 f26.
Notation p17 := (BND r37 i16). (* BND(c3 * (R * R + R * rhi + rhi * rhi), [-1.3113e-06, 3.66582e-06]) *)
Definition f27 := Float2 (1) (-3).
Definition f28 := Float2 (375299968947529) (-51).
Definition i17 := makepairF f27 f28.
Notation p18 := (BND _c3 i17). (* BND(c3, [0.125, 0.166667]) *)
Lemma t5 : p18.
Proof.
 refine (constant2 _ i17 _) ; finalize.
Qed.
Lemma l17 : s1 -> p18 (* BND(c3, [0.125, 0.166667]) *).
Proof.
 intros h0.
 apply t5.
Qed.
Definition f29 := Float2 (-1) (-17).
Definition f30 := Float2 (7269935870507401177612429125593104208858581981249729338772011075501166833964171033509977928790319467716142554238204119) (-407).
Definition i18 := makepairF f29 f30.
Notation p19 := (BND r38 i18). (* BND(R * R + R * rhi + rhi * rhi, [-7.62939e-06, 2.19949e-05]) *)
Definition f31 := Float2 (9693247827343201958281543158060691654537077330858540823627585349717333837496664129295221170636744176630143716535026521) (-408).
Definition i19 := makepairF f29 f31.
Notation p20 := (BND r39 i19). (* BND(R * R + R * rhi, [-7.62939e-06, 1.46633e-05]) *)
Definition f32 := Float2 (0) (0).
Definition f33 := Float2 (1211655978417900293301647601916324802383028636812925166451902016963294931305126505363441410701899947804647791257986909) (-406).
Definition i20 := makepairF f32 f33.
Notation p21 := (BND r3 i20). (* BND(R * R, [0, 7.33164e-06]) *)
Definition f34 := Float2 (223742655836669534340720572367479431113350942848489500213279595314480652965439215378432596291554842920723887039880659067) (-405).
Definition i21 := makepairF f32 f34.
Notation p22 := (ABS _R i21). (* ABS(R, [0, 0.0027077]) *)
Definition f35 := Float2 (223742655836669516422762634945041768067921420007798032182130442870563570116320028886358103138452134597727840600019468411) (-405).
Definition i22 := makepairF f32 f35.
Notation p23 := (ABS _rhi i22). (* ABS(rhi, [0, 0.0027077]) *)
Definition f36 := Float2 (-223742655836669516422762634945041768067921420007798032182130442870563570116320028886358103138452134597727840600019468411) (-405).
Definition i23 := makepairF f36 f35.
Notation p24 := (BND _rhi i23). (* BND(rhi, [-0.0027077, 0.0027077]) *)
Lemma t6 : p24 -> p23.
Proof.
 intros h0.
 refine (abs_of_bnd_o _rhi i23 i22 h0 _) ; finalize.
Qed.
Lemma l22 : s1 -> p23 (* ABS(rhi, [0, 0.0027077]) *).
Proof.
 intros h0.
 assert (h1 := l15 h0).
 apply t6. refine (subset _rhi i1 i23 h1 _) ; finalize.
Qed.
Definition i24 := makepairF f32 f4.
Notation p25 := (ABS _delta i24). (* ABS(delta, [0, 2.1684e-19]) *)
Lemma t7 : p2 -> p25.
Proof.
 intros h0.
 refine (abs_of_bnd_o _delta i2 i24 h0 _) ; finalize.
Qed.
Lemma l23 : s1 -> p25 (* ABS(delta, [0, 2.1684e-19]) *).
Proof.
 intros h0.
 assert (h1 := l5 h0).
 apply t7. exact h1.
Qed.
Lemma t8 : p23 -> p25 -> p22.
Proof.
 intros h0 h1.
 refine (add_aa_o _rhi _delta i22 i24 i21 h0 h1 _) ; finalize.
Qed.
Lemma l21 : s1 -> p22 (* ABS(R, [0, 0.0027077]) *).
Proof.
 intros h0.
 assert (h1 := l22 h0).
 assert (h2 := l23 h0).
 apply t8. exact h1. exact h2.
Qed.
Lemma t9 : p22 -> p21.
Proof.
 intros h0.
 refine (square _R i21 i20 h0 _) ; finalize.
Qed.
Lemma l20 : s1 -> p21 (* BND(R * R, [0, 7.33164e-06]) *).
Proof.
 intros h0.
 assert (h1 := l21 h0).
 apply t9. exact h1.
Qed.
Definition f37 := Float2 (-9466062331389845283349517090616000869150317936732109683242143128640926000539371304377842827791297627756938577154451) (-399).
Definition f38 := Float2 (4846623913671600785074952750395392445004962783606840157819977281864154112276158107841455527829144385411552551503078885) (-408).
Definition i25 := makepairF f37 f38.
Notation p26 := (BND r40 i25). (* BND(R * rhi, [-7.33164e-06, 7.33164e-06]) *)
Definition f39 := Float2 (1747989498723980737036879471620933055573054241003824220416246838394380101292493870144004658527772210318155367499067649) (-398).
Definition i26 := makepairF f22 f39.
Notation p27 := (BND _R i26). (* BND(R, [-0.0027077, 0.0027077]) *)
Definition f40 := Float2 (1747989498723980597052833085508138813030636093810922126422894084926277891533750225674672680769157301544748754687652097) (-398).
Definition i27 := makepairF f24 f40.
Notation p28 := (BND _rhi i27). (* BND(rhi, [-0.0027077, 0.0027077]) *)
Lemma t10 : p27 -> p28 -> p26.
Proof.
 intros h0 h1.
 refine (mul_oo _R _rhi i26 i27 i25 h0 h1 _) ; finalize.
Qed.
Lemma l24 : s1 -> p26 (* BND(R * rhi, [-7.33164e-06, 7.33164e-06]) *).
Proof.
 intros h0.
 assert (h1 := l14 h0).
 assert (h2 := l15 h0).
 apply t10. refine (subset _R i12 i26 h1 _) ; finalize. refine (subset _rhi i1 i27 h2 _) ; finalize.
Qed.
Definition i28 := makepairF f29 f38.
Notation p29 := (BND r40 i28). (* BND(R * rhi, [-7.62939e-06, 7.33164e-06]) *)
Lemma t11 : p21 -> p29 -> p20.
Proof.
 intros h0 h1.
 refine (add r3 r40 i20 i28 i19 h0 h1 _) ; finalize.
Qed.
Lemma l19 : s1 -> p20 (* BND(R * R + R * rhi, [-7.62939e-06, 1.46633e-05]) *).
Proof.
 intros h0.
 assert (h1 := l20 h0).
 assert (h2 := l24 h0).
 apply t11. exact h1. refine (subset r40 i25 i28 h2 _) ; finalize.
Qed.
Definition f41 := Float2 (4846623913671600396943315093125516763180086631640917853916436801284999830431677937724734686943894758802141391941381717) (-408).
Definition i29 := makepairF f32 f41.
Notation p30 := (BND r21 i29). (* BND(rhi * rhi, [0, 7.33164e-06]) *)
Definition f42 := Float2 (55935663959167379105690658736260442016980355001949508045532610717640892529080007221589525784613033649431960150004867103) (-403).
Definition i30 := makepairF f32 f42.
Notation p31 := (ABS _rhi i30). (* ABS(rhi, [0, 0.0027077]) *)
Lemma t12 : p31 -> p30.
Proof.
 intros h0.
 refine (square _rhi i30 i29 h0 _) ; finalize.
Qed.
Lemma l25 : s1 -> p30 (* BND(rhi * rhi, [0, 7.33164e-06]) *).
Proof.
 intros h0.
 assert (h1 := l22 h0).
 apply t12. refine (abs_subset _rhi i22 i30 h1 _) ; finalize.
Qed.
Lemma t13 : p20 -> p30 -> p19.
Proof.
 intros h0 h1.
 refine (add r39 r21 i19 i29 i18 h0 h1 _) ; finalize.
Qed.
Lemma l18 : s1 -> p19 (* BND(R * R + R * rhi + rhi * rhi, [-7.62939e-06, 2.19949e-05]) *).
Proof.
 intros h0.
 assert (h1 := l19 h0).
 assert (h2 := l25 h0).
 apply t13. exact h1. exact h2.
Qed.
Lemma t14 : p18 -> p19 -> p17.
Proof.
 intros h0 h1.
 refine (mul_po _c3 r38 i17 i18 i16 h0 h1 _) ; finalize.
Qed.
Lemma l16 : s1 -> p17 (* BND(c3 * (R * R + R * rhi + rhi * rhi), [-1.3113e-06, 3.66582e-06]) *).
Proof.
 intros h0.
 assert (h1 := l17 h0).
 assert (h2 := l18 h0).
 apply t14. exact h1. exact h2.
Qed.
Lemma t15 : p10 -> p17 -> p9.
Proof.
 intros h0 h1.
 refine (add r35 r37 i9 i16 i8 h0 h1 _) ; finalize.
Qed.
Lemma l10 : s1 -> p9 (* BND(5e-1 * (R + rhi) + c3 * (R * R + R * rhi + rhi * rhi), [-0.00270903, 0.00271137]) *).
Proof.
 intros h0.
 assert (h1 := l11 h0).
 assert (h2 := l16 h0).
 apply t15. exact h1. exact h2.
Qed.
Definition f43 := Float2 (-1) (-23).
Definition f44 := Float2 (273400074396838863018191607414747660285266308851942622322853642157438460567002402421343487305848181147941591383853) (-405).
Definition i31 := makepairF f43 f44.
Notation p32 := (BND r41 i31). (* BND(c4 * (R * R * R + R * R * rhi + R * rhi * rhi + rhi * rhi * rhi), [-1.19209e-07, 3.30865e-09]) *)
Definition f45 := Float2 (1) (-5).
Definition f46 := Float2 (6004799503160511) (-57).
Definition i32 := makepairF f45 f46.
Notation p33 := (BND _c4 i32). (* BND(c4, [0.03125, 0.0416667]) *)
Lemma t16 : p33.
Proof.
 refine (constant2 _ i32 _) ; finalize.
Qed.
Lemma l27 : s1 -> p33 (* BND(c4, [0.03125, 0.0416667]) *).
Proof.
 intros h0.
 apply t16.
Qed.
Definition f47 := Float2 (-1) (-19).
Definition f48 := Float2 (6561601785524296985609733602270254738905748990628025489167074500901783331708743546652810101660950754390575339973385) (-405).
Definition i33 := makepairF f47 f48.
Notation p34 := (BND r42 i33). (* BND(R * R * R + R * R * rhi + R * rhi * rhi + rhi * rhi * rhi, [-1.90735e-06, 7.94075e-08]) *)
Definition f49 := Float2 (-1) (-20).
Definition f50 := Float2 (4921201339143222936259306817563259521447908919066261330035882510046859076601261752655652087681202774589505559103425) (-405).
Definition i34 := makepairF f49 f50.
Notation p35 := (BND r43 i34). (* BND(R * R * R + R * R * rhi + R * rhi * rhi, [-9.53674e-07, 5.95556e-08]) *)
Definition f51 := Float2 (-1) (-21).
Definition f52 := Float2 (1640400446381074377770437811141279503015208351459865596559869224641956407687496294540181723046665496521073976820157) (-404).
Definition i35 := makepairF f51 f52.
Notation p36 := (BND r44 i35). (* BND(R * R * R + R * R * rhi, [-4.76837e-07, 3.97038e-08]) *)
Definition f53 := Float2 (-25631256974704288178975625256689729255064896608914882133106732869033687072305422965532317065852558573544149085089) (-399).
Definition f54 := Float2 (6561601785524297773817760065712570689296613531882209826075323614472623890510188279176273168858254994827302165782753) (-407).
Definition i36 := makepairF f53 f54.
Notation p37 := (BND r45 i36). (* BND(R * R * R, [-1.98519e-08, 1.98519e-08]) *)
Definition f55 := Float2 (9466062331389846041419121889971287518617411225100977862905484507525741650821300823151886021108593342223810869203023) (-399).
Definition i37 := makepairF f32 f55.
Notation p38 := (BND r3 i37). (* BND(R * R, [0, 7.33164e-06]) *)
Definition f56 := Float2 (-53344406088988669953518050281400544908845649444696784070320032909984744302139095158203267166985235910588237533541) (-383).
Definition f57 := Float2 (27312335917562199016201241744077078993328972515684753444003856849912189082695216721000072789496440786221177617172933) (-392).
Definition i38 := makepairF f56 f57.
Notation p39 := (BND _R i38). (* BND(R, [-0.0027077, 0.0027077]) *)
Lemma t17 : p38 -> p39 -> p37.
Proof.
 intros h0 h1.
 refine (mul_po r3 _R i37 i38 i36 h0 h1 _) ; finalize.
Qed.
Lemma l31 : s1 -> p37 (* BND(R * R * R, [-1.98519e-08, 1.98519e-08]) *).
Proof.
 intros h0.
 assert (h1 := l20 h0).
 assert (h2 := l14 h0).
 apply t17. refine (subset r3 i20 i37 h1 _) ; finalize. refine (subset _R i12 i38 h2 _) ; finalize.
Qed.
Definition f58 := Float2 (-1601953560919017882896909771342203450885022773387869859961823775064215666745552264928022611209733637046213293159) (-395).
Definition f59 := Float2 (6561601785524297248345742423417665334825053279796714946403630182663027370989782077145180615515068977341289648778503) (-407).
Definition i39 := makepairF f58 f59.
Notation p40 := (BND r46 i39). (* BND(R * R * rhi, [-1.98519e-08, 1.98519e-08]) *)
Definition f60 := Float2 (-6668050761123583210192997304947428943750900626414955621425224628167258802542687323282900546146992880038256663085) (-380).
Definition f61 := Float2 (13656167958781098414475258480532334476801844482897829112678860038486546027607423638083380318509041418318349645997283) (-391).
Definition i40 := makepairF f60 f61.
Notation p41 := (BND _rhi i40). (* BND(rhi, [-0.0027077, 0.0027077]) *)
Lemma t18 : p38 -> p41 -> p40.
Proof.
 intros h0 h1.
 refine (mul_po r3 _rhi i37 i40 i39 h0 h1 _) ; finalize.
Qed.
Lemma l32 : s1 -> p40 (* BND(R * R * rhi, [-1.98519e-08, 1.98519e-08]) *).
Proof.
 intros h0.
 assert (h1 := l20 h0).
 assert (h2 := l15 h0).
 apply t18. refine (subset r3 i20 i37 h1 _) ; finalize. refine (subset _rhi i1 i40 h2 _) ; finalize.
Qed.
Definition f62 := Float2 (-1) (-22).
Definition i41 := makepairF f62 f54.
Notation p42 := (BND r45 i41). (* BND(R * R * R, [-2.38419e-07, 1.98519e-08]) *)
Definition i42 := makepairF f62 f59.
Notation p43 := (BND r46 i42). (* BND(R * R * rhi, [-2.38419e-07, 1.98519e-08]) *)
Lemma t19 : p42 -> p43 -> p36.
Proof.
 intros h0 h1.
 refine (add r45 r46 i41 i42 i35 h0 h1 _) ; finalize.
Qed.
Lemma l30 : s1 -> p36 (* BND(R * R * R + R * R * rhi, [-4.76837e-07, 3.97038e-08]) *).
Proof.
 intros h0.
 assert (h1 := l31 h0).
 assert (h2 := l32 h0).
 apply t19. refine (subset r45 i36 i41 h1 _) ; finalize. refine (subset r46 i39 i42 h2 _) ; finalize.
Qed.
Definition f63 := Float2 (-800976780459508877303921482070654548543697371165297918416085967169407354114389240026996407025328018333670705793) (-394).
Definition f64 := Float2 (1640400446381074180718431195280700515417492216146530136916144060762946261226269163575288641587871781547357605463111) (-405).
Definition i43 := makepairF f63 f64.
Notation p44 := (BND r47 i43). (* BND(R * rhi * rhi, [-1.98519e-08, 1.98519e-08]) *)
Definition f65 := Float2 (9466062331389845283349517090616000869150317936732109683242143128640926000539371304377842827791297627756938577154451) (-399).
Definition i44 := makepairF f37 f65.
Notation p45 := (BND r40 i44). (* BND(R * rhi, [-7.33164e-06, 7.33164e-06]) *)
Definition f66 := Float2 (-13656167958781098414475258480532334476801844482897829112678860038486546027607423638083380318509041418318349645997283) (-391).
Definition i45 := makepairF f66 f61.
Notation p46 := (BND _rhi i45). (* BND(rhi, [-0.0027077, 0.0027077]) *)
Lemma t20 : p45 -> p46 -> p44.
Proof.
 intros h0 h1.
 refine (mul_oo r40 _rhi i44 i45 i43 h0 h1 _) ; finalize.
Qed.
Lemma l33 : s1 -> p44 (* BND(R * rhi * rhi, [-1.98519e-08, 1.98519e-08]) *).
Proof.
 intros h0.
 assert (h1 := l24 h0).
 assert (h2 := l15 h0).
 apply t20. refine (subset r40 i25 i44 h1 _) ; finalize. refine (subset _rhi i1 i45 h2 _) ; finalize.
Qed.
Definition i46 := makepairF f51 f64.
Notation p47 := (BND r47 i46). (* BND(R * rhi * rhi, [-4.76837e-07, 1.98519e-08]) *)
Lemma t21 : p36 -> p47 -> p35.
Proof.
 intros h0 h1.
 refine (add r44 r47 i35 i46 i34 h0 h1 _) ; finalize.
Qed.
Lemma l29 : s1 -> p35 (* BND(R * R * R + R * R * rhi + R * rhi * rhi, [-9.53674e-07, 5.95556e-08]) *).
Proof.
 intros h0.
 assert (h1 := l30 h0).
 assert (h2 := l33 h0).
 apply t21. exact h1. refine (subset r47 i43 i46 h2 _) ; finalize.
Qed.
Definition f67 := Float2 (-1601953560919017626318776156940425017048671944884535311651554678569261967878400189450349623027097636524482207881) (-395).
Definition f68 := Float2 (205050055797634256168803348088374402182230008945220519891398998856865531888435224249644751747468497475133722608745) (-402).
Definition i47 := makepairF f67 f68.
Notation p48 := (BND r48 i47). (* BND(rhi * rhi * rhi, [-1.98519e-08, 1.98519e-08]) *)
Definition f69 := Float2 (18932124662779689050559824582521549856172213404847335366861081255019530587623741944237244870874588901570864812271023) (-400).
Definition i48 := makepairF f32 f69.
Notation p49 := (BND r21 i48). (* BND(rhi * rhi, [0, 7.33164e-06]) *)
Definition f70 := Float2 (54624671835124393657901033922129337907207377931591316450715440153946184110429694552333521274036165673273398583989129) (-393).
Definition i49 := makepairF f60 f70.
Notation p50 := (BND _rhi i49). (* BND(rhi, [-0.0027077, 0.0027077]) *)
Lemma t22 : p49 -> p50 -> p48.
Proof.
 intros h0 h1.
 refine (mul_po r21 _rhi i48 i49 i47 h0 h1 _) ; finalize.
Qed.
Lemma l34 : s1 -> p48 (* BND(rhi * rhi * rhi, [-1.98519e-08, 1.98519e-08]) *).
Proof.
 intros h0.
 assert (h1 := l25 h0).
 assert (h2 := l15 h0).
 apply t22. refine (subset r21 i29 i48 h1 _) ; finalize. refine (subset _rhi i1 i49 h2 _) ; finalize.
Qed.
Definition i50 := makepairF f49 f68.
Notation p51 := (BND r48 i50). (* BND(rhi * rhi * rhi, [-9.53674e-07, 1.98519e-08]) *)
Lemma t23 : p35 -> p51 -> p34.
Proof.
 intros h0 h1.
 refine (add r43 r48 i34 i50 i33 h0 h1 _) ; finalize.
Qed.
Lemma l28 : s1 -> p34 (* BND(R * R * R + R * R * rhi + R * rhi * rhi + rhi * rhi * rhi, [-1.90735e-06, 7.94075e-08]) *).
Proof.
 intros h0.
 assert (h1 := l29 h0).
 assert (h2 := l34 h0).
 apply t23. exact h1. refine (subset r48 i47 i50 h2 _) ; finalize.
Qed.
Lemma t24 : p33 -> p34 -> p32.
Proof.
 intros h0 h1.
 refine (mul_po _c4 r42 i32 i33 i31 h0 h1 _) ; finalize.
Qed.
Lemma l26 : s1 -> p32 (* BND(c4 * (R * R * R + R * R * rhi + R * rhi * rhi + rhi * rhi * rhi), [-1.19209e-07, 3.30865e-09]) *).
Proof.
 intros h0.
 assert (h1 := l27 h0).
 assert (h2 := l28 h0).
 apply t24. exact h1. exact h2.
Qed.
Lemma t25 : p9 -> p32 -> p8.
Proof.
 intros h0 h1.
 refine (add r34 r41 i8 i31 i7 h0 h1 _) ; finalize.
Qed.
Lemma l9 : s1 -> p8 (* BND(5e-1 * (R + rhi) + c3 * (R * R + R * rhi + rhi * rhi) + c4 * (R * R * R + R * R * rhi + R * rhi * rhi + rhi * rhi * rhi), [-0.00270915, 0.00271137]) *).
Proof.
 intros h0.
 assert (h1 := l10 h0).
 assert (h2 := l26 h0).
 apply t25. exact h1. exact h2.
Qed.
Definition f71 := Float2 (1480571147276378754941261766369393995468798014118285199864960466813639950634266092698380809620251768035887632597) (-408).
Definition i51 := makepairF f62 f71.
Notation p52 := (BND r49 i51). (* BND(c5 * (R * R * R * R + R * R * R * rhi + R * R * rhi * rhi + R * rhi * rhi * rhi + rhi * rhi * rhi * rhi), [-2.38419e-07, 2.23971e-12]) *)
Definition f72 := Float2 (1) (-7).
Definition f73 := Float2 (4803840849707593) (-59).
Definition i52 := makepairF f72 f73.
Notation p53 := (BND _c5 i52). (* BND(c5, [0.0078125, 0.00833334]) *)
Lemma t26 : p53.
Proof.
 refine (constant2 _ i52 _) ; finalize.
Qed.
Lemma l36 : s1 -> p53 (* BND(c5, [0.0078125, 0.00833334]) *).
Proof.
 intros h0.
 apply t26.
Qed.
Definition f74 := Float2 (-1) (-16).
Definition f75 := Float2 (1388035090208135910886388028116259872709876436657166647859251359278774455134997683728016833799970993821439147431) (-401).
Definition i53 := makepairF f74 f75.
Notation p54 := (BND r50 i53). (* BND(R * R * R * R + R * R * R * rhi + R * R * rhi * rhi + R * rhi * rhi * rhi + rhi * rhi * rhi * rhi, [-1.52588e-05, 2.68765e-10]) *)
Definition f76 := Float2 (1110428072166508773172253615306814188315464339046679847004280824676407054787839655377635286646660768514729357077) (-401).
Definition i54 := makepairF f29 f76.
Notation p55 := (BND r51 i54). (* BND(R * R * R * R + R * R * R * rhi + R * R * rhi * rhi + R * rhi * rhi * rhi, [-7.62939e-06, 2.15012e-10]) *)
Definition f77 := Float2 (-1) (-18).
Definition f78 := Float2 (3331284216499526452906190424361868556862871437771729475085162480373670821270766367957338882879772968334972381229) (-403).
Definition i55 := makepairF f77 f78.
Notation p56 := (BND r52 i55). (* BND(R * R * R * R + R * R * R * rhi + R * R * rhi * rhi, [-3.8147e-06, 1.61259e-10]) *)
Definition f79 := Float2 (1110428072166508862098540000934433890084379569957565829405796570011939185246975904907231767920194225731642128677) (-402).
Definition i56 := makepairF f47 f79.
Notation p57 := (BND r53 i56). (* BND(R * R * R * R + R * R * R * rhi, [-1.90735e-06, 1.07506e-10]) *)
Definition f80 := Float2 (-8675219313800850832513149951158182044576028212092112790488933832751235458773824293704014508851913170858721701) (-396).
Definition f81 := Float2 (2220856144333017813123366387496494603411463222295580874365167061184316277446099019188227714266089771739832755421) (-404).
Definition i57 := makepairF f80 f81.
Notation p58 := (BND r54 i57). (* BND(R * R * R * R, [-5.37529e-11, 5.37529e-11]) *)
Definition f82 := Float2 (25631256974704288178975625256689729255064896608914882133106732869033687072305422965532317065852558573544149085089) (-399).
Definition i58 := makepairF f53 f82.
Notation p59 := (BND r45 i58). (* BND(R * R * R, [-1.98519e-08, 1.98519e-08]) *)
Definition f83 := Float2 (53344406088988669953518050281400544908845649444696784070320032909984744302139095158203267166985235910588237533541) (-383).
Definition i59 := makepairF f56 f83.
Notation p60 := (BND _R i59). (* BND(R, [-0.0027077, 0.0027077]) *)
Lemma t27 : p59 -> p60 -> p58.
Proof.
 intros h0 h1.
 refine (mul_oo r45 _R i58 i59 i57 h0 h1 _) ; finalize.
Qed.
Lemma l41 : s1 -> p58 (* BND(R * R * R * R, [-5.37529e-11, 5.37529e-11]) *).
Proof.
 intros h0.
 assert (h1 := l31 h0).
 assert (h2 := l14 h0).
 apply t27. refine (subset r45 i36 i58 h1 _) ; finalize. refine (subset _R i12 i59 h2 _) ; finalize.
Qed.
Definition f84 := Float2 (-34700877255203400551106150253769389951969610273979413175906550294741257242840696881885927459604486424792746239) (-398).
Definition f85 := Float2 (2220856144333017635270793616241240956926055057534682443258019218863440463541804600440699357414687131186735759287) (-404).
Definition i60 := makepairF f84 f85.
Notation p61 := (BND r55 i60). (* BND(R * R * R * rhi, [-5.37529e-11, 5.37529e-11]) *)
Definition f86 := Float2 (-3203907121838036022371953157086216156883112076114360266638341608629210884038177870691539633231569821693018635637) (-396).
Definition f87 := Float2 (3203907121838036022371953157086216156883112076114360266638341608629210884038177870691539633231569821693018635637) (-396).
Definition i61 := makepairF f86 f87.
Notation p62 := (BND r45 i61). (* BND(R * R * R, [-1.98519e-08, 1.98519e-08]) *)
Definition f88 := Float2 (6668050761123583210192997304947428943750900626414955621425224628167258802542687323282900546146992880038256663085) (-380).
Definition i62 := makepairF f60 f88.
Notation p63 := (BND _rhi i62). (* BND(rhi, [-0.0027077, 0.0027077]) *)
Lemma t28 : p62 -> p63 -> p61.
Proof.
 intros h0 h1.
 refine (mul_oo r45 _rhi i61 i62 i60 h0 h1 _) ; finalize.
Qed.
Lemma l42 : s1 -> p61 (* BND(R * R * R * rhi, [-5.37529e-11, 5.37529e-11]) *).
Proof.
 intros h0.
 assert (h1 := l31 h0).
 assert (h2 := l15 h0).
 apply t28. refine (subset r45 i36 i61 h1 _) ; finalize. refine (subset _rhi i1 i62 h2 _) ; finalize.
Qed.
Definition i63 := makepairF f49 f81.
Notation p64 := (BND r54 i63). (* BND(R * R * R * R, [-9.53674e-07, 5.37529e-11]) *)
Definition i64 := makepairF f49 f85.
Notation p65 := (BND r55 i64). (* BND(R * R * R * rhi, [-9.53674e-07, 5.37529e-11]) *)
Lemma t29 : p64 -> p65 -> p57.
Proof.
 intros h0 h1.
 refine (add r54 r55 i63 i64 i56 h0 h1 _) ; finalize.
Qed.
Lemma l40 : s1 -> p57 (* BND(R * R * R * R + R * R * R * rhi, [-1.90735e-06, 1.07506e-10]) *).
Proof.
 intros h0.
 assert (h1 := l41 h0).
 assert (h2 := l42 h0).
 apply t29. refine (subset r54 i57 i63 h1 _) ; finalize. refine (subset r55 i60 i64 h2 _) ; finalize.
Qed.
Definition f89 := Float2 (-2168804828450212360759981293931642141980688081751167609909315117870688380423465933872803412186297884515015867) (-394).
Definition f90 := Float2 (1110428072166508728709110422493000776694112297856597816273569340349792450776814558142875347039384516871688123875) (-403).
Definition i65 := makepairF f89 f90.
Notation p66 := (BND r56 i65). (* BND(R * R * rhi * rhi, [-5.37529e-11, 5.37529e-11]) *)
Definition f91 := Float2 (1601953560919017882896909771342203450885022773387869859961823775064215666745552264928022611209733637046213293159) (-395).
Definition i66 := makepairF f58 f91.
Notation p67 := (BND r46 i66). (* BND(R * R * rhi, [-1.98519e-08, 1.98519e-08]) *)
Definition f92 := Float2 (-26672203044494332840771989219789715775003602505659822485700898512669035210170749293131602184587971520153026652339) (-382).
Definition f93 := Float2 (26672203044494332840771989219789715775003602505659822485700898512669035210170749293131602184587971520153026652339) (-382).
Definition i67 := makepairF f92 f93.
Notation p68 := (BND _rhi i67). (* BND(rhi, [-0.0027077, 0.0027077]) *)
Lemma t30 : p67 -> p68 -> p66.
Proof.
 intros h0 h1.
 refine (mul_oo r46 _rhi i66 i67 i65 h0 h1 _) ; finalize.
Qed.
Lemma l43 : s1 -> p66 (* BND(R * R * rhi * rhi, [-5.37529e-11, 5.37529e-11]) *).
Proof.
 intros h0.
 assert (h1 := l32 h0).
 assert (h2 := l15 h0).
 apply t30. refine (subset r46 i39 i66 h1 _) ; finalize. refine (subset _rhi i1 i67 h2 _) ; finalize.
Qed.
Definition i68 := makepairF f47 f90.
Notation p69 := (BND r56 i68). (* BND(R * R * rhi * rhi, [-1.90735e-06, 5.37529e-11]) *)
Lemma t31 : p57 -> p69 -> p56.
Proof.
 intros h0 h1.
 refine (add r53 r56 i56 i68 i55 h0 h1 _) ; finalize.
Qed.
Lemma l39 : s1 -> p56 (* BND(R * R * R * R + R * R * R * rhi + R * R * rhi * rhi, [-3.8147e-06, 1.61259e-10]) *).
Proof.
 intros h0.
 assert (h1 := l40 h0).
 assert (h2 := l43 h0).
 apply t31. exact h1. refine (subset r56 i65 i68 h2 _) ; finalize.
Qed.
Definition f94 := Float2 (-138803509020813579972853004608173524549873239801873739116495102291494674735074031694150282963358763215493130885) (-400).
Definition f95 := Float2 (1110428072166508639782824036865388196398985918414989912931960818331957397880592253553202263706870105723945047079) (-403).
Definition i69 := makepairF f94 f95.
Notation p70 := (BND r57 i69). (* BND(R * rhi * rhi * rhi, [-5.37529e-11, 5.37529e-11]) *)
Definition f96 := Float2 (800976780459508877303921482070654548543697371165297918416085967169407354114389240026996407025328018333670705793) (-394).
Definition i70 := makepairF f63 f96.
Notation p71 := (BND r47 i70). (* BND(R * rhi * rhi, [-1.98519e-08, 1.98519e-08]) *)
Definition f97 := Float2 (-3334025380561791605096498652473714471875450313207477810712612314083629401271343661641450273073496440019128331543) (-379).
Definition f98 := Float2 (3334025380561791605096498652473714471875450313207477810712612314083629401271343661641450273073496440019128331543) (-379).
Definition i71 := makepairF f97 f98.
Notation p72 := (BND _rhi i71). (* BND(rhi, [-0.0027077, 0.0027077]) *)
Lemma t32 : p71 -> p72 -> p70.
Proof.
 intros h0 h1.
 refine (mul_oo r47 _rhi i70 i71 i69 h0 h1 _) ; finalize.
Qed.
Lemma l44 : s1 -> p70 (* BND(R * rhi * rhi * rhi, [-5.37529e-11, 5.37529e-11]) *).
Proof.
 intros h0.
 assert (h1 := l33 h0).
 assert (h2 := l15 h0).
 apply t32. refine (subset r47 i43 i70 h1 _) ; finalize. refine (subset _rhi i1 i71 h2 _) ; finalize.
Qed.
Definition i72 := makepairF f77 f95.
Notation p73 := (BND r57 i72). (* BND(R * rhi * rhi * rhi, [-3.8147e-06, 5.37529e-11]) *)
Lemma t33 : p56 -> p73 -> p55.
Proof.
 intros h0 h1.
 refine (add r52 r57 i55 i72 i54 h0 h1 _) ; finalize.
Qed.
Lemma l38 : s1 -> p55 (* BND(R * R * R * R + R * R * R * rhi + R * R * rhi * rhi + R * rhi * rhi * rhi, [-7.62939e-06, 2.15012e-10]) *).
Proof.
 intros h0.
 assert (h1 := l39 h0).
 assert (h2 := l44 h0).
 apply t33. exact h1. refine (subset r57 i69 i72 h2 _) ; finalize.
Qed.
Definition f99 := Float2 (-1084402414225106006695837550036897204665672256290964065839728650790497657606086048243677918567618067604335119) (-393).
Definition f100 := Float2 (138803509020813568857067206404722842197206048805243400427485267301183700173579014175190773576655112653354895177) (-400).
Definition i73 := makepairF f99 f100.
Notation p74 := (BND r58 i73). (* BND(rhi * rhi * rhi * rhi, [-5.37529e-11, 5.37529e-11]) *)
Definition f101 := Float2 (1601953560919017626318776156940425017048671944884535311651554678569261967878400189450349623027097636524482207881) (-395).
Definition i74 := makepairF f67 f101.
Notation p75 := (BND r48 i74). (* BND(rhi * rhi * rhi, [-1.98519e-08, 1.98519e-08]) *)
Lemma t34 : p75 -> p72 -> p74.
Proof.
 intros h0 h1.
 refine (mul_oo r48 _rhi i74 i71 i73 h0 h1 _) ; finalize.
Qed.
Lemma l45 : s1 -> p74 (* BND(rhi * rhi * rhi * rhi, [-5.37529e-11, 5.37529e-11]) *).
Proof.
 intros h0.
 assert (h1 := l34 h0).
 assert (h2 := l15 h0).
 apply t34. refine (subset r48 i47 i74 h1 _) ; finalize. refine (subset _rhi i1 i71 h2 _) ; finalize.
Qed.
Definition i75 := makepairF f29 f100.
Notation p76 := (BND r58 i75). (* BND(rhi * rhi * rhi * rhi, [-7.62939e-06, 5.37529e-11]) *)
Lemma t35 : p55 -> p76 -> p54.
Proof.
 intros h0 h1.
 refine (add r51 r58 i54 i75 i53 h0 h1 _) ; finalize.
Qed.
Lemma l37 : s1 -> p54 (* BND(R * R * R * R + R * R * R * rhi + R * R * rhi * rhi + R * rhi * rhi * rhi + rhi * rhi * rhi * rhi, [-1.52588e-05, 2.68765e-10]) *).
Proof.
 intros h0.
 assert (h1 := l38 h0).
 assert (h2 := l45 h0).
 apply t35. exact h1. refine (subset r58 i73 i75 h2 _) ; finalize.
Qed.
Lemma t36 : p53 -> p54 -> p52.
Proof.
 intros h0 h1.
 refine (mul_po _c5 r50 i52 i53 i51 h0 h1 _) ; finalize.
Qed.
Lemma l35 : s1 -> p52 (* BND(c5 * (R * R * R * R + R * R * R * rhi + R * R * rhi * rhi + R * rhi * rhi * rhi + rhi * rhi * rhi * rhi), [-2.38419e-07, 2.23971e-12]) *).
Proof.
 intros h0.
 assert (h1 := l36 h0).
 assert (h2 := l37 h0).
 apply t36. exact h1. exact h2.
Qed.
Lemma t37 : p8 -> p52 -> p7.
Proof.
 intros h0 h1.
 refine (add r33 r49 i7 i51 i6 h0 h1 _) ; finalize.
Qed.
Lemma l8 : s1 -> p7 (* BND(5e-1 * (R + rhi) + c3 * (R * R + R * rhi + rhi * rhi) + c4 * (R * R * R + R * R * rhi + R * rhi * rhi + rhi * rhi * rhi) + c5 * (R * R * R * R + R * R * R * rhi + R * R * rhi * rhi + R * rhi * rhi * rhi + rhi * rhi * rhi * rhi), [-0.00270939, 0.00271137]) *).
Proof.
 intros h0.
 assert (h1 := l9 h0).
 assert (h2 := l35 h0).
 apply t37. exact h1. exact h2.
Qed.
Definition f102 := Float2 (801788478043155866151459435250768569313292858653074877022955337084229572936534326139286140253644097443218027) (-408).
Definition i76 := makepairF f49 f102.
Notation p77 := (BND r59 i76). (* BND(c6 * (R * R * R * R * R + R * R * R * R * rhi + R * R * R * rhi * rhi + R * R * rhi * rhi * rhi + R * rhi * rhi * rhi * rhi + rhi * rhi * rhi * rhi * rhi), [-9.53674e-07, 1.21289e-15]) *)
Definition f103 := Float2 (1) (-10).
Definition f104 := Float2 (3202560482380763) (-61).
Definition i77 := makepairF f103 f104.
Notation p78 := (BND _c6 i77). (* BND(c6, [0.000976562, 0.00138889]) *)
Lemma t38 : p78.
Proof.
 refine (constant2 _ i77 _) ; finalize.
Qed.
Lemma l47 : s1 -> p78 (* BND(c6, [0.000976562, 0.00138889]) *).
Proof.
 intros h0.
 apply t38.
Qed.
Definition f105 := Float2 (-1) (-11).
Definition f106 := Float2 (563757392063485463459720833906176908758862097207466302596618559757851262883588308280010832116837235037866787) (-398).
Definition i78 := makepairF f105 f106.
Notation p79 := (BND r60 i78). (* BND(R * R * R * R * R + R * R * R * R * rhi + R * R * R * rhi * rhi + R * R * rhi * rhi * rhi + R * rhi * rhi * rhi * rhi + rhi * rhi * rhi * rhi * rhi, [-0.000488281, 8.73281e-13]) *)
Definition f107 := Float2 (-1) (-12).
Definition f108 := Float2 (939595653439142476722301230421319797609036785239953827524486190379994973287176668218939635426919945809989049) (-399).
Definition i79 := makepairF f107 f108.
Notation p80 := (BND r61 i79). (* BND(R * R * R * R * R + R * R * R * R * rhi + R * R * R * rhi * rhi + R * R * rhi * rhi * rhi + R * rhi * rhi * rhi * rhi, [-0.000244141, 7.27734e-13]) *)
Definition f109 := Float2 (-1) (-13).
Definition f110 := Float2 (3006706091005256045904216760530176285588763598136748263286477184570619631588386761639257099347906736922774695) (-401).
Definition i80 := makepairF f109 f110.
Notation p81 := (BND r62 i80). (* BND(R * R * R * R * R + R * R * R * R * rhi + R * R * R * rhi * rhi + R * R * rhi * rhi * rhi, [-0.00012207, 5.82187e-13]) *)
Definition f111 := Float2 (-1) (-14).
Definition f112 := Float2 (4510059136507884249445604375568203469650203261820341573010982517708672753692583133736782410106542745678814423) (-402).
Definition i81 := makepairF f111 f112.
Notation p82 := (BND r63 i81). (* BND(R * R * R * R * R + R * R * R * R * rhi + R * R * R * rhi * rhi, [-6.10352e-05, 4.3664e-13]) *)
Definition f113 := Float2 (-1) (-15).
Definition f114 := Float2 (24053648728042050293519379255152811479064267535989413280868382863836306543276376436667695980708845275201866553) (-405).
Definition i82 := makepairF f113 f114.
Notation p83 := (BND r64 i82). (* BND(R * R * R * R * R + R * R * R * R * rhi, [-3.05176e-05, 2.91094e-13]) *)
Definition f115 := Float2 (12026824364021025628331100920304294603749829601969924613831257160698760174394771808155767616872262725321976249) (-405).
Definition i83 := makepairF f74 f115.
Notation p84 := (BND r65 i83). (* BND(R * R * R * R * R, [-1.52588e-05, 1.45547e-13]) *)
Definition f116 := Float2 (8675219313800850832513149951158182044576028212092112790488933832751235458773824293704014508851913170858721701) (-396).
Definition i84 := makepairF f80 f116.
Notation p85 := (BND r54 i84). (* BND(R * R * R * R, [-5.37529e-11, 5.37529e-11]) *)
Definition f117 := Float2 (-416753172570223984011859767823441757100356636286693625549375257109255814860461680923463024742072155551470605731) (-376).
Definition f118 := Float2 (416753172570223984011859767823441757100356636286693625549375257109255814860461680923463024742072155551470605731) (-376).
Definition i85 := makepairF f117 f118.
Notation p86 := (BND _R i85). (* BND(R, [-0.0027077, 0.0027077]) *)
Lemma t39 : p85 -> p86 -> p84.
Proof.
 intros h0 h1.
 refine (mul_oo r54 _R i84 i85 i83 h0 h1 _) ; finalize.
Qed.
Lemma l53 : s1 -> p84 (* BND(R * R * R * R * R, [-1.52588e-05, 1.45547e-13]) *).
Proof.
 intros h0.
 assert (h1 := l41 h0).
 assert (h2 := l14 h0).
 apply t39. refine (subset r54 i57 i84 h1 _) ; finalize. refine (subset _R i12 i85 h2 _) ; finalize.
Qed.
Definition f119 := Float2 (93959565343914255196783424491004038088394046359527255211227544555762081006887536160249440342473301170936643) (-398).
Definition i86 := makepairF f74 f119.
Notation p87 := (BND r66 i86). (* BND(R * R * R * R * rhi, [-1.52588e-05, 1.45547e-13]) *)
Definition f120 := Float2 (-104188293142555987659265582889803577246107822287733681584769134815113418789729489426295321033546763750597760361) (-374).
Definition f121 := Float2 (104188293142555987659265582889803577246107822287733681584769134815113418789729489426295321033546763750597760361) (-374).
Definition i87 := makepairF f120 f121.
Notation p88 := (BND _rhi i87). (* BND(rhi, [-0.0027077, 0.0027077]) *)
Lemma t40 : p85 -> p88 -> p87.
Proof.
 intros h0 h1.
 refine (mul_oo r54 _rhi i84 i87 i86 h0 h1 _) ; finalize.
Qed.
Lemma l54 : s1 -> p87 (* BND(R * R * R * R * rhi, [-1.52588e-05, 1.45547e-13]) *).
Proof.
 intros h0.
 assert (h1 := l41 h0).
 assert (h2 := l15 h0).
 apply t40. refine (subset r54 i57 i84 h1 _) ; finalize. refine (subset _rhi i1 i87 h2 _) ; finalize.
Qed.
Lemma t41 : p84 -> p87 -> p83.
Proof.
 intros h0 h1.
 refine (add r65 r66 i83 i86 i82 h0 h1 _) ; finalize.
Qed.
Lemma l52 : s1 -> p83 (* BND(R * R * R * R * R + R * R * R * R * rhi, [-3.05176e-05, 2.91094e-13]) *).
Proof.
 intros h0.
 assert (h1 := l53 h0).
 assert (h2 := l54 h0).
 apply t41. exact h1. exact h2.
Qed.
Definition f122 := Float2 (12026824364021023702045455749392816278137358558573319303219477277833075486264288633226563300143496690228648831) (-405).
Definition i88 := makepairF f113 f122.
Notation p89 := (BND r67 i88). (* BND(R * R * R * rhi * rhi, [-3.05176e-05, 1.45547e-13]) *)
Definition f123 := Float2 (34700877255203400551106150253769389951969610273979413175906550294741257242840696881885927459604486424792746239) (-398).
Definition i89 := makepairF f84 f123.
Notation p90 := (BND r55 i89). (* BND(R * R * R * rhi, [-5.37529e-11, 5.37529e-11]) *)
Lemma t42 : p90 -> p88 -> p89.
Proof.
 intros h0 h1.
 refine (mul_oo r55 _rhi i89 i87 i88 h0 h1 _) ; finalize.
Qed.
Lemma l55 : s1 -> p89 (* BND(R * R * R * rhi * rhi, [-3.05176e-05, 1.45547e-13]) *).
Proof.
 intros h0.
 assert (h1 := l42 h0).
 assert (h2 := l15 h0).
 apply t42. refine (subset r55 i60 i89 h1 _) ; finalize. refine (subset _rhi i1 i87 h2 _) ; finalize.
Qed.
Lemma t43 : p83 -> p89 -> p82.
Proof.
 intros h0 h1.
 refine (add r64 r67 i82 i88 i81 h0 h1 _) ; finalize.
Qed.
Lemma l51 : s1 -> p82 (* BND(R * R * R * R * R + R * R * R * R * rhi + R * R * R * rhi * rhi, [-6.10352e-05, 4.3664e-13]) *).
Proof.
 intros h0.
 assert (h1 := l52 h0).
 assert (h2 := l55 h0).
 apply t43. exact h1. exact h2.
Qed.
Definition f124 := Float2 (1503353045502627842362829145492149101527323934453154953561971851432566509484190389541731788589270728166734967) (-402).
Definition i90 := makepairF f111 f124.
Notation p91 := (BND r68 i90). (* BND(R * R * rhi * rhi * rhi, [-6.10352e-05, 1.45547e-13]) *)
Definition f125 := Float2 (2168804828450212360759981293931642141980688081751167609909315117870688380423465933872803412186297884515015867) (-394).
Definition i91 := makepairF f89 f125.
Notation p92 := (BND r56 i91). (* BND(R * R * rhi * rhi, [-5.37529e-11, 5.37529e-11]) *)
Definition f126 := Float2 (-813971040176218653588012366326590447235217361622919387381008865743073584294761636142932195574584091801545003) (-367).
Definition f127 := Float2 (813971040176218653588012366326590447235217361622919387381008865743073584294761636142932195574584091801545003) (-367).
Definition i92 := makepairF f126 f127.
Notation p93 := (BND _rhi i92). (* BND(rhi, [-0.0027077, 0.0027077]) *)
Lemma t44 : p92 -> p93 -> p91.
Proof.
 intros h0 h1.
 refine (mul_oo r56 _rhi i91 i92 i90 h0 h1 _) ; finalize.
Qed.
Lemma l56 : s1 -> p91 (* BND(R * R * rhi * rhi * rhi, [-6.10352e-05, 1.45547e-13]) *).
Proof.
 intros h0.
 assert (h1 := l43 h0).
 assert (h2 := l15 h0).
 apply t44. refine (subset r56 i65 i91 h1 _) ; finalize. refine (subset _rhi i1 i92 h2 _) ; finalize.
Qed.
Lemma t45 : p82 -> p91 -> p81.
Proof.
 intros h0 h1.
 refine (add r63 r68 i81 i90 i80 h0 h1 _) ; finalize.
Qed.
Lemma l50 : s1 -> p81 (* BND(R * R * R * R * R + R * R * R * R * rhi + R * R * R * rhi * rhi + R * R * rhi * rhi * rhi, [-0.00012207, 5.82187e-13]) *).
Proof.
 intros h0.
 assert (h1 := l51 h0).
 assert (h2 := l56 h0).
 apply t45. exact h1. exact h2.
Qed.
Definition f128 := Float2 (751676522751313860984988161155102904847383542823067046811467576949360261560319911236501442359773046317181501) (-401).
Definition i93 := makepairF f109 f128.
Notation p94 := (BND r69 i93). (* BND(R * rhi * rhi * rhi * rhi, [-0.00012207, 1.45547e-13]) *)
Definition f129 := Float2 (138803509020813579972853004608173524549873239801873739116495102291494674735074031694150282963358763215493130885) (-400).
Definition i94 := makepairF f94 f129.
Notation p95 := (BND r57 i94). (* BND(R * rhi * rhi * rhi, [-5.37529e-11, 5.37529e-11]) *)
Lemma t46 : p95 -> p88 -> p94.
Proof.
 intros h0 h1.
 refine (mul_oo r57 _rhi i94 i87 i93 h0 h1 _) ; finalize.
Qed.
Lemma l57 : s1 -> p94 (* BND(R * rhi * rhi * rhi * rhi, [-0.00012207, 1.45547e-13]) *).
Proof.
 intros h0.
 assert (h1 := l44 h0).
 assert (h2 := l15 h0).
 apply t46. refine (subset r57 i69 i94 h1 _) ; finalize. refine (subset _rhi i1 i87 h2 _) ; finalize.
Qed.
Lemma t47 : p81 -> p94 -> p80.
Proof.
 intros h0 h1.
 refine (add r62 r69 i80 i93 i79 h0 h1 _) ; finalize.
Qed.
Lemma l49 : s1 -> p80 (* BND(R * R * R * R * R + R * R * R * R * rhi + R * R * R * rhi * rhi + R * R * rhi * rhi * rhi + R * rhi * rhi * rhi * rhi, [-0.000244141, 7.27734e-13]) *).
Proof.
 intros h0.
 assert (h1 := l50 h0).
 assert (h2 := l57 h0).
 apply t47. exact h1. exact h2.
Qed.
Definition f130 := Float2 (187919130687828450197140437391034019908687409174978777668750929135707552479999948341082028806754524265744525) (-399).
Definition i95 := makepairF f107 f130.
Notation p96 := (BND r70 i95). (* BND(rhi * rhi * rhi * rhi * rhi, [-0.000244141, 1.45547e-13]) *)
Definition f131 := Float2 (1084402414225106006695837550036897204665672256290964065839728650790497657606086048243677918567618067604335119) (-393).
Definition i96 := makepairF f99 f131.
Notation p97 := (BND r58 i96). (* BND(rhi * rhi * rhi * rhi, [-5.37529e-11, 5.37529e-11]) *)
Lemma t48 : p97 -> p93 -> p96.
Proof.
 intros h0 h1.
 refine (mul_oo r58 _rhi i96 i92 i95 h0 h1 _) ; finalize.
Qed.
Lemma l58 : s1 -> p96 (* BND(rhi * rhi * rhi * rhi * rhi, [-0.000244141, 1.45547e-13]) *).
Proof.
 intros h0.
 assert (h1 := l45 h0).
 assert (h2 := l15 h0).
 apply t48. refine (subset r58 i73 i96 h1 _) ; finalize. refine (subset _rhi i1 i92 h2 _) ; finalize.
Qed.
Lemma t49 : p80 -> p96 -> p79.
Proof.
 intros h0 h1.
 refine (add r61 r70 i79 i95 i78 h0 h1 _) ; finalize.
Qed.
Lemma l48 : s1 -> p79 (* BND(R * R * R * R * R + R * R * R * R * rhi + R * R * R * rhi * rhi + R * R * rhi * rhi * rhi + R * rhi * rhi * rhi * rhi + rhi * rhi * rhi * rhi * rhi, [-0.000488281, 8.73281e-13]) *).
Proof.
 intros h0.
 assert (h1 := l49 h0).
 assert (h2 := l58 h0).
 apply t49. exact h1. exact h2.
Qed.
Lemma t50 : p78 -> p79 -> p77.
Proof.
 intros h0 h1.
 refine (mul_po _c6 r60 i77 i78 i76 h0 h1 _) ; finalize.
Qed.
Lemma l46 : s1 -> p77 (* BND(c6 * (R * R * R * R * R + R * R * R * R * rhi + R * R * R * rhi * rhi + R * R * rhi * rhi * rhi + R * rhi * rhi * rhi * rhi + rhi * rhi * rhi * rhi * rhi), [-9.53674e-07, 1.21289e-15]) *).
Proof.
 intros h0.
 assert (h1 := l47 h0).
 assert (h2 := l48 h0).
 apply t50. exact h1. exact h2.
Qed.
Lemma t51 : p7 -> p77 -> p6.
Proof.
 intros h0 h1.
 refine (add r32 r59 i6 i76 i5 h0 h1 _) ; finalize.
Qed.
Lemma l7 : s1 -> p6 (* BND(5e-1 * (R + rhi) + c3 * (R * R + R * rhi + rhi * rhi) + c4 * (R * R * R + R * R * rhi + R * rhi * rhi + rhi * rhi * rhi) + c5 * (R * R * R * R + R * R * R * rhi + R * R * rhi * rhi + R * rhi * rhi * rhi + rhi * rhi * rhi * rhi) + c6 * (R * R * R * R * R + R * R * R * R * rhi + R * R * R * rhi * rhi + R * R * rhi * rhi * rhi + R * rhi * rhi * rhi * rhi + rhi * rhi * rhi * rhi * rhi), [-0.00271034, 0.00271137]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 assert (h2 := l46 h0).
 apply t51. exact h1. exact h2.
Qed.
Lemma t52 : p2 -> p6 -> p5.
Proof.
 intros h0 h1.
 refine (mul_oo _delta r31 i2 i5 i4 h0 h1 _) ; finalize.
Qed.
Lemma l4 : s1 -> p5 (* BND(delta * (5e-1 * (R + rhi) + c3 * (R * R + R * rhi + rhi * rhi) + c4 * (R * R * R + R * R * rhi + R * rhi * rhi + rhi * rhi * rhi) + c5 * (R * R * R * R + R * R * R * rhi + R * R * rhi * rhi + R * rhi * rhi * rhi + rhi * rhi * rhi * rhi) + c6 * (R * R * R * R * R + R * R * R * R * rhi + R * R * R * rhi * rhi + R * R * rhi * rhi * rhi + R * rhi * rhi * rhi * rhi + rhi * rhi * rhi * rhi * rhi)), [-5.87934e-22, 5.87934e-22]) *).
Proof.
 intros h0.
 assert (h1 := l5 h0).
 assert (h2 := l7 h0).
 apply t52. exact h1. exact h2.
Qed.
Definition i97 := makepairF f32 f32.
Notation p98 := (REL r1 r30 i97). (* REL(QR - QH, delta * (5e-1 * (R + rhi) + c3 * (R * R + R * rhi + rhi * rhi) + c4 * (R * R * R + R * R * rhi + R * rhi * rhi + rhi * rhi * rhi) + c5 * (R * R * R * R + R * R * R * rhi + R * R * rhi * rhi + R * rhi * rhi * rhi + rhi * rhi * rhi * rhi) + c6 * (R * R * R * R * R + R * R * R * R * rhi + R * R * R * rhi * rhi + R * R * rhi * rhi * rhi + R * rhi * rhi * rhi * rhi + rhi * rhi * rhi * rhi * rhi)), [0, 0]) *)
Notation p99 := (r1 = r30). (* EQL(QR - QH, delta * (5e-1 * (R + rhi) + c3 * (R * R + R * rhi + rhi * rhi) + c4 * (R * R * R + R * R * rhi + R * rhi * rhi + rhi * rhi * rhi) + c5 * (R * R * R * R + R * R * R * rhi + R * R * rhi * rhi + R * rhi * rhi * rhi + rhi * rhi * rhi * rhi) + c6 * (R * R * R * R * R + R * R * R * R * rhi + R * R * R * rhi * rhi + R * R * rhi * rhi * rhi + R * rhi * rhi * rhi * rhi + rhi * rhi * rhi * rhi * rhi))) *)
Lemma t53 : p99.
Proof.
 refine (b1) ; finalize.
Qed.
Lemma l60 : s1 -> p99 (* EQL(QR - QH, delta * (5e-1 * (R + rhi) + c3 * (R * R + R * rhi + rhi * rhi) + c4 * (R * R * R + R * R * rhi + R * rhi * rhi + rhi * rhi * rhi) + c5 * (R * R * R * R + R * R * R * rhi + R * R * rhi * rhi + R * rhi * rhi * rhi + rhi * rhi * rhi * rhi) + c6 * (R * R * R * R * R + R * R * R * R * rhi + R * R * R * rhi * rhi + R * R * rhi * rhi * rhi + R * rhi * rhi * rhi * rhi + rhi * rhi * rhi * rhi * rhi))) *).
Proof.
 intros h0.
 apply t53.
Qed.
Notation p100 := (REL r30 r30 i97). (* REL(delta * (5e-1 * (R + rhi) + c3 * (R * R + R * rhi + rhi * rhi) + c4 * (R * R * R + R * R * rhi + R * rhi * rhi + rhi * rhi * rhi) + c5 * (R * R * R * R + R * R * R * rhi + R * R * rhi * rhi + R * rhi * rhi * rhi + rhi * rhi * rhi * rhi) + c6 * (R * R * R * R * R + R * R * R * R * rhi + R * R * R * rhi * rhi + R * R * rhi * rhi * rhi + R * rhi * rhi * rhi * rhi + rhi * rhi * rhi * rhi * rhi)), delta * (5e-1 * (R + rhi) + c3 * (R * R + R * rhi + rhi * rhi) + c4 * (R * R * R + R * R * rhi + R * rhi * rhi + rhi * rhi * rhi) + c5 * (R * R * R * R + R * R * R * rhi + R * R * rhi * rhi + R * rhi * rhi * rhi + rhi * rhi * rhi * rhi) + c6 * (R * R * R * R * R + R * R * R * R * rhi + R * R * R * rhi * rhi + R * R * rhi * rhi * rhi + R * rhi * rhi * rhi * rhi + rhi * rhi * rhi * rhi * rhi)), [0, 0]) *)
Lemma t54 : p100.
Proof.
 refine (rel_refl r30 i97 _) ; finalize.
Qed.
Lemma l61 : s1 -> p100 (* REL(delta * (5e-1 * (R + rhi) + c3 * (R * R + R * rhi + rhi * rhi) + c4 * (R * R * R + R * R * rhi + R * rhi * rhi + rhi * rhi * rhi) + c5 * (R * R * R * R + R * R * R * rhi + R * R * rhi * rhi + R * rhi * rhi * rhi + rhi * rhi * rhi * rhi) + c6 * (R * R * R * R * R + R * R * R * R * rhi + R * R * R * rhi * rhi + R * R * rhi * rhi * rhi + R * rhi * rhi * rhi * rhi + rhi * rhi * rhi * rhi * rhi)), delta * (5e-1 * (R + rhi) + c3 * (R * R + R * rhi + rhi * rhi) + c4 * (R * R * R + R * R * rhi + R * rhi * rhi + rhi * rhi * rhi) + c5 * (R * R * R * R + R * R * R * rhi + R * R * rhi * rhi + R * rhi * rhi * rhi + rhi * rhi * rhi * rhi) + c6 * (R * R * R * R * R + R * R * R * R * rhi + R * R * R * rhi * rhi + R * R * rhi * rhi * rhi + R * rhi * rhi * rhi * rhi + rhi * rhi * rhi * rhi * rhi)), [0, 0]) *).
Proof.
 intros h0.
 apply t54.
Qed.
Lemma t55 : p99 -> p100 -> p98.
Proof.
 intros h0 h1.
 refine (rel_rewrite_1 r1 r30 r30 i97 h0 h1) ; finalize.
Qed.
Lemma l59 : s1 -> p98 (* REL(QR - QH, delta * (5e-1 * (R + rhi) + c3 * (R * R + R * rhi + rhi * rhi) + c4 * (R * R * R + R * R * rhi + R * rhi * rhi + rhi * rhi * rhi) + c5 * (R * R * R * R + R * R * R * rhi + R * R * rhi * rhi + R * rhi * rhi * rhi + rhi * rhi * rhi * rhi) + c6 * (R * R * R * R * R + R * R * R * R * rhi + R * R * R * rhi * rhi + R * R * rhi * rhi * rhi + R * rhi * rhi * rhi * rhi + rhi * rhi * rhi * rhi * rhi)), [0, 0]) *).
Proof.
 intros h0.
 assert (h1 := l60 h0).
 assert (h2 := l61 h0).
 apply t55. exact h1. exact h2.
Qed.
Lemma t56 : p5 -> p98 -> p4.
Proof.
 intros h0 h1.
 refine (bnd_of_bnd_rel_o r1 r30 i4 i97 i4 h0 h1 _) ; finalize.
Qed.
Lemma l3 : s1 -> p4 (* BND(QR - QH, [-5.87934e-22, 5.87934e-22]) *).
Proof.
 intros h0.
 assert (h1 := l4 h0).
 assert (h2 := l59 h0).
 apply t56. exact h1. exact h2.
Qed.
Lemma l1 : s1 -> False.
Proof.
 intros h0.
 assert (h1 := l2 h0).
 assert (h2 := l3 h0).
 refine (simplify (Tatom false (Abnd 0%nat i3)) Tfalse (Abnd 0%nat i4) (List.cons r1 List.nil) h2 h1 _) ; finalize.
Qed.
End Generated_by_Gappa.
