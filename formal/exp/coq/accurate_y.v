Require Import Gappa.Gappa_library.
Section Generated_by_Gappa.
Variable _Tj : R.
Variable _X1 : R.
Notation r9 := (Float1 (1)).
Variable _eT : R.
Notation r8 := ((r9 + _eT)%R).
Notation r7 := ((_Tj * r8)%R).
Variable _E1 : R.
Notation _H1 := ((_X1 + _E1)%R).
Notation r6 := ((r7 * _H1)%R).
Variable _mY : R.
Notation r13 := ((r9 + _mY)%R).
Notation _Y := ((r6 * r13)%R).
Notation r15 := ((_Tj * _X1)%R).
Notation r4 := ((_Y - r15)%R).
Notation r3 := ((r4 / r15)%R).
Notation r18 := ((r8 * r13)%R).
Notation r20 := ((_E1 / _X1)%R).
Notation r19 := ((r9 + r20)%R).
Notation r17 := ((r18 * r19)%R).
Notation r16 := ((r17 - r9)%R).
Hypothesis a1 : (_Tj <> 0)%R -> (_X1 <> 0)%R -> r3 = r16.
Lemma b1 : NZR _Tj -> NZR _X1 -> r3 = r16.
 intros h0 h1.
 apply a1.
 exact h0.
 exact h1.
Qed.
Definition f1 := Float2 (1) (0).
Definition f2 := Float2 (1) (1).
Definition i1 := makepairF f1 f2.
Notation p1 := (BND _Tj i1). (* BND(Tj, [1, 2]) *)
Definition f3 := Float2 (2574503128452647863886951414487002838706716675450735842292167378471025679150790671045756417220297417941595462456829250895) (-400).
Definition f4 := Float2 (1294998313860584657712443464759510454976347455103855591684575667305134782441445859106767144669989122465105440744332867929) (-399).
Definition i2 := makepairF f3 f4.
Notation p2 := (BND _X1 i2). (* BND(X1, [0.997, 1.003]) *)
Definition s5 := (p1 /\ p2).
Definition f5 := Float2 (-1) (-127).
Definition f6 := Float2 (1) (-127).
Definition i3 := makepairF f5 f6.
Notation p3 := (BND _eT i3). (* BND(eT, [-5.87747e-39, 5.87747e-39]) *)
Definition s4 := (s5 /\ p3).
Definition f7 := Float2 (0) (0).
Definition i4 := makepairF f5 f7.
Notation p4 := (BND _mY i4). (* BND(mY, [-5.87747e-39, 0]) *)
Definition s3 := (s4 /\ p4).
Definition f8 := Float2 (-521) (-135).
Definition f9 := Float2 (521) (-135).
Definition i5 := makepairF f8 f9.
Notation p5 := (BND _E1 i5). (* BND(E1, [-1.19616e-38, 1.19616e-38]) *)
Definition s2 := (s3 /\ p5).
Definition f10 := Float2 (-1) (-124).
Definition f11 := Float2 (1) (-124).
Definition i6 := makepairF f10 f11.
Notation p6 := (BND r3 i6). (* BND((Y - Tj * X1) / (Tj * X1), [-4.70198e-38, 4.70198e-38]) *)
Definition s6 := (not p6).
Definition s1 := (s2 /\ s6).
Lemma l2 : s1 -> s6.
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj2 h1).
Qed.
Definition f12 := Float2 (-61334914969846043575271464303182193844295084864115091158518261571860414918977502477) (-400).
Definition f13 := Float2 (23078907124666267604356584078061726193393374610438964685263489846326005709417263799) (-399).
Definition i7 := makepairF f12 f13.
Notation p7 := (BND r3 i7). (* BND((Y - Tj * X1) / (Tj * X1), [-2.37525e-38, 1.7875e-38]) *)
Notation p8 := (BND r16 i7). (* BND((1 + eT) * (1 + mY) * (1 + E1 / X1) - 1, [-2.37525e-38, 1.7875e-38]) *)
Definition f14 := Float2 (2582249878086908589655919172003011874268370877859377469255387892237465428172546109765530262121619569864042757053769990899) (-400).
Definition f15 := Float2 (1291124939043454294827959586001505937187931803539278024019686262348385537201813971925261641325332405564277591695791010487) (-399).
Definition i8 := makepairF f14 f15.
Notation p9 := (BND r17 i8). (* BND((1 + eT) * (1 + mY) * (1 + E1 / X1), [1, 1]) *)
Definition f16 := Float2 (28948022309329048855892746252171976962977213799489202546401021394546514198529) (-254).
Definition f17 := Float2 (170141183460469231731687303715884105729) (-127).
Definition i9 := makepairF f16 f17.
Notation p10 := (BND r18 i9). (* BND((1 + eT) * (1 + mY), [1, 1]) *)
Definition f18 := Float2 (170141183460469231731687303715884105727) (-127).
Definition i10 := makepairF f18 f17.
Notation p11 := (BND r8 i10). (* BND(1 + eT, [1, 1]) *)
Definition i11 := makepairF f1 f1.
Notation p12 := (BND r9 i11). (* BND(1, [1, 1]) *)
Lemma t1 : p12.
Proof.
 refine (constant1 _ i11 _) ; finalize.
Qed.
Lemma l8 : s1 -> p12 (* BND(1, [1, 1]) *).
Proof.
 intros h0.
 apply t1.
Qed.
Lemma l12 : s1 -> s2.
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj1 h1).
Qed.
Lemma l11 : s1 -> s3.
Proof.
 intros h0.
 assert (h1 := l12 h0).
 exact (proj1 h1).
Qed.
Lemma l10 : s1 -> s4.
Proof.
 intros h0.
 assert (h1 := l11 h0).
 exact (proj1 h1).
Qed.
Lemma l9 : s1 -> p3 (* BND(eT, [-5.87747e-39, 5.87747e-39]) *).
Proof.
 intros h0.
 assert (h1 := l10 h0).
 exact (proj2 h1).
Qed.
Lemma t2 : p12 -> p3 -> p11.
Proof.
 intros h0 h1.
 refine (add r9 _eT i11 i3 i10 h0 h1 _) ; finalize.
Qed.
Lemma l7 : s1 -> p11 (* BND(1 + eT, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 assert (h2 := l9 h0).
 apply t2. exact h1. exact h2.
Qed.
Definition i12 := makepairF f18 f1.
Notation p13 := (BND r13 i12). (* BND(1 + mY, [1, 1]) *)
Lemma l14 : s1 -> p4 (* BND(mY, [-5.87747e-39, 0]) *).
Proof.
 intros h0.
 assert (h1 := l11 h0).
 exact (proj2 h1).
Qed.
Lemma t3 : p12 -> p4 -> p13.
Proof.
 intros h0 h1.
 refine (add r9 _mY i11 i4 i12 h0 h1 _) ; finalize.
Qed.
Lemma l13 : s1 -> p13 (* BND(1 + mY, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 assert (h2 := l14 h0).
 apply t3. exact h1. exact h2.
Qed.
Lemma t4 : p11 -> p13 -> p10.
Proof.
 intros h0 h1.
 refine (mul_pp r8 r13 i10 i12 i9 h0 h1 _) ; finalize.
Qed.
Lemma l6 : s1 -> p10 (* BND((1 + eT) * (1 + mY), [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 assert (h2 := l13 h0).
 apply t4. exact h1. exact h2.
Qed.
Definition f19 := Float2 (645562469521727147413979793000752968574681269825101121497126121132895727772095084276887528957282855690149603635686319715) (-398).
Definition f20 := Float2 (645562469521727147413979793000752968590171626589510634918203557137428083236325513037935147682786060027801982350687426973) (-398).
Definition i13 := makepairF f19 f20.
Notation p14 := (BND r19 i13). (* BND(1 + E1 / X1, [1, 1]) *)
Definition f21 := Float2 (-7745178382204756710538718002266177732115214380523809362751602168826189357500553629) (-398).
Definition f22 := Float2 (7745178382204756710538718002266177732115214380523809362751602168826189357500553629) (-398).
Definition i14 := makepairF f21 f22.
Notation p15 := (BND r20 i14). (* BND(E1 / X1, [-1.19976e-38, 1.19976e-38]) *)
Lemma l17 : s1 -> p5 (* BND(E1, [-1.19616e-38, 1.19616e-38]) *).
Proof.
 intros h0.
 assert (h1 := l12 h0).
 exact (proj2 h1).
Qed.
Lemma l19 : s1 -> s5.
Proof.
 intros h0.
 assert (h1 := l10 h0).
 exact (proj1 h1).
Qed.
Lemma l18 : s1 -> p2 (* BND(X1, [0.997, 1.003]) *).
Proof.
 intros h0.
 assert (h1 := l19 h0).
 exact (proj2 h1).
Qed.
Definition f23 := Float2 (60526277673407871365834485034470260935077488079218221959001780390927736635924777271) (-275).
Definition i15 := makepairF f23 f2.
Notation p16 := (BND _X1 i15). (* BND(X1, [0.997, 2]) *)
Lemma t5 : p5 -> p16 -> p15.
Proof.
 intros h0 h1.
 refine (div_op _E1 _X1 i5 i15 i14 h0 h1 _) ; finalize.
Qed.
Lemma l16 : s1 -> p15 (* BND(E1 / X1, [-1.19976e-38, 1.19976e-38]) *).
Proof.
 intros h0.
 assert (h1 := l17 h0).
 assert (h2 := l18 h0).
 apply t5. exact h1. refine (subset _X1 i2 i15 h2 _) ; finalize.
Qed.
Lemma t6 : p12 -> p15 -> p14.
Proof.
 intros h0 h1.
 refine (add r9 r20 i11 i14 i13 h0 h1 _) ; finalize.
Qed.
Lemma l15 : s1 -> p14 (* BND(1 + E1 / X1, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 assert (h2 := l16 h0).
 apply t6. exact h1. exact h2.
Qed.
Lemma t7 : p10 -> p14 -> p9.
Proof.
 intros h0 h1.
 refine (mul_pp r18 r19 i9 i13 i8 h0 h1 _) ; finalize.
Qed.
Lemma l5 : s1 -> p9 (* BND((1 + eT) * (1 + mY) * (1 + E1 / X1), [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l6 h0).
 assert (h2 := l15 h0).
 apply t7. exact h1. exact h2.
Qed.
Lemma t8 : p9 -> p12 -> p8.
Proof.
 intros h0 h1.
 refine (sub r17 r9 i8 i11 i7 h0 h1 _) ; finalize.
Qed.
Lemma l4 : s1 -> p8 (* BND((1 + eT) * (1 + mY) * (1 + E1 / X1) - 1, [-2.37525e-38, 1.7875e-38]) *).
Proof.
 intros h0.
 assert (h1 := l5 h0).
 assert (h2 := l8 h0).
 apply t8. exact h1. exact h2.
Qed.
Definition i16 := makepairF f7 f7.
Notation p17 := (REL r3 r16 i16). (* REL((Y - Tj * X1) / (Tj * X1), (1 + eT) * (1 + mY) * (1 + E1 / X1) - 1, [0, 0]) *)
Notation p18 := (r3 = r16). (* EQL((Y - Tj * X1) / (Tj * X1), (1 + eT) * (1 + mY) * (1 + E1 / X1) - 1) *)
Notation p19 := (NZR _Tj). (* NZR(Tj) *)
Notation p20 := (ABS _Tj i1). (* ABS(Tj, [1, 2]) *)
Lemma l24 : s1 -> p1 (* BND(Tj, [1, 2]) *).
Proof.
 intros h0.
 assert (h1 := l19 h0).
 exact (proj1 h1).
Qed.
Lemma t9 : p1 -> p20.
Proof.
 intros h0.
 refine (abs_of_bnd_p _Tj i1 i1 h0 _) ; finalize.
Qed.
Lemma l23 : s1 -> p20 (* ABS(Tj, [1, 2]) *).
Proof.
 intros h0.
 assert (h1 := l24 h0).
 apply t9. exact h1.
Qed.
Lemma t10 : p20 -> p19.
Proof.
 intros h0.
 refine (nzr_of_abs _Tj i1 h0 _) ; finalize.
Qed.
Lemma l22 : s1 -> p19 (* NZR(Tj) *).
Proof.
 intros h0.
 assert (h1 := l23 h0).
 apply t10. exact h1.
Qed.
Notation p21 := (NZR _X1). (* NZR(X1) *)
Definition f24 := Float2 (1) (-1).
Definition i17 := makepairF f24 f2.
Notation p22 := (ABS _X1 i17). (* ABS(X1, [0.5, 2]) *)
Notation p23 := (BND _X1 i17). (* BND(X1, [0.5, 2]) *)
Lemma t11 : p23 -> p22.
Proof.
 intros h0.
 refine (abs_of_bnd_p _X1 i17 i17 h0 _) ; finalize.
Qed.
Lemma l26 : s1 -> p22 (* ABS(X1, [0.5, 2]) *).
Proof.
 intros h0.
 assert (h1 := l18 h0).
 apply t11. refine (subset _X1 i2 i17 h1 _) ; finalize.
Qed.
Lemma t12 : p22 -> p21.
Proof.
 intros h0.
 refine (nzr_of_abs _X1 i17 h0 _) ; finalize.
Qed.
Lemma l25 : s1 -> p21 (* NZR(X1) *).
Proof.
 intros h0.
 assert (h1 := l26 h0).
 apply t12. exact h1.
Qed.
Lemma t13 : p19 -> p21 -> p18.
Proof.
 intros h0 h1.
 refine (b1 h0 h1) ; finalize.
Qed.
Lemma l21 : s1 -> p18 (* EQL((Y - Tj * X1) / (Tj * X1), (1 + eT) * (1 + mY) * (1 + E1 / X1) - 1) *).
Proof.
 intros h0.
 assert (h1 := l22 h0).
 assert (h2 := l25 h0).
 apply t13. exact h1. exact h2.
Qed.
Notation p24 := (REL r16 r16 i16). (* REL((1 + eT) * (1 + mY) * (1 + E1 / X1) - 1, (1 + eT) * (1 + mY) * (1 + E1 / X1) - 1, [0, 0]) *)
Lemma t14 : p24.
Proof.
 refine (rel_refl r16 i16 _) ; finalize.
Qed.
Lemma l27 : s1 -> p24 (* REL((1 + eT) * (1 + mY) * (1 + E1 / X1) - 1, (1 + eT) * (1 + mY) * (1 + E1 / X1) - 1, [0, 0]) *).
Proof.
 intros h0.
 apply t14.
Qed.
Lemma t15 : p18 -> p24 -> p17.
Proof.
 intros h0 h1.
 refine (rel_rewrite_1 r3 r16 r16 i16 h0 h1) ; finalize.
Qed.
Lemma l20 : s1 -> p17 (* REL((Y - Tj * X1) / (Tj * X1), (1 + eT) * (1 + mY) * (1 + E1 / X1) - 1, [0, 0]) *).
Proof.
 intros h0.
 assert (h1 := l21 h0).
 assert (h2 := l27 h0).
 apply t15. exact h1. exact h2.
Qed.
Lemma t16 : p8 -> p17 -> p7.
Proof.
 intros h0 h1.
 refine (bnd_of_bnd_rel_o r3 r16 i7 i16 i7 h0 h1 _) ; finalize.
Qed.
Lemma l3 : s1 -> p7 (* BND((Y - Tj * X1) / (Tj * X1), [-2.37525e-38, 1.7875e-38]) *).
Proof.
 intros h0.
 assert (h1 := l4 h0).
 assert (h2 := l20 h0).
 apply t16. exact h1. exact h2.
Qed.
Lemma l1 : s1 -> False.
Proof.
 intros h0.
 assert (h1 := l2 h0).
 assert (h2 := l3 h0).
 refine (simplify (Tatom false (Abnd 0%nat i6)) Tfalse (Abnd 0%nat i7) (List.cons r3 List.nil) h2 h1 _) ; finalize.
Qed.
End Generated_by_Gappa.
