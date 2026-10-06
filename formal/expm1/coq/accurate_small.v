Require Import Gappa.Gappa_library.
Section Generated_by_Gappa.
Variable _G : R.
Variable _E2 : R.
Notation r5 := ((_G + _E2)%R).
Notation r8 := (Float1 (1)).
Variable _m : R.
Notation r7 := ((r8 + _m)%R).
Notation r4 := ((r5 * r7)%R).
Notation _Y := ((r4 / _G)%R).
Notation r2 := ((_Y - r8)%R).
Notation r11 := ((_E2 / _G)%R).
Notation r13 := ((r8 + r11)%R).
Notation r12 := ((r13 * _m)%R).
Notation r10 := ((r11 + r12)%R).
Hypothesis a1 : (_G <> 0)%R -> r2 = r10.
Lemma b1 : NZR _G -> r2 = r10.
 intros h0.
 apply a1.
 exact h0.
Qed.
Definition f1 := Float2 (2515194542613972755215995142407867922594546230390721766640292924655168175401070375939947621823456634657431082763109440881) (-400).
Definition f2 := Float2 (1325069099153883788577801498830289864819149253046040951385509107676009653641584913984373955182262744178088843131751843365) (-399).
Definition i1 := makepairF f1 f2.
Notation p1 := (BND _G i1). (* BND(G, [0.974032, 1.02629]) *)
Definition f3 := Float2 (-323) (-134).
Definition f4 := Float2 (323) (-134).
Definition i2 := makepairF f3 f4.
Notation p2 := (BND _E2 i2). (* BND(E2, [-1.48314e-38, 1.48314e-38]) *)
Definition s3 := (p1 /\ p2).
Definition f5 := Float2 (-1) (-127).
Definition f6 := Float2 (0) (0).
Definition i3 := makepairF f5 f6.
Notation p3 := (BND _m i3). (* BND(m, [-5.87747e-39, 0]) *)
Definition s2 := (s3 /\ p3).
Definition f7 := Float2 (-1) (-123).
Definition f8 := Float2 (1) (-123).
Definition i4 := makepairF f7 f8.
Notation p4 := (BND r2 i4). (* BND(Y - 1, [-9.40395e-38, 9.40395e-38]) *)
Definition s4 := (not p4).
Definition s1 := (s2 /\ s4).
Lemma l2 : s1 -> s4.
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj2 h1).
Qed.
Definition f9 := Float2 (-2318029289223785508566899407091272253996394209851263665626858519813855179968735692877147544066184936487098308197817123401) (-525).
Definition f10 := Float2 (1672466819702058361152919614090519285404137885151470353118000079376364276292877477822523767622202956064999131759965781321) (-525).
Definition i5 := makepairF f9 f10.
Notation p5 := (BND r2 i5). (* BND(Y - 1, [-2.11043e-38, 1.52268e-38]) *)
Notation p6 := (BND r10 i5). (* BND(E2 / G + (1 + E2 / G) * m, [-2.11043e-38, 1.52268e-38]) *)
Definition f11 := Float2 (-1672466819702058361152919614090519285404137885151470353118000079376364276292877477822523767622202956064999131759965781321) (-525).
Definition i6 := makepairF f11 f10.
Notation p7 := (BND r11 i6). (* BND(E2 / G, [-1.52268e-38, 1.52268e-38]) *)
Lemma l8 : s1 -> s2.
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj1 h1).
Qed.
Lemma l7 : s1 -> s3.
Proof.
 intros h0.
 assert (h1 := l8 h0).
 exact (proj1 h1).
Qed.
Lemma l6 : s1 -> p2 (* BND(E2, [-1.48314e-38, 1.48314e-38]) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 exact (proj2 h1).
Qed.
Lemma l9 : s1 -> p1 (* BND(G, [0.974032, 1.02629]) *).
Proof.
 intros h0.
 assert (h1 := l7 h0).
 exact (proj1 h1).
Qed.
Definition f12 := Float2 (1) (1).
Definition i7 := makepairF f1 f12.
Notation p8 := (BND _G i7). (* BND(G, [0.974032, 2]) *)
Lemma t1 : p2 -> p8 -> p7.
Proof.
 intros h0 h1.
 refine (div_op _E2 _G i2 i7 i6 h0 h1 _) ; finalize.
Qed.
Lemma l5 : s1 -> p7 (* BND(E2 / G, [-1.52268e-38, 1.52268e-38]) *).
Proof.
 intros h0.
 assert (h1 := l6 h0).
 assert (h2 := l9 h0).
 apply t1. exact h1. refine (subset _G i1 i7 h2 _) ; finalize.
Qed.
Definition f13 := Float2 (-2521728396569246669585858566409191283563501268358567626987728282958948842483821152557124126734304611023824907960356805) (-517).
Definition i8 := makepairF f13 f6.
Notation p9 := (BND r12 i8). (* BND((1 + E2 / G) * m, [-5.87747e-39, 0]) *)
Definition f14 := Float2 (1) (-1).
Definition f15 := Float2 (2521728396569246669585858566409191283563501268358567626987728282958948842483821152557124126734304611023824907960356805) (-390).
Definition i9 := makepairF f14 f15.
Notation p10 := (BND r13 i9). (* BND(1 + E2 / G, [0.5, 1]) *)
Definition f16 := Float2 (1) (0).
Definition i10 := makepairF f16 f16.
Notation p11 := (BND r8 i10). (* BND(1, [1, 1]) *)
Lemma t2 : p11.
Proof.
 refine (constant1 _ i10 _) ; finalize.
Qed.
Lemma l12 : s1 -> p11 (* BND(1, [1, 1]) *).
Proof.
 intros h0.
 apply t2.
Qed.
Definition f17 := Float2 (-1) (-1).
Definition f18 := Float2 (38397955048779040239037505087222649107999673426611086421670010012200716580720581) (-390).
Definition i11 := makepairF f17 f18.
Notation p12 := (BND r11 i11). (* BND(E2 / G, [-0.5, 1.52268e-38]) *)
Lemma t3 : p11 -> p12 -> p10.
Proof.
 intros h0 h1.
 refine (add r8 r11 i10 i11 i9 h0 h1 _) ; finalize.
Qed.
Lemma l11 : s1 -> p10 (* BND(1 + E2 / G, [0.5, 1]) *).
Proof.
 intros h0.
 assert (h1 := l12 h0).
 assert (h2 := l5 h0).
 apply t3. exact h1. refine (subset r11 i6 i11 h2 _) ; finalize.
Qed.
Lemma l13 : s1 -> p3 (* BND(m, [-5.87747e-39, 0]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 exact (proj2 h1).
Qed.
Lemma t4 : p10 -> p3 -> p9.
Proof.
 intros h0 h1.
 refine (mul_pn r13 _m i9 i3 i8 h0 h1 _) ; finalize.
Qed.
Lemma l10 : s1 -> p9 (* BND((1 + E2 / G) * m, [-5.87747e-39, 0]) *).
Proof.
 intros h0.
 assert (h1 := l11 h0).
 assert (h2 := l13 h0).
 apply t4. exact h1. exact h2.
Qed.
Lemma t5 : p7 -> p9 -> p6.
Proof.
 intros h0 h1.
 refine (add r11 r12 i6 i8 i5 h0 h1 _) ; finalize.
Qed.
Lemma l4 : s1 -> p6 (* BND(E2 / G + (1 + E2 / G) * m, [-2.11043e-38, 1.52268e-38]) *).
Proof.
 intros h0.
 assert (h1 := l5 h0).
 assert (h2 := l10 h0).
 apply t5. exact h1. exact h2.
Qed.
Definition i12 := makepairF f6 f6.
Notation p13 := (REL r2 r10 i12). (* REL(Y - 1, E2 / G + (1 + E2 / G) * m, [0, 0]) *)
Notation p14 := (r2 = r10). (* EQL(Y - 1, E2 / G + (1 + E2 / G) * m) *)
Notation p15 := (NZR _G). (* NZR(G) *)
Definition i13 := makepairF f14 f12.
Notation p16 := (ABS _G i13). (* ABS(G, [0.5, 2]) *)
Notation p17 := (BND _G i13). (* BND(G, [0.5, 2]) *)
Lemma t6 : p17 -> p16.
Proof.
 intros h0.
 refine (abs_of_bnd_p _G i13 i13 h0 _) ; finalize.
Qed.
Lemma l17 : s1 -> p16 (* ABS(G, [0.5, 2]) *).
Proof.
 intros h0.
 assert (h1 := l9 h0).
 apply t6. refine (subset _G i1 i13 h1 _) ; finalize.
Qed.
Lemma t7 : p16 -> p15.
Proof.
 intros h0.
 refine (nzr_of_abs _G i13 h0 _) ; finalize.
Qed.
Lemma l16 : s1 -> p15 (* NZR(G) *).
Proof.
 intros h0.
 assert (h1 := l17 h0).
 apply t7. exact h1.
Qed.
Lemma t8 : p15 -> p14.
Proof.
 intros h0.
 refine (b1 h0) ; finalize.
Qed.
Lemma l15 : s1 -> p14 (* EQL(Y - 1, E2 / G + (1 + E2 / G) * m) *).
Proof.
 intros h0.
 assert (h1 := l16 h0).
 apply t8. exact h1.
Qed.
Notation p18 := (REL r10 r10 i12). (* REL(E2 / G + (1 + E2 / G) * m, E2 / G + (1 + E2 / G) * m, [0, 0]) *)
Lemma t9 : p18.
Proof.
 refine (rel_refl r10 i12 _) ; finalize.
Qed.
Lemma l18 : s1 -> p18 (* REL(E2 / G + (1 + E2 / G) * m, E2 / G + (1 + E2 / G) * m, [0, 0]) *).
Proof.
 intros h0.
 apply t9.
Qed.
Lemma t10 : p14 -> p18 -> p13.
Proof.
 intros h0 h1.
 refine (rel_rewrite_1 r2 r10 r10 i12 h0 h1) ; finalize.
Qed.
Lemma l14 : s1 -> p13 (* REL(Y - 1, E2 / G + (1 + E2 / G) * m, [0, 0]) *).
Proof.
 intros h0.
 assert (h1 := l15 h0).
 assert (h2 := l18 h0).
 apply t10. exact h1. exact h2.
Qed.
Lemma t11 : p6 -> p13 -> p5.
Proof.
 intros h0 h1.
 refine (bnd_of_bnd_rel_o r2 r10 i5 i12 i5 h0 h1 _) ; finalize.
Qed.
Lemma l3 : s1 -> p5 (* BND(Y - 1, [-2.11043e-38, 1.52268e-38]) *).
Proof.
 intros h0.
 assert (h1 := l4 h0).
 assert (h2 := l14 h0).
 apply t11. exact h1. exact h2.
Qed.
Lemma l1 : s1 -> False.
Proof.
 intros h0.
 assert (h1 := l2 h0).
 assert (h2 := l3 h0).
 refine (simplify (Tatom false (Abnd 0%nat i4)) Tfalse (Abnd 0%nat i5) (List.cons r2 List.nil) h2 h1 _) ; finalize.
Qed.
End Generated_by_Gappa.
