Require Import Gappa.Gappa_library.
Section Generated_by_Gappa.
Variable _X1 : R.
Definition f1 := Float2 (1807574914660836012759143420402108312030794054980456458981461549578453335411788836240751747296096482005132220380923245363) (-400).
Definition f2 := Float2 (1) (0).
Definition i1 := makepairF f1 f2.
Notation p1 := (BND _X1 i1). (* BND(X1, [0.7, 1]) *)
Variable _E1 : R.
Definition f3 := Float2 (-259) (-218).
Definition f4 := Float2 (259) (-218).
Definition i2 := makepairF f3 f4.
Notation p2 := (BND _E1 i2). (* BND(E1, [-6.14838e-64, 6.14838e-64]) *)
Definition s3 := (p1 /\ p2).
Variable _dr : R.
Definition f5 := Float2 (-903) (-209).
Definition f6 := Float2 (903) (-209).
Definition i3 := makepairF f5 f6.
Notation p3 := (BND _dr i3). (* BND(dr, [-1.09754e-60, 1.09754e-60]) *)
Definition s2 := (s3 /\ p3).
Notation r7 := (Float1 (1)).
Notation r8 := ((_E1 / _X1)%R).
Notation r6 := ((r7 + r8)%R).
Notation r9 := ((r7 + _dr)%R).
Notation _Y := ((r6 * r9)%R).
Notation r4 := ((_Y - r7)%R).
Definition f7 := Float2 (-1) (-198).
Definition f8 := Float2 (1) (-198).
Definition i4 := makepairF f7 f8.
Notation p4 := (BND r4 i4). (* BND(Y - 1, [-2.48921e-60, 2.48921e-60]) *)
Definition s4 := (not p4).
Definition s1 := (s2 /\ s4).
Lemma l2 : s1 -> s4.
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj2 h1).
Qed.
Definition f9 := Float2 (-2836379526927567880382229278178443844461969217076343313793025) (-400).
Definition f10 := Float2 (709094881731891970095557319544610961115492304269085828448257) (-398).
Definition i5 := makepairF f9 f10.
Notation p5 := (BND r4 i5). (* BND(Y - 1, [-1.09841e-60, 1.09841e-60]) *)
Definition f11 := Float2 (2582249878086908589655919172003011874329705792829223512830656520161120694448960812400367174836293369466686095629433700351) (-400).
Definition f12 := Float2 (645562469521727147413979793000752968582426448207305878207665548230043637396180394214730882930995573351280062079015321601) (-398).
Definition i6 := makepairF f11 f12.
Notation p6 := (BND _Y i6). (* BND(Y, [1, 1]) *)
Definition f13 := Float2 (2582249878086908589655919172003011874329705792829223512830659354272554221535325684259291753097680239680169271141016272895) (-400).
Definition f14 := Float2 (1291124939043454294827959586001505937164852896414611756415329679404370511249178352499999476731297711595818536402239356929) (-399).
Definition i7 := makepairF f13 f14.
Notation p7 := (BND r6 i7). (* BND(1 + E1 / X1, [1, 1]) *)
Definition i8 := makepairF f2 f2.
Notation p8 := (BND r7 i8). (* BND(1, [1, 1]) *)
Lemma t1 : p8.
Proof.
 refine (constant1 _ i8 _) ; finalize.
Qed.
Lemma l6 : s1 -> p8 (* BND(1, [1, 1]) *).
Proof.
 intros h0.
 apply t1.
Qed.
Definition f15 := Float2 (-2268093400481515510370353600182457591755733900831731220481) (-400).
Definition f16 := Float2 (1134046700240757755185176800091228795877866950415865610241) (-399).
Definition i9 := makepairF f15 f16.
Notation p9 := (BND r8 i9). (* BND(E1 / X1, [-8.7834e-64, 8.7834e-64]) *)
Lemma l10 : s1 -> s2.
Proof.
 intros h0.
 assert (h1 := h0).
 exact (proj1 h1).
Qed.
Lemma l9 : s1 -> s3.
Proof.
 intros h0.
 assert (h1 := l10 h0).
 exact (proj1 h1).
Qed.
Lemma l8 : s1 -> p2 (* BND(E1, [-6.14838e-64, 6.14838e-64]) *).
Proof.
 intros h0.
 assert (h1 := l9 h0).
 exact (proj2 h1).
Qed.
Lemma l11 : s1 -> p1 (* BND(X1, [0.7, 1]) *).
Proof.
 intros h0.
 assert (h1 := l9 h0).
 exact (proj1 h1).
Qed.
Definition f17 := Float2 (2196985607385338267342526298122683245635824405562412079513) (-191).
Definition i10 := makepairF f17 f2.
Notation p10 := (BND _X1 i10). (* BND(X1, [0.7, 1]) *)
Lemma t2 : p2 -> p10 -> p9.
Proof.
 intros h0 h1.
 refine (div_op _E1 _X1 i2 i10 i9 h0 h1 _) ; finalize.
Qed.
Lemma l7 : s1 -> p9 (* BND(E1 / X1, [-8.7834e-64, 8.7834e-64]) *).
Proof.
 intros h0.
 assert (h1 := l8 h0).
 assert (h2 := l11 h0).
 apply t2. exact h1. refine (subset _X1 i1 i10 h2 _) ; finalize.
Qed.
Lemma t3 : p8 -> p9 -> p7.
Proof.
 intros h0 h1.
 refine (add r7 r8 i8 i9 i7 h0 h1 _) ; finalize.
Qed.
Lemma l5 : s1 -> p7 (* BND(1 + E1 / X1, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l6 h0).
 assert (h2 := l7 h0).
 apply t3. exact h1. exact h2.
Qed.
Definition f18 := Float2 (822752278660603021077484591278675252491367932816789931674303609) (-209).
Definition f19 := Float2 (822752278660603021077484591278675252491367932816789931674305415) (-209).
Definition i11 := makepairF f18 f19.
Notation p11 := (BND r9 i11). (* BND(1 + dr, [1, 1]) *)
Lemma l13 : s1 -> p3 (* BND(dr, [-1.09754e-60, 1.09754e-60]) *).
Proof.
 intros h0.
 assert (h1 := l10 h0).
 exact (proj2 h1).
Qed.
Lemma t4 : p8 -> p3 -> p11.
Proof.
 intros h0 h1.
 refine (add r7 _dr i8 i3 i11 h0 h1 _) ; finalize.
Qed.
Lemma l12 : s1 -> p11 (* BND(1 + dr, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l6 h0).
 assert (h2 := l13 h0).
 apply t4. exact h1. exact h2.
Qed.
Lemma t5 : p7 -> p11 -> p6.
Proof.
 intros h0 h1.
 refine (mul_pp r6 r9 i7 i11 i6 h0 h1 _) ; finalize.
Qed.
Lemma l4 : s1 -> p6 (* BND(Y, [1, 1]) *).
Proof.
 intros h0.
 assert (h1 := l5 h0).
 assert (h2 := l12 h0).
 apply t5. exact h1. exact h2.
Qed.
Lemma t6 : p6 -> p8 -> p5.
Proof.
 intros h0 h1.
 refine (sub _Y r7 i6 i8 i5 h0 h1 _) ; finalize.
Qed.
Lemma l3 : s1 -> p5 (* BND(Y - 1, [-1.09841e-60, 1.09841e-60]) *).
Proof.
 intros h0.
 assert (h1 := l4 h0).
 assert (h2 := l6 h0).
 apply t6. exact h1. exact h2.
Qed.
Lemma l1 : s1 -> False.
Proof.
 intros h0.
 assert (h1 := l2 h0).
 assert (h2 := l3 h0).
 refine (simplify (Tatom false (Abnd 0%nat i4)) Tfalse (Abnd 0%nat i5) (List.cons r4 List.nil) h2 h1 _) ; finalize.
Qed.
End Generated_by_Gappa.
