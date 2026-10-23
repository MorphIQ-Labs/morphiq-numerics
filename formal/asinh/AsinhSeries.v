(** asinh's series below 2^-7: the transcription's evaluation against
    formal/asinh/series_tail.g, and the fast value against [arcsinh]. *)
From Coq Require Import Reals ZArith Lia Lra Psatz List.
From Flocq Require Import Core Mult_error IEEE754.Binary IEEE754.Bits.
From Gappa Require Import Gappa_library.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Mul IEEE64Eft Grid Encodings.
From Interval Require Import Tactic.
Require Import StageGappa AsinTables AsinKernel AsinSqrtStep AsinNormal AsinSegment AsinSeriesSmall AsinhTables AsinhKernel AsinhWithin AsinhApprox.
Require asinh_series_tail.
Open Scope R_scope.

(** The certificate's positive coefficients. *)
Definition q0c : R := IZR 6004799503160661 * bpow radix2 (-55).
Definition q1c : R := IZR 1351079888189287 * bpow radix2 (-54).
Definition q2c : R := IZR 3216854006803669 * bpow radix2 (-56).
Definition q3c : R := IZR 8649021371757797 * bpow radix2 (-58).

Lemma series_tail_certificate x_ : bpow radix2 (-26) <= x_ <= 0.0078126 ->
  let zh := rn x_ in
  let uh := rn (zh * zh) in
  let p3 := rn (q2c - rn (uh * q3c)) in
  let p2 := rn (q1c - rn (uh * p3)) in
  let ps := rn (q0c - rn (uh * p2)) in
  let a3 := rn (zh * uh) in
  let tail := rn (a3 * ps) in
  let P := q0c - zh * zh * (q1c - zh * zh * (q2c - zh * zh * q3c)) in
  let Tx := zh * zh * zh * P in
  Rabs ((tail - Tx) / Tx) <= / 2 ^ 51.
Proof.
  intros X zh uh p3 p2 ps a3 tail P Tx.
  assert (G : BND ((tail - Tx) / Tx) (makepairF (Float2 (-1) (-51)) (Float2 1 (-51)))).
  { subst zh uh p3 p2 ps a3 tail P Tx. unfold q0c, q1c, q2c, q3c.
    gappa_goal (asinh_series_tail.l1 x_). }
  apply bnd_to in G. destruct G as [G1 G2]. bpow_num_all.
  apply Rabs_le. lra.
Qed.

(** Products and sums of binary64 values of bounded magnitude, signs free. *)
Lemma mul_abs a b ea eb : finite a -> finite b ->
  Rabs (B a) <= bpow radix2 ea -> Rabs (B b) <= bpow radix2 eb -> (-500 <= ea)%Z -> (-500 <= eb)%Z -> (ea <= 0)%Z -> (eb <= 0)%Z ->
  finite (fmul a b) /\ B (fmul a b) = rndF (B a * B b) /\ Rabs (B (fmul a b)) <= bpow radix2 (ea + eb).
Proof.
  intros Fa Fb Ha Hb H1 H2 H3 H4.
  assert (Hp : Rabs (B a * B b) <= bpow radix2 (ea + eb)).
  { rewrite Rabs_mult, bpow_plus. apply Rmult_le_compat; try apply Rabs_pos; assumption. }
  assert (Hbnd : bnd 1 (ea + eb) (B a * B b)) by (unfold bnd; change (IZR 1) with 1; rewrite Rmult_1_l; exact Hp).
  destruct (fmul_bnd 1 (ea + eb) a b Fa Fb ltac:(lia) ltac:(lia) ltac:(apply Z.pow_gt_1; lia) ltac:(lia) Hbnd) as [F [E Bd]].
  repeat split; try assumption. unfold bnd in Bd. change (IZR 1) with 1 in Bd. rewrite Rmult_1_l in Bd. exact Bd.
Qed.

Lemma add_abs a b e : finite a -> finite b -> Rabs (B a + B b) <= bpow radix2 e -> (-1000 <= e)%Z -> (e <= 0)%Z ->
  finite (fadd a b) /\ B (fadd a b) = rndF (B a + B b) /\ Rabs (B (fadd a b)) <= bpow radix2 e.
Proof.
  intros Fa Fb Hs He Hf.
  assert (Hbnd : bnd 1 e (B a + B b)) by (unfold bnd; change (IZR 1) with 1; rewrite Rmult_1_l; exact Hs).
  destruct (fadd_bnd 1 e a b Fa Fb ltac:(lia) ltac:(lia) ltac:(apply Z.pow_gt_1; lia) ltac:(lia) Hbnd) as [F [E Bd]].
  repeat split; try assumption. unfold bnd in Bd. change (IZR 1) with 1 in Bd. rewrite Rmult_1_l in Bd. exact Bd.
Qed.

(** The polynomial's words. *)
Lemma c0_val : finite (aw (nth (Z.to_nat 0%Z) asinh_poly0 0%Z)) /\ B (aw (nth (Z.to_nat 0%Z) asinh_poly0 0%Z)) = c0r.
Proof.
  change (nth (Z.to_nat 0%Z) asinh_poly0 0%Z) with 0xbfc5555555555555%Z.
  destruct (word_ok_intro (0xbfc5555555555555)%Z true 6004799503160661%positive 55%nat (-6004799503160661)%Z 0%Z (-55)%Z
    eq_refl eq_refl ltac:(lia) eq_refl) as [F V]. split; [exact F | ].
  rewrite V. unfold c0r. change (IZR (-6004799503160661)) with (- IZR 6004799503160661). ring.
Qed.

Lemma c1_val : finite (aw (nth (Z.to_nat 1%Z) asinh_poly0 0%Z)) /\ B (aw (nth (Z.to_nat 1%Z) asinh_poly0 0%Z)) = c1r.
Proof.
  change (nth (Z.to_nat 1%Z) asinh_poly0 0%Z) with 0x3fb333333331dd9c%Z.
  destruct (word_ok_intro (0x3fb333333331dd9c)%Z false 5404319552757148%positive 56%nat (1351079888189287)%Z 2%Z (-54)%Z
    eq_refl eq_refl ltac:(lia) eq_refl) as [F V]. split; [exact F | ]. rewrite V. reflexivity.
Qed.

Lemma c2_val : finite (aw (nth (Z.to_nat 2%Z) asinh_poly0 0%Z)) /\ B (aw (nth (Z.to_nat 2%Z) asinh_poly0 0%Z)) = c2r.
Proof.
  change (nth (Z.to_nat 2%Z) asinh_poly0 0%Z) with 0xbfa6db6c60bd59aa%Z.
  destruct (word_ok_intro (0xbfa6db6c60bd59aa)%Z true 6433708013607338%positive 57%nat (-3216854006803669)%Z 1%Z (-56)%Z
    eq_refl eq_refl ltac:(lia) eq_refl) as [F V]. split; [exact F | ].
  rewrite V. unfold c2r. change (IZR (-3216854006803669)) with (- IZR 3216854006803669). ring.
Qed.

Lemma c3_val : finite (aw (nth (Z.to_nat 3%Z) asinh_poly0 0%Z)) /\ B (aw (nth (Z.to_nat 3%Z) asinh_poly0 0%Z)) = c3r.
Proof.
  change (nth (Z.to_nat 3%Z) asinh_poly0 0%Z) with 0x3f9eba3d3684b4e5%Z.
  destruct (word_ok_intro (0x3f9eba3d3684b4e5)%Z false 8649021371757797%positive 58%nat (8649021371757797)%Z 0%Z (-58)%Z
    eq_refl eq_refl ltac:(lia) eq_refl) as [F V]. split; [exact F | ]. rewrite V. reflexivity.
Qed.

Lemma qc_facts : 0.1666 <= q0c <= 0.1667 /\ 0.0749 <= q1c <= 0.0751 /\ 0.0446 <= q2c <= 0.0448 /\ 0.03 <= q3c <= 0.0309.
Proof.
  unfold q0c, q1c, q2c, q3c.
  change (-55)%Z with (- Z.of_nat 55)%Z. change (-54)%Z with (- Z.of_nat 54)%Z.
  change (-56)%Z with (- Z.of_nat 56)%Z. change (-58)%Z with (- Z.of_nat 58)%Z.
  rewrite !bpow_negn. simpl.
  repeat split; unfold Rdiv; lra.
Qed.

Lemma q_facts : q0c = - c0r /\ q1c = c1r /\ q2c = - c2r /\ q3c = c3r.
Proof. unfold q0c, q1c, q2c, q3c, c0r, c1r, c2r, c3r. repeat split; ring. Qed.

Lemma cr_facts : Rabs c0r <= 0.1667 /\ Rabs c1r <= 0.0751 /\ Rabs c2r <= 0.0448 /\ Rabs c3r <= 0.0309.
Proof.
  destruct qc_facts as [[A0 A1] [[B0 B1] [[C0 C1] [D0 D1]]]]. destruct q_facts as [E0 [E1 [E2 E3]]].
  assert (c0r = - q0c) by lra. assert (c2r = - q2c) by lra.
  rewrite H, H0, <- E1, <- E3. rewrite !Rabs_Ropp.
  rewrite !Rabs_pos_eq by lra. repeat split; assumption.
Qed.

Lemma rndF_opp x : rndF (- x) = - rndF x.
Proof. exact (round_NE_opp_ne x). Qed.

Lemma inv51 : / 2 ^ 51 <= / 1000.
Proof. assert (H : 2 ^ 51 = 2251799813685248) by (simpl; ring). rewrite H. apply Rinv_le_contravar; lra. Qed.

Lemma sum_abs a b ca cb c : Rabs a <= ca -> Rabs b <= cb -> ca + cb <= c -> Rabs (a + b) <= c.
Proof. intros Ha Hb Hc. apply Rle_trans with (Rabs a + Rabs b); [apply Rabs_triang | lra]. Qed.

Lemma rabs_le_bpow v c e : Rabs v <= c -> c <= bpow radix2 e -> Rabs v <= bpow radix2 e.
Proof. intros; lra. Qed.

(** The series branch's evaluation: the double-word result is the argument plus
    the exact (negative) cubic term, with the tail's relative error and
    [add_f64]'s. *)
Theorem asinh_series_eval x : finite x -> bpow radix2 (-26) <= B x -> B x <= bpow radix2 (-7) ->
  exists h l, asinh_series x = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    exists ec ea, Rabs ec <= / 2 ^ 51 /\ Rabs ea <= / 2 ^ 104 /\
      let Tx := B x * B x * B x * (c0r + B x * B x * (c1r + B x * B x * (c2r + B x * B x * c3r))) in
      B h + B l = (B x + Tx * (1 + ec)) * (1 + ea).
Proof.
  intros Fx L U.
  unfold asinh_series. cbv zeta.
  destruct c0_val as [F0 E0]. destruct c1_val as [F1 E1]. destruct c2_val as [F2 E2]. destruct c3_val as [F3 E3].
  destruct cr_facts as [H0 [H1 [H2 H3]]].
  set (Q0 := aw (nth (Z.to_nat 0%Z) asinh_poly0 0%Z)) in *.
  set (Q1 := aw (nth (Z.to_nat 1%Z) asinh_poly0 0%Z)) in *.
  set (Q2 := aw (nth (Z.to_nat 2%Z) asinh_poly0 0%Z)) in *.
  set (Q3 := aw (nth (Z.to_nat 3%Z) asinh_poly0 0%Z)) in *.
  assert (HXa : Rabs (B x) <= bpow radix2 (-7)).
  { rewrite Rabs_pos_eq; [exact U | pose proof (bpow_gt_0 radix2 (-26)); lra]. }
  assert (A3 : Rabs (B Q3) <= bpow radix2 (-5)) by (rewrite E3; bpow_num; lra).
  assert (A2 : Rabs (B Q2) <= bpow radix2 (-4)) by (rewrite E2; bpow_num; lra).
  assert (A1 : Rabs (B Q1) <= bpow radix2 (-3)) by (rewrite E1; bpow_num; lra).
  assert (A0 : Rabs (B Q0) <= bpow radix2 (-2)) by (rewrite E0; bpow_num; lra).
  destruct (mul_abs x x (-7) (-7) Fx Fx HXa HXa ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [Fz2 [Ez2 Bz2]].
  change (-7 + -7)%Z with (-14)%Z in Bz2. set (z2 := fmul x x) in *.
  destruct (mul_abs z2 Q3 (-14) (-5) Fz2 F3 Bz2 A3 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [Fm3 [Em3 Bm3]].
  change (-14 + -5)%Z with (-19)%Z in Bm3. set (m3 := fmul z2 Q3) in *.
  destruct (add_abs Q2 m3 (-4) F2 Fm3 (sum_abs (B Q2) (B m3) 0.0448 (bpow radix2 (-19)) (bpow radix2 (-4)) ltac:(rewrite E2; exact H2) Bm3 ltac:(bpow_num; lra)) ltac:(lia) ltac:(lia)) as [Fp3 [Ep3 Bp3]].
  set (p3 := fadd Q2 m3) in *.
  destruct (mul_abs z2 p3 (-14) (-4) Fz2 Fp3 Bz2 Bp3 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [Fm2 [Em2 Bm2]].
  change (-14 + -4)%Z with (-18)%Z in Bm2. set (m2 := fmul z2 p3) in *.
  destruct (add_abs Q1 m2 (-3) F1 Fm2 (sum_abs (B Q1) (B m2) 0.0751 (bpow radix2 (-18)) (bpow radix2 (-3)) ltac:(rewrite E1; exact H1) Bm2 ltac:(bpow_num; lra)) ltac:(lia) ltac:(lia)) as [Fp2 [Ep2 Bp2]].
  set (p2 := fadd Q1 m2) in *.
  destruct (mul_abs z2 p2 (-14) (-3) Fz2 Fp2 Bz2 Bp2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [Fm1 [Em1 Bm1]].
  change (-14 + -3)%Z with (-17)%Z in Bm1. set (m1 := fmul z2 p2) in *.
  destruct (add_abs Q0 m1 (-2) F0 Fm1 (sum_abs (B Q0) (B m1) 0.1667 (bpow radix2 (-17)) (bpow radix2 (-2)) ltac:(rewrite E0; exact H0) Bm1 ltac:(bpow_num; lra)) ltac:(lia) ltac:(lia)) as [Fps [Eps Bps]].
  set (ps := fadd Q0 m1) in *.
  destruct (mul_abs x z2 (-7) (-14) Fx Fz2 HXa Bz2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [Fa3 [Ea3 Ba3]].
  change (-7 + -14)%Z with (-21)%Z in Ba3. set (a3 := fmul x z2) in *.
  destruct (mul_abs a3 ps (-21) (-2) Fa3 Fps Ba3 Bps ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [Ftail [Etail Btail]].
  change (-21 + -2)%Z with (-23)%Z in Btail. set (tail := fmul a3 ps) in *.
  (* the certificate's chain, in the kernel's negated form *)
  destruct qc_facts as [[PQ0 PQ0'] [[PQ1 PQ1'] [[PQ2 PQ2'] [PQ3 PQ3']]]]. destruct q_facts as [G0 [G1 [G2 G3]]].
  assert (HX : rn (B x) = B x) by (apply rn_id; apply B_fmt).
  assert (Xp : 0 < B x) by (pose proof (bpow_gt_0 radix2 (-26)); lra).
  assert (X1 : bpow radix2 (-26) <= B x <= 0.0078126).
  { split; [exact L | ]. assert (bpow radix2 (-7) = / 128) by (bpow_num; reflexivity). rewrite H in U. lra. }
  pose proof (series_tail_certificate (B x) X1) as C. cbv zeta in C. rewrite HX in C.
  set (X := B x) in *.
  set (uh := rn (X * X)) in *.
  assert (Euh : B z2 = uh) by (rewrite Ez2; reflexivity).
  set (m3c := rn (uh * q3c)) in *.
  assert (Em3' : B m3 = m3c) by (rewrite Em3, Euh, E3, <- G3; reflexivity).
  set (p3c := rn (q2c - m3c)) in *.
  assert (Ep3' : B p3 = - p3c).
  { rewrite Ep3, E2, Em3'. replace (c2r + m3c) with (- (q2c - m3c)) by (rewrite G2; ring).
    change (rndF (- (q2c - m3c))) with (rn (- (q2c - m3c))). unfold p3c. 
    change (rn (- (q2c - m3c))) with (rndF (- (q2c - m3c))). rewrite rndF_opp. reflexivity. }
  set (m2c := rn (uh * p3c)) in *.
  assert (Em2' : B m2 = - m2c).
  { rewrite Em2, Euh, Ep3'. replace (uh * - p3c) with (- (uh * p3c)) by ring. rewrite rndF_opp. reflexivity. }
  set (p2c := rn (q1c - m2c)) in *.
  assert (Ep2' : B p2 = p2c).
  { rewrite Ep2, E1, Em2'. replace (c1r + - m2c) with (q1c - m2c) by (rewrite G1; ring). reflexivity. }
  set (m1c := rn (uh * p2c)) in *.
  assert (Em1' : B m1 = m1c) by (rewrite Em1, Euh, Ep2'; reflexivity).
  set (psc := rn (q0c - m1c)) in *.
  assert (Eps' : B ps = - psc).
  { rewrite Eps, E0, Em1'. replace (c0r + m1c) with (- (q0c - m1c)) by (rewrite G0; ring).
    rewrite rndF_opp. reflexivity. }
  set (a3c := rn (X * uh)) in *.
  assert (Ea3' : B a3 = a3c) by (rewrite Ea3, Euh; reflexivity).
  set (tailc := rn (a3c * psc)) in *.
  assert (Etail' : B tail = - tailc).
  { rewrite Etail, Ea3', Eps'. replace (a3c * - psc) with (- (a3c * psc)) by ring. rewrite rndF_opp. reflexivity. }
  (* the exact cubic term *)
  set (Pc := q0c - X * X * (q1c - X * X * (q2c - X * X * q3c))) in *.
  assert (XX : 0 < X * X <= / 16384).
  { assert (bpow radix2 (-7) = / 128) by (bpow_num; reflexivity). rewrite H in U. split; nra. }
  assert (Pcb : 0.16 <= Pc <= 0.1667).
  { unfold Pc. set (S := X * X) in *.
    assert (Hm : forall a b A Bb, 0 <= a <= A -> 0 <= b <= Bb -> 0 <= a * b <= A * Bb)
      by (intros a b A Bb [a0 a1] [b0 b1]; split; [apply Rmult_le_pos; assumption | apply Rmult_le_compat; assumption]).
    destruct (Hm S q3c (/ 16384) 0.0309 ltac:(split; lra) ltac:(split; lra)) as [T0 T1].
    assert (T2 : 0 <= q2c - S * q3c <= 0.0448) by (split; lra).
    destruct (Hm S (q2c - S * q3c) (/ 16384) 0.0448 ltac:(split; lra) T2) as [U0 U1].
    assert (T3 : 0 <= q1c - S * (q2c - S * q3c) <= 0.0751) by (split; lra).
    destruct (Hm S (q1c - S * (q2c - S * q3c)) (/ 16384) 0.0751 ltac:(split; lra) T3) as [V0 V1].
    split; lra. }
  set (Txc := X * X * X * Pc) in *.
  assert (Txp : 0 < Txc).
  { unfold Txc. assert (0 < X * X * X) by (apply Rmult_lt_0_compat; [apply Rmult_lt_0_compat | ]; lra).
    apply Rmult_lt_0_compat; lra. }
  assert (Txle : Txc <= X * (1.1e-5)).
  { unfold Txc. assert (X * X * X * Pc <= X * (X * X) * 0.1667) by (assert (0 <= X * X * X) by nra; nra).
    assert (X * (X * X) <= X * / 16384) by nra. nra. }
  assert (Tk : B x * B x * B x * (c0r + B x * B x * (c1r + B x * B x * (c2r + B x * B x * c3r))) = - Txc).
  { unfold Txc, Pc. fold X. rewrite G0, G1, G2, G3. ring. }
  fold X in Tk.
  set (ec := (tailc - Txc) / Txc) in *.
  assert (Ehc : tailc = Txc * (1 + ec)) by (unfold ec; field; lra).
  assert (Hec : Rabs ec <= / 2 ^ 51) by exact C.
  assert (Htr : Rabs (B tail) <= X * 1.2e-5).
  { pose proof inv51 as I51. apply Rabs_le_inv in Hec.
    rewrite Etail', Rabs_Ropp, Ehc.
    rewrite Rabs_pos_eq by nra. nra. }
  assert (Htl : Rabs (B tail) <= bpow radix2 (-12)).
  { assert (Hb12 : bpow radix2 (-12) = / 4096) by (bpow_num; reflexivity).
    assert (bpow radix2 (-7) = / 128) by (bpow_num; reflexivity). rewrite Hb12. rewrite H in U. nra. }
  (* the final sum *)
  assert (Fz : finite asin_zero) by (destruct zero_val as [_ F]; exact F).
  assert (Bz : B asin_zero = 0) by (destruct zero_val as [Z _]; exact Z).
  assert (Hdw : B x = rndF (B x + B asin_zero)).
  { rewrite Bz, Rplus_0_r. symmetry. apply round_generic; [exact _ | apply B_fmt]. }
  assert (Hxa : Rabs (B x) <= bpow radix2 1018).
  { apply Rle_trans with (bpow radix2 (-7)); [exact HXa | apply bpow_le; lia]. }
  assert (Hza : Rabs (B asin_zero) <= bpow radix2 1018) by (rewrite Bz, Rabs_R0; apply bpow_ge_0).
  assert (Hta : Rabs (B tail) <= bpow radix2 1018).
  { apply Rle_trans with (bpow radix2 (-12)); [exact Htl | apply bpow_le; lia]. }
  pose proof (add_f64_ieee x asin_zero tail Fx Fz Ftail Hdw Hxa Hza Hta) as AF.
  pose proof (add_f64_normalized_ieee x asin_zero tail Fx Fz Ftail Hdw Hxa Hza Hta) as AFN.
  destruct (add_f64_64 x asin_zero tail) as [h l] eqn:Ead. cbv iota in AF, AFN. destruct AF as [Fh' [Fl' Bd]].
  destruct AFN as [_ [_ Nrm]].
  exists h, l. split; [reflexivity | ]. split; [exact Fh' | ]. split; [exact Fl' | ]. split; [exact Nrm | ].
  set (Xs := X + B asin_zero + B tail) in *.
  assert (Hxs : 0 < Xs).
  { unfold Xs. rewrite Bz. apply Rabs_le_inv in Htr. lra. }
  exists ec, ((B h + B l - Xs) / Xs). split; [exact Hec | split].
  - apply Rle_trans with (1 := Bd). replace (- prec)%Z with (-53)%Z by (unfold prec; reflexivity). rewrite bp53.
    assert (p104 : 2 ^ 104 = 20282409603651670423947251286016) by (simpl; ring). rewrite p104.
    assert (Hs : (/ 9007199254740992) ^ 2 = / 81129638414606681695789005144064) by (simpl; field). rewrite Hs. lra.
  - cbv zeta. rewrite Tk.
    assert (Xs0 : Xs <> 0) by lra.
    assert (Hb : B tail = - Txc * (1 + ec)) by (rewrite Etail', Ehc; ring).
    assert (Hxs' : Xs = X + - Txc * (1 + ec)) by (unfold Xs; rewrite Bz, Hb; ring).
    replace (X + - Txc * (1 + ec)) with Xs by (symmetry; exact Hxs').
    field. exact Xs0.
Qed.

(** The series branch's fast value against [arcsinh]: relative error below [2^-66]. *)
Theorem asinh_series_fast x : finite x -> bpow radix2 (-26) <= B x -> B x <= bpow radix2 (-7) ->
  exists h l, asinh_series x = (h, l) /\ finite h /\ finite l /\ B h = rndF (B h + B l) /\
    Rabs (B h + B l - arcsinh (B x)) <= bpow radix2 (-66) * arcsinh (B x).
Proof.
  intros Fx L U.
  destruct (asinh_series_eval x Fx L U) as [h [l [Hs [Fh [Fl [Dw [ec [ea [Hec [Hea Hv]]]]]]]]]].
  exists h, l. split; [exact Hs | ]. split; [exact Fh | ]. split; [exact Fl | ]. split; [exact Dw | ].
  cbv zeta in Hv.
  set (X := B x) in *.
  assert (Xp : 0 < X) by (pose proof (bpow_gt_0 radix2 (-26)); lra).
  assert (U' : X <= / 128) by (assert (bpow radix2 (-7) = / 128) by (bpow_num; reflexivity); lra).
  assert (X3 : X * X * X <= X / 16384) by nra.
  assert (X3p : 0 < X * X * X) by (repeat apply Rmult_lt_0_compat; lra).
  set (Pk := c0r + X * X * (c1r + X * X * (c2r + X * X * c3r))).
  assert (HPk : Rabs Pk <= 0.1667).
  { destruct qc_facts as [[A0 A1] [[B0 B1] [[C0 C1] [D0 D1]]]]. destruct q_facts as [G0 [G1 [G2 G3]]].
    unfold Pk. assert (Pk' : c0r + X * X * (c1r + X * X * (c2r + X * X * c3r)) = - (q0c - X * X * (q1c - X * X * (q2c - X * X * q3c)))) by (rewrite G0, G1, G2, G3; ring).
    rewrite Pk'. rewrite Rabs_Ropp.
    assert (Hm : forall a b A Bb, 0 <= a <= A -> 0 <= b <= Bb -> 0 <= a * b <= A * Bb)
      by (intros a b A Bb [a0 a1] [b0 b1]; split; [apply Rmult_le_pos; assumption | apply Rmult_le_compat; assumption]).
    assert (XX : 0 <= X * X <= / 16384) by (split; nra).
    destruct (Hm (X * X) q3c (/ 16384) 0.0309 XX ltac:(split; lra)) as [T0 T1].
    assert (T2 : 0 <= q2c - X * X * q3c <= 0.0448) by (split; lra).
    destruct (Hm (X * X) (q2c - X * X * q3c) (/ 16384) 0.0448 XX T2) as [U0 U1].
    assert (T3 : 0 <= q1c - X * X * (q2c - X * X * q3c) <= 0.0751) by (split; lra).
    destruct (Hm (X * X) (q1c - X * X * (q2c - X * X * q3c)) (/ 16384) 0.0751 XX T3) as [V0 V1].
    rewrite Rabs_pos_eq by lra. lra. }
  assert (HTk : Rabs (X * X * X * Pk) <= X * X * X * 0.1667).
  { rewrite Rabs_mult, (Rabs_pos_eq (X * X * X)) by lra. apply Rmult_le_compat_l; [lra | exact HPk]. }
  set (Tk := X * X * X * Pk) in *.
  assert (L28 : / 268435456 <= X).
  { assert (bpow radix2 (-26) = / 67108864) by (bpow_num; reflexivity). rewrite H in L. lra. }
  assert (U28 : X <= 0.0078126) by lra.
  pose proof (approx_series X (conj L28 U28)) as Hap.
  fold Pk in Hap.
  replace (X + X * X * X * Pk) with (X + Tk) in Hap by (unfold Tk; ring).
  pose proof (arcsinh_le_id X ltac:(lra)) as A1.
  pose proof (arcsinh_ge_cubic X ltac:(split; lra)) as A0.
  set (A := arcsinh X) in *.
  pose proof (Rabs_pos ea) as Pea. pose proof (Rabs_pos ec) as Pec.
  assert (Hq51 : / 2 ^ 51 = / 2251799813685248) by (assert (2 ^ 51 = 2251799813685248) by (simpl; ring); rewrite H; reflexivity).
  assert (Hq104 : / 2 ^ 104 = / 20282409603651670423947251286016) by (assert (2 ^ 104 = 20282409603651670423947251286016) by (simpl; ring); rewrite H; reflexivity).
  rewrite Hq51 in Hec. rewrite Hq104 in Hea.
  set (Q := X + Tk * (1 + ec)) in *.
  assert (HQ : Rabs Q <= 2 * X).
  { unfold Q. apply Rle_trans with (Rabs X + Rabs (Tk * (1 + ec))); [apply Rabs_triang | ].
    rewrite Rabs_pos_eq by lra. rewrite Rabs_mult.
    assert (Rabs (1 + ec) <= 2) by (apply Rabs_le; apply Rabs_le_inv in Hec; split; lra).
    assert (Rabs Tk <= X * X * X * 0.1667) by exact HTk.
    assert (Rabs Tk * Rabs (1 + ec) <= (X * X * X * 0.1667) * 2) by (apply Rmult_le_compat; try apply Rabs_pos; assumption).
    nra. }
  assert (Hid : B h + B l - A = (X + Tk - A) + Tk * ec + Q * ea) by (rewrite Hv; unfold Q, Tk, Pk; ring).
  assert (Hp1 : Rabs (X + Tk - A) <= 3 / 16 / 18014398509481984 * (X * X * X)).
  { replace (X + Tk - A) with (- (A - (X + Tk))) by ring. rewrite Rabs_Ropp. exact Hap. }
  assert (Hp2 : Rabs (Tk * ec) <= X * X * X * 0.1667 * / 2251799813685248).
  { rewrite Rabs_mult. apply Rmult_le_compat; try apply Rabs_pos; assumption. }
  assert (Hp3 : Rabs (Q * ea) <= 2 * X * / 20282409603651670423947251286016).
  { rewrite Rabs_mult. apply Rmult_le_compat; try apply Rabs_pos; assumption. }
  assert (Hb66 : bpow radix2 (-66) = / 73786976294838206464) by (bpow_num; reflexivity).
  rewrite Hid, Hb66.
  apply Rle_trans with (Rabs (X + Tk - A) + Rabs (Tk * ec) + Rabs (Q * ea)).
  { apply Rle_trans with (Rabs (X + Tk - A + Tk * ec) + Rabs (Q * ea)); [apply Rabs_triang | ].
    pose proof (Rabs_triang (X + Tk - A) (Tk * ec)). lra. }
  apply Rabs_le_inv in HTk. 
  assert (Hxx : 3 / 16 / 18014398509481984 * (X * X * X) <= 3 / 16 / 18014398509481984 * (X / 16384)) by (apply Rmult_le_compat_l; [lra | exact X3]).
  assert (Hyy : X * X * X * 0.1667 * / 2251799813685248 <= X / 16384 * 0.1667 * / 2251799813685248).
  { apply Rmult_le_compat_r; [lra | ]. apply Rmult_le_compat_r; [lra | exact X3]. }
  assert (HA : 0.99998 * X <= A) by nra.
  assert (Hfin : 3 / 16 / 18014398509481984 * (X / 16384) + X / 16384 * 0.1667 * / 2251799813685248 + 2 * X * / 20282409603651670423947251286016 <= / 73786976294838206464 * (0.99998 * X)) by lra.
  assert (Hmon : / 73786976294838206464 * (0.99998 * X) <= / 73786976294838206464 * A) by (apply Rmult_le_compat_l; [lra | exact HA]).
  lra.
Qed.
