(** The accurate path against [atan (n/d)]: one Newton step in [Q256] from the fast path's
    start lands within [5e-58] of the angle, relatively, and the form's constant keeps
    the result within [2^-190] of the form's value. *)
From Coq Require Import Reals ZArith Lia Lra Psatz List.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64.
From Interval Require Import Tactic.
From Q Require Import Q256 Q256Real QSpec.
Require Import Ln1pLemmas AsinTables AsinKernel AsinWithin AsinFacts AsinSeries AsinQSeries AsinSinCos AsinRecip AsinNewton
  AsinAccurate ErfcxAccurateInputs Atan2Kernel Atan2Within Atan2Approx Atan2Recip Atan2Forms Atan2FastPath Atan2Newton Atan2NewtonReal.
Open Scope R_scope.

Definition newton_phi1 (n d : f64) (phi : f64 * f64) : q256 :=
  let phi0 := Q256.add (qf (fst phi)) (qf (snd phi)) in
  let '(sin, cos) := q_sin_cos phi0 in
  let nq := qf n in
  let dq := qf d in
  let numerator := Q256.add (Q256.mul nq cos) (Q256.neg_q (Q256.mul dq sin)) in
  let denominator := Q256.add (Q256.mul dq cos) (Q256.mul nq sin) in
  Q256.add phi0 (Q256.mul numerator (atan2_recip denominator)).

Lemma accurate_value_split n d f phi : atan2_accurate_value n d f phi =
  match f with
  | Phi => newton_phi1 n d phi
  | HalfPiMinus => Q256.add q_half_pi (Q256.neg_q (newton_phi1 n d phi))
  | HalfPiPlus => Q256.add q_half_pi (newton_phi1 n d phi)
  | PiMinus => Q256.add (Q256Real.mul_pow2 q_half_pi 1) (Q256.neg_q (newton_phi1 n d phi))
  end.
Proof. destruct f; reflexivity. Qed.

Lemma pi4_le : PI / 4 <= 0.785399.
Proof. interval with (i_prec 60). Qed.

Lemma cos_pt : 0.7071 <= cos 0.7854.
Proof. interval with (i_prec 100). Qed.

Lemma cos_lo r : 0 <= r <= 0.7854 -> 0.7071 <= cos r.
Proof.
  intros [R0 R1]. pose proof pi_gt_3 as P3.
  apply Rle_trans with (cos 0.7854).
  - exact cos_pt.
  - destruct (Rle_lt_or_eq_dec r 0.7854 R1) as [Hl | He].
    + apply Rlt_le. apply cos_decreasing_1; lra.
    + rewrite He. lra.
Qed.

Lemma bp196_tau : bpow radix2 (-196) <= tauA.
Proof. unfold tauA. bpow_num. interval with (i_prec 100). Qed.

Lemma bp255_tau : bpow radix2 (-255) <= tauA.
Proof. unfold tauA. bpow_num. interval with (i_prec 100). Qed.

Lemma bp252_tau : bpow radix2 (-252) <= tauA.
Proof. unfold tauA. bpow_num. interval with (i_prec 100). Qed.

Lemma bp254_tau : bpow radix2 (-254) * 1.1 <= tauA.
Proof. unfold tauA. bpow_num. interval with (i_prec 100). Qed.

Lemma eta_start : bpow radix2 (-63) * (1 + bpow radix2 (-39)) + 2 * bpow radix2 (-254) <= etaA.
Proof. unfold etaA. bpow_num. interval with (i_prec 100). Qed.

Theorem newton_phi1_ok n d ph pl :
  finite n -> finite d -> finite ph -> finite pl ->
  0 < B n -> B n <= B d -> bpow radix2 (-901) <= B n / B d ->
  0 < B ph -> Rabs (B pl) <= bpow radix2 (-52) * B ph ->
  Rabs (B ph + B pl - atan (B n / B d)) <= bpow radix2 (-63) * (1 + bpow radix2 (-39)) * atan (B n / B d) ->
  Q256Real.valid (newton_phi1 n d (ph, pl)) /\
  Rabs (qval (newton_phi1 n d (ph, pl)) - atan (B n / B d)) <= bndN * atan (B n / B d).
Proof.
  intros Fn Fd Fph Fpl Hn0 Hnd Hq Hph0 Hpl Hst.
  assert (Hd0 : 0 < B d) by lra.
  set (t := B n / B d) in *.
  assert (Ht0 : 0 < t) by (pose proof (bpow_gt_0 radix2 (-901)); lra).
  assert (Ht1 : t <= 1).
  { unfold t. apply Rmult_le_reg_r with (B d); [exact Hd0 | ]. unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra. lra. }
  assert (Hnt : B n = t * B d) by (unfold t; field; lra).
  set (Y := atan t) in *.
  pose proof (atan_pos t Ht0) as Y0.
  assert (HYt : Y <= t) by (unfold Y; apply atan_le_id; lra).
  assert (HYh : t / 2 <= Y) by (unfold Y; apply atan_half; lra).
  assert (HY4 : Y <= PI / 4) by (rewrite <- atan_1; unfold Y; apply atan_le; exact Ht1).
  pose proof pi4_le as P4.
  assert (HY7 : Y <= 0.785399) by lra.
  destruct bpow_254 as [B252 [B255 [Upos Usmall]]]. set (U := bpow radix2 (-254)) in *.
  assert (HU1 : U * 1.1 <= tauA) by exact bp254_tau.
  (* the start *)
  destruct (q_float_ok ph Fph) as [Vph Qph]. destruct (q_float_ok pl Fpl) as [Vpl Qpl].
  pose proof (add_any (q_float ph) (q_float pl) Vph Vpl) as [V0 E0].
  rewrite Qph, Qpl in E0.
  assert (Hmax0 : Rmax (Rabs (B ph)) (Rabs (B pl)) = B ph).
  { rewrite (Rabs_pos_eq (B ph)) by lra. apply Rmax_left.
    apply Rle_trans with (1 := Hpl). assert (bpow radix2 (-52) <= 1) by (bpow_num; interval with (i_prec 60)). nra. }
  rewrite Hmax0 in E0. change (bpow radix2 (-254)) with U in E0.
  change (qf ph) with (q_float ph). change (qf pl) with (q_float pl).
  set (phi0 := Q256.add (q_float ph) (q_float pl)) in *.
  set (r := qval phi0) in *.
  assert (Hphi : ph = ph) by reflexivity.
  assert (Hb52 : bpow radix2 (-52) <= / 4503599627370496) by (bpow_num; interval with (i_prec 100)).
  assert (HpY : B ph <= 1.01 * Y).
  { apply Rabs_le_inv in Hst as [S1 S2]. apply Rabs_le_inv in Hpl as [L1 L2].
    assert (Hc1 : bpow radix2 (-63) * (1 + bpow radix2 (-39)) <= / 1000000) by (bpow_num; interval with (i_prec 100)).
    pose proof (bpow_gt_0 radix2 (-63)). pose proof (bpow_gt_0 radix2 (-39)).
    nra. }
  assert (Hrr : Rabs (r - Y) <= etaA * Y).
  { apply Rabs_le_inv in E0 as [A1 A2]. apply Rabs_le_inv in Hst as [S1 S2].
    pose proof eta_start as Hes. pose proof (bpow_gt_0 radix2 (-254)).
    assert (Hu : U * B ph <= 2 * U * Y) by nra.
    assert (Hes' : (bpow radix2 (-63) * (1 + bpow radix2 (-39)) + 2 * U) * Y <= etaA * Y) by (apply Rmult_le_compat_r; [lra | exact Hes]).
    apply Rabs_le. split; lra. }
  assert (Heta : 0 < etaA <= / 1000000000) by (unfold etaA; split; [lra | ]; bpow_num; interval with (i_prec 100)).
  apply Rabs_le_inv in Hrr as [Hr1 Hr2].
  assert (Hrpos : 0 < r) by nra.
  assert (Hr7 : r <= 0.7854) by nra.
  assert (Hr1' : r <= 1.0001 * Y) by nra.
  assert (HY7' : Y <= 0.7854) by lra.
  (* sin and cos of the start *)
  pose proof (q_sin_cos_error phi0 V0 (conj (Rlt_le _ _ Hrpos) Hr7)) as [Vsn [Vcs [Esn Ecs]]].
  unfold newton_phi1. cbn [fst snd]. change (qf ph) with (q_float ph). change (qf pl) with (q_float pl).
  change (Q256.add (q_float ph) (q_float pl)) with phi0.
  destruct (q_sin_cos phi0) as [sn cs] eqn:Esc. cbn [fst snd] in Vsn, Vcs, Esn, Ecs.
  cbv iota.
  pose proof pi_gt_3 as P3.
  assert (Hspos : 0 < sin r) by (apply sin_gt_0; lra).
  assert (Hcl : 0.7071 <= cos r) by (apply cos_lo; split; lra).
  pose proof (COS_bound r) as [_ Hc1].
  assert (Hcpos : 0 < cos r) by lra.
  destruct (rel_split _ _ _ Hspos Esn) as [sg [Hsg Hsg']].
  destruct (rel_split _ _ _ Hcpos Ecs) as [gm [Hgm Hgm']].
  assert (Hsg2 : Rabs sg <= tauA) by (apply Rle_trans with (1 := Hsg'); exact bp196_tau).
  assert (Hgm2 : Rabs gm <= tauA) by (apply Rle_trans with (1 := Hgm'); exact bp196_tau).
  destruct tauA_facts as [T0 T1].
  assert (Hs_le : sin r <= 1.0001 * t).
  { pose proof (sin_taylor_pos r ltac:(split; lra)) as [_ S]. nra. }
  assert (Hsnn : 0 <= sin r) by lra.
  (* the exact step *)
  assert (HrY : Rabs (Y - r) <= etaA * Y).
  { rewrite Rabs_minus_sym. apply Rabs_le. split; lra. }
  assert (Hd6 : Rabs (atan t - r) <= / 1000000).
  { apply Rle_trans with (1 := HrY). assert (etaA * Y <= / 1000000000 * 1) by (apply Rmult_le_compat; [lra | lra | lra | lra]). lra. }
  destruct (newton_exact t r Ht0 Hd6) as [w [Hex [Dpos [Hcub Hwb]]]].
  fold Y in Hcub, Hwb.
  (* products *)
  destruct (q_float_ok n Fn) as [Vn Qn]. destruct (q_float_ok d Fd) as [Vd Qd].
  change (qf n) with (q_float n). change (qf d) with (q_float d).
  destruct (mul_relative (q_float n) cs Vn Vcs) as [Vp1 [d1 [Hd1 Ep1]]]. rewrite Qn in Ep1.
  destruct (mul_relative (q_float d) sn Vd Vsn) as [Vp2 [d2 [Hd2 Ep2]]]. rewrite Qd in Ep2.
  destruct (neg_any (Q256.mul (q_float d) sn) Vp2) as [Vnp2 Qnp2].
  destruct (add_any (Q256.mul (q_float n) cs) (Q256.neg_q (Q256.mul (q_float d) sn)) Vp1 Vnp2) as [Vnu Enu].
  rewrite Qnp2 in Enu.
  destruct (mul_relative (q_float d) cs Vd Vcs) as [Vq1 [d3 [Hd3 Eq1]]]. rewrite Qd in Eq1.
  destruct (mul_relative (q_float n) sn Vn Vsn) as [Vq2 [d4 [Hd4 Eq2]]]. rewrite Qn in Eq2.
  destruct (add_any (Q256.mul (q_float d) cs) (Q256.mul (q_float n) sn) Vq1 Vq2) as [Vden Eden].
  rewrite B255 in Hd1, Hd2, Hd3, Hd4.
  assert (HdU : U / 2 <= tauA) by (pose proof bp254_tau; pose proof Upos; lra).
  assert (Hd1' : Rabs d1 <= tauA) by (apply Rle_trans with (1 := Hd1); exact HdU).
  assert (Hd2' : Rabs d2 <= tauA) by (apply Rle_trans with (1 := Hd2); exact HdU).
  assert (Hd3' : Rabs d3 <= tauA) by (apply Rle_trans with (1 := Hd3); exact HdU).
  assert (Hd4' : Rabs d4 <= tauA) by (apply Rle_trans with (1 := Hd4); exact HdU).
  set (p1 := qval (Q256.mul (q_float n) cs)) in *. set (p2 := qval (Q256.mul (q_float d) sn)) in *.
  set (q1 := qval (Q256.mul (q_float d) cs)) in *. set (q2 := qval (Q256.mul (q_float n) sn)) in *.
  set (numq := Q256.add (Q256.mul (q_float n) cs) (Q256.neg_q (Q256.mul (q_float d) sn))) in *.
  set (denq := Q256.add (Q256.mul (q_float d) cs) (Q256.mul (q_float n) sn)) in *.
  set (csv := qval cs) in *. set (snv := qval sn) in *.
  assert (Hcsv : Rabs csv <= 1.0001) by (rewrite Hgm; apply Rabs_le_inv in Hgm2 as [G1 G2]; rewrite Rabs_pos_eq by nra; nra).
  assert (Hsnv : Rabs snv <= 1.0002 * t) by (rewrite Hsg; apply Rabs_le_inv in Hsg2 as [G1 G2]; rewrite Rabs_pos_eq by nra; nra).
  assert (Hnpos : 0 < B n) by lra.
  (* the numerator's rounding *)
  assert (Hmax1 : Rmax (Rabs p1) (Rabs (- p2)) <= 1.1 * B n).
  { apply Rmax_lub.
    - rewrite Ep1. rewrite !Rabs_mult. rewrite (Rabs_pos_eq (B n)) by lra.
      assert (Rabs (1 + d1) <= 1.0001) by (apply Rabs_le_inv in Hd1' as [G1 G2]; apply Rabs_le; split; lra).
      pose proof (Rabs_pos csv). pose proof (Rabs_pos (1 + d1)).
      assert (Rabs csv * Rabs (1 + d1) <= 1.0001 * 1.0001) by (apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | exact Hcsv | assumption]).
      nra.
    - rewrite Rabs_Ropp. rewrite Ep2. rewrite !Rabs_mult. rewrite (Rabs_pos_eq (B d)) by lra.
      assert (Rabs (1 + d2) <= 1.0001) by (apply Rabs_le_inv in Hd2' as [G1 G2]; apply Rabs_le; split; lra).
      pose proof (Rabs_pos snv). pose proof (Rabs_pos (1 + d2)).
      assert (Rabs snv * Rabs (1 + d2) <= (1.0002 * t) * 1.0001) by (apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | exact Hsnv | assumption]).
      rewrite Hnt. nra. }
  set (g1 := qval numq - (p1 + - p2)).
  assert (Hg1 : Rabs g1 <= tauA * B n).
  { apply Rle_trans with (U * Rmax (Rabs p1) (Rabs (- p2))); [exact Enu | ].
    apply Rle_trans with (U * (1.1 * B n)); [apply Rmult_le_compat_l; [lra | exact Hmax1] | ].
    replace (U * (1.1 * B n)) with ((U * 1.1) * B n) by ring. apply Rmult_le_compat_r; [lra | exact HU1]. }
  (* the denominator's rounding *)
  assert (Hmax4 : Rmax (Rabs q1) (Rabs q2) <= 1.1 * B d).
  { apply Rmax_lub.
    - rewrite Eq1. rewrite !Rabs_mult. rewrite (Rabs_pos_eq (B d)) by lra.
      assert (Rabs (1 + d3) <= 1.0001) by (apply Rabs_le_inv in Hd3' as [G1 G2]; apply Rabs_le; split; lra).
      pose proof (Rabs_pos csv). pose proof (Rabs_pos (1 + d3)).
      assert (Rabs csv * Rabs (1 + d3) <= 1.0001 * 1.0001) by (apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | exact Hcsv | assumption]).
      nra.
    - rewrite Eq2. rewrite !Rabs_mult. rewrite (Rabs_pos_eq (B n)) by lra.
      assert (Rabs (1 + d4) <= 1.0001) by (apply Rabs_le_inv in Hd4' as [G1 G2]; apply Rabs_le; split; lra).
      pose proof (Rabs_pos snv). pose proof (Rabs_pos (1 + d4)).
      assert (Rabs snv * Rabs (1 + d4) <= (1.0002 * t) * 1.0001) by (apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | exact Hsnv | assumption]).
      assert (Hx4 : Rabs snv * Rabs (1 + d4) <= 1.001) by nra.
      assert (B n * (Rabs snv * Rabs (1 + d4)) <= B n * 1.001) by (apply Rmult_le_compat_l; lra).
      nra. }
  set (g4 := qval denq - (q1 + q2)).
  assert (Hg4 : Rabs g4 <= tauA * B d).
  { apply Rle_trans with (U * Rmax (Rabs q1) (Rabs q2)); [exact Eden | ].
    apply Rle_trans with (U * (1.1 * B d)); [apply Rmult_le_compat_l; [lra | exact Hmax4] | ].
    replace (U * (1.1 * B d)) with ((U * 1.1) * B d) by ring. apply Rmult_le_compat_r; [lra | exact HU1]. }
  (* the denominator is positive *)
  assert (Hq1 : 0.7 * B d <= q1).
  { rewrite Eq1, Hgm. apply Rabs_le_inv in Hgm2 as [G1 G2]. apply Rabs_le_inv in Hd3' as [H1 H2].
    assert (Hk : 0.9999 <= (1 + gm) * (1 + d3)) by (clear - G1 G2 H1 H2 T0 T1; nra).
    assert (Hc : 0.7 <= cos r * ((1 + gm) * (1 + d3))) by (clear - Hk Hcl; nra).
    replace (B d * (cos r * (1 + gm)) * (1 + d3)) with (B d * (cos r * ((1 + gm) * (1 + d3)))) by ring.
    apply Rmult_le_compat_l with (r := B d) in Hc; [lra | lra]. }
  assert (Hq2 : 0 <= q2).
  { rewrite Eq2, Hsg. apply Rabs_le_inv in Hsg2 as [G1 G2]. apply Rabs_le_inv in Hd4' as [H1 H2].
    assert (Hk : 0 <= (1 + sg) * (1 + d4)) by (clear - G1 G2 H1 H2 T0 T1; nra).
    replace (B n * (sin r * (1 + sg)) * (1 + d4)) with (B n * (sin r * ((1 + sg) * (1 + d4)))) by ring.
    apply Rmult_le_pos; [lra | apply Rmult_le_pos; lra]. }
  assert (Hden : 0.69 * B d <= qval denq).
  { apply Rabs_le_inv in Hg4 as [G1 G2]. unfold g4 in G1.
    assert (Hdd : tauA * B d <= 0.01 * B d) by (apply Rmult_le_compat_r; lra).
    clear - G1 Hdd Hq1 Hq2 Hd0. lra. }
  assert (Hdenp : 0 < qval denq) by (clear - Hden Hd0; lra).
  destruct (atan2_recip_ok denq Vden Hdenp) as [Vri [Pri Eri]].
  assert (Hee : Rabs (qval denq * qval (atan2_recip denq) - 1) <= tauA) by (apply Rle_trans with (1 := Eri); exact bp252_tau).
  destruct (mul_relative numq (atan2_recip denq) Vnu Vri) as [Vpr [d6 [Hd6e Epr]]].
  rewrite B255 in Hd6e.
  assert (Hd6' : Rabs d6 <= tauA) by (apply Rle_trans with (1 := Hd6e); exact HdU).
  set (prq := Q256.mul numq (atan2_recip denq)) in *.
  set (Ph := qval prq) in *.
  (* the quotient against w *)
  assert (Hrw : Rabs (Y - r) <= etaA * Y) by exact HrY.
  assert (Hcl7 : 0.7 <= cos r) by lra.
  assert (HPw : Rabs (Ph - w) <= 7.7 * tauA * t).
  { refine (newton_atan_P (B n) (B d) t Y r (sin r) (cos r) w snv csv sg gm d1 d2 d3 d4 d6 (qval denq * qval (atan2_recip denq) - 1)
      g1 g4 p1 p2 (qval numq) (qval denq) (qval (atan2_recip denq)) Ph Hd0 Ht0 Ht1 Hnt _ HYt HY7' Hrw Hsnn Hs_le Hcl7 Hc1 Hex Dpos Hcub _ Hsg Hsg2 Hgm Hgm2 Ep1 Hd1' Ep2 Hd2' _ Hg1 _ Hd3' Hd4' Hg4 _ Hee _ Hd6'); try (unfold g1, g4; ring).
    - lra.
    - exact Hwb.
    - unfold g4. rewrite <- Eq1, <- Eq2. ring.
    - exact Epr. }
  (* the final sum *)
  destruct (add_any phi0 prq V0 Vpr) as [Vy Ey]. change (bpow radix2 (-254)) with U in Ey.
  set (phi1q := Q256.add phi0 prq) in *.
  set (g5 := qval phi1q - (r + Ph)).
  assert (HPb : Rabs Ph <= 1.1 * Y).
  { assert (Hw1 : Rabs w <= 0.001 * Y).
    { apply Rle_trans with (1.0001 * Rabs (Y - r)); [exact Hwb | ]. apply Rle_trans with (1.0001 * (etaA * Y)); [apply Rmult_le_compat_l; [lra | exact HrY] | ].
      assert (etaA * Y <= / 1000000000 * Y) by (apply Rmult_le_compat_r; lra). lra. }
    assert (H7 : 7.7 * tauA * t <= 0.001 * Y).
    { assert (tauA * t <= tauA * 1) by (apply Rmult_le_compat_l; lra).
      assert (tauA <= / 1000000000000) by (unfold tauA; bpow_num; interval with (i_prec 100)).
      assert (Y >= 0.5 * t) by lra. nra. }
    apply Rabs_le_inv in HPw as [P1 P2]. apply Rabs_le_inv in Hw1 as [W1 W2]. apply Rabs_le. split; lra. }
  assert (Hmax5 : Rmax (Rabs r) (Rabs Ph) <= 1.1 * Y).
  { apply Rmax_lub; [rewrite Rabs_pos_eq by lra; lra | exact HPb]. }
  assert (Hg5 : Rabs g5 <= tauA * Y).
  { apply Rle_trans with (U * Rmax (Rabs r) (Rabs Ph)); [exact Ey | ].
    apply Rle_trans with (U * (1.1 * Y)); [apply Rmult_le_compat_l; [lra | exact Hmax5] | ].
    replace (U * (1.1 * Y)) with ((U * 1.1) * Y) by ring. apply Rmult_le_compat_r; [lra | exact HU1]. }
  refine (conj Vy _).
  assert (HYl : 0.5 * t <= Y) by (clear - HYh; lra).
  assert (Hnu : qval numq = (p1 + - p2) + g1) by (unfold g1; ring).
  assert (Hdh : qval denq = (B d * csv * (1 + d3) + B n * snv * (1 + d4)) + g4) by (unfold g4; rewrite <- Eq1, <- Eq2; ring).
  assert (Hrih : qval denq * qval (atan2_recip denq) = 1 + (qval denq * qval (atan2_recip denq) - 1)) by ring.
  assert (Hphi1 : qval phi1q = (r + Ph) + g5) by (unfold g5; ring).
  exact (newton_atan_final (B n) (B d) t Y r (sin r) (cos r) w snv csv sg gm d1 d2 d3 d4 d6 (qval denq * qval (atan2_recip denq) - 1)
      g1 g4 g5 p1 p2 (qval numq) (qval denq) (qval (atan2_recip denq)) Ph (qval phi1q) Hd0 Ht0 Ht1 Hnt HYl HYt HY7' Hrw Hsnn Hs_le Hcl7 Hc1 Hex Dpos Hcub Hwb Hsg Hsg2 Hgm Hgm2 Ep1 Hd1' Ep2 Hd2' Hnu Hg1 Hdh Hd3' Hd4' Hg4 Hrih Hee Epr Hd6' HPw Hphi1 Hg5).
Qed.

Lemma bnd_room : bndN * 0.7854 + / 1000000000000000000000000000000000000000000000000000000000000000000000 <= bndM * 0.78.
Proof. unfold bndN, bndM. interval with (i_prec 300). Qed.

Lemma bndN_le : bndN <= bndM.
Proof. unfold bndN, bndM. interval with (i_prec 300). Qed.

Theorem atan2_accurate_ok n d f ph pl :
  finite n -> finite d -> finite ph -> finite pl ->
  0 < B n -> B n <= B d -> bpow radix2 (-901) <= B n / B d ->
  0 < B ph -> Rabs (B pl) <= bpow radix2 (-52) * B ph ->
  Rabs (B ph + B pl - atan (B n / B d)) <= bpow radix2 (-63) * (1 + bpow radix2 (-39)) * atan (B n / B d) ->
  Q256Real.valid (atan2_accurate_value n d f (ph, pl)) /\
  Rabs (qval (atan2_accurate_value n d f (ph, pl)) - form_value f (atan (B n / B d))) <= bndM * form_value f (atan (B n / B d)).
Proof.
  intros Fn Fd Fph Fpl Hn0 Hnd Hq Hph0 Hpl Hst.
  destruct (newton_phi1_ok n d ph pl Fn Fd Fph Fpl Hn0 Hnd Hq Hph0 Hpl Hst) as [V1 E1].
  rewrite accurate_value_split.
  set (t := B n / B d) in *. set (Y := atan t) in *.
  assert (Ht0 : 0 < t) by (pose proof (bpow_gt_0 radix2 (-901)); lra).
  assert (Ht1 : t <= 1).
  { unfold t. assert (Hd0 : 0 < B d) by lra. apply Rmult_le_reg_r with (B d); [exact Hd0 | ]. unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra. lra. }
  pose proof (atan_pos t Ht0) as Y0. fold Y in Y0.
  assert (HY4 : Y <= PI / 4) by (rewrite <- atan_1; unfold Y; apply atan_le; exact Ht1).
  pose proof pi4_le as P4. pose proof pi_gt_3 as P3.
  assert (P314 : 3.14 < PI) by (interval with (i_prec 60)).
  set (p1 := newton_phi1 n d (ph, pl)) in *.
  destruct half_pi_q as [Vh Eh].
  destruct bpow_254 as [B252 [B255 [Upos Usmall]]]. set (U := bpow radix2 (-254)) in *.
  assert (HU : U <= / 10000000000000000000000000000000000000000000000000000000000000000000000) by (unfold U; bpow_num; interval with (i_prec 300)).
  set (e70 := / 10000000000000000000000000000000000000000000000000000000000000000000000) in *.
  assert (He70 : 0 < e70) by (unfold e70; apply Rinv_0_lt_compat; lra).
  assert (He70s : e70 <= / 1000000) by (unfold e70; apply Rinv_le_contravar; lra).
  assert (HbNs : bndN <= / 1000000000) by (unfold bndN; interval with (i_prec 100)).
  assert (HbNY : bndN * Y <= / 1000000000 * Y) by exact (Rmult_le_compat_r Y _ _ (Rlt_le _ _ Y0) HbNs).
  assert (Hphi1 : Rabs (qval p1) <= 1) by (apply Rabs_le_inv in E1 as [A1 A2]; apply Rabs_le; split; lra).
  assert (HbN : bndN * Y <= bndN * 0.7854) by (apply Rmult_le_compat_l; [unfold bndN; lra | clear - HY4 P4; lra]).
  assert (Hroom : bndN * 0.7854 + 8 * e70 <= bndM * 0.78) by (unfold bndN, bndM, e70; interval with (i_prec 300)).
  pose proof bnd_room as Hroom0. pose proof bndN_le as HNle.
  assert (Hb190 : 0 < bndM) by (unfold bndM; apply Rmult_lt_0_compat; [lra | apply Rinv_0_lt_compat; lra]).
  destruct f; cbn [form_value].
  - split; [exact V1 | ]. apply Rle_trans with (bndN * Y); [exact E1 | apply Rmult_le_compat_r; lra].
  - destruct (neg_any p1 V1) as [Vn Qn].
    destruct (add_any q_half_pi (Q256.neg_q p1) Vh Vn) as [Va Ea]. rewrite Qn in Ea.
    refine (conj Va _).
    assert (Hm : Rmax (Rabs (qval q_half_pi)) (Rabs (- qval p1)) <= 2).
    { apply Rmax_lub; [apply Rabs_le_inv in Eh as [A1 A2]; apply Rabs_le; split; lra | rewrite Rabs_Ropp; lra]. }
    assert (Hu2 : U * Rmax (Rabs (qval q_half_pi)) (Rabs (- qval p1)) <= U * 2) by (apply Rmult_le_compat_l; lra).
    apply Rabs_le_inv in Ea as [A1 A2]. change (bpow radix2 (-254)) with U in A1, A2. apply Rabs_le_inv in Eh as [H1 H2]. apply Rabs_le_inv in E1 as [F1 F2].
    assert (HZ : 0.78 <= PI / 2 - Y) by lra.
    assert (Hr : bndM * 0.78 <= bndM * (PI / 2 - Y)) by (apply Rmult_le_compat_l; lra).
    apply Rabs_le. split; lra.
  - destruct (Q256Real.mul_pow2_any q_half_pi 1 Vh) as [Vh2 Qh2].
    destruct (neg_any p1 V1) as [Vn Qn].
    destruct (add_any (Q256Real.mul_pow2 q_half_pi 1) (Q256.neg_q p1) Vh2 Vn) as [Va Ea]. rewrite Qn, Qh2 in Ea.
    refine (conj Va _).
    assert (Hb1 : bpow radix2 1 = 2) by reflexivity. rewrite Hb1 in Ea.
    assert (Hm : Rmax (Rabs (qval q_half_pi * 2)) (Rabs (- qval p1)) <= 4).
    { apply Rmax_lub; [apply Rabs_le_inv in Eh as [A1 A2]; apply Rabs_le; split; lra | rewrite Rabs_Ropp; lra]. }
    assert (Hu2 : U * Rmax (Rabs (qval q_half_pi * 2)) (Rabs (- qval p1)) <= U * 4) by (apply Rmult_le_compat_l; lra).
    apply Rabs_le_inv in Ea as [A1 A2]. change (bpow radix2 (-254)) with U in A1, A2. apply Rabs_le_inv in Eh as [H1 H2]. apply Rabs_le_inv in E1 as [F1 F2].
    assert (HZ : 0.78 <= PI - Y) by lra.
    assert (Hr : bndM * 0.78 <= bndM * (PI - Y)) by (apply Rmult_le_compat_l; lra).
    apply Rabs_le. split; lra.
  - destruct (add_any q_half_pi p1 Vh V1) as [Va Ea].
    refine (conj Va _).
    assert (Hm : Rmax (Rabs (qval q_half_pi)) (Rabs (qval p1)) <= 2).
    { apply Rmax_lub; [apply Rabs_le_inv in Eh as [A1 A2]; apply Rabs_le; split; lra | lra]. }
    assert (Hu2 : U * Rmax (Rabs (qval q_half_pi)) (Rabs (qval p1)) <= U * 2) by (apply Rmult_le_compat_l; lra).
    apply Rabs_le_inv in Ea as [A1 A2]. change (bpow radix2 (-254)) with U in A1, A2. apply Rabs_le_inv in Eh as [H1 H2]. apply Rabs_le_inv in E1 as [F1 F2].
    assert (HZ : 0.78 <= PI / 2 + Y) by lra.
    assert (Hr : bndM * 0.78 <= bndM * (PI / 2 + Y)) by (apply Rmult_le_compat_l; lra).
    apply Rabs_le. split; lra.
Qed.
