(** asinh's accurate path, the Newton step [y + (x - sinh y)/cosh y] in [Q256]:
    the scaled reciprocal, [sinh] and [cosh] from [e^y] and [e^-y], and the
    step's error against [arcsinh]. *)
From Coq Require Import Reals ZArith Lia Lra Psatz List.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Q Require Import Q256 Q256Real QSpec Limbs LimbScan.
Require Import Ln1pLemmas AsinTables AsinKernel AsinQSeries AsinRecip AsinhTables AsinhKernel AsinhWithin AsinhRoot AsinhExp AsinhExpRed AsinhRecip AsinhNewtonReal.
Open Scope R_scope.

Lemma top_bounds c : Q256Real.valid c -> 0 < qval c -> bpow radix2 (Q256Real.top c) <= qval c < bpow radix2 (Q256Real.top c + 1).
Proof.
  intros [O N] Pos. unfold Q256Real.top. rewrite is_zero_ok by apply O.
  destruct (Z.eqb_spec (v (m c)) 0) as [Z | Z].
  - exfalso. rewrite (qval_zero c Z) in Pos. lra.
  - destruct N as [N | N]; [contradiction | ].
    pose proof (mag_bounds c N) as [Low High]. rewrite mag_abs in Low, High by exact O.
    rewrite (Rabs_pos_eq (qval c)) in Low, High by lra.
    replace (e c + 255 + 1)%Z with (e c + 256)%Z by ring. split; assumption.
Qed.

(** [asinh_recip c] is [1/c] to [2^-252], for a positive valid [c]. *)
Theorem asinh_recip_ok c : Q256Real.valid c -> 0 < qval c ->
  Q256Real.valid (asinh_recip c) /\ 0 < qval (asinh_recip c) /\ Rabs (qval c * qval (asinh_recip c) - 1) <= bpow radix2 (-252).
Proof.
  intros Vc Pos. unfold asinh_recip.
  set (tp := Q256Real.top c) in *.
  destruct (top_bounds c Vc Pos) as [Lo Hi].
  change (Q256Real.top c) with tp in Lo, Hi.
  destruct (mul_pow2_any c (- tp) Vc) as [V1 Q1].
  set (c1 := Q256Real.mul_pow2 c (- tp)) in *.
  assert (Hp : bpow radix2 tp * bpow radix2 (- tp) = 1) by (rewrite <- bpow_plus; replace (tp + - tp)%Z with 0%Z by ring; reflexivity).
  assert (Hp1 : bpow radix2 (tp + 1) * bpow radix2 (- tp) = 2) by (rewrite bpow_plus; change (bpow radix2 1) with 2; nra).
  assert (Pm : 0 < bpow radix2 (- tp)) by apply bpow_gt_0.
  assert (Hc1 : 1 <= qval c1 <= 2).
  { rewrite Q1. split.
    - assert (bpow radix2 tp * bpow radix2 (- tp) <= qval c * bpow radix2 (- tp)) by (apply Rmult_le_compat_r; lra). lra.
    - assert (qval c * bpow radix2 (- tp) <= bpow radix2 (tp + 1) * bpow radix2 (- tp)) by (apply Rmult_le_compat_r; lra). lra. }
  destruct (q_recip_ok2 c1 V1 Hc1) as [V2 [P2 E2]].
  destruct (mul_pow2_any (q_recip c1) (- tp) V2) as [V3 Q3].
  refine (conj V3 (conj _ _)).
  - rewrite Q3. apply Rmult_lt_0_compat; [exact P2 | exact Pm].
  - rewrite Q3. replace (qval c * (qval (q_recip c1) * bpow radix2 (- tp))) with (qval c1 * qval (q_recip c1)) by (rewrite Q1; ring).
    exact E2.
Qed.

Lemma inv_le x c : 0 < x -> 1 <= c * x -> / x <= c.
Proof. intros Hx H. apply (Rmult_le_reg_l x); [exact Hx | ]. rewrite Rinv_r by lra. lra. Qed.

Lemma exp_ln2_k z : exp (IZR z * ln 2) = bpow radix2 z.
Proof.
  rewrite <- ln_bpow. rewrite exp_ln. reflexivity. apply bpow_gt_0.
Qed.

Definition rho_e : R := 3.1 * bpow radix2 (-237).

(** [e^y] and [e^-y] from the exponential and the scaled reciprocal. *)
Lemma exp_pair y : Q256Real.valid y -> 0 <= qval y <= 711 ->
  let '(m, kz) := asinh_exp y in
  let e := Q256Real.mul_pow2 m kz in
  let ei := Q256Real.mul_pow2 (asinh_recip m) (- kz) in
  Q256Real.valid e /\ Q256Real.valid ei /\
  Rabs (qval e - exp (qval y)) <= rho_e * exp (qval y) /\
  Rabs (qval ei - exp (- qval y)) <= rho_e * exp (- qval y) /\
  0 < qval e /\ 0 < qval ei.
Proof.
  intros Vy Hy. pose proof (asinh_exp_ok y Vy Hy) as X.
  destruct (asinh_exp y) as [m kz] eqn:Ex. cbn [fst snd] in X. cbv zeta.
  destruct X as [Vm [Hrt [Hk Hm]]].
  set (yv := qval y) in *.
  set (rt := yv - IZR kz * ln 2) in *.
  set (M := qval m) in *.
  set (a := bpow radix2 kz).
  assert (Ha : 0 < a) by apply bpow_gt_0.
  apply Rabs_le_inv in Hrt. destruct Hrt as [Hrt1 Hrt2].
  assert (Hex : 0.7 <= exp rt <= 1.42) by (split; interval with (i_prec 60)).
  assert (HexN : 0.7 <= exp (- rt) <= 1.42) by (split; interval with (i_prec 60)).
  destruct Hex as [Hex1 Hex2]. destruct HexN as [HN1 HN2].
  assert (E1 : exp yv = exp rt * a).
  { unfold a. rewrite <- (exp_ln2_k kz), <- exp_plus. f_equal. unfold rt. ring. }
  assert (E2 : exp (- yv) = exp (- rt) / a) by (rewrite exp_Ropp, exp_Ropp, E1; field; split; [apply Rgt_not_eq, exp_pos | lra]).
  assert (HU : bpow radix2 (-237) <= / 1000000000000) by (apply Rle_trans with (bpow radix2 (-40)); [apply bpow_le; lia | bpow_num; apply Rinv_le_contravar; lra]).
  pose proof (bpow_gt_0 radix2 (-237)) as Hb0.
  assert (HM : 0.69 <= M <= 1.43).
  { apply Rabs_le_inv in Hm. destruct Hm as [Hm1 Hm2]. split; lra. }
  destruct HM as [HM1 HM2].
  destruct (mul_pow2_any m kz Vm) as [Ve Qe].
  assert (Pm : 0 < M) by lra.
  destruct (asinh_recip_ok m Vm Pm) as [Vr [Pr Er]].
  destruct (mul_pow2_any (asinh_recip m) (- kz) Vr) as [Vei Qei].
  set (R := qval (asinh_recip m)) in *.
  assert (Ha' : bpow radix2 (- kz) = / a) by (unfold a; rewrite bpow_opp; reflexivity).
  rewrite Ha' in Qei.
  refine (conj Ve (conj Vei _)).
  assert (Hbe : Rabs (qval (Q256Real.mul_pow2 m kz) - exp yv) <= rho_e * exp yv).
  { rewrite Qe. unfold M. replace (qval m * bpow radix2 kz - exp yv) with ((qval m - exp rt) * a) by (rewrite E1; unfold a; ring).
    rewrite Rabs_mult, (Rabs_pos_eq a) by lra. rewrite E1. unfold rho_e.
    assert (Rabs (qval m - exp rt) * a <= bpow radix2 (-237) * a) by (apply Rmult_le_compat_r; [lra | exact Hm]).
    assert (bpow radix2 (-237) * a <= 3.1 * bpow radix2 (-237) * (exp rt * a)).
    { assert (bpow radix2 (-237) * a * 1 <= bpow radix2 (-237) * a * (3.1 * exp rt)) by (apply Rmult_le_compat_l; [nra | lra]). nra. }
    lra. }
  assert (HM0 : M <> 0) by lra.
  assert (Hexp0 : exp rt <> 0) by (apply Rgt_not_eq; lra).
  assert (HR1 : Rabs (R - / M) <= bpow radix2 (-252) / 0.69).
  { assert (E : R - / M = (R * M - 1) / M) by (field; exact HM0).
    rewrite E. rewrite Rabs_div' by exact HM0. rewrite (Rabs_pos_eq M) by lra.
    assert (Rabs (R * M - 1) <= bpow radix2 (-252)) by (rewrite Rmult_comm; exact Er).
    apply Rle_trans with (bpow radix2 (-252) / M); [unfold Rdiv; apply Rmult_le_compat_r; [apply Rlt_le, Rinv_0_lt_compat; lra | exact H] | ].
    unfold Rdiv. apply Rmult_le_compat_l; [apply bpow_ge_0 | apply Rinv_le_contravar; lra]. }
  assert (HR2 : Rabs (/ M - exp (- rt)) <= bpow radix2 (-237) / (0.69 * 0.7)).
  { rewrite exp_Ropp. assert (E : / M - / exp rt = (exp rt - M) / (M * exp rt)) by (field; split; assumption).
    rewrite E, Rabs_div'. 
    - rewrite (Rabs_pos_eq (M * exp rt)) by nra. rewrite Rabs_minus_sym.
      apply Rle_trans with (bpow radix2 (-237) / (M * exp rt)); [unfold Rdiv; apply Rmult_le_compat_r; [apply Rlt_le, Rinv_0_lt_compat; nra | exact Hm] | ].
      unfold Rdiv. apply Rmult_le_compat_l; [apply bpow_ge_0 | apply Rinv_le_contravar; [lra | nra]].
    - nra. }
  assert (HRe : Rabs (R - exp (- rt)) <= 2.08 * bpow radix2 (-237)).
  { assert (B252 : bpow radix2 (-252) = bpow radix2 (-237) * bpow radix2 (-15)) by (rewrite <- bpow_plus; reflexivity).
    assert (B15 : bpow radix2 (-15) <= / 30000) by (bpow_num; apply Rinv_le_contravar; lra).
    assert (Hs : Rabs (R - exp (- rt)) <= Rabs (R - / M) + Rabs (/ M - exp (- rt))).
    { replace (R - exp (- rt)) with ((R - / M) + (/ M - exp (- rt))) by ring. apply Rabs_triang. }
    assert (bpow radix2 (-252) / 0.69 <= 0.001 * bpow radix2 (-237)).
    { rewrite B252. assert (bpow radix2 (-237) * bpow radix2 (-15) <= bpow radix2 (-237) * / 30000) by (apply Rmult_le_compat_l; lra). unfold Rdiv.
      assert (/ 0.69 <= 1.45) by (apply inv_le; lra).
      nra. }
    assert (bpow radix2 (-237) / (0.69 * 0.7) <= 2.071 * bpow radix2 (-237)).
    { unfold Rdiv. rewrite Rmult_comm. apply Rmult_le_compat_r; [lra | ]. assert (Hi2 : / (0.69 * 0.7) <= 2.071) by (apply inv_le; lra). exact Hi2. }
    lra. }
  assert (Hbei : Rabs (qval (Q256Real.mul_pow2 (asinh_recip m) (- kz)) - exp (- yv)) <= rho_e * exp (- yv)).
  { rewrite Qei, E2. replace (R * / a - exp (- rt) / a) with ((R - exp (- rt)) * / a) by (unfold Rdiv; ring).
    rewrite Rabs_mult, Rabs_Rinv by lra. rewrite (Rabs_pos_eq a) by lra. unfold rho_e.
    assert (Hia : 0 < / a) by (apply Rinv_0_lt_compat; lra).
    assert (Rabs (R - exp (- rt)) * / a <= 2.08 * bpow radix2 (-237) * / a) by (apply Rmult_le_compat_r; [lra | exact HRe]).
    assert (2.08 * bpow radix2 (-237) * / a <= 3.1 * bpow radix2 (-237) * (exp (- rt) / a)).
    { unfold Rdiv. assert (2.08 * bpow radix2 (-237) * / a <= 3.1 * bpow radix2 (-237) * (0.7 * / a)).
      { assert (bpow radix2 (-237) * / a >= 0) by (apply Rle_ge, Rmult_le_pos; [apply bpow_ge_0 | lra]). nra. }
      assert (3.1 * bpow radix2 (-237) * (0.7 * / a) <= 3.1 * bpow radix2 (-237) * (exp (- rt) * / a)).
      { apply Rmult_le_compat_l; [nra | apply Rmult_le_compat_r; lra]. }
      lra. }
    lra. }
  repeat split; try assumption.
  - rewrite Qe. apply Rmult_lt_0_compat; [exact Pm | exact Ha].
  - rewrite Qei. apply Rmult_lt_0_compat; [exact Pr | apply Rinv_0_lt_compat; exact Ha].
Qed.

Lemma rabs_sub_r' a b : Rabs a <= Rabs b + Rabs (a - b).
Proof. apply Rle_trans with (Rabs (b + (a - b))); [right; f_equal; ring | apply Rabs_triang]. Qed.

(** The algebra of the computed step: [finv] is within [1.2 rho + 714 U] of [yv + u]. *)
Lemma newton_alg (C S xv sq cq Rc rrv prv finv yv u rho U eps d3 : R) :
  1 <= C -> xv - S = C * u -> Rabs u <= 0.0000011 ->
  Rabs (sq - S) <= rho * C -> Rabs (cq - C) <= rho * C -> 0 < rho <= 1e-60 -> 0 < U <= rho ->
  Rabs (cq * Rc - 1) <= eps -> 0 <= eps <= rho / 1000 ->
  Rabs (rrv - (xv - sq)) <= 1.01 * U * C ->
  prv = rrv * Rc * (1 + d3) -> Rabs d3 <= U ->
  0 <= yv <= 711 -> Rabs (finv - (yv + prv)) <= U * Rmax (Rabs yv) (Rabs prv) ->
  Rabs (finv - (yv + u)) <= 1.2 * rho + 714 * U.
Proof.
  intros HC Hx Hu Hs Hc [Hr0 Hr1] [HU0 HU1] He [He0 He1] Hrr Hprv Hd3 [Hy0 Hy1] Hfin.
  pose proof Hc as Hs0. rewrite Rabs_minus_sym in Hs0. pose proof Hc as Hcabs.
  assert (HCp : 0 < C) by lra.
  set (w := rrv - C * u).
  assert (Hw : Rabs w <= (1.01 * rho + 1.01 * U) * C).
  { assert (E : w = (rrv - (xv - sq)) + (S - sq)) by (unfold w; lra).
    rewrite E. apply Rle_trans with (Rabs (rrv - (xv - sq)) + Rabs (S - sq)); [apply Rabs_triang | ].
    rewrite Rabs_minus_sym in Hs. nra. }
  set (theta := Rc * C - 1).
  assert (Hcq : cq >= C * (1 - rho)).
  { apply Rabs_le_inv in Hc. destruct Hc as [Hc1 Hc2]. nra. }
  assert (Hcqp : 0.5 <= cq) by nra.
  assert (Hth : Rabs theta <= 1.002 * rho).
  { assert (E : theta = (cq * Rc - 1) * (C / cq) + (C / cq - 1)).
    { unfold theta. field. lra. }
    assert (Hr : C / cq <= 1.0001).
    { apply (Rmult_le_reg_r cq); [lra | ]. unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. nra. }
    assert (Hr2 : Rabs (C / cq - 1) <= 1.0001 * rho).
    { assert (E2 : C / cq - 1 = (C - cq) / cq) by (field; lra).
      rewrite E2, Rabs_div' by lra. rewrite (Rabs_pos_eq cq) by lra.
      assert (Hcc : Rabs (C - cq) <= rho * C) by exact Hs0.
      assert (HC2 : C <= 1.0001 * cq) by nra.
      apply (Rmult_le_reg_r cq); [lra | ]. unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. rewrite Rmult_1_r.
      assert (rho * C <= rho * (1.0001 * cq)) by (apply Rmult_le_compat_l; lra). nra. }
    rewrite E. 
    apply Rle_trans with (Rabs ((cq * Rc - 1) * (C / cq)) + Rabs (C / cq - 1)); [apply Rabs_triang | ].
    rewrite Rabs_mult, (Rabs_pos_eq (C / cq)) by (apply Rmult_le_pos; [lra | apply Rlt_le, Rinv_0_lt_compat; lra]).
    assert (Rabs (cq * Rc - 1) * (C / cq) <= (rho / 1000) * 1.0001) by (apply Rmult_le_compat; [apply Rabs_pos | apply Rmult_le_pos; [lra | apply Rlt_le, Rinv_0_lt_compat; lra] | lra | exact Hr]).
    lra. }
  set (P := (1 + theta) * (1 + d3)).
  assert (Hprv2 : prv = (u + w / C) * P).
  { rewrite Hprv. unfold P, theta, w. field. lra. }
  apply Rabs_le_inv in Hth. destruct Hth as [Ht1 Ht2].
  pose proof Hd3 as Hd3c. apply Rabs_le_inv in Hd3c. destruct Hd3c as [Hd1 Hd2].
  assert (HP : Rabs (P - 1) <= 2.01 * rho).
  { assert (E : P - 1 = theta + d3 + theta * d3) by (unfold P; ring).
    assert (Hp1 : Rabs (theta * d3) <= 1.002e-60 * 1e-60).
    { rewrite Rabs_mult. apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | apply Rabs_le; lra | apply Rabs_le; lra]. }
    rewrite E. apply Rabs_le_inv in Hp1. destruct Hp1 as [Hq1 Hq2].
    apply Rabs_le. split; nra. }
  assert (HPa : Rabs P <= 1.0001) by (apply Rabs_le_inv in HP; apply Rabs_le; split; nra).
  assert (Hwc : Rabs (w / C) <= 1.01 * rho + 1.01 * U).
  { rewrite Rabs_div' by lra. rewrite (Rabs_pos_eq C) by lra.
    apply (Rmult_le_reg_r C); [lra | ]. unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. rewrite Rmult_1_r. lra. }
  assert (Hpu : Rabs (prv - u) <= 1.011 * rho + 1.011 * U).
  { assert (E : prv - u = (w / C) * P + u * (P - 1)) by (rewrite Hprv2; ring).
    rewrite E. apply Rle_trans with (Rabs ((w / C) * P) + Rabs (u * (P - 1))); [apply Rabs_triang | ].
    rewrite !Rabs_mult.
    assert (Rabs (w / C) * Rabs P <= (1.01 * rho + 1.01 * U) * 1.0001) by (apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | exact Hwc | exact HPa]).
    assert (Rabs u * Rabs (P - 1) <= 0.0000011 * (2.01 * rho)) by (apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | exact Hu | exact HP]).
    lra. }
  assert (Hprv1 : Rabs prv <= 1).
  { apply Rle_trans with (Rabs u + Rabs (prv - u)); [apply rabs_sub_r' | lra]. }
  assert (Hmx : Rmax (Rabs yv) (Rabs prv) <= 712).
  { apply Rmax_lub; [rewrite Rabs_pos_eq by lra; lra | lra]. }
  assert (Hfin2 : Rabs (finv - (yv + prv)) <= U * 712).
  { apply Rle_trans with (1 := Hfin). apply Rmult_le_compat_l; lra. }
  apply Rle_trans with (Rabs (finv - (yv + prv)) + Rabs (prv - u)).
  - replace (finv - (yv + u)) with ((finv - (yv + prv)) + (prv - u)) by ring. apply Rabs_triang.
  - lra.
Qed.

Lemma bp254_small : bpow radix2 (-254) <= 1e-76.
Proof.
  bpow_num. apply Rle_trans with (/ 10000000000000000000000000000000000000000000000000000000000000000000000000000).
  - apply Rinv_le_contravar; lra.
  - lra.
Qed.

(** One computed Newton step is within [2^-235] of the exact one. *)
Theorem newton_step_ok x y xv : Q256Real.valid x -> Q256Real.valid y -> qval x = xv -> 0 < xv ->
  0 <= qval y <= 711 -> Rabs (arcsinh xv - qval y) <= / 1000000 ->
  Q256Real.valid (asinh_newton x y) /\
  Rabs (qval (asinh_newton x y) - arcsinh xv) <= 4 * ((arcsinh xv - qval y) * (arcsinh xv - qval y)) + bpow radix2 (-235).
Proof.
  intros Vx Vy Qx Pxv Hy Hdelta.
  pose proof (exp_pair y Vy Hy) as XP.
  unfold asinh_newton. destruct (asinh_exp y) as [m kz] eqn:Ex. cbv zeta in XP |- *.
  destruct XP as [Ve [Vei [Hbe [Hbei [Pe Pei]]]]].
  set (e := Q256Real.mul_pow2 m kz) in *. set (ei := Q256Real.mul_pow2 (asinh_recip m) (- kz)) in *.
  set (yv := qval y) in *.
  set (A := arcsinh xv) in *.
  set (delta := A - yv) in *.
  destruct bpow_254 as [B252 [B255 [Upos Usmall]]].
  set (U := bpow radix2 (-254)) in *.
  assert (Hrho : rho_e = 406323.2 * U).
  { unfold rho_e, U. replace (-237)%Z with (-254 + 17)%Z by reflexivity. rewrite bpow_plus. change (bpow radix2 17) with 131072. lra. }
  assert (B237 : bpow radix2 (-237) = 131072 * U) by (unfold U; replace (-237)%Z with (-254 + 17)%Z by reflexivity; rewrite bpow_plus; change (bpow radix2 17) with 131072; ring).
  assert (B235 : bpow radix2 (-235) = 524288 * U) by (unfold U; replace (-235)%Z with (-254 + 19)%Z by reflexivity; rewrite bpow_plus; change (bpow radix2 19) with 524288; ring).
  assert (B252' : bpow radix2 (-252) = 4 * U) by exact B252.
  assert (HUs : U <= 1e-76) by exact bp254_small.
  (* the exponentials *)
  set (E1 := exp yv) in *. set (E2 := exp (- yv)) in *.
  assert (HE1 : 0 < E1) by apply exp_pos. assert (HE2 : 0 < E2) by apply exp_pos.
  assert (HE12 : E1 * E2 = 1) by (unfold E1, E2; rewrite <- exp_plus; replace (yv + - yv) with 0 by ring; apply exp_0).
  set (C := cosh yv). set (S := sinh yv).
  assert (HC : C = (E1 + E2) / 2) by reflexivity.
  assert (HS : S = (E1 - E2) / 2) by reflexivity.
  assert (HC1 : 1 <= C) by apply cosh_pos.
  set (qe := qval e) in *. set (qei := qval ei) in *.
  rewrite Hrho in Hbe, Hbei.
  pose proof Hbe as Hbe_c. apply Rabs_le_inv in Hbe_c. destruct Hbe_c as [Hbe1 Hbe2].
  pose proof Hbei as Hbei_c. apply Rabs_le_inv in Hbei_c. destruct Hbei_c as [Hbi1 Hbi2].
  assert (Hr1 : 406323.2 * U <= 0.0001) by lra.
  assert (P1 : 406323.2 * U * E1 <= 0.0001 * E1) by (apply Rmult_le_compat_r; lra).
  assert (P2 : 406323.2 * U * E2 <= 0.0001 * E2) by (apply Rmult_le_compat_r; lra).
  assert (Hqe : qe <= 1.0001 * E1) by lra.
  assert (Hqei : qei <= 1.0001 * E2) by lra.
  assert (Hqe0 : 0.9999 * E1 <= qe) by lra.
  assert (Hqei0 : 0.9999 * E2 <= qei) by lra.
  (* s0, c0 *)
  destruct (neg_any ei Vei) as [Vn En].
  destruct (add_any e (Q256.neg_q ei) Ve Vn) as [Vs0 Es0].
  destruct (add_any e ei Ve Vei) as [Vc0 Ec0].
  change (qval e) with qe in Es0, Ec0. change (qval ei) with qei in Ec0. rewrite En in Es0.
  change (q_sub e ei) with (Q256.add e (Q256.neg_q ei)).
  destruct (mul_pow2_any (Q256.add e (Q256.neg_q ei)) (-1) Vs0) as [Vsq Qsq].
  destruct (mul_pow2_any (Q256.add e ei) (-1) Vc0) as [Vcq Qcq].
  assert (Hb1 : bpow radix2 (-1) = / 2) by (bpow_num; reflexivity).
  rewrite Hb1 in Qsq, Qcq.
  set (sinh_q := Q256Real.mul_pow2 (Q256.add e (Q256.neg_q ei)) (-1)) in *.
  set (cosh_q := Q256Real.mul_pow2 (Q256.add e ei) (-1)) in *.
  assert (Hmx1 : Rmax (Rabs qe) (Rabs (- qei)) <= 1.0001 * (E1 + E2)).
  { apply Rmax_lub; [rewrite Rabs_pos_eq by lra; lra | rewrite Rabs_Ropp, Rabs_pos_eq by lra; lra]. }
  assert (Hmx2 : Rmax (Rabs qe) (Rabs qei) <= 1.0001 * (E1 + E2)).
  { apply Rmax_lub; [rewrite Rabs_pos_eq by lra; lra | rewrite Rabs_pos_eq by lra; lra]. }
  set (rhos := 406323.2 * U + 2 * U).
  assert (Hes0 : Rabs (qval (Q256.add e (Q256.neg_q ei)) - (qe + - qei)) <= U * (1.0001 * (E1 + E2))).
  { apply Rle_trans with (1 := Es0). apply Rmult_le_compat_l; [lra | exact Hmx1]. }
  assert (Hec0 : Rabs (qval (Q256.add e ei) - (qe + qei)) <= U * (1.0001 * (E1 + E2))).
  { apply Rle_trans with (1 := Ec0). apply Rmult_le_compat_l; [lra | exact Hmx2]. }
  apply Rabs_le_inv in Hes0. destruct Hes0 as [Hs1 Hs2].
  apply Rabs_le_inv in Hec0. destruct Hec0 as [Hc1 Hc2].
  assert (Hsq : Rabs (qval sinh_q - S) <= rhos * C).
  { rewrite Qsq. apply Rabs_le. unfold rhos. rewrite HC, HS. split; nra. }
  assert (Hcq : Rabs (qval cosh_q - C) <= rhos * C).
  { rewrite Qcq. apply Rabs_le. unfold rhos. rewrite HC. split; nra. }
  (* the correction *)
  assert (HsA : sinh (yv + delta) = xv) by (replace (yv + delta) with A by (unfold delta; ring); unfold A; apply sinh_arcsinh).
  assert (Hd50 : Rabs delta <= / 50) by (apply Rle_trans with (/ 1000000); [exact Hdelta | lra]).
  destruct (newton_exact yv delta Hd50) as [NE1 NE2].
  rewrite HsA in NE1, NE2. change (sinh yv) with S in NE1, NE2. change (cosh yv) with C in NE1, NE2.
  set (u := (xv - S) / C) in *.
  assert (Hx : xv - S = C * u) by (unfold u; field; lra).
  assert (Hu : Rabs u <= 0.0000011).
  { apply Rle_trans with (1.1 * Rabs delta); [exact NE2 | ]. assert (Rabs delta <= / 1000000) by exact Hdelta. lra. }
  (* cosh_q > 0, its reciprocal *)
  assert (Hrs : 0 < rhos <= 1e-60) by (unfold rhos; split; lra).
  apply Rabs_le_inv in Hcq. destruct Hcq as [Hcq1 Hcq2].
  assert (Hcqp : 0 < qval cosh_q) by (unfold rhos in Hcq1; nra).
  destruct (asinh_recip_ok cosh_q Vcq Hcqp) as [Vrc [Prc Erc]].
  set (Rc := asinh_recip cosh_q) in *.
  (* the residual, product and sum *)
  destruct (neg_any sinh_q Vsq) as [Vn2 En2].
  destruct (add_any x (Q256.neg_q sinh_q) Vx Vn2) as [Vrr Err].
  change (q_sub x sinh_q) with (Q256.add x (Q256.neg_q sinh_q)).
  set (rr := Q256.add x (Q256.neg_q sinh_q)) in *.
  destruct (mul_relative rr Rc Vrr Vrc) as [Vpr [d3 [Hd3 Epr]]].
  set (pr := Q256.mul rr Rc) in *.
  destruct (add_any y pr Vy Vpr) as [Vfin Efin].
  set (fin := Q256.add y pr) in *.
  change (qval y) with yv in Efin. rewrite Qx in Err. rewrite En2 in Err.
  apply Rabs_le_inv in Hsq. destruct Hsq as [Hsq1 Hsq2].
  assert (HxvC : Rabs xv <= 1.01 * C).
  { assert (E : xv = S + C * u) by lra.
    pose proof (sinh_le_cosh yv) as Hsc. change (sinh yv) with S in Hsc. change (cosh yv) with C in Hsc.
    assert (Hcu : Rabs (C * u) <= C * 0.0000011) by (rewrite Rabs_mult, (Rabs_pos_eq C) by lra; apply Rmult_le_compat_l; lra).
    apply Rabs_le_inv in Hsc. apply Rabs_le_inv in Hcu. apply Rabs_le. split; lra. }
  assert (HsqC : Rabs (qval sinh_q) <= 1.01 * C).
  { pose proof (sinh_le_cosh yv) as Hsc. change (sinh yv) with S in Hsc. change (cosh yv) with C in Hsc.
    apply Rabs_le_inv in Hsc. apply Rabs_le.
    assert (rhos * C <= 1e-60 * C) by (apply Rmult_le_compat_r; lra). split; lra. }
  assert (Hrr : Rabs (qval rr - (xv - qval sinh_q)) <= 1.01 * U * C).
  { apply Rle_trans with (1 := Err). 
    assert (Rmax (Rabs xv) (Rabs (- qval sinh_q)) <= 1.01 * C) by (apply Rmax_lub; [exact HxvC | rewrite Rabs_Ropp; exact HsqC]).
    replace (1.01 * U * C) with (U * (1.01 * C)) by ring. apply Rmult_le_compat_l; lra. }
  assert (Hd3' : Rabs d3 <= U).
  { rewrite B255 in Hd3. apply Rle_trans with (U / 2); [exact Hd3 | lra]. }
  assert (Hfin' : Rabs (qval fin - (yv + qval pr)) <= U * Rmax (Rabs yv) (Rabs (qval pr))) by exact Efin.
  assert (Hepsb : 0 <= bpow radix2 (-252) <= rhos / 1000) by (rewrite B252'; unfold rhos; split; lra).
  pose proof (newton_alg C S xv (qval sinh_q) (qval cosh_q) (qval Rc) (qval rr) (qval pr) (qval fin) yv u rhos U (bpow radix2 (-252)) d3
    HC1 Hx Hu ltac:(rewrite Rabs_minus_sym; apply Rabs_le; split; lra) ltac:(apply Rabs_le; split; lra) Hrs
    ltac:(split; [exact Upos | unfold rhos; lra]) Erc Hepsb Hrr Epr Hd3' Hy Hfin') as NA.
  split; [exact Vfin | ].
  assert (Hyu : Rabs (yv + u - A) <= 4 * (delta * delta)).
  { replace (yv + u - A) with (u - delta) by (unfold delta; ring). exact NE1. }
  apply Rle_trans with (Rabs (qval fin - (yv + u)) + Rabs (yv + u - A)).
  - replace (qval fin - A) with ((qval fin - (yv + u)) + (yv + u - A)) by ring. apply Rabs_triang.
  - rewrite B235. unfold rhos in NA. lra.
Qed.
