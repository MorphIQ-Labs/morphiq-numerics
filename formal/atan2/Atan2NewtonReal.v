(** The accurate path's Newton step for [atan (n/d)], in real arithmetic: from a start
    within [2^-63 (1 + 1e-4)] of the angle, whatever the roundings do within their
    contracts, the step is within [2^-190] of it, relatively. Every error scales with
    [t = n/d], so the bound holds down to the smallest quotient the fast path admits. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
Open Scope R_scope.

Definition tauA : R := / 100000000000000000000000000000000000000000000000000000000000.
Definition etaA : R := / 9223372036854775808 * 1.0001.
Definition bndN : R := 5 * / 10000000000000000000000000000000000000000000000000000000000.
Definition bnd190 : R := / 1569275433846670190958947355801916604025588861116008628224.

Lemma tauA_facts : 0 < tauA <= / 1000000.
Proof. unfold tauA. split; [apply Rinv_0_lt_compat; lra | apply Rinv_le_contravar; lra]. Qed.

Lemma bnd_mul x y X Y : Rabs x <= X -> Rabs y <= Y -> Rabs (x * y) <= X * Y.
Proof.
  intros Hx Hy. rewrite Rabs_mult. apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | exact Hx | exact Hy].
Qed.

(** [(1 + a)(1 + b) - 1] for two small relative errors. *)
Lemma prod_dev a b : Rabs a <= tauA -> Rabs b <= tauA -> Rabs ((1 + a) * (1 + b) - 1) <= 2.01 * tauA.
Proof.
  intros Ha Hb. destruct tauA_facts as [T0 T1].
  pose proof (bnd_mul a b tauA tauA Ha Hb) as Hab.
  apply Rabs_le_inv in Ha as [A1 A2]. apply Rabs_le_inv in Hb as [B1 B2]. apply Rabs_le_inv in Hab as [C1 C2].
  replace ((1 + a) * (1 + b) - 1) with (a + b + a * b) by ring.
  apply Rabs_le. split; nra.
Qed.

Lemma abs_tri3 a b c : Rabs (a + b + c) <= Rabs a + Rabs b + Rabs c.
Proof.
  apply Rle_trans with (Rabs (a + b) + Rabs c); [apply Rabs_triang | ].
  pose proof (Rabs_triang a b). lra.
Qed.

(** [|g / d| <= tau t] from [|g| <= tau (t d)]. *)
Lemma div_small g d t : 0 < d -> Rabs g <= tauA * (t * d) -> Rabs (g / d) <= tauA * t.
Proof.
  intros Hd H. unfold Rdiv. rewrite Rabs_mult, Rabs_Rinv by lra. rewrite (Rabs_pos_eq d) by lra.
  apply (Rmult_le_reg_r d); [exact Hd | ]. rewrite Rmult_assoc, Rinv_l by lra. lra.
Qed.

Lemma div_small1 g d : 0 < d -> Rabs g <= tauA * d -> Rabs (g / d) <= tauA.
Proof.
  intros Hd H. unfold Rdiv. rewrite Rabs_mult, Rabs_Rinv by lra. rewrite (Rabs_pos_eq d) by lra.
  apply (Rmult_le_reg_r d); [exact Hd | ]. rewrite Rmult_assoc, Rinv_l by lra. lra.
Qed.

Theorem newton_atan_P n d t Y r s c w sn cs sg gm d1 d2 d3 d4 d6 e g1 g4 p1 p2 nuh dh rih Ph :
  0 < d -> 0 < t -> t <= 1 -> n = t * d ->
  0.5 * t <= Y -> Y <= t -> Y <= 0.7854 ->
  Rabs (Y - r) <= etaA * Y ->
  0 <= s -> s <= 1.0001 * t -> 0.7 <= c -> c <= 1 ->
  t * c - s = w * (c + t * s) -> 0 < c + t * s ->
  Rabs (Y - r - w) <= Rabs w * Rabs w * Rabs w / 3 -> Rabs w <= 1.0001 * Rabs (Y - r) ->
  sn = s * (1 + sg) -> Rabs sg <= tauA -> cs = c * (1 + gm) -> Rabs gm <= tauA ->
  p1 = n * cs * (1 + d1) -> Rabs d1 <= tauA -> p2 = d * sn * (1 + d2) -> Rabs d2 <= tauA ->
  nuh = (p1 + - p2) + g1 -> Rabs g1 <= tauA * n ->
  dh = (d * cs * (1 + d3) + n * sn * (1 + d4)) + g4 -> Rabs d3 <= tauA -> Rabs d4 <= tauA -> Rabs g4 <= tauA * d ->
  dh * rih = 1 + e -> Rabs e <= tauA ->
  Ph = nuh * rih * (1 + d6) -> Rabs d6 <= tauA ->
  Rabs (Ph - w) <= 7.7 * tauA * t.
Proof.
  intros Hd Ht Ht1 Hn HYl HYh HY7 Hr Hs0 Hs1 Hc0 Hc1 Hex Dpos Hcub Hw Hsn Hsg Hcs Hgm Hp1 Hd1 Hp2 Hd2 Hnu Hg1 Hdh Hd3 Hd4 Hg4 Hrih He HPh Hd6.
  destruct tauA_facts as [T0 T1].
  assert (Hdne : d <> 0) by lra.
  (* the numerator and denominator against the exact ones *)
  remember (t * c * ((1 + gm) * (1 + d1) - 1) - s * ((1 + sg) * (1 + d2) - 1) + g1 / d) as anu eqn:Eanu.
  remember (c * ((1 + gm) * (1 + d3) - 1) + t * s * ((1 + sg) * (1 + d4) - 1) + g4 / d) as aD eqn:EaD.
  assert (Hnu' : nuh = d * ((t * c - s) + anu)).
  { rewrite Hnu, Hp1, Hp2, Hcs, Hsn, Hn, Eanu. field. exact Hdne. }
  assert (Hdh' : dh = d * ((c + t * s) + aD)).
  { rewrite Hdh, Hcs, Hsn, Hn, EaD. field. exact Hdne. }
  assert (Hp_gm : Rabs ((1 + gm) * (1 + d1) - 1) <= 2.01 * tauA) by (apply prod_dev; assumption).
  assert (Hp_sg : Rabs ((1 + sg) * (1 + d2) - 1) <= 2.01 * tauA) by (apply prod_dev; assumption).
  assert (Hp_gm3 : Rabs ((1 + gm) * (1 + d3) - 1) <= 2.01 * tauA) by (apply prod_dev; assumption).
  assert (Hp_sg4 : Rabs ((1 + sg) * (1 + d4) - 1) <= 2.01 * tauA) by (apply prod_dev; assumption).
  assert (Hg1d : Rabs (g1 / d) <= tauA * t).
  { apply div_small; [exact Hd | rewrite <- Hn; exact Hg1]. }
  assert (Hg4d : Rabs (g4 / d) <= tauA) by (apply div_small1; assumption).
  assert (Htc : Rabs (t * c) <= t) by (rewrite Rabs_pos_eq by nra; nra).
  assert (Hts : Rabs (t * s) <= 1.0001) by (rewrite Rabs_pos_eq by nra; nra).
  assert (Hsa : Rabs s <= 1.0001 * t) by (rewrite Rabs_pos_eq by lra; exact Hs1).
  assert (Hca : Rabs c <= 1) by (rewrite Rabs_pos_eq by lra; exact Hc1).
  assert (Hanu : Rabs anu <= 5.1 * tauA * t).
  { rewrite Eanu. apply Rle_trans with (Rabs (t * c * ((1 + gm) * (1 + d1) - 1)) + Rabs (- (s * ((1 + sg) * (1 + d2) - 1))) + Rabs (g1 / d)).
    - replace (t * c * ((1 + gm) * (1 + d1) - 1) - s * ((1 + sg) * (1 + d2) - 1) + g1 / d)
        with (t * c * ((1 + gm) * (1 + d1) - 1) + - (s * ((1 + sg) * (1 + d2) - 1)) + g1 / d) by ring.
      apply abs_tri3.
    - rewrite Rabs_Ropp.
      pose proof (bnd_mul (t * c) _ t (2.01 * tauA) Htc Hp_gm) as A1.
      pose proof (bnd_mul s _ (1.0001 * t) (2.01 * tauA) Hsa Hp_sg) as A2.
      nra. }
  assert (HaD : Rabs aD <= 5.1 * tauA).
  { rewrite EaD. apply Rle_trans with (Rabs (c * ((1 + gm) * (1 + d3) - 1)) + Rabs (t * s * ((1 + sg) * (1 + d4) - 1)) + Rabs (g4 / d)).
    - apply abs_tri3.
    - pose proof (bnd_mul c _ 1 (2.01 * tauA) Hca Hp_gm3) as A1.
      pose proof (bnd_mul (t * s) _ 1.0001 (2.01 * tauA) Hts Hp_sg4) as A2.
      nra. }
  (* the quotient: Ph = K (nu + anu) / (Dl + aD) *)
  set (Dl := c + t * s) in *.
  assert (HDl : 0.7 <= Dl <= 2.0001) by (unfold Dl; split; nra).
  assert (HDh : 0.69 <= Dl + aD).
  { apply Rabs_le_inv in HaD as [A1 A2]. lra. }
  remember ((1 + e) * (1 + d6)) as K eqn:EK.
  assert (HK : Rabs (K - 1) <= 2.01 * tauA) by (rewrite EK; apply prod_dev; assumption).
  assert (HPh' : Ph * (Dl + aD) = K * ((t * c - s) + anu)).
  { rewrite HPh, Hnu', EK.
    assert (HDz : Dl + aD <> 0) by (apply Rgt_not_eq; lra).
    assert (Xne : d * (Dl + aD) <> 0) by (apply Rgt_not_eq; apply Rmult_lt_0_compat; lra).
    assert (Hrih' : rih = (1 + e) / (d * (Dl + aD))).
    { apply (Rmult_eq_reg_l (d * (Dl + aD))); [ | exact Xne].
      replace (d * (Dl + aD) * ((1 + e) / (d * (Dl + aD)))) with ((1 + e) * ((d * (Dl + aD)) * / (d * (Dl + aD)))) by (unfold Rdiv; ring).
      rewrite Rinv_r by exact Xne. rewrite Rmult_1_r.
      rewrite <- Hdh'. exact Hrih. }
    rewrite Hrih'. field; repeat (first [exact Hdne | exact HDz | split]). }
  assert (Hdiff : (Ph - w) * (Dl + aD) = w * Dl * (K - 1) + K * anu - w * aD).
  { replace ((Ph - w) * (Dl + aD)) with (Ph * (Dl + aD) - w * (Dl + aD)) by ring.
    rewrite HPh', Hex. ring. }
  (* sizes of w *)
  assert (Hyr : Rabs (Y - r) <= etaA * t).
  { apply Rle_trans with (1 := Hr). apply Rmult_le_compat_l; [unfold etaA; lra | exact HYh]. }
  assert (Heta : 0 < etaA <= / 9223372036854775808 * 1.0001 + / 1000000000000000000000) by (unfold etaA; split; [ | lra]; lra).
  assert (Hwt : Rabs w <= 1.0001 * etaA * t).
  { apply Rle_trans with (1 := Hw). nra. }
  assert (Hwq : Rabs w <= / 1000000000000000000 * t).
  { apply Rle_trans with (1 := Hwt). unfold etaA. apply Rmult_le_compat_r; [lra | ]. interval with (i_prec 100). }
  (* the quotient's deviation *)
  assert (HR : Rabs (w * Dl * (K - 1) + K * anu - w * aD) <= 5.3 * tauA * t).
  { assert (B1 : Rabs (w * Dl * (K - 1)) <= (/ 1000000000000000000 * t * 2.0001) * (2.01 * tauA)).
    { apply bnd_mul; [ | exact HK]. rewrite Rabs_mult. rewrite (Rabs_pos_eq Dl) by lra.
      apply Rle_trans with ((/ 1000000000000000000 * t) * 2.0001); [ | lra].
      apply Rmult_le_compat; [apply Rabs_pos | lra | exact Hwq | lra]. }
    assert (B2 : Rabs (K * anu) <= 1.0001 * (5.1 * tauA * t)).
    { apply bnd_mul; [ | exact Hanu]. apply Rabs_le_inv in HK as [A1 A2]. apply Rabs_le. split; lra. }
    assert (B3 : Rabs (w * aD) <= (/ 1000000000000000000 * t) * (5.1 * tauA)) by (apply bnd_mul; assumption).
    apply Rle_trans with (Rabs (w * Dl * (K - 1) + K * anu) + Rabs (w * aD)).
    - replace (w * Dl * (K - 1) + K * anu - w * aD) with ((w * Dl * (K - 1) + K * anu) + - (w * aD)) by ring.
      apply Rle_trans with (Rabs (w * Dl * (K - 1) + K * anu) + Rabs (- (w * aD))); [apply Rabs_triang | rewrite Rabs_Ropp; lra].
    - assert (Rabs (w * Dl * (K - 1) + K * anu) <= Rabs (w * Dl * (K - 1)) + Rabs (K * anu)) by apply Rabs_triang.
      nra. }
  assert (HPw : Rabs (Ph - w) <= 7.7 * tauA * t).
  { assert (Hpos : 0 < Dl + aD) by lra.
    assert (E : Rabs (Ph - w) * (Dl + aD) <= 5.3 * tauA * t).
    { assert (Eq : Rabs ((Ph - w) * (Dl + aD)) = Rabs (Ph - w) * (Dl + aD)) by (rewrite Rabs_mult, (Rabs_pos_eq (Dl + aD)); [reflexivity | lra]).
      rewrite <- Eq, Hdiff. exact HR. }
    apply Rabs_le_inv in HR. 
    assert (0 <= Rabs (Ph - w)) by apply Rabs_pos.
    assert (0 <= tauA * t) by nra.
    nra. }
  exact HPw.
Qed.

Theorem newton_atan_final n d t Y r s c w sn cs sg gm d1 d2 d3 d4 d6 e g1 g4 g5 p1 p2 nuh dh rih Ph phi1 :
  0 < d -> 0 < t -> t <= 1 -> n = t * d ->
  0.5 * t <= Y -> Y <= t -> Y <= 0.7854 ->
  Rabs (Y - r) <= etaA * Y ->
  0 <= s -> s <= 1.0001 * t -> 0.7 <= c -> c <= 1 ->
  t * c - s = w * (c + t * s) -> 0 < c + t * s ->
  Rabs (Y - r - w) <= Rabs w * Rabs w * Rabs w / 3 -> Rabs w <= 1.0001 * Rabs (Y - r) ->
  sn = s * (1 + sg) -> Rabs sg <= tauA -> cs = c * (1 + gm) -> Rabs gm <= tauA ->
  p1 = n * cs * (1 + d1) -> Rabs d1 <= tauA -> p2 = d * sn * (1 + d2) -> Rabs d2 <= tauA ->
  nuh = (p1 + - p2) + g1 -> Rabs g1 <= tauA * n ->
  dh = (d * cs * (1 + d3) + n * sn * (1 + d4)) + g4 -> Rabs d3 <= tauA -> Rabs d4 <= tauA -> Rabs g4 <= tauA * d ->
  dh * rih = 1 + e -> Rabs e <= tauA ->
  Ph = nuh * rih * (1 + d6) -> Rabs d6 <= tauA ->
  Rabs (Ph - w) <= 7.7 * tauA * t ->
  phi1 = (r + Ph) + g5 -> Rabs g5 <= tauA * Y ->
  Rabs (phi1 - Y) <= bndN * Y.
Proof.
  intros Hd Ht Ht1 Hn HYl HYh HY7 Hr Hs0 Hs1 Hc0 Hc1 Hex Dpos Hcub Hw Hsn Hsg Hcs Hgm Hp1 Hd1 Hp2 Hd2 Hnu Hg1 Hdh Hd3 Hd4 Hg4 Hrih He HPh Hd6 HPw Hphi Hg5.
  destruct tauA_facts as [T0 T1].
  assert (Hyr : Rabs (Y - r) <= etaA * t).
  { apply Rle_trans with (1 := Hr). apply Rmult_le_compat_l; [unfold etaA; lra | exact HYh]. }
  assert (Hwt : Rabs w <= 1.0001 * etaA * t).
  { assert (0 < etaA) by (unfold etaA; lra). apply Rle_trans with (1 := Hw). nra. }
  (* assemble *)
  assert (HYp : 0 < Y) by lra. assert (Heta0 : 0 < etaA) by (unfold etaA; lra).
  assert (Hfin : phi1 - Y = (Ph - w) + (r + w - Y) + g5) by (rewrite Hphi; ring).
  assert (Hcub' : Rabs (r + w - Y) <= Rabs w * Rabs w * Rabs w / 3).
  { replace (r + w - Y) with (- (Y - r - w)) by ring. rewrite Rabs_Ropp. exact Hcub. }
  assert (Hw3 : Rabs w * Rabs w * Rabs w / 3 <= (1.0001 * etaA * Y) * (1.0001 * etaA * Y) * (1.0001 * etaA * Y) / 3).
  { assert (Hwy : Rabs w <= 1.0001 * etaA * Y) by nra.
    assert (0 <= Rabs w) by apply Rabs_pos.
    assert (0 <= 1.0001 * etaA * Y) by nra.
    apply Rmult_le_compat_r; [lra | ]. apply Rmult_le_compat; [nra | assumption | | ]; try nra. }
  rewrite Hfin.
  apply Rle_trans with (Rabs ((Ph - w) + (r + w - Y)) + Rabs g5); [apply Rabs_triang | ].
  assert (Rabs ((Ph - w) + (r + w - Y)) <= Rabs (Ph - w) + Rabs (r + w - Y)) by apply Rabs_triang.
  assert (Hc3 : (1.0001 * etaA * Y) * (1.0001 * etaA * Y) * (1.0001 * etaA * Y) / 3 <= (1.0001 * etaA) * (1.0001 * etaA) * (1.0001 * etaA) / 3 * 0.6169 * Y).
  { assert (Y * Y <= 0.6169) by nra.
    assert (Y * Y * Y <= 0.6169 * Y) by nra.
    assert (HK0 : 0 < 1.0001 * etaA) by lra.
    assert (Hcube : forall k, 0 < k -> 0 <= k * k * k / 3) by (intros k Hk; assert (0 < k * k) by nra; assert (0 < k * k * k) by nra; lra).
    pose proof (Hcube _ HK0).
    nra. }
  assert (Hnum : 7.7 * tauA / 0.5 + (1.0001 * etaA) * (1.0001 * etaA) * (1.0001 * etaA) / 3 * 0.6169 + tauA <= bndN)
    by (unfold tauA, etaA, bndN; interval with (i_prec 300)).
  assert (Htt : 7.7 * tauA * t <= 7.7 * tauA / 0.5 * Y) by (assert (t <= Y / 0.5) by lra; nra).
  assert (Hmul : (7.7 * tauA / 0.5 + (1.0001 * etaA) * (1.0001 * etaA) * (1.0001 * etaA) / 3 * 0.6169 + tauA) * Y <= bndN * Y)
    by (apply Rmult_le_compat_r; [lra | exact Hnum]).
  assert (Hc3' : (1.0001 * etaA * Y) * (1.0001 * etaA * Y) * (1.0001 * etaA * Y) / 3 <= (1.0001 * etaA) * (1.0001 * etaA) * (1.0001 * etaA) / 3 * 0.6169 * Y).
  { exact Hc3. }
  assert (Hg5' : Rabs g5 <= tauA * Y) by exact Hg5.
  assert (Hlast : Rabs (Ph - w) + Rabs (r + w - Y) + Rabs g5 <= bndN * Y).
  { apply Rle_trans with (7.7 * tauA * t + (1.0001 * etaA * Y) * (1.0001 * etaA * Y) * (1.0001 * etaA * Y) / 3 + tauA * Y).
    - apply Rplus_le_compat; [apply Rplus_le_compat | exact Hg5']; [exact HPw | apply Rle_trans with (1 := Hcub'); exact Hw3].
    - apply Rle_trans with ((7.7 * tauA / 0.5 + (1.0001 * etaA) * (1.0001 * etaA) * (1.0001 * etaA) / 3 * 0.6169 + tauA) * Y); [ | exact Hmul].
      nra. }
  lra.
Qed.
