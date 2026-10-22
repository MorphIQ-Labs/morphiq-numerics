(** The midpoints between consecutive binary64 numbers, as odd multiples of a power of two, and
    how a quotient of two binary64 values stands to them: it is one, or it is relatively far from
    every one. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 Grid RoundingGaps.
From Interval Require Import Tactic.
Require Import Ln1pLemmas AsinTables AsinKernel.
Open Scope R_scope.

Lemma izr_pow2 (k : Z) : (0 <= k)%Z -> IZR (2 ^ k) = bpow radix2 k.
Proof. intros H. apply (IZR_Zpower radix2). exact H. Qed.

(** An odd multiple of a power of two determines both. *)
Lemma odd_unique o1 o2 e1 e2 : Z.odd o1 = true -> Z.odd o2 = true -> (0 < o1)%Z -> (0 < o2)%Z ->
  IZR o1 * bpow radix2 e1 = IZR o2 * bpow radix2 e2 -> e1 = e2 /\ o1 = o2.
Proof.
  intros O1 O2 P1 P2 H.
  assert (Key : forall a b ea eb, Z.odd a = true -> (0 < a)%Z -> (0 < b)%Z -> (ea <= eb)%Z ->
    IZR a * bpow radix2 ea = IZR b * bpow radix2 eb -> ea = eb /\ a = b).
  { intros a b ea eb Oa Pa Pb Hle E.
    assert (E2 : IZR a = IZR (b * 2 ^ (eb - ea))).
    { rewrite mult_IZR, izr_pow2 by lia.
      assert (Hp : bpow radix2 eb = bpow radix2 (eb - ea) * bpow radix2 ea) by (rewrite <- bpow_plus; f_equal; ring).
      rewrite Hp in E. pose proof (bpow_gt_0 radix2 ea). nra. }
    apply eq_IZR in E2.
    destruct (Z.eq_dec ea eb) as [Eq | Ne].
    - split; [exact Eq | ]. replace (eb - ea)%Z with 0%Z in E2 by lia. rewrite Z.pow_0_r in E2. lia.
    - exfalso. assert (Hk : (0 < eb - ea)%Z) by lia.
      assert (Ev : Z.Even a).
      { exists (b * 2 ^ (eb - ea - 1))%Z.
        assert (Hk2 : (eb - ea = Z.succ (eb - ea - 1))%Z) by lia. rewrite Hk2 in E2.
        rewrite Z.pow_succ_r in E2 by lia. rewrite E2. ring. }
      apply Z.even_spec in Ev. rewrite <- Z.negb_odd, Oa in Ev. discriminate Ev. }
  destruct (Z_le_dec e1 e2) as [L | L].
  - exact (Key o1 o2 e1 e2 O1 P1 P2 L H).
  - destruct (Key o2 o1 e2 e1 O2 P2 P1 ltac:(lia) (eq_sym H)) as [A B]. split; symmetry; assumption.
Qed.

(** The midpoint above a nonnegative binary64 number [u], as [(2 mu + 1) 2^c] with [u = mu 2^(c+1)]. *)
Lemma midpoint_form u : fmtF u -> 0 <= u ->
  exists mu c, (0 <= mu < 2 ^ 53)%Z /\ (-1075 <= c)%Z /\ u = IZR mu * bpow radix2 (c + 1) /\
    (u + succ radix2 fexp64 u) / 2 = IZR (2 * mu + 1) * bpow radix2 c /\
    (bpow radix2 (-1022) <= u -> (2 ^ 52 <= mu)%Z) /\ (u < bpow radix2 (-1022) -> c = (-1075)%Z).
Proof.
  intros Fu U0. destruct (Req_dec u 0) as [Z0 | NZ].
  - subst u. exists 0%Z, (-1075)%Z. repeat split; try lia.
    + simpl. ring.
    + rewrite succ_0, ulp_FLT_0 by exact _.
      assert (E : bpow radix2 (-1074) = 2 * bpow radix2 (-1075)) by (replace (-1074)%Z with (-1075 + 1)%Z by reflexivity; rewrite bpow_plus; change (bpow radix2 1) with 2; ring).
      replace (IZR (2 * 0 + 1)) with 1 by (simpl; ring). rewrite E. field.
    + intros H. exfalso. pose proof (bpow_gt_0 radix2 (-1022)). lra.
  - assert (Pu : 0 < u) by lra.
    set (c := (cexp radix2 fexp64 u - 1)%Z).
    pose proof (grid_fmt _ _ Fu) as [mu Hmu].
    assert (Hcmax : cexp radix2 fexp64 u = Z.max (mag radix2 u - 53) (-1074)) by reflexivity.
    assert (Hc : (-1075 <= c)%Z) by (unfold c; rewrite Hcmax; pose proof (Z.le_max_r (mag radix2 u - 53) (-1074)); lia).
    assert (Hcc : cexp radix2 fexp64 u = (c + 1)%Z) by (unfold c; ring).
    assert (Hu : u = IZR mu * bpow radix2 (c + 1)) by (rewrite <- Hcc; exact Hmu).
    pose proof (bpow_mag_gt radix2 u) as Hm. rewrite Rabs_pos_eq in Hm by lra.
    pose proof (bpow_mag_le radix2 u ltac:(lra)) as Hge. rewrite Rabs_pos_eq in Hge by lra.
    assert (Hcx : (mag radix2 u <= c + 1 + 53)%Z) by (rewrite Hcc in Hcmax; pose proof (Z.le_max_l (mag radix2 u - 53) (-1074)); lia).
    assert (Hp0 : 0 < bpow radix2 (c + 1)) by apply bpow_gt_0.
    assert (Hmu0 : 0 < IZR mu) by (destruct (Rlt_le_dec 0 (IZR mu)) as [H | H]; [exact H | exfalso; nra]).
    assert (Hmulo : (0 <= mu)%Z) by (apply le_IZR; lra).
    assert (Hmuhi : (mu < 2 ^ 53)%Z).
    { apply lt_IZR. rewrite izr_pow2 by lia.
      assert (Hb : bpow radix2 (mag radix2 u) <= bpow radix2 53 * bpow radix2 (c + 1)) by (rewrite <- bpow_plus; apply bpow_le; lia).
      apply (Rmult_lt_reg_r (bpow radix2 (c + 1))); [exact Hp0 | ]. rewrite <- Hu. lra. }
    exists mu, c. refine (conj (conj Hmulo Hmuhi) (conj Hc (conj Hu (conj _ (conj _ _))))).
    + rewrite succ_eq_pos by lra. rewrite ulp_neq_0 by lra.
      assert (Hcc2 : bpow radix2 (cexp radix2 fexp64 u) = bpow radix2 (c + 1)) by (rewrite Hcc; reflexivity).
      change (cexp radix2 (FLT_exp (-1074) 53) u) with (cexp radix2 fexp64 u). rewrite Hcc2.
      assert (Hc1 : bpow radix2 (c + 1) = 2 * bpow radix2 c) by (rewrite bpow_plus; change (bpow radix2 1) with 2; ring).
      assert (Hu' : u = IZR mu * (2 * bpow radix2 c)) by (rewrite Hu, Hc1; reflexivity).
      rewrite Hc1. rewrite plus_IZR, mult_IZR. simpl IZR. rewrite Hu'. field.
    + intros H.
      assert (Hmag : (-1021 <= mag radix2 u)%Z).
      { apply mag_ge_bpow. replace (-1021 - 1)%Z with (-1022)%Z by ring. rewrite Rabs_pos_eq by lra. exact H. }
      assert (Hce : (c + 1 = mag radix2 u - 53)%Z) by (rewrite Hcc in Hcmax; rewrite Hcmax; apply Z.max_l; lia).
      apply le_IZR. rewrite izr_pow2 by lia.
      assert (Hl : bpow radix2 (mag radix2 u - 1) <= IZR mu * bpow radix2 (c + 1)) by (rewrite <- Hu; exact Hge).
      assert (E : bpow radix2 (mag radix2 u - 1) = bpow radix2 52 * bpow radix2 (c + 1)) by (rewrite <- bpow_plus; f_equal; lia).
      rewrite E in Hl. apply (Rmult_le_reg_r (bpow radix2 (c + 1))); [exact Hp0 | exact Hl].
    + intros H.
      assert (Hmag : (mag radix2 u <= -1022)%Z).
      { apply mag_le_bpow; [lra | ]. rewrite Rabs_pos_eq by lra. exact H. }
      unfold c. rewrite Hcmax. rewrite Z.max_r by lia. reflexivity.
Qed.

(** The quotient of two positive binary64 numbers is a midpoint, or relatively far from it. *)
Theorem gap_rel nv dv mn en md ed mu c :
  0 < nv -> 0 < dv -> Z.odd mn = true -> (0 < mn < 2 ^ 53)%Z -> nv = IZR mn * bpow radix2 en ->
  (0 < md < 2 ^ 53)%Z -> dv = IZR md * bpow radix2 ed ->
  (0 <= mu < 2 ^ 53)%Z -> 
  nv / dv = IZR (2 * mu + 1) * bpow radix2 c \/
  nv / dv * bpow radix2 (-108) <= Rabs (nv / dv - IZR (2 * mu + 1) * bpow radix2 c).
Proof.
  intros Pn Pd Omn [Hmn0 Hmn1] Hn [Hmd0 Hmd1] Hd [Hmu0 Hmu1].
  set (mid := IZR (2 * mu + 1) * bpow radix2 c).
  set (t := nv / dv).
  assert (Hd0 : dv <> 0) by lra.
  destruct (Req_dec (nv - mid * dv) 0) as [Z0 | NZ].
  - left. unfold t. apply (Rmult_eq_reg_r dv); [ | exact Hd0]. field_simplify; [ | exact Hd0]. lra.
  - right.
    assert (Gn : on_grid en nv) by (exists mn; exact Hn).
    assert (Gm : on_grid (c + ed) (mid * dv)).
    { exists ((2 * mu + 1) * md)%Z. unfold mid. rewrite Hd, mult_IZR, bpow_plus. ring. }
    assert (Gx : on_grid (Z.min en (c + ed)) (nv - mid * dv)).
    { apply grid_minus; [apply (grid_le en); [apply Z.le_min_l | exact Gn] | apply (grid_le (c + ed)); [apply Z.le_min_r | exact Gm]]. }
    pose proof (grid_nonzero _ _ Gx NZ) as Hx.
    assert (Hdiff : nv / dv - mid = (nv - mid * dv) / dv) by (field; exact Hd0).
    assert (Habs : bpow radix2 (Z.min en (c + ed)) / dv <= Rabs (t - mid)).
    { unfold t. rewrite Hdiff. unfold Rdiv. rewrite Rabs_mult, Rabs_Rinv by exact Hd0. rewrite (Rabs_pos_eq dv) by lra.
      apply Rmult_le_compat_r; [apply Rlt_le, Rinv_0_lt_compat; lra | exact Hx]. }
    assert (Hn53 : nv < bpow radix2 53 * bpow radix2 en).
    { rewrite Hn. apply Rmult_lt_compat_r; [apply bpow_gt_0 | ]. rewrite <- izr_pow2 by lia. apply IZR_lt. lia. }
    assert (Hd53 : dv < bpow radix2 53 * bpow radix2 ed).
    { rewrite Hd. apply Rmult_lt_compat_r; [apply bpow_gt_0 | ]. rewrite <- izr_pow2 by lia. apply IZR_lt. lia. }
    assert (Hm54 : mid < bpow radix2 54 * bpow radix2 c).
    { unfold mid. apply Rmult_lt_compat_r; [apply bpow_gt_0 | ]. rewrite <- izr_pow2 by lia. apply IZR_lt. lia. }
    assert (Hbp : bpow radix2 (-108) <= bpow radix2 (-53) /\ bpow radix2 (-108) <= bpow radix2 (-107) /\ bpow radix2 (-53) * bpow radix2 53 = 1).
    { split; [apply bpow_le; lia | split; [apply bpow_le; lia | rewrite <- bpow_plus; reflexivity]]. }
    destruct Hbp as [B1 [B2 B3]].
    destruct (Z.le_ge_cases en (c + ed)) as [Hle | Hge].
    + rewrite Z.min_l in Habs by lia.
      (* 2^en > nv 2^-53 *)
      assert (Hq : t * bpow radix2 (-53) <= bpow radix2 en / dv).
      { assert (H1 : nv * bpow radix2 (-53) <= bpow radix2 en).
        { apply (Rmult_le_reg_r (bpow radix2 53)); [apply bpow_gt_0 | ]. rewrite Rmult_assoc, B3. lra. }
        unfold t. replace (nv / dv * bpow radix2 (-53)) with ((nv * bpow radix2 (-53)) / dv) by (field; exact Hd0).
        unfold Rdiv. apply Rmult_le_compat_r; [left; apply Rinv_0_lt_compat; lra | exact H1]. }
      assert (Ht : t * bpow radix2 (-108) <= t * bpow radix2 (-53)).
      { assert (0 < t) by (unfold t; apply Rdiv_lt_0_compat; lra). apply Rmult_le_compat_l; lra. }
      lra.
    + rewrite Z.min_r in Habs by lia.
      assert (Hb54 : bpow radix2 (-54) * bpow radix2 54 = 1) by (rewrite <- bpow_plus; reflexivity).
      assert (Hg : mid * dv * bpow radix2 (-107) <= bpow radix2 (c + ed)).
      { rewrite bpow_plus.
        assert (E1 : bpow radix2 (-54) * mid <= bpow radix2 c).
        { apply (Rmult_le_reg_l (bpow radix2 54)); [apply bpow_gt_0 | ]. rewrite <- Rmult_assoc, (Rmult_comm (bpow radix2 54)), Hb54. lra. }
        assert (E2 : bpow radix2 (-53) * dv <= bpow radix2 ed).
        { apply (Rmult_le_reg_l (bpow radix2 53)); [apply bpow_gt_0 | ]. rewrite <- Rmult_assoc, (Rmult_comm (bpow radix2 53)), B3. lra. }
        assert (Hp : bpow radix2 (-107) = bpow radix2 (-54) * bpow radix2 (-53)) by (rewrite <- bpow_plus; reflexivity).
        pose proof (bpow_ge_0 radix2 (-54)). pose proof (bpow_ge_0 radix2 (-53)). pose proof (bpow_gt_0 radix2 c). pose proof (bpow_gt_0 radix2 ed).
        assert (0 < mid) by (unfold mid; apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0]).
        rewrite Hp. replace (mid * dv * (bpow radix2 (-54) * bpow radix2 (-53))) with ((bpow radix2 (-54) * mid) * (bpow radix2 (-53) * dv)) by ring.
        apply Rmult_le_compat; [apply Rmult_le_pos; lra | apply Rmult_le_pos; lra | exact E1 | exact E2]. }
      assert (Hq : mid * bpow radix2 (-107) <= Rabs (t - mid)).
      { apply Rle_trans with (bpow radix2 (c + ed) / dv); [ | exact Habs].
        apply (Rmult_le_reg_r dv); [lra | ]. replace (bpow radix2 (c + ed) / dv * dv) with (bpow radix2 (c + ed)) by (field; exact Hd0). nra. }
      assert (Pm : 0 < mid) by (unfold mid; apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0]).
      assert (Pt : 0 < t) by (unfold t; apply Rdiv_lt_0_compat; lra).
      destruct (Rle_dec t (2 * mid)) as [Hle2 | Hgt2].
      * assert (t * bpow radix2 (-108) <= 2 * mid * bpow radix2 (-108)) by (apply Rmult_le_compat_r; [apply bpow_ge_0 | exact Hle2]).
        assert (2 * mid * bpow radix2 (-108) <= mid * bpow radix2 (-107)).
        { replace (bpow radix2 (-107)) with (2 * bpow radix2 (-108)) by (replace (-107)%Z with (-108 + 1)%Z by reflexivity; rewrite bpow_plus; change (bpow radix2 1) with 2; ring). lra. }
        lra.
      * assert (Hh : t / 2 <= Rabs (t - mid)).
        { apply Rle_trans with (t - mid); [lra | apply Rle_abs]. }
        assert (t * bpow radix2 (-108) <= t / 2).
        { assert (bpow radix2 (-108) <= / 2) by (apply Rle_trans with (bpow radix2 (-1)); [apply bpow_le; lia | change (bpow radix2 (-1)) with (/ 2); lra]). nra. }
        lra.
Qed.
