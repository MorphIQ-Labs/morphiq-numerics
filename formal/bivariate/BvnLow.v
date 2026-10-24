(** One node of the low-correlation rule, from the stored abscissa and weight
    to the term added to the sum. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
Require Import BvnRound BvnQ BvnArg BvnNode BvnTrig.
Open Scope R_scope.

(** The node angle as the Rust forms it: [asr * (sign * x + 1) / 2]. *)
Definition angle (asr sgn xh : R) : R := rndF (rndF (asr * rndF (sgn * xh + 1)) / 2).

Lemma angle_err asr sgn xs xh tau :
  bpow radix2 (-53) <= Rabs asr -> Rabs asr <= 6 / 5 ->
  (sgn = 1 \/ sgn = -1) -> 0 < xs < 1 -> tau = (sgn * xs + 1) / 2 ->
  / 4096 <= tau -> tau <= 1 -> xh = rndF xs ->
  Rabs (angle asr sgn xh - asr * tau) <= u * Rabs asr * (tau + 76 / 100).
Proof.
  intros Ha1 Ha2 Hsg [Hx0 Hx1] Htau Htl Hth Hxh.
  pose proof u_pos as Hu. pose proof u_val as Huv. pose proof z_pos as Hz.
  assert (Hxe : Rabs (xh - xs) <= bpow radix2 (-54)).
  { rewrite Hxh. replace (-54)%Z with (0 - 54)%Z by reflexivity. apply rnd_pow; [lia |].
    rewrite Rabs_pos_eq by lra. replace (bpow radix2 0) with 1 by reflexivity. lra. }
  set (v1 := sgn * xh + 1).
  assert (Hxh0 : 0 <= xh <= 1).
  { rewrite Hxh. split.
    - rewrite <- (round_0 radix2 (FLT_exp (-1074) 53) (Znearest (fun n => negb (Z.even n)))).
      apply round_le; [auto with typeclass_instances | auto with typeclass_instances | lra].
    - assert (Hr : Rabs (rndF xs) <= bpow radix2 0) by (apply rnd_abs_le_pow; [lia | rewrite Rabs_pos_eq by lra; replace (bpow radix2 0) with 1 by reflexivity; lra]).
      replace (bpow radix2 0) with 1 in Hr by reflexivity. apply Rabs_le_inv in Hr. lra. }
  assert (Hv1 : Rabs v1 <= bpow radix2 1).
  { replace (bpow radix2 1) with 2 by reflexivity. unfold v1. destruct Hsg as [H | H]; rewrite H; apply Rabs_le; split; lra. }
  assert (Hp : Rabs (rndF v1 - v1) <= bpow radix2 (-53)).
  { replace (-53)%Z with (1 - 54)%Z by reflexivity. apply rnd_pow; [lia | exact Hv1]. }
  set (p := rndF v1) in *.
  set (pstar := sgn * xs + 1).
  assert (Hpstar : pstar = 2 * tau) by (unfold pstar; rewrite Htau; field).
  assert (Hv1e : Rabs (v1 - pstar) <= bpow radix2 (-54)).
  { assert (E : v1 - pstar = sgn * (xh - xs)) by (unfold v1, pstar; ring).
    rewrite E, Rabs_mult. assert (Rabs sgn = 1) by (destruct Hsg as [H | H]; rewrite H; unfold Rabs; destruct (Rcase_abs _); lra).
    rewrite H. lra. }
  assert (Hb53 : bpow radix2 (-53) = u) by reflexivity.
  assert (Hb54 : bpow radix2 (-54) = u / 2).
  { unfold u. replace (-54)%Z with (-53 + -1)%Z by reflexivity. rewrite bpow_plus. change (bpow radix2 (-1)) with (/ 2). field. }
  assert (Hpp : Rabs (p - pstar) <= 3 / 2 * u).
  { assert (E : p - pstar = (p - v1) + (v1 - pstar)) by ring. rewrite E.
    eapply Rle_trans; [apply Rabs_triang |]. rewrite Hb53 in Hp. rewrite Hb54 in Hv1e. lra. }
  apply Rabs_le_inv in Hpp. destruct Hpp as [Hpp1 Hpp2].
  assert (Hppos : 0 < p) by (rewrite Huv in *; nra).
  set (q := rndF (asr * p)).
  assert (Hq : Rabs (q - asr * p) <= u * Rabs (asr * p) + z) by apply rnd_rel_z.
  assert (Hasrp : Rabs (asr * p) = Rabs asr * p) by (rewrite Rabs_mult, (Rabs_pos_eq p); [reflexivity | lra]).
  assert (Hqn : bpow radix2 (-1021) <= Rabs q).
  { assert (Hlow : Rabs asr * p <= Rabs (asr * p)) by lra.
    assert (Hrq : Rabs (asr * p) <= Rabs q + Rabs (q - asr * p)).
    { assert (E : asr * p = q + (asr * p - q)) by ring. rewrite E at 1. eapply Rle_trans; [apply Rabs_triang |].
      rewrite Rabs_minus_sym. lra. }
    assert (Hm : bpow radix2 (-53) * (1 / 4096) <= Rabs asr * p).
    { apply Rmult_le_compat; [apply bpow_ge_0 | lra | exact Ha1 | rewrite Huv in *; lra]. }
    assert (Hu1 : u * Rabs (asr * p) <= u * (Rabs asr * 3)) by (apply Rmult_le_compat_l; [lra | rewrite Hasrp; nra]).
    assert (Hb : bpow radix2 (-1021) <= bpow radix2 (-53) * (1 / 4096) / 2).
    { assert (E : bpow radix2 (-66) = bpow radix2 (-53) * (1 / 4096) / 2).
      { replace (-66)%Z with (-53 + -13)%Z by reflexivity. rewrite bpow_plus.
        change (bpow radix2 (-13)) with (/ 8192). field. }
      rewrite <- E. apply bpow_le. lia. }
    assert (Hz1 : z <= bpow radix2 (-53) * (1 / 4096) / 4).
    { assert (E : bpow radix2 (-67) = bpow radix2 (-53) * (1 / 4096) / 4).
      { replace (-67)%Z with (-53 + -14)%Z by reflexivity. rewrite bpow_plus.
        change (bpow radix2 (-14)) with (/ 16384). field. }
      rewrite <- E. unfold z. apply bpow_le. lia. }
    nra. }
  assert (Hth' : angle asr sgn xh = q / 2).
  { unfold angle. fold p. fold q. apply rnd_half; [apply fmtF_rnd | exact Hqn]. }
  rewrite Hth'.
  assert (E : q / 2 - asr * tau = (q - asr * pstar) / 2) by (rewrite Hpstar; field).
  rewrite E.
  assert (E2 : q - asr * pstar = (q - asr * p) + asr * (p - pstar)) by ring.
  rewrite E2.
  assert (Hb : Rabs ((q - asr * p) + asr * (p - pstar)) <= u * Rabs asr * (p + 3 / 2) + z).
  { eapply Rle_trans; [apply Rabs_triang |]. rewrite Rabs_mult.
    assert (Hm : Rabs asr * Rabs (p - pstar) <= Rabs asr * (3 / 2 * u)) by (apply Rmult_le_compat_l; [apply Rabs_pos | apply Rabs_le; lra]).
    rewrite Hasrp in Hq. nra. }
  unfold Rdiv. rewrite Rabs_mult. rewrite (Rabs_pos_eq (/ 2)) by lra.
  assert (Hpbound : p <= 2 * tau + 3 / 2 * u) by lra.
  assert (Hzs : z <= u * Rabs asr * (1 / 100)).
  { assert (u * Rabs asr * (1 / 100) >= bpow radix2 (-53) * bpow radix2 (-53) * (1 / 100)).
    { rewrite Hb53. apply Rmult_ge_compat_r; [lra |]. apply Rmult_ge_compat_l; lra. }
    assert (bpow radix2 (-53) * bpow radix2 (-53) * (1 / 100) >= bpow radix2 (-120)).
    { rewrite <- bpow_plus. replace (1 / 100) with (/ 100) by field.
      assert (bpow radix2 (-106) * / 100 >= bpow radix2 (-120)).
      { assert (bpow radix2 (-120) * 100 <= bpow radix2 (-106)).
        { replace (-106)%Z with (-120 + 14)%Z by reflexivity. rewrite bpow_plus. replace (bpow radix2 14) with 16384 by reflexivity.
          pose proof (bpow_gt_0 radix2 (-120)). nra. }
        pose proof (bpow_gt_0 radix2 (-120)). nra. }
      simpl. lra. }
    assert (z <= bpow radix2 (-120)) by (unfold z; apply bpow_le; lia).
    lra. }
  assert (Hfin : u * Rabs asr * (p + 3 / 2) + z <= 2 * (u * Rabs asr * (tau + 76 / 100))).
  { assert (Hua : 0 <= u * Rabs asr) by (apply Rmult_le_pos; [lra | apply Rabs_pos]).
    assert (u * Rabs asr * (p + 3 / 2) <= u * Rabs asr * (2 * tau + 3 / 2 + 3 / 2 * u)) by (apply Rmult_le_compat_l; lra).
    assert (u * Rabs asr * (3 / 2 * u) <= u * Rabs asr * (1 / 100)) by (apply Rmult_le_compat_l; [lra | rewrite Huv; lra]).
    nra. }
  nra.
Qed.


Definition node_term (expI sinI : R -> R) (x y asr sgn xh wh : R) : R :=
  termf expI x y (sinI (angle asr sgn xh)) wh.

(** The contracts of the library functions the node uses, in the weakest form
    their documents prove. *)
Definition exp_contract (expI : R -> R) : Prop :=
  forall v, exists Zc, expI v = rndF Zc /\ Rabs (Zc - exp v) <= bpow radix2 (-100) * exp v.

Definition sin_contract (sinI : R -> R) : Prop :=
  (forall th, fmtF (sinI th)) /\
  forall th k, Rabs th <= 3 / 2 -> (-1021 <= k)%Z -> Rabs (sin th) <= bpow radix2 k ->
    Rabs (sinI th - sin th) <= (1 + bpow radix2 (-100)) * bpow radix2 (k - 54).

Lemma node_full expI sinI x y asr sgn xs xh W wh A tauhi taulo k ew :
  exp_contract expI -> sin_contract sinI ->
  fmtF x -> fmtF y -> Rabs x <= 64 -> Rabs y <= 64 ->
  bpow radix2 (-53) <= Rabs asr -> Rabs asr <= A -> A <= 6 / 5 ->
  (sgn = 1 \/ sgn = -1) -> 0 < xs < 1 ->
  taulo <= (sgn * xs + 1) / 2 -> (sgn * xs + 1) / 2 <= tauhi -> / 4096 <= taulo -> tauhi <= 1 ->
  xh = rndF xs ->
  (-1021 <= k)%Z -> (k <= 0)%Z ->
  sin (A * tauhi + u * A * (tauhi + 76 / 100)) <= bpow radix2 k ->
  (let sg := sin (A * tauhi + u * A * (tauhi + 76 / 100)) in
   sg + (1 + bpow radix2 (-100)) * bpow radix2 (k - 54) <= 99 / 100) ->
  Rabs (wh - W) <= ew * Rabs W -> 0 <= ew -> Rabs wh <= 1 ->
  let tau := (sgn * xs + 1) / 2 in
  let dth := u * A * (tauhi + 76 / 100) in
  let sg := sin (A * tauhi + dth) in
  let hs_ := (1 + bpow radix2 (-100)) * bpow radix2 (k - 54) in
  let eps1 := (dth + hs_) / (1 - (sg + hs_)) in
  let theta := eps1 + (1 + eps1) * (71 / 10 * u) in
  let t := asr * tau in
  let r := x * x + y * y in
  let p := x * y in
  Rabs (node_term expI sinI x y asr sgn xh wh - W * exp (- Qf r p (sin t)))
    <= Rabs W * exp (- Qf r p (sin t)) * ((1 + ew) * (1 + rx) * exp (theta * Qf r p (sin t) + 300 * z) - 1) + 3 * z.
Proof.
  intros Hexp [Hsfmt Hsin] Fx Fy Hx Hy Ha1 Ha2 HA Hsg Hxs Htl Hth Htaulo Htauhi Hxh Hk1 Hk2 Hsgk Hsgs HwW Hew Hwh tau dth sg hs_ eps1 theta t r p.
  pose proof u_pos as Hu. pose proof u_val as Huv. pose proof z_pos as Hz.
  destruct Hxs as [Hxs0 Hxs1].
  assert (Htl' : taulo <= tau) by exact Htl.
  assert (Hth' : tau <= tauhi) by exact Hth.
  assert (Htau1 : / 4096 <= tau) by lra.
  assert (Htau2 : tau <= 1) by lra.
  pose proof (angle_err asr sgn xs xh tau Ha1 ltac:(lra) Hsg (conj Hxs0 Hxs1) eq_refl Htau1 Htau2 Hxh) as Hang.
  set (th := angle asr sgn xh) in *.
  assert (Hdth : Rabs (th - t) <= dth).
  { eapply Rle_trans; [exact Hang |]. unfold dth.
    assert (Hm1 : Rabs asr * (tau + 76 / 100) <= A * (tauhi + 76 / 100)).
    { apply Rmult_le_compat; [apply Rabs_pos | lra | exact Ha2 | lra]. }
    pose proof (Rabs_pos asr). nra. }
  assert (HtA : Rabs t <= A * tauhi).
  { unfold t. rewrite Rabs_mult, (Rabs_pos_eq tau) by lra.
    apply Rmult_le_compat; [apply Rabs_pos | lra | exact Ha2 | lra]. }
  assert (HA0 : 0 <= A) by (pose proof (Rabs_pos asr); lra).
  assert (Hdth0 : 0 <= dth) by (unfold dth; apply Rmult_le_pos; [nra | lra]).
  assert (HAt : A * tauhi <= 6 / 5) by nra.
  assert (Hdthsmall : dth <= / 1000) by (unfold dth; rewrite Huv; nra).
  assert (Hth3 : Rabs th <= A * tauhi + dth).
  { assert (E : th = t + (th - t)) by ring.
    assert (Rabs th <= Rabs t + Rabs (th - t)) by (rewrite E at 1; apply Rabs_triang). lra. }
  assert (Hsin_abs : Rabs (sin t) < 1) by (apply sin_abs_lt_1; lra).
  assert (Hsgb : Rabs (sin th) <= sg).
  { unfold sg. rewrite abs_sin_eq by lra. apply sin_mono_pos; [apply Rabs_pos | exact Hth3 | lra]. }
  assert (Hsg0 : 0 <= sg) by (pose proof (Rabs_pos (sin th)); lra).
  assert (Hshe : Rabs (sinI th - sin th) <= hs_).
  { unfold hs_. apply Hsin; [lra | exact Hk1 | eapply Rle_trans; [exact Hsgb | exact Hsgk]]. }
  assert (Hhs0 : 0 <= hs_) by (unfold hs_; apply Rmult_le_pos; [pose proof (bpow_gt_0 radix2 (-100)); lra | apply bpow_ge_0]).
  assert (Hsgs' : sg + hs_ <= 99 / 100) by exact Hsgs.
  exact (node_err expI x y t th (sinI th) W wh dth sg hs_ ew Hexp Fx Fy (Hsfmt th) Hx Hy Hdth Hsin_abs Hsgb Hshe Hsgs' Hhs0 Hdth0 HwW Hew Hwh Hsg0).
Qed.
