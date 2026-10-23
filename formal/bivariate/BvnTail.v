(** The last stage of the low-correlation branch: the constant
    [asr / (2 TAU)], the product of the two normal distribution functions, the
    final sum and the clamp. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
Require Import BvnRound BvnQ.
Open Scope R_scope.

(** Rust's [TAU] (binary64, [0x401921FB54442D18]). *)
Definition TAU : R := 884279719003555 / 140737488355328.

Lemma TAU_close : Rabs (TAU - 2 * PI) <= 25 / 10 ^ 17.
Proof. unfold TAU. apply Rabs_le. split; interval with (i_prec 80). Qed.

Definition ETAK : R := 17 / 10 ^ 17.

(** [asr / (2 TAU)] rounded, against [asr / (4 pi)], relative [ETAK]. *)
Lemma K_close asr : bpow radix2 (-53) <= Rabs asr -> Rabs asr <= 6 / 5 ->
  Rabs (rndF (asr / (2 * TAU)) - asr / (4 * PI)) <= ETAK * Rabs (asr / (4 * PI)).
Proof.
  intros H1 H2.
  pose proof u_pos as Hu. pose proof u_val as Huv. pose proof z_pos as Hz.
  pose proof TAU_close as Ht. apply Rabs_le_inv in Ht. destruct Ht as [Ht1 Ht2].
  assert (HT : 6 < TAU < 7) by (unfold TAU; split; interval).
  assert (HPI : 3 < PI < 315 / 100) by (pose proof PI_RGT_0; split; interval).
  destruct HT as [HT1 HT2]. destruct HPI as [HPI1 HPI2].
  pose proof (rnd_rel_z (asr / (2 * TAU))) as Hr.
  set (v := asr / (2 * TAU)) in *.
  set (Kex := asr / (4 * PI)) in *.
  assert (Hvk : Rabs (v - Kex) <= 42 / 10 ^ 18 * Rabs Kex).
  { assert (E : v - Kex = Kex * (2 * PI / TAU - 1)).
    { unfold v, Kex. field. split; lra. }
    rewrite E, Rabs_mult.
    assert (Hf : Rabs (2 * PI / TAU - 1) <= 42 / 10 ^ 18).
    { assert (E2 : 2 * PI / TAU - 1 = (2 * PI - TAU) / TAU) by (field; lra).
      rewrite E2. rewrite Rabs_div_pos by lra. rewrite (Rabs_minus_sym (2 * PI) TAU).
      apply (Rle_trans _ (25 / 10 ^ 17 / TAU)).
      - unfold Rdiv. apply Rmult_le_compat_r; [apply Rlt_le, Rinv_0_lt_compat; lra | apply Rabs_le; lra].
      - unfold Rdiv. assert (/ TAU <= / 6) by (apply Rinv_le_contravar; lra).
        assert (0 <= 25 / 10 ^ 17) by lra. nra. }
    pose proof (Rabs_pos Kex). nra. }
  assert (HKe : Rabs Kex >= bpow radix2 (-53) / 13).
  { unfold Kex. rewrite Rabs_div_pos by lra.
    apply Rle_ge. apply Rle_trans with (bpow radix2 (-53) / 13).
    - lra.
    - unfold Rdiv. apply Rmult_le_compat; [apply bpow_ge_0 | lra | exact H1 | apply Rinv_le_contravar; lra]. }
  assert (Hzs : z <= bpow radix2 (-53) / 13 * (1 / 10 ^ 17)).
  { assert (z <= bpow radix2 (-200)) by (unfold z; apply bpow_le; lia).
    assert (bpow radix2 (-200) <= bpow radix2 (-53) / 13 * (1 / 10 ^ 17)).
    { assert (bpow radix2 (-200) <= bpow radix2 (-120)) by (apply bpow_le; lia).
      assert (bpow radix2 (-120) <= bpow radix2 (-53) / 13 * (1 / 10 ^ 17)) by (simpl; interval).
      lra. }
    lra. }
  assert (Hv : Rabs v <= Rabs Kex * (1 + 42 / 10 ^ 18)).
  { assert (E : v = Kex + (v - Kex)) by ring. assert (Rabs v <= Rabs Kex + Rabs (v - Kex)) by (rewrite E at 1; apply Rabs_triang). lra. }
  assert (E3 : rndF v - Kex = (rndF v - v) + (v - Kex)) by ring.
  rewrite E3. eapply Rle_trans; [apply Rabs_triang |].
  assert (A1 : z <= Rabs Kex * (1 / 10 ^ 17)).
  { assert (Hm : bpow radix2 (-53) / 13 * (1 / 10 ^ 17) <= Rabs Kex * (1 / 10 ^ 17))
      by (apply Rmult_le_compat_r; [lra | lra]). lra. }
  assert (A2 : u * Rabs v <= u * (Rabs Kex * (1 + 42 / 10 ^ 18))) by (apply Rmult_le_compat_l; [lra | exact Hv]).
  pose proof (Rabs_pos Kex).
  unfold ETAK. rewrite Huv in A2, Hr.
  nra.
Qed.

Lemma rnd_mono a b : a <= b -> rndF a <= rndF b.
Proof. intros H. apply round_le; auto with typeclass_instances. Qed.

Lemma rnd_zero : rndF 0 = 0.
Proof. apply round_0; auto with typeclass_instances. Qed.

Lemma rnd_one : rndF 1 = 1.
Proof.
  replace 1 with (bpow radix2 0) by reflexivity.
  apply round_generic; [auto with typeclass_instances |].
  apply generic_format_bpow. unfold FLT_exp. apply Z.max_lub; lia.
Qed.

Lemma rnd_unit a : 0 <= a <= 1 -> 0 <= rndF a <= 1 /\ Rabs (rndF a - a) <= bpow radix2 (-54).
Proof.
  intros [H0 H1]. split.
  - split.
    + rewrite <- rnd_zero. apply rnd_mono. exact H0.
    + rewrite <- rnd_one. apply rnd_mono. exact H1.
  - replace (-54)%Z with (0 - 54)%Z by reflexivity. apply rnd_pow; [lia |].
    replace (bpow radix2 0) with 1 by reflexivity. rewrite Rabs_pos_eq by lra. exact H1.
Qed.

(** The product of the two rounded distribution functions, rounded. *)
Lemma phi_part a b ah bh : 0 <= a <= 1 -> 0 <= b <= 1 -> ah = rndF a -> bh = rndF b ->
  Rabs (rndF (ah * bh) - a * b) <= 3 * bpow radix2 (-54).
Proof.
  intros Ha Hb Eh Fh.
  destruct (rnd_unit a Ha) as [[A0 A1] Ae]. destruct (rnd_unit b Hb) as [[B0 B1] Be].
  rewrite <- Eh in A0, A1, Ae. rewrite <- Fh in B0, B1, Be.
  destruct (rnd_unit (ah * bh)) as [_ Pe]; [split; nra |].
  assert (Hp : Rabs (ah * bh - a * b) <= 2 * bpow radix2 (-54)).
  { assert (E : ah * bh - a * b = ah * (bh - b) + b * (ah - a)) by ring.
    rewrite E. eapply Rle_trans; [apply Rabs_triang |]. rewrite !Rabs_mult.
    rewrite (Rabs_pos_eq ah A0), (Rabs_pos_eq b (proj1 Hb)).
    assert (Hm1 : ah * Rabs (bh - b) <= 1 * bpow radix2 (-54)) by (apply Rmult_le_compat; [lra | apply Rabs_pos | lra | exact Be]).
    assert (Hm2 : b * Rabs (ah - a) <= 1 * bpow radix2 (-54)) by (apply Rmult_le_compat; [lra | apply Rabs_pos | lra | exact Ae]).
    lra. }
  assert (E : rndF (ah * bh) - a * b = (rndF (ah * bh) - ah * bh) + (ah * bh - a * b)) by ring.
  rewrite E. eapply Rle_trans; [apply Rabs_triang |]. lra.
Qed.

Definition clampf (v : R) : R := Rmin 1 (Rmax 0 v).

(** The final rounding and the clamp, for a true value in [[0, 1]]. *)
Lemma clamp_round s P : 0 <= P <= 1 ->
  Rabs (clampf (rndF s) - P) <= Rabs (s - P) + bpow radix2 (-54).
Proof.
  intros [HP0 HP1]. unfold clampf.
  pose proof (bpow_gt_0 radix2 (-54)) as Hb.
  destruct (Rle_dec s 0) as [Hs0 | Hs0].
  - assert (Hr : rndF s <= 0) by (rewrite <- rnd_zero; apply rnd_mono; exact Hs0).
    rewrite Rmax_left by exact Hr. rewrite Rmin_right by lra.
    assert (Rabs (0 - P) = P) by (replace (0 - P) with (- P) by ring; rewrite Rabs_Ropp; apply Rabs_pos_eq; lra).
    assert (Rabs (s - P) = P - s) by (rewrite Rabs_left1 by lra; ring).
    lra.
  - destruct (Rle_dec s 1) as [Hs1 | Hs1].
    + destruct (rnd_unit s) as [[R0 R1] Re]; [split; lra |].
      rewrite Rmax_right by exact R0. rewrite Rmin_right by exact R1.
      assert (E : rndF s - P = (rndF s - s) + (s - P)) by ring.
      rewrite E. eapply Rle_trans; [apply Rabs_triang |]. lra.
    + assert (Hr : 1 <= rndF s) by (rewrite <- rnd_one; apply rnd_mono; lra).
      rewrite Rmax_right by lra. rewrite Rmin_left by lra.
      assert (Rabs (1 - P) = 1 - P) by (rewrite Rabs_pos_eq by lra; reflexivity).
      assert (Rabs (s - P) = s - P) by (rewrite Rabs_pos_eq by lra; reflexivity).
      lra.
Qed.

(** The per-node weight [Kw = rndF (rndF W * Kh)] against [Kex W]. *)
Definition ew : R := (1 + u) * (1 + u) * (1 + ETAK) - 1.

Lemma kw_close W wh Kw Kh Kex :
  / 4096 <= W -> W <= 1 -> wh = rndF W -> Kw = rndF (wh * Kh) ->
  Rabs (Kh - Kex) <= ETAK * Rabs Kex -> bpow radix2 (-57) <= Rabs Kex -> Rabs Kex <= / 10 ->
  Rabs (Kw - Kex * W) <= ew * Rabs (Kex * W) /\ Rabs Kw <= 1.
Proof.
  intros HW1 HW2 Hwh HKw HKh Hk1 Hk2.
  pose proof u_pos as Hu. pose proof u_val as Huv.
  assert (HWn : bpow radix2 (-1022) <= Rabs W).
  { rewrite Rabs_pos_eq by lra. eapply Rle_trans; [| exact HW1].
    replace (/ 4096) with (bpow radix2 (-12)) by reflexivity. apply bpow_le. lia. }
  destruct (rnd_delta W (or_intror HWn)) as [d1 [Hd1 E1]]. rewrite <- Hwh in E1.
  assert (HE : ETAK = 17 / 10 ^ 17) by reflexivity.
  assert (Hkne : Kex <> 0) by (intro H0; rewrite H0, Rabs_R0 in Hk1; pose proof (bpow_gt_0 radix2 (-57)); lra).
  set (eta := (Kh - Kex) / Kex).
  assert (Heta : Rabs eta <= ETAK).
  { unfold eta. rewrite Rabs_div_abs by exact Hkne.
    apply Rmult_le_reg_r with (Rabs Kex); [apply Rabs_pos_lt; exact Hkne |].
    unfold Rdiv. rewrite Rmult_assoc, Rinv_l by (apply Rabs_no_R0; exact Hkne). lra. }
  assert (EKh : Kh = Kex * (1 + eta)) by (unfold eta; field; exact Hkne).
  assert (Hwhn : bpow radix2 (-1022) <= Rabs (wh * Kh)).
  { rewrite Rabs_mult. apply Rabs_le_between in Hd1.
    assert (Hwh1 : / 8192 <= Rabs wh).
    { rewrite E1. rewrite Rabs_mult, (Rabs_pos_eq W) by lra. rewrite (Rabs_pos_eq (1 + d1)) by lra. nra. }
    assert (HKh1 : bpow radix2 (-58) <= Rabs Kh).
    { rewrite EKh. rewrite Rabs_mult. rewrite (Rabs_pos_eq (1 + eta)).
      - assert (bpow radix2 (-57) = 2 * bpow radix2 (-58)) by (replace (-57)%Z with (-58 + 1)%Z by reflexivity; rewrite bpow_plus; change (bpow radix2 1) with 2; ring).
        apply Rabs_le_between in Heta. rewrite HE in Heta.
        assert (Hm : Rabs Kex * (1 / 2) <= Rabs Kex * (1 + eta)) by (apply Rmult_le_compat_l; [apply Rabs_pos | lra]).
        lra.
      - apply Rabs_le_between in Heta. rewrite HE in Heta. lra. }
    assert (Hb : bpow radix2 (-1022) <= / 8192 * bpow radix2 (-58)).
    { replace (/ 8192) with (bpow radix2 (-13)) by reflexivity. rewrite <- bpow_plus. apply bpow_le. lia. }
    pose proof (bpow_gt_0 radix2 (-58)).
    assert (/ 8192 * bpow radix2 (-58) <= Rabs wh * Rabs Kh) by (apply Rmult_le_compat; lra).
    lra. }
  destruct (rnd_delta (wh * Kh) (or_intror Hwhn)) as [d2 [Hd2 E2]]. rewrite <- HKw in E2.
  assert (Eq : Kw - Kex * W = Kex * W * ((1 + d1) * (1 + eta) * (1 + d2) - 1)) by (rewrite E2, E1, EKh; ring).
  assert (Hmain : Rabs (Kw - Kex * W) <= ew * Rabs (Kex * W)).
  { rewrite Eq, Rabs_mult.
    assert (Hr : Rabs ((1 + d1) * (1 + eta) * (1 + d2) - 1) <= ew).
    { unfold ew. apply Rabs_le_between in Hd1. apply Rabs_le_between in Hd2. apply Rabs_le_between in Heta.
      destruct Hd1 as [a1 a2]. destruct Hd2 as [b1 b2]. destruct Heta as [c1 c2].
      assert (HE' : ETAK = 17 / 10 ^ 17) by exact HE.
      assert (Hp1 : (1 + d1) * (1 + eta) <= (1 + u) * (1 + ETAK)) by (apply Rmult_le_compat; lra).
      assert (Hp2 : (1 + d1) * (1 + eta) * (1 + d2) <= (1 + u) * (1 + ETAK) * (1 + u)).
      { apply Rmult_le_compat; [apply Rmult_le_pos; lra | lra | exact Hp1 | lra]. }
      assert (Hq1 : (1 - u) * (1 - ETAK) <= (1 + d1) * (1 + eta)) by (apply Rmult_le_compat; lra).
      assert (Hq2 : (1 - u) * (1 - ETAK) * (1 - u) <= (1 + d1) * (1 + eta) * (1 + d2)).
      { apply Rmult_le_compat; [apply Rmult_le_pos; lra | lra | exact Hq1 | lra]. }
      apply Rabs_le. split; [| nra].
      rewrite HE' in Hq2. rewrite HE'. rewrite Huv in *. nra. }
    assert (Hm : Rabs (Kex * W) * Rabs ((1 + d1) * (1 + eta) * (1 + d2) - 1) <= Rabs (Kex * W) * ew) by (apply Rmult_le_compat_l; [apply Rabs_pos | exact Hr]).
    lra. }
  split; [exact Hmain |].
  assert (HKW : Rabs (Kex * W) <= / 10) by (rewrite Rabs_mult, (Rabs_pos_eq W) by lra; assert (Rabs Kex * W <= / 10 * 1) by (apply Rmult_le_compat; [apply Rabs_pos | lra | exact Hk2 | lra]); lra).
  assert (Hew : ew <= / 1000) by (unfold ew; rewrite HE, Huv; nra).
  assert (E3 : Kw = Kex * W + (Kw - Kex * W)) by ring.
  assert (Rabs Kw <= Rabs (Kex * W) + Rabs (Kw - Kex * W)) by (rewrite E3 at 1; apply Rabs_triang).
  pose proof (Rabs_pos (Kex * W)).
  nra.
Qed.

(** The product of the two rounded distribution functions against the exact
    one, from the contract [|Phi' - Phi| <= eP], [Phi'] in [[0, 1]]. *)
Definition eP : R := bpow radix2 (-54) + bpow radix2 (-112).

Lemma phi_prod a b ah bh : 0 <= a <= 1 -> 0 <= b <= 1 -> 0 <= ah <= 1 -> 0 <= bh <= 1 ->
  Rabs (ah - a) <= eP -> Rabs (bh - b) <= eP -> Rabs (ah * bh - a * b) <= 2 * eP.
Proof.
  intros Ha Hb Hah Hbh Ea Eb.
  assert (E : ah * bh - a * b = ah * (bh - b) + b * (ah - a)) by ring.
  rewrite E. eapply Rle_trans; [apply Rabs_triang |]. rewrite !Rabs_mult.
  rewrite (Rabs_pos_eq ah (proj1 Hah)), (Rabs_pos_eq b (proj1 Hb)).
  assert (Hm1 : ah * Rabs (bh - b) <= 1 * eP) by (apply Rmult_le_compat; [lra | apply Rabs_pos | lra | exact Eb]).
  assert (Hm2 : b * Rabs (ah - a) <= 1 * eP) by (apply Rmult_le_compat; [lra | apply Rabs_pos | lra | exact Ea]).
  lra.
Qed.
