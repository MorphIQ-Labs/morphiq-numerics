(** asinh's accurate path, the exponential's argument reduction: [k] is the
    nearest integer to [y / ln 2], [r = y - k ln 2] stays within [0.3467], and
    [asinh_exp y] is [m 2^k] with [m] within [2^-237] of [exp r]. *)
From Coq Require Import Reals ZArith Lia Lra Psatz List.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Mul Grid Encodings RoundingCore.
From Interval Require Import Tactic.
From Q Require Import Q256 Q256Real QSpec.
Require Import Ln1pLemmas AsinTables AsinKernel AsinSqrtStep AsinSegment AsinSeriesSmall AsinRecip AsinQSeries
  ExpReduction ErfcxAccurateInputs AsinhTables AsinhKernel AsinhConst AsinhOps AsinhWithin AsinhExp.
Import ListNotations.
Open Scope R_scope.

(** The integer a binary64 integer holds. *)
Lemma asinh_int_val f z : finite f -> B f = IZR z -> asinh_int f = z.
Proof.
  intros Ff Hv. destruct f as [s | s | s pl Hpl | s m e Hb]; try (simpl in Ff; discriminate Ff).
  - simpl in Hv. simpl. assert (IZR z = 0) by (rewrite <- Hv; reflexivity). apply eq_IZR in H. lia.
  - cbn [asinh_int]. cbn in Hv. unfold F2R in Hv. cbn [Fnum Fexp] in Hv.
    destruct (e <? 0)%Z eqn:Ee.
    + apply Z.ltb_lt in Ee.
      assert (Hp : bpow radix2 e = / IZR (2 ^ (- e))).
      { replace e with (- (- e))%Z at 1 by ring. rewrite bpow_opp. f_equal. symmetry. apply (IZR_Zpower radix2). lia. }
      rewrite Hp in Hv.
      assert (Hpos : 0 < IZR (2 ^ (- e))) by (apply IZR_lt; apply Z.pow_pos_nonneg; lia).
      assert (Hz : cond_Zopp s (Zpos m) = (z * 2 ^ (- e))%Z).
      { apply eq_IZR. rewrite mult_IZR. rewrite <- Hv.
        field. apply not_eq_sym. apply Rlt_not_eq. exact Hpos. }
      rewrite (Z.shiftr_div_pow2 (Zpos m) (- e)) by lia.
      destruct s.
      * simpl in Hz. simpl. assert (Zpos m = (- z * 2 ^ (- e))%Z) by lia.
        rewrite H. rewrite Z.div_mul by (apply Z.pow_nonzero; lia). lia.
      * simpl in Hz. simpl. rewrite Hz. rewrite Z.div_mul by (apply Z.pow_nonzero; lia). lia.
    + apply Z.ltb_ge in Ee. rewrite (Z.shiftl_mul_pow2 (Zpos m) e) by lia.
      assert (Hp : bpow radix2 e = IZR (2 ^ e)) by (symmetry; apply (IZR_Zpower radix2); lia).
      rewrite Hp in Hv. rewrite <- mult_IZR in Hv. apply eq_IZR in Hv.
      destruct s; cbn [cond_Zopp] in Hv |- *.
      * change (Z.neg m) with (- Z.pos m)%Z in Hv. rewrite <- Hv. ring.
      * exact Hv.
Qed.

Definition ln2q : q256 := Q256.new false (fst asinh_ln2_q256) (snd asinh_ln2_q256).

Lemma ln2q_limbs : limbs_check (fst asinh_ln2_q256) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma ln2q_v : Limbs.v (fst asinh_ln2_q256) = 80260960185991308862233904206310070533990667611589946606122867505419956976172%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma ln2q_ok : Q256Real.valid ln2q /\ Rabs (qval ln2q - ln 2) <= bpow radix2 (-250) /\ 0.69 <= qval ln2q <= 0.7.
Proof.
  pose proof (limbs_check_ok _ ln2q_limbs) as Ok.
  split; [exact (new_valid false _ _ Ok) | ].
  assert (Hq : qval ln2q = IZR 80260960185991308862233904206310070533990667611589946606122867505419956976172 * bpow radix2 (-256)).
  { unfold ln2q. rewrite new_val by exact Ok. rewrite ln2q_v. unfold val, F2R. cbn [Fnum Fexp]. 
    change (snd asinh_ln2_q256) with (-256)%Z. reflexivity. }
  rewrite Hq. bpow_num. split.
  - apply Rabs_le. split; interval with (i_prec 500).
  - split; interval with (i_prec 500).
Qed.

Lemma inv_ln2_val : finite (aw asinh_inv_ln2) /\ Rabs (B (aw asinh_inv_ln2) - / ln 2) <= / 5000000000000000 /\ 1.44 <= B (aw asinh_inv_ln2) <= 1.45.
Proof.
  destruct (word_ok_intro (0x3ff71547652b82fe)%Z false 6497320848556798%positive 52%nat (3248660424278399)%Z 1%Z (-51)%Z
    eq_refl eq_refl ltac:(lia) eq_refl) as [F V].
  unfold asinh_inv_ln2. split; [exact F | ]. rewrite V. bpow_num.
  split; [ | split]; interval with (i_prec 100).
Qed.

(** [|exp u - 1| <= 2 |u|] for [|u| <= 1/2]. *)
Lemma exp_near1 u : Rabs u <= / 2 -> Rabs (exp u - 1) <= 2 * Rabs u.
Proof.
  intros H. apply Rabs_le_inv in H. destruct H as [H1 H2].
  pose proof (exp_pos u) as P.
  assert (L : 1 + u <= exp u).
  { destruct (Req_dec u 0) as [-> | N]; [rewrite exp_0; lra | pose proof (exp_ineq1 u N); lra]. }
  assert (L' : 1 + - u <= exp (- u)).
  { destruct (Req_dec u 0) as [-> | N]; [rewrite Ropp_0, exp_0; lra | pose proof (exp_ineq1 (- u) ltac:(lra)); lra]. }
  destruct (Rle_lt_dec 0 u) as [Hp | Hn].
  - assert (E : exp u = / exp (- u)) by (rewrite exp_Ropp, Rinv_involutive; [reflexivity | apply Rgt_not_eq, P]).
    assert (U : exp u <= / (1 - u)) by (rewrite E; apply Rinv_le_contravar; lra).
    assert (U2 : / (1 - u) <= 1 + 2 * u).
    { apply (Rmult_le_reg_l (1 - u)); [lra | ]. rewrite Rinv_r by lra. nra. }
    rewrite (Rabs_pos_eq u) by lra. apply Rabs_le. split; lra.
  - assert (U : exp u <= 1) by (rewrite <- exp_0; apply Rlt_le, exp_increasing; lra).
    rewrite (Rabs_left u) by lra. apply Rabs_le. split; lra.
Qed.

(** [exp] is [3]-Lipschitz on [[-0.35, 0.35]]. *)
Lemma exp_lip a b : Rabs a <= 0.35 -> Rabs b <= 0.35 -> Rabs (a - b) <= / 2 -> Rabs (exp a - exp b) <= 3 * Rabs (a - b).
Proof.
  intros Ha Hb Hd.
  pose proof (exp_near1 (a - b) Hd) as N.
  assert (E : exp a - exp b = exp b * (exp (a - b) - 1)).
  { assert (E1 : exp b * exp (a - b) = exp a) by (rewrite <- exp_plus; f_equal; ring).
    rewrite Rmult_minus_distr_l, Rmult_1_r, E1. reflexivity. }
  rewrite E, Rabs_mult, (Rabs_pos_eq (exp b)) by apply Rlt_le, exp_pos.
  assert (Eb : exp b <= 1.5).
  { apply Rabs_le_inv in Hb. destruct Hb as [Hb1 Hb2]. destruct (Rle_lt_or_eq_dec b 0.35 Hb2) as [Hlt | Heq]; [apply Rle_trans with (exp 0.35); [apply Rlt_le, exp_increasing; exact Hlt | interval with (i_prec 60)] | rewrite Heq; interval with (i_prec 60)]. }
  pose proof (Rabs_pos (exp (a - b) - 1)). 
  apply Rle_trans with (1.5 * (2 * Rabs (a - b))); [apply Rmult_le_compat; try apply Rlt_le, exp_pos; try lra; exact N | lra].
Qed.

Lemma ln2_b : 0.6931 <= ln 2 <= 0.6932.
Proof. split; interval with (i_prec 60). Qed.

Lemma asinh_shifter_eq : asinh_shifter = shifter.
Proof. exact asin_shifter_eq. Qed.

Lemma bpm53 : bpow radix2 (-53) = / 9007199254740992. Proof. bpow_num. reflexivity. Qed.
Lemma bpm1075_tiny : bpow radix2 (-1075) <= 1e-100.
Proof.
  apply Rle_trans with (bpow radix2 (-340)); [apply bpow_le; lia | ].
  bpow_num. apply Rle_trans with (/ 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000);
    [apply Rinv_le_contravar; [lra | ] | lra].
  simpl. lra.
Qed.

Theorem asinh_exp_ok y : Q256Real.valid y -> 0 <= qval y <= 711 ->
  Q256Real.valid (fst (asinh_exp y)) /\
  Rabs (qval y - IZR (snd (asinh_exp y)) * ln 2) <= 0.3467 /\
  (Z.abs (snd (asinh_exp y)) <= 1100)%Z /\
  Rabs (qval (fst (asinh_exp y)) - exp (qval y - IZR (snd (asinh_exp y)) * ln 2)) <= bpow radix2 (-237).
Proof.
  intros Vy [Hy0 Hy1].
  unfold asinh_exp. cbv zeta. cbn [fst snd].
  set (yv := qval y) in *.
  (* the binary64 start *)
  assert (Hrb : Rabs (rndF yv) < bpow radix2 1024).
  { apply Rle_lt_trans with 1024.
    - apply rnd_bound; [change 1024 with (bpow radix2 10); apply fmt_pow; lia | rewrite Rabs_pos_eq by lra; lra].
    - change (bpow radix2 1024) with (2 * bpow radix2 1023). assert (1024 <= bpow radix2 1023) by (apply Rle_trans with (bpow radix2 10); [change (bpow radix2 10) with 1024; lra | apply bpow_le; lia]). lra. }
  destruct (q_to_float_round y Vy Hrb) as [Fy64 By64].
  set (y64 := Q256.to_f64 y) in *.
  change (qval y) with yv in By64.
  assert (Heta : bpow radix2 (-1075) <= 1e-100) by exact bpm1075_tiny.
  assert (HBy : Rabs (B y64 - yv) <= 8e-14).
  { rewrite By64. pose proof (rnd_err yv) as R. rewrite bpm53, (Rabs_pos_eq yv) in R by lra.
    assert (/ 9007199254740992 * yv <= / 9007199254740992 * 711) by (apply Rmult_le_compat_l; lra). lra. }
  assert (HBy0 : 0 <= B y64) by (rewrite By64; apply round_ge_generic; [exact _ | exact _ | apply generic_format_0 | exact Hy0]).
  assert (HBy2 : 0 <= B y64 <= 711.1) by (apply Rabs_le_inv in HBy; destruct HBy as [H1 H2]; split; lra).
  destruct inv_ln2_val as [Finv [Hinv_c [Hinv1 Hinv2]]].
  set (inv := aw asinh_inv_ln2) in *.
  assert (Hpa : Rabs (B y64 * B inv) <= bpow radix2 11).
  { destruct HBy2 as [P1 P2]. rewrite Rabs_pos_eq by nra. change (bpow radix2 11) with 2048.
    assert (B y64 * B inv <= 711.1 * 1.45) by (apply Rmult_le_compat; lra). lra. }
  destruct (mul_abs2 y64 inv 11 Fy64 Finv Hpa ltac:(lia)) as [Fprod [Eprod Bprod]].
  set (prod := fmul y64 inv) in *.
  assert (Hpe : Rabs (B prod - B y64 * B inv) <= 1.2e-13).
  { rewrite Eprod. pose proof (rnd_err (B y64 * B inv)) as R. rewrite bpm53 in R.
    assert (Rabs (B y64 * B inv) <= 1032).
    { destruct HBy2 as [P1 P2]. rewrite Rabs_pos_eq by nra. assert (B y64 * B inv <= 711.1 * 1.45) by (apply Rmult_le_compat; lra). lra. }
    assert (/ 9007199254740992 * Rabs (B y64 * B inv) <= / 9007199254740992 * 1032) by (apply Rmult_le_compat_l; lra). lra. }
  assert (Hp50 : Rabs (B prod) <= bpow radix2 50).
  { apply Rle_trans with (bpow radix2 11); [exact Bprod | apply bpow_le; lia]. }
  rewrite asinh_shifter_eq.
  destruct (shifter_round prod Fprod Hp50) as [Fk Bk].
  set (kn := Znearest ne (B prod)) in *.
  set (k := fsub (fadd prod shifter) shifter) in *.
  assert (Hkz : asinh_int k = kn) by (apply asinh_int_val; assumption).
  rewrite Hkz.
  pose proof ln2_b as [Hl1 Hl2].
  assert (Hk_half : Rabs (B prod - IZR kn) <= / 2) by (unfold kn; apply Znearest_half).
  assert (Hq_c : Rabs (B prod - yv / ln 2) <= 4e-13).
  { assert (E1 : B prod - yv / ln 2 = (B prod - B y64 * B inv) + (B y64 - yv) * B inv + yv * (B inv - / ln 2)) by (unfold Rdiv; ring).
    rewrite E1.
    apply Rle_trans with (Rabs (B prod - B y64 * B inv) + Rabs ((B y64 - yv) * B inv) + Rabs (yv * (B inv - / ln 2))).
    { pose proof (Rabs_triang (B prod - B y64 * B inv + (B y64 - yv) * B inv) (yv * (B inv - / ln 2))).
      pose proof (Rabs_triang (B prod - B y64 * B inv) ((B y64 - yv) * B inv)). lra. }
    rewrite !Rabs_mult. rewrite (Rabs_pos_eq yv) by lra. rewrite (Rabs_pos_eq (B inv)) by lra.
    assert (Rabs (B y64 - yv) * B inv <= 8e-14 * 1.45) by (apply Rmult_le_compat; [apply Rabs_pos | lra | exact HBy | lra]).
    assert (yv * Rabs (B inv - / ln 2) <= 711 * / 5000000000000000) by (apply Rmult_le_compat; [lra | apply Rabs_pos | lra | exact Hinv_c]).
    lra. }
  assert (Hkd : Rabs (IZR kn - yv / ln 2) <= 0.5 + 4e-13).
  { apply Rabs_le_inv in Hk_half. apply Rabs_le_inv in Hq_c. destruct Hk_half as [A1 A2]. destruct Hq_c as [B1 B2].
    apply Rabs_le. split; lra. }
  assert (Hrt : Rabs (yv - IZR kn * ln 2) <= 0.3467).
  { assert (E : yv - IZR kn * ln 2 = - (ln 2 * (IZR kn - yv / ln 2))) by (field; lra).
    rewrite E, Rabs_Ropp, Rabs_mult, (Rabs_pos_eq (ln 2)) by lra.
    apply Rle_trans with (0.6932 * (0.5 + 4e-13)); [apply Rmult_le_compat; [lra | apply Rabs_pos | lra | exact Hkd] | lra]. }
  assert (Hkabs : (Z.abs kn <= 1100)%Z).
  { apply Rabs_le_inv in Hkd. destruct Hkd as [K1 K2].
    assert (yv / ln 2 <= 1027) by (apply Rle_trans with (711 / 0.6931); [unfold Rdiv; apply Rmult_le_compat; [lra | apply Rlt_le, Rinv_0_lt_compat; lra | lra | apply Rinv_le_contravar; lra] | lra]).
    assert (0 <= yv / ln 2) by (unfold Rdiv; apply Rmult_le_pos; [lra | apply Rlt_le, Rinv_0_lt_compat; lra]).
    assert (Hr1 : IZR kn <= 1028) by lra. assert (Hr2 : -1 <= IZR kn) by lra.
    assert (kn <= 1028)%Z by (apply le_IZR; exact Hr1). assert (-1 <= kn)%Z by (apply le_IZR; exact Hr2). lia. }
  change (Q256.new false (fst asinh_ln2_q256) (snd asinh_ln2_q256)) with ln2q.
  set (rq := Q256.add y (Q256.neg_q (Q256.mul (qf k) ln2q))).
  change (fold_left (fun h '(m, e) => Q256.add q_one (Q256.mul (Q256.mul rq (Q256.new false m e)) h)) (rev asinh_exp_steps) q_one)
    with (q_hser rq asinh_exp_steps).
  assert (Hqf : Q256Real.valid (qf k) /\ qval (qf k) = B k) by exact (q_float_ok k Fk).
  destruct Hqf as [Vk Qk]. rewrite Bk in Qk.
  destruct ln2q_ok as [Vl [Hlc [Hl1' Hl2']]].
  set (Lv := qval ln2q) in *.
  destruct (mul_relative (qf k) ln2q Vk Vl) as [Vp [d1 [D1 E1]]].
  destruct (neg_any (Q256.mul (qf k) ln2q) Vp) as [Vn En].
  destruct (add_any y (Q256.neg_q (Q256.mul (qf k) ln2q)) Vy Vn) as [Vr Er].
  set (p := qval (Q256.mul (qf k) ln2q)) in *.
  change (qval y) with yv in Er.
  destruct bpow_254 as [B252 [B255 [Upos Usmall]]].
  set (U := bpow radix2 (-254)) in *.
  rewrite B255 in D1.
  assert (B250 : bpow radix2 (-250) = 16 * U) by (unfold U; replace (-250)%Z with (-254 + 4)%Z by reflexivity; rewrite bpow_plus; change (bpow radix2 4) with 16; ring).
  assert (B239 : bpow radix2 (-239) = 32768 * U) by (unfold U; replace (-239)%Z with (-254 + 15)%Z by reflexivity; rewrite bpow_plus; change (bpow radix2 15) with 32768; ring).
  assert (B237 : bpow radix2 (-237) = 131072 * U) by (unfold U; replace (-237)%Z with (-254 + 17)%Z by reflexivity; rewrite bpow_plus; change (bpow radix2 17) with 131072; ring).
  assert (Hkr : -1100 <= IZR kn <= 1100).
  { apply Z.abs_le in Hkabs. destruct Hkabs as [K1 K2]. split; [change (-1100) with (IZR (-1100)) | change 1100 with (IZR 1100)]; apply IZR_le; assumption. }
  destruct Hkr as [Hkz1 Hkz2].
  assert (Hp : p = IZR kn * Lv * (1 + d1)) by (rewrite E1, Qk; reflexivity).
  pose proof D1 as D1c. apply Rabs_le_inv in D1c. destruct D1c as [D1a D1b].
  assert (Hpb : Rabs p <= 771).
  { rewrite Hp. rewrite !Rabs_mult. rewrite (Rabs_pos_eq Lv) by lra.
    assert (Rabs (IZR kn) <= 1100) by (apply Rabs_le; split; lra).
    assert (Rabs (1 + d1) <= 1.0001) by (apply Rabs_le; split; lra).
    assert (Rabs (IZR kn) * Lv <= 1100 * 0.7) by (apply Rmult_le_compat; [apply Rabs_pos | lra | lra | lra]).
    pose proof (Rabs_pos (IZR kn)).
    assert (Rabs (IZR kn) * Lv * Rabs (1 + d1) <= (1100 * 0.7) * 1.0001) by (apply Rmult_le_compat; [apply Rle_trans with 0; [lra | apply Rmult_le_pos; [apply Rabs_pos | lra]] | apply Rabs_pos | lra | lra]).
    lra. }
  assert (HEr : Rabs (qval rq - (yv + qval (Q256.neg_q (Q256.mul (qf k) ln2q)))) <= U * 771).
  { apply Rle_trans with (1 := Er). rewrite En. 
    assert (Rmax (Rabs yv) (Rabs (- p)) <= 771) by (apply Rmax_lub; [rewrite Rabs_pos_eq by lra; lra | rewrite Rabs_Ropp; exact Hpb]).
    apply Rle_trans with (U * 771); [apply Rmult_le_compat_l; lra | lra]. }
  rewrite En in HEr.
  set (rt := yv - IZR kn * ln 2).
  assert (Hdiff : Rabs (qval rq - rt) <= 32768 * U).
  { assert (E : qval rq - rt = (qval rq - (yv + - p)) + IZR kn * (ln 2 - Lv) - IZR kn * Lv * d1) by (unfold rt; rewrite Hp; ring).
    rewrite E.
    assert (Hb1 : Rabs (IZR kn * (ln 2 - Lv)) <= 1100 * (16 * U)).
    { rewrite Rabs_mult. rewrite Rabs_minus_sym in Hlc. rewrite B250 in Hlc.
      apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | apply Rabs_le; split; lra | exact Hlc]. }
    assert (Hb2 : Rabs (IZR kn * Lv * d1) <= (1100 * 0.7) * (U / 2)).
    { rewrite Rabs_mult, Rabs_mult, (Rabs_pos_eq Lv) by lra.
      assert (Rabs (IZR kn) * Lv <= 1100 * 0.7) by (apply Rmult_le_compat; [apply Rabs_pos | lra | apply Rabs_le; split; lra | lra]).
      apply Rmult_le_compat; [apply Rle_trans with 0; [lra | apply Rmult_le_pos; [apply Rabs_pos | lra]] | apply Rabs_pos | exact H | lra]. }
    apply Rle_trans with (Rabs (qval rq - (yv + - p)) + Rabs (IZR kn * (ln 2 - Lv)) + Rabs (IZR kn * Lv * d1)).
    { pose proof (Rabs_triang (qval rq - (yv + - p) + IZR kn * (ln 2 - Lv)) (- (IZR kn * Lv * d1))).
      pose proof (Rabs_triang (qval rq - (yv + - p)) (IZR kn * (ln 2 - Lv))).
      rewrite Rabs_Ropp in H. replace (qval rq - (yv + - p) + IZR kn * (ln 2 - Lv) - IZR kn * Lv * d1) with (qval rq - (yv + - p) + IZR kn * (ln 2 - Lv) + - (IZR kn * Lv * d1)) by ring.
      lra. }
    lra. }
  assert (HUs : U <= 1e-60) by (apply Rle_trans with (/ 1000000000000000000000000000000000000000000000000000000000000); [exact Usmall | lra]).
  change (yv - IZR kn * ln 2) with rt in Hrt.
  assert (Hrq : Rabs (qval rq) <= 0.35).
  { pose proof (Rabs_triang rt (qval rq - rt)). replace (rt + (qval rq - rt)) with (qval rq) in H by ring.
    lra. }
  destruct (q_hser_exp rq Vr Hrq) as [Vh Eh].
  assert (Hrt' : Rabs rt <= 0.35) by lra.
  assert (Hdd : Rabs (qval rq - rt) <= / 2) by lra.
  pose proof (exp_lip (qval rq) rt Hrq Hrt' Hdd) as Lp.
  rewrite B239 in Eh.
  assert (Hfin : Rabs (qval (q_hser rq asinh_exp_steps) - exp rt) <= bpow radix2 (-237)).
  { rewrite B237.
    apply Rle_trans with (Rabs (qval (q_hser rq asinh_exp_steps) - exp (qval rq)) + Rabs (exp (qval rq) - exp rt)).
    - replace (qval (q_hser rq asinh_exp_steps) - exp rt) with ((qval (q_hser rq asinh_exp_steps) - exp (qval rq)) + (exp (qval rq) - exp rt)) by ring.
      apply Rabs_triang.
    - lra. }
  split; [exact Vh | split; [exact Hrt | split; [exact Hkabs | exact Hfin]]].
Qed.
