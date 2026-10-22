(** The accurate path against [asin]: one Newton step in [Q256] from the fast
    path's start lands within [2^-124] of the root, relatively, on both branches. *)
From Coq Require Import Reals ZArith Lia Lra Psatz List.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64.
From Interval Require Import Tactic.
From Q Require Import Q256 Q256Real QSpec.
Require Import Ln1pLemmas AsinTables AsinKernel AsinWithin AsinFacts AsinQSeries AsinSinCos AsinRecip AsinNewton ErfcxAccurateInputs.
Open Scope R_scope.

Lemma tiny_bpow : forall n, (n <= -196)%Z -> bpow radix2 n <= tiny.
Proof.
  intros n H. apply Rle_trans with (bpow radix2 (-196)); [apply bpow_le; lia | ].
  unfold tiny. bpow_num. interval with (i_prec 100).
Qed.

Lemma bpow_124 : bpow radix2 (-124) = / 21267647932558653966460912964485513216.
Proof. bpow_num. reflexivity. Qed.

Lemma bpow_62 : bpow radix2 (-62) = / 4611686018427387904.
Proof. bpow_num. reflexivity. Qed.

(** Splitting a relative error: [v = a (1 + s)] with [|s| <= b] from [|v - a| <= b a]. *)
Lemma rel_split v a b : 0 < a -> Rabs (v - a) <= b * a -> exists s, v = a * (1 + s) /\ Rabs s <= b.
Proof.
  intros Ha H. exists ((v - a) / a). split; [field; lra | ].
  unfold Rdiv. rewrite Rabs_mult, Rabs_Rinv by lra. rewrite (Rabs_pos_eq a) by lra.
  apply (Rmult_le_reg_r a); [exact Ha | ]. rewrite Rmult_assoc, Rinv_l by lra. lra.
Qed.

Lemma cs_range cos_r gamma csv : 0.7071 <= cos_r -> cos_r <= 1 -> Rabs gamma <= tiny -> csv = cos_r * (1 + gamma) ->
  bpow radix2 (-28) <= csv <= 1.0001.
Proof.
  intros H1 H2 Hg Hc. assert (Hb28 : bpow radix2 (-28) <= 0.7) by (bpow_num; interval with (i_prec 100)).
  assert (Ht : 0 < tiny <= / 1000000) by (unfold tiny; split; [apply Rinv_0_lt_compat; lra | apply Rinv_le_contravar; lra]).
  apply Rabs_le_inv in Hg as [Hg1 Hg2]. rewrite Hc. destruct Ht as [Ht0 Ht1]. split; nra.
Qed.

Lemma sn_bound sin_r sigma snv : 0 <= sin_r -> sin_r <= 0.70711 -> Rabs sigma <= tiny -> snv = sin_r * (1 + sigma) -> Rabs snv <= 0.7072.
Proof.
  intros H0 H1 Hs Hn.
  assert (Ht : 0 < tiny <= / 1000000) by (unfold tiny; split; [apply Rinv_0_lt_compat; lra | apply Rinv_le_contravar; lra]).
  destruct Ht as [Ht0 Ht1]. apply Rabs_le_inv in Hs as [Hs1 Hs2]. rewrite Hn. apply Rabs_le. split; nra.
Qed.

Lemma cs_lo cos_r gamma csv : 0.7071 <= cos_r -> cos_r <= 1 -> Rabs gamma <= tiny -> csv = cos_r * (1 + gamma) -> 0.7 <= csv.
Proof.
  intros H1 H2 Hg Hc.
  assert (Ht : 0 < tiny <= / 1000000) by (unfold tiny; split; [apply Rinv_0_lt_compat; lra | apply Rinv_le_contravar; lra]).
  apply Rabs_le_inv in Hg as [Hg1 Hg2]. rewrite Hc. destruct Ht as [Ht0 Ht1]. nra.
Qed.

Theorem accurate_direct x yh yl :
  finite x -> finite yh -> finite yl ->
  / 67108864 <= B x -> B x <= SPLIT -> 0 < B yh -> Rabs (B yl) <= bpow radix2 (-52) * B yh ->
  Rabs (B yh + B yl - asin (B x)) <= bpow radix2 (-62) * asin (B x) ->
  Rabs (qval (asin_accurate_value true x (yh, yl)) - asin (B x)) <= bpow radix2 (-124) * asin (B x).
Proof.
  intros Fx Fyh Fyl Hx0 HxS Hyh Hyl Hst.
  pose proof (quarter_pi_le) as Pq. pose proof PI_RGT_0 as Ppos.
  assert (Hxb : 0 <= B x <= 1) by (split; [lra | ]; unfold SPLIT in HxS; lra).
  pose proof (asin_nonneg _ Hxb) as Y0. pose proof (asin_ge _ Hxb) as Yge. pose proof (asin_bound (B x)) as [_ Yhalf].
  assert (HsY : sin (asin (B x)) = B x) by (apply sin_asin; split; lra).
  pose proof (sin_split_range (asin (B x)) (conj Y0 Yhalf) ltac:(rewrite HsY; exact HxS)) as HYhi.
  set (Y := asin (B x)) in *.
  assert (HY1 : Y <= 0.7854) by lra.
  assert (HY2 : / 67108864 <= Y) by lra.
  unfold asin_accurate_value. cbv zeta beta.
  destruct (q_sin_cos (asin_start (yh, yl))) as [sn cs] eqn:Esc.
  cbv iota.
  (* the start as a Q256 value *)
  destruct (q_float_ok yh Fyh) as [Vyh Qyh]. destruct (q_float_ok yl Fyl) as [Vyl Qyl].
  destruct bpow_254 as [B252 [B255 [Upos Usmall]]]. set (U := bpow radix2 (-254)) in *.
  assert (HUs : 0 < U <= / 1000000000000000000000000000000000000000000000000000000000000) by (split; [exact Upos | exact Usmall]).
  assert (P52 : bpow radix2 (-52) = / 4503599627370496) by (bpow_num; reflexivity).
  assert (P62 : bpow radix2 (-62) = / 4611686018427387904) by (bpow_num; reflexivity).
  rewrite P52 in Hyl. rewrite P62 in Hst.
  pose proof (add_any (q_float yh) (q_float yl) Vyh Vyl) as [Vst Est].
  rewrite Qyh, Qyl in Est.
  assert (Hmax : Rmax (Rabs (B yh)) (Rabs (B yl)) = B yh).
  { rewrite (Rabs_pos_eq (B yh)) by lra. apply Rmax_left. lra. }
  rewrite Hmax in Est. change (bpow radix2 (-254)) with U in Est.
  set (st := asin_start (yh, yl)) in *.
  assert (Hstv : st = Q256.add (q_float yh) (q_float yl)) by reflexivity.
  rewrite <- Hstv in Vst, Est.
  set (r := qval st) in *.
  apply Rabs_le_inv in Hst as [Hst1 Hst2]. pose proof Hyl as Hyl'. apply Rabs_le_inv in Hyl' as [Hyl1 Hyl2].
  assert (Hyhb : B yh <= 1.0001 * Y) by lra.
  assert (HUy : U * B yh <= / 100000000000000000000000000000 * Y).
  { assert (U * B yh <= U * (1.0001 * Y)) by (apply Rmult_le_compat_l; lra).
    assert (U * Y <= / 1000000000000000000000000000000000000000000000000000000000000 * Y) by (apply Rmult_le_compat_r; lra).
    lra. }
  assert (Hrr : Rabs (r - Y) <= eta62 * Y).
  { unfold eta62. apply Rabs_le_inv in Est as [Es1 Es2]. apply Rabs_le. split; lra. }
  assert (Hrpos : 0 < r) by (unfold eta62 in Hrr; apply Rabs_le_inv in Hrr; nra).
  assert (Hr2 : r <= 0.7854) by (unfold eta62 in Hrr; apply Rabs_le_inv in Hrr; nra).
  assert (Hr3 : r <= PI / 4) by (unfold eta62 in Hrr; apply Rabs_le_inv in Hrr; nra).
  set (d := Y - r).
  assert (Hd : Rabs d <= eta62 * Y) by (unfold d; rewrite Rabs_minus_sym; exact Hrr).
  assert (Hd61 : Rabs d <= / 2 ^ 61).
  { apply Rle_trans with (1 := Hd). apply Rle_trans with (eta62 * 0.7854);
      [apply Rmult_le_compat_l; [unfold eta62; lra | lra] | unfold eta62; interval with (i_prec 60)]. }
  (* Taylor at the start *)
  assert (H260 : / 2 ^ 60 = / 1152921504606846976) by (f_equal; simpl; ring).
  destruct (taylor_sin r d (conj (Rlt_le _ _ Hrpos) Hr3) Hd61) as [rr [[Hrr1 Hrr2] Htay]].
  rewrite H260 in Hrr1.
  replace (r + d) with Y in Htay by (unfold d; ring). rewrite HsY in Htay.
  (* sin and cos at the start, in Q256 *)
  pose proof (q_sin_cos_error st Vst (conj (Rlt_le _ _ Hrpos) Hr2)) as [Vsn [Vcs [Esn Ecs]]].
  rewrite Esc in Vsn, Vcs, Esn, Ecs. cbn [fst snd] in Vsn, Vcs, Esn, Ecs.
  pose proof (sin_ratio r (conj Hrpos Hr3)) as Hsr.
  pose proof (quarter_pi_ranges r (conj (Rlt_le _ _ Hrpos) Hr3)) as [Hc71 Hs71].
  pose proof (COS_bound r) as [_ Hc1].
  assert (Hsinpos : 0 < sin r) by lra. assert (Hcospos : 0 < cos r) by lra.
  destruct (rel_split _ _ _ Hsinpos Esn) as [sigma [Hsig Hsig']].
  destruct (rel_split _ _ _ Hcospos Ecs) as [gamma [Hgam Hgam']].
  assert (Hsig2 : Rabs sigma <= tiny) by (apply Rle_trans with (1 := Hsig'); apply tiny_bpow; lia).
  assert (Hgam2 : Rabs gamma <= tiny) by (apply Rle_trans with (1 := Hgam'); apply tiny_bpow; lia).
  assert (Ht : 0 < tiny <= / 1000000) by (unfold tiny; split; [apply Rinv_0_lt_compat; lra | apply Rinv_le_contravar; lra]).
  (* the reciprocal of cos *)
  set (csv := qval cs) in *. set (snv := qval sn) in *.
  assert (Hcsr : bpow radix2 (-28) <= csv <= 1.0001) by (apply (cs_range (cos r) gamma csv); assumption).
  destruct (q_recip_ok cs Vcs Hcsr) as [Vri [Pri Eri]].
  set (riv := qval (q_recip cs)) in *.
  assert (He : Rabs (csv * riv - 1) <= tiny) by (apply Rle_trans with (1 := Eri); apply tiny_bpow; lia).
  (* the residual *)
  destruct (q_float_ok x Fx) as [Vx Qx].
  destruct (neg_any sn Vsn) as [Vns Qns].
  destruct (add_any (q_float x) (neg_q sn) Vx Vns) as [Vres Eres].
  rewrite Qx, Qns in Eres. change (bpow radix2 (-254)) with U in Eres.
  assert (Hsn1 : Rabs snv <= 0.7072) by (apply (sn_bound (sin r) sigma snv); lra).
  assert (Hmax2 : Rmax (Rabs (B x)) (Rabs (- snv)) <= 1).
  { apply Rmax_lub; [rewrite Rabs_pos_eq by lra; unfold SPLIT in HxS; lra | rewrite Rabs_Ropp; lra]. }
  set (resq := Q256.add (q_float x) (neg_q sn)) in *.
  set (resv := qval resq) in *.
  set (g2 := resv - (B x + - snv)).
  assert (HUt : U <= tiny) by (apply Rle_trans with (1 := proj2 HUs); unfold tiny; apply Rinv_le_contravar; lra).
  assert (Hg2 : Rabs g2 <= tiny).
  { apply Rle_trans with (U * 1); [ | lra].
    apply Rle_trans with (1 := Eres). apply Rmult_le_compat_l; [lra | exact Hmax2]. }
  (* the product and the sum *)
  destruct (mul_relative resq (q_recip cs) Vres Vri) as [Vp [d3 [Hd3 Ep]]].
  rewrite B255 in Hd3.
  set (prq := Q256.mul resq (q_recip cs)) in *. set (prv := qval prq) in *.
  destruct (add_any st prq Vst Vp) as [Vy Ey]. change (bpow radix2 (-254)) with U in Ey.
  set (y1q := Q256.add st prq) in *. set (y1v := qval y1q) in *.
  set (g3 := y1v - (r + prv)).
  (* crude sizes: |res| <= 2, |ri| <= 2, so |prod| <= 5 *)
  assert (Hres2 : Rabs resv <= 2).
  { assert (g2 = resv - (B x + - snv)) by reflexivity.
    apply Rabs_le_inv in Hg2 as [Hg2a Hg2b]. apply Rabs_le_inv in Hsn1 as [Hsa Hsb]. destruct Ht as [Ht0 Ht1].
    apply Rabs_le. unfold SPLIT in HxS. split; lra. }
  assert (Hri2 : Rabs riv <= 2).
  { assert (Hcs7 : 0.7 <= csv) by (apply cs_lo with (cos r) gamma; assumption).
    apply Rabs_le_inv in He as [He1 He2]. destruct Ht as [Ht0 Ht1].
    rewrite Rabs_pos_eq by lra. nra. }
  assert (Hprv : Rabs prv <= 5).
  { rewrite Ep. rewrite !Rabs_mult. assert (Rabs (1 + d3) <= 1.01).
    { apply Rabs_le_inv in Hd3. destruct Ht as [Ht0 Ht1]. apply Rabs_le. split; lra. }
    pose proof (Rabs_pos resv). pose proof (Rabs_pos riv). pose proof (Rabs_pos (1 + d3)).
    assert (Rabs resv * Rabs riv <= 2 * 2) by (apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | exact Hres2 | exact Hri2]).
    assert (Hf : Rabs resv * Rabs riv * Rabs (1 + d3) <= 4 * 1.01) by (apply Rmult_le_compat; [apply Rmult_le_pos; apply Rabs_pos | apply Rabs_pos | lra | lra]).
    apply Rle_trans with (1 := Hf). lra. }
  assert (HU2 : U <= / 10000000000000000000000000000000000000000000000000000000000000000000000) by (unfold U; bpow_num; interval with (i_prec 300)).
  assert (Hmax3 : Rmax (Rabs r) (Rabs prv) <= 5) by (apply Rmax_lub; [rewrite Rabs_pos_eq by lra; lra | exact Hprv]).
  assert (Hg3 : Rabs g3 <= tiny * Y).
  { apply Rle_trans with (U * 5); [apply Rle_trans with (1 := Ey); apply Rmult_le_compat_l; [lra | exact Hmax3] | ].
    apply Rle_trans with (tiny * / 67108864).
    - unfold tiny. lra.
    - apply Rmult_le_compat_l; [lra | exact HY2]. }
  assert (Hd3' : Rabs d3 <= tiny) by (apply Rle_trans with (U / 2); [exact Hd3 | lra]).
  rewrite bpow_124.
  exact (newton_direct_real Y r d (B x) snv csv riv resv prv y1v (sin r) (cos r) sigma gamma (csv * riv - 1) d3 g2 g3 rr
    (ltac:(unfold d; ring)) HY1 HY2 Hd Hc71 Hc1 ltac:(lra) Hs71 Htay ltac:(split; assumption) Hsig Hsig2 Hgam Hgam2
    ltac:(ring) He ltac:(unfold g2; ring) Hg2 Ep Hd3' ltac:(unfold g3; ring) Hg3).
Qed.
