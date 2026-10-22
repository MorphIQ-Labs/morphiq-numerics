(** asinh's accurate path: two Newton steps from the fast value land within
    [2^-124] relatively of [arcsinh x] (the Rust's [2^-216] is far inside). *)
From Coq Require Import Reals ZArith Lia Lra Psatz List.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 RoundingCore RoundingTest.
From Interval Require Import Tactic.
From Q Require Import Q256 Q256Real QSpec.
Require Import Ln1pLemmas AsinTables AsinKernel AsinQSeries ErfcxAccurateInputs AsinhTables AsinhKernel AsinhWithin AsinhRoot AsinhExp
  AsinhExpRed AsinhNewton AsinhFast.
Open Scope R_scope.

(** The range of [arcsinh x] on the accurate path's domain. *)
Lemma arcsinh_range x : finite x -> bpow radix2 (-26) <= B x -> 1.4e-8 <= arcsinh (B x) <= 710.6.
Proof.
  intros Fx L.
  assert (HXhi : B x < bpow radix2 1024).
  { pose proof (abs_B2R_lt_emax 53 1024 x) as H. rewrite Rabs_pos_eq in H by (assert (bpow radix2 (-26) > 0) by apply bpow_gt_0; lra). exact H. }
  assert (Hb26 : bpow radix2 (-26) = / 67108864) by (bpow_num; reflexivity).
  assert (HX0 : 0 < B x) by (rewrite Hb26 in L; lra).
  split.
  - apply Rle_trans with (arcsinh (/ 67108864)).
    + pose proof (arcsinh_ge_cubic (/ 67108864) ltac:(split; lra)) as Ag. lra.
    + apply arcsinh_le. rewrite Hb26 in L. exact L.
  - unfold arcsinh. pose proof (sqrt_pos (B x ^ 2 + 1)) as Hsp.
    assert (Hq : sqrt (B x ^ 2 + 1) <= B x + 1).
    { apply Rle_trans with (sqrt ((B x + 1) * (B x + 1))); [apply sqrt_le_1_alt; nra | rewrite sqrt_square by lra; lra]. }
    apply Rle_trans with (ln (bpow radix2 1025 * 1.0001)).
    + apply ln_mono; [lra | ].
      assert (2 * B x + 1 <= bpow radix2 1025 * 1.0001).
      { assert (bpow radix2 1025 = 2 * bpow radix2 1024) by (replace 1025%Z with (1024 + 1)%Z by reflexivity; rewrite bpow_plus; change (bpow radix2 1) with 2; ring).
        assert (10000 <= bpow radix2 1024) by (apply Rle_trans with (bpow radix2 20); [change (bpow radix2 20) with 1048576; lra | apply bpow_le; lia]). lra. }
      lra.
    + rewrite ln_mult by (try apply bpow_gt_0; lra). rewrite ln_bpow. change (IZR 1025) with 1025.
      pose proof ln2_b as [_ Hl2]. assert (ln 1.0001 <= 0.0001) by (interval with (i_prec 60)). nra.
Qed.

Lemma sq_le d b : Rabs d <= b -> d * d <= b * b.
Proof.
  intros H. pose proof (Rabs_pos d) as Hp. assert (Hm : Rabs d * Rabs d <= b * b) by (apply Rmult_le_compat; assumption || lra).
  rewrite <- Rabs_mult in Hm. rewrite Rabs_pos_eq in Hm by exact (Rle_0_sqr _). exact Hm.
Qed.

Lemma bp_m52_ : bpow radix2 (-52) = / 4503599627370496. Proof. bpow_num. reflexivity. Qed.

Lemma bp63 : bpow radix2 (-63) = / 9223372036854775808. Proof. bpow_num. reflexivity. Qed.
Lemma bp124_big : 4e-38 <= bpow radix2 (-124).
Proof. bpow_num. rewrite <- (Rinv_involutive 4e-38) by lra. apply Rinv_le_contravar; [lra | ]. simpl. lra. Qed.

Lemma bp235_tiny : bpow radix2 (-235) <= 1e-70.
Proof.
  bpow_num. apply Rle_trans with (/ 10000000000000000000000000000000000000000000000000000000000000000000000).
  - apply Rinv_le_contravar; lra.
  - lra.
Qed.

(** The error recursion: [4 d^2 + 2^-235] against [(2843 eps^2 + 1e-62) A]. *)
Lemma next_err A d eps : 1.4e-8 <= A <= 710.6 -> Rabs d <= eps * A -> 0 <= eps <= 1e-10 ->
  4 * (d * d) + bpow radix2 (-235) <= (2843 * (eps * eps) + 1e-62) * A.
Proof.
  intros [HA1 HA2] Hd [He0 He1].
  assert (Hsq : d * d <= (eps * A) * (eps * A)) by (apply sq_le; exact Hd).
  assert (HAA : A * A <= 710.6 * A) by (apply Rmult_le_compat_r; lra).
  assert (E : (eps * A) * (eps * A) = (eps * eps) * (A * A)) by ring.
  assert (Hee : 0 <= eps * eps) by (apply Rmult_le_pos; lra).
  assert (H3 : (eps * eps) * (A * A) <= (eps * eps) * (710.6 * A)) by (apply Rmult_le_compat_l; lra).
  assert (Ht : bpow radix2 (-235) <= 1e-62 * A) by (pose proof bp235_tiny; nra).
  nra.
Qed.

Theorem asinh_accurate_value_ok x yh yl : finite x -> finite yh -> finite yl -> bpow radix2 (-26) <= B x ->
  FastOk x (yh, yl) ->
  Q256Real.valid (asinh_accurate_value x (yh, yl)) /\
  Rabs (qval (asinh_accurate_value x (yh, yl)) - arcsinh (B x)) <= bpow radix2 (-124) * arcsinh (B x).
Proof.
  intros Fx Fyh Fyl L [_ [_ [Dw [Hy1 [Hy2 Err]]]]]. cbn [fst snd] in *.
  unfold asinh_accurate_value. cbn [fst snd].
  pose proof (arcsinh_range x Fx L) as [HA1 HA2].
  set (A := arcsinh (B x)) in *.
  assert (Hb26 : bpow radix2 (-26) = / 67108864) by (bpow_num; reflexivity).
  assert (HX0 : 0 < B x) by (rewrite Hb26 in L; lra).
  destruct (q_float_ok x Fx) as [Vx Qx].
  destruct (q_float_ok yh Fyh) as [Vh Qh]. destruct (q_float_ok yl Fyl) as [Vl Ql].
  destruct bpow_254 as [B252 [B255 [Upos Usmall]]]. set (U := bpow radix2 (-254)) in *.
  assert (HUs : U <= 1e-76) by exact bp254_small.
  (* the start *)
  assert (Hyl : Rabs (B yl) <= bpow radix2 (-52) * Rabs (B yh)).
  { apply lo_bound; [ | exact Dw]. rewrite Rabs_pos_eq by (assert (bpow radix2 (-30) > 0) by apply bpow_gt_0; lra).
    apply Rle_trans with (bpow radix2 (-30)); [apply bpow_le; lia | exact Hy1]. }
  cbv zeta.
  set (start := Q256.add (qf yh) (qf yl)).
  set (xq := qf x).
  destruct (add_any (qf yh) (qf yl) Vh Vl) as [Vs Es].
  assert (Qh' : qval (qf yh) = B yh) by exact Qh. assert (Ql' : qval (qf yl) = B yl) by exact Ql.
  rewrite Qh', Ql' in Es.
  assert (Hmx : Rmax (Rabs (B yh)) (Rabs (B yl)) <= 1024).
  { apply Rmax_lub.
    - rewrite Rabs_pos_eq by (assert (bpow radix2 (-30) > 0) by apply bpow_gt_0; lra). change 1024 with (bpow radix2 10). exact Hy2.
    - rewrite bp_m52_ in Hyl. rewrite (Rabs_pos_eq (B yh)) in Hyl by (assert (bpow radix2 (-30) > 0) by apply bpow_gt_0; lra).
      assert (B yh <= 1024) by (change 1024 with (bpow radix2 10); exact Hy2).
      assert (/ 4503599627370496 * B yh <= / 4503599627370496 * 1024) by (apply Rmult_le_compat_l; lra). lra. }
  assert (Hes : Rabs (qval start - (B yh + B yl)) <= 1024 * U).
  { apply Rle_trans with (1 := Es). replace (1024 * U) with (U * 1024) by ring. apply Rmult_le_compat_l; lra. }
  assert (HAp : bpow radix2 (-63) * A >= 1e-27).
  { rewrite bp63. assert (/ 9223372036854775808 * 1.4e-8 <= / 9223372036854775808 * A) by (apply Rmult_le_compat_l; lra). lra. }
  apply Rabs_le_inv in Err. destruct Err as [Er1 Er2].
  apply Rabs_le_inv in Hes. destruct Hes as [Hs1 Hs2].
  assert (Hd0 : Rabs (A - qval start) <= 1.0001 * bpow radix2 (-63) * A).
  { apply Rabs_le. assert (bpow radix2 (-63) * A >= 0) by lra. split; nra. }
  assert (Hsv : 0 <= qval start <= 711).
  { assert (bpow radix2 (-63) <= / 9223372036854775808) by (rewrite bp63; lra).
    assert (bpow radix2 (-63) * A <= / 9223372036854775808 * A) by (apply Rmult_le_compat_r; lra).
    apply Rabs_le_inv in Hd0. destruct Hd0 as [D1 D2]. split; nra. }
  assert (Hd0' : Rabs (A - qval start) <= / 1000000).
  { apply Rle_trans with (1.0001 * bpow radix2 (-63) * A); [exact Hd0 | ].
    rewrite bp63. assert (/ 9223372036854775808 * A <= / 9223372036854775808 * 710.6) by (apply Rmult_le_compat_l; lra). lra. }
  assert (Qx' : qval xq = B x) by exact Qx.
  destruct (newton_step_ok xq start (B x) Vx Vs Qx' HX0 Hsv Hd0') as [V1 E1].
  change (arcsinh (B x)) with A in E1.
  set (y1 := asinh_newton xq start) in *.
  (* the first step: relative 3.35e-35 *)
  assert (Heps0 : Rabs (A - qval start) <= 1.0845e-19 * A).
  { apply Rle_trans with (1 := Hd0). rewrite bp63. assert (/ 9223372036854775808 <= 1.0843e-19) by lra. nra. }
  pose proof (next_err A (A - qval start) 1.0845e-19 ltac:(split; assumption) Heps0 ltac:(split; lra)) as N1.
  assert (Hyy1 : Rabs (qval y1 - A) <= 3.4e-35 * A).
  { apply Rle_trans with (1 := E1). apply Rle_trans with (1 := N1). apply Rmult_le_compat_r; [lra | ]. lra. }
  assert (Hsv1 : 0 <= qval y1 <= 711).
  { apply Rabs_le_inv in Hyy1. destruct Hyy1 as [D1 D2]. assert (3.4e-35 * A <= 3.4e-35 * 710.6) by (apply Rmult_le_compat_l; lra). split; lra. }
  assert (Hd1 : Rabs (A - qval y1) <= / 1000000).
  { rewrite Rabs_minus_sym. apply Rle_trans with (3.4e-35 * A); [exact Hyy1 | ]. assert (3.4e-35 * A <= 3.4e-35 * 710.6) by (apply Rmult_le_compat_l; lra). lra. }
  destruct (newton_step_ok xq y1 (B x) Vx V1 Qx' HX0 Hsv1 Hd1) as [V2 E2].
  change (arcsinh (B x)) with A in E2.
  split; [exact V2 | ].
  assert (Heps1 : Rabs (A - qval y1) <= 3.4e-35 * A) by (rewrite Rabs_minus_sym; exact Hyy1).
  pose proof (next_err A (A - qval y1) 3.4e-35 ltac:(split; assumption) Heps1 ltac:(split; lra)) as N2.
  apply Rle_trans with (1 := E2). apply Rle_trans with (1 := N2).
  apply Rmult_le_compat_r; [lra | ]. pose proof bp124_big. lra.
Qed.
