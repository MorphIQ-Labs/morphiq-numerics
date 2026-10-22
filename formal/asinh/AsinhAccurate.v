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
