(** asinh's entry point over every binary64 input: the special values, the
    threshold, the fast path with its rounding decision, the accurate path, and
    the sign through the encoding. *)
From Coq Require Import Reals ZArith Lia Lra Psatz List.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 RoundingCore RoundingTest.
From Interval Require Import Tactic.
From Q Require Import Q256 Q256Real QSpec.
Require Import Ln1pLemmas AsinTables AsinKernel AsinSqrtStep AsinRecip AsinCorrect AsinEntry ErfcxAccurateInputs
  AsinhTables AsinhKernel AsinhConst AsinhWithin AsinhExpRed AsinhFast AsinhAccurate AsinhSmall.
Open Scope R_scope.

(** The published worst-case search: no binary64 midpoint within [2^-124] of [arcsinh a]. *)
Definition CoreMathH : Prop :=
  forall a, finite a -> B asinh_is_x < B a -> Stable (arcsinh (B a)).

Lemma accurate_round_h q Z : Q256Real.valid q -> Rabs (qval q - Z) <= bpow radix2 (-124) * Z -> Stable Z ->
  1e-9 <= Z <= 711 -> finite (Q256.to_f64 q) /\ B (Q256.to_f64 q) = rndF Z.
Proof.
  intros Vq Err St [Z0 Z1].
  assert (Hb : bpow radix2 (-124) <= 1e-30).
  { apply Rle_trans with (bpow radix2 (-100)); [apply bpow_le; lia | bpow_num; apply Rle_trans with (/ 1000000000000000000000000000000); [apply Rinv_le_contravar; [lra | simpl; lra] | lra]]. }
  pose proof (bpow_gt_0 radix2 (-124)) as Hb0.
  assert (HE : Rabs (qval q - Z) <= 1e-30 * Z) by (apply Rle_trans with (1 := Err); apply Rmult_le_compat_r; lra).
  apply Rabs_le_inv in HE. destruct HE as [E1 E2].
  assert (Hq : 0 <= qval q <= 712) by (assert (1e-30 * Z <= 1e-30 * 711) by (apply Rmult_le_compat_l; lra); split; lra).
  assert (Hr : Rabs (rndF (qval q)) < bpow radix2 1024).
  { apply Rle_lt_trans with 1024.
    - apply rnd_bound; [change 1024 with (bpow radix2 10); apply fmt_bpow; lia | rewrite Rabs_pos_eq by lra; lra].
    - assert (10000 <= bpow radix2 1024) by (apply Rle_trans with (bpow radix2 20); [change (bpow radix2 20) with 1048576; lra | apply bpow_le; lia]). lra. }
  destruct (q_to_float_round q Vq Hr) as [Fq Bq]. split; [exact Fq | ]. rewrite Bq. apply St.
  apply Rabs_le. split.
  - apply Rabs_le_inv in Err. destruct Err as [Er1 Er2]. rewrite (Rabs_pos_eq Z) by lra. lra.
  - apply Rabs_le_inv in Err. destruct Err as [Er1 Er2]. rewrite (Rabs_pos_eq Z) by lra. lra.
Qed.

Lemma cmp_inf f : finite f -> asin_cmp f asinh_infinity = Some Lt.
Proof.
  intros Ff. assert (E : asinh_infinity = B754_infinity 53 1024 false) by (vm_compute; reflexivity).
  unfold asin_cmp. rewrite E. destruct f; try discriminate Ff; reflexivity.
Qed.

Lemma thr_ge_26 : bpow radix2 (-26) <= B asinh_is_x.
Proof. destruct is_x_val as [_ V]. rewrite V. bpow_num. interval with (i_prec 100). Qed.

Theorem asinh_entry_nan x : asin_is_nan x = true -> asinh_entry x = x.
Proof. intros H. unfold asinh_entry. rewrite H. reflexivity. Qed.

Theorem asinh_entry_inf s : asinh_entry (B754_infinity 53 1024 s) = B754_infinity 53 1024 s.
Proof. destruct s; vm_compute; reflexivity. Qed.
