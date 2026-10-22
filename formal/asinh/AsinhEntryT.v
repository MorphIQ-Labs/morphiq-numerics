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

Local Opaque asinh_fast asinh_accurate asinh_decide asinh_accurate_value asinh_logarithm asinh_large asinh_series.

Theorem asinh_entry_finite x : CoreMathH -> finite x ->
  finite (asinh_entry x) /\ B (asinh_entry x) = rndF (arcsinh (B x)).
Proof.
  intros CM Fx.
  assert (Hn : asin_is_nan x = false) by (destruct x; first [reflexivity | discriminate Fx]).
  unfold asinh_entry. rewrite Hn.
  destruct (abs_split x Fx) as [n0 [R0 [Ha [Fa [Na Hs]]]]].
  rewrite Ha. set (a := b64_of_bits n0) in *.
  assert (Hab : B a = Rabs (B x)).
  { destruct Hs as [[_ E] | [_ E]]; rewrite E; [rewrite Rabs_pos_eq by exact Na; reflexivity | rewrite Rabs_Ropp, Rabs_pos_eq by exact Na; reflexivity]. }
  destruct is_x_val as [Fi Vi]. change (IZR 3247657313705851 * bpow radix2 (-77)) with ThrT in Vi.
  assert (C1 : asin_cmp a asinh_is_x = Some (Rcompare (B a) (B asinh_is_x))).
  { unfold asin_cmp. rewrite (Bcompare_correct 53 1024 a asinh_is_x Fa Fi). reflexivity. }
  rewrite C1.
  destruct (Rcompare_spec (B a) (B asinh_is_x)) as [Hlt | Heq | Hgt].
  - timeout 20 cbv iota. split; [exact Fx | ].
    symmetry. apply small_signed; [apply B_fmt | ]. rewrite <- Hab. rewrite Vi in Hlt. timeout 20 lra.
  - timeout 20 cbv iota. split; [exact Fx | ].
    symmetry. apply small_signed; [apply B_fmt | ]. rewrite <- Hab. rewrite Vi in Heq. timeout 20 lra.
  - timeout 20 cbv iota. rewrite (cmp_inf a Fa). timeout 20 cbv iota.
    pose proof thr_ge_26 as T26.
    assert (L26 : bpow radix2 (-26) <= B a) by timeout 20 lra.
    pose proof (asinh_fast_ok a Fa L26) as FO.
    pose proof (arcsinh_range a Fa L26) as [HA1 HA2].
    set (y := asinh_fast a) in *.
    assert (Hv : exists v, finite v /\ B v = rndF (arcsinh (B a)) /\
      (match asinh_decide y with Some r => r | None => asinh_accurate a y end) = v).
    { destruct (asinh_decide y) as [r | ] eqn:Hd.
      - destruct FO as [Fh [Fl [Dw [L1 [L2 Er]]]]].
        destruct y as [yh yl]. cbn [fst snd] in *.
        assert (Er' : Rabs (arcsinh (B a) - (B yh + B yl)) <= bpow radix2 (-63) * Rabs (arcsinh (B a))).
        { rewrite Rabs_minus_sym, (Rabs_pos_eq (arcsinh (B a))) by timeout 20 lra. exact Er. }
        destruct (asinh_decide_some yh yl (arcsinh (B a)) r Fh Fl L1 L2 Dw Er' Hd) as [Hr HZ].
        exists r. rewrite Hr. split; [exact Fh | split; [symmetry; exact HZ | reflexivity]].
      - destruct (asinh_accurate_value_ok a (fst y) (snd y) Fa ltac:(destruct FO as [F _]; exact F) ltac:(destruct FO as [_ [F _]]; exact F) L26 FO) as [Vq Eq'].
        assert (HZr : 1e-9 <= arcsinh (B a) <= 711) by (split; timeout 20 lra).
        destruct (accurate_round_h _ (arcsinh (B a)) Vq Eq' (CM a Fa Hgt) HZr) as [Fv Bv].
        exists (Q256.to_f64 (asinh_accurate_value a y)). split; [exact Fv | split; [exact Bv | reflexivity]]. }
    destruct Hv as [v [Fv [Bv Ev]]]. rewrite Ev.
    assert (Pv : 0 < B v).
    { rewrite Bv. apply Rlt_le_trans with (bpow radix2 (-27)); [apply bpow_gt_0 | apply rndF_ge_bpow; [lia | ]].
      assert (bpow radix2 (-27) = / 134217728) by (bpow_num; reflexivity). timeout 20 lra. }
    destruct (with_sign_val v x Fv Pv Fx) as [Fws [Hp Hng]].
    split; [exact Fws | ].
    destruct Hs as [[Hb E] | [Hb E]].
    + rewrite (Hp (ex_intro _ n0 (conj Hb R0))), Bv, E. reflexivity.
    + rewrite (Hng (ex_intro _ n0 (conj Hb R0))), Bv, E, arcsinh_opp, round_NE_opp_ne. reflexivity.
Qed.
