(** atan2's reduction to [atan t]: the exponent of the larger magnitude, the
    exact scalings by powers of two, and the double-word quotient
    [t = n/d = th + tl] (docs/atan2.md section 3). *)
From Coq Require Import Reals ZArith Lia Lra Psatz List.
From Flocq Require Import Core Mult_error Sterbenz IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add Binary64Mul IEEE64 IEEE64Add IEEE64Mul IEEE64Eft Grid Encodings RoundingCore.
From Interval Require Import Tactic.
Require Import Ln1pLemmas AsinTables AsinKernel AsinSqrtStep AsinNormal AsinSeriesSmall AsinSegment AsinEntry
  Atan2Tables Atan2Kernel.
Open Scope R_scope.

(** A subnormal encoding's value. *)
Lemma sub_val n : (0 < n < 2 ^ 52)%Z ->
  finite (b64_of_bits n) /\ B (b64_of_bits n) = IZR n * bpow radix2 (-1074).
Proof.
  intros Hn. unfold b64_of_bits, binary_float_of_bits. rewrite B2R_FF2B, is_finite_FF2B.
  unfold binary_float_of_bits_aux.
  assert (Hs : split_bits 52 11 n = (false, n, 0%Z)).
  { unfold split_bits.
    assert (E1 : (2 ^ 52 * 2 ^ 11 <=? n)%Z = false) by (apply Z.leb_gt; lia).
    change (Zpower 2 52) with (2 ^ 52)%Z. change (Zpower 2 11) with (2 ^ 11)%Z.
    rewrite E1, Z.mod_small by lia.
    rewrite (Z.div_small n (2 ^ 52)) by lia. reflexivity. }
  rewrite Hs. cbv iota.
  destruct n as [ | p | p]; [lia | | lia].
  split; [reflexivity | ]. unfold FF2R, F2R. cbn [Fnum Fexp cond_Zopp].
  f_equal. change (3 - 2 ^ (11 - 1) - (52 + 1))%Z with (-1074)%Z. reflexivity.
Qed.

(** [2^p] for [-1022 <= p <= 1023] is the encoding the Rust builds. *)
Lemma pow2_val p : (-1022 <= p <= 1023)%Z -> finite (atan2_pow2 p) /\ B (atan2_pow2 p) = bpow radix2 p.
Proof.
  intros Hp. unfold atan2_pow2, aw.
  assert (E : Z.shiftl (1023 + p) 52 = join_bits 52 11 false 0 (1023 + p)).
  { rewrite join_eq, Z.shiftl_mul_pow2 by lia. lia. }
  rewrite E. destruct (join_val 0 (1023 + p) ltac:(lia) ltac:(lia)) as [F V].
  split; [exact F | ]. rewrite V. replace (IZR (0 + 2 ^ 52)) with (bpow radix2 52) by reflexivity.
  rewrite <- bpow_plus. f_equal. lia.
Qed.

(** A finite encoding's exponent field is below 2047. *)
Lemma bits_exp_lt n : (0 <= n < 2 ^ 63)%Z -> finite (b64_of_bits n) -> (n / 2 ^ 52 < 2047)%Z.
Proof.
  intros Hn F. destruct (Z_lt_ge_dec (n / 2 ^ 52) 2047) as [L | G]; [exact L | exfalso].
  assert (E : (n / 2 ^ 52 = 2047)%Z).
  { assert (n / 2 ^ 52 < 2048)%Z by (apply Z.div_lt_upper_bound; [lia | replace (2 ^ 52 * 2048)%Z with (2 ^ 63)%Z by reflexivity; lia]). lia. }
  revert F. unfold b64_of_bits, binary_float_of_bits. rewrite is_finite_FF2B. unfold binary_float_of_bits_aux.
  assert (Hs : split_bits 52 11 n = (false, (n mod 2 ^ 52)%Z, 2047%Z)).
  { unfold split_bits.
    assert (E1 : (2 ^ 52 * 2 ^ 11 <=? n)%Z = false) by (apply Z.leb_gt; lia).
    change (Zpower 2 52) with (2 ^ 52)%Z. change (Zpower 2 11) with (2 ^ 11)%Z.
    rewrite E1, E. f_equal. }
  rewrite Hs. cbv iota.
  replace (Zeq_bool 2047 0) with false by reflexivity.
  replace (Zeq_bool 2047 (2 ^ 11 - 1)) with true by reflexivity.
  destruct (n mod 2 ^ 52)%Z; simpl; discriminate.
Qed.

(** The Rust's exponent of a positive finite number: [2^e <= x < 2^(e+1)]. *)
Lemma exponent_ok x : finite x -> 0 < B x ->
  exists e, atan2_exponent x = e /\ (-1074 <= e <= 1023)%Z /\ bpow radix2 e <= B x < bpow radix2 (e + 1).
Proof.
  intros Fx Px.
  destruct (abs_split x Fx) as [n0 [R0 [_ [Fa [Na Hs]]]]].
  destruct Hs as [[Hb E] | [Hb E]]; [ | exfalso; lra].
  set (n := bits_of_b64 x) in *. subst n0.
  assert (Hx : x = b64_of_bits n) by (symmetry; apply bits_round).
  assert (Hshift : forall k, (0 <= k)%Z -> Z.shiftr n k = (n / 2 ^ k)%Z) by (intros k Hk; apply Z.shiftr_div_pow2; exact Hk).
  unfold atan2_exponent. fold n.
  rewrite Hshift by lia.
  destruct (Z_lt_ge_dec n (2 ^ 52)) as [Sub | Nor].
  - assert (E0 : (n / 2 ^ 52 = 0)%Z) by (apply Z.div_small; lia).
    rewrite E0. replace (0 =? 0)%Z with true by reflexivity. cbv iota zeta.
    assert (Hn0 : (0 < n)%Z).
    { destruct (Z.eq_dec n 0) as [Z0 | NZ]; [exfalso | lia].
      rewrite Z0 in E. replace (b64_of_bits 0) with (B754_zero 53 1024 false) in E by (vm_compute; reflexivity). simpl in E. lra. }
    destruct (sub_val n ltac:(lia)) as [Fs Vs]. rewrite Vs in E.
    assert (Hland : Z.land n (2 ^ 52 - 1) = n).
    { replace (2 ^ 52 - 1)%Z with (Z.ones 52) by reflexivity. rewrite Z.land_ones by lia. apply Z.mod_small. lia. }
    rewrite Hland.
    pose proof (Z.log2_nonneg n) as Ln0. pose proof (proj1 (Z.log2_lt_pow2 n 52 Hn0) Sub) as Ln1.
    exists (Z.log2 n - 1074)%Z. split; [lia | ]. split.
    + split; lia.
    + destruct (Z.log2_spec n Hn0) as [L1 L2].
      assert (HL : bpow radix2 (Z.log2 n) <= IZR n) by (rewrite <- (IZR_Zpower radix2 (Z.log2 n)) by (apply Z.log2_nonneg); apply IZR_le; exact L1).
      assert (HU : IZR n < bpow radix2 (Z.log2 n + 1)) by (rewrite <- (IZR_Zpower radix2 (Z.log2 n + 1)) by (pose proof (Z.log2_nonneg n); lia); apply IZR_lt; exact L2).
      rewrite E. split.
      * replace (Z.log2 n - 1074)%Z with (Z.log2 n + -1074)%Z by ring. rewrite bpow_plus. apply Rmult_le_compat_r; [apply bpow_ge_0 | exact HL].
      * replace (Z.log2 n - 1074 + 1)%Z with ((Z.log2 n + 1) + -1074)%Z by ring. rewrite bpow_plus. apply Rmult_lt_compat_r; [apply bpow_gt_0 | exact HU].
  - assert (HE1 : (1 <= n / 2 ^ 52)%Z) by (apply Z.div_le_lower_bound; lia).
    pose proof (bits_exp_lt n R0 Fa) as HE2.
    set (Ef := (n / 2 ^ 52)%Z) in *. set (m := (n mod 2 ^ 52)%Z).
    assert (Hn : n = (Ef * 2 ^ 52 + m)%Z) by (unfold Ef, m; rewrite Z.mul_comm; apply Z.div_mod; lia).
    assert (Hm : (0 <= m < 2 ^ 52)%Z) by (unfold m; apply Z.mod_pos_bound; lia).
    destruct (join_val m Ef Hm ltac:(lia)) as [Fj Vj].
    assert (Hbn : n = join_bits 52 11 false m Ef) by (rewrite join_eq; exact Hn).
    rewrite <- Hbn in Vj. rewrite Vj in E.
    replace (Ef =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
    exists (Ef - 1023)%Z. split; [reflexivity | ]. split; [lia | ].
    rewrite E. replace (Ef - 1023 + 1)%Z with (Ef - 1022)%Z by ring.
    assert (HB : bpow radix2 (Ef - 1075) * bpow radix2 52 = bpow radix2 (Ef - 1023)) by (rewrite <- bpow_plus; f_equal; lia).
    assert (HB2 : bpow radix2 (Ef - 1075) * bpow radix2 53 = bpow radix2 (Ef - 1022)) by (rewrite <- bpow_plus; f_equal; lia).
    assert (H52 : IZR (m + 2 ^ 52) >= bpow radix2 52).
    { replace (bpow radix2 52) with (IZR (2 ^ 52)) by reflexivity. apply Rle_ge, IZR_le. lia. }
    assert (H53 : IZR (m + 2 ^ 52) < bpow radix2 53).
    { replace (bpow radix2 53) with (IZR (2 ^ 53)) by reflexivity. apply IZR_lt. lia. }
    pose proof (bpow_gt_0 radix2 (Ef - 1075)). split; nra.
Qed.

(** Multiplying by a power of two is exact unless it overflows or leaves the
    normal range downward. *)
Lemma mul_pow2_exact x p : finite x -> (-1022 <= p <= 1023)%Z -> 0 <= B x -> B x * bpow radix2 p <= bpow radix2 1000 ->
  ((0 <= p)%Z \/ bpow radix2 (-1022) <= B x * bpow radix2 p) ->
  finite (fmul x (atan2_pow2 p)) /\ B (fmul x (atan2_pow2 p)) = B x * bpow radix2 p.
Proof.
  intros Fx Hp H0 Hu Hn. destruct (pow2_val p Hp) as [FP VP].
  assert (Hb : bnd 1 1000 (B x * B (atan2_pow2 p))).
  { unfold bnd. rewrite VP. rewrite Rabs_pos_eq by (apply Rmult_le_pos; [exact H0 | apply bpow_ge_0]). change (IZR 1) with 1. lra. }
  destruct (fmul_bnd 1 1000 x (atan2_pow2 p) Fx FP ltac:(lia) ltac:(lia) ltac:(apply Z.pow_gt_1; lia) ltac:(lia) Hb) as [F [E _]].
  split; [exact F | ]. rewrite E, VP.
  apply round_generic; [exact _ | ].
  destruct Hn as [Pos | Nor].
  - destruct (FLT_format_generic radix2 emin prec (B x) (B_fmt x)) as [f Hf Hm He].
    apply generic_format_FLT. apply (FLT_spec radix2 emin prec _ (Float radix2 (Fnum f) (Fexp f + p))).
    + rewrite Hf. unfold F2R. simpl. rewrite bpow_plus. ring.
    + simpl. exact Hm.
    + simpl. unfold emin in *. lia.
  - destruct (Req_dec (B x) 0) as [Z0 | NZ].
    + rewrite Z0, Rmult_0_l. apply generic_format_0.
    + apply mult_bpow_exact_FLT; [apply B_fmt | ].
      assert (M : (-1021 <= mag radix2 (B x * bpow radix2 p))%Z).
      { apply mag_ge_bpow. rewrite Rabs_pos_eq by (apply Rmult_le_pos; [exact H0 | apply bpow_ge_0]).
        replace (-1021 - 1)%Z with (-1022)%Z by reflexivity. exact Nor. }
      rewrite mag_mult_bpow in M by exact NZ. unfold emin, prec. lia.
Qed.

(** [x 2^-k] in two exact multiplications, for [x 2^-k] in [[2^-1000, 2]]. *)
Lemma scale_exact x k : finite x -> 0 <= B x -> (-1074 <= k <= 1023)%Z ->
  bpow radix2 (-1000) <= B x * bpow radix2 (- k) -> B x * bpow radix2 (- k) <= 2 ->
  finite (atan2_scale x k) /\ B (atan2_scale x k) = B x * bpow radix2 (- k).
Proof.
  intros Fx H0 Hk Hlo Hhi. unfold atan2_scale.
  set (half := Z.quot k 2) in *.
  pose proof (Z.quot_rem k 2 ltac:(lia)) as QR. pose proof (Z.rem_bound_abs k 2 ltac:(lia)) as RB.
  fold half in QR. rewrite Z.abs_lt in RB. rewrite (Z.abs_eq 2) in RB by lia.
  set (v := B x * bpow radix2 (- k)) in *.
  assert (Hv0 : 0 < v) by (pose proof (bpow_gt_0 radix2 (-1000)); lra).
  assert (Hy : B x * bpow radix2 (- half) = v * bpow radix2 (k - half)).
  { unfold v. rewrite Rmult_assoc, <- bpow_plus. f_equal. f_equal. ring. }
  assert (Hb512 : bpow radix2 (k - half) <= bpow radix2 512) by (apply bpow_le; lia).
  assert (Hb1000 : 2 * bpow radix2 512 <= bpow radix2 1000).
  { replace 1000%Z with (1 + 999)%Z by reflexivity. rewrite bpow_plus. change (bpow radix2 1) with 2.
    assert (bpow radix2 512 <= bpow radix2 999) by (apply bpow_le; lia). pose proof (bpow_ge_0 radix2 512). nra. }
  assert (B1 : B x * bpow radix2 (- half) <= bpow radix2 1000).
  { rewrite Hy. pose proof (bpow_ge_0 radix2 (k - half)). nra. }
  assert (N1 : (0 <= - half)%Z \/ bpow radix2 (-1022) <= B x * bpow radix2 (- half)).
  { destruct (Z_le_gt_dec 0 (- half)) as [P | P]; [left; exact P | right].
    assert (Hkh : (0 <= k - half)%Z) by lia.
    assert (1 <= bpow radix2 (k - half)) by (change 1 with (bpow radix2 0); apply bpow_le; exact Hkh).
    rewrite Hy. assert (bpow radix2 (-1022) <= bpow radix2 (-1000)) by (apply bpow_le; lia). nra. }
  destruct (mul_pow2_exact x (- half) Fx ltac:(lia) H0 B1 N1) as [F1 V1].
  assert (H1 : 0 <= B (fmul x (atan2_pow2 (- half)))) by (rewrite V1; apply Rmult_le_pos; [exact H0 | apply bpow_ge_0]).
  assert (Hy2 : B x * bpow radix2 (- half) * bpow radix2 (- (k - half)) = v).
  { unfold v. rewrite Rmult_assoc, <- bpow_plus. f_equal. f_equal. ring. }
  assert (B2 : B (fmul x (atan2_pow2 (- half))) * bpow radix2 (- (k - half)) <= bpow radix2 1000).
  { rewrite V1, Hy2. apply Rle_trans with 2; [exact Hhi | ]. apply Rle_trans with (2 * bpow radix2 512); [ | exact Hb1000].
    pose proof (bpow_ge_0 radix2 512). assert (1 <= bpow radix2 512) by (change 1 with (bpow radix2 0); apply bpow_le; lia). nra. }
  assert (N2 : (0 <= - (k - half))%Z \/ bpow radix2 (-1022) <= B (fmul x (atan2_pow2 (- half))) * bpow radix2 (- (k - half))).
  { destruct (Z_le_gt_dec 0 (- (k - half))) as [P | P]; [left; exact P | right].
    rewrite V1, Hy2. apply Rle_trans with (bpow radix2 (-1000)); [apply bpow_le; lia | exact Hlo]. }
  destruct (mul_pow2_exact (fmul x (atan2_pow2 (- half))) (- (k - half)) F1 ltac:(lia) H1 B2 N2) as [F2 V2].
  split; [exact F2 | ]. rewrite V2, V1, Hy2. reflexivity.
Qed.

(** [atan2_fast] split at the reduced argument: the ratio's double-word [(th, tl)], then
    the series and the form. *)
Definition atan2_ratio (n d : f64) : f64 * f64 :=
  let e := atan2_exponent d in
  let ns := atan2_scale n e in
  let ds := atan2_scale d e in
  let q := fdiv ns ds in
  let '(p, pe) := two_prod64 q ds in
  let residual := fsub (fsub ns p) pe in
  fast_two_sum64 q (fdiv residual ds).

Definition atan2_post (th tl : f64) (f : form) : (f64 * f64) * (f64 * f64) :=
  let '(ph, pl) := atan2_series th tl in
  let '(hh, hl) := two_sum64 (aw (fst atan2_half_pi)) (aw (snd atan2_half_pi)) in
  let y :=
    match f with
    | Phi => (ph, pl)
    | HalfPiMinus => sub64 hh hl ph pl
    | HalfPiPlus => add64 hh hl ph pl
    | PiMinus => let '(mh, ml) := mul_f64_64 hh hl asin_two in sub64 mh ml ph pl
    end in
  (y, (ph, pl)).

Lemma atan2_fast_split n d f : atan2_fast n d f = let '(th, tl) := atan2_ratio n d in atan2_post th tl f.
Proof.
  unfold atan2_fast, atan2_ratio, atan2_post. cbv zeta.
  match goal with |- context [two_prod64 ?a ?b] => destruct (two_prod64 a b) as [p pe] end.
  reflexivity.
Qed.

(** A positive value at most [1 + 2^-104], rounded: at most [1], within [2^-53]. *)
Lemma rn_unit t : bpow radix2 (-1022) <= t -> t <= 1 + bpow radix2 (-104) ->
  rndF t <= 1 /\ Rabs (rndF t - t) <= bpow radix2 (-53).
Proof.
  intros L U. pose proof (bpow_gt_0 radix2 (-1022)) as P.
  destruct (Rlt_le_dec t 1) as [Lt | Ge].
  - assert (R : Rabs (rndF t - t) <= bpow radix2 (-53) * Rabs t).
    { change (rndF t) with (RNE t). apply rnd_rel. rewrite Rabs_pos_eq by lra. exact L. }
    rewrite (Rabs_pos_eq t) in R by lra.
    split.
    + apply Rle_trans with (rndF 1); [apply round_le; [exact _ | exact _ | lra] | ].
      rewrite round_generic; [lra | exact _ | apply fmt_bpow with (e := 0%Z); lia].
    + assert (bpow radix2 (-53) * t <= bpow radix2 (-53)) by (pose proof (bpow_ge_0 radix2 (-53)); nra). lra.
  - assert (R1 : rndF t = 1).
    { apply Rle_antisym.
      + apply (round_N_le_midp radix2 (FLT_exp emin prec) ne 1 t); [apply fmt_bpow with (e := 0%Z); lia | ].
        rewrite (succ_eq_pos radix2 (FLT_exp emin prec) 1 ltac:(lra)).
        rewrite (ulp_neq_0 radix2 (FLT_exp emin prec) 1 ltac:(lra)).
        assert (cexp radix2 (FLT_exp emin prec) 1 = (-52)%Z) as Hc.
        { unfold cexp. rewrite (mag_unique_pos radix2 1 1) by (change (bpow radix2 (1 - 1)) with 1; change (bpow radix2 1) with 2; lra). unfold FLT_exp, emin, prec. lia. }
        rewrite Hc.
        assert (bpow radix2 (-104) < / 2 * bpow radix2 (-52)).
        { replace (-52)%Z with (-104 + 52)%Z by reflexivity. rewrite bpow_plus.
          assert (4 <= bpow radix2 52) by (change 4 with (bpow radix2 2); apply bpow_le; lia).
          pose proof (bpow_gt_0 radix2 (-104)). nra. }
        lra.
      + rewrite <- (round_generic radix2 (FLT_exp emin prec) (Znearest ne) 1) at 1; [apply round_le; [exact _ | exact _ | lra] | apply fmt_bpow with (e := 0%Z); lia]. }
    rewrite R1. split; [lra | ].
    assert (bpow radix2 (-104) <= bpow radix2 (-53)) by (apply bpow_le; lia). apply Rabs_le. split; lra.
Qed.

(** The ratio on scaled operands. *)
Definition ratio_pair (ns ds : f64) : f64 * f64 :=
  let q := fdiv ns ds in
  let '(p, pe) := two_prod64 q ds in
  let residual := fsub (fsub ns p) pe in
  fast_two_sum64 q (fdiv residual ds).

Lemma atan2_ratio_pair n d : atan2_ratio n d = ratio_pair (atan2_scale n (atan2_exponent d)) (atan2_scale d (atan2_exponent d)).
Proof. reflexivity. Qed.

(** A value that is zero or normal, rounded: a relative error. *)
Lemma rn_rel_ex x : (x = 0 \/ bpow radix2 (-1022) <= Rabs x) -> exists d, Rabs d <= bpow radix2 (-53) /\ rndF x = x * (1 + d).
Proof.
  intros [Z | N].
  - exists 0. rewrite Z, round_0 by exact _. rewrite Rabs_R0. split; [apply bpow_ge_0 | ring].
  - pose proof (rnd_rel x N) as R. change (RNE x) with (rndF x) in R.
    assert (x <> 0) by (intros Z; rewrite Z, Rabs_R0 in N; pose proof (bpow_gt_0 radix2 (-1022)); lra).
    exists ((rndF x - x) / x). split.
    + unfold Rdiv. rewrite Rabs_mult, Rabs_Rinv by exact H.
      assert (Abs : 0 < Rabs x) by (apply Rabs_pos_lt; exact H).
      apply (Rmult_le_reg_r (Rabs x)); [exact Abs | ]. rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra. exact R.
    + field. exact H.
Qed.

Lemma bpow_cancel e : bpow radix2 e * bpow radix2 (- e) = 1.
Proof. rewrite <- bpow_plus. replace (e + - e)%Z with 0%Z by ring. reflexivity. Qed.

Lemma grid_fmt_a m x : fmtF x -> (x = 0 \/ bpow radix2 m <= Rabs x) -> on_grid (m - 52) x.
Proof. intros F H. apply (grid_fmt_bound (FLT_exp emin prec) m x); [intros e; unfold FLT_exp, emin, prec; lia | exact F | exact H]. Qed.

Lemma rndF_bpow_le e x : (-1074 <= e)%Z -> bpow radix2 e <= x -> bpow radix2 e <= rndF x.
Proof.
  intros He H. rewrite <- (rnd_bpow e He) at 1. apply round_le; [exact _ | exact _ | exact H].
Qed.

Lemma prod_bound a b eps : 0 <= eps -> eps <= / 1000000000 -> Rabs a <= eps -> Rabs b <= eps -> Rabs ((1 + a) * (1 + b)) <= 1.0001.
Proof.
  intros E0 E1 Ha Hb. apply Rabs_le_inv in Ha as [A1 A2]. apply Rabs_le_inv in Hb as [B1 B2].
  apply Rabs_le. split; nra.
Qed.

Lemma tl_small th tl t eps : 0 < eps -> eps <= / 1000000000 -> t = th + tl -> 0 < t -> Rabs (th - t) <= eps * t -> 0 < th ->
  Rabs tl <= 2 * eps * th.
Proof.
  intros E0 E1 Ht Tp R Th. apply Rabs_le_inv in R as [R1 R2]. apply Rabs_le. split; nra.
Qed.

Lemma ratio_core ns ds : finite ns -> finite ds -> 1 <= B ds < 2 ->
  bpow radix2 (-901) <= B ns / B ds -> B ns / B ds <= 1 ->
  exists th tl, ratio_pair ns ds = (th, tl) /\ finite th /\ finite tl /\ B th = rndF (B th + B tl) /\
    Rabs (B tl) <= bpow radix2 (-52) * B th /\ Rabs (B tl) <= bpow radix2 (-53) /\ B th <= 1 /\ bpow radix2 (-902) <= B th /\
    Rabs (B th + B tl - B ns / B ds) <= bpow radix2 (-104) * (B ns / B ds) /\
    (bpow radix2 (-8) <= B ns / B ds -> on_grid (-211) (B tl)).
Proof.
  intros Fns Fds [Hds1 Hds2] Hlo Hhi.
  set (tt := B ns / B ds) in *.
  assert (Pds : 0 < B ds) by lra.
  pose proof (bpow_gt_0 radix2 (-901)) as P901.
  assert (Htt0 : 0 < tt) by lra.
  assert (Hns : B ns = tt * B ds) by (unfold tt; field; lra).
  assert (Pns : 0 < B ns) by (rewrite Hns; nra).
  assert (Hnsb : bpow radix2 (-901) <= B ns) by (rewrite Hns; nra).
  assert (P1022 : bpow radix2 (-1022) <= bpow radix2 (-901)) by (apply bpow_le; lia).
  (* q = RN(tt) *)
  assert (Hbq : bnd 1 0 tt) by (apply bnd0; change (IZR 1) with 1; rewrite Rabs_pos_eq by lra; exact Hhi).
  destruct (fdiv_bnd 1 0 ns ds Fns ltac:(lra) ltac:(lia) ltac:(lia) ltac:(apply Z.pow_gt_1; lia) ltac:(lia) Hbq) as [Fq [Eq Bq]].
  set (q := fdiv ns ds) in *.
  assert (Eq' : B q = rndF tt) by exact Eq.
  assert (Hq1 : bpow radix2 (-901) <= B q) by (rewrite Eq'; apply rndF_bpow_le; [lia | exact Hlo]).
  assert (Hq2 : B q <= 1).
  { rewrite Eq'. apply Rle_trans with (rndF 1); [apply round_le; [exact _ | exact _ | exact Hhi] | ].
    rewrite round_generic; [lra | exact _ | apply fmt_bpow with (e := 0%Z); lia]. }
  assert (Ntt : bpow radix2 (-1022) <= Rabs tt) by (rewrite Rabs_pos_eq by lra; lra).
  destruct (rn_rel_ex tt (or_intror Ntt)) as [d0 [Hd0 Eq0]].
  rewrite <- Eq' in Eq0. set (eps := bpow radix2 (-53)) in *.
  assert (Peps : 0 < eps) by (subst eps; apply bpow_gt_0).
  assert (Heps : eps <= / 1000000000) by (subst eps; bpow_num; interval with (i_prec 100)).
  (* q ds = ns (1 + d0) *)
  assert (Hqds : B q * B ds = B ns * (1 + d0)) by (rewrite Eq0, Hns; ring).
  (* the exact product *)
  assert (Hdom : in_two_prod_domain (B q) (B ds)).
  { right. rewrite Rabs_pos_eq by nra. apply Rle_trans with (bpow radix2 (-901)); [apply bpow_le; lia | nra]. }
  pose proof (two_prod_ieee 0 1 q ds Fq Fds ltac:(rewrite Rabs_pos_eq by lra; change (bpow radix2 0) with 1; lra)
    ltac:(rewrite Rabs_pos_eq by lra; change (bpow radix2 1) with 2; lra) ltac:(lia) ltac:(lia) ltac:(lia) Hdom) as TP.
  destruct (two_prod64 q ds) as [p pe] eqn:Etp. destruct TP as [Fp [Fpe [Ep Esum]]].
  assert (Hqd0 : bpow radix2 (-1022) <= Rabs (B q * B ds)).
  { rewrite Rabs_pos_eq by nra. apply Rle_trans with (bpow radix2 (-901)); [exact P1022 | nra]. }
  destruct (rn_rel_ex (B q * B ds) (or_intror Hqd0)) as [d1 [Hd1 Ed1]]. rewrite <- Ep in Ed1.
  change (bpow radix2 (-53)) with eps in Hd1.
  assert (Hpns : B p = B ns * ((1 + d0) * (1 + d1))) by (rewrite Ed1, Hqds; ring).
  (* ns - p exact (Sterbenz) *)
  assert (Hd01 : Rabs ((1 + d0) * (1 + d1) - 1) <= 3 * eps).
  { assert (M1 : Rabs (d0 * d1) <= eps * eps) by (rewrite Rabs_mult; apply Rmult_le_compat; try apply Rabs_pos; assumption).
    replace ((1 + d0) * (1 + d1) - 1) with (d0 + d1 + d0 * d1) by ring.
    apply Rle_trans with (Rabs d0 + Rabs d1 + Rabs (d0 * d1)).
    - apply Rle_trans with (Rabs (d0 + d1) + Rabs (d0 * d1)); [apply Rabs_triang | ]. pose proof (Rabs_triang d0 d1). lra.
    - pose proof (Rmult_le_compat_l eps eps (/ 1000000000) (Rlt_le _ _ Peps) Heps) as ee. lra. }
  apply Rabs_le_inv in Hd01 as [Hd01a Hd01b].
  set (X := (1 + d0) * (1 + d1)) in *.
  assert (Pns2 : B ns <= 2) by (rewrite Hns; nra).
  assert (HX1 : 0.99 <= X) by lra. assert (HX2 : X <= 1.01) by lra.
  assert (Hster : fmtF (B ns - B p)).
  { apply (sterbenz radix2 (FLT_exp emin prec) (B ns) (B p) (B_fmt ns) (B_fmt p)). rewrite Hpns. split; nra. }
  assert (Hb1 : bnd 1 0 (B ns - B p)).
  { apply bnd0. change (IZR 1) with 1. rewrite Hpns. apply Rabs_le. split; nra. }
  destruct (fsub_bnd 1 0 ns p Fns Fp ltac:(lia) ltac:(lia) ltac:(apply Z.pow_gt_1; lia) ltac:(lia) Hb1) as [Fs1 [Es1 _]].
  rewrite round_generic in Es1 by (try exact _; exact Hster).
  (* the residual *)
  set (s1 := fsub ns p) in *.
  set (r := B ns - B q * B ds).
  assert (Hr : r = - tt * d0 * B ds) by (unfold r; rewrite Hqds, Hns; ring).
  assert (Hrs : B s1 - B pe = r) by (rewrite Es1; unfold r; lra).
  assert (Hrb : Rabs r <= eps * 2).
  { rewrite Hr. rewrite Rabs_mult, Rabs_mult, Rabs_Ropp, (Rabs_pos_eq tt) by lra. rewrite (Rabs_pos_eq (B ds)) by lra.
    pose proof (Rabs_pos d0). nra. }
  assert (Hb2 : bnd 1 0 (B s1 - B pe)).
  { apply bnd0. change (IZR 1) with 1. rewrite Hrs. apply Rle_trans with (eps * 2); [exact Hrb | lra]. }
  destruct (fsub_bnd 1 0 s1 pe Fs1 Fpe ltac:(lia) ltac:(lia) ltac:(apply Z.pow_gt_1; lia) ltac:(lia) Hb2) as [Fres [Eres _]].
  rewrite Hrs in Eres. set (resid := fsub s1 pe) in *.
  (* r lies on a grid, so it is zero or normal *)
  assert (Gns : on_grid (-901 - 52) (B ns)) by (apply grid_fmt_a; [apply B_fmt | right; rewrite Rabs_pos_eq by lra; exact Hnsb]).
  assert (Gq : on_grid (-901 - 52) (B q)) by (apply grid_fmt_a; [apply B_fmt | right; rewrite Rabs_pos_eq by lra; exact Hq1]).
  assert (Gds : on_grid (0 - 52) (B ds)) by (apply grid_fmt_a; [apply B_fmt | right; rewrite Rabs_pos_eq by lra; change (bpow radix2 0) with 1; lra]).
  assert (Gr : on_grid (-1005) r).
  { unfold r. replace (-1005)%Z with ((-901 - 52) + (0 - 52))%Z by reflexivity.
    apply grid_minus; [apply (grid_le (-901 - 52)); [lia | exact Gns] | apply grid_mult; assumption]. }
  assert (Hr0 : r = 0 \/ bpow radix2 (-1022) <= Rabs r).
  { destruct (Req_dec r 0) as [Z | NZ]; [left; exact Z | right].
    apply Rle_trans with (bpow radix2 (-1005)); [apply bpow_le; lia | exact (grid_nonzero _ _ Gr NZ)]. }
  destruct (rn_rel_ex r Hr0) as [a [Ha Ea]]. rewrite <- Eres in Ea.
  change (bpow radix2 (-53)) with eps in Ha.
  assert (Hr1 : r = 0 \/ bpow radix2 (-1005) <= Rabs r) by (destruct (Req_dec r 0) as [Z | NZ]; [left; exact Z | right; exact (grid_nonzero _ _ Gr NZ)]).
  assert (Ha' : Rabs a <= eps) by exact Ha.
  apply Rabs_le_inv in Ha' as [Ha1 Ha2]. 
  (* the quotient of the residual *)
  assert (HRb : Rabs (B resid) <= eps * 3).
  { rewrite Ea. replace (r * (1 + a)) with (r + r * a) by ring.
    apply Rle_trans with (Rabs r + Rabs (r * a)); [apply Rabs_triang | ].
    rewrite Rabs_mult. assert (Rabs a <= eps) by exact Ha. pose proof (Rabs_pos a). pose proof (Rabs_pos r).
    assert (Rabs r * Rabs a <= eps * 2 * eps) by (apply Rmult_le_compat; try assumption; try apply Rabs_pos; exact Hrb).
    nra. }
  assert (Hb3 : bnd 1 0 (B resid / B ds)).
  { apply bnd0. change (IZR 1) with 1. unfold Rdiv. rewrite Rabs_mult, Rabs_Rinv by lra. rewrite (Rabs_pos_eq (B ds)) by lra.
    pose proof (Rabs_pos (B resid)) as RR0.
    assert (Rabs (B resid) * / B ds <= Rabs (B resid)) by (apply Rmult_le_reg_r with (B ds); [lra | ]; rewrite Rmult_assoc, Rinv_l by lra; nra).
    nra. }
  destruct (fdiv_bnd 1 0 resid ds Fres ltac:(lra) ltac:(lia) ltac:(lia) ltac:(apply Z.pow_gt_1; lia) ltac:(lia) Hb3) as [Fql [Eql _]].
  set (ql := fdiv resid ds) in *.
  assert (HRn : B resid / B ds = 0 \/ bpow radix2 (-1022) <= Rabs (B resid / B ds)).
  { destruct Hr1 as [Z | NZ].
    - left. rewrite Ea, Z. field. lra.
    - right. rewrite Ea. unfold Rdiv. rewrite Rabs_mult, Rabs_Rinv, Rabs_mult by lra.
      rewrite (Rabs_pos_eq (B ds)) by lra.
      assert (H099 : 0.99 <= Rabs (1 + a)) by (rewrite Rabs_pos_eq by lra; lra).
      assert (P1005 : bpow radix2 (-1022) <= bpow radix2 (-1005) / 4) by (replace (-1022)%Z with (-1005 + -17)%Z by reflexivity; rewrite bpow_plus; assert (bpow radix2 (-17) <= / 4) by (bpow_num; interval with (i_prec 60)); pose proof (bpow_ge_0 radix2 (-1005)); nra).
      assert (Rabs r * Rabs (1 + a) >= bpow radix2 (-1005) * 0.99).
      { pose proof (Rmult_le_compat (bpow radix2 (-1005)) (Rabs r) 0.99 (Rabs (1 + a)) (bpow_ge_0 radix2 (-1005)) ltac:(lra) NZ H099) as M. lra. }
      assert (/ B ds >= / 2) by (apply Rle_ge, Rinv_le_contravar; lra).
      assert (0 <= Rabs r * Rabs (1 + a)) by (apply Rmult_le_pos; apply Rabs_pos).
      nra. }
  destruct (rn_rel_ex (B resid / B ds) HRn) as [b [Hb Eb]]. rewrite <- Eql in Eb.
  change (bpow radix2 (-53)) with eps in Hb.
  assert (Hb' : Rabs b <= eps) by exact Hb. apply Rabs_le_inv in Hb' as [Hbl1 Hbl2].
  assert (Hqlv : B ql = - (tt * d0 * ((1 + a) * (1 + b)))).
  { rewrite Eb, Ea, Hr. field. lra. }
  (* the fast sum *)
  assert (Hqge : 0.99 * tt <= B q).
  { rewrite Eq0. apply Rabs_le_inv in Hd0 as [D1 D2]. nra. }
  assert (Hqlb : Rabs (B ql) <= 1.01 * eps * tt).
  { rewrite Hqlv, Rabs_Ropp, Rabs_mult, Rabs_mult, (Rabs_pos_eq tt) by lra.
    assert (Rabs ((1 + a) * (1 + b)) <= 1.0001) by (apply prod_bound with (eps := eps); try assumption; lra).
    assert (Rabs d0 <= eps) by exact Hd0. pose proof (Rabs_pos d0). pose proof (Rabs_pos ((1 + a) * (1 + b))).
    assert (Rabs d0 * Rabs ((1 + a) * (1 + b)) <= eps * 1.0001) by (apply Rmult_le_compat; try assumption; try apply Rabs_pos).
    nra. }
  assert (Hql1021 : Rabs (B ql) <= bpow radix2 1021).
  { apply Rle_trans with 1; [nra | change 1 with (bpow radix2 0); apply bpow_le; lia]. }
  assert (Hq1021 : Rabs (B q) <= bpow radix2 1021).
  { rewrite Rabs_pos_eq by lra. apply Rle_trans with 1; [exact Hq2 | change 1 with (bpow radix2 0); apply bpow_le; lia]. }
  assert (Hqlq : Rabs (B ql) <= Rabs (B q)).
  { rewrite (Rabs_pos_eq (B q)) by lra. nra. }
  pose proof (fast_two_sum_ieee q ql Fq Fql Hq1021 Hql1021 (or_intror (or_introl Hqlq))) as FS.
  destruct (fast_two_sum64 q ql) as [th tl] eqn:Efs. destruct FS as [Fth [Ftl [Eth Esum2]]].
  assert (Hrp : ratio_pair ns ds = (th, tl)).
  { unfold ratio_pair. cbv zeta. fold q. rewrite Etp. fold s1. fold resid. fold ql. exact Efs. }
  (* the value of the sum *)
  assert (Ht : B th + B tl - tt = - (tt * d0 * (a + b + a * b))).
  { rewrite Esum2, Eq0, Hqlv. ring. }
  assert (Habc : Rabs (a + b + a * b) <= 3 * eps).
  { assert (M : Rabs (a * b) <= eps * eps) by (rewrite Rabs_mult; apply Rmult_le_compat; try apply Rabs_pos; assumption).
    apply Rle_trans with (Rabs a + Rabs b + Rabs (a * b)).
    - apply Rle_trans with (Rabs (a + b) + Rabs (a * b)); [apply Rabs_triang | ]. pose proof (Rabs_triang a b). lra.
    - pose proof (Rmult_le_compat_l eps eps (/ 1000000000) (Rlt_le _ _ Peps) Heps) as ee. assert (Rabs a <= eps) by exact Ha. assert (Rabs b <= eps) by exact Hb. lra. }
  assert (Hee : eps * eps = bpow radix2 (-106)) by (subst eps; rewrite <- bpow_plus; reflexivity).
  assert (Htb : Rabs (B th + B tl - tt) <= bpow radix2 (-104) * tt).
  { rewrite Ht, Rabs_Ropp, Rabs_mult, Rabs_mult, (Rabs_pos_eq tt) by lra.
    assert (Rabs d0 * Rabs (a + b + a * b) <= eps * (3 * eps)) by (apply Rmult_le_compat; try apply Rabs_pos; try assumption; exact Hd0).
    assert (b104 : bpow radix2 (-104) = 4 * bpow radix2 (-106)) by (replace (-104)%Z with (-106 + 2)%Z by reflexivity; rewrite bpow_plus; change (bpow radix2 2) with 4; ring).
    assert (bpow radix2 (-106) > 0) by apply bpow_gt_0. nra. }
  apply Rabs_le_inv in Htb as [Htb1 Htb2].
  set (t := B th + B tl) in *.
  assert (Hb104 : bpow radix2 (-104) <= / 1000000000) by (apply Rle_trans with (bpow radix2 (-30)); [apply bpow_le; lia | bpow_num; interval with (i_prec 60)]).
  assert (Ht1 : 0.99 * tt <= t) by nra.
  assert (Ht2 : t <= 1 + bpow radix2 (-104)) by nra.
  assert (Ht902 : bpow radix2 (-902) <= t).
  { assert (Hb902 : bpow radix2 (-901) = 2 * bpow radix2 (-902)) by (replace (-901)%Z with (-902 + 1)%Z by reflexivity; rewrite bpow_plus; change (bpow radix2 1) with 2; ring).
    pose proof (bpow_gt_0 radix2 (-902)) as P902. lra. }
  assert (Htn : bpow radix2 (-1022) <= t) by (apply Rle_trans with (bpow radix2 (-902)); [apply bpow_le; lia | exact Ht902]).
  destruct (rn_unit t Htn Ht2) as [Hth1 Hth2].
  assert (Hthv : B th = rndF t) by (rewrite Eth; f_equal; symmetry; exact Esum2).
  assert (Htl : B tl = t - B th) by (unfold t; ring).
  assert (Hrt : Rabs (B th - t) <= eps * Rabs t).
  { assert (Htn' : bpow radix2 (-1022) <= Rabs t) by (rewrite Rabs_pos_eq by (pose proof (bpow_gt_0 radix2 (-1022)); lra); exact Htn).
    pose proof (rnd_rel t Htn') as R. change (RNE t) with (rndF t) in R. rewrite <- Hthv in R. change (bpow radix2 (-53)) with eps in R. exact R. }
  rewrite (Rabs_pos_eq t) in Hrt by lra.
  exists th, tl. split; [exact Hrp | ]. split; [exact Fth | ]. split; [exact Ftl | ].
  split; [exact Hthv | ].
  split.
  { assert (E52 : bpow radix2 (-52) = 2 * eps) by (subst eps; replace (-52)%Z with (-53 + 1)%Z by reflexivity; rewrite bpow_plus; change (bpow radix2 1) with 2; ring).
    assert (Hthp : 0 < B th) by (rewrite Hthv; apply Rlt_le_trans with (bpow radix2 (-902)); [apply bpow_gt_0 | apply rndF_bpow_le; [lia | exact Ht902]]).
    rewrite E52. apply (tl_small (B th) (B tl) t eps Peps Heps eq_refl ltac:(lra) Hrt Hthp). }
  split.
  { rewrite Htl. rewrite Rabs_minus_sym. rewrite Hthv. exact Hth2. }
  split; [rewrite Hthv; exact Hth1 | ].
  split; [rewrite Hthv; apply rndF_bpow_le; [lia | exact Ht902] | ].
  split; [apply Rabs_le; split; assumption | ].
  (* the grid of tl when the ratio is at least 2^-8 *)
  intros Hge8.
  assert (Hns8 : bpow radix2 (-8) <= B ns) by (rewrite Hns; nra).
  assert (Hq9 : bpow radix2 (-9) <= B q).
  { assert (Hb9 : bpow radix2 (-8) = 2 * bpow radix2 (-9)) by (replace (-8)%Z with (-9 + 1)%Z by reflexivity; rewrite bpow_plus; change (bpow radix2 1) with 2; ring).
    pose proof (bpow_gt_0 radix2 (-9)). lra. }
  assert (Gns8 : on_grid (-8 - 52) (B ns)) by (apply grid_fmt_a; [apply B_fmt | right; rewrite Rabs_pos_eq by lra; exact Hns8]).
  assert (Gq9 : on_grid (-9 - 52) (B q)) by (apply grid_fmt_a; [apply B_fmt | right; rewrite Rabs_pos_eq by lra; exact Hq9]).
  assert (Gr8 : on_grid (-113) r).
  { unfold r. replace (-113)%Z with ((-9 - 52) + (0 - 52))%Z by reflexivity.
    apply grid_minus; [apply (grid_le (-8 - 52)); [lia | exact Gns8] | apply grid_mult; assumption]. }
  assert (Gres : on_grid (-113) (B resid)) by (rewrite Eres; exact (grid_round (FLT_exp emin prec) (Znearest ne) (-113) r Gr8)).
  assert (Gql : on_grid (-166) (B ql)).
  { destruct Hr1 as [Z | NZ].
    - assert (B resid = 0) by (rewrite Ea, Z; ring).
      assert (B ql = 0) by (rewrite Eb, H; field; lra).
      rewrite H0. apply grid_0.
    - assert (Rne : B resid <> 0).
      { rewrite Ea. apply Rmult_integral_contrapositive. split; [intros Z; rewrite Z, Rabs_R0 in NZ; pose proof (bpow_gt_0 radix2 (-1005)); lra | lra]. }
      pose proof (grid_nonzero _ _ Gres Rne) as Hg.
      assert (Hqlb8 : bpow radix2 (-114) <= Rabs (B ql)).
      { assert (Hrd : bpow radix2 (-114) <= Rabs (B resid / B ds)).
        { unfold Rdiv. rewrite Rabs_mult, Rabs_Rinv by lra. rewrite (Rabs_pos_eq (B ds)) by lra.
          assert (E114 : bpow radix2 (-113) = 2 * bpow radix2 (-114)) by (replace (-113)%Z with (-114 + 1)%Z by reflexivity; rewrite bpow_plus; change (bpow radix2 1) with 2; ring).
          assert (/ B ds >= / 2) by (apply Rle_ge, Rinv_le_contravar; lra).
          pose proof (bpow_gt_0 radix2 (-114)).
          pose proof (Rmult_le_compat (bpow radix2 (-113)) (Rabs (B resid)) (/ 2) (/ B ds) (bpow_ge_0 radix2 (-113)) ltac:(lra) Hg ltac:(lra)) as M. lra. }
        rewrite Eql. rewrite <- round_NE_abs by exact _. change (round radix2 (FLT_exp emin prec) (Znearest ne) (Rabs (B resid / B ds))) with (rndF (Rabs (B resid / B ds))).
        apply rndF_bpow_le; [lia | exact Hrd]. }
      replace (-166)%Z with (-114 - 52)%Z by reflexivity.
      apply grid_fmt_a; [apply B_fmt | right; exact Hqlb8]. }
  assert (Gth : on_grid (-9 - 52) (B th)).
  { apply grid_fmt_a; [apply B_fmt | right]. rewrite Hthv. rewrite Rabs_pos_eq.
    - apply rndF_bpow_le; [lia | ]. 
      assert (Hb9 : bpow radix2 (-8) = 2 * bpow radix2 (-9)) by (replace (-8)%Z with (-9 + 1)%Z by reflexivity; rewrite bpow_plus; change (bpow radix2 1) with 2; ring).
      pose proof (bpow_gt_0 radix2 (-9)). lra.
    - apply Rle_trans with (bpow radix2 (-902)); [apply bpow_ge_0 | apply rndF_bpow_le; [lia | exact Ht902]]. }
  assert (Htl2 : B tl = (B q + B ql) - B th) by lra.
  rewrite Htl2. apply (grid_le (-166) (-211)); [lia | ].
  apply grid_minus; [apply grid_plus; [apply (grid_le (-9 - 52)); [lia | exact Gq9] | exact Gql] | apply (grid_le (-9 - 52)); [lia | exact Gth]].
Qed.
