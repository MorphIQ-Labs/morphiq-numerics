(** Below [ASIN_IS_X] the Rust returns [x], and [x] is [RN (asin x)]: [asin x - x <=
    x^3 (1 + x^2)/6] stays below half an ulp of [x]. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Binary64 Require Import Binary64Add IEEE64 Grid.
From Interval Require Import Tactic.
Require Import Ln1pLemmas AsinTables AsinKernel AsinSqrtStep AsinSegment AsinWithin AsinFacts.
Open Scope R_scope.

(** [asin a <= a + a^3 (1 + a^2)/6] for [0 <= a <= 1/64]. *)
Lemma asin_upper a : 0 <= a <= / 64 -> asin a <= a + a * a * a * (1 + a * a) / 6.
Proof.
  intros [H0 H1]. set (w := a + a * a * a * (1 + a * a) / 6).
  assert (Ha2 : a * a <= / 4096) by nra.
  assert (Ha3 : 0 <= a * a * a <= / 262144).
  { split; [apply Rmult_le_pos; [apply Rmult_le_pos; lra | lra] | ].
    assert (Hm : a * a * a <= / 4096 * / 64) by (apply Rmult_le_compat; [apply Rmult_le_pos; lra | lra | exact Ha2 | exact H1]).
    lra. }
  assert (Hp : 0 <= a * a * a * (1 + a * a) / 6 <= / 1000).
  { assert (Hq : 0 <= a * a * a * (1 + a * a)) by (apply Rmult_le_pos; [lra | nra]).
    assert (Hr : a * a * a * (1 + a * a) <= / 262144 * (1 + / 4096)) by (apply Rmult_le_compat; [lra | nra | lra | lra]).
    split; lra. }
  assert (Hw : 0 <= w <= 1) by (split; unfold w; lra).
  pose proof (sin_taylor_pos w Hw) as [L _].
  assert (Hw3 : w * w * w <= a * a * a * (1 + a * a)).
  { assert (Hs : w = a * (1 + a * a * (1 + a * a) / 6)) by (unfold w; field).
    set (s := a * a * (1 + a * a) / 6) in *.
    assert (Hs0 : 0 <= s <= / 1000) by (split; unfold s; nra).
    assert (Hcube : (1 + s) * (1 + s) * (1 + s) <= 1 + a * a).
    { assert ((1 + s) * (1 + s) * (1 + s) <= 1 + 4 * s) by nra.
      assert (4 * s <= a * a) by (unfold s; nra). lra. }
    assert (w * w * w = a * a * a * ((1 + s) * (1 + s) * (1 + s))) by (rewrite Hs; ring).
    rewrite H. assert (0 <= a * a * a) by (apply Rmult_le_pos; [apply Rmult_le_pos; lra | lra]). nra. }
  assert (Hsw : a <= sin w) by (unfold w in *; nra).
  assert (Hv : -1 <= a <= 1) by (split; lra).
  pose proof (asin_bound a) as [A1 A2]. pose proof (sin_asin a Hv) as Hs.
  destruct (Rle_lt_dec (asin a) w) as [Hok | Hbad]; [exact Hok | exfalso].
  pose proof PI_RGT_0. pose proof one_le_half_pi.
  pose proof (sin_increasing_1 w (asin a) ltac:(lra) ltac:(lra) A1 A2 Hbad). lra.
Qed.

Lemma small_round a : fmtF a -> 0 < a -> a <= asin a ->
  asin a < a + / 2 * bpow radix2 (cexp radix2 (FLT_exp emin prec) a) -> rndF (asin a) = a.
Proof.
  intros Fa Ha Hge Hlt. apply Rle_antisym.
  - apply (round_N_le_midp radix2 (FLT_exp emin prec) ne a (asin a) Fa).
    rewrite (succ_eq_pos radix2 (FLT_exp emin prec) a (Rlt_le _ _ Ha)). rewrite (ulp_neq_0 radix2 (FLT_exp emin prec) a (Rgt_not_eq _ _ Ha)).
    lra.
  - apply round_ge_generic; [exact _ | exact _ | exact Fa | exact Hge].
Qed.

Lemma is_x_val : finite asin_is_x /\ B asin_is_x = IZR 3247657313705851 * bpow radix2 (-77).
Proof.
  destruct (word_ok_intro (0x3e57137449123ef6)%Z false 6495314627411702%positive 78%nat (3247657313705851)%Z 1%Z (-77)%Z
    eq_refl eq_refl ltac:(lia) eq_refl) as [F V].
  split; [exact F | exact V].
Qed.

(** Below the threshold the result is [x]: [asin x] rounds to [x]. *)
Theorem small_correct x : finite x -> 0 <= B x -> B x < B asin_is_x -> rndF (asin (B x)) = B x.
Proof.
  intros Fx H0 H1. destruct is_x_val as [Fi Vi]. rewrite Vi in H1.
  destruct (Req_dec (B x) 0) as [Hz | Hnz].
  - rewrite Hz, asin_0. apply round_0. exact _.
  - assert (Hpos : 0 < B x) by lra. set (a := B x) in *.
    assert (Hx0 : IZR 3247657313705851 * bpow radix2 (-77) < bpow radix2 (-25)) by (bpow_num; interval with (i_prec 100)).
    assert (Ha25 : Rabs a < bpow radix2 (-25)) by (rewrite Rabs_pos_eq by lra; lra).
    assert (Ha64 : a <= / 64).
    { assert (bpow radix2 (-25) <= / 64) by (bpow_num; interval with (i_prec 100)). lra. }
    pose proof (asin_upper a (conj (Rlt_le _ _ Hpos) Ha64)) as Hup.
    assert (Ha1 : a <= 1) by lra.
    pose proof (asin_ge a (conj (Rlt_le _ _ Hpos) Ha1)) as Hge.
    assert (Fa : fmtF a) by (apply B_fmt).
    apply small_round; [exact Fa | exact Hpos | exact Hge | ].
    set (ex := mag radix2 a).
    pose proof (bpow_mag_le radix2 a (Rgt_not_eq _ _ Hpos)) as Hlo. rewrite (Rabs_pos_eq a) in Hlo by lra.
    pose proof (bpow_mag_gt radix2 a) as Hhi. rewrite (Rabs_pos_eq a) in Hhi by lra.
    fold ex in Hlo, Hhi.
    assert (Hex : (ex <= -25)%Z) by (apply (mag_le_bpow radix2 a (-25) (Rgt_not_eq _ _ Hpos) Ha25)).
    unfold cexp. fold ex. unfold FLT_exp.
    assert (Hw : a * a * a * (1 + a * a) / 6 < / 2 * bpow radix2 (Z.max (ex - prec) emin)).
    { destruct (Z.eq_dec ex (-25)) as [E | E].
      - (* top binade below 2^-25: a is at most the grid point below the threshold *)
        assert (Hm : Z.max (ex - prec) emin = (-78)%Z) by (rewrite E; reflexivity).
        rewrite Hm. unfold generic_format, F2R in Fa. simpl in Fa.
        assert (Hc : cexp radix2 (FLT_exp emin prec) a = (-78)%Z) by (unfold cexp; fold ex; unfold FLT_exp; rewrite E; reflexivity).
        rewrite Hc in Fa.
        set (m := Ztrunc (scaled_mantissa radix2 (FLT_exp emin prec) a)) in *.
        assert (Hlt : IZR m < 6495314627411702).
        { assert (Hq : a * bpow radix2 78 = IZR m) by (rewrite Fa at 1; rewrite Rmult_assoc, <- bpow_plus; replace (-78 + 78)%Z with 0%Z by lia; simpl; ring).
          assert (E77 : bpow radix2 (-77) * bpow radix2 78 = 2) by (rewrite <- bpow_plus; change (-77 + 78)%Z with 1%Z; change (bpow radix2 1) with 2; reflexivity).
          pose proof (bpow_gt_0 radix2 78) as P78.
          assert (Ht : a * bpow radix2 78 < 6495314627411702) by nra.
          lra. }
        assert (Hm1 : (m <= 6495314627411701)%Z) by (apply lt_IZR in Hlt; lia).
        assert (Hle : IZR m <= 6495314627411701) by (apply IZR_le; exact Hm1).
        assert (Ha' : a <= 6495314627411701 * bpow radix2 (-78)) by (rewrite Fa at 1; bpow_num; nra).
        assert (Hp : 0 <= a) by lra.
        assert (Hc3 : a * a * a * (1 + a * a) / 6 <= (6495314627411701 * bpow radix2 (-78)) * (6495314627411701 * bpow radix2 (-78)) * (6495314627411701 * bpow radix2 (-78)) * (1 + (6495314627411701 * bpow radix2 (-78)) * (6495314627411701 * bpow radix2 (-78))) / 6).
        { set (T := 6495314627411701 * bpow radix2 (-78)) in *.
          assert (HT : 0 <= T) by (unfold T; apply Rmult_le_pos; [lra | apply bpow_ge_0]).
          assert (a * a <= T * T) by nra.
          assert (a * a * a <= T * T * T) by nra.
          assert (Hq : 0 <= a * a * a) by (apply Rmult_le_pos; [apply Rmult_le_pos; lra | lra]).
          assert (a * a * a * (a * a) <= T * T * T * (T * T)) by (apply Rmult_le_compat; [exact Hq | nra | assumption | assumption]).
          lra. }
        refine (Rle_lt_trans _ _ _ Hc3 _). bpow_num. interval with (i_prec 120).
      - assert (Hex' : (ex <= -26)%Z) by lia.
        assert (Hb : a < bpow radix2 (-26)) by (apply Rlt_le_trans with (bpow radix2 ex); [exact Hhi | apply bpow_le; exact Hex']).
        assert (Hq : a * a * (1 + a * a) / 6 <= bpow radix2 (-54)).
        { assert (Hb' : a < / 67108864) by (apply Rlt_le_trans with (bpow radix2 (-26)); [exact Hb | bpow_num; interval with (i_prec 100)]).
          assert (a * a < / 4503599627370496) by nra.
          bpow_num. nra. }
        assert (Hu : bpow radix2 (ex - 54) <= / 2 * bpow radix2 (Z.max (ex - prec) emin)).
        { replace (ex - 54)%Z with ((ex - 53) + (-1))%Z by lia. rewrite bpow_plus.
          assert (Hh : bpow radix2 (-1) = / 2) by (bpow_num; reflexivity).
          rewrite Hh.
          assert (bpow radix2 (ex - 53) <= bpow radix2 (Z.max (ex - prec) emin)) by (apply bpow_le; apply Z.le_max_l).
          lra. }
        assert (Hcube : a * a * a * (1 + a * a) / 6 <= a * bpow radix2 (-54)).
        { assert (a * (a * a * (1 + a * a) / 6) <= a * bpow radix2 (-54)) by (apply Rmult_le_compat_l; [lra | exact Hq]).
          lra. }
        assert (Hmul : a * bpow radix2 (-54) < bpow radix2 ex * bpow radix2 (-54)).
        { apply Rmult_lt_compat_r; [apply bpow_gt_0 | exact Hhi]. }
        rewrite <- bpow_plus in Hmul. replace (ex + -54)%Z with (ex - 54)%Z in Hmul by lia. lra. }
    lra.
Qed.
