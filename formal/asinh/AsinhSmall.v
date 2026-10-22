(** Below [ASINH_IS_X] (inclusive) the Rust returns [x], and [x] is [RN (arcsinh x)]:
    [x - arcsinh x <= x^3/6] stays below half the gap to the predecessor. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Binary64 Require Import Binary64Add IEEE64.
From Interval Require Import Tactic.
Require Import Ln1pLemmas AsinhWithin AsinhExpRed.
Open Scope R_scope.

(** The gap below a positive binary64. *)
Lemma gap_below a : fmtF a -> 0 < a ->
  bpow radix2 (mag radix2 a - 1) <= a < bpow radix2 (mag radix2 a) /\
  (a <> bpow radix2 (mag radix2 a - 1) -> bpow radix2 (mag radix2 a - 53) <= a - pred radix2 (FLT_exp emin prec) a) /\
  (a = bpow radix2 (mag radix2 a - 1) -> bpow radix2 (mag radix2 a - 54) <= a - pred radix2 (FLT_exp emin prec) a).
Proof.
  intros Fa Pa.
  pose proof (bpow_mag_le radix2 a (Rgt_not_eq _ _ Pa)) as Hlo. rewrite (Rabs_pos_eq a) in Hlo by lra.
  pose proof (bpow_mag_gt radix2 a) as Hhi. rewrite (Rabs_pos_eq a) in Hhi by lra.
  repeat split; try assumption.
  - intros Hn. rewrite (pred_eq_pos radix2 (FLT_exp emin prec) a (Rlt_le _ _ Pa)). unfold pred_pos.
    destruct (Req_bool_spec a (bpow radix2 (mag radix2 a - 1))) as [E | N]; [exfalso; apply Hn; exact E | ].
    rewrite (ulp_neq_0 radix2 (FLT_exp emin prec) a (Rgt_not_eq _ _ Pa)). unfold cexp, FLT_exp.
    replace (a - (a - bpow radix2 (Z.max (mag radix2 a - prec) emin))) with (bpow radix2 (Z.max (mag radix2 a - prec) emin)) by ring.
    apply bpow_le. unfold prec. apply Z.le_max_l.
  - intros E. rewrite (pred_eq_pos radix2 (FLT_exp emin prec) a (Rlt_le _ _ Pa)). unfold pred_pos.
    destruct (Req_bool_spec a (bpow radix2 (mag radix2 a - 1))) as [E' | N]; [ | exfalso; apply N; exact E].
    unfold FLT_exp. replace (a - (a - bpow radix2 (Z.max (mag radix2 a - 1 - prec) emin))) with (bpow radix2 (Z.max (mag radix2 a - 1 - prec) emin)) by ring.
    apply bpow_le. unfold prec. 
    apply Z.le_trans with (mag radix2 a - 1 - 53)%Z; [lia | apply Z.le_max_l].
Qed.

Lemma cube_mono a t : 0 <= a -> a <= t -> a * a * a <= t * t * t.
Proof.
  intros Ha Hat. assert (H1 : a * a <= t * t) by (apply Rmult_le_compat; lra).
  apply Rmult_le_compat; [apply Rmult_le_pos; lra | lra | exact H1 | exact Hat].
Qed.

Definition ThrT : R := IZR 3247657313705851 * bpow radix2 (-77).

Lemma bpm1 : bpow radix2 (-1) = / 2.
Proof. bpow_num. reflexivity. Qed.

Lemma bpe1 e : bpow radix2 (e - 1) = bpow radix2 e / 2.
Proof. replace (e - 1)%Z with (e + -1)%Z by ring. rewrite bpow_plus, bpm1. reflexivity. Qed.

Lemma bpe e k : bpow radix2 (e - k) = bpow radix2 e * bpow radix2 (- k).
Proof. replace (e - k)%Z with (e + - k)%Z by ring. apply bpow_plus. Qed.

Lemma thr_facts : ThrT < bpow radix2 (-25) /\ ThrT * ThrT * ThrT / 6 < bpow radix2 (-79) /\ 0 < ThrT <= 1.
Proof.
  unfold ThrT. bpow_num. split; [ | split]; [interval with (i_prec 100) | interval with (i_prec 100) | split; interval with (i_prec 100)].
Qed.

Lemma small_round_below a : fmtF a -> 0 < a -> a <= ThrT -> rndF (arcsinh a) = a.
Proof.
  intros Fa Pa HT.
  destruct thr_facts as [Tlt [Tcube [Tp Tle1]]].
  destruct (gap_below a Fa Pa) as [[Hlo Hhi] [GN GP]].
  set (ex := mag radix2 a) in *.
  assert (Hex : (ex <= -25)%Z).
  { apply (mag_le_bpow radix2 a (-25) (Rgt_not_eq _ _ Pa)). rewrite Rabs_pos_eq by lra. lra. }
  assert (Hy1 : arcsinh a <= a) by (apply arcsinh_le_id; lra).
  assert (Hy2 : a - a * a * a / 6 <= arcsinh a) by (apply arcsinh_ge_cubic; split; lra).
  apply Rle_antisym.
  - apply round_le_generic; [exact _ | exact _ | exact Fa | exact Hy1].
  - apply (round_N_ge_midp radix2 (FLT_exp emin prec) ne a (arcsinh a) Fa).
    set (P := bpow radix2 ex) in *.
    assert (HP : 0 < P) by apply bpow_gt_0.
    assert (Hb54 : bpow radix2 (ex - 54) = P * bpow radix2 (-54)) by apply bpe.
    assert (Hb53 : bpow radix2 (ex - 53) = P * bpow radix2 (-53)) by apply bpe.
    assert (Hm1 : bpow radix2 (ex - 1) = P * / 2) by (rewrite bpe1; reflexivity).
    assert (Hc : a * a * a / 6 < (a - pred radix2 (FLT_exp emin prec) a) / 2).
    { destruct (Req_dec a (bpow radix2 (ex - 1))) as [Epw | Enp].
      - (* a is a power of two *)
        specialize (GP Epw). rewrite Hb54 in GP.
        assert (Hbp : bpow radix2 (-54) = / 18014398509481984) by (bpow_num; reflexivity).
        assert (Hbp2 : bpow radix2 (-25) = / 33554432) by (bpow_num; reflexivity).
        assert (HPle : P <= bpow radix2 (-25)) by (apply bpow_le; lia).
        rewrite Hm1 in Epw. rewrite Hbp in GP. rewrite Hbp2 in HPle.
        assert (Ha : a = P / 2) by lra.
        assert (HP2 : P * P <= / 33554432 * / 33554432) by (apply Rmult_le_compat; lra).
        assert (Hcube : a * a * a / 6 = P * (P * P) / 48) by (replace a with (P / 2) by lra; field).
        rewrite Hcube. 
        assert (HPP : P * (P * P) <= P * (/ 33554432 * / 33554432)) by (apply Rmult_le_compat_l; lra).
        assert (HQ : P * (/ 33554432 * / 33554432) / 48 < P * / 18014398509481984 / 2) by (apply Rmult_lt_reg_r with 96; [lra | ]; nra).
        lra.
      - specialize (GN Enp). rewrite Hb53 in GN.
        destruct (Z.eq_dec ex (-25)) as [E25 | N25].
        + assert (HP25 : P = bpow radix2 (-25)) by (unfold P; rewrite E25; reflexivity).
          assert (H78 : P * bpow radix2 (-53) = 2 * bpow radix2 (-79)).
          { rewrite HP25, <- bpow_plus. replace (-25 + -53)%Z with (-78)%Z by reflexivity.
            replace (-79)%Z with (-78 - 1)%Z by reflexivity. rewrite bpe1. lra. }
          assert (Hcu : a * a * a <= ThrT * ThrT * ThrT) by (apply cube_mono; lra).
          lra.
        + assert (Hex2 : (ex <= -26)%Z) by lia.
          assert (HPle : P <= bpow radix2 (-26)) by (apply bpow_le; lia).
          assert (Hbp : bpow radix2 (-53) = / 9007199254740992) by (bpow_num; reflexivity).
          assert (Hb26 : bpow radix2 (-26) = / 67108864) by (bpow_num; reflexivity).
          rewrite Hbp in GN. rewrite Hb26 in HPle.
          assert (Hlt : a * a * a < P * P * P).
          { assert (a * a < P * P) by (apply Rmult_le_0_lt_compat; lra). apply Rmult_le_0_lt_compat; [nra | lra | exact H | exact Hhi]. }
          assert (HP2 : P * P <= / 67108864 * / 67108864) by (apply Rmult_le_compat; lra).
          assert (HPPP : P * P * P <= P * (/ 67108864 * / 67108864)) by (replace (P * P * P) with (P * (P * P)) by ring; apply Rmult_le_compat_l; lra).
          lra. }
    lra.
Qed.

Lemma arcsinh_opp x : arcsinh (- x) = - arcsinh x.
Proof.
  assert (E : - x = sinh (- arcsinh x)).
  { unfold sinh. rewrite exp_Ropp, Ropp_involutive. 
    assert (H : sinh (arcsinh x) = x) by apply sinh_arcsinh. unfold sinh in H.
    rewrite exp_Ropp in H. lra. }
  rewrite E, arcsinh_sinh. reflexivity.
Qed.

(** Below the threshold, in either sign, [arcsinh b] rounds to [b]. *)
Lemma small_signed b : fmtF b -> Rabs b <= ThrT -> rndF (arcsinh b) = b.
Proof.
  intros Fb H. destruct thr_facts as [_ [_ [Tp _]]].
  destruct (Rtotal_order b 0) as [Hn | [Hz | Hp]].
  - assert (Hnb : fmtF (- b)) by (apply generic_format_opp; exact Fb).
    pose proof (small_round_below (- b) Hnb ltac:(lra) ltac:(rewrite Rabs_left in H by lra; lra)) as R.
    replace b with (- (- b)) at 1 by ring. rewrite arcsinh_opp. rewrite round_NE_opp_ne. rewrite R. ring.
  - rewrite Hz, arcsinh_0. apply round_0. exact _.
  - apply small_round_below; [exact Fb | exact Hp | rewrite Rabs_pos_eq in H by lra; exact H].
Qed.
