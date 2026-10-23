(** asin's entry point end to end: every binary64 input, the sign handling
    through the encoding, the special values, and the two thresholds. *)
From Coq Require Import Reals ZArith Lia Lra Psatz List.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 RoundingCore RoundingTest Grid.
From Interval Require Import Tactic.
Require Import Ln1pLemmas AsinTables AsinKernel AsinSqrtStep AsinWithin AsinFacts AsinPath AsinCorrect AsinSmall.
Open Scope R_scope.

(** Setting the sign bit negates the value of an encoding. *)
Lemma split_hi n : (0 <= n < 2 ^ 63)%Z ->
  split_bits 52 11 (n + 2 ^ 63) = (true, snd (fst (split_bits 52 11 n)), snd (split_bits 52 11 n)) /\
  fst (fst (split_bits 52 11 n)) = false.
Proof.
  intros H. unfold split_bits. cbn [fst snd].
  assert (E1 : (2 ^ 52 * 2 ^ 11 <=? n + 2 ^ 63)%Z = true) by (apply Z.leb_le; lia).
  assert (E2 : (2 ^ 52 * 2 ^ 11 <=? n)%Z = false) by (apply Z.leb_gt; lia).
  rewrite E1, E2. split; [ | reflexivity].
  assert (M : ((n + 2 ^ 63) mod 2 ^ 52 = n mod 2 ^ 52)%Z).
  { replace (2 ^ 63)%Z with (2 ^ 11 * 2 ^ 52)%Z by reflexivity. rewrite Z.mod_add by lia. reflexivity. }
  assert (D : ((n + 2 ^ 63) / 2 ^ 52 = n / 2 ^ 52 + 2 ^ 11)%Z).
  { replace (2 ^ 63)%Z with (2 ^ 11 * 2 ^ 52)%Z by reflexivity. rewrite Z.div_add by lia. reflexivity. }
  rewrite M, D.
  pose proof (Z.mod_add (n / 2 ^ 52) 1 (2 ^ 11) ltac:(lia)) as Hm. rewrite Z.mul_1_l in Hm. rewrite Hm. reflexivity.
Qed.

Lemma fneg p z : F2R (Float radix2 (Z.neg p) z) = - F2R (Float radix2 (Z.pos p) z).
Proof. unfold F2R; simpl. replace (IZR (Z.neg p)) with (- IZR (Z.pos p)) by (rewrite <- opp_IZR; reflexivity). ring. Qed.

Lemma fnn p z : 0 <= F2R (Float radix2 (Z.pos p) z).
Proof. apply F2R_ge_0. simpl. lia. Qed.

Lemma bits_sign n : (0 <= n < 2 ^ 63)%Z ->
  (finite (b64_of_bits (n + 2 ^ 63)) <-> finite (b64_of_bits n)) /\
  (finite (b64_of_bits n) -> B (b64_of_bits (n + 2 ^ 63)) = - B (b64_of_bits n) /\ 0 <= B (b64_of_bits n)).
Proof.
  intros H. destruct (split_hi n H) as [S1 S2].
  unfold b64_of_bits, binary_float_of_bits. rewrite !is_finite_FF2B, !B2R_FF2B.
  unfold binary_float_of_bits_aux. rewrite S1.
  destruct (split_bits 52 11 n) as [[s m] e] eqn:Sp. cbn [fst snd] in S2, S1 |- *. subst s.
  destruct (Zeq_bool e 0); [destruct m | destruct (Zeq_bool e (2 ^ 11 - 1)); [destruct m | destruct (m + 2 ^ 52)%Z]];
    cbn [is_finite_FF FF2R cond_Zopp]; (split; [tauto | intros Fn]);
    first [ discriminate Fn | split; [exact (fneg _ _) | exact (fnn _ _)] | (split; [simpl; lra | simpl; lra]) ].
Qed.

Lemma bits_round x : b64_of_bits (bits_of_b64 x) = x.
Proof. unfold b64_of_bits, bits_of_b64. exact (binary_float_of_bits_of_binary_float 52 11 eq_refl eq_refl eq_refl x). Qed.

Lemma bits_range x : (0 <= bits_of_b64 x < 2 ^ 64)%Z.
Proof. exact (bits_of_binary_float_range 52 11 eq_refl eq_refl x). Qed.

Lemma land_sign m : (0 <= m < 2 ^ 63)%Z ->
  Z.land m (2 ^ 63) = 0%Z /\ Z.land (m + 2 ^ 63) (2 ^ 63) = (2 ^ 63)%Z.
Proof.
  intros H. split; apply Z.bits_inj'; intros k Hk; rewrite Z.land_spec, Z.pow2_bits_eqb by lia;
    destruct (63 =? k)%Z eqn:E.
  - apply Z.eqb_eq in E. subst k. rewrite Z.bits_0, Bool.andb_true_r.
    destruct (Z.testbit m 63) eqn:Tb; [ | reflexivity].
    apply Z.testbit_true in Tb; [ | lia]. rewrite Z.div_small in Tb by lia. discriminate Tb.
  - rewrite Bool.andb_false_r. symmetry. apply Z.bits_0.
  - apply Z.eqb_eq in E. subst k. rewrite Bool.andb_true_r.
    apply (proj2 (Z.testbit_true (m + 2 ^ 63) 63 ltac:(lia))).
    replace ((m + 2 ^ 63) / 2 ^ 63)%Z with 1%Z by (apply Z.div_unique_pos with (r := m); [split; lia | lia]).
    reflexivity.
  - rewrite Bool.andb_false_r. reflexivity.
Qed.


Lemma lor_sign v : (0 <= v < 2 ^ 63)%Z -> Z.lor v (2 ^ 63) = (v + 2 ^ 63)%Z.
Proof.
  intros H. destruct (land_sign v H) as [L _]. rewrite <- (Z.lxor_lor v (2 ^ 63) L). symmetry. apply Z.add_nocarry_lxor. exact L.
Qed.

(** The magnitude word: [x] is the encoding of [n0], negated when the sign bit is set. *)
Lemma abs_split x : finite x ->
  exists n0, (0 <= n0 < 2 ^ 63)%Z /\ aw (Z.land (bits_of_b64 x) (asin_sign_bit - 1)) = b64_of_bits n0 /\
    finite (b64_of_bits n0) /\ 0 <= B (b64_of_bits n0) /\
    ((bits_of_b64 x = n0 /\ B x = B (b64_of_bits n0)) \/
     (bits_of_b64 x = (n0 + 2 ^ 63)%Z /\ B x = - B (b64_of_bits n0))).
Proof.
  intros Fx. pose proof (bits_range x) as Hr. set (n := bits_of_b64 x) in *.
  assert (Hland : Z.land n (asin_sign_bit - 1) = (n mod 2 ^ 63)%Z).
  { unfold asin_sign_bit. replace (2 ^ 63 - 1)%Z with (Z.ones 63) by reflexivity. rewrite Z.land_ones by lia. reflexivity. }
  assert (Hx : x = b64_of_bits n) by (symmetry; apply bits_round).
  destruct (Z_lt_ge_dec n (2 ^ 63)) as [Lo | Hi].
  - assert (Fn : finite (b64_of_bits n)) by (rewrite <- Hx; exact Fx).
    exists n. rewrite Hland, Z.mod_small by lia. split; [lia | ]. split; [reflexivity | ].
    split; [exact Fn | ]. split.
    + exact (proj2 (proj2 (bits_sign n ltac:(lia)) Fn)).
    + left. split; [reflexivity | rewrite Hx; reflexivity].
  - set (n0 := (n - 2 ^ 63)%Z).
    assert (Hn : n = (n0 + 2 ^ 63)%Z) by (unfold n0; lia).
    assert (R0 : (0 <= n0 < 2 ^ 63)%Z) by (unfold n0; lia).
    assert (Fn : finite (b64_of_bits (n0 + 2 ^ 63))) by (rewrite <- Hn, <- Hx; exact Fx).
    destruct (bits_sign n0 R0) as [Hf Hb].
    assert (Fn0 : finite (b64_of_bits n0)) by (apply Hf; exact Fn).
    exists n0. rewrite Hland. replace (n mod 2 ^ 63)%Z with n0 by (apply Z.mod_unique_pos with (q := 1%Z); [split; lia | lia]).
    split; [exact R0 | ]. split; [reflexivity | ]. split; [exact Fn0 | ].
    destruct (Hb Fn0) as [Hneg Hnn]. split; [exact Hnn | ].
    right. split; [exact Hn | ]. rewrite Hx, Hn. exact Hneg.
Qed.

Lemma land_mask n : (0 <= n < 2 ^ 63)%Z -> Z.land n (asin_sign_bit - 1) = n.
Proof.
  intros H. unfold asin_sign_bit. replace (2 ^ 63 - 1)%Z with (Z.ones 63) by reflexivity.
  rewrite Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

(** [asin_with_sign v x] is [v] or [-v] by the sign bit of [x], for a positive finite [v]. *)
Lemma with_sign_val v x : finite v -> 0 < B v -> finite x ->
  finite (asin_with_sign v x) /\
  ((exists n0, bits_of_b64 x = n0 /\ (0 <= n0 < 2 ^ 63)%Z) -> asin_with_sign v x = v) /\
  ((exists n0, bits_of_b64 x = (n0 + 2 ^ 63)%Z /\ (0 <= n0 < 2 ^ 63)%Z) -> B (asin_with_sign v x) = - B v).
Proof.
  intros Fv Pv Fx.
  destruct (abs_split v Fv) as [nv [Rv [_ [Fnv [Nnv [[Hbv Bv] | [Hbv Bv]]]]]]]; [ | exfalso; lra].
  assert (Hv : v = b64_of_bits nv) by (rewrite <- Hbv; symmetry; apply bits_round).
  assert (Hland : Z.land (bits_of_b64 v) (asin_sign_bit - 1) = nv) by (rewrite Hbv; apply land_mask; exact Rv).
  assert (W : asin_with_sign v x = aw (Z.lor nv (Z.land (bits_of_b64 x) asin_sign_bit))) by
    (unfold asin_with_sign; rewrite Hland; reflexivity).
  destruct (abs_split x Fx) as [nx [Rx [_ [_ [_ [[Hbx _] | [Hbx _]]]]]]].
  - assert (L : Z.land (bits_of_b64 x) asin_sign_bit = 0%Z) by (rewrite Hbx; unfold asin_sign_bit; exact (proj1 (land_sign nx Rx))).
    rewrite L, Z.lor_0_r in W. assert (E : asin_with_sign v x = v) by (rewrite W; unfold aw; rewrite Hv; reflexivity).
    split; [rewrite E; exact Fv | ]. split.
    + intros _. exact E.
    + intros [n0 [Hn0 R0]]. exfalso. rewrite Hbx in Hn0. lia.
  - assert (L : Z.land (bits_of_b64 x) asin_sign_bit = (2 ^ 63)%Z) by (rewrite Hbx; unfold asin_sign_bit; exact (proj2 (land_sign nx Rx))).
    rewrite L, (lor_sign nv Rv) in W.
    destruct (bits_sign nv Rv) as [Hf Hb]. destruct (Hb Fnv) as [Hneg _].
    assert (E : asin_with_sign v x = b64_of_bits (nv + 2 ^ 63)) by (rewrite W; reflexivity).
    split; [rewrite E; apply Hf; exact Fnv | ]. split.
    + intros [n0 [Hn0 R0]]. exfalso. rewrite Hbx in Hn0. lia.
    + intros _. rewrite E, Hneg, <- Hv. reflexivity.
Qed.

Lemma half_pi_rn : finite asin_half_pi_f64 /\ B asin_half_pi_f64 = rndF (PI / 2).
Proof.
  destruct half_pi_words as [Fhi [_ [Vhi _]]].
  change asin_half_pi_f64 with (aw (fst asin_half_pi)).
  set (hi := aw (fst asin_half_pi)) in *.
  split; [exact Fhi | ].
  assert (Hb : 1 <= B hi < 2) by (rewrite Vhi; bpow_num; split; interval with (i_prec 80)).
  assert (Hmag : mag radix2 (B hi) = 1%Z :> Z).
  { apply mag_unique_pos. change (bpow radix2 (1 - 1)) with 1. change (bpow radix2 1) with 2. exact Hb. }
  assert (Hulp : ulp radix2 (FLT_exp (-1074) 53) (B hi) = bpow radix2 (-52)).
  { rewrite ulp_neq_0 by lra. unfold cexp. rewrite Hmag. reflexivity. }
  assert (Hlow : B hi <= PI / 2) by (rewrite Vhi; bpow_num; interval with (i_prec 300)).
  assert (Hhigh : PI / 2 < B hi + / 2 * bpow radix2 (-52)) by (rewrite Vhi; bpow_num; interval with (i_prec 300)).
  symmetry. apply Rle_antisym.
  - apply (round_N_le_midp radix2 (FLT_exp (-1074) 53) ne (B hi) (PI / 2) (B_fmt hi)).
    rewrite (succ_eq_pos radix2 (FLT_exp (-1074) 53) (B hi) ltac:(lra)), Hulp. lra.
  - apply round_ge_generic; [exact _ | exact _ | exact (B_fmt hi) | exact Hlow].
Qed.

(** The published worst-case search: no binary64 midpoint within [2^-124] relatively of [asin a]. *)
Definition CoreMath : Prop :=
  forall a, finite a -> / 67108864 <= B a -> B a <= 1 - / 9007199254740992 -> Stable (asin (B a)).

Lemma lt_one_le a : finite a -> B a < 1 -> B a <= 1 - / 9007199254740992.
Proof.
  intros Fa H. destruct (Rle_lt_dec (B a) (/ 2)) as [Lo | Hi]; [lra | ].
  assert (Hr : bpow radix2 (-1) <= Rabs (B a)).
  { rewrite Rabs_pos_eq by lra. assert (Hh : bpow radix2 (-1) = / 2) by (bpow_num; reflexivity). rewrite Hh. lra. }
  destruct (grid_fmt_bound (FLT_exp emin prec) (-1) (B a) ltac:(intros e; unfold FLT_exp, emin, prec; lia) (B_fmt a) (or_intror Hr)) as [k Hk].
  replace (-1 - 52)%Z with (-53)%Z in Hk by reflexivity. rewrite bp53 in Hk.
  assert (Hk1 : (k < 9007199254740992)%Z).
  { apply lt_IZR. change (IZR 9007199254740992) with 9007199254740992.
    assert (Hp : 0 < / 9007199254740992) by (apply Rinv_0_lt_compat; lra). rewrite Hk in H. nra. }
  assert (Hk2 : IZR k <= 9007199254740991) by (apply IZR_le; lia).
  assert (Hp : 0 < / 9007199254740992) by (apply Rinv_0_lt_compat; lra). rewrite Hk. nra.
Qed.

Lemma half_pi_pos : 0 < B asin_half_pi_f64.
Proof.
  destruct half_pi_words as [_ [_ [Vhi _]]].
  change asin_half_pi_f64 with (aw (fst asin_half_pi)). rewrite Vhi. bpow_num. interval with (i_prec 80).
Qed.

Lemma is_x_lo : / 67108864 <= B asin_is_x.
Proof. destruct is_x_val as [_ V]. rewrite V. bpow_num. interval with (i_prec 100). Qed.

Lemma rnd_pos y : / 67108864 <= y -> 0 < rndF y.
Proof.
  intros H. apply Rlt_le_trans with (bpow radix2 (-26)).
  - apply bpow_gt_0.
  - apply round_ge_generic; [exact _ | exact _ | apply fmt_bpow; lia | ].
    apply Rle_trans with (/ 67108864); [bpow_num; interval with (i_prec 100) | exact H].
Qed.

Theorem asin_entry_finite x : CoreMath -> finite x -> Rabs (B x) <= 1 ->
  finite (asin_entry x) /\ B (asin_entry x) = rndF (asin (B x)).
Proof.
  intros CM Fx Hx1.
  assert (Hn : asin_is_nan x = false) by (destruct x; first [reflexivity | discriminate Fx]).
  unfold asin_entry. rewrite Hn.
  destruct (abs_split x Fx) as [n0 [R0 [Ha [Fa [Na Hs]]]]].
  rewrite Ha. set (a := b64_of_bits n0) in *.
  assert (Hab : B a = Rabs (B x)).
  { destruct Hs as [[_ E] | [_ E]]; rewrite E; [rewrite Rabs_pos_eq by exact Na; reflexivity | rewrite Rabs_Ropp, Rabs_pos_eq by exact Na; reflexivity]. }
  assert (Hgo : B a < 1 -> / 67108864 <= B a ->
    finite (asin_with_sign (asin_positive a) x) /\ B (asin_with_sign (asin_positive a) x) = rndF (asin (B x))).
  { intros Hlt L.
    assert (U : B a <= 1 - / 9007199254740992) by (apply lt_one_le; assumption).
    destruct (positive_correct a Fa L U (CM a Fa L U)) as [Fv Bv].
    assert (Hxb : 0 <= B a <= 1) by (split; [lra | lra]).
    pose proof (asin_ge _ Hxb) as Age.
    assert (Pv : 0 < B (asin_positive a)) by (rewrite Bv; apply rnd_pos; lra).
    destruct (with_sign_val _ x Fv Pv Fx) as [Fws [Hp Hng]].
    split; [exact Fws | ].
    destruct Hs as [[Hb E] | [Hb E]].
    - rewrite (Hp (ex_intro _ n0 (conj Hb R0))), Bv, E. reflexivity.
    - rewrite (Hng (ex_intro _ n0 (conj Hb R0))), Bv, E, asin_opp, round_NE_opp_ne. reflexivity. }
  destruct one_val as [V1 F1].
  assert (C1 : asin_cmp a asin_one = Some (Rcompare (B a) 1)).
  { unfold asin_cmp. rewrite (Bcompare_correct 53 1024 a asin_one Fa F1), V1. reflexivity. }
  rewrite C1.
  destruct (Rcompare_spec (B a) 1) as [Hlt | Heq | Hgt].
  - (* below one *)
    cbv iota.
    destruct is_x_val as [Fi Vi'].
    assert (C2 : asin_cmp a asin_is_x = Some (Rcompare (B a) (B asin_is_x))).
    { unfold asin_cmp. rewrite (Bcompare_correct 53 1024 a asin_is_x Fa Fi). reflexivity. }
    rewrite C2.
    destruct (Rcompare_spec (B a) (B asin_is_x)) as [Hs2 | Hs2 | Hs2].
    + cbv iota.
      split; [exact Fx | ].
      pose proof (small_correct a Fa Na Hs2) as Sm.
      destruct Hs as [[_ E] | [_ E]]; rewrite E.
      * exact (eq_sym Sm).
      * rewrite asin_opp, round_NE_opp_ne. rewrite Sm. reflexivity.
    + cbv iota. apply Hgo; [exact Hlt | ]. rewrite Hs2. exact is_x_lo.
    + cbv iota. apply Hgo; [exact Hlt | ]. apply Rle_trans with (B asin_is_x); [exact is_x_lo | lra].
  - (* one *)
    cbv iota.
    pose proof half_pi_rn as [Fh Bh].
    destruct (with_sign_val _ x Fh half_pi_pos Fx) as [Fws [Hp Hng]].
    split; [exact Fws | ].
    destruct Hs as [[Hb E] | [Hb E]].
    + rewrite (Hp (ex_intro _ n0 (conj Hb R0))), Bh, E, Heq, asin_1. reflexivity.
    + rewrite (Hng (ex_intro _ n0 (conj Hb R0))), Bh, E, Heq, asin_opp, asin_1, round_NE_opp_ne. reflexivity.
  - exfalso. lra.
Qed.

Lemma nan_is_nan : asin_is_nan asin_nan = true.
Proof. reflexivity. Qed.

Theorem asin_entry_nan x : asin_is_nan x = true -> asin_entry x = x.
Proof. intros H. unfold asin_entry. rewrite H. reflexivity. Qed.

Theorem asin_entry_inf s : asin_is_nan (asin_entry (B754_infinity 53 1024 s)) = true.
Proof. destruct s; vm_compute; reflexivity. Qed.

Theorem asin_entry_large x : finite x -> 1 < Rabs (B x) -> asin_is_nan (asin_entry x) = true.
Proof.
  intros Fx Hx1.
  assert (Hn : asin_is_nan x = false) by (destruct x; first [reflexivity | discriminate Fx]).
  unfold asin_entry. rewrite Hn.
  destruct (abs_split x Fx) as [n0 [R0 [Ha [Fa [Na Hs]]]]].
  rewrite Ha. set (a := b64_of_bits n0) in *.
  assert (Hab : B a = Rabs (B x)).
  { destruct Hs as [[_ E] | [_ E]]; rewrite E; [rewrite Rabs_pos_eq by exact Na; reflexivity | rewrite Rabs_Ropp, Rabs_pos_eq by exact Na; reflexivity]. }
  destruct one_val as [V1 F1].
  assert (C1 : asin_cmp a asin_one = Some (Rcompare (B a) 1)).
  { unfold asin_cmp. rewrite (Bcompare_correct 53 1024 a asin_one Fa F1), V1. reflexivity. }
  rewrite C1.
  destruct (Rcompare_spec (B a) 1) as [Hlt | Heq | Hgt]; [exfalso; lra | exfalso; lra | ].
  cbv iota. reflexivity.
Qed.
