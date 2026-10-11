(** ln_1p's reduction for stages H and B (docs/ln.md, section 7), transcribed
    on binary64 encodings as crates/morphiq-numerics/src/ln/stages.rs computes
    it, and proved: for a positive normal [h <= 2^1020], [E] and the index [i]
    read from [bits(h) − OFF] give [h = 2^E·y] with [y] in table interval
    [i]; [rs = R[i]·2^-E] from [R[i]]'s encoding; and
    [z = (hh·rs − 1) + hl·rs] is [y·R[i] − 1] exactly, every operation exact
    ([reduce_ok]). And [1 + x = s0 + l] exactly for the split
    [s0 = RN(1 + x)], [l = x − (s0 − 1)], [−1 < x < 2^53] ([split_ok]). *)

From Coq Require Import ZArith Reals Lia Lra Psatz List.
From Flocq Require Import Core Sterbenz Plus_error IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 Grid Encodings.
Require Import Ln1pCheck Ln1pTables.
Import ListNotations.

Open Scope R_scope.

(** * Binary64 helpers *)

Lemma bpow_m (k : nat) : bpow radix2 (- Z.of_nat k) = / 2 ^ k.
Proof. rewrite bpow_opp, bpow_powerRZ, <- pow_powerRZ. reflexivity. Qed.

Lemma IZR_pow2' k : (0 <= k)%Z -> IZR (2 ^ k) = bpow radix2 k.
Proof. intros H. change (2 ^ k)%Z with (Zpower radix2 k). apply IZR_Zpower, H. Qed.

(** A real on [2^q]'s grid below [2^(q+53)] in magnitude is a binary64 number. *)
Lemma grid_repr q v : (-1074 <= q)%Z -> on_grid q v -> Rabs v < bpow radix2 (q + 53) -> fmtF v.
Proof.
  intros Hq [k Ek] Hv. subst v. apply generic_format_FLT.
  exists (Float radix2 k q); [reflexivity | | simpl; unfold emin; lia].
  simpl. apply lt_IZR. rewrite abs_IZR. change (IZR (Z.pow_pos 2 53)) with (bpow radix2 53).
  apply Rmult_lt_reg_r with (bpow radix2 q); [apply bpow_gt_0 | ].
  rewrite <- bpow_plus, Z.add_comm. rewrite Rabs_mult, (Rabs_pos_eq (bpow radix2 q)) in Hv by apply bpow_ge_0.
  exact Hv.
Qed.

(** An exact operation: the result is representable, so rounding returns it. *)
Lemma exact_round v : fmtF v -> rndF v = v.
Proof. intros F. apply round_generic; [exact _ | exact F]. Qed.

(** The four operations on operands below [2^1000] in magnitude whose exact
    result is below [2^1000]: finite, and rounded as the model does. *)
Lemma fadd_s x y : finite x -> finite y -> Rabs (B x + B y) <= bpow radix2 1000 ->
  finite (fadd x y) /\ B (fadd x y) = rndF (B x + B y).
Proof.
  intros Fx Fy H. apply (fadd_ok 1 1000 x y Fx Fy ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)).
  unfold bnd. rewrite Rmult_1_l. exact H.
Qed.
Lemma fsub_s x y : finite x -> finite y -> Rabs (B x - B y) <= bpow radix2 1000 ->
  finite (fsub x y) /\ B (fsub x y) = rndF (B x - B y).
Proof.
  intros Fx Fy H. apply (fsub_ok 1 1000 x y Fx Fy ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)).
  unfold bnd. rewrite Rmult_1_l. exact H.
Qed.
Lemma fmul_s x y : finite x -> finite y -> Rabs (B x * B y) <= bpow radix2 1000 ->
  finite (fmul x y) /\ B (fmul x y) = rndF (B x * B y).
Proof.
  intros Fx Fy H. apply (fmul_ok 1 1000 x y Fx Fy ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)).
  unfold bnd. rewrite Rmult_1_l. exact H.
Qed.

(** * Encodings *)

(** A positive normal encoding's value from its fields. *)
Lemma normal_bits n : (2 ^ 52 <= n < 2047 * 2 ^ 52)%Z ->
  finite (b64_of_bits n) /\
  B (b64_of_bits n) = IZR (n mod 2 ^ 52 + 2 ^ 52) * bpow radix2 (n / 2 ^ 52 - 1075).
Proof.
  intros H.
  assert (M : (0 <= n mod 2 ^ 52 < 2 ^ 52)%Z) by (apply Z.mod_pos_bound; lia).
  assert (D : (1 <= n / 2 ^ 52 <= 2046)%Z).
  { split; [apply Z.div_le_lower_bound; lia | ].
    assert (n / 2 ^ 52 < 2047)%Z by (apply Z.div_lt_upper_bound; lia). lia. }
  pose proof (join_val (n mod 2 ^ 52) (n / 2 ^ 52) M D) as J. rewrite join_eq in J.
  replace (n / 2 ^ 52 * 2 ^ 52 + n mod 2 ^ 52)%Z with n in J
    by (rewrite Z.mul_comm; apply Z.div_mod; lia).
  exact J.
Qed.

(** A positive normal number's encoding. *)
Lemma bits_normal h : finite h -> bpow radix2 (-1022) <= B h ->
  (2 ^ 52 <= bits_of_b64 h < 2047 * 2 ^ 52)%Z /\ b64_of_bits (bits_of_b64 h) = h.
Proof.
  intros Fh Hh. destruct (pos_normal h Fh Hh) as [mx [ex [Hx [_ [Mx [Ex [_ [_ [_ Bits]]]]]]]]].
  rewrite Bits, join_eq. split; [lia | ].
  rewrite <- join_eq, <- Bits. unfold b64_of_bits, bits_of_b64.
  exact (binary_float_of_bits_of_binary_float 52 11 eq_refl eq_refl eq_refl h).
Qed.

(** Subtracting [k] from the exponent field divides by [2^k]. *)
Lemma scale_bits n k : (2 ^ 52 <= n < 2047 * 2 ^ 52)%Z -> (2 ^ 52 <= n - k * 2 ^ 52 < 2047 * 2 ^ 52)%Z ->
  finite (b64_of_bits (n - k * 2 ^ 52)) /\
  B (b64_of_bits (n - k * 2 ^ 52)) = B (b64_of_bits n) * bpow radix2 (- k).
Proof.
  intros H1 H2. destruct (normal_bits n H1) as [_ V1]. destruct (normal_bits _ H2) as [F V2].
  split; [exact F | ]. rewrite V2, V1.
  replace ((n - k * 2 ^ 52) mod 2 ^ 52)%Z with (n mod 2 ^ 52)%Z
    by (replace (n - k * 2 ^ 52)%Z with (n + (- k) * 2 ^ 52)%Z by ring; rewrite Z.mod_add; lia).
  replace ((n - k * 2 ^ 52) / 2 ^ 52)%Z with (n / 2 ^ 52 - k)%Z
    by (replace (n - k * 2 ^ 52)%Z with (n + (- k) * 2 ^ 52)%Z by ring; rewrite Z.div_add; lia).
  rewrite Rmult_assoc, <- bpow_plus. do 2 f_equal. ring.
Qed.

(** Within one exponent field, the value grows with the encoding. *)
Lemma bits_mono n1 n2 : (2 ^ 52 <= n1 <= n2)%Z -> (n2 < 2047 * 2 ^ 52)%Z -> (n1 / 2 ^ 52 = n2 / 2 ^ 52)%Z ->
  B (b64_of_bits n1) <= B (b64_of_bits n2).
Proof.
  intros H1 H2 E. destruct (normal_bits n1 ltac:(lia)) as [_ V1]. destruct (normal_bits n2 ltac:(lia)) as [_ V2].
  rewrite V1, V2, E. apply Rmult_le_compat_r; [apply bpow_ge_0 | apply IZR_le].
  pose proof (Z.div_mod n1 (2 ^ 52) ltac:(lia)). pose proof (Z.div_mod n2 (2 ^ 52) ltac:(lia)). lia.
Qed.

(** * The split [1 + x = s0 + l] (stage H, and stage B below [2^53]) *)

Definition c_one : f64 := b64_of_bits 4607182418800017408.   (* 0x3ff0000000000000 *)

Lemma c_one_ok : finite c_one /\ B c_one = 1.
Proof.
  unfold c_one. destruct (normal_bits 4607182418800017408 ltac:(lia)) as [F V]. split; [exact F | rewrite V].
  change (4607182418800017408 mod 2 ^ 52 + 2 ^ 52)%Z with (2 ^ 52)%Z.
  change (4607182418800017408 / 2 ^ 52 - 1075)%Z with (-52)%Z.
  rewrite IZR_pow2' by lia. rewrite <- bpow_plus. reflexivity.
Qed.

Definition split_s0 (x : f64) : f64 := fadd c_one x.
Definition split_l (x : f64) : f64 := fsub x (fsub (split_s0 x) c_one).

Theorem split_ok x : finite x -> -1 < B x < bpow radix2 53 ->
  let s0 := split_s0 x in let l := split_l x in
  finite s0 /\ finite l /\ B s0 = rndF (1 + B x) /\ B s0 + B l = 1 + B x /\
  bpow radix2 (-53) <= B s0 <= bpow radix2 53 /\ Rabs (B l) <= bpow radix2 (-53) * B s0.
Proof.
  intros Fx [Hx1 Hx2]. destruct c_one_ok as [F1 B1].
  assert (Fm : fmtF (B x)) by apply B_fmt.
  (* 1 + x is at least 2^-53: x is on 2^-53's grid when |x| >= 1/2 *)
  assert (Lo : bpow radix2 (-53) <= 1 + B x).
  { destruct (Rle_lt_dec (/ 2) (Rabs (B x))) as [Big | Small].
    - destruct (Rlt_le_dec (B x) 0) as [N | P].
      + assert (G : on_grid (-53) (B x)).
        { apply (grid_fmt_bound (FLT_exp emin prec) (-1)); [intros e; unfold FLT_exp, emin, prec; lia | exact Fm | ].
          right. change (bpow radix2 (-1)) with (/ 2). exact Big. }
        assert (G1 : on_grid (-53) (1 + B x)).
        { apply grid_plus; [exists (2 ^ 53)%Z; rewrite IZR_pow2' by lia; rewrite <- bpow_plus; reflexivity | exact G]. }
        assert (Nz : 1 + B x <> 0) by lra.
        pose proof (grid_nonzero _ _ G1 Nz) as Gn. rewrite Rabs_pos_eq in Gn by lra. exact Gn.
      + apply Rle_trans with 1; [change 1 with (bpow radix2 0); apply bpow_le; lia | lra].
    - apply Rabs_lt_inv in Small. apply Rle_trans with (/ 2); [ | lra].
      change (/ 2) with (bpow radix2 (-1)). apply bpow_le. lia. }
  (* 1 + x is at most 2^53: x is below 2^53, so at most 2^53 - 1 *)
  assert (Hi : 1 + B x <= bpow radix2 53).
  { assert (G : on_grid 0 (B x) \/ B x < bpow radix2 52).
    { destruct (Rlt_le_dec (B x) (bpow radix2 52)) as [L | L]; [right; exact L | left].
      apply (grid_le (cexp radix2 (FLT_exp emin prec) (B x))); [ | apply grid_fmt, Fm].
      unfold cexp, FLT_exp, emin, prec.
      assert (M : (53 <= mag radix2 (B x))%Z)
        by (apply mag_ge_bpow; rewrite Rabs_pos_eq by (pose proof (bpow_gt_0 radix2 52); lra); exact L).
      lia. }
    destruct G as [[k Ek] | L].
    - change (bpow radix2 0) with 1 in Ek. rewrite Rmult_1_r in Ek.
      assert (k < 2 ^ 53)%Z by (apply lt_IZR; rewrite <- Ek, IZR_pow2' by lia; exact Hx2).
      assert (Kl : IZR k <= IZR (2 ^ 53 - 1)) by (apply IZR_le; lia).
      rewrite minus_IZR, IZR_pow2' in Kl by lia. rewrite Ek. lra.
    - assert (bpow radix2 52 + 1 <= bpow radix2 53)
        by (change (bpow radix2 53) with (2 * bpow radix2 52); pose proof (bpow_ge_0 radix2 52);
            change (bpow radix2 52) with 4503599627370496 in *; lra).
      lra. }
  destruct (fadd_s c_one x F1 Fx ltac:(rewrite B1, Rabs_pos_eq by lra; apply Rle_trans with (1 := Hi); apply bpow_le; lia))
    as [Fs Bs]. rewrite B1 in Bs.
  fold (split_s0 x) in Fs, Bs. set (s0 := split_s0 x) in *.
  assert (S0 : bpow radix2 (-53) <= B s0 <= bpow radix2 53).
  { rewrite Bs. split.
    - apply round_ge_generic; [exact _ | exact _ | apply generic_format_bpow; unfold FLT_exp, emin, prec; lia | exact Lo].
    - apply round_le_generic; [exact _ | exact _ | apply generic_format_bpow; unfold FLT_exp, emin, prec; lia | exact Hi]. }
  (* s0 - 1 is exact *)
  assert (D : fmtF (B s0 - 1)).
  { destruct (Rlt_le_dec (B x) (- / 2)) as [N | P].
    - (* 1 + x is exact by Sterbenz's lemma, so s0 - 1 = x *)
      assert (E1 : fmtF (1 + B x)).
      { replace (1 + B x) with (1 - - B x) by ring.
        apply sterbenz; [exact _ | exact _ | | apply generic_format_opp, Fm | lra].
        apply generic_format_bpow' with (e := 0%Z); [exact _ | unfold FLT_exp, emin, prec; lia]. }
      rewrite Bs, exact_round by exact E1. replace (1 + B x - 1) with (B x) by ring. exact Fm.
    - destruct (Rle_lt_dec (B s0) 2) as [S2 | S2].
      + (* s0 in [1/2, 2] *)
        assert (Hs : / 2 <= B s0).
        { rewrite Bs. apply round_ge_generic; [exact _ | exact _ | | lra].
          change (/ 2) with (bpow radix2 (-1)). apply generic_format_bpow; unfold FLT_exp, emin, prec; lia. }
        apply sterbenz; [exact _ | exact _ | rewrite Bs; apply fmtF_rnd | | lra].
        apply generic_format_bpow' with (e := 0%Z); [exact _ | unfold FLT_exp, emin, prec; lia].
      + (* s0 > 2: s0 - 1 stays on s0's grid, or s0 = 2^53 *)
        set (q := Z.min (cexp radix2 (FLT_exp emin prec) (B s0)) 0).
        assert (Gs : on_grid q (B s0)).
        { apply (grid_le (cexp radix2 (FLT_exp emin prec) (B s0))); [unfold q; lia | apply grid_fmt; rewrite Bs; apply fmtF_rnd]. }
        assert (G1 : on_grid q 1) by (exists (2 ^ (- q))%Z; rewrite IZR_pow2' by (unfold q; lia); rewrite <- bpow_plus; replace (- q + q)%Z with 0%Z by ring; reflexivity).
        apply (grid_repr q); [unfold q, cexp, FLT_exp, emin, prec; lia | apply grid_minus; assumption | ].
        rewrite Rabs_pos_eq by lra.
        destruct (Z.le_gt_cases (cexp radix2 (FLT_exp emin prec) (B s0)) 0) as [C | C].
        * replace q with (cexp radix2 (FLT_exp emin prec) (B s0)) by (unfold q; lia).
          assert (M : B s0 < bpow radix2 (mag radix2 (B s0))) by (pose proof (bpow_mag_gt radix2 (B s0)) as G; rewrite Rabs_pos_eq in G by lra; exact G).
          unfold cexp, FLT_exp, emin, prec in *.
          assert (Mg : (mag radix2 (B s0) - 53 >= -1074)%Z) by (assert (1 <= mag radix2 (B s0))%Z by (apply mag_ge_bpow; rewrite Rabs_pos_eq by lra; simpl; lra); lia).
          rewrite Z.max_l by lia. replace (mag radix2 (B s0) - 53 + 53)%Z with (mag radix2 (B s0) : Z) by ring. lra.
        * replace q with 0%Z by (unfold q; lia). simpl Z.add.
          assert (B s0 = bpow radix2 53).
          { apply Rle_antisym; [lra | ].
            assert (M : (54 <= mag radix2 (B s0))%Z) by (unfold cexp, FLT_exp, emin, prec in C; lia).
            pose proof (bpow_mag_le radix2 (B s0) ltac:(lra)) as G. rewrite Rabs_pos_eq in G by lra.
            apply Rle_trans with (bpow radix2 (mag radix2 (B s0) - 1)); [apply bpow_le; lia | exact G]. }
          lra. }
  assert (P53 : 1 <= bpow radix2 53) by (change 1 with (bpow radix2 0); apply bpow_le; lia).
  assert (Pm : 0 < bpow radix2 (-53)) by apply bpow_gt_0.
  destruct (fsub_s s0 c_one Fs F1 ltac:(rewrite B1; apply Rle_trans with (bpow radix2 53); [apply Rabs_le; lra | apply bpow_le; lia]))
    as [Fd Bd]. rewrite B1, exact_round in Bd by exact D.
  (* l = (1 + x) - s0 is the rounding error of 1 + x, so exact *)
  assert (Ferr : fmtF (B x - (B s0 - 1))).
  { replace (B x - (B s0 - 1)) with (- (rndF (1 + B x) - (1 + B x))) by (rewrite <- Bs; ring).
    apply generic_format_opp, plus_error; [exact _ | exact _ | | exact Fm].
    apply generic_format_bpow' with (e := 0%Z); [exact _ | unfold FLT_exp, emin, prec; lia]. }
  assert (Herr : Rabs (B x - (B s0 - 1)) <= bpow radix2 (-53) * B s0).
  { replace (B x - (B s0 - 1)) with (- (rndF (1 + B x) - (1 + B x))) by (rewrite <- Bs; ring).
    rewrite Rabs_Ropp. apply Rle_trans with (/ 2 * ulp radix2 (FLT_exp emin prec) (rndF (1 + B x))).
    - apply error_le_half_ulp_round; exact _.
    - rewrite <- Bs. assert (N : bpow radix2 (emin + prec - 1) <= Rabs (B s0)).
      { rewrite Rabs_pos_eq by (pose proof (bpow_gt_0 radix2 (-53)); lra). apply Rle_trans with (2 := proj1 S0).
        apply bpow_le. unfold emin, prec. lia. }
      pose proof (ulp_FLT_le radix2 emin prec (B s0) N) as U. rewrite Rabs_pos_eq in U by (pose proof (bpow_gt_0 radix2 (-53)); lra).
      replace (bpow radix2 (1 - prec)) with (2 * bpow radix2 (-53)) in U
        by (unfold prec; change 2 with (bpow radix2 1); rewrite <- bpow_plus; reflexivity).
      lra. }
  destruct (fsub_s x (fsub s0 c_one) Fx Fd ltac:(rewrite Bd; apply Rle_trans with 1; [ | change 1 with (bpow radix2 0); apply bpow_le; lia];
                                                    apply Rle_trans with (1 := Herr); pose proof (bpow_gt_0 radix2 (-53));
                                                    apply Rle_trans with (bpow radix2 (-53) * bpow radix2 53); [apply Rmult_le_compat_l; lra | rewrite <- bpow_plus; simpl; lra]))
    as [Fl Bl].
  rewrite Bd, exact_round in Bl by exact Ferr.
  cbv zeta. unfold split_l. fold s0.
  split; [exact Fs | split; [exact Fl | split; [exact Bs | split; [rewrite Bl; ring | split; [exact S0 | rewrite Bl; exact Herr]]]]].
Qed.

(** * The reduction from [h]'s encoding *)

Definition st_r (i : nat) : f64 := b64_of_bits (nth i st_r_bits 0%Z).
Definition st_th (i : nat) : f64 := b64_of_bits (fst (nth i st_t_bits (0%Z, 0%Z))).
Definition st_tl (i : nat) : f64 := b64_of_bits (snd (nth i st_t_bits (0%Z, 0%Z))).

(** [u = bits(h).wrapping_sub(OFF)], [E = (u as i64) >> 52],
    [i = (u >> 43) & 511], [rs = R[i].wrapping_sub((E as u64) << 52)],
    [hh = bits(h) & !0x3ff], and [z = (hh·rs − 1) + (h − hh)·rs]. *)
Definition rd_u (hb : Z) : Z := ((hb - st_off) mod 2 ^ 64)%Z.
Definition rd_e (hb : Z) : Z := ((if rd_u hb <? 2 ^ 63 then rd_u hb else rd_u hb - 2 ^ 64) / 2 ^ 52)%Z.
Definition rd_i (hb : Z) : nat := Z.to_nat (Z.land (Z.shiftr (rd_u hb) 43) 511).
Definition rd_rs (hb : Z) : f64 := b64_of_bits ((nth (rd_i hb) st_r_bits 0%Z - rd_e hb * 2 ^ 52) mod 2 ^ 64).
Definition rd_hh (hb : Z) : f64 := b64_of_bits (Z.land hb (Z.lnot 1023)).
Definition rd_z (h : f64) : f64 :=
  let hb := bits_of_b64 h in
  let rs := rd_rs hb in
  let hh := rd_hh hb in
  fadd (fsub (fmul hh rs) c_one) (fmul (fsub h hh) rs).

(** The index and exponent: [bits(h) − OFF = E·2^52 + i·2^43 + r]. *)
Lemma rd_fields hb : (970 * 2 ^ 52 <= hb < 2044 * 2 ^ 52)%Z ->
  let E := rd_e hb in let i := Z.of_nat (rd_i hb) in
  (0 <= i < 512)%Z /\ (-53 <= E <= 1021)%Z /\
  exists r, (0 <= r < 2 ^ 43)%Z /\ (hb - st_off = E * 2 ^ 52 + i * 2 ^ 43 + r)%Z.
Proof.
  intros H. unfold rd_e, rd_i, rd_u, st_off in *. cbv zeta.
  set (d := (hb - 4604543590893355008)%Z).
  assert (Sg : (if (d mod 2 ^ 64 <? 2 ^ 63)%Z then d mod 2 ^ 64 else (d mod 2 ^ 64 - 2 ^ 64))%Z = d).
  { destruct (Z.leb_spec 0 d) as [P | N].
    - rewrite (Z.mod_small d (2 ^ 64)) by (unfold d; lia). replace (d <? 2 ^ 63)%Z with true by (symmetry; apply Z.ltb_lt; unfold d; lia). reflexivity.
    - replace (d mod 2 ^ 64)%Z with (d + 2 ^ 64)%Z by (apply Z.mod_unique with (-1)%Z; [left; unfold d; lia | ring]).
      replace (d + 2 ^ 64 <? 2 ^ 63)%Z with false by (symmetry; apply Z.ltb_ge; unfold d; lia). ring. }
  rewrite Sg.
  assert (Ix : Z.land (Z.shiftr (d mod 2 ^ 64) 43) 511 = (d / 2 ^ 43) mod 2 ^ 9).
  { change 511%Z with (Z.ones 9). rewrite Z.land_ones by lia. rewrite Z.shiftr_div_pow2 by lia.
    destruct (Z.leb_spec 0 d) as [P | N].
    - rewrite (Z.mod_small d (2 ^ 64)) by (unfold d; lia). reflexivity.
    - replace (d mod 2 ^ 64)%Z with (d + 2 ^ 21 * 2 ^ 43)%Z by (apply Z.mod_unique with (-1)%Z; [left; unfold d; lia | ring]).
      rewrite Z.div_add by lia. replace (2 ^ 21)%Z with (2 ^ 12 * 2 ^ 9)%Z by reflexivity.
      rewrite Z.mod_add by lia. reflexivity. }
  rewrite Ix, Z2Nat.id by (apply Z.mod_pos_bound; lia).
  split; [apply Z.mod_pos_bound; lia | ].
  split.
  - split; [apply Z.div_le_lower_bound; unfold d; lia | ].
    assert (d / 2 ^ 52 < 1022)%Z by (apply Z.div_lt_upper_bound; unfold d; lia). lia.
  - exists (d mod 2 ^ 43)%Z. split; [apply Z.mod_pos_bound; lia | ].
    assert (D1 : (d / 2 ^ 43 = 2 ^ 9 * (d / 2 ^ 52) + (d / 2 ^ 43) mod 2 ^ 9)%Z).
    { replace (d / 2 ^ 52)%Z with (d / 2 ^ 43 / 2 ^ 9)%Z by (rewrite Z.div_div by lia; reflexivity).
      apply Z.div_mod. lia. }
    pose proof (Z.div_mod d (2 ^ 43) ltac:(lia)). lia.
Qed.

Lemma hh_bits hb : (0 <= hb)%Z -> Z.land hb (Z.lnot 1023) = (hb / 2 ^ 10 * 2 ^ 10)%Z.
Proof.
  intros H. rewrite <- Z.ldiff_land. change 1023%Z with (Z.ones 10).
  rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

(** [z = y·R[i] − 1] is on [2^-62]'s grid: [y < 1] on [2^-53]'s with [R[i] >= 1]
    on [2^-9]'s, or [y >= 1] on [2^-52]'s with [R[i] <= 1] on [2^-10]'s. *)
Lemma r_grid r : (r mod 2 ^ 43 = 0)%Z -> (1022 <= r / 2 ^ 52 <= 1023)%Z ->
  exists K, (2 ^ 9 <= K < 2 ^ 10)%Z /\ B (b64_of_bits r) = IZR K * bpow radix2 (r / 2 ^ 52 - 1032).
Proof.
  intros Hm He. destruct (normal_bits r ltac:(pose proof (Z.div_mod r (2 ^ 52) ltac:(lia)); pose proof (Z.mod_pos_bound r (2 ^ 52) ltac:(lia)); lia)) as [_ V].
  set (Q := ((r mod 2 ^ 52 + 2 ^ 52) / 2 ^ 43)%Z).
  assert (M : ((r mod 2 ^ 52) mod 2 ^ 43 = 0)%Z).
  { pose proof (Z.div_mod r (2 ^ 52) ltac:(lia)) as Dr.
    replace (r mod 2 ^ 52)%Z with (r + (- (2 ^ 9 * (r / 2 ^ 52))) * 2 ^ 43)%Z by lia.
    rewrite Z.mod_add by lia. exact Hm. }
  assert (D : (r mod 2 ^ 52 + 2 ^ 52 = 2 ^ 43 * Q)%Z).
  { pose proof (Z.div_mod (r mod 2 ^ 52 + 2 ^ 52) (2 ^ 43) ltac:(lia)) as Dm.
    replace ((r mod 2 ^ 52 + 2 ^ 52) mod 2 ^ 43)%Z with 0%Z in Dm
      by (replace (2 ^ 52)%Z with (2 ^ 9 * 2 ^ 43)%Z at 2 by reflexivity; rewrite Z.mod_add by lia; lia).
    unfold Q. lia. }
  pose proof (Z.mod_pos_bound r (2 ^ 52) ltac:(lia)).
  exists Q. split; [lia | ].
  rewrite V, D, mult_IZR, IZR_pow2' by lia.
  rewrite (Rmult_comm (bpow radix2 43)), Rmult_assoc, <- bpow_plus. f_equal. f_equal. ring.
Qed.

Lemma zero_bits : B (b64_of_bits 0) = 0.
Proof. reflexivity. Qed.

Theorem reduce_ok h : finite h -> bpow radix2 (-53) <= B h <= bpow radix2 1020 ->
  let hb := bits_of_b64 h in let E := rd_e hb in let i := rd_i hb in
  let y := B h * bpow radix2 (- E) in let R := B (st_r i) in
  (-53 <= E <= 1020)%Z /\ (i < 512)%nat /\ / 2 <= R <= 2 /\ 7 / 10 <= y <= 3 / 2 /\
  B (b64_of_bits (st_off + Z.of_nat i * width)) <= y <= B (b64_of_bits (st_off + (Z.of_nat i + 1) * width - 1)) /\
  finite (rd_rs hb) /\ B (rd_rs hb) = R * bpow radix2 (- E) /\
  finite (rd_z h) /\ B (rd_z h) = y * R - 1 /\
  (B (rd_z h) = 0 \/ bpow radix2 (-62) <= Rabs (B (rd_z h))) /\
  (exists zi, zi <= / 2 ^ 9 /\ Rabs (B (rd_z h)) <= zi /\
     (near_b (Z.of_nat i) = true -> B (st_th i) = 0 /\ B (st_tl i) = 0 /\ R = 1) /\
     (near_b (Z.of_nat i) = false -> zi + dval (b_s_min st_bounds) <= Rabs (B (st_th i)))) /\
  finite (st_th i) /\ finite (st_tl i) /\
  on_grid (-43) (B (st_th i)) /\ Rabs (B (st_tl i)) <= dval (b_tl_max st_bounds) /\
  Rabs (B (st_th i)) <= dval (b_th_max st_bounds) /\
  Rabs (B (st_th i) + B (st_tl i) + ln R) <= dval (b_t_err st_bounds).
Proof.
  intros Fh [Hl Hu].
  assert (Nh : bpow radix2 (-1022) <= B h) by (apply Rle_trans with (2 := Hl); apply bpow_le; lia).
  destruct (bits_normal h Fh Nh) as [_ Rt].
  destruct (pos_normal h Fh Nh) as [mx [ex [Hx [_ [Mx [Ex [Vh [_ [_ Bits]]]]]]]]].
  cbv zeta. set (hb := bits_of_b64 h) in *.
  assert (Hbits : hb = ((ex + 1075) * 2 ^ 52 + (Z.pos mx - 2 ^ 52))%Z) by (rewrite Bits, join_eq; ring).
  assert (Ex1 : (-105 <= ex)%Z).
  { apply Z.nlt_ge. intros L. assert (B h < bpow radix2 (-53)); [ | lra].
    rewrite Vh. apply Rlt_le_trans with (IZR (2 ^ 53) * bpow radix2 ex).
    - apply Rmult_lt_compat_r; [apply bpow_gt_0 | apply IZR_lt; lia].
    - rewrite IZR_pow2', <- bpow_plus by lia. apply bpow_le. lia. }
  assert (Ex2 : (hb <= 2043 * 2 ^ 52)%Z).
  { destruct (Z.le_gt_cases ex 967) as [L | L]; [lia | ].
    assert (Z.pos mx * 2 ^ ex <= 2 ^ 1020)%Z.
    { apply le_IZR. rewrite mult_IZR, !IZR_pow2' by lia. rewrite <- Vh. exact Hu. }
    assert (ex = 968)%Z.
    { apply Z.le_antisymm; [ | lia]. apply Z.nlt_ge. intros L2.
      assert (2 ^ 52 * 2 ^ 969 <= Z.pos mx * 2 ^ ex)%Z
        by (apply Z.mul_le_mono_nonneg; [lia | lia | lia | apply Z.pow_le_mono_r; lia]).
      lia. }
    subst ex. assert (Z.pos mx <= 2 ^ 52)%Z by nia. lia. }
  assert (Hr : (970 * 2 ^ 52 <= hb < 2044 * 2 ^ 52)%Z) by lia.
  destruct (rd_fields hb Hr) as [Ii [Ee [r [Hr0 Hd]]]].
  set (E := rd_e hb) in *. set (i := rd_i hb) in *.
  assert (E1020 : (E <= 1020)%Z) by (unfold st_off in Hd; lia).
  assert (Hi : (i < 512)%nat) by lia.
  pose proof (rt_check_ok st_bounds st_r_bits st_t_bits i st_rt_check Hi) as T.
  unfold rt_entry_ok in T. cbv zeta in T.
  set (rr := nth i st_r_bits 0%Z) in *. set (t := nth i st_t_bits (0%Z, 0%Z)) in *.
  destruct T as [FR [FTh [FTl [Rr [Rm [Rb [Rone [Rlo [Rhi [[zi [Zi [Za [Zb [Zn Zf]]]]] [Gth [Ttl [Tth Terr]]]]]]]]]]]]].
  fold (st_r i) in FR. change (b64_of_bits rr) with (st_r i) in *.
  change (b64_of_bits (fst t)) with (st_th i) in *. change (b64_of_bits (snd t)) with (st_tl i) in *.
  set (R := B (st_r i)) in *.
  destruct (r_grid rr Rm Rb) as [K [Kb VR]]. change (B (b64_of_bits rr)) with R in VR.
  pose proof (Z.div_mod rr (2 ^ 52) ltac:(lia)) as Drr. pose proof (Z.mod_pos_bound rr (2 ^ 52) ltac:(lia)) as Mrr.
  set (rb := (rr / 2 ^ 52)%Z) in *.
  assert (RR : / 2 <= R <= 2).
  { rewrite VR. assert (Kr : IZR (2 ^ 9) <= IZR K < IZR (2 ^ 10)) by (split; apply IZR_le || apply IZR_lt; lia).
    rewrite !IZR_pow2' in Kr by lia. pose proof (bpow_gt_0 radix2 (rb - 1032)) as P.
    split.
    - apply Rle_trans with (bpow radix2 9 * bpow radix2 (rb - 1032)); [ | apply Rmult_le_compat_r; lra].
      rewrite <- bpow_plus. change (/ 2) with (bpow radix2 (-1)). apply bpow_le. lia.
    - apply Rle_trans with (bpow radix2 10 * bpow radix2 (rb - 1032)); [apply Rmult_le_compat_r; lra | ].
      rewrite <- bpow_plus. change 2 with (bpow radix2 1). apply bpow_le. lia. }
  (* y's encoding *)
  set (hy := (hb - E * 2 ^ 52)%Z).
  assert (Hy : hy = (st_off + Z.of_nat i * width + r)%Z) by (unfold hy, width; lia).
  assert (Hyr : (2 ^ 52 <= hy < 2047 * 2 ^ 52)%Z) by (rewrite Hy; unfold st_off, width; lia).
  destruct (scale_bits hb E ltac:(lia) Hyr) as [Fy Vy]. fold hy in Fy, Vy. rewrite Rt in Vy.
  set (y := B h * bpow radix2 (- E)) in *.
  assert (Yb : (hy / 2 ^ 52 = if (Z.of_nat i <? 300)%Z then 1022 else 1023)%Z).
  { rewrite Hy. unfold st_off, width. destruct (Z.ltb_spec (Z.of_nat i) 300).
    - symmetry. apply Z.div_unique with (st_off + Z.of_nat i * width + r - 1022 * 2 ^ 52)%Z; unfold st_off, width; lia.
    - symmetry. apply Z.div_unique with (st_off + Z.of_nat i * width + r - 1023 * 2 ^ 52)%Z; unfold st_off, width; lia. }
  assert (Ya : B (b64_of_bits (st_off + Z.of_nat i * width)) <= y).
  { rewrite <- Vy. apply bits_mono; [unfold st_off, width in *; lia | lia | ].
    rewrite Yb. unfold st_off, width. destruct (Z.ltb_spec (Z.of_nat i) 300).
    - symmetry. apply Z.div_unique with (4604543590893355008 + Z.of_nat i * 8796093022208 - 1022 * 2 ^ 52)%Z; lia.
    - symmetry. apply Z.div_unique with (4604543590893355008 + Z.of_nat i * 8796093022208 - 1023 * 2 ^ 52)%Z; lia. }
  assert (Yb2 : y <= B (b64_of_bits (st_off + (Z.of_nat i + 1) * width - 1))).
  { rewrite <- Vy. apply bits_mono; [unfold st_off, width in *; lia | unfold st_off, width; lia | ].
    rewrite Yb. unfold st_off, width. destruct (Z.ltb_spec (Z.of_nat i) 300).
    - apply Z.div_unique with (4604543590893355008 + (Z.of_nat i + 1) * 8796093022208 - 1 - 1022 * 2 ^ 52)%Z; lia.
    - apply Z.div_unique with (4604543590893355008 + (Z.of_nat i + 1) * 8796093022208 - 1 - 1023 * 2 ^ 52)%Z; lia. }
  (* |y R - 1| <= zi: y R - 1 is increasing in y *)
  assert (Yz : Rabs (y * R - 1) <= zi).
  { apply Rabs_le_inv in Za. apply Rabs_le_inv in Zb. apply Rabs_le.
    assert (B (b64_of_bits (st_off + Z.of_nat i * width)) * R <= y * R) by (apply Rmult_le_compat_r; lra).
    assert (y * R <= B (b64_of_bits (st_off + (Z.of_nat i + 1) * width - 1)) * R) by (apply Rmult_le_compat_r; lra).
    lra. }
  (* rs *)
  assert (Rsb : ((rr - E * 2 ^ 52) mod 2 ^ 64 = rr - E * 2 ^ 52)%Z) by (apply Z.mod_small; lia).
  destruct (scale_bits rr E ltac:(lia) ltac:(lia)) as [Frs Vrs].
  assert (Frs' : finite (rd_rs hb)) by (unfold rd_rs; fold i; fold E; fold rr; rewrite Rsb; exact Frs).
  assert (Vrs' : B (rd_rs hb) = R * bpow radix2 (- E)) by (unfold rd_rs; fold i; fold E; fold rr; rewrite Rsb; exact Vrs).
  set (rs := rd_rs hb) in *.
  (* hh: h with its low 10 bits cleared, on the same exponent *)
  set (f := (Z.pos mx - 2 ^ 52)%Z) in *.
  set (fh := (f / 2 ^ 10 * 2 ^ 10)%Z).
  assert (Fh0 : (0 <= fh <= f)%Z /\ (f - fh < 2 ^ 10)%Z /\ (f < 2 ^ 52)%Z).
  { pose proof (Z.div_mod f (2 ^ 10) ltac:(lia)). pose proof (Z.mod_pos_bound f (2 ^ 10) ltac:(lia)).
    assert (0 <= f / 2 ^ 10)%Z by (apply Z.div_pos; unfold f; lia). unfold fh, f in *. lia. }
  assert (HHb : Z.land hb (Z.lnot 1023) = ((ex + 1075) * 2 ^ 52 + fh)%Z).
  { rewrite hh_bits by lia. rewrite Hbits. fold f.
    replace ((ex + 1075) * 2 ^ 52 + f)%Z with (f + ((ex + 1075) * 2 ^ 42) * 2 ^ 10)%Z by ring.
    rewrite Z.div_add by lia. unfold fh. ring. }
  destruct (normal_bits (Z.land hb (Z.lnot 1023)) ltac:(rewrite HHb; lia)) as [Fhh Vhh].
  change (b64_of_bits (Z.land hb (Z.lnot 1023))) with (rd_hh hb) in Fhh, Vhh.
  rewrite HHb in Vhh.
  replace (((ex + 1075) * 2 ^ 52 + fh) mod 2 ^ 52)%Z with fh in Vhh
    by (rewrite Z.add_comm, Z.mod_add by lia; symmetry; apply Z.mod_small; lia).
  replace (((ex + 1075) * 2 ^ 52 + fh) / 2 ^ 52 - 1075)%Z with ex in Vhh
    by (rewrite Z.add_comm, Z.div_add by lia; rewrite Z.div_small by lia; ring).
  set (hh := rd_hh hb) in *.
  assert (Bh2 : B h = IZR (f + 2 ^ 52) * bpow radix2 ex) by (rewrite Vh; unfold f; f_equal; f_equal; ring).
  pose proof (bpow_gt_0 radix2 ex) as Pex.
  assert (Hsb : fmtF (B h - B hh)).
  { apply sterbenz; [exact _ | exact _ | apply B_fmt | apply B_fmt | ].
    rewrite Bh2, Vhh. assert (IZR (fh + 2 ^ 52) / 2 <= IZR (f + 2 ^ 52) <= 2 * IZR (fh + 2 ^ 52)).
    { rewrite !plus_IZR, IZR_pow2' by lia. pose proof (IZR_le _ _ (proj1 (proj1 Fh0))). pose proof (IZR_le _ _ (proj2 (proj1 Fh0))).
      assert (IZR (f - fh) < IZR (2 ^ 10)) by (apply IZR_lt; lia). rewrite minus_IZR, IZR_pow2' in H1 by lia.
      assert (bpow radix2 10 <= bpow radix2 52) by (apply bpow_le; lia). lra. }
    split; [unfold Rdiv; rewrite Rmult_comm, <- Rmult_assoc; apply Rmult_le_compat_r; lra | ].
    rewrite <- Rmult_assoc. apply Rmult_le_compat_r; lra. }
  assert (Bnd1 : forall v, Rabs v <= 4 -> Rabs v <= bpow radix2 1000).
  { intros v Hv. apply Rle_trans with 4; [exact Hv | change 4 with (bpow radix2 2); apply bpow_le; lia]. }
  assert (Dhh : B h - B hh = IZR (f - fh) * bpow radix2 ex)
    by (rewrite Bh2, Vhh, <- Rmult_minus_distr_r, <- minus_IZR; f_equal; f_equal; ring).
  assert (Ex3 : (ex <= 968)%Z) by lia.
  destruct (fsub_s h hh Fh Fhh) as [Fhl Bhl].
  { rewrite Dhh, Rabs_mult. rewrite (Rabs_pos_eq (bpow radix2 ex)) by apply bpow_ge_0. rewrite <- abs_IZR.
    apply Rle_trans with (IZR (2 ^ 10) * bpow radix2 ex).
    - apply Rmult_le_compat_r; [apply bpow_ge_0 | apply IZR_le; lia].
    - rewrite IZR_pow2', <- bpow_plus by lia. apply bpow_le. lia. }
  rewrite exact_round in Bhl by exact Hsb.
  set (hl := fsub h hh) in *.
  assert (Vhl : B hl = IZR (f - fh) * bpow radix2 ex) by (rewrite Bhl; exact Dhh).
  (* the exponents: ex - E and rb are each 1022 or 1023 *)
  assert (Eyb : (hy / 2 ^ 52 = ex + 1075 - E)%Z).
  { unfold hy. rewrite Hbits. fold f.
    replace ((ex + 1075) * 2 ^ 52 + f - E * 2 ^ 52)%Z with (f + (ex + 1075 - E) * 2 ^ 52)%Z by ring.
    rewrite Z.div_add by lia. rewrite Z.div_small by lia. ring. }
  assert (Rb2 : (Z.of_nat i < 300)%Z -> (1023 <= rb)%Z) by (intros L; specialize (Rlo L); unfold one_bits in Rlo; unfold rb; apply Z.div_le_lower_bound; lia).
  assert (Ey : (1022 <= ex + 1075 - E <= 1023)%Z) by (rewrite <- Eyb, Yb; destruct (Z.of_nat i <? 300)%Z; lia).
  assert (Esum : (2045 <= ex + 1075 - E + rb)%Z).
  { rewrite <- Eyb, Yb. destruct (Z.ltb_spec (Z.of_nat i) 300) as [L | L]; [specialize (Rb2 L); lia | lia]. }
  (* rs on its grid *)
  assert (Brs : B rs = IZR K * bpow radix2 (rb - 1032 - E)).
  { rewrite Vrs', VR, Rmult_assoc, <- bpow_plus. reflexivity. }
  (* y R = h rs *)
  assert (Yr : B h * B rs = y * R) by (unfold y; rewrite Vrs'; ring).
  apply Rabs_le_inv in Yz as Yz'.
  (* hh rs, exactly *)
  set (A := (fh / 2 ^ 10)%Z).
  assert (FA : (fh = A * 2 ^ 10)%Z /\ (2 ^ 42 * 2 ^ 10 <= (A * 2 ^ 10) + 2 ^ 52)%Z /\ (0 <= A < 2 ^ 42)%Z).
  { unfold A, fh. rewrite Z.div_mul by lia. split; [reflexivity | ].
    assert (0 <= f / 2 ^ 10)%Z by (apply Z.div_pos; lia).
    assert (f / 2 ^ 10 < 2 ^ 42)%Z by (apply Z.div_lt_upper_bound; lia). lia. }
  set (q := (ex + rb - 1022 - E)%Z).
  assert (Vp : B hh * B rs = IZR ((A + 2 ^ 42) * K) * bpow radix2 q).
  { rewrite Vhh, Brs. destruct FA as [FA1 _]. rewrite FA1.
    replace (A * 2 ^ 10 + 2 ^ 52)%Z with ((A + 2 ^ 42) * 2 ^ 10)%Z by ring.
    replace q with ((ex + 10) + (rb - 1032 - E))%Z by (unfold q; ring).
    rewrite !mult_IZR, (IZR_pow2' 10) by lia. rewrite !bpow_plus. ring. }
  assert (Fp : fmtF (B hh * B rs)).
  { rewrite Vp. apply (grid_repr q); [unfold q; lia | exists ((A + 2 ^ 42) * K)%Z; reflexivity | ].
    rewrite Rabs_mult, (Rabs_pos_eq (bpow radix2 q)) by apply bpow_ge_0.
    rewrite bpow_plus, (Rmult_comm (bpow radix2 q) (bpow radix2 53)).
    apply Rmult_lt_compat_r; [apply bpow_gt_0 | ]. rewrite <- abs_IZR, <- IZR_pow2' by lia. apply IZR_lt.
    destruct FA as [_ [_ FA3]]. rewrite Z.abs_eq by nia.
    replace (2 ^ 53)%Z with (2 ^ 43 * 2 ^ 10)%Z by reflexivity. apply Z.mul_lt_mono_nonneg; lia. }
  (* hl rs, exactly *)
  assert (Vq : B hl * B rs = IZR ((f - fh) * K) * bpow radix2 (q - 10)).
  { rewrite Vhl, Brs, mult_IZR.
    replace (q - 10)%Z with (ex + (rb - 1032 - E))%Z by (unfold q; ring).
    rewrite bpow_plus. ring. }
  assert (Fq : fmtF (B hl * B rs)).
  { rewrite Vq. apply (grid_repr (q - 10)); [unfold q; lia | exists ((f - fh) * K)%Z; reflexivity | ].
    rewrite Rabs_mult, (Rabs_pos_eq (bpow radix2 (q - 10))) by apply bpow_ge_0.
    rewrite bpow_plus, (Rmult_comm (bpow radix2 (q - 10)) (bpow radix2 53)).
    apply Rmult_lt_compat_r; [apply bpow_gt_0 | ]. rewrite <- abs_IZR, <- IZR_pow2' by lia. apply IZR_lt.
    rewrite Z.abs_eq by nia. assert ((f - fh) * K < 2 ^ 10 * 2 ^ 10)%Z by (apply Z.mul_lt_mono_nonneg; lia). lia. }
  (* the magnitudes: hl <= 2^-42 h *)
  assert (Hlh : 0 <= B hl <= bpow radix2 (-42) * B h).
  { rewrite Vhl, Bh2. pose proof (IZR_le _ _ (proj1 (proj1 Fh0))). pose proof (IZR_le _ _ (proj2 (proj1 Fh0))).
    split; [apply Rmult_le_pos; [apply IZR_le; lia | lra] | ].
    assert (Z1 : ((f - fh) * 2 ^ 42 <= f + 2 ^ 52)%Z) by nia.
    apply IZR_le in Z1. rewrite mult_IZR, IZR_pow2' in Z1 by lia.
    rewrite <- Rmult_assoc. apply Rmult_le_compat_r; [lra | ].
    replace (IZR (f - fh)) with (IZR (f - fh) * bpow radix2 42 * bpow radix2 (-42))
      by (rewrite Rmult_assoc, <- bpow_plus; simpl; ring).
    rewrite (Rmult_comm (bpow radix2 (-42))). apply Rmult_le_compat_r; [apply bpow_ge_0 | exact Z1]. }
  assert (Prs : 0 < B rs) by (rewrite Vrs'; pose proof (bpow_gt_0 radix2 (- E)); nra).
  assert (Z9 : zi <= / 512) by (apply Rle_trans with (1 := Zi); simpl; lra).
  assert (Hpr : / 2 <= B hh * B rs <= 2).
  { replace (B hh * B rs) with (B h * B rs - B hl * B rs) by (rewrite Bhl; ring). rewrite Yr.
    pose proof (bpow_gt_0 radix2 (-42)) as P42.
    assert (B42 : bpow radix2 (-42) <= / 4) by (change (/ 4) with (bpow radix2 (-2)); apply bpow_le; lia).
    assert (X : 0 <= B hl * B rs <= bpow radix2 (-42) * (y * R)) by (rewrite <- Yr; split; nra).
    split; nra. }
  destruct (fmul_s hh rs Fhh (proj1 (conj Frs' Vrs'))) as [Fm1 Bm1]; [apply Bnd1; rewrite Rabs_pos_eq; lra | ].
  rewrite exact_round in Bm1 by exact Fp.
  destruct (fsub_s (fmul hh rs) c_one Fm1 (proj1 c_one_ok)) as [Fm2 Bm2]; [rewrite Bm1, (proj2 c_one_ok); apply Bnd1; apply Rabs_le; lra | ].
  rewrite Bm1, (proj2 c_one_ok), exact_round in Bm2
    by (apply sterbenz; [exact _ | exact _ | exact Fp | apply generic_format_bpow' with (e := 0%Z); [exact _ | unfold FLT_exp, emin, prec; lia] | lra]).
  destruct (fmul_s hl rs Fhl Frs') as [Fm3 Bm3].
  { apply Bnd1. pose proof (bpow_gt_0 radix2 (-42)).
    assert (B42 : bpow radix2 (-42) <= / 4) by (change (/ 4) with (bpow radix2 (-2)); apply bpow_le; lia).
    assert (0 <= B hl * B rs <= bpow radix2 (-42) * (y * R)) by (rewrite <- Yr; split; nra).
    rewrite Rabs_pos_eq by lra. nra. }
  rewrite exact_round in Bm3 by exact Fq.
  (* z = y R - 1, on 2^-62's grid and at most 2^-9 *)
  assert (Zv : (B hh * B rs - 1) + B hl * B rs = y * R - 1) by (rewrite <- Yr, Bhl; ring).
  assert (Gy : on_grid (hy / 2 ^ 52 - 1075) y).
  { rewrite <- Vy. destruct (normal_bits hy Hyr) as [_ V]. rewrite V. exists (hy mod 2 ^ 52 + 2 ^ 52)%Z. reflexivity. }
  assert (GR : on_grid (rb - 1032) R) by (rewrite VR; exists K; reflexivity).
  assert (Gz : on_grid (-62) (y * R - 1)).
  { apply grid_minus.
    - apply (grid_le (hy / 2 ^ 52 - 1075 + (rb - 1032))); [rewrite Eyb; lia | apply grid_mult; assumption].
    - exists (2 ^ 62)%Z. rewrite IZR_pow2' by lia. rewrite <- bpow_plus. reflexivity. }
  assert (B9 : / 2 ^ 9 = bpow radix2 (-9)) by (rewrite <- (bpow_m 9); reflexivity).
  assert (Fz : fmtF (y * R - 1)).
  { destruct (Rlt_le_dec (Rabs (y * R - 1)) (bpow radix2 (-9))) as [L | L].
    - apply (grid_repr (-62)); [lia | exact Gz | exact L].
    - assert (E9 : Rabs (y * R - 1) = bpow radix2 (-9)) by (apply Rle_antisym; [rewrite <- B9; lra | exact L]).
      destruct (Rcase_abs (y * R - 1)) as [N | P].
      + rewrite Rabs_left in E9 by exact N. replace (y * R - 1) with (- bpow radix2 (-9)) by lra.
        apply generic_format_opp, generic_format_bpow. unfold FLT_exp, emin, prec. lia.
      + rewrite Rabs_pos_eq in E9 by lra. rewrite E9. apply generic_format_bpow. unfold FLT_exp, emin, prec. lia. }
  destruct (fadd_s (fsub (fmul hh rs) c_one) (fmul hl rs) Fm2 Fm3) as [Fz' Bz'].
  { rewrite Bm2, Bm3, Zv. apply Bnd1. apply Rabs_le. lra. }
  rewrite Bm2, Bm3, Zv, exact_round in Bz' by exact Fz.
  assert (Ez : rd_z h = fadd (fsub (fmul hh rs) c_one) (fmul hl rs)) by reflexivity.
  rewrite Ez.
  assert (Yr2 : 7 / 10 <= y <= 3 / 2).
  { rewrite <- Vy. destruct (normal_bits hy Hyr) as [_ V]. rewrite V.
    pose proof (Z.mod_pos_bound hy (2 ^ 52) ltac:(lia)) as Mb. pose proof (Z.div_mod hy (2 ^ 52) ltac:(lia)) as Dv.
    destruct (Z.ltb_spec (Z.of_nat i) 300) as [L | L].
    - assert (Q : (hy / 2 ^ 52 = 1022)%Z) by (rewrite Yb; destruct (Z.ltb_spec (Z.of_nat i) 300); [reflexivity | lia]).
      rewrite Q in Dv |- *. change (bpow radix2 (1022 - 1075)) with (/ 9007199254740992).
      assert (F1 : IZR 6305039478318695 <= IZR (hy mod 2 ^ 52 + 2 ^ 52) <= IZR 9007199254740992)
        by (split; apply IZR_le; unfold st_off, width in Hy; lia).
      split; [apply Rmult_le_reg_r with 9007199254740992; [lra | ]; rewrite Rmult_assoc, Rinv_l by lra; lra
             | apply Rmult_le_reg_r with 9007199254740992; [lra | ]; rewrite Rmult_assoc, Rinv_l by lra; lra].
    - assert (Q : (hy / 2 ^ 52 = 1023)%Z) by (rewrite Yb; destruct (Z.ltb_spec (Z.of_nat i) 300); [lia | reflexivity]).
      rewrite Q in Dv |- *. change (bpow radix2 (1023 - 1075)) with (/ 4503599627370496).
      assert (F1 : IZR 4503599627370496 <= IZR (hy mod 2 ^ 52 + 2 ^ 52) <= IZR 6755399441055744)
        by (split; apply IZR_le; unfold st_off, width in Hy; lia).
      split; [apply Rmult_le_reg_r with 4503599627370496; [lra | ]; rewrite Rmult_assoc, Rinv_l by lra; lra
             | apply Rmult_le_reg_r with 4503599627370496; [lra | ]; rewrite Rmult_assoc, Rinv_l by lra; lra]. }
  split; [lia | ]. split; [exact Hi | ]. split; [exact RR | ]. split; [exact Yr2 | ]. split; [split; assumption | ].
  split; [exact Frs' | ]. split; [exact Vrs' | ]. split; [exact Fz' | ]. split; [exact Bz' | ].
  split.
  { rewrite Bz'. destruct (Req_dec (y * R - 1) 0) as [Z0 | N0]; [left; exact Z0 | right; apply grid_nonzero; assumption]. }
  split.
  { exists zi. split; [exact Zi | ]. split; [rewrite Bz'; exact Yz | ]. split.
    - intros Nb. destruct (Zn Nb) as [T1 T2]. unfold st_th, st_tl. fold t. rewrite T1, T2.
      split; [reflexivity | split; [reflexivity | ]].
      apply Rone in Nb. unfold R, st_r. fold rr. rewrite Nb. exact (proj2 c_one_ok).
    - exact Zf. }
  repeat split; assumption.
Qed.
