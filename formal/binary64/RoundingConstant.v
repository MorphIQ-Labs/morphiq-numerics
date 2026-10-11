(** exp/mod.rs's [decide]: the rounding test with a constant absolute bound
    and the exact scaling on the exponent field (docs/exp.md, section 7),
    transcribed on binary64 and proved.

    The test returns [RN(y + RN(l − E))] when it equals [RN(y + RN(l + E))].
    If [|Z − (y + l)| <= ε], and [E] exceeds [ε] by at least the rounding
    error of [l ± E], then [y + RN(l − E) <= Z <= y + RN(l + E)], and rounding
    is monotone, so both bounds rounding alike forces [RN(Z)] to the same
    value ([const_test_real]). No property of [Z] beyond the bound is used:
    it may even be a rounding breakpoint. Scaling by [2^k] then adds [k] to
    the exponent field of the positive normal result, which is exact while
    both stay normal ([decide_const_ok]). *)

From Coq Require Import ZArith Reals Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 Encodings RoundingGaps RoundingCore.
From Binary64 Require RoundingTest.

Open Scope R_scope.

(** Rounding errs by at most [2^(em − 54)] below [2^em] in magnitude. *)
Lemma rnd_err_below v em : (-1021 <= em)%Z -> Rabs v <= bpow radix2 em ->
  Rabs (rndF v - v) <= bpow radix2 (em - 54).
Proof.
  intros He Hv. destruct (Req_dec v 0) as [Z0 | Nz].
  { rewrite Z0, round_0 by apply valid_rnd_N. rewrite Rminus_0_r, Rabs_R0. apply bpow_ge_0. }
  destruct (Rle_lt_or_eq_dec _ _ Hv) as [Lt | Eq].
  - apply Rle_trans with (/ 2 * ulp radix2 (FLT_exp emin prec) v).
    + apply error_le_half_ulp. exact _.
    + rewrite ulp_neq_0 by exact Nz. unfold cexp.
      pose proof (mag_le_bpow radix2 v em Nz Lt) as M.
      replace (em - 54)%Z with (-1 + (em - 53))%Z by ring. rewrite bpow_plus.
      change (bpow radix2 (-1)) with (/ 2).
      apply Rmult_le_compat_l; [lra | apply bpow_le]. unfold FLT_exp, emin, prec. lia.
  - (* |v| = 2^em is representable *)
    assert (F : fmtF v).
    { destruct (Rcase_abs v) as [Neg | Pos].
      - rewrite Rabs_left in Eq by exact Neg. replace v with (- bpow radix2 em) by lra.
        apply generic_format_opp, generic_format_bpow. unfold FLT_exp, emin, prec. lia.
      - rewrite Rabs_pos_eq in Eq by lra. rewrite Eq.
        apply generic_format_bpow. unfold FLT_exp, emin, prec. lia. }
    rewrite round_generic by (auto with typeclass_instances || exact F).
    rewrite Rminus_diag_eq, Rabs_R0 by reflexivity. apply bpow_ge_0.
Qed.

(** The test's real-number core. *)
Theorem const_test_real (y l E z eps : R) (em : Z) :
  (-1021 <= em)%Z -> 0 <= E -> Rabs l + E <= bpow radix2 em ->
  eps + bpow radix2 (em - 54) <= E -> Rabs (z - (y + l)) <= eps ->
  rndF (y + rndF (l - E)) = rndF (y + rndF (l + E)) ->
  rndF z = rndF (y + rndF (l - E)).
Proof.
  intros He E0 Hl Heps HZ Heq.
  assert (B1 : Rabs (l - E) <= bpow radix2 em).
  { pose proof (Rabs_triang l (- E)) as T. rewrite Rabs_Ropp, (Rabs_pos_eq E) in T by lra.
    unfold Rminus. lra. }
  assert (B2 : Rabs (l + E) <= bpow radix2 em).
  { pose proof (Rabs_triang l E) as T. rewrite (Rabs_pos_eq E) in T by lra. lra. }
  pose proof (rnd_err_below _ em He B1) as R1. pose proof (rnd_err_below _ em He B2) as R2.
  apply Rabs_le_inv in R1. apply Rabs_le_inv in R2. apply Rabs_le_inv in HZ.
  assert (Lo : y + rndF (l - E) <= z) by lra.
  assert (Hi : z <= y + rndF (l + E)) by lra.
  apply Rle_antisym.
  - rewrite Heq. apply round_le; auto with typeclass_instances.
  - apply round_le; auto with typeclass_instances.
Qed.

(** exp/mod.rs's [decide]: [low = y + (l − e)], [high = y + (l + e)], and
    [low.to_bits().wrapping_add((k << 52) as u64)] when [low == high]. *)
Definition decide_const (y l e : f64) (k : Z) : option f64 :=
  let low := fadd y (fsub l e) in
  let high := fadd y (fadd l e) in
  match Bcompare 53 1024 low high with
  | Some Eq => Some (b64_of_bits ((bits_of_b64 low + k * 2 ^ 52) mod 2 ^ 64))
  | _ => None
  end.

(** An operation whose exact result is at most 16 in magnitude is finite
    and rounds as the binary64 model does. *)
Lemma fadd16 x y : finite x -> finite y -> Rabs (B x + B y) <= 16 ->
  finite (fadd x y) /\ B (fadd x y) = rndF (B x + B y).
Proof.
  intros Fx Fy H. apply (fadd_ok 1 4 x y Fx Fy ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)).
  unfold bnd. change (bpow radix2 4) with 16. lra.
Qed.
Lemma fsub16 x y : finite x -> finite y -> Rabs (B x - B y) <= 16 ->
  finite (fsub x y) /\ B (fsub x y) = rndF (B x - B y).
Proof.
  intros Fx Fy H. apply (fsub_ok 1 4 x y Fx Fy ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)).
  unfold bnd. change (bpow radix2 4) with 16. lra.
Qed.
Lemma fmul16 x y : finite x -> finite y -> Rabs (B x * B y) <= 16 ->
  finite (fmul x y) /\ B (fmul x y) = rndF (B x * B y).
Proof.
  intros Fx Fy H. apply (fmul_ok 1 4 x y Fx Fy ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia)).
  unfold bnd. change (bpow radix2 4) with 16. lra.
Qed.

Theorem decide_const_ok y l e k (z eps : R) (em : Z) v :
  finite y -> finite l -> finite e -> Rabs (B y) <= 4 ->
  (-1021 <= em <= 0)%Z -> 0 <= B e -> Rabs (B l) + B e <= bpow radix2 em ->
  eps + bpow radix2 (em - 54) <= B e -> Rabs (z - (B y + B l)) <= eps ->
  9 / 10 <= z <= 21 / 10 -> (-1016 <= k <= 1016)%Z ->
  decide_const y l e k = Some v ->
  finite v /\ B v = rndF (z * bpow radix2 k).
Proof.
  intros Fy Fl Fe Hy Hem E0 Hl Heps HZ Zr Hk Hd.
  assert (Pem : bpow radix2 em <= 1) by (change 1 with (bpow radix2 0); apply bpow_le; lia).
  destruct (fsub16 l e Fl Fe) as [F1 B1].
  { pose proof (Rabs_triang (B l) (- B e)) as T. rewrite Rabs_Ropp, (Rabs_pos_eq (B e)) in T by lra.
    unfold Rminus. lra. }
  destruct (fadd16 l e Fl Fe) as [F2 B2].
  { apply Rle_trans with (Rabs (B l) + Rabs (B e)); [apply Rabs_triang | rewrite (Rabs_pos_eq (B e)) by lra; lra]. }
  assert (Small : forall w, Rabs w <= 1 -> Rabs (rndF w) <= 1).
  { intros w Hw. apply abs_round_le_generic; auto with typeclass_instances.
    change 1 with (bpow radix2 0). apply generic_format_bpow. unfold FLT_exp, emin, prec. lia. }
  assert (S1 : Rabs (B (fsub l e)) <= 1).
  { rewrite B1. apply Small. apply Rle_trans with (Rabs (B l) + Rabs (B e));
      [unfold Rminus; rewrite <- (Rabs_Ropp (B e)); apply Rabs_triang | rewrite (Rabs_pos_eq (B e)) by lra; lra]. }
  assert (S2 : Rabs (B (fadd l e)) <= 1).
  { rewrite B2. apply Small. apply Rle_trans with (Rabs (B l) + Rabs (B e));
      [apply Rabs_triang | rewrite (Rabs_pos_eq (B e)) by lra; lra]. }
  destruct (fadd16 y (fsub l e) Fy F1) as [F3 B3].
  { apply Rle_trans with (Rabs (B y) + Rabs (B (fsub l e))); [apply Rabs_triang | lra]. }
  destruct (fadd16 y (fadd l e) Fy F2) as [F4 B4].
  { apply Rle_trans with (Rabs (B y) + Rabs (B (fadd l e))); [apply Rabs_triang | lra]. }
  unfold decide_const in Hd. cbv zeta in Hd.
  set (low := fadd y (fsub l e)) in *. set (high := fadd y (fadd l e)) in *.
  destruct (Bcompare 53 1024 low high) as [[ | | ] | ] eqn:C; try discriminate.
  injection Hd as Hv.
  rewrite Bcompare_correct in C by assumption. injection C as C. apply Rcompare_Eq_inv in C.
  (* RN(Z) = low *)
  assert (RZ : rndF z = B low).
  { rewrite B3, B1.
    apply (const_test_real (B y) (B l) (B e) z eps em ltac:(lia) E0 Hl Heps HZ).
    rewrite <- B1, <- B2, <- B3, <- B4. exact C. }
  (* low is a positive normal number near z *)
  assert (Zn : bpow radix2 (-1022) <= Rabs z).
  { rewrite Rabs_pos_eq by lra. apply Rle_trans with (9 / 10); [ | lra].
    apply Rle_trans with (bpow radix2 (-1)); [apply bpow_le; lia | change (bpow radix2 (-1)) with (/ 2); lra]. }
  pose proof (rnd_rel z Zn) as RR. change (round radix2 fexp64 (Znearest (fun n => negb (Z.even n))) z) with (rndF z) in RR.
  rewrite RZ, (Rabs_pos_eq z) in RR by lra. apply Rabs_le_inv in RR.
  assert (P53 : bpow radix2 (-53) = / 9007199254740992) by reflexivity. rewrite P53 in RR.
  assert (Lr : 1 / 2 <= B low < 4) by (split; nra).
  assert (Ln : bpow radix2 (-1022) <= B low)
    by (apply Rle_trans with (1 / 2); [apply Rle_trans with (bpow radix2 (-1)); [apply bpow_le; lia | change (bpow radix2 (-1)) with (/ 2); lra] | lra]).
  destruct (pos_normal low F3 Ln) as [mx [ex [Hx [_ [Mx [Ex [V [_ [_ Bits]]]]]]]]].
  (* its exponent: 2^(52+ex) <= low < 2^(53+ex) *)
  assert (A1 : bpow radix2 (52 + ex) <= B low).
  { rewrite bpow_plus, V. apply Rmult_le_compat_r; [apply bpow_ge_0 | ].
    replace (bpow radix2 52) with (IZR (2 ^ 52)) by reflexivity. apply IZR_le. lia. }
  assert (A2 : B low < bpow radix2 (53 + ex)).
  { rewrite bpow_plus, V. apply Rmult_lt_compat_r; [apply bpow_gt_0 | ].
    replace (bpow radix2 53) with (IZR (2 ^ 53)) by reflexivity. apply IZR_lt. lia. }
  assert (Ex1 : (52 + ex < 2)%Z).
  { apply (lt_bpow radix2). change (bpow radix2 2) with 4. lra. }
  assert (Ex2 : (-1 < 53 + ex)%Z).
  { apply (lt_bpow radix2). change (bpow radix2 (-1)) with (/ 2). lra. }
  (* the encoding plus k·2^52 is the encoding of low·2^k *)
  assert (Eb : ((bits_of_b64 low + k * 2 ^ 52) mod 2 ^ 64
                = join_bits 52 11 false (Z.pos mx - 2 ^ 52) (ex + 1075 + k))%Z).
  { rewrite Bits, !join_eq.
    replace ((ex + 1075) * 2 ^ 52 + (Z.pos mx - 2 ^ 52) + k * 2 ^ 52)%Z
      with ((ex + 1075 + k) * 2 ^ 52 + (Z.pos mx - 2 ^ 52))%Z by ring.
    apply Z.mod_small. lia. }
  assert (Ev : v = b64_of_bits (join_bits 52 11 false (Z.pos mx - 2 ^ 52) (ex + 1075 + k)))
    by (rewrite <- Hv; f_equal; exact Eb).
  rewrite Ev.
  destruct (join_val (Z.pos mx - 2 ^ 52) (ex + 1075 + k) ltac:(lia) ltac:(lia)) as [Fv Bv].
  split; [exact Fv | ]. rewrite Bv.
  replace (Z.pos mx - 2 ^ 52 + 2 ^ 52)%Z with (Z.pos mx) by ring.
  replace (ex + 1075 + k - 1075)%Z with (ex + k)%Z by ring.
  assert (Mz : (0 <= mag radix2 z)%Z).
  { apply mag_ge_bpow. rewrite Rabs_pos_eq by lra. change (bpow radix2 (0 - 1)) with (/ 2). lra. }
  rewrite RoundingTest.round_scale by (lra || lia).
  rewrite RZ, V, bpow_plus. ring.
Qed.
