(** [ln_1p]'s stage rounding test (docs/ln.md, section 7), transcribed on
    binary64 and proved: [decide s lo eps] returns [lb = RN(s + RN(lo − eps))]
    when it equals [ub = RN(s + RN(lo + eps))]. Then every real [w] within
    [eps − 2^-53·(|lo| + eps)] of [s + lo] rounds to [lb] ([decide_ok]):
    [s + RN(lo − eps) <= w <= s + RN(lo + eps)], and rounding is monotone. No
    property of [w] beyond the distance is used; in particular [w] may be a
    rounding breakpoint, and any [w] that close, the exact result and today's
    accurate value alike, rounds to the same [lb]. *)

From Coq Require Import ZArith Reals Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 Grid RoundingCore.
Require Import Ln1pReduction.

Open Scope R_scope.

(** Rounding a sum of two binary64 numbers errs by at most [2^-53] of it:
    relatively above [2^-1022], and not at all below, where the sum is exact. *)
Lemma rnd_sum_err a b : fmtF a -> fmtF b -> Rabs (rndF (a + b) - (a + b)) <= bpow radix2 (-53) * Rabs (a + b).
Proof.
  intros Fa Fb.
  destruct (Rle_lt_dec (bpow radix2 (-1022)) (Rabs (a + b))) as [L | L].
  - exact (rnd_rel (a + b) L).
  - assert (Ga : on_grid (-1074) a)
      by (apply (grid_le (cexp radix2 (FLT_exp emin prec) a)); [unfold cexp, FLT_exp, emin, prec; lia | apply grid_fmt, Fa]).
    assert (Gb : on_grid (-1074) b)
      by (apply (grid_le (cexp radix2 (FLT_exp emin prec) b)); [unfold cexp, FLT_exp, emin, prec; lia | apply grid_fmt, Fb]).
    assert (F : fmtF (a + b)).
    { apply (grid_repr (-1074)); [lia | apply grid_plus; assumption | ].
      apply Rlt_le_trans with (1 := L). apply bpow_le. lia. }
    rewrite exact_round by exact F. rewrite Rminus_diag_eq, Rabs_R0 by reflexivity.
    apply Rmult_le_pos; [apply bpow_ge_0 | apply Rabs_pos].
Qed.

(** The same, as a relative error [d]. *)
Lemma rnd_sum_rel a b : fmtF a -> fmtF b ->
  exists d, Rabs d <= bpow radix2 (-53) /\ rndF (a + b) = (a + b) * (1 + d).
Proof.
  intros Fa Fb. pose proof (rnd_sum_err a b Fa Fb) as E.
  destruct (Req_dec (a + b) 0) as [Z | N].
  - exists 0. split; [rewrite Rabs_R0; apply bpow_ge_0 | ].
    rewrite Z, round_0 by exact _. ring.
  - exists ((rndF (a + b) - (a + b)) / (a + b)). split.
    + unfold Rdiv. rewrite Rabs_mult, Rabs_Rinv by exact N.
      apply Rmult_le_reg_r with (Rabs (a + b)); [apply Rabs_pos_lt, N | ].
      rewrite Rmult_assoc, Rinv_l, Rmult_1_r by (apply Rabs_no_R0, N). exact E.
    + field. exact N.
Qed.

(** * The test *)

Definition decide (s lo eps : f64) : option f64 :=
  let lb := fadd s (fsub lo eps) in
  let ub := fadd s (fadd lo eps) in
  match Bcompare 53 1024 lb ub with
  | Some Eq => Some lb
  | _ => None
  end.

Theorem decide_bounded_ok s lo eps v :
  finite s -> finite lo -> finite eps -> 0 <= B eps ->
  Rabs (B s) <= bpow radix2 999 -> Rabs (B lo) + B eps <= bpow radix2 999 ->
  decide s lo eps = Some v ->
  finite v /\ forall w, Rabs (w - (B s + B lo)) + bpow radix2 (-53) * (Rabs (B lo) + B eps) <= B eps -> rndF w = B v.
Proof.
  intros Fs Fl Fe E0 Hs Hl Hd.
  assert (P1 : 1 <= bpow radix2 999) by (change 1 with (bpow radix2 0); apply bpow_le; lia).
  assert (P2 : 2 * bpow radix2 999 = bpow radix2 1000) by (change 2 with (bpow radix2 1); rewrite <- bpow_plus; reflexivity).
  assert (A1 : Rabs (B lo - B eps) <= Rabs (B lo) + B eps)
    by (unfold Rminus; apply Rle_trans with (1 := Rabs_triang _ _); rewrite Rabs_Ropp, (Rabs_pos_eq (B eps)) by lra; lra).
  assert (A2 : Rabs (B lo + B eps) <= Rabs (B lo) + B eps)
    by (apply Rle_trans with (1 := Rabs_triang _ _); rewrite (Rabs_pos_eq (B eps)) by lra; lra).
  destruct (fsub_s lo eps Fl Fe) as [F1 B1]; [lra | ].
  destruct (fadd_s lo eps Fl Fe) as [F2 B2]; [lra | ].
  pose proof (rnd_sum_err (B lo) (- B eps) (B_fmt lo) (generic_format_opp _ _ _ (B_fmt eps))) as R1.
  pose proof (rnd_sum_err (B lo) (B eps) (B_fmt lo) (B_fmt eps)) as R2.
  replace (B lo + - B eps) with (B lo - B eps) in R1 by ring. rewrite <- B1 in R1. rewrite <- B2 in R2.
  pose proof (bpow_ge_0 radix2 (-53)) as P53.
  assert (One : fmtF (bpow radix2 999)) by ( apply generic_format_bpow; unfold FLT_exp, emin, prec; lia).
  assert (M1 : Rabs (B (fsub lo eps)) <= bpow radix2 999) by (rewrite B1; apply abs_round_le_generic; [exact _ | exact _ | exact One | lra]).
  assert (M2 : Rabs (B (fadd lo eps)) <= bpow radix2 999) by (rewrite B2; apply abs_round_le_generic; [exact _ | exact _ | exact One | lra]).
  destruct (fadd_s s (fsub lo eps) Fs F1) as [F3 B3].
  { apply Rle_trans with (1 := Rabs_triang _ _). lra. }
  destruct (fadd_s s (fadd lo eps) Fs F2) as [F4 B4].
  { apply Rle_trans with (1 := Rabs_triang _ _). lra. }
  unfold decide in Hd. cbv zeta in Hd.
  destruct (Bcompare 53 1024 (fadd s (fsub lo eps)) (fadd s (fadd lo eps))) as [[ | | ] | ] eqn:C; try discriminate.
  injection Hd as <-.
  rewrite Bcompare_correct in C by assumption. injection C as C. apply Rcompare_Eq_inv in C.
  split; [exact F3 | ].
  intros w Hw.
  apply Rabs_le_inv in R1. apply Rabs_le_inv in R2.
  assert (Lo : B s + B (fsub lo eps) <= w).
  { assert (Rabs (w - (B s + B lo)) <= B eps - bpow radix2 (-53) * (Rabs (B lo) + B eps)) by lra.
    apply Rabs_le_inv in H. assert (bpow radix2 (-53) * Rabs (B lo - B eps) <= bpow radix2 (-53) * (Rabs (B lo) + B eps))
      by (apply Rmult_le_compat_l; lra). lra. }
  assert (Hi : w <= B s + B (fadd lo eps)).
  { assert (Rabs (w - (B s + B lo)) <= B eps - bpow radix2 (-53) * (Rabs (B lo) + B eps)) by lra.
    apply Rabs_le_inv in H. assert (bpow radix2 (-53) * Rabs (B lo + B eps) <= bpow radix2 (-53) * (Rabs (B lo) + B eps))
      by (apply Rmult_le_compat_l; lra). lra. }
  apply Rle_antisym.
  - rewrite C, B4. apply round_le; [exact _ | exact _ | exact Hi].
  - rewrite B3. apply round_le; [exact _ | exact _ | exact Lo].

Qed.

Theorem decide_ok s lo eps v :
  finite s -> finite lo -> finite eps -> 0 <= B eps ->
  Rabs (B s) <= bpow radix2 999 -> Rabs (B lo) + B eps <= 1 ->
  decide s lo eps = Some v ->
  finite v /\ forall w, Rabs (w - (B s + B lo)) + bpow radix2 (-53) * (Rabs (B lo) + B eps) <= B eps -> rndF w = B v.
Proof.
 intros Fs Fl Fe E0 Hs Hl Hd.
 apply decide_bounded_ok; try assumption.
 apply Rle_trans with 1; [exact Hl | change 1 with (bpow radix2 0); apply bpow_le; lia].
Qed.
