(** Discrete binary64 input bounds and real exponential range for exp2. *)
From Coq Require Import ZArith Reals Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Mul Grid Encodings RoundingConstant.
Require Import ExpFast Ln1pLemmas Ln1pReduction.
Open Scope R_scope.

Lemma exp2_integer k : exp (IZR k * ln 2) = bpow radix2 k.
Proof.
 rewrite bpow_powerRZ, powerRZ_Rpower by (simpl; lra).
 unfold Rpower. reflexivity.
Qed.
Lemma exp_monotone a b : a <= b -> exp a <= exp b.
Proof. intros H. destruct (Rle_lt_or_eq_dec _ _ H); [apply Rlt_le, exp_increasing; assumption | subst; lra]. Qed.

Lemma exp2_below_overflow x : finite x -> B x < 1024 ->
 exp (B x * ln 2) <= bpow radix2 1024 * (1 - / 2 ^ 46).
Proof.
 intros Fx X.
 assert (Xp : B x <= 1024 - / 2 ^ 43).
 { destruct (Rlt_or_le (B x) 512) as [S | S]; [interval with (i_prec 80) | ].
   assert (G : on_grid (-43) (1024 - B x)).
   { apply grid_minus.
     - exists 9007199254740992%Z. bpow_num. field.
     - apply (grid_fmt_bound (FLT_exp emin prec) 9); [intros e; unfold FLT_exp, emin, prec; lia | apply B_fmt | ].
       right. rewrite Rabs_pos_eq by lra. change (bpow radix2 9) with 512. lra. }
   pose proof (grid_nonzero _ _ G ltac:(lra)) as Gn.
   rewrite Rabs_pos_eq in Gn by lra. bpow_num_in Gn.
   assert (/ 2 ^ 43 = / 8796093022208) by (f_equal; ring). lra. }
 assert (L : 0 < ln 2) by interval with (i_prec 64).
 apply Rle_trans with (exp ((1024 - / 2 ^ 43) * ln 2)).
 - apply exp_monotone. nra.
 - replace ((1024 - / 2 ^ 43) * ln 2) with (1024 * ln 2 + (- / 2 ^ 43 * ln 2)) by ring.
   rewrite exp_plus, (exp2_integer 1024).
   apply Rmult_le_compat_l; [apply bpow_ge_0 | interval with (i_prec 120)].
Qed.

Lemma exp2_round_finite x : finite x -> B x < 1024 ->
 Rabs (rndF (exp (B x * ln 2))) < bpow radix2 1024.
Proof.
 intros Fx X. pose proof (exp2_below_overflow x Fx X) as Eb.
 set (mx := IZR (2 ^ 53 - 1) * bpow radix2 971).
 assert (Fmx : fmtF mx).
 { apply generic_format_FLT. exists (Float radix2 (2 ^ 53 - 1) 971);
   [reflexivity | unfold prec; simpl; lia | unfold emin; simpl; lia]. }
 assert (B971 : bpow radix2 971 = 2 ^ 971)
   by (change 971%Z with (Z.of_nat 971); rewrite bpow_powerRZ, <- pow_powerRZ; reflexivity).
 assert (Mx : mx = 9007199254740991 * 2 ^ 971) by (unfold mx; rewrite B971; reflexivity).
 assert (B1024 : bpow radix2 1024 = 2 ^ 1024)
   by (change 1024%Z with (Z.of_nat 1024); rewrite bpow_powerRZ, <- pow_powerRZ; reflexivity).
 assert (Le : Rabs (exp (B x * ln 2)) <= mx).
 { rewrite Rabs_pos_eq by (apply Rlt_le, exp_pos). rewrite Mx.
   apply Rle_trans with (1 := Eb). rewrite B1024. interval with (i_prec 64). }
 pose proof (abs_round_le_generic radix2 (FLT_exp emin prec) (Znearest ne) _ _ Fmx Le) as R1.
 apply Rle_lt_trans with (1 := R1). rewrite Mx, B1024. interval with (i_prec 64).
Qed.
