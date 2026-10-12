(** exp2's exponential stages, from exact dyadic reduction through the
    binary64 interval test and normal power-of-two scaling. *)
From Coq Require Import ZArith Reals Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add Grid Encodings RoundingConstant.
From Interval Require Import Tactic.
Require Import StageGappa ExpStageA ExpStageB ExpStageReduction Exp2Constants Exp2Reduction Exp2Product Ln1pLemmas Ln1pReduction.
Open Scope R_scope.

Lemma exp_local_lipschitz a b : Rabs a <= / 1024 -> Rabs b <= / 1024 ->
 Rabs (exp a - exp b) <= 2 * Rabs (a - b).
Proof.
 intros Aa Ab. apply Rabs_le_inv in Aa. apply Rabs_le_inv in Ab.
 assert (Step : forall a b, - / 1024 <= a <= / 1024 -> - / 1024 <= b <= / 1024 -> a < b ->
   Rabs (exp b - exp a) <= 2 * Rabs (b - a)).
 { intros u v U V Lt.
   destruct (MVT_cor2 exp exp u v Lt ltac:(intros c Hc; apply derivable_pt_lim_exp)) as [c [Ec [Cu Cv]]].
   assert (C : Rabs (exp c) <= 2).
   { rewrite Rabs_pos_eq by (apply Rlt_le, exp_pos). assert (- / 1024 <= c <= / 1024) by lra. interval with (i_prec 64). }
   rewrite Ec, Rabs_mult. apply Rmult_le_compat_r; [apply Rabs_pos | exact C]. }
 destruct (Rtotal_order a b) as [Lt | [Eq | Gt]].
 - rewrite (Rabs_minus_sym (exp a)), (Rabs_minus_sym a). apply Step; lra.
 - subst b. rewrite !Rminus_diag_eq, !Rabs_R0 by reflexivity. lra.
 - apply Step; lra.
Qed.

Lemma exp2_residual_range d : Rabs d <= bpow radix2 (-10) ->
 Rabs (d * ln 2) <= 0.000677 /\ Rabs (d * B e2_lh) <= 0.000677.
Proof.
 intros Ad.
 assert (L : Rabs (ln 2) <= 0.693148) by interval with (i_prec 64).
 assert (H : Rabs (B e2_lh) <= 0.693148) by (rewrite e2_lh_val; interval with (i_prec 64)).
 split; rewrite Rabs_mult; apply Rle_trans with (bpow radix2 (-10) * 0.693148);
 [apply Rmult_le_compat; try apply Rabs_pos; assumption | bpow_num; lra
 |apply Rmult_le_compat; try apply Rabs_pos; assumption | bpow_num; lra].
Qed.

Definition e2_a_value d j := stage_a_at (fmul d e2_lh) j.
Definition e2_b_value d j := let '(rh,rt) := exp2_product d in stage_b_at rh rt j.

Lemma e2_a_value_ok d j : finite d -> Rabs (B d) <= bpow radix2 (-10) -> (j < 512)%nat ->
 let '(y,l) := e2_a_value d j in
 finite y /\ finite l /\ Rabs (B y) <= 4 /\ Rabs (B l) <= IZR 181 * bpow radix2 (-17) /\
 Rabs (exp (INR j * ln 2 / 512) * exp (B d * ln 2) - (B y + B l)) <=
   IZR 302 * bpow radix2 (-69) + bpow radix2 (-63).
Proof.
 intros Fd Ad Hj. destruct (exp2_residual_range (B d) Ad) as [Rt Rh].
 destruct (fmul_s d e2_lh Fd e2_lh_finite) as [Fr Br].
 { apply Rle_trans with (1 := Rh). apply Rle_trans with 1; [lra | change 1 with (bpow radix2 0); apply bpow_le; lia]. }
 assert (Br' : B (fmul d e2_lh) = StageGappa.rn (B d * B e2_lh + 0)).
 { rewrite Rplus_0_r. exact Br. }
 pose proof (stage_a_at_ok (fmul d e2_lh) j (B d * B e2_lh) 0 Fr Br' Rh ltac:(rewrite Rabs_R0; apply bpow_ge_0) Hj) as AV.
 unfold e2_a_value. revert AV. generalize (stage_a_at (fmul d e2_lh) j). intros [y l] [Fy [Fl [Hy [Hl Err]]]].
 assert (T : Rabs (exp (INR j * ln 2 / 512)) <= 2).
 { assert (J : 0 <= INR j <= 511) by (split; [apply pos_INR | replace 511 with (INR 511) by (rewrite INR_IZR_INZ; reflexivity); apply le_INR; lia]).
   generalize (INR j) J. intros q Hq. interval with (i_prec 64). }
 assert (Delta : Rabs (B d * ln 2 - B d * B e2_lh) <= bpow radix2 (-65)).
 { replace (B d * ln 2 - B d * B e2_lh) with (B d * (ln 2 - B e2_lh)) by ring.
   rewrite Rabs_mult, Rabs_minus_sym.
   apply Rle_trans with (bpow radix2 (-10) * / 2 ^ 55).
   - apply Rmult_le_compat; try apply Rabs_pos; [exact Ad | exact e2_lh_close].
   - bpow_num. interval with (i_prec 100). }
 pose proof (exp_local_lipschitz (B d * ln 2) (B d * B e2_lh) ltac:(lra) ltac:(lra)) as Lip.
 assert (Diff : Rabs (exp (INR j * ln 2 / 512) * exp (B d * ln 2) - exp (INR j * ln 2 / 512) * exp (B d * B e2_lh)) <= bpow radix2 (-63)).
 { replace (exp (INR j * ln 2 / 512) * exp (B d * ln 2) - exp (INR j * ln 2 / 512) * exp (B d * B e2_lh)) with
     (exp (INR j * ln 2 / 512) * (exp (B d * ln 2) - exp (B d * B e2_lh))) by ring.
   rewrite Rabs_mult. apply Rle_trans with (2 * (2 * bpow radix2 (-65))).
   - apply Rmult_le_compat; try apply Rabs_pos; [exact T | lra].
   - bpow_num. lra. }
 repeat split; try assumption.
 replace (exp (INR j * ln 2 / 512) * exp (B d * ln 2) - (B y + B l)) with
  ((exp (INR j * ln 2 / 512) * exp (B d * ln 2) - exp (INR j * ln 2 / 512) * exp (B d * B e2_lh)) +
   (exp (INR j * ln 2 / 512) * exp (B d * B e2_lh) - (B y + B l))) by ring.
 apply Rle_trans with (1 := Rabs_triang _ _). lra.
Qed.

Lemma e2_b_value_ok d j : finite d -> Rabs (B d) <= bpow radix2 (-10) ->
 (B d = 0 \/ bpow radix2 (-62) <= Rabs (B d)) -> (j < 512)%nat ->
 let '(y,l) := e2_b_value d j in
 finite y /\ finite l /\ Rabs (B y) <= 4 /\ Rabs (B l) <= bpow radix2 (-20) /\
 Rabs (exp (INR j * ln 2 / 512) * exp (B d * ln 2) - (B y + B l)) <= IZR 209 * bpow radix2 (-78).
Proof.
 intros Fd Ad Dlo Hj. pose proof (exp2_product_ok d Fd Ad Dlo) as P.
 unfold e2_b_value. revert P. generalize (exp2_product d). intros [rh rt] [Fh [Ft [Gh [Ah [At Err]]]]].
 apply stage_b_at_ok; try assumption. exact (proj1 (exp2_residual_range (B d) Ad)).
Qed.

Definition c_e2a : f64 := b64_of_bits 4341470040785158144.
Lemma c_e2a_ok : finite c_e2a /\ B c_e2a = bpow radix2 (-59).
Proof. exact (enc_pow2 (-59) ltac:(lia)). Qed.

Definition exp2_a x :=
 let '(_,j,k,d) := exp2_reduce x in
 let '(y,l) := e2_a_value d (Z.to_nat j) in decide_const y l c_e2a k.
Definition exp2_b x :=
 let '(_,j,k,d) := exp2_reduce x in
 let '(y,l) := e2_b_value d (Z.to_nat j) in decide_const y l c_eb k.

Lemma e2_split x ni j k d : ni = (512*k+j)%Z -> (0 <= j)%Z -> d = x - IZR ni / 512 ->
 exp (x * ln 2) = exp (INR (Z.to_nat j) * ln 2 / 512) * exp (d * ln 2) * bpow radix2 k.
Proof.
 intros Hni Hj Hd. rewrite <- ExpStageA.exp_split. f_equal.
 rewrite Z2Nat.id by exact Hj. rewrite <- Hni. unfold L. rewrite Hd. field.
Qed.

Theorem exp2_a_ok x v : finite x -> bpow radix2 (-55) <= Rabs (B x) -> Rabs (B x) < 1016 ->
 exp2_a x = Some v -> finite v /\ B v = rndF (exp (B x * ln 2)).
Proof.
 intros Fx Xlo Xhi. pose proof (exp2_reduce_ok x Fx Xlo Xhi) as RD.
 unfold exp2_a. revert RD. generalize (exp2_reduce x). intros [[[n j] k] d] [ni [Fn [Bn [Ni [JK [J K]]]]]].
 destruct K as [K [Fd [Bd [Ad Dlo]]]].
 assert (Jn : (Z.to_nat j < 512)%nat) by lia.
 pose proof (e2_a_value_ok d (Z.to_nat j) Fd Ad Jn) as AV.
 revert AV. generalize (e2_a_value d (Z.to_nat j)). intros [y l] [Fy [Fl [Hy [Hl Err]]]] Hd.
 rewrite (e2_split (B x) ni j k (B d) JK ltac:(lia) Bd).
 destruct c_e2a_ok as [Fe Be].
 apply (decide_const_ok y l c_e2a k (exp (INR (Z.to_nat j) * ln 2 / 512) * exp (B d * ln 2))
   (IZR 302 * bpow radix2 (-69) + bpow radix2 (-63)) (-9) v Fy Fl Fe Hy ltac:(lia)); try assumption.
 - rewrite Be. apply bpow_ge_0.
 - rewrite Be. bpow_num_all. lra.
 - rewrite Be. change (-9 - 54)%Z with (-63)%Z. bpow_num_all. lra.
 - apply z_range; [exact Jn | exact (proj1 (exp2_residual_range (B d) Ad))].
Qed.

Theorem exp2_b_ok x v : finite x -> bpow radix2 (-55) <= Rabs (B x) -> Rabs (B x) < 1016 ->
 exp2_b x = Some v -> finite v /\ B v = rndF (exp (B x * ln 2)).
Proof.
 intros Fx Xlo Xhi. pose proof (exp2_reduce_ok x Fx Xlo Xhi) as RD.
 unfold exp2_b. revert RD. generalize (exp2_reduce x). intros [[[n j] k] d] [ni [Fn [Bn [Ni [JK [J K]]]]]].
 destruct K as [K [Fd [Bd [Ad Dlo]]]].
 assert (Jn : (Z.to_nat j < 512)%nat) by lia.
 pose proof (e2_b_value_ok d (Z.to_nat j) Fd Ad Dlo Jn) as AV.
 revert AV. generalize (e2_b_value d (Z.to_nat j)). intros [y l] [Fy [Fl [Hy [Hl Err]]]] Hd.
 rewrite (e2_split (B x) ni j k (B d) JK ltac:(lia) Bd).
 apply (decide_const_ok y l c_eb k (exp (INR (Z.to_nat j) * ln 2 / 512) * exp (B d * ln 2))
   (IZR 209 * bpow radix2 (-78)) (-19) v Fy Fl c_eb_finite Hy ltac:(lia)); try assumption.
 - rewrite c_eb_val. apply bpow_ge_0.
 - rewrite c_eb_val. bpow_num_all. lra.
 - rewrite c_eb_val. change (-19 - 54)%Z with (-73)%Z. bpow_num_all. lra.
 - apply z_range; [exact Jn | exact (proj1 (exp2_residual_range (B d) Ad))].
Qed.

Definition e2_screen (x : f64) : bool :=
  let m := Z.land (bits_of_b64 x) 9223372036854775807 in
  andb (4359484439294640128 <=? m)%Z (m <? 4652148046329544704)%Z.

Theorem e2_screen_ok x : e2_screen x = true -> finite x /\ bpow radix2 (-55) <= Rabs (B x) /\ Rabs (B x) < 1016.
Proof.
  unfold e2_screen. intros H. apply andb_prop in H as [Lo H]. apply Z.leb_le in Lo. apply Z.ltb_lt in H.
  pose proof (bits_of_binary_float_range 52 11 eq_refl eq_refl x) as Rg.
  rewrite <- (binary_float_of_bits_of_binary_float 52 11 eq_refl eq_refl eq_refl x).
  change (bits_of_binary_float 52 11 x) with (bits_of_b64 x) in *.
  generalize (bits_of_b64 x) Rg H Lo. clear. intros b Rg H Lo.
  change (2 ^ (52 + 11 + 1))%Z with (2 ^ 64)%Z in Rg.
  change 9223372036854775807%Z with (Z.ones 63) in H, Lo. rewrite Z.land_ones in H, Lo by lia.
  change (2 ^ 63)%Z with (2 ^ 52 * 2 ^ 11)%Z in H, Lo. rewrite Z.rem_mul_r in H, Lo by lia.
  assert (Mr : (0 <= b mod 2 ^ 52 < 2 ^ 52)%Z) by (apply Z.mod_pos_bound; lia).
  assert (Er : (0 <= (b / 2 ^ 52) mod 2 ^ 11 < 2 ^ 11)%Z) by (apply Z.mod_pos_bound; lia).
  unfold binary_float_of_bits. rewrite is_finite_FF2B, B2R_FF2B.
  unfold binary_float_of_bits_aux, split_bits. cbv zeta.
  change (Zpower 2 52) with (2 ^ 52)%Z. change (Zpower 2 11) with (2 ^ 11)%Z.
  generalize (Zle_bool (2 ^ 52 * 2 ^ 11) b). intros s.
  remember (b mod 2 ^ 52)%Z as M in *. remember ((b / 2 ^ 52) mod 2 ^ 11)%Z as E in *.
  clear HeqM HeqE Rg.
  assert (E1 : (E <= 1032)%Z) by lia.
  assert (E2 : E = 1032%Z -> (M < 4433230883192832)%Z) by lia.
  assert (El : (968 <= E)%Z) by lia.
  assert (N0 : Zeq_bool E 0 = false) by (apply Zeq_bool_false; lia).
  rewrite N0.
  assert (N2047 : Zeq_bool E (2 ^ 11 - 1) = false) by (apply Zeq_bool_false; lia).
    rewrite N2047.
    destruct (M + 2 ^ 52)%Z as [ | px | px] eqn:HP; [lia | | lia].
    split; [reflexivity | ]. simpl FF2R. unfold F2R. cbn [Fnum Fexp].
    rewrite Rabs_mult, Rabs_Zabs, (Rabs_pos_eq (bpow radix2 _)) by apply bpow_ge_0.
    replace (Z.abs (cond_Zopp s (Zpos px))) with (Zpos px) by (destruct s; reflexivity).
    replace (E + -1074 - 1)%Z with (E - 1075)%Z by ring.
    split.
    { apply Rle_trans with (bpow radix2 52 * bpow radix2 (E - 1075)).
      - rewrite <- bpow_plus. apply bpow_le. lia.
      - apply Rmult_le_compat_r; [apply bpow_ge_0 | change (bpow radix2 52) with (IZR (2 ^ 52)); apply IZR_le; lia]. }
    destruct (Z.eq_dec E 1032) as [E32 | E31].
    + subst E. specialize (E2 eq_refl).
      assert (P : IZR (Zpos px) < IZR 8936830510563328) by (apply IZR_lt; lia).
      change (1032 - 1075)%Z with (-43)%Z. change (bpow radix2 (-43)) with (/ 8796093022208).
      lra.
    + assert (P : IZR (Zpos px) < bpow radix2 53) by (change (bpow radix2 53) with (IZR (2 ^ 53)); apply IZR_lt; lia).
      apply Rlt_le_trans with (bpow radix2 53 * bpow radix2 (E - 1075)).
      * apply Rmult_lt_compat_r; [apply bpow_gt_0 | exact P].
      * rewrite <- bpow_plus. apply Rle_trans with (bpow radix2 9); [apply bpow_le; lia | ].
        change (bpow radix2 9) with 512. lra.
Qed.

Definition exp2_stages x :=
 if e2_screen x then match exp2_a x with Some v => Some v | None => exp2_b x end else None.

Theorem exp2_stages_ok x v : exp2_stages x = Some v -> finite v /\ B v = rndF (exp (B x * ln 2)).
Proof.
 unfold exp2_stages. destruct (e2_screen x) eqn:Sc; [ | discriminate].
 destruct (e2_screen_ok x Sc) as [Fx [Xlo Xhi]].
 destruct (exp2_a x) as [w | ] eqn:A.
 - intros H. injection H as <-. exact (exp2_a_ok x w Fx Xlo Xhi A).
 - apply exp2_b_ok; assumption.
Qed.
