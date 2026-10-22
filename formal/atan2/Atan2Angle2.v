(** [atan2_angle] for finite positive magnitudes: the tiny path and the main path together, against
    the real angle [angle_real]. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 RoundingCore RoundingTest.
From Interval Require Import Tactic.
Require Import Ln1pLemmas AsinSeries AsinTables AsinKernel AsinSqrtStep AsinRecip AsinCorrect ErfcxAccurateInputs
  Atan2Tables Atan2Kernel Atan2Within Atan2Approx Atan2Forms Atan2FastPath Atan2NewtonReal Atan2Accurate Atan2Angle
  Atan2Consts Atan2Odd Atan2Decode Atan2TinyMid Atan2Tiny Atan2Spec.
Open Scope R_scope.

Definition angle_form (swap neg : bool) : form :=
  match swap, neg with
  | false, false => Phi | true, false => HalfPiMinus
  | false, true => PiMinus | true, true => HalfPiPlus
  end.

Definition tiny_body (n d q : f64) (f : form) : f64 :=
  match f with
  | Phi => atan2_tiny_phi n d q
  | HalfPiMinus | HalfPiPlus => atan2_half_pi_f64
  | PiMinus => atan2_pi
  end.

Definition angle_body (n d : f64) (f : form) : f64 :=
  let quotient := fdiv n d in
  if atan2_cmp_is quotient atan2_tiny Lt then tiny_body n d quotient f else atan2_main n d f.

Lemma angle_unfold a b neg : atan2_angle a b neg =
  angle_body (if atan2_cmp_is a b Gt then b else a) (if atan2_cmp_is a b Gt then a else b) (angle_form (atan2_cmp_is a b Gt) neg).
Proof. unfold atan2_angle, angle_body, tiny_body, angle_form, atan2_main. destruct (atan2_cmp_is a b Gt), neg; reflexivity. Qed.

(** The two ways a result is correct without any hypothesis: the tiny path, or a decision that succeeded. *)
Definition body_certified (n d : f64) (f : form) : Prop :=
  atan2_cmp_is (fdiv n d) atan2_tiny Lt = true \/ atan2_decide (fst (atan2_fast n d f)) <> None.

Theorem angle_core n d f : finite n -> finite d -> 0 < B n -> B n <= B d ->
  finite (angle_body n d f) /\ 0 <= B (angle_body n d f) /\
  Rabs (B (angle_body n d f) - form_value f (atan (B n / B d))) <= (/ 2 + bpow radix2 (-137)) * ulpF (B (angle_body n d f)) /\
  (body_certified n d f -> B (angle_body n d f) = rndF (form_value f (atan (B n / B d)))) /\
  (Stable190 (form_value f (atan (B n / B d))) -> B (angle_body n d f) = rndF (form_value f (atan (B n / B d)))).
Proof.
  intros Fn Fd Pn Hnd.
  assert (Pd : 0 < B d) by lra.
  assert (Ht1 : B n / B d <= 1).
  { apply Rmult_le_reg_r with (B d); [exact Pd | ]. unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra. lra. }
  assert (Pt : 0 < B n / B d) by (apply Rdiv_lt_0_compat; lra).
  destruct (fdiv_ok 1 0 n d Fn ltac:(lra) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(unfold bnd; rewrite Rabs_pos_eq by lra; simpl; lra)) as [Fq Bq].
  destruct tiny_val as [Ft Vt].
  unfold angle_body. set (q := fdiv n d) in *.
  destruct (atan2_cmp_is q atan2_tiny Lt) eqn:Hc.
  - (* tiny *)
    apply (proj1 (cmp_val q atan2_tiny Lt Fq Ft)) in Hc. apply Rcompare_Lt_inv in Hc. rewrite Vt in Hc.
    set (t := B n / B d) in *.
    assert (Ht9 : t <= bpow radix2 (-900)).
    { destruct (Rle_dec t (bpow radix2 (-900))) as [L | G]; [exact L | exfalso].
      pose proof (rndF_mono_bpow (-900) t ltac:(lia) ltac:(lra)) as H. rewrite <- Bq in H. lra. }
    pose proof (atan_pos t Pt) as Y0. pose proof (atan_le_id t ltac:(lra)) as Y1.
    assert (Hphi : atan t <= / 100000000000000000000).
    { apply Rle_trans with t; [exact Y1 | apply Rle_trans with (bpow radix2 (-900)); [exact Ht9 | ]].
      apply Rle_trans with (bpow radix2 (-70)); [apply bpow_le; lia | bpow_num; interval with (i_prec 100)]. }
    assert (Hcor : finite (tiny_body n d q f) /\ B (tiny_body n d q f) = rndF (form_value f (atan t))).
    { destruct f; cbn [form_value tiny_body].
      - exact (tiny_phi_ok n d Fn Fd Pn Hnd Hc).
      - destruct half_pi_rn_a as [F _]. split; [exact F | ]. symmetry. apply half_pi_minus_rn. split; lra.
      - destruct pi_rn as [F _]. destruct atan2_pi_val as [F2 _]. split; [exact F | ]. symmetry. apply pi_minus_rn. split; lra.
      - destruct half_pi_rn_a as [F _]. split; [exact F | ]. symmetry. apply half_pi_plus_rn. split; lra. }
    destruct Hcor as [Fm Bm]. set (M := tiny_body n d q f) in *.
    assert (Hnn : 0 <= B M).
    { rewrite Bm. apply round_ge_generic; [exact _ | exact _ | apply generic_format_0 | ].
      pose proof pi_gt_3 as P3. destruct f; cbn [form_value]; lra. }
    refine (conj Fm (conj Hnn (conj _ (conj (fun _ => Bm) (fun _ => Bm))))).
    pose proof (half_ulp_rn (form_value f (atan t))) as Hh. rewrite <- Bm in Hh.
    pose proof (ulp_ge_0 radix2 (FLT_exp (-1074) 53) (B M)) as Hu0. pose proof (bpow_gt_0 radix2 (-137)).
    assert (Hpp : 0 <= bpow radix2 (-137) * ulpF (B M)) by (apply Rmult_le_pos; [apply bpow_ge_0 | exact Hu0]).
    apply Rle_trans with (1 := Hh). lra.
  - (* the main path *)
    assert (Hge : bpow radix2 (-900) <= B q).
    { destruct (Rlt_le_dec (B q) (bpow radix2 (-900))) as [L | G]; [exfalso | exact G].
      assert (Hcc : atan2_cmp_is q atan2_tiny Lt = true) by (apply (proj2 (cmp_val q atan2_tiny Lt Fq Ft)); rewrite Vt; apply Rcompare_Lt; exact L).
      rewrite Hc in Hcc. discriminate Hcc. }
    assert (Hq : bpow radix2 (-901) <= B n / B d).
    { destruct (Rlt_le_dec (B n / B d) (bpow radix2 (-901))) as [L | G]; [exfalso | exact G].
      pose proof (rndF_le_bpow (-901) (B n / B d) ltac:(lia) (Rlt_le _ _ L)) as H. rewrite <- Bq in H.
      assert (bpow radix2 (-901) < bpow radix2 (-900)) by (apply bpow_lt; lia). lra. }
    destruct (atan2_main_ok n d f Fn Fd Pn Hnd Hq) as [F [Nn [Ub [Dec St]]]].
    refine (conj F (conj Nn (conj Ub (conj _ St)))).
    intros [Tiny | Dd]; [change (fdiv n d) with q in Tiny; rewrite Hc in Tiny; discriminate Tiny | exact (Dec Dd)].
Qed.

Definition angle_certified (a b : f64) (neg : bool) : Prop :=
  body_certified (if atan2_cmp_is a b Gt then b else a) (if atan2_cmp_is a b Gt then a else b) (angle_form (atan2_cmp_is a b Gt) neg).

Theorem angle_ok a b neg : finite a -> finite b -> 0 < B a -> 0 < B b ->
  finite (atan2_angle a b neg) /\ 0 <= B (atan2_angle a b neg) /\
  Rabs (B (atan2_angle a b neg) - angle_real (B a) (B b) neg) <= (/ 2 + bpow radix2 (-137)) * ulpF (B (atan2_angle a b neg)) /\
  (angle_certified a b neg -> B (atan2_angle a b neg) = rndF (angle_real (B a) (B b) neg)) /\
  (Stable190 (angle_real (B a) (B b) neg) -> B (atan2_angle a b neg) = rndF (angle_real (B a) (B b) neg)).
Proof.
  intros Fa Fb Pa Pb. rewrite angle_unfold. unfold angle_certified.
  destruct (atan2_cmp_is a b Gt) eqn:Hs.
  - assert (Hgt : B b < B a).
    { pose proof (proj1 (cmp_val a b Gt Fa Fb) Hs) as H. apply Rcompare_Gt_inv in H. exact H. }
    destruct (angle_core b a (angle_form true neg) Fb Fa Pb ltac:(lra)) as [F [Nn [Ub [Cert St]]]].
    assert (Z : form_value (angle_form true neg) (atan (B b / B a)) = angle_real (B a) (B b) neg).
    { unfold angle_real. destruct (Rle_dec (B a) (B b)) as [L | G]; [lra | ]. destruct neg; reflexivity. }
    rewrite Z in Ub, Cert, St. exact (conj F (conj Nn (conj Ub (conj Cert St)))).
  - assert (Hle : B a <= B b).
    { destruct (Rle_dec (B a) (B b)) as [L | G]; [exact L | exfalso].
      assert (Hcc : atan2_cmp_is a b Gt = true) by (apply (proj2 (cmp_val a b Gt Fa Fb)); apply Rcompare_Gt; lra).
      rewrite Hs in Hcc. discriminate Hcc. }
    destruct (angle_core a b (angle_form false neg) Fa Fb Pa Hle) as [F [Nn [Ub [Cert St]]]].
    assert (Z : form_value (angle_form false neg) (atan (B a / B b)) = angle_real (B a) (B b) neg).
    { unfold angle_real. destruct (Rle_dec (B a) (B b)) as [L | G]; [ | lra]. destruct neg; reflexivity. }
    rewrite Z in Ub, Cert, St. exact (conj F (conj Nn (conj Ub (conj Cert St)))).
Qed.
