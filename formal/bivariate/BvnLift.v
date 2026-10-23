(** The kernel's binary64 operations against the real-valued rounding model
    the error proofs are written in.

    [exb a r E] says the binary64 value [a] is finite, equals the real [r], and
    [|r| <= 2^E]. Each lemma here takes operands so related and, where the
    result's bound stays below [2^1000], returns the operation's result related to
    the one rounding of the exact result: an operation never overflows on the
    operands the proofs consider, and then [B (fadd a b) = rndF (B a + B b)]
    (formal/binary64/IEEE64.v). The bounds are upper bounds only, clamped below
    at [2^-1000] so every exponent names a binary64 number; they are crude and
    exist to exclude overflow, never to carry accuracy. *)

From Coq Require Import Reals ZArith Lia Lra.
From Flocq Require Import Core Relative IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add Binary64Mul IEEE64 IEEE64Add IEEE64Mul IEEE64Eft IEEE64Sqrt IEEE64Div Encodings.
Require Import BvnKernel.
Open Scope R_scope.

Definition exb (a : f64) (r : R) (E : Z) : Prop :=
  finite a /\ B a = r /\ Rabs r <= bpow radix2 E.

Definition cl (E : Z) : Z := Z.max E (-1000).

Lemma exb_fin a r E : exb a r E -> finite a.
Proof. intros H. exact (proj1 H). Qed.

Lemma exb_val a r E : exb a r E -> B a = r.
Proof. intros H. exact (proj1 (proj2 H)). Qed.

Lemma exb_bnd a r E : exb a r E -> Rabs r <= bpow radix2 E.
Proof. intros H. exact (proj2 (proj2 H)). Qed.

Lemma exb_weak a r E E' : exb a r E -> (E <= E')%Z -> exb a r E'.
Proof.
  intros [F [V H]] L. repeat split; try assumption.
  eapply Rle_trans; [exact H | apply bpow_le; exact L].
Qed.

Lemma exb_tight a r E E' : exb a r E -> Rabs r <= bpow radix2 E' -> exb a r E'.
Proof. intros [F [V H]] H'. repeat split; assumption. Qed.

Lemma exb_cong a r r' E : exb a r E -> r = r' -> exb a r' E.
Proof. intros H ->. exact H. Qed.

Lemma bnd_of_exb a r E : exb a r E -> bnd 1 E (B a).
Proof.
  intros [F [V H]]. unfold bnd. rewrite V. change (IZR 1) with 1. rewrite Rmult_1_l. exact H.
Qed.

Lemma bnd_exb' a r E : exb a r E -> bnd 1 E r.
Proof.
  intros [F [V H]]. unfold bnd. change (IZR 1) with 1. rewrite Rmult_1_l. exact H.
Qed.

Lemma bnd_exb a r E : finite a -> B a = r -> bnd 1 E r -> exb a r E.
Proof.
  intros F V H. repeat split; try assumption.
  unfold bnd in H. change (IZR 1) with 1 in H. rewrite Rmult_1_l in H. exact H.
Qed.

Lemma pow_big e : (e <= 1000)%Z -> (1 < 2 ^ (1024 - e))%Z.
Proof. intros H. apply Z.pow_gt_1; lia. Qed.

Lemma bpow_cl E : bpow radix2 E <= bpow radix2 (cl E).
Proof. apply bpow_le. unfold cl. lia. Qed.

Lemma bpow_le_abs v E E' : Rabs v <= bpow radix2 E -> (E <= E')%Z -> Rabs v <= bpow radix2 E'.
Proof. intros H L. eapply Rle_trans; [exact H | apply bpow_le; exact L]. Qed.

(** The cores: a finite result whose exact value is bounded by [2^E]. *)
Lemma add_core a b ra rb E : finite a -> finite b -> B a = ra -> B b = rb ->
  Rabs (ra + rb) <= bpow radix2 E -> (-1000 <= E <= 1000)%Z -> exb (fadd a b) (rndF (ra + rb)) E.
Proof.
  intros Fa Fb Va Vb H HE. subst ra rb.
  assert (Hb : bnd 1 E (B a + B b)) by (unfold bnd; change (IZR 1) with 1; rewrite Rmult_1_l; exact H).
  destruct (fadd_bnd 1 E a b Fa Fb ltac:(lia) ltac:(lia) (pow_big E ltac:(lia)) ltac:(lia) Hb) as [F [V Bd]].
  apply bnd_exb; [exact F | exact V | ]. rewrite <- V. exact Bd.
Qed.

Lemma sub_core a b ra rb E : finite a -> finite b -> B a = ra -> B b = rb ->
  Rabs (ra - rb) <= bpow radix2 E -> (-1000 <= E <= 1000)%Z -> exb (fsub a b) (rndF (ra - rb)) E.
Proof.
  intros Fa Fb Va Vb H HE. subst ra rb.
  assert (Hb : bnd 1 E (B a - B b)) by (unfold bnd; change (IZR 1) with 1; rewrite Rmult_1_l; exact H).
  destruct (fsub_bnd 1 E a b Fa Fb ltac:(lia) ltac:(lia) (pow_big E ltac:(lia)) ltac:(lia) Hb) as [F [V Bd]].
  apply bnd_exb; [exact F | exact V | ]. rewrite <- V. exact Bd.
Qed.

Lemma mul_core a b ra rb E : finite a -> finite b -> B a = ra -> B b = rb ->
  Rabs (ra * rb) <= bpow radix2 E -> (-1000 <= E <= 1000)%Z -> exb (fmul a b) (rndF (ra * rb)) E.
Proof.
  intros Fa Fb Va Vb H HE. subst ra rb.
  assert (Hb : bnd 1 E (B a * B b)) by (unfold bnd; change (IZR 1) with 1; rewrite Rmult_1_l; exact H).
  destruct (fmul_bnd 1 E a b Fa Fb ltac:(lia) ltac:(lia) (pow_big E ltac:(lia)) ltac:(lia) Hb) as [F [V Bd]].
  apply bnd_exb; [exact F | exact V | ]. rewrite <- V. exact Bd.
Qed.

Lemma div_core a b ra rb E : finite a -> B b <> 0 -> B a = ra -> B b = rb ->
  Rabs (ra / rb) <= bpow radix2 E -> (-1000 <= E <= 1000)%Z -> finite b -> exb (fdiv a b) (rndF (ra / rb)) E.
Proof.
  intros Fa Hb0 Va Vb H HE Fb. subst ra rb.
  assert (Hb : bnd 1 E (B a / B b)) by (unfold bnd; change (IZR 1) with 1; rewrite Rmult_1_l; exact H).
  destruct (fdiv_bnd 1 E a b Fa Hb0 ltac:(lia) ltac:(lia) (pow_big E ltac:(lia)) ltac:(lia) Hb) as [F [V Bd]].
  apply bnd_exb; [exact F | exact V | ]. rewrite <- V. exact Bd.
Qed.

(** The operations with their bounds computed from the operands'. *)
Lemma exb_add a b ra rb E1 E2 : exb a ra E1 -> exb b rb E2 -> (cl (Z.max E1 E2 + 1) <= 1000)%Z ->
  exb (fadd a b) (rndF (ra + rb)) (cl (Z.max E1 E2 + 1)).
Proof.
  intros Ha Hb Hc. apply add_core; try (eapply exb_fin; eassumption);
    try (exact (exb_val _ _ _ Ha)); try (exact (exb_val _ _ _ Hb)).
  - eapply Rle_trans; [apply Rabs_triang |].
    pose proof (exb_bnd _ _ _ Ha) as A. pose proof (exb_bnd _ _ _ Hb) as B1.
    pose proof (bpow_le radix2 E1 (Z.max E1 E2) ltac:(lia)) as M1.
    pose proof (bpow_le radix2 E2 (Z.max E1 E2) ltac:(lia)) as M2.
    pose proof (bpow_cl (Z.max E1 E2 + 1)) as C. rewrite bpow_plus in C. change (bpow radix2 1) with 2 in C. lra.
  - unfold cl in Hc; unfold cl; lia.
Qed.

Lemma exb_sub a b ra rb E1 E2 : exb a ra E1 -> exb b rb E2 -> (cl (Z.max E1 E2 + 1) <= 1000)%Z ->
  exb (fsub a b) (rndF (ra - rb)) (cl (Z.max E1 E2 + 1)).
Proof.
  intros Ha Hb Hc. apply sub_core; try (eapply exb_fin; eassumption);
    try (exact (exb_val _ _ _ Ha)); try (exact (exb_val _ _ _ Hb)).
  - unfold Rminus. eapply Rle_trans; [apply Rabs_triang |]. rewrite Rabs_Ropp.
    pose proof (exb_bnd _ _ _ Ha) as A. pose proof (exb_bnd _ _ _ Hb) as B1.
    pose proof (bpow_le radix2 E1 (Z.max E1 E2) ltac:(lia)) as M1.
    pose proof (bpow_le radix2 E2 (Z.max E1 E2) ltac:(lia)) as M2.
    pose proof (bpow_cl (Z.max E1 E2 + 1)) as C. rewrite bpow_plus in C. change (bpow radix2 1) with 2 in C. lra.
  - unfold cl in Hc; unfold cl; lia.
Qed.

Lemma exb_mul a b ra rb E1 E2 : exb a ra E1 -> exb b rb E2 -> (cl (E1 + E2) <= 1000)%Z ->
  exb (fmul a b) (rndF (ra * rb)) (cl (E1 + E2)).
Proof.
  intros Ha Hb Hc. apply mul_core; try (eapply exb_fin; eassumption);
    try (exact (exb_val _ _ _ Ha)); try (exact (exb_val _ _ _ Hb)).
  - rewrite Rabs_mult.
    pose proof (exb_bnd _ _ _ Ha) as A. pose proof (exb_bnd _ _ _ Hb) as B1.
    pose proof (bpow_cl (E1 + E2)) as C. rewrite bpow_plus in C.
    eapply Rle_trans; [| exact C]. apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | exact A | exact B1].
  - unfold cl in Hc; unfold cl; lia.
Qed.

(** A quotient needs a lower bound [2^-L] of the divisor's magnitude. *)
Definition divlow (r : R) (L : Z) : Prop := bpow radix2 (- L) <= Rabs r.

Lemma exb_div a b ra rb E1 E2 L : exb a ra E1 -> exb b rb E2 -> (E2 <= 1000)%Z -> divlow rb L ->
  (cl (E1 + L) <= 1000)%Z ->
  exb (fdiv a b) (rndF (ra / rb)) (cl (E1 + L)).
Proof.
  intros Ha Hb0 He2 Hl Hc. unfold divlow in Hl.
  pose proof (exb_weak _ _ _ 1000 Hb0 He2) as Hb.
  assert (Hb1 : rb <> 0) by (intros ->; rewrite Rabs_R0 in Hl; pose proof (bpow_gt_0 radix2 (- L)); lra).
  apply div_core; try (eapply exb_fin; eassumption); try (exact (exb_val _ _ _ Ha)); try (exact (exb_val _ _ _ Hb)).
  - rewrite (exb_val _ _ _ Hb). exact Hb1.
  - pose proof (bnd_div 1 E1 L ra rb ltac:(lia) (bnd_exb' _ _ _ Ha) Hl) as D.
    unfold bnd in D. change (IZR 1) with 1 in D. rewrite Rmult_1_l in D.
    eapply Rle_trans; [exact D | apply bpow_cl].
  - unfold cl in Hc; unfold cl; lia.
Qed.

(** A quotient by a divisor of magnitude at least 1. *)
Lemma exb_div_one a b ra rb E1 E2 : exb a ra E1 -> exb b rb E2 -> (E2 <= 1000)%Z -> 1 <= Rabs rb ->
  (cl (E1 + 0) <= 1000)%Z ->
  exb (fdiv a b) (rndF (ra / rb)) (cl (E1 + 0)).
Proof.
  intros Ha Hb He Hl Hc. eapply exb_div; [exact Ha | exact Hb | exact He | | exact Hc].
  unfold divlow. replace (- 0)%Z with 0%Z by reflexivity. exact Hl.
Qed.

(** Negation, absolute value and square root. *)
Lemma exb_neg a r E : exb a r E -> exb (fneg a) (- r) E.
Proof.
  intros [F [V H]]. unfold fneg, b64_opp. split; [|split].
  - rewrite is_finite_Bopp. exact F.
  - rewrite B2R_Bopp. rewrite V. reflexivity.
  - rewrite Rabs_Ropp. exact H.
Qed.

Lemma exb_abs a r E : exb a r E -> exb (fabs a) (Rabs r) E.
Proof.
  intros [F [V H]]. unfold fabs, b64_abs. split; [|split].
  - rewrite is_finite_Babs. exact F.
  - rewrite B2R_Babs. rewrite V. reflexivity.
  - rewrite Rabs_Rabsolu. exact H.
Qed.

Lemma fmtF_bpow E : (-1074 <= E)%Z -> fmtF (bpow radix2 E).
Proof.
  intros H. pose proof (bnd_fmt 1 E ltac:(split; [lia | apply Z.pow_gt_1; lia]) H) as F.
  rewrite <- (Rmult_1_l (bpow radix2 E)). exact F.
Qed.

Lemma rnd_bound v E : Rabs v <= bpow radix2 E -> (-1074 <= E)%Z -> Rabs (rndF v) <= bpow radix2 E.
Proof.
  intros H HE. apply abs_round_le_generic; [exact _ | exact _ | apply fmtF_bpow; exact HE | exact H].
Qed.

Lemma exb_sqrt a r E : exb a r E -> 0 <= r -> (0 <= E)%Z -> exb (fsqrt a) (rndF (sqrt r)) E.
Proof.
  intros [F [V H]] H0 HE. destruct (sqrt_ieee a) as [Vs Fs].
  repeat split.
  - apply Fs. split; [exact F | rewrite V; exact H0].
  - rewrite Vs, V. reflexivity.
  - apply rnd_bound; [ | lia].
    rewrite Rabs_pos_eq by (apply sqrt_pos).
    rewrite Rabs_pos_eq in H by exact H0.
    pose proof (bpow_ge_0 radix2 E) as P.
    assert (H1 : 1 <= bpow radix2 E) by (replace 1 with (bpow radix2 0) by reflexivity; apply bpow_le; exact HE).
    assert (Hr : r <= bpow radix2 E * bpow radix2 E) by nra.
    apply sqrt_le_1_alt in Hr. rewrite sqrt_square in Hr by lra. exact Hr.
Qed.

(** The comparisons of finite values. *)
Lemma flt_iff a b : finite a -> finite b -> (flt a b = true <-> B a < B b).
Proof.
  intros Fa Fb. unfold flt, fcmp. rewrite (Bcompare_correct 53 1024 a b Fa Fb).
  destruct (Rcompare (B a) (B b)) eqn:E.
  - apply Rcompare_Eq_inv in E. split; [discriminate | intros H; lra].
  - apply Rcompare_Lt_inv in E. split; [intros _; exact E | auto].
  - apply Rcompare_Gt_inv in E. split; [discriminate | intros H; lra].
Qed.

Lemma fle_iff a b : finite a -> finite b -> (fle a b = true <-> B a <= B b).
Proof.
  intros Fa Fb. unfold fle, fcmp. rewrite (Bcompare_correct 53 1024 a b Fa Fb).
  destruct (Rcompare (B a) (B b)) eqn:E.
  - apply Rcompare_Eq_inv in E. split; [intros _; lra | auto].
  - apply Rcompare_Lt_inv in E. split; [intros _; lra | auto].
  - apply Rcompare_Gt_inv in E. split; [discriminate | intros H; lra].
Qed.

Lemma fgt_iff a b : finite a -> finite b -> (fgt a b = true <-> B b < B a).
Proof. intros Fa Fb. unfold fgt. apply flt_iff; assumption. Qed.

Lemma fge_iff a b : finite a -> finite b -> (fge a b = true <-> B b <= B a).
Proof. intros Fa Fb. unfold fge. apply fle_iff; assumption. Qed.

Lemma feq_iff a b : finite a -> finite b -> (feq a b = true <-> B a = B b).
Proof.
  intros Fa Fb. unfold feq, fcmp. rewrite (Bcompare_correct 53 1024 a b Fa Fb).
  destruct (Rcompare (B a) (B b)) eqn:E.
  - apply Rcompare_Eq_inv in E. split; [intros _; exact E | auto].
  - apply Rcompare_Lt_inv in E. split; [discriminate | intros H; lra].
  - apply Rcompare_Gt_inv in E. split; [discriminate | intros H; lra].
Qed.

Lemma fisnan_finite a : finite a -> fisnan a = false.
Proof. destruct a; simpl; congruence. Qed.

(** The error-free transforms. *)
Lemma exb_two_sum a b ra rb E : exb a ra E -> exb b rb E -> (-1000 <= E <= 1000)%Z ->
  exb (fst (two_sum64 a b)) (fst (two_sum ra rb)) (E + 1)
  /\ exb (snd (two_sum64 a b)) (snd (two_sum ra rb)) (E + 4).
Proof.
  intros Ha Hb HE.
  destruct (two_sum64_ok 1 E a b (exb_fin _ _ _ Ha) (exb_fin _ _ _ Hb) (bnd_of_exb _ _ _ Ha) (bnd_of_exb _ _ _ Hb)
    ltac:(lia) ltac:(lia) ltac:(apply (Z.lt_le_trans _ (2 ^ 4)); [lia | apply Z.pow_le_mono_r; lia]) ltac:(lia))
    as [F1 [F2 [Pair [B1 B2]]]].
  rewrite (exb_val _ _ _ Ha), (exb_val _ _ _ Hb) in Pair.
  pose proof (f_equal fst Pair) as P1. pose proof (f_equal snd Pair) as P2. cbn [fst snd] in P1, P2.
  split.
  - apply bnd_exb; [exact F1 | exact P1 | ].
    unfold bnd in B1; unfold bnd. rewrite <- P1. rewrite bpow_plus. change (bpow radix2 1) with 2.
    change (IZR (2 * 1)) with 2 in B1. change (IZR 1) with 1. lra.
  - apply bnd_exb; [exact F2 | exact P2 | ].
    unfold bnd in B2; unfold bnd. rewrite <- P2. rewrite bpow_plus. change (bpow radix2 4) with 16.
    change (IZR (10 * 1)) with 10 in B2. change (IZR 1) with 1. pose proof (bpow_ge_0 radix2 E). lra.
Qed.

(** The constants. *)
Lemma val_of_bits n s m e : binary_float_of_bits_aux 52 11 n = F754_finite s m e ->
  B (aw n) = F2R (Float radix2 (cond_Zopp s (Zpos m)) e).
Proof. intros D. unfold aw, b64_of_bits, binary_float_of_bits. rewrite B2R_FF2B, D. reflexivity. Qed.

Lemma exb_of_bits n s m e r E : binary_float_of_bits_aux 52 11 n = F754_finite s m e ->
  F2R (Float radix2 (cond_Zopp s (Zpos m)) e) = r -> Rabs r <= bpow radix2 E -> exb (aw n) r E.
Proof.
  intros D V H. repeat split.
  - exact (bits_finite n s m e D).
  - rewrite (val_of_bits n s m e D). exact V.
  - exact H.
Qed.

Ltac kconst :=
  match goal with
  | |- exb (aw ?n) ?r ?E =>
      let d := eval vm_compute in (binary_float_of_bits_aux 52 11 n) in
      match d with
      | F754_finite ?s ?m ?e =>
          refine (exb_of_bits n s m e r E _ _ _);
          [ vm_compute; reflexivity | unfold F2R; simpl; lra | apply Rabs_le; simpl; lra ]
      end
  end.

Lemma exb_k0 : exb k0 0 (-1000).
Proof.
  unfold k0, aw. split; [|split].
  - exact (bits_finite_zero 0 false eq_refl).
  - rewrite (bits_zero 0 false eq_refl). reflexivity.
  - rewrite Rabs_R0. apply bpow_ge_0.
Qed.

Lemma exb_k1 : exb k1 1 0. Proof. unfold k1. kconst. Qed.
Lemma exb_kneg1 : exb kneg1 (-1) 0.
Proof.
  unfold kneg1. refine (exb_of_bits _ true _ _ _ _ _ _ _).
  - vm_compute. reflexivity.
  - unfold F2R. simpl. lra.
  - apply Rabs_le. simpl. lra.
Qed.
Lemma exb_k2 : exb k2 2 1. Proof. unfold k2. kconst. Qed.
Lemma exb_k3 : exb k3 3 2. Proof. unfold k3. kconst. Qed.
Lemma exb_k4 : exb k4 4 2. Proof. unfold k4. kconst. Qed.
Lemma exb_k5 : exb k5 5 3. Proof. unfold k5. kconst. Qed.
Lemma exb_k8 : exb k8 8 3. Proof. unfold k8. kconst. Qed.
Lemma exb_k12 : exb k12 12 4. Proof. unfold k12. kconst. Qed.
Lemma exb_k16 : exb k16 16 4. Proof. unfold k16. kconst. Qed.
Lemma exb_k20 : exb k20 20 5. Proof. unfold k20. kconst. Qed.
Lemma exb_k100 : exb k100 100 7. Proof. unfold k100. kconst. Qed.
Lemma exb_kquarter : exb kquarter (/ 4) 0. Proof. unfold kquarter. kconst. Qed.
Lemma exb_ktau : exb ktau (884279719003555 / 140737488355328) 3. Proof. unfold ktau. kconst. Qed.
Lemma exb_ksqrt_tau : exb ksqrt_tau (2822212540896131 / 1125899906842624) 2. Proof. unfold ksqrt_tau. kconst. Qed.
Lemma exb_kcentre_square : exb kcentre_square (9 / 16) 0. Proof. unfold kcentre_square. kconst. Qed.
Lemma exb_ksaturated : exb ksaturated 39 6. Proof. unfold ksaturated. kconst. Qed.
Lemma exb_kpanel_floor : exb kpanel_floor (3458764513820541 / 1152921504606846976) 0. Proof. unfold kpanel_floor. kconst. Qed.
Lemma exb_kpanel_wide : exb kpanel_wide (3422735716801577 / 36028797018963968) 0. Proof. unfold kpanel_wide. kconst. Qed.

Lemma exb_k0' : exb k0 0 0. Proof. eapply exb_weak; [exact exb_k0 | lia]. Qed.

Create HintDb exb.
#[export] Hint Resolve exb_k0 exb_k1 exb_kneg1 exb_k2 exb_k3 exb_k4 exb_k5 exb_k8 exb_k12 exb_k16 exb_k20 exb_k100
  exb_kquarter exb_ktau exb_ksqrt_tau exb_kcentre_square : exb.

(** A product by [+-1] is exact. *)
Lemma exb_mul_sign a b sgn r E : exb a sgn 0 -> exb b r E -> (sgn = 1 \/ sgn = -1) -> (-1000 <= E <= 1000)%Z ->
  exb (fmul a b) (sgn * r) E.
Proof.
  intros Ha Hb Hs HE.
  assert (Hr : rndF (sgn * r) = sgn * r).
  { apply round_generic; [exact _ |].
    destruct Hs as [-> | ->]; [rewrite Rmult_1_l | replace (-1 * r) with (- r) by ring].
    - rewrite <- (exb_val _ _ _ Hb). apply B_fmt.
    - apply generic_format_opp. rewrite <- (exb_val _ _ _ Hb). apply B_fmt. }
  rewrite <- Hr. apply mul_core; try (eapply exb_fin; eassumption); try (exact (exb_val _ _ _ Ha)); try (exact (exb_val _ _ _ Hb)).
  - assert (Habs : Rabs sgn = 1) by (destruct Hs as [-> | ->]; unfold Rabs; destruct Rcase_abs; lra).
    rewrite Rabs_mult, Habs, Rmult_1_l. exact (exb_bnd _ _ _ Hb).
  - exact HE.
Qed.

Lemma exb_two_prod a b ra rb Ea Eb : exb a ra Ea -> exb b rb Eb ->
  (-537 <= Ea <= 994)%Z -> (-537 <= Eb <= 994)%Z -> (Ea + Eb <= 1020)%Z ->
  exb (fst (two_prod64 a b)) (fst (two_prod ra rb)) (Ea + Eb)
  /\ exb (snd (two_prod64 a b)) (snd (two_prod ra rb)) (Ea + Eb + 4).
Proof.
  intros Ha Hb HEa HEb HE.
  pose proof (two_prod64_ok Ea Eb a b (exb_fin _ _ _ Ha) (exb_fin _ _ _ Hb) (bnd_of_exb _ _ _ Ha) (bnd_of_exb _ _ _ Hb) HEa HEb HE) as H.
  revert H. generalize (two_prod64 a b) as p. intros p [F1 [F2 [Pair [B1 B2]]]].
  rewrite (exb_val _ _ _ Ha), (exb_val _ _ _ Hb) in Pair.
  pose proof (f_equal fst Pair) as P1. pose proof (f_equal snd Pair) as P2. cbn [fst snd] in P1, P2.
  split.
  - apply bnd_exb; [exact F1 | exact P1 | ]. rewrite <- P1. exact B1.
  - apply bnd_exb; [exact F2 | exact P2 | ].
    unfold bnd in B2; unfold bnd. rewrite <- P2. rewrite bpow_plus. change (bpow radix2 4) with 16.
    change (IZR 1) with 1. change (IZR 10) with 10 in B2. pose proof (bpow_ge_0 radix2 (Ea + Eb)). lra.
Qed.

(** The probability clamp. *)
Lemma exb_clamp a r E : exb a r E -> exb (clamp_to_probability a) (Rmin 1 (Rmax 0 r)) 0.
Proof.
  intros Ha. pose proof (exb_fin _ _ _ Ha) as Fa. pose proof (exb_val _ _ _ Ha) as Va.
  assert (F0 : finite k0) by exact (proj1 exb_k0). assert (F1 : finite k1) by exact (proj1 exb_k1).
  assert (V0 : B k0 = 0) by exact (proj1 (proj2 exb_k0)). assert (V1 : B k1 = 1) by exact (proj1 (proj2 exb_k1)).
  unfold clamp_to_probability. rewrite (fisnan_finite _ Fa).
  destruct (flt a k0) eqn:E0.
  - apply (flt_iff a k0 Fa F0) in E0. rewrite V0, Va in E0.
    replace (Rmin 1 (Rmax 0 r)) with 0.
    + exact exb_k0'.
    + unfold Rmax. destruct (Rle_dec 0 r); [lra |]. unfold Rmin. destruct (Rle_dec 1 0); lra.
  - assert (E0' : ~ r < 0).
    { intro Hc. assert (Ht : flt a k0 = true) by (apply (flt_iff a k0 Fa F0); rewrite V0, Va; exact Hc).
      congruence. }
    destruct (fgt a k1) eqn:E1.
    + apply (fgt_iff a k1 Fa F1) in E1. rewrite V1, Va in E1.
      replace (Rmin 1 (Rmax 0 r)) with 1.
      * exact exb_k1.
      * unfold Rmax. destruct (Rle_dec 0 r); [| lra]. unfold Rmin. destruct (Rle_dec 1 r); lra.
    + assert (E1' : ~ 1 < r).
      { intro Hc. assert (Ht : fgt a k1 = true) by (apply (fgt_iff a k1 Fa F1); rewrite V1, Va; exact Hc).
        congruence. }
      replace (Rmin 1 (Rmax 0 r)) with r.
      * repeat split; [exact Fa | exact Va | ].
        apply Rabs_le. simpl. lra.
      * unfold Rmax. destruct (Rle_dec 0 r); [| lra]. unfold Rmin. destruct (Rle_dec 1 r); lra.
Qed.

(** The library functions, as the proofs state their contracts: the kernel's
    [exp] (of an argument at most [a]) returns the binary64 whose value the proofs
    call [expI], [sin] (of an argument of at most 2 in magnitude) [sinI], [norm_cdf]
    [ncI] and [asin] [asinI], each finite and bounded by [2^E] where the contract
    bounds it. *)
Definition lib_exp_rel (L : lib) (expI : R -> R) (a : R) (Ee : Z) : Prop :=
  forall v, finite v -> B v <= a ->
    finite (lib_exp L v) /\ B (lib_exp L v) = expI (B v) /\ Rabs (expI (B v)) <= bpow radix2 Ee.

Definition lib_sin_rel (L : lib) (sinI : R -> R) : Prop :=
  forall v, finite v -> Rabs (B v) <= 2 ->
    finite (lib_sin L v) /\ B (lib_sin L v) = sinI (B v) /\ Rabs (sinI (B v)) <= 2.

Definition lib_ncdf_rel (L : lib) (ncI : R -> R) : Prop :=
  forall v, finite v ->
    finite (lib_norm_cdf L v) /\ B (lib_norm_cdf L v) = ncI (B v) /\ 0 <= ncI (B v) <= 1.

Lemma exb_lib_exp L expI a Ee v r E : lib_exp_rel L expI a Ee -> exb v r E -> r <= a ->
  exb (lib_exp L v) (expI r) Ee.
Proof.
  intros H [F [V _]] Hr. subst r. destruct (H v F Hr) as [F' [V' B']].
  repeat split; assumption.
Qed.

Lemma exb_lib_sin L sinI v r E : lib_sin_rel L sinI -> exb v r E -> Rabs r <= 2 -> exb (lib_sin L v) (sinI r) 1.
Proof.
  intros H [F [V _]] Hr. subst r. destruct (H v F Hr) as [F' [V' B']].
  repeat split; try assumption.
Qed.

Lemma exb_lib_ncdf L ncI v r E : lib_ncdf_rel L ncI -> exb v r E -> exb (lib_norm_cdf L v) (ncI r) 0.
Proof.
  intros H [F [V _]]. subst r. destruct (H v F) as [F' [V' [B1 B2]]].
  repeat split; try assumption. rewrite Rabs_pos_eq by exact B1. exact B2.
Qed.

(** A rounded value at least [2^-L] has magnitude at least [2^-L]. *)
Lemma divlow_rnd X L : bpow radix2 (- L) <= X -> (L <= 1000)%Z -> (0 <= L)%Z -> divlow (rndF X) L.
Proof.
  intros H HL HL0. unfold divlow.
  assert (G : fmtF (bpow radix2 (- L))) by (apply fmtF_bpow; lia).
  assert (Hr : bpow radix2 (- L) <= rndF X).
  { rewrite <- (round_generic radix2 (FLT_exp (-1074) 53) (Znearest ne) _ G) at 1.
    apply round_le; [exact _ | exact _ | exact H]. }
  rewrite Rabs_pos_eq; [exact Hr | ].
  eapply Rle_trans; [apply bpow_ge_0 | exact Hr].
Qed.

Lemma rnd_nonneg0 x : 0 <= x -> 0 <= rndF x.
Proof.
  intros H. rewrite <- (round_0 radix2 (FLT_exp (-1074) 53) (Znearest ne)).
  apply round_le; [exact _ | exact _ | exact H].
Qed.

Lemma exb_div_one2 a b ra rb E1 E2 : 1 <= Rabs rb -> exb a ra E1 -> exb b rb E2 -> (E2 <= 1000)%Z ->
  (cl (E1 + 0) <= 1000)%Z -> exb (fdiv a b) (rndF (ra / rb)) (cl (E1 + 0)).
Proof. intros Hl Ha Hb He Hc. exact (exb_div_one a b ra rb E1 E2 Ha Hb He Hl Hc). Qed.

Lemma exb_div2 a b ra rb E1 E2 L : divlow rb L -> exb a ra E1 -> exb b rb E2 -> (E2 <= 1000)%Z ->
  (cl (E1 + L) <= 1000)%Z -> exb (fdiv a b) (rndF (ra / rb)) (cl (E1 + L)).
Proof. intros Hl Ha Hb He Hc. exact (exb_div a b ra rb E1 E2 L Ha Hb He Hl Hc). Qed.

(** The tactic that builds the relation from the kernel's operations. *)
Ltac cl_side := unfold cl; lia.
Ltac one_side := rewrite Rabs_pos_eq by lra; lra.
Ltac lift :=
  first [ eassumption | lift_struct ]
with lift_struct :=
  lazymatch goal with
  | |- exb (fneg _) _ _ => eapply exb_neg; lift
  | |- exb (fabs _) _ _ => eapply exb_abs; lift
  | |- exb (fadd _ _) _ _ => eapply exb_add; [ lift | lift | cl_side ]
  | |- exb (fsub _ _) _ _ => eapply exb_sub; [ lift | lift | cl_side ]
  | |- exb (fmul _ _) _ _ => eapply exb_mul; [ lift | lift | cl_side ]
  | |- exb (fdiv _ _) _ _ =>
      first
      [ eapply exb_div_one2; [ one_side | lift | lift | cl_side | cl_side ]
      | eapply exb_div2; [ eassumption | lift | lift | cl_side | cl_side ] ]
  | |- exb (fsqrt _) _ _ => eapply exb_sqrt; [ lift | eassumption | cl_side ]
  | |- exb (lib_exp _ _) _ _ => eapply exb_lib_exp; [ eassumption | lift | lra ]
  | |- exb (lib_sin _ _) _ _ => eapply exb_lib_sin; [ eassumption | lift | lra ]
  | |- exb (lib_norm_cdf _ _) _ _ => eapply exb_lib_ncdf; [ eassumption | lift ]
  | _ => solve [ eauto with exb ]
  end.

(** Exactness of the doubling and the halvings the kernel does by [2] and [4]. *)
Lemma fmtF_double r : fmtF r -> fmtF (2 * r).
Proof.
  intros F. destruct (FLT_format_generic radix2 (-1074) 53 r F) as [[m e] H1 H2 H3].
  apply generic_format_FLT. exists (Float radix2 m (e + 1)).
  - rewrite H1. unfold F2R. simpl. rewrite bpow_plus. change (bpow radix2 1) with 2. ring.
  - simpl. exact H2.
  - simpl. unfold emin. simpl in H3. lia.
Qed.

Lemma fmtF_div_pow2 r k : fmtF r -> bpow radix2 (-1000) <= Rabs r -> (0 <= k <= 20)%Z -> fmtF (r / bpow radix2 k).
Proof.
  intros F Hr Hk. destruct (FLT_format_generic radix2 (-1074) 53 r F) as [[m e] H1 H2 H3].
  simpl in H2, H3.
  assert (Hek : (-1074 <= e - k)%Z).
  { destruct (Z_le_gt_dec (-1074 + k) e) as [A | A]; [lia |].
    exfalso.
    assert (Hm : Rabs (IZR m) < bpow radix2 53).
    { rewrite <- abs_IZR. rewrite <- (IZR_Zpower radix2 53) by lia. apply IZR_lt. exact H2. }
    assert (Hr2 : Rabs r = Rabs (IZR m) * bpow radix2 e).
    { rewrite H1. unfold F2R. simpl. rewrite Rabs_mult, (Rabs_pos_eq (bpow radix2 e)); [reflexivity | apply bpow_ge_0]. }
    assert (He : bpow radix2 e <= bpow radix2 (-1054)) by (apply bpow_le; lia).
    pose proof (Rabs_pos (IZR m)) as Pm.
    assert (Hlt : Rabs (IZR m) * bpow radix2 e < bpow radix2 53 * bpow radix2 (-1054)).
    { apply Rle_lt_trans with (Rabs (IZR m) * bpow radix2 (-1054)).
      - apply Rmult_le_compat_l; [exact Pm | exact He].
      - apply Rmult_lt_compat_r; [apply bpow_gt_0 | exact Hm]. }
    rewrite <- bpow_plus in Hlt.
    assert (Hb : bpow radix2 (53 + -1054) <= bpow radix2 (-1000)) by (apply bpow_le; lia).
    rewrite <- Hr2 in Hlt. lra. }
  apply generic_format_FLT. exists (Float radix2 m (e - k)).
  - rewrite H1. unfold F2R. simpl.
    replace (e - k)%Z with (e + - k)%Z by ring.
    rewrite bpow_plus, bpow_opp.
    assert (bpow radix2 k <> 0) by (apply Rgt_not_eq; apply bpow_gt_0).
    field. assumption.
  - simpl. exact H2.
  - simpl. unfold emin. exact Hek.
Qed.

Lemma exb_k2_is : B k2 = 2. Proof. exact (proj1 (proj2 exb_k2)). Qed.

(** Halving and quartering are exact away from the subnormal range. *)
Lemma exb_half a r E : exb a r E -> (r = 0 \/ bpow radix2 (-1000) <= Rabs r) -> (cl E <= 1000)%Z ->
  exb (fdiv a k2) (r / 2) (cl E).
Proof.
  intros Ha Hr Hc.
  pose proof (exb_div_one a k2 r 2 E 1 Ha exb_k2 ltac:(lia) ltac:(rewrite Rabs_pos_eq by lra; lra) ltac:(unfold cl in Hc; unfold cl; lia)) as H.
  assert (E0 : rndF (r / 2) = r / 2).
  { apply round_generic; [exact _ |]. destruct Hr as [-> | Hr].
    - replace (0 / 2) with 0 by field. apply generic_format_0.
    - change 2 with (bpow radix2 1).
      pose proof (B_fmt a) as Fa. rewrite (exb_val _ _ _ Ha) in Fa.
      apply fmtF_div_pow2; [exact Fa | exact Hr | lia]. }
  rewrite E0 in H. replace (cl (E + 0)) with (cl E) in H by (unfold cl; f_equal; lia). exact H.
Qed.

(** [lift_to E] proves [exb a r E] with the bound the operations give, if it is at most [E]. *)
Ltac lift_to := eapply exb_weak; [ lift | cl_side ].

(** Doubling and quartering. *)
Lemma exb_double a r E : exb a r E -> (cl (E + 1) <= 1000)%Z -> exb (k2 *f a) (2 * r) (cl (E + 1)).
Proof.
  intros Ha Hc.
  pose proof (exb_mul k2 a 2 r 1 E exb_k2 Ha ltac:(unfold cl in Hc |- *; lia)) as H.
  assert (E0 : rndF (2 * r) = 2 * r).
  { apply round_generic; [exact _ |]. apply fmtF_double. rewrite <- (exb_val _ _ _ Ha). apply B_fmt. }
  rewrite E0 in H. eapply exb_weak; [exact H | unfold cl; lia].
Qed.

Lemma exb_quarter a r E : exb a r E -> (r = 0 \/ bpow radix2 (-1000) <= Rabs r) -> (cl E <= 1000)%Z ->
  exb (a /f k4) (r / 4) (cl E).
Proof.
  intros Ha Hr Hc.
  pose proof (exb_div_one a k4 r 4 E 2 Ha exb_k4 ltac:(lia) ltac:(rewrite Rabs_pos_eq by lra; lra) ltac:(unfold cl in Hc |- *; lia)) as H.
  assert (E0 : rndF (r / 4) = r / 4).
  { apply round_generic; [exact _ |]. destruct Hr as [-> | Hr].
    - replace (0 / 4) with 0 by field. apply generic_format_0.
    - change 4 with (bpow radix2 2).
      pose proof (B_fmt a) as Fa. rewrite (exb_val _ _ _ Ha) in Fa.
      apply fmtF_div_pow2; [exact Fa | exact Hr | lia]. }
  rewrite E0 in H. replace (cl (E + 0)) with (cl E) in H by (unfold cl; f_equal; lia). exact H.
Qed.

(** The rounding error of one operation. *)
Lemma rndF_err x : Rabs (rndF x - x) <= bpow radix2 (-53) * Rabs x + bpow radix2 (-1075).
Proof.
  destruct (Rle_or_lt (bpow radix2 (-1022)) (Rabs x)) as [H | H].
  - pose proof (relative_error_N_FLT radix2 (-1074) 53 ltac:(lia) (fun n => negb (Z.even n)) x) as R.
    replace (-1074 + 53 - 1)%Z with (-1022)%Z in R by reflexivity. specialize (R H).
    assert (E : / 2 * bpow radix2 (- (53) + 1) = bpow radix2 (-53)).
    { replace (- (53) + 1)%Z with (-53 + 1)%Z by reflexivity. rewrite bpow_plus.
      change (bpow radix2 1) with 2%R. field. }
    assert (R' : Rabs (rndF x - x) <= bpow radix2 (-53) * Rabs x) by (rewrite <- E; exact R).
    pose proof (bpow_ge_0 radix2 (-1075)). lra.
  - destruct (Req_dec x 0) as [H0 | H0].
    + assert (Hz : rndF 0 = 0) by (apply round_0; exact _).
      rewrite H0, Hz. rewrite Rminus_0_r, Rabs_R0. pose proof (bpow_ge_0 radix2 (-1075)). lra.
    + pose proof (error_le_half_ulp radix2 (FLT_exp (-1074) 53) (fun n => negb (Z.even n)) x) as E.
      assert (Hu : ulp radix2 (FLT_exp (-1074) 53) x <= bpow radix2 (-1074)).
      { rewrite ulp_neq_0 by exact H0. unfold cexp, FLT_exp.
        pose proof (mag_le_bpow radix2 x (-1022) H0 H) as Hm. apply bpow_le. lia. }
      assert (E2 : / 2 * bpow radix2 (-1074) = bpow radix2 (-1075)).
      { replace (-1074)%Z with (-1075 + 1)%Z by reflexivity. rewrite bpow_plus. change (bpow radix2 1) with 2%R. field. }
      assert (E3 : Rabs (rndF x - x) <= / 2 * bpow radix2 (-1074)).
      { eapply Rle_trans; [exact E |]. apply Rmult_le_compat_l; [lra | exact Hu]. }
      pose proof (bpow_ge_0 radix2 (-53)) as P. pose proof (Rabs_pos x). nra.
Qed.


(** Rounding preserves a bound that is itself a binary64 value. *)
Lemma rnd_ge_fmt a x : fmtF a -> a <= x -> a <= rndF x.
Proof.
  intros F H. rewrite <- (round_generic radix2 (FLT_exp (-1074) 53) (Znearest ne) _ F) at 1.
  apply round_le; [exact _ | exact _ | exact H].
Qed.

Lemma rnd_le_fmt b x : fmtF b -> x <= b -> rndF x <= b.
Proof.
  intros F H. rewrite <- (round_generic radix2 (FLT_exp (-1074) 53) (Znearest ne) _ F) at 1.
  apply round_le; [exact _ | exact _ | exact H].
Qed.

Lemma fmtF_one : fmtF 1.
Proof. replace 1 with (bpow radix2 0) by reflexivity. apply fmtF_bpow. lia. Qed.

(** 2Sum on operands bounded by [2^E] ([-100 <= E]): the rounded sum, bounded by [2^(E+1)],
    and its exact error, bounded by [2^E]. *)
Lemma exb_two_sum_ideal a b ra rb E : exb a ra E -> exb b rb E -> (-100 <= E <= 1000)%Z ->
  exb (fst (two_sum64 a b)) (rndF (ra + rb)) (E + 1)
  /\ exb (snd (two_sum64 a b)) (ra + rb - rndF (ra + rb)) E.
Proof.
  intros Ha Hb HE.
  pose proof (exb_two_sum a b ra rb E Ha Hb ltac:(lia)) as H1.
  assert (Ba : Rabs (B a) <= bpow radix2 1020).
  { rewrite (exb_val _ _ _ Ha). eapply Rle_trans; [exact (exb_bnd _ _ _ Ha) | apply bpow_le; lia]. }
  assert (Bb : Rabs (B b) <= bpow radix2 1020).
  { rewrite (exb_val _ _ _ Hb). eapply Rle_trans; [exact (exb_bnd _ _ _ Hb) | apply bpow_le; lia]. }
  pose proof (two_sum_ieee a b (exb_fin _ _ _ Ha) (exb_fin _ _ _ Hb) Ba Bb) as H2.
  revert H1 H2. generalize (two_sum64 a b) as p. intros [s t] H1 H2.
  destruct H1 as [E1 E2]. destruct H2 as [Fs [Ft [Bs Bst]]].
  cbn [fst snd] in E1, E2 |- .
  rewrite (exb_val _ _ _ Ha), (exb_val _ _ _ Hb) in Bs, Bst.
  pose proof (exb_val _ _ _ E1) as V1. pose proof (exb_val _ _ _ E2) as V2.
  split.
  - eapply exb_cong; [exact E1 |]. rewrite <- V1. exact Bs.
  - assert (Et : B t = ra + rb - rndF (ra + rb)) by lra.
    split; [exact Ft | split; [exact Et |]].
    pose proof (exb_bnd _ _ _ Ha) as A. pose proof (exb_bnd _ _ _ Hb) as B1.
    pose proof (rndF_err (ra + rb)) as Er.
    assert (Hab : Rabs (ra + rb) <= bpow radix2 (E + 1)).
    { eapply Rle_trans; [apply Rabs_triang |].
      rewrite bpow_plus. change (bpow radix2 1) with 2. lra. }
    assert (Hrn : Rabs (rndF (ra + rb) - (ra + rb)) <= bpow radix2 (-53) * bpow radix2 (E + 1) + bpow radix2 (-1075)).
    { eapply Rle_trans; [exact Er |]. apply Rplus_le_compat_r. apply Rmult_le_compat_l; [apply bpow_ge_0 | exact Hab]. }
    assert (Hc1 : bpow radix2 (-53) * bpow radix2 (E + 1) = bpow radix2 (E - 52)).
    { rewrite <- bpow_plus. f_equal. ring. }
    assert (Hc2 : bpow radix2 (E - 52) + bpow radix2 (-1075) <= bpow radix2 E).
    { assert (bpow radix2 (E - 52) <= bpow radix2 (E - 1)) by (apply bpow_le; lia).
      assert (bpow radix2 (-1075) <= bpow radix2 (E - 1)) by (apply bpow_le; lia).
      assert (bpow radix2 E = bpow radix2 (E - 1) + bpow radix2 (E - 1)).
      { replace E with ((E - 1) + 1)%Z at 1 by ring. rewrite bpow_plus. change (bpow radix2 1) with 2.
        replace (E - 1 + 1)%Z with E by ring. replace (E - 1)%Z with (E - 1)%Z by ring. lra. }
      lra. }
    replace (ra + rb - rndF (ra + rb)) with (- (rndF (ra + rb) - (ra + rb))) by ring.
    rewrite Rabs_Ropp. lra.
Qed.

(** Numeric literals for powers of two: [simpl] leaves [Z.pow_pos 2 n], which
    [lra] cannot read. *)
Ltac zpow_goal :=
  repeat match goal with
  | |- context [Z.pow_pos ?a ?n] =>
      let v := eval vm_compute in (Z.pow_pos a n) in change (Z.pow_pos a n) with v
  end.
Ltac zpow_hyp H :=
  repeat match type of H with
  | context [Z.pow_pos ?a ?n] =>
      let v := eval vm_compute in (Z.pow_pos a n) in change (Z.pow_pos a n) with v in H
  end.
Ltac bnum := simpl; zpow_goal.
Ltac bnum_in H := simpl in H; zpow_hyp H.
