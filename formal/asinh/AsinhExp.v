(** asinh's accurate path, the exponential: [asinh_exp] computes [e^y = m 2^k] with
    the 45-step [Q256] Horner series; this file bounds the series (against
    [exp r]), the argument reduction and the result. *)
From Coq Require Import Reals ZArith Lia Lra Psatz List Bool.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Q Require Import Q256 Q256Real QSpec Limbs QRound.
Require Import Ln1pLemmas AsinTables AsinKernel AsinSeries AsinQSeries AsinhTables AsinhKernel.
Import ListNotations.
Open Scope R_scope.

(** The Horner form with plus signs. *)
Fixpoint hser (r : R) (cs : list R) : R :=
  match cs with nil => 1 | c :: cs' => 1 + r * c * hser r cs' end.

Definition q_hser (r : q256) (steps : list (list Z * Z)) : q256 :=
  fold_left (fun h '(m, e) => Q256.add q_one (Q256.mul (Q256.mul r (Q256.new false m e)) h)) (rev steps) q_one.

Lemma q_hser_cons r m0 e0 steps :
  q_hser r ((m0, e0) :: steps) = Q256.add q_one (Q256.mul (Q256.mul r (Q256.new false m0 e0)) (q_hser r steps)).
Proof. unfold q_hser. cbn [rev]. rewrite fold_left_app. reflexivity. Qed.

Lemma q_hser_nil r : q_hser r [] = q_one.
Proof. reflexivity. Qed.

Lemma step_check_ok1 den m0 e0 : step_check den (m0, e0) = true -> (1 <= den)%Z ->
  ok4 m0 /\ Rabs (qval (Q256.new false m0 e0) - / IZR den) <= bpow radix2 (-254) * / IZR den.
Proof.
  unfold step_check. cbn [fst snd]. intros H D2.
  repeat rewrite andb_true_iff in H. destruct H as [[Lc Ee] Er].
  apply Z.leb_le in Ee. apply Z.leb_le in Er.
  pose proof (limbs_check_ok _ Lc) as Ok. split; [exact Ok | ].
  rewrite new_val by exact Ok. unfold val.
  unfold F2R. cbn [Fnum Fexp].
  assert (Hd : 0 < IZR den) by (apply IZR_lt; lia).
  set (N := (- e0)%Z) in *.
  assert (HN : (254 <= N)%Z) by (unfold N; lia).
  set (b := bpow radix2 (N - 254)). set (k := bpow radix2 254).
  assert (Pb : 0 < b) by apply bpow_gt_0. assert (Pk : 0 < k) by apply bpow_gt_0.
  assert (HBn : IZR (2 ^ N) = b * k).
  { unfold b, k. rewrite <- bpow_plus. replace (N - 254 + 254)%Z with N by ring. apply IZR_pow2'. lia. }
  assert (Hb2 : IZR (2 ^ (N - 254)) = b) by (unfold b; apply IZR_pow2'; lia).
  assert (E1 : bpow radix2 e0 = / (b * k)).
  { rewrite <- HBn. rewrite IZR_pow2' by lia. replace e0 with (- N)%Z by (unfold N; ring). rewrite bpow_opp. reflexivity. }
  assert (HB : bpow radix2 (-254) = / k) by (unfold k; bpow_num; reflexivity).
  rewrite E1, HB.
  set (X := IZR den * IZR (Limbs.v m0) - b * k).
  assert (HX : Rabs X <= b).
  { unfold X. rewrite <- HBn, <- Hb2. rewrite <- mult_IZR, <- minus_IZR, <- abs_IZR. apply IZR_le. exact Er. }
  assert (Hd0 : IZR den <> 0) by (apply not_eq_sym, Rlt_not_eq; exact Hd).
  assert (Hb0 : b <> 0) by (apply not_eq_sym, Rlt_not_eq; exact Pb).
  assert (Hk0 : k <> 0) by (apply not_eq_sym, Rlt_not_eq; exact Pk).
  assert (Hpos : 0 < IZR den * (b * k)) by (apply Rmult_lt_0_compat; [exact Hd | apply Rmult_lt_0_compat; assumption]).
  assert (Eq : IZR (Limbs.v m0) * / (b * k) - / IZR den = X * / (IZR den * (b * k))).
  { unfold X. field. all: repeat split; assumption. }
  rewrite Eq.
  rewrite Rabs_mult. rewrite (Rabs_pos_eq (/ (IZR den * (b * k)))) by (apply Rlt_le; apply Rinv_0_lt_compat; exact Hpos).
  apply Rle_trans with (b * / (IZR den * (b * k))).
  - apply Rmult_le_compat_r; [apply Rlt_le; apply Rinv_0_lt_compat; exact Hpos | exact HX].
  - apply Req_le. field. all: repeat split; assumption.
Qed.


(** One level of the series. *)
Lemma hser_step_err (r c h : q256) cc H K :
  Q256Real.valid r -> Q256Real.valid c -> Q256Real.valid h ->
  Rabs (qval r) <= 0.35 -> 0 < cc <= 1 ->
  Rabs (qval c - cc) <= bpow radix2 (-254) * cc ->
  0.4 <= H <= 1.6 -> Rabs (qval h - H) <= K -> bpow radix2 (-250) <= K <= bpow radix2 (-200) ->
  Q256Real.valid (Q256.add q_one (Q256.mul (Q256.mul r c) h)) /\
  Rabs (qval (Q256.add q_one (Q256.mul (Q256.mul r c) h)) - (1 + qval r * cc * H)) <= K.
Proof.
  intros Vr Vc Vh Hr [Hcc0 Hcc1] Hc [HH0 HH1] Hh [HK0 HK1].
  destruct q_one_valid as [Vone Qone].
  destruct (mul_relative r c Vr Vc) as [V1 [d1 [D1 E1]]].
  destruct (mul_relative (Q256.mul r c) h V1 Vh) as [V2 [d2 [D2 E2]]].
  destruct (add_any q_one (Q256.mul (Q256.mul r c) h) Vone V2) as [V4 E4].
  split; [exact V4 | ].
  destruct bpow_254 as [B252 [B255 [Upos Usmall]]].
  set (U := bpow radix2 (-254)) in *.
  set (rv := qval r) in *. set (cv := qval c) in *. set (hv := qval h) in *.
  set (p2 := qval (Q256.mul (Q256.mul r c) h)) in *.
  rewrite Qone in E4.
  rewrite B255 in D1, D2.
  assert (HKU : 16 * U <= K).
  { assert (E : bpow radix2 (-250) = 16 * U) by (unfold U; replace (-250)%Z with (-254 + 4)%Z by reflexivity; rewrite bpow_plus; change (bpow radix2 4) with 16; ring).
    lra. }
  assert (HKs : K <= / 1000000) by (apply Rle_trans with (bpow radix2 (-200)); [exact HK1 | apply Rle_trans with (bpow radix2 (-20)); [apply bpow_le; lia | bpow_num; apply Rinv_le_contravar; lra]]).
  assert (Hrcc : Rabs (rv * cc) <= 0.35).
  { rewrite Rabs_mult, (Rabs_pos_eq cc) by lra. nra. }
  set (eps := (cv - cc) / cc).
  assert (Heps : cv = cc * (1 + eps)) by (unfold eps; field; lra).
  assert (Heps' : Rabs eps <= U).
  { unfold eps. unfold Rdiv. rewrite Rabs_mult, Rabs_Rinv by lra. rewrite (Rabs_pos_eq cc) by lra.
    apply (Rmult_le_reg_r cc); [lra | ]. rewrite Rmult_assoc, Rinv_l by lra. lra. }
  set (P := (1 + eps) * (1 + d1) * (1 + d2)).
  assert (HP : Rabs (P - 1) <= 3.01 * U).
  { unfold P. apply prod3; [exact Heps' | lra | lra | lra]. }
  assert (Hp2 : p2 = rv * cc * hv * P).
  { rewrite E2, E1, Heps. unfold P. ring. }
  assert (HPa : Rabs P <= 1.0001) by (apply Rabs_le_inv in HP; apply Rabs_le; split; nra).
  assert (Hdiff : Rabs (p2 - rv * cc * H) <= 0.35 * (K * 1.0001 + 1.6 * (3.01 * U))).
  { replace (p2 - rv * cc * H) with ((rv * cc) * ((hv - H) * P + H * (P - 1))) by (rewrite Hp2; ring).
    rewrite Rabs_mult.
    apply Rle_trans with (0.35 * Rabs ((hv - H) * P + H * (P - 1))).
    - apply Rmult_le_compat_r; [apply Rabs_pos | exact Hrcc].
    - apply Rmult_le_compat_l; [lra | ].
      apply Rle_trans with (Rabs ((hv - H) * P) + Rabs (H * (P - 1))); [apply Rabs_triang | ].
      rewrite !Rabs_mult. rewrite (Rabs_pos_eq H) by lra.
      pose proof (Rabs_pos (hv - H)). pose proof (Rabs_pos P). pose proof (Rabs_pos (P - 1)).
      assert (Rabs (hv - H) * Rabs P <= K * 1.0001) by (apply Rmult_le_compat; assumption || lra).
      assert (H * Rabs (P - 1) <= 1.6 * (3.01 * U)) by (apply Rmult_le_compat; lra).
      lra. }
  assert (Hrch : Rabs (rv * cc * H) <= 0.56).
  { rewrite Rabs_mult, (Rabs_pos_eq H) by lra. nra. }
  assert (Hp2b : Rabs p2 <= 1).
  { apply Rabs_le. apply Rabs_le_inv in Hdiff. apply Rabs_le_inv in Hrch. nra. }
  assert (Hmax : Rmax (Rabs 1) (Rabs p2) <= 1).
  { apply Rmax_lub; [rewrite Rabs_pos_eq by lra; lra | exact Hp2b]. }
  assert (HE4 : Rabs (qval (Q256.add q_one (Q256.mul (Q256.mul r c) h)) - (1 + p2)) <= U).
  { apply Rle_trans with (1 := E4). replace (U) with (U * 1) at 2 by ring. apply Rmult_le_compat_l; [lra | exact Hmax]. }
  replace (qval (Q256.add q_one (Q256.mul (Q256.mul r c) h)) - (1 + rv * cc * H))
    with ((qval (Q256.add q_one (Q256.mul (Q256.mul r c) h)) - (1 + p2)) + (p2 - rv * cc * H)) by ring.
  apply Rle_trans with (Rabs (qval (Q256.add q_one (Q256.mul (Q256.mul r c) h)) - (1 + p2)) + Rabs (p2 - rv * cc * H)); [apply Rabs_triang | ].
  nra.
Qed.

(** The ideal coefficients [cs] approximate the [Q256] constants of [steps]. *)
Fixpoint const_ok1 (steps : list (list Z * Z)) (cs : list R) : Prop :=
  match steps, cs with
  | nil, nil => True
  | (m0, e0) :: st, cc :: cs' =>
      (0 < cc <= 1) /\ Rabs (qval (Q256.new false m0 e0) - cc) <= bpow radix2 (-254) * cc /\
      ok4 m0 /\ const_ok1 st cs'
  | _, _ => False
  end.

Lemma const_ok1_forall steps cs : const_ok1 steps cs -> Forall (fun c => 0 < c <= 1) cs.
Proof.
  revert cs. induction steps as [ | [m0 e0] st IH]; intros [ | cc cs'] H; simpl in H; try contradiction.
  - constructor.
  - destruct H as [Hc [_ [_ H']]]. constructor; [exact Hc | exact (IH _ H')].
Qed.

Lemma hser_range cs r : Forall (fun c => 0 < c <= 1) cs -> Rabs r <= 0.35 -> 0.4 <= hser r cs <= 1.6.
Proof.
  intros F S. apply Rabs_le_inv in S. destruct S as [S1 S2].
  induction F as [ | c cs' [Hc0 Hc1] F IH]; simpl.
  - lra.
  - destruct IH as [I1 I2].
    assert (Hm : r * c * hser r cs' <= 0.35 * 1.6 /\ - (0.35 * 1.6) <= r * c * hser r cs').
    { assert (Hrc : - 0.35 <= r * c <= 0.35) by (split; nra).
      destruct Hrc as [R1 R2]. split; nra. }
    destruct Hm as [M1 M2]. lra.
Qed.

Theorem hser_error steps cs r : const_ok1 steps cs -> Q256Real.valid r -> Rabs (qval r) <= 0.35 ->
  Q256Real.valid (q_hser r steps) /\ Rabs (qval (q_hser r steps) - hser (qval r) cs) <= bpow radix2 (-250).
Proof.
  revert cs. induction steps as [ | [m0 e0] st IH]; intros [ | cc cs'] Hc Vr Hr; simpl in Hc; try contradiction.
  - destruct q_one_valid as [V Q]. rewrite q_hser_nil. split; [exact V | ].
    change (hser (qval r) nil) with 1. rewrite Q.
    replace (1 - 1) with 0 by ring. rewrite Rabs_R0. apply bpow_ge_0.
  - destruct Hc as [Hcc [Hce [Hok Hc']]].
    destruct (IH cs' Hc' Vr Hr) as [Vh Eh].
    pose proof (hser_range cs' (qval r) (const_ok1_forall st cs' Hc') Hr) as Hrg.
    assert (HK : bpow radix2 (-250) <= bpow radix2 (-250) <= bpow radix2 (-200)) by (split; [apply Rle_refl | apply bpow_le; lia]).
    destruct (hser_step_err r (Q256.new false m0 e0) (q_hser r st) cc (hser (qval r) cs') (bpow radix2 (-250)) Vr
      (new_valid false m0 e0 Hok) Vh Hr Hcc Hce Hrg Eh HK) as [V E].
    rewrite q_hser_cons. split; [exact V | ].
    change (hser (qval r) (cc :: cs')) with (1 + qval r * cc * hser (qval r) cs'). exact E.
Qed.

(** The ideal coefficients [1/n]. *)
Definition f_exp (n : nat) : R := / IZR (Z.of_nat n).

Lemma hser_exp_ok r : Rabs r <= 0.35 -> Rabs (hser r (cs_gen f_exp 1 45) - exp r) <= bpow radix2 (-240).
Proof.
  intros H. apply Rabs_le_inv in H. destruct H as [H1 H2].
  cbn [cs_gen hser f_exp Z.of_nat Pos.of_succ_nat Pos.succ].
  bpow_num.
  apply Rabs_le. split; interval with (i_bisect r, i_taylor r, i_prec 400, i_degree 50, i_depth 1).
Qed.

Fixpoint steps_check1 (dens : nat -> Z) (j : nat) (steps : list (list Z * Z)) : bool :=
  match steps with
  | nil => true
  | st :: tl => step_check (dens j) st && (1 <=? dens j)%Z && steps_check1 dens (S j) tl
  end.

Lemma steps_check1_sound dens f steps : forall j, (forall n, f n = / IZR (dens n)) ->
  steps_check1 dens j steps = true -> const_ok1 steps (cs_gen f j (length steps)).
Proof.
  induction steps as [ | [m0 e0] st IH]; intros j Hf C; simpl.
  - exact I.
  - simpl in C. rewrite !andb_true_iff in C. destruct C as [[Cs C2] Cr].
    apply Z.leb_le in C2.
    destruct (step_check_ok1 (dens j) m0 e0 Cs C2) as [Ok E].
    rewrite Hf. assert (Hd : 1 <= IZR (dens j)) by (change 1 with (IZR 1); apply IZR_le; exact C2).
    refine (conj (conj _ _) (conj E (conj Ok _))).
    + apply Rinv_0_lt_compat; lra.
    + rewrite <- Rinv_1. apply Rinv_le_contravar; lra.
    + exact (IH (S j) Hf Cr).
Qed.

Definition dens_exp (j : nat) : Z := Z.of_nat j.

Lemma exp_steps_check : steps_check1 dens_exp 1 asinh_exp_steps = true.
Proof. vm_compute. reflexivity. Qed.

Lemma exp_steps_len : length asinh_exp_steps = 45%nat.
Proof. reflexivity. Qed.

Theorem exp_const_ok : const_ok1 asinh_exp_steps (cs_gen f_exp 1 45).
Proof.
  change 45%nat with (length asinh_exp_steps).
  exact (steps_check1_sound dens_exp f_exp asinh_exp_steps 1 (fun n => eq_refl) exp_steps_check).
Qed.

(** The series, for a reduced argument [|r| <= 0.35]: within [2^-239] of [exp r]. *)
Theorem q_hser_exp r : Q256Real.valid r -> Rabs (qval r) <= 0.35 ->
  Q256Real.valid (q_hser r asinh_exp_steps) /\ Rabs (qval (q_hser r asinh_exp_steps) - exp (qval r)) <= bpow radix2 (-239).
Proof.
  intros Vr Hr. destruct (hser_error asinh_exp_steps (cs_gen f_exp 1 45) r exp_const_ok Vr Hr) as [V E].
  pose proof (hser_exp_ok (qval r) Hr) as T. split; [exact V | ].
  apply Rle_trans with (Rabs (qval (q_hser r asinh_exp_steps) - hser (qval r) (cs_gen f_exp 1 45)) + Rabs (hser (qval r) (cs_gen f_exp 1 45) - exp (qval r))).
  - replace (qval (q_hser r asinh_exp_steps) - exp (qval r)) with
      ((qval (q_hser r asinh_exp_steps) - hser (qval r) (cs_gen f_exp 1 45)) + (hser (qval r) (cs_gen f_exp 1 45) - exp (qval r))) by ring.
    apply Rabs_triang.
  - assert (Hb : bpow radix2 (-250) + bpow radix2 (-240) <= bpow radix2 (-239)).
    { assert (bpow radix2 (-250) <= bpow radix2 (-240)) by (apply bpow_le; lia).
      assert (bpow radix2 (-239) = 2 * bpow radix2 (-240)) by (replace (-239)%Z with (-240 + 1)%Z by reflexivity; rewrite bpow_plus; change (bpow radix2 1) with 2; ring).
      lra. }
    lra.
Qed.
