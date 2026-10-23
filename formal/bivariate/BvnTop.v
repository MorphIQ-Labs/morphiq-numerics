(** The absolute error of the low-correlation branch, from the table of one
    rule: [|R - P| <= B] for the computed result [R] and
    [P = Phi(x) Phi(y) + (1/2 pi) int_0^{asin rho} f]. Every classical or
    library fact the statement uses is a hypothesis of the theorem:

    - the normal distribution function, [asin], [sin], [cos] and [exp] are
      correctly rounded ([Phi_cr] below and the definitions of the node
      terms), as their derivation documents prove;
    - [Plackett]: the exact value is a probability, so the clamp cannot raise
      the error;
    - [T1]: the Gauss-Legendre remainder, the cited theorem of
      docs/bivariate_normal_truncation.md section 2. *)
From Coq Require Import Reals ZArith Lia Lra Psatz List.
Import ListNotations.
From Flocq Require Import Core.
From Double Require Import DWPlus.
From Binary64 Require Import Binary64Add.
From Interval Require Import Tactic.
From Coquelicot Require Import Coquelicot.
Require Import BvnRound BvnArg BvnNode BvnTrig BvnLow BvnSum BvnChain BvnQuadG BvnRule BvnTail BvnIntegral.
Open Scope R_scope.

(** The corrected sum with a constant of either sign: rounding is odd. *)
Lemma rule_bound_signed x y asr A etaK nodes dats Kex Kh :
  0 <= etaK -> dom x -> dom y -> bpow radix2 (-53) <= Rabs asr -> Rabs asr <= A -> A <= 6 / 5 ->
  Forall2 (node_ok asr A) nodes dats -> (length nodes <= 24)%nat ->
  Rabs Kex <= 1 -> Rabs (Kh - Kex) <= etaK * Rabs Kex -> etaK <= / 1000 ->
  Rabs (rndF (rndF (fst (acc (map (tn x y asr) nodes) (0, 0)) + snd (acc (map (tn x y asr) nodes) (0, 0))) * Kh)
        - Kex * sumR (map (vn x y asr) nodes))
    <= Rabs Kex * sum2 (gn A etaK) nodes dats + 1000 * z.
Proof.
  intros Heta Hx Hy Ha1 Ha2 HA Hall Hlen HK1 HKh Heta1.
  set (hh := rndF (fst (acc (map (tn x y asr) nodes) (0, 0)) + snd (acc (map (tn x y asr) nodes) (0, 0)))).
  destruct (Rle_dec 0 Kex) as [Hk | Hk].
  - rewrite (Rabs_pos_eq Kex Hk) in *.
    exact (rule_bound x y asr A etaK Heta nodes dats Kex Kh Hx Hy Ha1 Ha2 HA Hall Hlen Hk HK1 HKh Heta1).
  - assert (Hk' : 0 <= - Kex) by lra.
    rewrite (Rabs_left Kex ltac:(lra)) in *.
    pose proof (rule_bound x y asr A etaK Heta nodes dats (- Kex) (- Kh) Hx Hy Ha1 Ha2 HA Hall Hlen Hk' HK1
      ltac:(replace (- Kh - - Kex) with (- (Kh - Kex)) by ring; rewrite Rabs_Ropp; exact HKh) Heta1) as H.
    fold hh in H.
    replace (hh * Kh) with (- (hh * - Kh)) by ring. rewrite rnd_opp.
    replace (- rndF (hh * - Kh) - Kex * sumR (map (vn x y asr) nodes))
      with (- (rndF (hh * - Kh) - - Kex * sumR (map (vn x y asr) nodes))) by ring.
    rewrite Rabs_Ropp. exact H.
Qed.

(** The result of the low-correlation branch for one rule: the correction
    [Chat], the product of the rounded distribution functions, their sum and
    the clamp, as the Rust forms them. *)
Definition Chat (x y asr : R) (nodes : list NodeS) : R :=
  rndF (rndF (fst (acc (map (tn x y asr) nodes) (0, 0)) + snd (acc (map (tn x y asr) nodes) (0, 0))) * rndF (asr / (2 * TAU))).

Definition Rhat (x y asr : R) (nodes : list NodeS) (Phix Phiy : R) : R :=
  clampf (rndF (Chat x y asr nodes + rndF (rndF Phix * rndF Phiy))).

Theorem low_branch x y rho asr A Tr Phix Phiy nodes dats :
  dom x -> dom y ->
  0 <= Phix <= 1 -> 0 <= Phiy <= 1 ->
  asr = rndF (asin rho) -> bpow radix2 (-53) <= Rabs asr -> Rabs asr <= A -> A <= 6 / 5 ->
  Rabs (asin rho) <= 3 / 2 ->
  Forall2 (node_ok asr A) nodes dats -> (length nodes <= 24)%nat ->
  (* Plackett: the exact value is a probability *)
  0 <= Phix * Phiy + Iint (x * x + y * y) (x * y) (asin rho) / (2 * PI) <= 1 ->
  (* T1: the Gauss-Legendre remainder at the rounded angle *)
  Rabs (Iint (x * x + y * y) (x * y) asr - asr / 2 * sumR (map (vn x y asr) nodes)) <= Tr ->
  Rabs (Rhat x y asr nodes Phix Phiy - (Phix * Phiy + Iint (x * x + y * y) (x * y) (asin rho) / (2 * PI)))
    <= 4 * bpow radix2 (-54) + A / (4 * PI) * sumD (gdat A ETAK) dats + 1000 * z
       + Tr / (2 * PI) + bpow radix2 (-53) / (2 * PI).
Proof.
  intros Hx Hy HPx HPy Hasr Ha1 Ha2 HA Hasin Hall Hlen Hprob HT1.
  pose proof u_pos as Hu. pose proof z_pos as Hz.
  assert (HPI : 3 < PI < 315 / 100) by (pose proof PI_RGT_0; split; interval).
  destruct HPI as [HPI1 HPI2].
  set (r := x * x + y * y). set (p := x * y).
  assert (Hr : 0 <= r) by (unfold r; nra).
  assert (Hp : Rabs p <= r / 2).
  { unfold p, r. pose proof (Rle_0_sqr (x - y)) as h1. pose proof (Rle_0_sqr (x + y)) as h2. unfold Rsqr in h1, h2.
    apply Rabs_le. split; nra. }
  set (Kex := asr / (4 * PI)).
  set (Kh := rndF (asr / (2 * TAU))).
  set (V := sumR (map (vn x y asr) nodes)).
  assert (HKex1 : Rabs Kex <= 1).
  { unfold Kex. rewrite Rabs_div_pos by lra. apply Rmult_le_reg_r with (4 * PI); [lra |].
    unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. lra. }
  assert (HKh : Rabs (Kh - Kex) <= ETAK * Rabs Kex) by (apply K_close; lra).
  assert (HETAK : 0 <= ETAK /\ ETAK <= / 1000) by (unfold ETAK; split; lra).
  destruct HETAK as [HE0 HE1].
  assert (HAbs : Rabs asr <= A) by exact Ha2.
  (* the rounded correction *)
  pose proof (rule_bound_signed x y asr A ETAK nodes dats Kex Kh HE0 Hx Hy Ha1 Ha2 HA Hall Hlen HKex1 HKh HE1) as HC.
  change (Rabs (Chat x y asr nodes - Kex * V) <= Rabs Kex * sum2 (gn A ETAK) nodes dats + 1000 * z) in HC.
  assert (Hbp : 0 <= bp ETAK).
  { unfold bp, psi. assert (1 <= (1 + ETAK) * (1 + 2000 * u * u) * (1 + u) * (1 + u)) by (unfold ETAK in *; nra).
    assert (1 <= (1 + u) ^ 3) by (apply pow_R1_Rle; lra).
    assert (1 <= exp z) by (rewrite <- exp_0; apply exp_mono; lra).
    replace ((1 + ETAK) * (1 + 2000 * u * u) * (1 + u) * (1 + u) - 1 + 1) with ((1 + ETAK) * (1 + 2000 * u * u) * (1 + u) * (1 + u)) by ring.
    assert (1 <= (1 + ETAK) * (1 + 2000 * u * u) * (1 + u) * (1 + u) * (1 + u) ^ 3) by nra.
    nra. }
  pose proof (sum_g_le asr A ETAK nodes dats Hbp Hall) as Hg.
  assert (HKA : Rabs Kex <= A / (4 * PI)).
  { unfold Kex. rewrite Rabs_div_pos by lra. unfold Rdiv. apply Rmult_le_compat_r; [apply Rlt_le, Rinv_0_lt_compat; lra | exact Ha2]. }
  pose proof (sum_g_nonneg asr A ETAK nodes dats Hbp Hall) as Hg0.
  assert (HCb : Rabs (Chat x y asr nodes - Kex * V) <= A / (4 * PI) * sumD (gdat A ETAK) dats + 1000 * z).
  { eapply Rle_trans; [exact HC |].
    assert (Hm : Rabs Kex * sum2 (gn A ETAK) nodes dats <= A / (4 * PI) * sumD (gdat A ETAK) dats).
    { apply Rmult_le_compat; [apply Rabs_pos | exact Hg0 | exact HKA | exact Hg]. }
    lra. }
  (* the integral *)
  assert (HIn : Rabs (Iint r p asr / (2 * PI) - Kex * V) <= Tr / (2 * PI)).
  { assert (E : Iint r p asr / (2 * PI) - Kex * V = (Iint r p asr - asr / 2 * V) / (2 * PI)).
    { unfold Kex. field. lra. }
    rewrite E. rewrite Rabs_div_pos by lra. unfold Rdiv. apply Rmult_le_compat_r; [apply Rlt_le, Rinv_0_lt_compat; lra | exact HT1]. }
  assert (Hshift : Rabs (asin rho - asr) <= bpow radix2 (-53)).
  { rewrite Hasr. rewrite Rabs_minus_sym.
    replace (-53)%Z with (1 - 54)%Z by reflexivity. apply rnd_pow; [lia |].
    replace (bpow radix2 1) with 2 by reflexivity. lra. }
  assert (HIl : Rabs (Iint r p (asin rho) / (2 * PI) - Iint r p asr / (2 * PI)) <= bpow radix2 (-53) / (2 * PI)).
  { assert (E : Iint r p (asin rho) / (2 * PI) - Iint r p asr / (2 * PI) = (Iint r p (asin rho) - Iint r p asr) / (2 * PI)) by (field; lra).
    rewrite E. rewrite Rabs_div_pos by lra. unfold Rdiv. apply Rmult_le_compat_r; [apply Rlt_le, Rinv_0_lt_compat; lra |].
    eapply Rle_trans; [apply Iint_lip; try assumption; lra |]. exact Hshift. }
  set (c := Iint r p (asin rho) / (2 * PI)) in *.
  assert (Hasrb : Rabs asr <= 3 / 2) by lra.
  assert (HChat : Rabs (Chat x y asr nodes - c) <= A / (4 * PI) * sumD (gdat A ETAK) dats + 1000 * z + Tr / (2 * PI) + bpow radix2 (-53) / (2 * PI)).
  { assert (E : Chat x y asr nodes - c = (Chat x y asr nodes - Kex * V) + (Kex * V - Iint r p asr / (2 * PI)) + (Iint r p asr / (2 * PI) - c)) by ring.
    rewrite E. eapply Rle_trans; [apply Rabs_triang |]. eapply Rle_trans; [apply Rplus_le_compat_r; apply Rabs_triang |].
    rewrite (Rabs_minus_sym (Kex * V)). rewrite (Rabs_minus_sym (Iint r p asr / (2 * PI)) c). lra. }
  (* the product of the distribution functions *)
  pose proof (phi_part Phix Phiy (rndF Phix) (rndF Phiy) HPx HPy eq_refl eq_refl) as HPh.
  (* the sum and the clamp *)
  unfold Rhat.
  set (s := Chat x y asr nodes + rndF (rndF Phix * rndF Phiy)).
  pose proof (clamp_round s (Phix * Phiy + c) Hprob) as Hcl.
  assert (Hs : Rabs (s - (Phix * Phiy + c)) <= Rabs (Chat x y asr nodes - c) + 3 * bpow radix2 (-54)).
  { assert (E : s - (Phix * Phiy + c) = (Chat x y asr nodes - c) + (rndF (rndF Phix * rndF Phiy) - Phix * Phiy)) by (unfold s; ring).
    rewrite E. eapply Rle_trans; [apply Rabs_triang |]. lra. }
  lra.
Qed.
