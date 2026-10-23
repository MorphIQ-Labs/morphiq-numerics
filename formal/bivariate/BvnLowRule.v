(** The branch bound for a rule, from the rule's correlation limit [L]: the
    angle of every [|rho| <= L] is below [A], so the rule's data apply. *)
From Coq Require Import Reals ZArith Lia Lra List.
Import ListNotations.
From Flocq Require Import Core.
From Double Require Import DWPlus.
From Binary64 Require Import Binary64Add.
From Interval Require Import Tactic.
From Coquelicot Require Import Coquelicot.
Require Import BvnRound BvnQ BvnArg BvnNode BvnTrig BvnLow BvnSum BvnQuadG BvnTail BvnRule BvnIntegral BvnFinal BvnTop.
Open Scope R_scope.

Lemma asin_le_A rho L A : Rabs rho <= L -> L + 2 / 10 ^ 4 <= sin A -> 0 <= A -> A <= 3 / 2 ->
  Rabs (asin rho) <= A - 1 / 10 ^ 4.
Proof.
  intros Hr HL HA0 HA1. pose proof PI2_gt as Hp.
  assert (Hrho : -1 <= rho <= 1).
  { assert (Rabs rho <= 1).
    { assert (sin A <= 1) by (pose proof (SIN_bound A) as [_ H]; exact H). lra. }
    apply Rabs_le_between in H. exact H. }
  destruct Hrho as [Hr1 Hr2].
  pose proof (asin_bound rho) as [Hl Hu].
  pose proof (sin_asin rho (conj Hr1 Hr2)) as Hs.
  set (a := asin rho) in *.
  apply Rabs_le_between in Hr.
  apply Rabs_le_between.
  split.
  - (* a >= -(A - 1e-4): if a < -(A-1e-4) then rho = sin a < -L *)
    destruct (Rlt_le_dec a (-(A - 1 / 10 ^ 4))) as [Hlt | Hge]; [| lra].
    exfalso.
    destruct (Rle_dec (-A) a) as [H1 | H1].
    + pose proof (sin_lip (-A) a) as Hlip. rewrite sin_neg in Hlip.
      assert (Rabs (- sin A - sin a) <= Rabs (- A - a)) by exact Hlip.
      apply Rabs_le_between in H. rewrite Rabs_left1 in H by lra.
      destruct H as [H2 H3]. rewrite Hs in *. lra.
    + assert (sin a <= sin (- A)) by (apply sin_incr_1; lra).
      rewrite sin_neg in H. rewrite Hs in H. lra.
  - destruct (Rlt_le_dec (A - 1 / 10 ^ 4) a) as [Hlt | Hge]; [| lra].
    exfalso.
    destruct (Rle_dec a A) as [H1 | H1].
    + pose proof (sin_lip A a) as Hlip.
      apply Rabs_le_between in Hlip.
      rewrite Rabs_pos_eq in Hlip by lra. destruct Hlip as [H2 H3]. rewrite Hs in *. lra.
    + assert (sin A <= sin a) by (apply sin_incr_1; lra).
      rewrite Hs in H. lra.
Qed.


(** The multiplicative constant of one term: folded weight, [exp], product,
    the accumulation, as an upper bound of [bq]. *)
Definition B0 : R := 62 / 10 ^ 17.

Lemma B0_ok : 0 <= B0 /\ bq <= B0.
Proof.
  split; [unfold B0; lra |].
  unfold bq, psi2, ew, rx, ue, ETAK, u, z. simpl. interval with (i_prec 120).
Qed.

Theorem low_rule (expI sinI : R -> R) (x y rho asr L A Tr E T S Bd : R) (kA : Z) (pxI pyI Phix Phiy : R)
  (nodes : list NodeS) (dats : list Dat) :
  exp_contract expI -> sin_contract sinI ->
  L + 2 / 10 ^ 4 <= sin A -> 0 <= A -> A <= 6 / 5 -> (-1021 <= kA)%Z -> (kA <= 1)%Z -> A <= bpow radix2 kA ->
  List.Forall (dat_ok A) dats -> List.Forall (br_ok A B0) dats ->
  A / (4 * PI) * sumD (gcl A B0) dats <= E -> E <= 1 ->
  Tr / (2 * PI) <= T -> (bpow radix2 (kA - 54) + bpow radix2 (-62) * bpow radix2 kA) / (2 * PI) <= S ->
  bpow radix2 (-54) + bpow radix2 (-900) + bpow radix2 (-90) + 2 * eP + E + 200 * z + T + S <= Bd ->
  Rabs rho <= L -> bpow radix2 (-52) <= Rabs rho ->
  fmtF x -> fmtF y -> Rabs x <= 64 -> Rabs y <= 64 ->
  0 <= Phix <= 1 -> 0 <= Phiy <= 1 -> fmtF pxI -> fmtF pyI -> 0 <= pxI <= 1 -> 0 <= pyI <= 1 ->
  Rabs (pxI - Phix) <= eP -> Rabs (pyI - Phiy) <= eP ->
  (exists Za, asr = rndF Za /\ Rabs (Za - asin rho) <= bpow radix2 (-62) * Rabs (asin rho)) ->
  List.Forall2 (ok A (rndF (asr / (2 * TAU)))) nodes dats -> (length nodes <= 24)%nat ->
  0 <= Phix * Phiy + Iint (x * x + y * y) (x * y) (asin rho) / (2 * PI) <= 1 ->
  Rabs (Iint (x * x + y * y) (x * y) asr
        - asr / 2 * sumR (map (fun n => nW n * exp (- Qn x y asr n)) nodes)) <= Tr ->
  Rabs (Rhat expI sinI x y asr nodes pxI pyI - (Phix * Phiy + Iint (x * x + y * y) (x * y) (asin rho) / (2 * PI)))
    <= Bd.
Proof.
  intros Hexp Hsin HL HA0 HA1 Hk1 Hk2 HAk Hdat Hbr Hsum HE1 HT HS HBd Hrho Hrlow Fx Fy Hx Hy HPx HPy Fpx Fpy Hpx Hpy Epx Epy Hasin Hall Hlen Hprob HT1.
  pose proof u_pos as Hu. pose proof u_val as Huv. pose proof z_pos as Hz.
  destruct B0_ok as [HB00 HB0q].
  assert (Hrng : Rabs (asin rho) <= A - 1 / 10 ^ 4) by (apply (asin_le_A rho L A); lra).
  destruct Hasin as [Za [Eas HZa]].
  assert (Hasin1 : Rabs (asin rho) >= bpow radix2 (-52)).
  { assert (Hs : Rabs (sin (asin rho) - sin 0) <= Rabs (asin rho - 0)) by apply sin_lip.
    rewrite sin_0, Rminus_0_r, Rminus_0_r in Hs.
    assert (Hrr : -1 <= rho <= 1).
    { apply Rabs_le_between. assert (sin A <= 1) by (pose proof (SIN_bound A) as [_ H]; exact H). lra. }
    rewrite (sin_asin rho Hrr) in Hs. lra. }
  assert (Hb62 : bpow radix2 (-62) <= / 1000000) by (apply Rle_trans with (bpow radix2 (-20)); [apply bpow_le; lia | change (bpow radix2 (-20)) with (/ 1048576); lra]).
  assert (HZ1 : Rabs Za <= (1 + bpow radix2 (-62)) * Rabs (asin rho)).
  { assert (Eq0 : Za = asin rho + (Za - asin rho)) by ring.
    assert (Rabs Za <= Rabs (asin rho) + Rabs (Za - asin rho)) by (rewrite Eq0 at 1; apply Rabs_triang). lra. }
  assert (HZ2 : Rabs Za >= (1 - bpow radix2 (-62)) * Rabs (asin rho)).
  { assert (Eq0 : asin rho = Za + (asin rho - Za)) by ring.
    assert (Rabs (asin rho) <= Rabs Za + Rabs (asin rho - Za)) by (rewrite Eq0 at 1; apply Rabs_triang).
    rewrite Rabs_minus_sym in HZa. lra. }
  pose proof (rnd_rel_z Za) as Hr. rewrite <- Eas in Hr.
  assert (Hz' : z <= bpow radix2 (-100)) by (unfold z; apply bpow_le; lia).
  assert (Hb100 : bpow radix2 (-100) <= bpow radix2 (-53) / 1000000) by (replace (bpow radix2 (-53) / 1000000) with (bpow radix2 (-53) * / 1000000) by reflexivity; apply Rle_trans with (bpow radix2 (-53) * bpow radix2 (-20)); [rewrite <- bpow_plus; apply bpow_le; lia | apply Rmult_le_compat_l; [apply Rlt_le, bpow_gt_0 | change (bpow radix2 (-20)) with (/ 1048576); lra]]).
  assert (Hb53 : bpow radix2 (-52) = 2 * bpow radix2 (-53)) by (replace (-52)%Z with (-53 + 1)%Z by reflexivity; rewrite bpow_plus; change (bpow radix2 1) with 2; ring).
  assert (Hasr1 : bpow radix2 (-53) <= Rabs asr).
  { assert (Eq1 : Za = asr - (asr - Za)) by ring.
    assert (Rabs Za <= Rabs asr + Rabs (asr - Za)) by (rewrite Eq1 at 1; eapply Rle_trans; [apply Rabs_triang |]; rewrite Rabs_Ropp; lra).
    assert (Hm : u * Rabs Za <= u * 2) by nra.
    pose proof (bpow_gt_0 radix2 (-53)).
    assert (Hm2 : (1 - bpow radix2 (-62)) * Rabs (asin rho) >= (1 - / 1000000) * bpow radix2 (-52)).
    { apply Rle_ge. apply Rmult_le_compat; [lra | apply Rlt_le; apply bpow_gt_0 | lra | lra]. }
    pose proof (Rabs_pos Za). nra. }
  assert (Hasr2 : Rabs asr <= A).
  { assert (Eq1 : asr = Za + (asr - Za)) by ring.
    assert (Rabs asr <= Rabs Za + Rabs (asr - Za)) by (rewrite Eq1 at 1; apply Rabs_triang).
    assert (Hm : u * Rabs Za <= u * 2).
    { apply Rmult_le_compat_l; [lra |]. assert (Rabs (asin rho) <= 6 / 5) by lra. nra. }
    assert (HZA : Rabs Za <= A - 1 / 10 ^ 4 / 2).
    { assert (Hm3 : bpow radix2 (-62) * Rabs (asin rho) <= / 1000000 * 2) by (apply Rmult_le_compat; [apply Rlt_le, bpow_gt_0 | apply Rabs_pos | lra | lra]). lra. }
    assert (Hm4 : (1 + bpow radix2 (-62)) * Rabs (asin rho) <= Rabs (asin rho) + / 1000000 * 2) by nra.
    assert (u <= / 1000000) by (rewrite Huv; lra). nra. }
  assert (HAll : List.Forall2 (ok A (rndF (asr / (2 * TAU)))) nodes dats) by exact Hall.
  assert (Hshift : Rabs (asin rho) <= A - 1 / 10 ^ 4) by exact Hrng.
  assert (HgS : A / (4 * PI) * sumD (gdat A B0) dats <= E) by (rewrite (sumD_gcl A B0 dats Hbr); exact Hsum).
  assert (Hsd : bpow radix2 (kA - 54) <= bpow radix2 (kA - 54)) by lra.
  pose proof (low_branch expI sinI x y rho asr A Tr B0 E kA pxI pyI Phix Phiy nodes dats Hexp Hsin Fx Fy Hx Hy HPx HPy Fpx Fpy Hpx Hpy Epx Epy
    (ex_intro _ Za (conj Eas HZa)) Hasr1 Hasr2 HA1 Hshift HAk Hk1 Hk2 HB00 HB0q HAll Hlen HgS HE1 Hprob HT1) as Hb.
  lra.
Qed.
