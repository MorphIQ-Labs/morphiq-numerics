(** The branch bound for a rule, from the rule's correlation limit [L]: the
    angle of every [|rho| <= L] is below [A], so the rule's data apply. *)
From Coq Require Import Reals ZArith Lia Lra List.
Import ListNotations.
From Flocq Require Import Core.
From Double Require Import DWPlus.
From Binary64 Require Import Binary64Add.
From Interval Require Import Tactic.
From Coquelicot Require Import Coquelicot.
Require Import BvnRound BvnArg BvnNode BvnTrig BvnLow BvnSum BvnChain BvnQuadG BvnRule BvnTail BvnIntegral BvnTop.
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

(** The multiplicative constant of one term: weight, [exp], product, sum,
    the constant [asr / (2 TAU)] and its multiplication, as an upper bound
    of [(1 + psi) (1 + u)^3 exp z - 1]. *)
Definition B0 : R := 73 / 10 ^ 17.

Lemma B0_ok : 0 <= B0 /\ bq ETAK <= B0.
Proof.
  split; [unfold B0; lra |].
  unfold bq, psi, ETAK, u, z. simpl. interval with (i_prec 120).
Qed.

Theorem low_rule (x y rho asr L A Tr E T S Bd Phix Phiy : R) (kA : Z) (nodes : list NodeS) (dats : list Dat) :
  L + 2 / 10 ^ 4 <= sin A -> 0 <= A -> A <= 6 / 5 -> (-1021 <= kA)%Z -> (kA <= 1)%Z ->
  A <= bpow radix2 kA ->
  List.Forall (dat_ok A) dats -> List.Forall (br_ok A B0) dats ->
  A / (4 * PI) * sumD (gcl A B0) dats <= E ->
  Tr / (2 * PI) <= T -> bpow radix2 (kA - 54) / (2 * PI) <= S ->
  4 * bpow radix2 (-54) + E + 1000 * z + T + S <= Bd ->
  Rabs rho <= L -> bpow radix2 (-52) <= Rabs rho ->
  dom x -> dom y -> 0 <= Phix <= 1 -> 0 <= Phiy <= 1 -> asr = rndF (asin rho) ->
  List.Forall2 node_enc nodes dats -> (length nodes <= 24)%nat ->
  0 <= Phix * Phiy + Iint (x * x + y * y) (x * y) (asin rho) / (2 * PI) <= 1 ->
  Rabs (Iint (x * x + y * y) (x * y) asr - asr / 2 * sumR (map (vn x y asr) nodes)) <= Tr ->
  Rabs (Rhat x y asr nodes Phix Phiy - (Phix * Phiy + Iint (x * x + y * y) (x * y) (asin rho) / (2 * PI)))
    <= Bd.
Proof.
  intros HL HA0 HA1 Hk1 Hk2 HAk Hdat Hbr Hsum HT HS HBd Hrho Hrlow Hx Hy HPx HPy Hasr Hnodes Hlen Hprob HT1.
  pose proof u_pos as Hu. pose proof u_val as Huv. pose proof z_pos as Hz.
  destruct B0_ok as [HB00 HB0q].
  assert (Hasin : Rabs (asin rho) <= A - 1 / 10 ^ 4) by (apply (asin_le_A rho L A); lra).
  assert (Hshift : Rabs (asin rho - asr) <= bpow radix2 (kA - 54)).
  { rewrite Hasr, Rabs_minus_sym. apply rnd_pow; [exact Hk1 | lra]. }
  assert (Hsh53 : bpow radix2 (kA - 54) <= bpow radix2 (-53)) by (apply bpow_le; lia).
  assert (Hasr1 : Rabs asr <= A).
  { assert (Eq0 : asr = asin rho + (asr - asin rho)) by ring.
    assert (Rabs asr <= Rabs (asin rho) + Rabs (asr - asin rho)) by (rewrite Eq0 at 1; apply Rabs_triang).
    rewrite Rabs_minus_sym in H. fold u in Huv. assert (bpow radix2 (-53) = u) by reflexivity.
    assert (u <= 1 / 10 ^ 4) by (rewrite Huv; lra). lra. }
  assert (Hasr2 : bpow radix2 (-53) <= Rabs asr).
  { assert (Hge : bpow radix2 (-52) <= Rabs (asin rho)).
    { assert (Hs : Rabs (sin (asin rho) - sin 0) <= Rabs (asin rho - 0)) by apply sin_lip.
      rewrite sin_0 in Hs. rewrite Rminus_0_r in Hs. rewrite Rminus_0_r in Hs.
      assert (Hrr : -1 <= rho <= 1).
      { apply Rabs_le_between. assert (sin A <= 1) by (pose proof (SIN_bound A) as [_ H]; exact H). lra. }
      rewrite (sin_asin rho Hrr) in Hs. lra. }
    pose proof (rnd_rel_z (asin rho)) as Hr. rewrite <- Hasr in Hr.
    assert (Hb52 : bpow radix2 (-52) = 2 * bpow radix2 (-53)).
    { replace (-52)%Z with (-53 + 1)%Z by reflexivity. rewrite bpow_plus. change (bpow radix2 1) with 2. ring. }
    assert (Hz' : z <= bpow radix2 (-53) / 4).
    { unfold z. assert (bpow radix2 (-1075) <= bpow radix2 (-55)) by (apply bpow_le; lia).
      assert (bpow radix2 (-53) = 4 * bpow radix2 (-55)) by (replace (-53)%Z with (-55 + 2)%Z by reflexivity; rewrite bpow_plus; replace (bpow radix2 2) with 4 by reflexivity; ring).
      lra. }
    assert (Hu1 : u * Rabs (asin rho) <= Rabs (asin rho) / 4) by (rewrite Huv; pose proof (Rabs_pos (asin rho)); nra).
    assert (Eq0 : asin rho = asr - (asr - asin rho)) by ring.
    assert (Rabs (asin rho) <= Rabs asr + Rabs (asr - asin rho)) by (rewrite Eq0 at 1; eapply Rle_trans; [apply Rabs_triang |]; rewrite Rabs_Ropp; lra).
    assert (bpow radix2 (-53) = u) by reflexivity.
    pose proof (bpow_gt_0 radix2 (-53)). nra. }
  assert (Hask : Rabs (asin rho) <= bpow radix2 kA) by lra.
  assert (Hasin32 : Rabs (asin rho) <= 3 / 2) by lra.
  assert (HAll : List.Forall2 (node_ok asr A) nodes dats) by (apply Forall2_node_ok; assumption).
  pose proof (low_branch x y rho asr A Tr B0 kA Phix Phiy nodes dats HB00 HB0q Hk1 Hask Hx Hy HPx HPy Hasr Hasr2 Hasr1 HA1 Hasin32 HAll Hlen Hprob HT1) as Hb.
  pose proof (sumD_gcl A B0 dats Hbr) as Hg.
  assert (Hm : A / (4 * PI) * sumD (gdat A B0) dats <= E) by (rewrite Hg; exact Hsum).
  eapply Rle_trans; [exact Hb |]. lra.
Qed.
