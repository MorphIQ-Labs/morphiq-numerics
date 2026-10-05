(** The error-free transforms in IEEE 754 binary64 arithmetic: exact, and no
    operation overflows, on operands bounded as stated. *)

From Coq Require Import Reals ZArith Lia Lra.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Double Require Import DWPlus F2Sum F2SumFLX.
From Binary64 Require Import Binary64Add Binary64Mul IEEE64 IEEE64Add IEEE64Mul.
Require TwoProdBinary64.

Open Scope R_scope.

Lemma bnd_of_pow E v : Rabs v <= bpow radix2 E -> bnd 1 E v.
Proof. unfold bnd. lra. Qed.

(** 2Sum: [s = RN(a + b)] and [s + t = a + b] when [|a|, |b| <= 2^1020]. *)
Theorem two_sum_ieee a b : finite a -> finite b ->
  Rabs (B a) <= bpow radix2 1020 -> Rabs (B b) <= bpow radix2 1020 ->
  let '(s, t) := two_sum64 a b in
  finite s /\ finite t /\ B s = rndF (B a + B b) /\ B s + B t = B a + B b.
Proof.
  intros Fa Fb Ba Bb.
  destruct (two_sum64_ok 1 1020 a b Fa Fb (bnd_of_pow _ _ Ba) (bnd_of_pow _ _ Bb)
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [Fs [Ft [E _]]].
  rewrite (two_sum_eq _ _ (B_fmt a) (B_fmt b)) in E.
  destruct (two_sum64 a b) as [s t]. cbn [fst snd] in *.
  injection E as Es Et.
  repeat split; try assumption.
  - rewrite Es. unfold TwoSum_sum, TwoSum. simpl. now rewrite <- sum_round by apply B_fmt.
  - rewrite Es, Et, (@TwoSum_correct prec (ltac:(unfold prec; lia)) ne eq_refl (B a) (B b)
                       (fmtF_fmtX _ (B_fmt a)) (fmtF_fmtX _ (B_fmt b))). ring.
Qed.

(** Fast2Sum: exact when [a = 0], [|b| <= |a|], or [b]'s exponent is at most
    [a]'s, with [|a|, |b| <= 2^1021]. *)
Theorem fast_two_sum_ieee a b : finite a -> finite b ->
  Rabs (B a) <= bpow radix2 1021 -> Rabs (B b) <= bpow radix2 1021 ->
  (B a = 0 \/ Rabs (B b) <= Rabs (B a)
   \/ (cexp radix2 (FLX_exp prec) (B b) <= cexp radix2 (FLX_exp prec) (B a))%Z) ->
  let '(s, t) := fast_two_sum64 a b in
  finite s /\ finite t /\ B s = rndF (B a + B b) /\ B s + B t = B a + B b.
Proof.
  intros Fa Fb Ba Bb Pre.
  destruct (fast_two_sum64_ok 1 1021 a b Fa Fb (bnd_of_pow _ _ Ba) (bnd_of_pow _ _ Bb)
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [Fs [Ft [E _]]].
  rewrite (fast_two_sum_eq _ _ (B_fmt a) (B_fmt b)) in E.
  assert (Opp : forall x, rndX (- x) = - rndX x).
  { intros x. assert (Hne : ne = fun n => negb (Z.even n)) by reflexivity.
    rewrite Hne. apply round_NE_opp. }
  assert (C : Fast2Sum_correct radix2 prec ne (B a) (B b)).
  { destruct Pre as [P | [P | P]].
    - (* a = 0: s = b, then z = b and t = 0. *)
      unfold Fast2Sum_correct, F2SumFLX.Fast2Sum. cbv zeta. cbn [fst snd]. rewrite P.
      rewrite Rplus_0_l, Rminus_0_r.
      assert (Rb : rndX (B b) = B b) by (apply round_generic; auto with typeclass_instances; apply fmtF_fmtX, B_fmt).
      rewrite !Rb.
      replace (B b - B b) with 0 by ring.
      rewrite (round_0 radix2 (FLX_exp prec) (Znearest ne)). ring.
    - apply F2Sum_correct_abs; auto; [unfold prec; lia | | apply fmtF_fmtX, B_fmt | apply fmtF_fmtX, B_fmt].
      simpl; lia.
    - apply F2Sum_correct_cexp; auto; [unfold prec; lia | | apply fmtF_fmtX, B_fmt | apply fmtF_fmtX, B_fmt].
      simpl; lia. }
  unfold Fast2Sum_correct in C. cbv zeta in C.
  unfold F2Sum.Fast2Sum in E.
  destruct (fast_two_sum64 a b) as [s t]. cbn [fst snd] in Fs, Ft, E |- *.
  injection E as Es Et.
  repeat split; try assumption.
  - rewrite Es. simpl. now rewrite <- sum_round by apply B_fmt.
  - rewrite Es, Et. unfold F2SumFLX.Fast2Sum in C. cbn [fst snd] in C. lra.
Qed.

(** Dekker's product: [p = RN(a b)] and [p + e = a b] when [|a| <= 2^Ea],
    [|b| <= 2^Eb], [Ea, Eb <= 994], [Ea + Eb <= 1020], and [a b] is zero or at
    least [2^-969] in magnitude. *)
Theorem two_prod_ieee Ea Eb a b : finite a -> finite b ->
  Rabs (B a) <= bpow radix2 Ea -> Rabs (B b) <= bpow radix2 Eb ->
  (-537 <= Ea <= 994)%Z -> (-537 <= Eb <= 994)%Z -> (Ea + Eb <= 1020)%Z ->
  in_two_prod_domain (B a) (B b) ->
  let '(p, e) := two_prod64 a b in
  finite p /\ finite e /\ B p = rndF (B a * B b) /\ B p + B e = B a * B b.
Proof.
  intros Fa Fb Ba Bb Ha Hb Hab D.
  destruct (two_prod64_ok Ea Eb a b Fa Fb (bnd_of_pow _ _ Ba) (bnd_of_pow _ _ Bb) Ha Hb Hab)
    as [Fp [Fe [E _]]].
  pose proof (TwoProdBinary64.two_prod_exact (B a) (B b) (B_fmt a) (B_fmt b) D) as X.
  unfold two_prod in E.
  destruct (two_prod64 a b) as [p e]. cbn [fst snd] in *.
  injection E as Ep Ee.
  repeat split; try assumption.
  rewrite X. lra.
Qed.
