(** Real-valued Q256 contracts, including zero operands. *)
From Coq Require Import Reals ZArith Lia Lra Psatz Bool List.
From Flocq Require Import Core.
Require Import QSpec Q256 Q128Mul Limbs LimbScan.
Import ListNotations.
Open Scope R_scope.

Definition valid (x : q256) :=
  ok4 (m x) /\ ((v (m x)=0)%Z \/ normalized 256 (v (m x))).

Lemma zero_valid : valid zero.
Proof. split; [apply ok4_zero | left; reflexivity]. Qed.

Lemma qval_zero x : (v (m x)=0)%Z -> qval x=0.
Proof. intros Z. unfold qval. rewrite Z. apply val_zero. Qed.

Lemma mag_abs x : ok4 (m x) -> mag x=Rabs (qval x).
Proof.
  intros [O L]. unfold mag,qval. rewrite val_abs by (apply v_nonneg; exact O).
  reflexivity.
Qed.

Lemma new_valid n limbs exponent : ok4 limbs -> valid (new n limbs exponent).
Proof.
  intros O. destruct (new_ok n limbs exponent O) as [N E].
  pose proof (norm_ok 256 ltac:(lia) (v limbs) exponent (v4_bound limbs O)) as V.
  destruct (norm 256 (v limbs) exponent) as [m' e']. injection E as Em Ee.
  split; [exact N | ]. rewrite Em.
  destruct V as [[[_ Z] | Normal] _]; [left; exact Z | right; exact Normal].
Qed.

Lemma from_f64_valid bits : valid (from_f64 bits).
Proof.
  unfold from_f64. cbv zeta.
  assert (Mask : Z.land bits (2^52-1)=(bits mod 2^52)%Z).
  { rewrite <- Z.land_ones by lia. reflexivity. }
  rewrite Mask. set (f := (bits mod 2^52)%Z).
  assert (F : (0<=f<2^52)%Z) by (apply Z.mod_pos_bound; lia).
  assert (Or : Z.lor f (2^52)=(f+2^52)%Z).
  { replace (2^52)%Z with (Z.shiftl 1 52) at 1 by reflexivity.
    rewrite lor_disjoint_low by lia. ring. }
  rewrite Or.
  assert (Ok : forall s, (0<=s<2^53)%Z -> ok4 [s;0%Z;0%Z;0%Z]).
  { intros s S. split; [repeat constructor; unfold Limbs.B; lia | reflexivity]. }
  destruct (Z.land (Z.shiftr bits 52) 2047 =? 0)%Z;
    apply new_valid, Ok; lia.
Qed.

Theorem neg_any x : valid x -> valid (neg_q x) /\ qval (neg_q x)= -qval x.
Proof.
  intros [O N]. split; [ | apply neg_ok; exact O].
  unfold neg_q. destruct (is_zero (m x)); [split; assumption | ].
  split; assumption.
Qed.

Theorem add_any a b : valid a -> valid b ->
  valid (add a b) /\
  Rabs (qval (add a b)-(qval a+qval b))<=
    bpow radix2 (-254)*Rmax (Rabs (qval a)) (Rabs (qval b)).
Proof.
  intros [Oa Na] [Ob Nb].
  destruct (Z.eq_dec (v (m a)) 0) as [Za | Za].
  { unfold add. rewrite is_zero_ok by apply Oa. rewrite Za. cbn [Z.eqb].
    split; [split; assumption | ]. rewrite (qval_zero a Za), Rplus_0_l, Rminus_diag_eq, Rabs_R0 by reflexivity.
    apply Rmult_le_pos; [apply bpow_ge_0 | ].
    eapply Rle_trans; [apply Rabs_pos | apply Rmax_r]. }
  destruct (Z.eq_dec (v (m b)) 0) as [Zb | Zb].
  { unfold add. rewrite !is_zero_ok by (apply Oa || apply Ob).
    rewrite Zb. replace (v (m a)=?0)%Z with false by (symmetry; apply Z.eqb_neq; exact Za).
    cbn [Z.eqb]. split; [split; assumption | ].
    rewrite (qval_zero b Zb), Rplus_0_r, Rminus_diag_eq, Rabs_R0 by reflexivity.
    apply Rmult_le_pos; [apply bpow_ge_0 | ].
    eapply Rle_trans; [apply Rabs_pos | apply Rmax_l]. }
  destruct Na as [Na | Na]; [contradiction | ].
  destruct Nb as [Nb | Nb]; [contradiction | ].
  destruct (add_ok a b Oa Ob Na Nb) as [O [N E]].
  split; [split; assumption | ]. rewrite <- !mag_abs by assumption. exact E.
Qed.

Theorem mul_any a b : valid a -> valid b ->
  valid (mul a b) /\
  Rabs (qval (mul a b)-qval a*qval b)<=bpow radix2 (-255)*Rabs (qval a*qval b).
Proof.
  intros [Oa Na] [Ob Nb].
  destruct (Z.eq_dec (v (m a)) 0) as [Za | Za].
  { assert (M : mul a b=zero).
    { unfold mul. rewrite is_zero_ok by apply Oa. rewrite Za. reflexivity. }
    rewrite M. split; [apply zero_valid | ].
    rewrite (qval_zero a Za), (qval_zero zero eq_refl).
    rewrite !Rmult_0_l, Rminus_diag_eq, Rabs_R0, Rmult_0_r by reflexivity. lra. }
  destruct (Z.eq_dec (v (m b)) 0) as [Zb | Zb].
  { assert (M : mul a b=zero).
    { unfold mul. rewrite (is_zero_ok (m b)) by apply Ob. rewrite Zb, orb_true_r. reflexivity. }
    rewrite M. split; [apply zero_valid | ].
    rewrite (qval_zero b Zb), (qval_zero zero eq_refl).
    rewrite !Rmult_0_r, Rminus_diag_eq, Rabs_R0, Rmult_0_r by reflexivity. lra. }
  destruct Na as [Na | Na]; [contradiction | ].
  destruct Nb as [Nb | Nb]; [contradiction | ].
  destruct (mul_value a b Oa Ob Na Nb) as [O [N E]].
  split; [split; [exact O | right; exact N] | ].
  pose proof (Rabs_le_inv (qval a*qval b) (Rabs (qval a*qval b)) (Rle_refl _)) as P.
  pose proof (bpow_ge_0 radix2 (-255)) as Upos.
  destruct E as [[L U] | [L U]]; apply Rabs_le; split; nra.
Qed.

Theorem mul_relative a b : valid a -> valid b ->
  valid (mul a b) /\ exists d, Rabs d<=bpow radix2 (-255) /\
    qval (mul a b)=qval a*qval b*(1+d).
Proof.
  intros A B. destruct (mul_any a b A B) as [V E]. split; [exact V | ].
  set (p := qval a*qval b) in *.
  destruct (Req_dec p 0) as [P | P].
  - exists 0. rewrite P in E |- *.
    rewrite Rabs_R0,Rmult_0_r,Rminus_0_r in E.
    split; [rewrite Rabs_R0; apply bpow_ge_0 | ].
    pose proof (Rabs_le_inv _ _ E). lra.
  - exists ((qval (mul a b)-p)/p). split.
    + unfold Rdiv. rewrite Rabs_mult,Rabs_Rinv by exact P.
      assert (Abs : 0<Rabs p) by (apply Rabs_pos_lt; exact P).
      apply (Rmult_le_reg_r (Rabs p)); [exact Abs | ].
      rewrite Rmult_assoc,Rinv_l,Rmult_1_r by lra. exact E.
    + field. exact P.
Qed.
