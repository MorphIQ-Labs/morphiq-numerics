(** The integer decision interpreted at the full input scale. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Binary64 Require Import IEEE64.
From Q Require Import Limbs QSpec.
From Interval Require Import Tactic.
Require Import TrigConstants TrigWindow TrigWindowError TrigClosest TrigFraction.
Open Scope R_scope.

Definition trig_full_integer (e m : Z) :=
  (trig_nearest_integer (trig_product e m)+4*(m*(trig_prefix e/2^317)))%Z.
Definition trig_centered_integer (e m : Z) :=
  (v (trig_product e m)-trig_nearest_integer (trig_product e m)*2^315)%Z.

Theorem trig_centered_exact e m : (-53<=e<=971)%Z -> (0<m<2^53)%Z ->
  (m*trig_prefix e-trig_full_integer e m*2^315=trig_centered_integer e m)%Z /\
  fst (trig_select (trig_product e m))=(trig_full_integer e m mod 4)%Z /\
  (-2^314<=trig_centered_integer e m<2^314)%Z /\
  (if trig_negative (trig_fraction (trig_product e m))
   then -v (snd (trig_select (trig_product e m)))
   else v (snd (trig_select (trig_product e m))))%Z=trig_centered_integer e m.
Proof.
  intros E M. destruct (trig_product_exact e m E ltac:(lia)) as [O [L V]].
  destruct (trig_select_exact _ O L) as [K [_ [_ [S R]]]].
  pose proof (trig_window_congruence e m E ltac:(lia)) as W.
  unfold trig_full_integer,trig_centered_integer.
  split; [nia|]. split.
  - rewrite K. rewrite Z.mul_comm,Z.mod_add by lia; reflexivity.
  - split; assumption.
Qed.

Theorem trig_centered_real e m : (-53<=e<=971)%Z -> (0<m<2^53)%Z ->
  trig_prefix_value e m-IZR (trig_full_integer e m)=
    IZR (trig_centered_integer e m)/2^315.
Proof.
  intros E M. destruct (trig_centered_exact e m E M) as [I _].
  rewrite <-I,minus_IZR,!mult_IZR. unfold trig_prefix_value.
  assert (S : IZR (2^315)=(2:R)^315) by (rewrite pow_IZR; reflexivity).
  rewrite S. field.
Qed.

Lemma trig_center_interval z : (-2^314<=z<2^314)%Z ->
  -/2<=IZR z/2^315</2.
Proof.
  intros Z.
  assert (L : -(2:R)^314<=IZR z).
  { rewrite pow_IZR,<-opp_IZR. apply IZR_le; exact (proj1 Z). }
  assert (H : IZR z<(2:R)^314).
  { rewrite pow_IZR. apply IZR_lt; exact (proj2 Z). }
  assert (S : 0</(2:R)^315) by (apply Rinv_0_lt_compat; apply pow_lt; lra).
  assert (Half : (2:R)^314*/2^315=/2) by field.
  unfold Rdiv. split; nra.
Qed.

Theorem trig_centered_interval e m : (-53<=e<=971)%Z -> (0<m<2^53)%Z ->
  -/2<=trig_prefix_value e m-IZR (trig_full_integer e m)</2.
Proof.
  intros E M. rewrite trig_centered_real by assumption.
  apply trig_center_interval. exact (proj1 (proj2 (proj2 (trig_centered_exact e m E M)))).
Qed.

Theorem trig_centered_nearest x e m :
  finite x -> PI/4<=IEEE64.B x -> (-53<=e<=971)%Z -> (0<m<2^53)%Z ->
  IEEE64.B x=IZR m*bpow radix2 e ->
  -/2<IEEE64.B x*(2/PI)-IZR (trig_full_integer e m)</2.
Proof.
  intros F X E M V. apply (trig_prefix_nearest x e m); try assumption.
  apply trig_centered_interval; assumption.
Qed.

Theorem trig_centered_nonzero x e m :
  finite x -> PI/4<=IEEE64.B x -> (-53<=e<=971)%Z -> (0<m<2^53)%Z ->
  IEEE64.B x=IZR m*bpow radix2 e -> (trig_centered_integer e m<>0)%Z.
Proof.
  intros F X E M V Zero.
  pose proof (trig_binary64_separation x (trig_full_integer e m) F X) as Gap.
  pose proof (trig_prefix_error e m E M) as Err. rewrite <-V in Err.
  pose proof (trig_centered_real e m E M) as R. rewrite Zero in R.
  assert (R0 : trig_prefix_value e m=IZR (trig_full_integer e m)) by (simpl in R; lra).
  rewrite R0 in Err. rewrite Rabs_pos_eq in Gap by lra.
  assert (Small : /2^262</2^62) by interval. lra.
Qed.

Theorem trig_centered_input e m : (-53<=e<=971)%Z -> (0<m<2^53)%Z ->
  let p:=trig_product e m in
  val (trig_negative (trig_fraction p)) (v (snd (trig_select p))) (-315) =
    trig_prefix_value e m-IZR (trig_full_integer e m).
Proof.
  intros E M; cbv zeta.
  destruct (trig_centered_exact e m E M) as [_ [_ [_ S]]].
  unfold val,F2R; cbn [Fnum Fexp]. rewrite S.
  rewrite trig_centered_real by assumption.
  assert (Pow : bpow radix2 (-315)=/(2:R)^315).
  { rewrite pow_IZR; reflexivity. }
  rewrite Pow; reflexivity.
Qed.
