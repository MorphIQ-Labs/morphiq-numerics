(** The exact integer prefix and its absolute error before quadrant selection. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Binary64 Require Import IEEE64.
From Interval Require Import Tactic.
Require Import TrigConstants TrigSeparation TrigClosest TrigWindow.
Open Scope R_scope.

Lemma integer_prefix_enclosure a (n d : Z) :
  (0<d)%Z -> IZR n<a*IZR d<IZR n+1 ->
  IZR (n/d)<a<IZR (n/d)+1.
Proof.
  intros D [L H].
  pose proof (Z.div_mod n d ltac:(lia)) as E.
  pose proof (Z.mod_pos_bound n d D) as R.
  assert (Dr : 0<IZR d) by (apply IZR_lt; exact D).
  assert (R0 : 0<=IZR (n mod d)) by (apply IZR_le; lia).
  assert (R1 : IZR (n mod d)+1<=IZR d).
  { rewrite <- (plus_IZR (n mod d) 1). apply IZR_le; lia. }
  assert (Nr : IZR n=IZR d*IZR (n/d)+IZR (n mod d)).
  { rewrite <-mult_IZR,<-plus_IZR. f_equal; exact E. }
  split; apply Rmult_lt_reg_r with (IZR d); try exact Dr; nra.
Qed.

Theorem trig_prefix_bits e : (e<=1408)%Z ->
  let prefix := (trig_two_over_pi / 2^(1408-e))%Z in
  IZR prefix < bpow radix2 e*(2/PI) < IZR prefix+1.
Proof.
  intros E; cbv zeta.
  apply integer_prefix_enclosure.
  - apply Z.pow_pos_nonneg; lia.
  - exact (trig_scaled_table e E).
Qed.

Lemma scaled_prefix_error a p s m :
  0<s -> 0<m -> p<a*s<p+1 -> 0<m*a-m*p/s<m/s.
Proof.
  intros S M P.
  assert (D : (m*a-m*p/s)*s=m*(a*s-p)) by (field; lra).
  assert (C : (m/s)*s=m) by (field; lra).
  split; apply Rmult_lt_reg_r with s; try exact S.
  - rewrite D; nra.
  - rewrite D,C; nra.
Qed.

Definition trig_prefix_value (e m : Z) := IZR m*IZR (trig_prefix e)/2^315.

Theorem trig_prefix_error e m : (-53<=e<=971)%Z -> (0<m<2^53)%Z ->
  0 < (IZR m*bpow radix2 e)*(2/PI)-trig_prefix_value e m < /2^262.
Proof.
  intros E M. pose proof (trig_prefix_bits (e+315)%Z ltac:(lia)) as P.
  unfold trig_prefix_value,trig_prefix,trig_fraction_bits.
  cbv zeta in P. rewrite bpow_plus in P.
  assert (BP : bpow radix2 315=(2:R)^315) by (rewrite pow_IZR; reflexivity).
  rewrite BP in P.
  assert (Mr : 0<IZR m<2^53).
  { split; [apply IZR_lt; lia|]. rewrite pow_IZR. apply IZR_lt; lia. }
  assert (Scale : 0<(2:R)^315) by (apply pow_lt; lra).
  assert (Budget : (2:R)^53/2^315=/2^262) by field.
  assert (P' : IZR (trig_prefix e) < (bpow radix2 e*(2/PI))*2^315 <
      IZR (trig_prefix e)+1).
  { unfold trig_prefix,trig_fraction_bits. nra. }
  pose proof (scaled_prefix_error _ _ _ _ Scale (proj1 Mr) P') as T.
  unfold trig_prefix,trig_fraction_bits in T.
  replace ((IZR m*bpow radix2 e)*(2/PI))
    with (IZR m*(bpow radix2 e*(2/PI))) by ring.
  split; [exact (proj1 T)|]. apply Rlt_trans with (1:=proj2 T).
  rewrite <-Budget. unfold Rdiv. apply Rmult_lt_compat_r; [apply Rinv_0_lt_compat; exact Scale|exact (proj2 Mr)].
Qed.

Theorem trig_prefix_relative x e m k :
  finite x -> PI/4<=B x -> (-53<=e<=971)%Z -> (0<m<2^53)%Z ->
  B x=IZR m*bpow radix2 e ->
  Rabs (B x*(2/PI)-trig_prefix_value e m) <
    /2^200*Rabs (B x*(2/PI)-IZR k).
Proof.
  intros F X E M V. apply trig_truncation_relative; try assumption.
  rewrite V. pose proof (trig_prefix_error e m E M) as T.
  rewrite Rabs_pos_eq by lra; exact (proj2 T).
Qed.

(** Removing the table's high bits changes the scaled product by a multiple
    of four, so the selected low quadrant bits retain the full prefix. *)
Theorem trig_window_congruence e m : (-53<=e<=971)%Z -> (0<=m<2^53)%Z ->
  (m*trig_prefix e = Limbs.v (trig_product e m) +
    4*(m*(trig_prefix e / 2^317))*2^315)%Z.
Proof.
  intros E M. destruct (trig_product_exact e m E M) as [_ [_ V]]. rewrite V.
  pose proof (Z.div_mod (trig_prefix e) (2^317) ltac:(lia)) as D.
  rewrite D at 1. ring.
Qed.

(** The abstract nearest-integer decision is stable under the proved prefix
    truncation. Connecting the limb decision to its interval is separate. *)
Theorem trig_prefix_nearest x e m (k : Z) :
  finite x -> PI/4<=B x -> (-53<=e<=971)%Z -> (0<m<2^53)%Z ->
  B x=IZR m*bpow radix2 e ->
  -/2<=trig_prefix_value e m-IZR k</2 ->
  -/2<B x*(2/PI)-IZR k</2.
Proof.
  intros F X E M V Nearest.
  pose proof (trig_prefix_error e m E M) as T. rewrite <-V in T.
  pose proof (trig_binary64_half_separation x k F X) as Gap.
  assert (Budget : /2^262</2^63) by interval.
  split; [lra|]. destruct (Rlt_dec (B x*(2/PI)-IZR k) (/2)); [assumption|].
  rewrite Rabs_pos_eq in Gap by lra. lra.
Qed.
