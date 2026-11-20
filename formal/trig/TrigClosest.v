(** Uniform separation from integer multiples of pi/2. Every exponent uses
    a checked rational witness, interpreted by the determinant-one lemma.
    The bound is conservative; the sampled nearest witness is not assumed. *)
From Coq Require Import Reals ZArith List Lia Lra Psatz.
From Flocq Require Import Core.
From Binary64 Require Import IEEE64 Encodings.
From Interval Require Import Tactic.
Require Import TrigSeparation TrigSeparationData.
Open Scope R_scope.

Theorem trig_integer_separation (e m k : Z) :
  (-53<=e<=972)%Z -> (0<m<2^53)%Z ->
  /2^62<=Rabs((IZR m*bpow radix2 e)*(2/PI)-IZR k).
Proof.
  intros E M.
  set (n:=Z.to_nat (e+53)).
  set (d:=witness 0 1 1 1).
  assert (N : (n<length trig_separation_witnesses)%nat).
  { rewrite trig_separation_count. unfold n.
    apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia. simpl; lia. }
  pose proof (separation_check_at (-53) trig_separation_witnesses n d
    trig_separation_checked N) as V.
  unfold n in V. rewrite Z2Nat.id in V by lia.
  replace (-53+(e+53))%Z with e in V by ring.
  replace ((IZR m*bpow radix2 e)*(2/PI)-IZR k)
    with ((bpow radix2 e*(2/PI))*IZR m-IZR k) by ring.
  exact (separation_check_sound e _ m k ltac:(lia) V M).
Qed.

Lemma trig_binary64_fields x : finite x -> PI/4<=B x ->
  exists m e, (0<m<2^53)%Z /\ (-53<=e<=971)%Z /\
    B x=IZR m*bpow radix2 e.
Proof.
  intros F X.
  assert (Half : /2<PI/4) by interval.
  assert (Normal : bpow radix2 (-1022)<=B x).
  { apply Rle_trans with (bpow radix2 (-1)); [apply bpow_le; lia|].
    change (/2<=B x); lra. }
  destruct (pos_normal x F Normal) as [m [e [Hx [_ [M [E [V _]]]]]]].
  assert (Low : (-53<=e)%Z).
  { destruct (Z_le_gt_dec (-53) e) as [Yes|No]; [exact Yes|].
    assert (Small : B x < bpow radix2 (e+53)).
    { rewrite V,bpow_plus,Rmult_comm. apply Rmult_lt_compat_l; [apply bpow_gt_0|].
      change (IZR (Zpos m)<IZR (2^53)). apply IZR_lt; lia. }
    assert (Upper : bpow radix2 (e+53)<=/2).
    { change (bpow radix2 (e+53)<=bpow radix2 (-1)). apply bpow_le; lia. }
    exfalso; lra. }
  exists (Zpos m),e. split; [lia|]. split; [lia|exact V].
Qed.

Theorem trig_binary64_separation x (k : Z) :
  finite x -> PI/4<=B x ->
  /2^62<=Rabs(B x*(2/PI)-IZR k).
Proof.
  intros F X. destruct (trig_binary64_fields x F X) as [m [e [M [E V]]]].
  rewrite V. apply trig_integer_separation; lia.
Qed.

(** The extra exponent in the witness table handles twice the largest
    binary64 input, separating the quadrant decision from a half-integer. *)
Theorem trig_binary64_half_separation x (k : Z) :
  finite x -> PI/4<=B x ->
  /2^63<=Rabs(B x*(2/PI)-(IZR k+/2)).
Proof.
  intros F X. destruct (trig_binary64_fields x F X) as [m [e [M [E V]]]].
  pose proof (trig_integer_separation (e+1)%Z m (2*k+1)%Z ltac:(lia) M) as Gap.
  rewrite bpow_plus in Gap. change (bpow radix2 1) with 2 in Gap.
  rewrite plus_IZR,mult_IZR in Gap.
  assert (Pi : 0<PI) by interval.
  replace ((IZR m*(bpow radix2 e*2))*(2/PI)-(IZR 2*IZR k+IZR 1))
    with (2*(B x*(2/PI)-(IZR k+/2))) in Gap by (rewrite V; field; lra).
  rewrite Rabs_mult,Rabs_pos_eq in Gap by lra.
  assert (Scale : /2^62=2*/2^63) by field.
  rewrite Scale in Gap; lra.
Qed.

(** Interface to the subsequent window proof: F=315 gives an absolute
    truncation budget below 2^(53-315). Its relative budget follows from
    the all-input separation theorem, not from a sampled closest approach. *)
Theorem trig_truncation_relative x (k : Z) t :
  finite x -> PI/4<=B x -> Rabs t < /2^262 ->
  Rabs t < /2^200*Rabs(B x*(2/PI)-IZR k).
Proof.
  intros F X T. pose proof (trig_binary64_separation x k F X) as Gap.
  apply Rlt_le_trans with (1:=T).
  replace (/2^262) with (/2^200*(/2^62)) by field.
  apply Rmult_le_compat_l; [left; interval|exact Gap].
Qed.
