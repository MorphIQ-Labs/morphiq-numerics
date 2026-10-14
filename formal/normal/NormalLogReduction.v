(** Exact integer-exponent normalization for the accurate logarithm, and
    the magnitude comparison used by its early termination test. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Q Require Import QSpec Q256 Q256Real Limbs LimbScan.
Require Import StageGappa.
Open Scope R_scope.

Theorem normal_q_top_range x : valid x -> qval x<>0 ->
  bpow radix2(top x)<=Rabs(qval x)<bpow radix2(top x+1).
Proof.
  intros[O N] Nonzero.
  assert (NonzeroM : (v(m x)<>0)%Z)by(intros Zero;apply Nonzero,qval_zero,Zero).
  destruct N as[Zero|Normalized];[contradiction|].
  pose proof(mag_bounds x Normalized)as Bounds;rewrite mag_abs in Bounds by exact O.
  unfold top;rewrite is_zero_ok by apply O.
  rewrite (proj2(Z.eqb_neq _ _) NonzeroM);replace(e x+255+1)%Z with(e x+256)%Z by lia.
  exact Bounds.
Qed.

Definition normal_q_log_normalized x := mul_pow2 x (-top x).

Theorem normal_q_log_normalized_range x : valid x -> 0<qval x ->
  valid(normal_q_log_normalized x) /\ 1<=qval(normal_q_log_normalized x)<2 /\
  qval x=bpow radix2(top x)*qval(normal_q_log_normalized x).
Proof.
  intros X Positive;pose proof(normal_q_top_range x X ltac:(lra))as[Lower Upper].
  rewrite Rabs_pos_eq in Lower,Upper by lra.
  destruct(mul_pow2_any x (-top x) X)as[Result Value].
  assert (Inverse : bpow radix2(top x)*bpow radix2(-top x)=1).
  { rewrite <-bpow_plus;replace(top x+-top x)%Z with 0%Z by lia;reflexivity. }
  assert (Two : bpow radix2(top x+1)=2*bpow radix2(top x)).
  { rewrite bpow_plus;change(bpow radix2 1)with 2;ring. }
  unfold normal_q_log_normalized;split;[exact Result|]. rewrite Value.
  split.
  - split.
    + apply(Rmult_le_compat_r(bpow radix2(-top x)))in Lower;[nra|apply bpow_ge_0].
    + apply(Rmult_lt_compat_r(bpow radix2(-top x)))in Upper;[rewrite Two in Upper;nra|apply bpow_gt_0].
  - nra.
Qed.

Theorem normal_q_log_reduction_identity x : valid x -> 0<qval x ->
  ln(qval x)=IZR(top x)*ln 2+ln(qval(normal_q_log_normalized x)).
Proof.
  intros X Positive;destruct(normal_q_log_normalized_range x X Positive)as[_ [Range Value]].
  rewrite Value at 1;rewrite ln_mult by(try apply bpow_gt_0;lra).
  rewrite bpow_exp,ln_exp;reflexivity.
Qed.

Theorem normal_q_early_term_bound term sum : valid term -> valid sum -> qval sum<>0 ->
  (top term<top sum-270)%Z -> Rabs(qval term)<bpow radix2(-270)*Rabs(qval sum).
Proof.
  intros Term Sum Nonzero Early.
  pose proof(top_small term (top sum-270) Term Early)as Small.
  pose proof(normal_q_top_range sum Sum Nonzero)as[Lower _].
  replace(top sum-270)%Z with(top sum+(-270))%Z in Small by lia.
  rewrite bpow_plus in Small.
  eapply Rlt_le_trans;[exact Small|].
  rewrite Rmult_comm;apply Rmult_le_compat_l;[apply bpow_ge_0|exact Lower].
Qed.
