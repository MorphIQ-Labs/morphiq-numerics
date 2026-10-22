(** asinh's accurate path, the Newton step [y + (x - sinh y)/cosh y] in [Q256]:
    the scaled reciprocal, [sinh] and [cosh] from [e^y] and [e^-y], and the
    step's error against [arcsinh]. *)
From Coq Require Import Reals ZArith Lia Lra Psatz List.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Q Require Import Q256 Q256Real QSpec Limbs LimbScan.
Require Import Ln1pLemmas AsinTables AsinKernel AsinQSeries AsinRecip AsinhTables AsinhKernel AsinhWithin AsinhExp AsinhExpRed AsinhRecip.
Open Scope R_scope.

Lemma top_bounds c : Q256Real.valid c -> 0 < qval c -> bpow radix2 (Q256Real.top c) <= qval c < bpow radix2 (Q256Real.top c + 1).
Proof.
  intros [O N] Pos. unfold Q256Real.top. rewrite is_zero_ok by apply O.
  destruct (Z.eqb_spec (v (m c)) 0) as [Z | Z].
  - exfalso. rewrite (qval_zero c Z) in Pos. lra.
  - destruct N as [N | N]; [contradiction | ].
    pose proof (mag_bounds c N) as [Low High]. rewrite mag_abs in Low, High by exact O.
    rewrite (Rabs_pos_eq (qval c)) in Low, High by lra.
    replace (e c + 255 + 1)%Z with (e c + 256)%Z by ring. split; assumption.
Qed.

(** [asinh_recip c] is [1/c] to [2^-252], for a positive valid [c]. *)
Theorem asinh_recip_ok c : Q256Real.valid c -> 0 < qval c ->
  Q256Real.valid (asinh_recip c) /\ 0 < qval (asinh_recip c) /\ Rabs (qval c * qval (asinh_recip c) - 1) <= bpow radix2 (-252).
Proof.
  intros Vc Pos. unfold asinh_recip.
  set (tp := Q256Real.top c) in *.
  destruct (top_bounds c Vc Pos) as [Lo Hi].
  change (Q256Real.top c) with tp in Lo, Hi.
  destruct (mul_pow2_any c (- tp) Vc) as [V1 Q1].
  set (c1 := Q256Real.mul_pow2 c (- tp)) in *.
  assert (Hp : bpow radix2 tp * bpow radix2 (- tp) = 1) by (rewrite <- bpow_plus; replace (tp + - tp)%Z with 0%Z by ring; reflexivity).
  assert (Hp1 : bpow radix2 (tp + 1) * bpow radix2 (- tp) = 2) by (rewrite bpow_plus; change (bpow radix2 1) with 2; nra).
  assert (Pm : 0 < bpow radix2 (- tp)) by apply bpow_gt_0.
  assert (Hc1 : 1 <= qval c1 <= 2).
  { rewrite Q1. split.
    - assert (bpow radix2 tp * bpow radix2 (- tp) <= qval c * bpow radix2 (- tp)) by (apply Rmult_le_compat_r; lra). lra.
    - assert (qval c * bpow radix2 (- tp) <= bpow radix2 (tp + 1) * bpow radix2 (- tp)) by (apply Rmult_le_compat_r; lra). lra. }
  destruct (q_recip_ok2 c1 V1 Hc1) as [V2 [P2 E2]].
  destruct (mul_pow2_any (q_recip c1) (- tp) V2) as [V3 Q3].
  refine (conj V3 (conj _ _)).
  - rewrite Q3. apply Rmult_lt_0_compat; [exact P2 | exact Pm].
  - rewrite Q3. replace (qval c * (qval (q_recip c1) * bpow radix2 (- tp))) with (qval c1 * qval (q_recip c1)) by (rewrite Q1; ring).
    exact E2.
Qed.
