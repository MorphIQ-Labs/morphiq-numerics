(** Repeated Q256 residual multiplication, initialized with h itself. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Q Require Import Q256 Q256Real.
Require Import StageGappa ErfcxAccurateTaylorStep.
Open Scope R_scope.
Fixpoint q_taylor_power h n :=
  match n with O => h | S k => mul (q_taylor_power h k) h end.
Theorem q_taylor_power_error h n : valid h -> Rabs(qval h)<=/8 ->
  valid(q_taylor_power h n) /\ Rabs(qval(q_taylor_power h n))<=1 /\
  Rabs(qval(q_taylor_power h n)-(qval h)^S n)<=bpow radix2 (-255).
Proof.
  intros H Hr. induction n as [|n [P [Pm Pe]]].
  - cbn [q_taylor_power pow]. split; [exact H|]. split; [lra|].
    replace (qval h-qval h*1) with 0 by ring. rewrite Rabs_R0;apply bpow_ge_0.
  - destruct(q_mul_magnitude _ _ 1 (/8) P H Pm Hr) as [Result [Error Magnitude]].
    cbn [q_taylor_power]. split; [exact Result|]. split.
    + eapply Rle_trans; [exact Magnitude|]. bpow_num;lra.
    + replace ((qval h)^S(S n)) with ((qval h)^S n*qval h) by (cbn [pow];ring).
      replace (qval(mul(q_taylor_power h n)h)-(qval h)^S n*qval h) with
        ((qval(mul(q_taylor_power h n)h)-qval(q_taylor_power h n)*qval h)+
         (qval(q_taylor_power h n)-(qval h)^S n)*qval h) by ring.
      eapply Rle_trans; [apply Rabs_triang|]. rewrite Rabs_mult.
      assert (Propagate : Rabs(qval(q_taylor_power h n)-(qval h)^S n)*Rabs(qval h)<=bpow radix2 (-255)/8).
      { unfold Rdiv. apply Rmult_le_compat; [apply Rabs_pos|apply Rabs_pos|exact Pe|exact Hr]. }
      bpow_num_all;lra.
Qed.
