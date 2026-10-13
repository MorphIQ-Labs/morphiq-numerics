(** Q256 arithmetic for one Taylor coefficient recurrence step. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Q Require Import Q256 Q256Real.
Require Import StageGappa ErfcxAccurateConstants.
Open Scope R_scope.
Definition q_taylor_step c prev cur k :=
  let p:=mul c cur in mul (add (add p p) (add prev prev)) (q_reciprocal k).

Lemma q_add_magnitude a b ma mb : valid a -> valid b ->
  Rabs(qval a)<=ma -> Rabs(qval b)<=mb ->
  valid(add a b) /\ Rabs(qval(add a b)-(qval a+qval b))<=bpow radix2 (-254)*Rmax ma mb /\
  Rabs(qval(add a b))<=ma+mb+bpow radix2 (-254)*Rmax ma mb.
Proof.
  intros A B Ma Mb. destruct(add_any a b A B) as [V E].
  assert (Err : Rabs(qval(add a b)-(qval a+qval b))<=bpow radix2 (-254)*Rmax ma mb).
  { eapply Rle_trans; [exact E|]. apply Rmult_le_compat_l; [apply bpow_ge_0|].
    apply Rmax_lub.
    - eapply Rle_trans; [exact Ma|apply Rmax_l].
    - eapply Rle_trans; [exact Mb|apply Rmax_r]. }
  split; [exact V|]. split; [exact Err|].
  replace (qval(add a b)) with ((qval(add a b)-(qval a+qval b))+(qval a+qval b)) by ring.
  eapply Rle_trans; [apply Rabs_triang|]. pose proof(Rabs_triang (qval a) (qval b)); lra.
Qed.
Lemma q_mul_magnitude a b ma mb : valid a -> valid b ->
  Rabs(qval a)<=ma -> Rabs(qval b)<=mb ->
  valid(mul a b) /\ Rabs(qval(mul a b)-qval a*qval b)<=bpow radix2 (-255)*ma*mb /\
  Rabs(qval(mul a b))<=ma*mb*(1+bpow radix2 (-255)).
Proof.
  intros A B Ma Mb. destruct(mul_any a b A B) as [V E].
  assert (Prod : Rabs(qval a*qval b)<=ma*mb).
  { rewrite Rabs_mult. apply Rmult_le_compat; [apply Rabs_pos|apply Rabs_pos|exact Ma|exact Mb]. }
  assert (Err : Rabs(qval(mul a b)-qval a*qval b)<=bpow radix2 (-255)*ma*mb).
  { eapply Rle_trans; [exact E|]. rewrite Rmult_assoc. apply Rmult_le_compat_l; [apply bpow_ge_0|exact Prod]. }
  split; [exact V|]. split; [exact Err|].
  replace (qval(mul a b)) with ((qval(mul a b)-qval a*qval b)+qval a*qval b) by ring.
  eapply Rle_trans; [apply Rabs_triang|]. nra.
Qed.

Theorem q_taylor_step_error c prev cur k : valid c -> valid prev -> valid cur ->
  Rabs(qval c)<=16 -> Rabs(qval prev)<=bpow radix2 68 -> Rabs(qval cur)<=bpow radix2 68 ->
  (1<=k<99)%nat ->
  valid(q_taylor_step c prev cur k) /\
  Rabs(qval(q_taylor_step c prev cur k)-
    (2*qval c*qval cur+2*qval prev)/INR(S k))<=bpow radix2 (-176).
Proof.
  intros C Prev Cur Cr Pr Ur K.
  destruct(q_mul_magnitude c cur 16 (bpow radix2 68) C Cur Cr Ur) as [P [Pe Pm]].
  assert (Pm' : Rabs(qval(mul c cur))<=bpow radix2 73).
  { eapply Rle_trans; [exact Pm|]. bpow_num; lra. }
  destruct(q_add_magnitude _ _ _ _ P P Pm' Pm') as [PP [PPe PPm]].
  rewrite Rmax_left in PPe,PPm by lra.
  assert (PPm' : Rabs(qval(add (mul c cur) (mul c cur)))<=bpow radix2 75).
  { eapply Rle_trans; [exact PPm|]. bpow_num; lra. }
  destruct(q_add_magnitude _ _ _ _ Prev Prev Pr Pr) as [Prev2 [Prev2e Prev2m]].
  rewrite Rmax_left in Prev2e,Prev2m by lra.
  assert (Prev2m' : Rabs(qval(add prev prev))<=bpow radix2 70).
  { eapply Rle_trans; [exact Prev2m|]. bpow_num; lra. }
  destruct(q_add_magnitude _ _ _ _ PP Prev2 PPm' Prev2m') as [Sum [Se Sm]].
  rewrite Rmax_left in Se,Sm by (apply bpow_le;lia).
  assert (Sm' : Rabs(qval(add (add (mul c cur)(mul c cur))(add prev prev)))<=bpow radix2 77).
  { eapply Rle_trans; [exact Sm|]. bpow_num; lra. }
  destruct(q_reciprocal_ok k ltac:(lia)) as [Rec Re].
  set (d:=INR(S k)) in *.
  assert (D : 2<=d) by (unfold d; change 2 with (INR 2); apply le_INR;lia).
  assert (Dr : 0</d<=/2).
  { split; [apply Rinv_0_lt_compat;lra|apply Rinv_le_contravar;lra]. }
  assert (Rm : Rabs(qval(q_reciprocal k))<=1).
  { apply Rabs_le_inv in Re. bpow_num_all. apply Rabs_le; split; nra. }
  destruct(q_mul_magnitude _ _ _ _ Sum Rec Sm' Rm) as [Result [FinalError FinalMagnitude]].
  unfold q_taylor_step. split; [exact Result|].
  set (s:=qval(add (add (mul c cur)(mul c cur))(add prev prev))) in *.
  set (p:=qval(mul c cur)) in *.
  set (pp:=qval(add (mul c cur)(mul c cur))) in *.
  set (pv:=qval(add prev prev)) in *.
  set (r:=qval(q_reciprocal k)) in *.
  assert (SumError : Rabs(s-(2*qval c*qval cur+2*qval prev))<=bpow radix2 (-177)).
  { replace (s-(2*qval c*qval cur+2*qval prev)) with
      ((s-(pp+pv))+(pp-(p+p))+(pv-(qval prev+qval prev))+2*(p-qval c*qval cur)) by (unfold s,pp,pv,p;ring).
    eapply Rle_trans; [apply Rabs_triang|].
    pose proof(Rabs_triang (s-(pp+pv)) (pp-(p+p))) as A.
    pose proof(Rabs_triang ((s-(pp+pv))+(pp-(p+p))) (pv-(qval prev+qval prev))) as B.
    rewrite Rabs_mult,(Rabs_pos_eq 2) by lra.
    bpow_num_all. lra. }
  assert (Rerror : Rabs(r-/d)<=bpow radix2 (-255)/2).
  { replace (r-/d) with ((r*d-1)*(/d)) by (field;lra).
    rewrite Rabs_mult,(Rabs_pos_eq(/d)) by lra.
    eapply Rle_trans; [apply Rmult_le_compat; [apply Rabs_pos|lra|exact Re|exact (proj2 Dr)]|].
    unfold Rdiv;right;ring. }
  replace (qval(mul (add (add (mul c cur)(mul c cur))(add prev prev)) (q_reciprocal k))-
    (2*qval c*qval cur+2*qval prev)/d) with
    ((qval(mul (add (add (mul c cur)(mul c cur))(add prev prev)) (q_reciprocal k))-s*r)+
     s*(r-/d)+(s-(2*qval c*qval cur+2*qval prev))*(/d)) by (unfold Rdiv;ring).
  eapply Rle_trans; [apply Rabs_triang|].
  pose proof(Rabs_triang
    (qval(mul (add (add (mul c cur)(mul c cur))(add prev prev)) (q_reciprocal k))-s*r)
    (s*(r-/d))) as AddError.
  rewrite !Rabs_mult,(Rabs_pos_eq(/d)) by lra.
  rewrite Rabs_mult in AddError.
  assert (RE : Rabs s*Rabs(r-/d)<=bpow radix2 77*(bpow radix2 (-255)/2))
    by (apply Rmult_le_compat; [apply Rabs_pos|apply Rabs_pos|exact Sm'|exact Rerror]).
  assert (SE : Rabs(s-(2*qval c*qval cur+2*qval prev))*(/d)<=bpow radix2 (-177)/2).
  { replace (bpow radix2 (-177)/2) with (bpow radix2 (-177)*(/2)) by reflexivity.
    apply Rmult_le_compat; [apply Rabs_pos|lra|exact SumError|exact(proj2 Dr)]. }
  bpow_num_all. lra.
Qed.
