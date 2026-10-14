(** End-to-end bound for the accurate logarithm series, including the
    remainder after the actual integer-exponent early termination test. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Q Require Import Q256 Q256Real Limbs LimbScan.
Require Import StageGappa NormalLogReduction NormalLogArgument NormalLogSeries
  NormalLogAnalytic.
Open Scope R_scope.

Lemma normal_q_log_sum_top sum : valid sum -> Rabs(qval sum)<=128 -> (top sum<=7)%Z.
Proof.
  intros S Range;destruct(Req_dec(qval sum)0)as[Zero|Nonzero].
  - unfold top;rewrite is_zero_ok by apply S.
    destruct(Z.eqb_spec(v(m sum))0)as[Z|NZ];[lia|].
    destruct S as[O [Z|N]];[contradiction|].
    pose proof(mag_bounds sum N)as[Lower _];rewrite mag_abs,Zero,Rabs_R0 in Lower by exact O.
    pose proof(bpow_gt_0 radix2(e sum+255));lra.
  - pose proof(normal_q_top_range sum S Nonzero)as[Lower _].
    apply(le_bpow radix2);change(bpow radix2 7)with 128;lra.
Qed.

Lemma normal_q_log_early_term term sum : valid term -> valid sum -> Rabs(qval sum)<=128 ->
  (top term<top sum-270)%Z -> Rabs(qval term)<bpow radix2 (-263).
Proof.
  intros T S Range Early;pose proof(normal_q_log_sum_top sum S Range).
  apply top_small;[exact T|lia].
Qed.

Lemma normal_log_stopped_remainder y n term sum : 1<=y<=2 -> (n<100)%nat ->
  valid term -> valid sum -> Rabs(qval sum)<=128 ->
  (top term<top sum-270)%Z ->
  Rabs(qval term-(normal_atanh_argument y)^(2*n+1)/(2*INR n+1))<=bpow radix2 (-245) ->
  Rabs(ln y-2*normal_atanh_series (S n)(normal_atanh_argument y))<=bpow radix2 (-237).
Proof.
  intros Y N Term Sum SumRange Early Error.
  pose proof(normal_q_log_early_term term sum Term Sum SumRange Early)as Small.
  destruct(normal_atanh_identity y Y)as[T _];set(t:=normal_atanh_argument y)in *.
  assert (Index : 0<=INR n<=100).
  { split;[apply pos_INR|replace 100 with(INR 100)by(simpl;ring);apply le_INR;lia]. }
  assert (Power : 0<=t^(2*n+1))by(apply pow_le;lra).
  assert (ExactTerm : 0<=t^(2*n+1)/(2*INR n+1)<=bpow radix2 (-244)).
  { split;[unfold Rdiv;apply Rmult_le_pos;[exact Power|left;apply Rinv_0_lt_compat;lra]|].
    apply Rabs_le_inv in Error;apply Rabs_lt_inv in Small.
    assert (Budget : bpow radix2 (-263)+bpow radix2 (-245)<=bpow radix2 (-244))by(interval with(i_prec 300));lra. }
  pose proof(normal_atanh_series_error (S n)y Y)as Remainder;fold t in Remainder.
  eapply Rle_trans;[exact Remainder|].
  assert (Next : t^(2*S n+1)=t^(2*n+1)*(t*t)).
  { replace(t*t)with(t^2)by(cbn;ring);rewrite <-pow_add;f_equal;lia. }
  rewrite Next.
  replace(2*(t^(2*n+1)*(t*t))/(1-t))with
    ((t^(2*n+1)/(2*INR n+1))*(2*(2*INR n+1)*t*t/(1-t)))by(field;split;lra).
  assert (Factor : 0<=2*(2*INR n+1)*t*t/(1-t)<=128)by(split;interval with(i_prec 80)).
  replace(bpow radix2 (-237))with(bpow radix2 (-244)*128)by(bpow_num;field).
  apply Rmult_le_compat;lra.
Qed.

Lemma normal_log_sum_final_error y n sum : (n<=100)%nat ->
  Rabs(qval sum-normal_atanh_series n(normal_atanh_argument y))<=INR n*bpow radix2 (-244) ->
  Rabs(ln y-2*normal_atanh_series n(normal_atanh_argument y))<=bpow radix2 (-237) ->
  Rabs(2*qval sum-ln y)<=bpow radix2 (-234).
Proof.
  intros N Sum Remainder.
  assert (Index : INR n<=100).
  { replace 100 with(INR 100)by(simpl;ring);apply le_INR;exact N. }
  replace(2*qval sum-ln y)with
    (2*(qval sum-normal_atanh_series n(normal_atanh_argument y))+
      -(ln y-2*normal_atanh_series n(normal_atanh_argument y)))by ring.
  eapply Rle_trans;[apply Rabs_triang|].
  rewrite Rabs_mult,Rabs_Ropp,(Rabs_pos_eq 2)by lra.
  assert (Budget : 200*bpow radix2 (-244)+bpow radix2 (-237)<=bpow radix2 (-234))by(interval with(i_prec 300)).
  pose proof(bpow_gt_0 radix2 (-244));nra.
Qed.

Theorem normal_q_log_loop_error fuel y n square power sum :
  1<=y<=2 -> (1<=n)%nat -> (n+fuel=100)%nat ->
  normal_log_state (normal_atanh_argument y) n power sum ->
  valid square -> Rabs(qval square-normal_atanh_argument y*normal_atanh_argument y)<=bpow radix2 (-248) ->
  valid(normal_q_log_loop fuel n square power sum) /\
  Rabs(2*qval(normal_q_log_loop fuel n square power sum)-ln y)<=bpow radix2 (-234).
Proof.
  revert n power sum;induction fuel as[|fuel IH];intros n power sum Y N Count State Square SquareError.
  - assert (Index : n=100%nat)by lia;subst n.
    destruct State as[_ [Sum [_ Error]]];cbn[normal_q_log_loop].
    split;[exact Sum|]. apply(normal_log_sum_final_error y 100 sum);try assumption;[lia|].
    eapply Rle_trans;[apply normal_atanh_series100_error;exact Y|apply bpow_le;lia].
  - destruct(normal_atanh_identity y Y)as[T _].
    pose proof(normal_q_log_series_step (normal_atanh_argument y)n power sum square T ltac:(lia)
      State Square SquareError)as[Next [Term TermError]].
    cbv zeta in Next,Term,TermError;cbn[normal_q_log_loop].
    destruct(Z.ltb(top(normal_q_log_term(mul power square)n))
      (top(add sum(normal_q_log_term(mul power square)n))-270))eqn:Early.
    + destruct Next as[P [Sum [Perror Serror]]];split;[exact Sum|].
      apply(normal_log_sum_final_error y (S n));try assumption;[lia|].
      apply(normal_log_stopped_remainder y n (normal_q_log_term(mul power square)n)
        (add sum(normal_q_log_term(mul power square)n)));try assumption;[lia| |apply Z.ltb_lt;exact Early].
      exact(normal_log_sum_bound _ (S n) _ T ltac:(lia) Serror).
    + apply IH;try assumption;lia.
Qed.

Theorem normal_q_log_series_error y : valid y -> 1<=qval y<2 ->
  valid(normal_q_log_series y) /\ Rabs(2*qval(normal_q_log_series y)-ln(qval y))<=bpow radix2 (-234).
Proof.
  intros Y Range;destruct(normal_q_log_argument_error y Y Range)as[T [e [E Value]]].
  destruct(normal_atanh_identity(qval y)ltac:(split;lra))as[Domain _].
  destruct(normal_q_log_square_error y Y Range)as[Square SquareError].
  set(t:=normal_atanh_argument(qval y))in *.
  assert (Difference : Rabs(qval(normal_q_log_argument y)-t)<=bpow radix2 (-250)).
  { rewrite Value;replace(t*(1+e)-t)with(t*e)by ring.
    rewrite Rabs_mult,(Rabs_pos_eq t)by lra;pose proof(Rabs_pos e);nra. }
  assert (State : normal_log_state t 1 (normal_q_log_argument y)(normal_q_log_argument y)).
  { unfold normal_log_state;split;[exact T|]. split;[exact T|]. split.
    - replace(t^(2*1-1))with t by(cbn;ring);eapply Rle_trans;[exact Difference|apply bpow_le;lia].
    - replace(normal_atanh_series 1 t)with t by(cbn;field).
      change(INR 1)with 1;rewrite Rmult_1_l;eapply Rle_trans;[exact Difference|apply bpow_le;lia]. }
  unfold normal_q_log_series;apply normal_q_log_loop_error;try assumption;try lia;split;lra.
Qed.
