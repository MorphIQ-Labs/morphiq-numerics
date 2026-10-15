(** Complete relative bound for ln(1-q), including its early termination
    and final binary64 conversion with gradual underflow. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Binary64 Require Import IEEE64.
From Q Require Import Q256 Q256Real.
Require Import StageGappa NormalLogReduction NormalComplementAnalytic
  NormalComplementSeries NormalAccurateRounding.
Open Scope R_scope.

Lemma normal_complement_stopped_remainder q n power sum term :
  0<q<=/2 -> (1<=n<=299)%nat -> normal_complement_state q n power sum ->
  valid term -> (exists et,Rabs et<=bpow radix2 (-244) /\ qval term=(q^n/INR n)*(1+et)) ->
  (top term<top sum-270)%Z ->
  Rabs(-ln(1-q)-normal_complement_series n q)<=(-ln(1-q))*bpow radix2 (-256).
Proof.
  intros Q N [_ [Sum [ep [es [_ [ES [_ Svalue]]]]]]] Term [et [ET Tvalue]] Early.
  pose proof(normal_complement_target_range q Q)as Target.
  pose proof(normal_complement_series_range n q (proj1 N)Q)as SeriesRange.
  destruct(normal_complement_count_bounds n (proj2 N))as[Index [_ SumBudget]].
  assert (IndexPositive : 1<=INR n)by(change 1 with(INR 1);apply le_INR;lia).
  assert (ExactTermPositive : 0<q^n/INR n)by(apply Rdiv_lt_0_compat;[apply pow_lt;lra|lra]).
  assert (SumRange : 0<qval sum<=4*(-ln(1-q))).
  { rewrite Svalue;apply Rabs_le_inv in ES;split;nra. }
  assert (TermRange : 0<qval term /\ q^n/INR n<=2*qval term).
  { rewrite Tvalue;apply Rabs_le_inv in ET.
    assert(bpow radix2 (-244)<=/2)by(interval with(i_prec 80));split;nra. }
  pose proof(normal_q_early_term_bound term sum Term Sum ltac:(lra)Early)as Small.
  rewrite(Rabs_pos_eq(qval term)),(Rabs_pos_eq(qval sum))in Small by lra.
  assert (ExactTerm : q^n/INR n<=8*(-ln(1-q))*bpow radix2 (-270)).
  { pose proof(bpow_gt_0 radix2 (-270));nra. }
  pose proof(normal_complement_remainder n q ltac:(split;lra))as Error.
  eapply Rle_trans;[exact Error|].
  replace(q^(n+1)/(1-q))with((q^n/INR n)*(INR n*q/(1-q)))
    by(rewrite pow_add;change(q^1)with(q*1);field;split;lra).
  assert (Factor : 0<=INR n*q/(1-q)<=300)by(split;interval with(i_prec 80)).
  assert (Product : (q^n/INR n)*(INR n*q/(1-q))<=
    (8*(-ln(1-q))*bpow radix2 (-270))*300).
  { apply Rmult_le_compat;lra. }
  assert (Budget : 2400*bpow radix2 (-270)<=bpow radix2 (-256))by(interval with(i_prec 300)).
  nra.
Qed.

Lemma normal_complement_sum_final_error q n power sum :
  0<q<=/2 -> (1<=n<=299)%nat -> normal_complement_state q n power sum ->
  Rabs(-ln(1-q)-normal_complement_series n q)<=(-ln(1-q))*bpow radix2 (-256) ->
  Rabs(qval sum- -ln(1-q))<=(-ln(1-q))*bpow radix2 (-232).
Proof.
  intros Q N [_ [_ [ep [es [_ [ES [_ Value]]]]]]] Remainder.
  pose proof(normal_complement_target_range q Q)as Target.
  pose proof(normal_complement_series_range n q (proj1 N)Q)as SeriesRange.
  destruct(normal_complement_count_bounds n (proj2 N))as[Index _].
  assert (E : Rabs es<=300*bpow radix2 (-243)).
  { eapply Rle_trans;[exact ES|apply Rmult_le_compat_r;[apply bpow_ge_0|lra]]. }
  replace(qval sum- -ln(1-q))with
    ((qval sum-normal_complement_series n q)+ -( -ln(1-q)-normal_complement_series n q))by ring.
  eapply Rle_trans;[apply Rabs_triang|];rewrite Rabs_Ropp,Value.
  replace(normal_complement_series n q*(1+es)-normal_complement_series n q)with
    (normal_complement_series n q*es)by ring.
  rewrite Rabs_mult,(Rabs_pos_eq(normal_complement_series n q))by lra.
  assert (Product : normal_complement_series n q*Rabs es<=
    (2*(-ln(1-q)))*(300*bpow radix2 (-243))).
  { apply Rmult_le_compat;[lra|apply Rabs_pos|lra|exact E]. }
  assert (Budget : 600*bpow radix2 (-243)+bpow radix2 (-256)<=bpow radix2 (-232))by(interval with(i_prec 300)).
  nra.
Qed.

Theorem normal_q_complement_loop_error fuel x n power sum : valid x -> 0<qval x<=/2 ->
  (1<=n)%nat -> (n+fuel=299)%nat -> normal_complement_state (qval x)n power sum ->
  valid(normal_q_complement_loop fuel n x power sum) /\
  Rabs(qval(normal_q_complement_loop fuel n x power sum)- -ln(1-qval x))<=
    (-ln(1-qval x))*bpow radix2 (-232).
Proof.
  revert n power sum;induction fuel as[|fuel IH];intros n power sum X Q N Count State.
  - assert(n=299%nat)by lia;subst n;cbn[normal_q_complement_loop].
    split;[exact(proj1(proj2 State))|].
    apply(normal_complement_sum_final_error (qval x)299 power sum);try assumption;[lia|].
    eapply Rle_trans;[apply normal_complement_remainder299;exact Q|].
    apply Rmult_le_compat_l;[pose proof(normal_complement_target_range _ Q);lra|apply bpow_le;lia].
  - pose proof(normal_q_complement_series_step x n power sum X Q ltac:(lia)State)as[Next [Term TermError]].
    cbv zeta in Next,Term,TermError;cbn[normal_q_complement_loop].
    destruct(Z.ltb(top(normal_q_complement_term(mul power x)(S n)))
      (top(add sum(normal_q_complement_term(mul power x)(S n)))-270))eqn:Early.
    + split;[exact(proj1(proj2 Next))|].
      apply(normal_complement_sum_final_error (qval x)(S n)(mul power x));try assumption;[lia|].
      apply(normal_complement_stopped_remainder (qval x)(S n)(mul power x)
        (add sum(normal_q_complement_term(mul power x)(S n)))
        (normal_q_complement_term(mul power x)(S n)));try assumption;[lia|apply Z.ltb_lt;exact Early].
    + apply IH;try assumption;lia.
Qed.

Theorem normal_q_log_complement_error x : valid x -> 0<qval x<=/2 ->
  valid(normal_q_log_complement x) /\ exists e,Rabs e<=bpow radix2 (-232) /\
  qval(normal_q_log_complement x)=ln(1-qval x)*(1+e).
Proof.
  intros X Q.
  assert (State : normal_complement_state (qval x)1 x x).
  { unfold normal_complement_state;split;[exact X|]. split;[exact X|]. exists 0,0.
    rewrite Rabs_R0;change(INR 1)with 1;rewrite !Rmult_1_l.
    split;[apply bpow_ge_0|]. split;[apply bpow_ge_0|].
    replace(normal_complement_series 1(qval x))with(qval x)by(cbn;field);cbn[pow];split;ring. }
  destruct(normal_q_complement_loop_error 298 x 1 x x X Q ltac:(lia)ltac:(lia)State)as[Result Error].
  destruct(neg_any _ Result)as[Negative Value];split;[exact Negative|].
  pose proof(normal_complement_target_range _ Q)as Range.
  set(target:= -ln(1-qval x))in *.
  exists((qval(normal_q_complement_loop 298 1 x x x)-target)/target);split.
  - unfold Rdiv;rewrite Rabs_mult,Rabs_Rinv,(Rabs_pos_eq target)by lra.
    apply(Rmult_le_reg_r target);[lra|];rewrite Rmult_assoc,Rinv_l,Rmult_1_r by lra;nra.
  - unfold normal_q_log_complement;rewrite Value;unfold target in *;field;lra.
Qed.

Theorem normal_q_log_complement_rounded x : valid x -> 0<qval x<=/2 ->
  finite(Q256.to_f64(normal_q_log_complement x)) /\ exists d a,
  Rabs d<=bpow radix2 (-53)+bpow radix2 (-231) /\ Rabs a<=bpow radix2 (-1075) /\
  B(Q256.to_f64(normal_q_log_complement x))=ln(1-qval x)*(1+d)+a.
Proof.
  intros X Q;destruct(normal_q_log_complement_error x X Q)as[Result Error].
  pose proof(normal_complement_target_range _ Q)as Range.
  replace(bpow radix2 (-231))with(2*bpow radix2 (-232))by(bpow_num;field).
  apply normal_q_bounded_rounded;try assumption.
  - rewrite Rabs_left1;lra.
  - split;[apply bpow_ge_0|interval with(i_prec 80)].
Qed.
