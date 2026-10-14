(** Relative operation bounds for the positive series used by ln(1-q). *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Q Require Import Q256 Q256Real.
Require Import StageGappa ErfcxAccurateInputs ErfcxAccurateSetup
  NormalLogReciprocal NormalPositiveSum NormalComplementAnalytic.
Open Scope R_scope.

Definition normal_q_complement_integer n := q_float(LnAccurate.fe(Z.of_nat n)).
Definition normal_q_complement_term power n := mul power (q_recip(normal_q_complement_integer n)).

Fixpoint normal_q_complement_loop fuel n x power sum :=
  match fuel with
  | O=>sum
  | S rest=>
      let power':=mul power x in
      let term:=normal_q_complement_term power' (S n) in
      let sum':=add sum term in
      if Z.ltb(top term)(top sum'-270) then sum'
      else normal_q_complement_loop rest (S n) x power' sum'
  end.
Definition normal_q_log_complement x := neg_q(normal_q_complement_loop 298 1 x x x).

Theorem normal_q_complement_reciprocal n : (1<=n<=299)%nat ->
  valid(q_recip(normal_q_complement_integer n)) /\ exists e,Rabs e<=bpow radix2 (-252) /\
  qval(q_recip(normal_q_complement_integer n))=(/INR n)*(1+e).
Proof.
  intros N;destruct(LnAccurate.fe_ok (Z.of_nat n)ltac:(rewrite Z.abs_eq;lia))as[F Value].
  destruct(q_float_ok _ F)as[Q Qvalue];rewrite Value,<-INR_IZR_INZ in Qvalue.
  assert (Index : 1<=INR n<=299).
  { split;[change 1 with(INR 1)|replace 299 with(INR 299)by(simpl;ring)];apply le_INR;lia. }
  assert (Upper : 299<=3*bpow radix2 1022).
  { assert(128<=bpow radix2 1022)by(change 128 with(bpow radix2 7);apply bpow_le;lia);lra. }
  destruct(normal_q_log_reciprocal_error _ Q ltac:(rewrite Qvalue;split;lra))as[Result Error].
  rewrite Qvalue in Error;split;assumption.
Qed.

Lemma normal_relative_error_growth e m n epsilon mu :
  0<=n -> 0<=epsilon -> n*epsilon<=1 -> 2*mu<=epsilon ->
  Rabs e<=n*epsilon -> Rabs m<=mu ->
  Rabs((1+e)*(1+m)-1)<=(n+1)*epsilon.
Proof.
  intros N Epsilon Small Budget E M.
  assert (Factor : Rabs(1+e)<=2).
  { apply Rabs_le_inv in E;apply Rabs_le;split;lra. }
  replace((1+e)*(1+m)-1)with(e+(1+e)*m)by ring.
  eapply Rle_trans;[apply Rabs_triang|];rewrite Rabs_mult.
  assert (Product : Rabs(1+e)*Rabs m<=2*mu).
  { apply Rmult_le_compat;[apply Rabs_pos|apply Rabs_pos|exact Factor|exact M]. } nra.
Qed.

Lemma normal_complement_term_product_error p r m :
  Rabs p<=bpow radix2 (-245) -> Rabs r<=bpow radix2 (-252) ->
  Rabs m<=bpow radix2 (-255) -> Rabs((1+p)*(1+r)*(1+m)-1)<=bpow radix2 (-244).
Proof.
  intros P R M;apply Rabs_le_inv in P,R,M.
  replace((1+p)*(1+r)*(1+m)-1)with(p+(1+p)*(r+(1+r)*m))by ring.
  bpow_num_all;apply Rabs_le;split;interval with(i_prec 400).
Qed.

Theorem normal_q_complement_term_error power target n : valid power ->
  (exists e,Rabs e<=bpow radix2 (-245) /\ qval power=target*(1+e)) ->
  (1<=n<=299)%nat ->
  valid(normal_q_complement_term power n) /\ exists e,Rabs e<=bpow radix2 (-244) /\
  qval(normal_q_complement_term power n)=(target/INR n)*(1+e).
Proof.
  intros P [p [PE Pvalue]] N;destruct(normal_q_complement_reciprocal n N)as[R [r [RE Rvalue]]].
  destruct(mul_relative _ _ P R)as[Result [m [M Value]]].
  split;[exact Result|];exists((1+p)*(1+r)*(1+m)-1);split.
  - apply normal_complement_term_product_error;assumption.
  - unfold normal_q_complement_term;rewrite Value,Pvalue,Rvalue;unfold Rdiv;ring.
Qed.

Definition normal_complement_state q n power sum :=
  valid power /\ valid sum /\ exists ep es,
  Rabs ep<=INR n*bpow radix2 (-254) /\ Rabs es<=INR n*bpow radix2 (-243) /\
  qval power=q^n*(1+ep) /\ qval sum=normal_complement_series n q*(1+es).

Lemma normal_complement_count_bounds n : (n<=299)%nat ->
  0<=INR n<=300 /\ INR n*bpow radix2 (-254)<=bpow radix2 (-245) /\
  INR n*bpow radix2 (-243)<=/2.
Proof.
  intros N;assert (Index : 0<=INR n<=300).
  { split;[apply pos_INR|replace 300 with(INR 300)by(simpl;ring);apply le_INR;lia]. }
  split;[exact Index|];split;interval with(i_prec 300).
Qed.

Theorem normal_q_complement_series_step x n power sum : valid x -> 0<qval x<=/2 ->
  (1<=n<299)%nat -> normal_complement_state (qval x)n power sum ->
  let power':=mul power x in
  let term:=normal_q_complement_term power' (S n) in
  normal_complement_state (qval x)(S n)power'(add sum term) /\ valid term /\
  exists et,Rabs et<=bpow radix2 (-244) /\
    qval term=((qval x)^(S n)/INR(S n))*(1+et).
Proof.
  intros X Range N [P [Sum [ep [es [EP [ES [Pvalue Svalue]]]]]]];cbv zeta.
  destruct(normal_complement_count_bounds n ltac:(lia))as[Index [PowerBudget SumBudget]].
  destruct(normal_complement_count_bounds (S n)ltac:(lia))as[Index' [PowerBudget' SumBudget']].
  destruct(mul_relative _ _ P X)as[P' [m [M Value]]].
  set(ep':=(1+ep)*(1+m)-1).
  assert (EP' : Rabs ep'<=INR(S n)*bpow radix2 (-254)).
  { unfold ep';rewrite S_INR;apply(normal_relative_error_growth ep m (INR n) _ (bpow radix2 (-255)));
      try assumption;try lra.
    - apply bpow_ge_0.
    - eapply Rle_trans;[exact PowerBudget|interval with(i_prec 300)].
    - interval with(i_prec 300). }
  assert (Pvalue' : qval(mul power x)=(qval x)^(S n)*(1+ep')).
  { rewrite Value,Pvalue;unfold ep';cbn[pow];ring. }
  destruct(normal_q_complement_term_error _ ((qval x)^(S n)) (S n) P'
    ltac:(exists ep';split;[eapply Rle_trans;[exact EP'|exact PowerBudget']|exact Pvalue'])ltac:(lia))
    as[Term [et [ET Tvalue]]].
  pose proof(normal_complement_series_range n (qval x)ltac:(lia)Range)as SeriesRange.
  assert (TargetTerm : 0<(qval x)^(S n)/INR(S n)).
  { apply Rdiv_lt_0_compat;[apply pow_lt;lra|apply lt_0_INR;lia]. }
  assert (SumPositive : 0<qval sum).
  { rewrite Svalue;apply Rabs_le_inv in ES;nra. }
  assert (TermPositive : 0<qval(normal_q_complement_term(mul power x)(S n))).
  { rewrite Tvalue;apply Rabs_le_inv in ET;assert(bpow radix2 (-244)<1)by(interval with(i_prec 80));nra. }
  destruct(normal_q_positive_add_relative _ _ Sum Term ltac:(lra)ltac:(lra))as[Sum' [a [A Avalue]]].
  set(w:=(normal_complement_series n(qval x)*es+((qval x)^(S n)/INR(S n))*et)/
    (normal_complement_series n(qval x)+(qval x)^(S n)/INR(S n))).
  assert (W : Rabs w<=INR n*bpow radix2 (-243)).
  { unfold w;apply normal_weighted_relative_error;try assumption;try lra.
    assert (One : 1<=INR n)by(change 1 with(INR 1);apply le_INR;lia).
    assert (Budget : bpow radix2 (-244)<=bpow radix2 (-243))by(apply bpow_le;lia).
    pose proof(bpow_gt_0 radix2 (-243));nra. }
  assert (Wvalue : qval sum+qval(normal_q_complement_term(mul power x)(S n))=
    normal_complement_series(S n)(qval x)*(1+w)).
  { rewrite Svalue,Tvalue;change(normal_complement_series(S n)(qval x))with
      (normal_complement_series n(qval x)+(qval x)^(S n)/INR(S n)).
    assert (0<INR(S n))by(apply lt_0_INR;lia).
    assert (0<(qval x)^(S n))by(apply pow_lt;lra).
    unfold w;field;nra. }
  split;[|split;[exact Term|exists et;split;assumption]].
  unfold normal_complement_state;split;[exact P'|]. split;[exact Sum'|].
  exists ep',((1+w)*(1+a)-1);split;[exact EP'|]. split.
  - rewrite S_INR;apply(normal_relative_error_growth w a (INR n) _ (bpow radix2 (-254)));
      try assumption;try lra;[apply bpow_ge_0|interval with(i_prec 300)].
  - split;[exact Pvalue'|];rewrite Avalue,Wvalue;ring.
Qed.
