(** The accurate logarithm's forward odd-power series, with its actual
    early-stop test. Local operation bounds are stated before composition. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Q Require Import Q256 Q256Real.
Require Import StageGappa ErfcxAccurateInputs ErfcxAccurateSetup
  NormalConstants NormalLogReduction NormalLogReciprocal NormalLogArgument
  NormalLogAnalytic.
Open Scope R_scope.

Definition normal_q_log_term power n := mul power (q_recip(q_odd n)).

Fixpoint normal_q_log_loop fuel n square power sum :=
  match fuel with
  | O => sum
  | S rest =>
      let power' := mul power square in
      let term := normal_q_log_term power' n in
      let sum' := add sum term in
      if Z.ltb(top term)(top sum'-270) then sum'
      else normal_q_log_loop rest (S n) square power' sum'
  end.

Definition normal_q_log_series y :=
  let t:=normal_q_log_argument y in
  normal_q_log_loop 99 1 (mul t t) t t.

Definition normal_q_logarithm x :=
  let exponent:=top x in
  let y:=normal_q_log_normalized x in
  add (mul_pow2(normal_q_log_series y)1)
    (mul(q_float(LnAccurate.fe exponent))normal_q_ln2).

Theorem normal_q_log_odd_reciprocal n : (n<100)%nat ->
  valid(q_recip(q_odd n)) /\ exists e,Rabs e<=bpow radix2 (-252) /\
  qval(q_recip(q_odd n))=(/(2*INR n+1))*(1+e).
Proof.
  intros N;destruct(q_odd_ok n ltac:(lia))as[Q Value].
  assert (Index : 0<=INR n<100).
  { split;[apply pos_INR|replace 100 with(INR 100)by(simpl;ring);apply lt_INR;exact N]. }
  assert (Upper : 256<=3*bpow radix2 1022).
  { assert(128<=bpow radix2 1022)by(change 128 with(bpow radix2 7);apply bpow_le;lia);lra. }
  destruct(normal_q_log_reciprocal_error _ Q ltac:(rewrite Value;split;lra))as[Result Error].
  rewrite Value in Error;split;assumption.
Qed.

Lemma normal_log_square_product_error t e m : 0<=t<=/3 ->
  Rabs e<=bpow radix2 (-250) -> Rabs m<=bpow radix2 (-255) ->
  Rabs((t+e)*(t+e)*(1+m)-t*t)<=bpow radix2 (-248).
Proof.
  intros T E M;apply Rabs_le_inv in E,M.
  replace((t+e)*(t+e)*(1+m)-t*t)with(2*t*e+e*e+(t+e)*(t+e)*m)by ring.
  bpow_num_all;apply Rabs_le;split;interval with(i_prec 400).
Qed.

Theorem normal_q_log_square_error y : valid y -> 1<=qval y<2 ->
  valid(mul(normal_q_log_argument y)(normal_q_log_argument y)) /\
  Rabs(qval(mul(normal_q_log_argument y)(normal_q_log_argument y))-
    normal_atanh_argument(qval y)*normal_atanh_argument(qval y))<=bpow radix2 (-248).
Proof.
  intros Y Range;destruct(normal_q_log_argument_error y Y Range)as[T [e [E Value]]].
  destruct(normal_atanh_identity(qval y)ltac:(split;lra))as[Domain _].
  destruct(mul_relative _ _ T T)as[Result [m [M Product]]].
  split;[exact Result|].
  set(t:=normal_atanh_argument(qval y))in *.
  assert (Difference : Rabs(qval(normal_q_log_argument y)-t)<=bpow radix2 (-250)).
  { rewrite Value;replace(t*(1+e)-t)with(t*e)by ring.
    rewrite Rabs_mult,(Rabs_pos_eq t)by lra;pose proof(Rabs_pos e);nra. }
  rewrite Product;replace(qval(normal_q_log_argument y))with
    (t+(qval(normal_q_log_argument y)-t))by ring.
  apply normal_log_square_product_error;assumption.
Qed.

Lemma normal_log_power_product_error p z pe ze m :
  Rabs p<=1 -> 0<=z<=/9 -> Rabs pe<=bpow radix2 (-246) ->
  Rabs ze<=bpow radix2 (-248) -> Rabs m<=bpow radix2 (-255) ->
  Rabs((p+pe)*(z+ze)*(1+m)-p*z)<=bpow radix2 (-246).
Proof.
  intros P Z PE ZE M;apply Rabs_le_inv in P,PE,ZE,M.
  replace((p+pe)*(z+ze)*(1+m)-p*z)with(pe*z+(p+pe)*ze+(p+pe)*(z+ze)*m)by ring.
  bpow_num_all;apply Rabs_le;split;interval with(i_prec 400).
Qed.

Theorem normal_q_log_power_step power square p t : valid power -> valid square ->
  Rabs p<=1 -> 0<=t<=/3 ->
  Rabs(qval power-p)<=bpow radix2 (-246) ->
  Rabs(qval square-t*t)<=bpow radix2 (-248) ->
  valid(mul power square) /\ Rabs(qval(mul power square)-p*(t*t))<=bpow radix2 (-246).
Proof.
  intros P S Prange Trange Perror Serror;destruct(mul_relative _ _ P S)as[Result [m [M Value]]].
  split;[exact Result|];rewrite Value.
  replace(qval power)with(p+(qval power-p))by ring.
  replace(qval square)with(t*t+(qval square-t*t))by ring.
  apply normal_log_power_product_error;try assumption;split;nra.
Qed.

Lemma normal_log_term_product_error p e r m d :
  Rabs p<=1 -> Rabs e<=bpow radix2 (-246) ->
  Rabs r<=bpow radix2 (-252) -> Rabs m<=bpow radix2 (-255) -> 0<=d<=1 ->
  Rabs((p+e)*(d*(1+r))*(1+m)-p*d)<=bpow radix2 (-245).
Proof.
  intros P E R M D;apply Rabs_le_inv in P,E,R,M.
  replace((p+e)*(d*(1+r))*(1+m)-p*d)with(d*(e+(p+e)*(r+(1+r)*m)))by ring.
  bpow_num_all;apply Rabs_le;split;interval with(i_prec 400).
Qed.

Theorem normal_q_log_term_error power p n : valid power -> Rabs p<=1 ->
  Rabs(qval power-p)<=bpow radix2 (-246) -> (n<100)%nat ->
  valid(normal_q_log_term power n) /\
  Rabs(qval(normal_q_log_term power n)-p/(2*INR n+1))<=bpow radix2 (-245).
Proof.
  intros P Prange Perror N;destruct(normal_q_log_odd_reciprocal n N)as[R [r [RE Rvalue]]].
  destruct(mul_relative _ _ P R)as[Result [m [M Value]]].
  assert (D : 0<=/(2*INR n+1)<=1).
  { pose proof(pos_INR n);split;[left;apply Rinv_0_lt_compat;lra|].
    rewrite <-Rinv_1;apply Rinv_le_contravar;lra. }
  split;[exact Result|];unfold normal_q_log_term;rewrite Value,Rvalue.
  replace(qval power)with(p+(qval power-p))by ring;unfold Rdiv.
  apply normal_log_term_product_error;assumption.
Qed.

Lemma normal_log_power_range t n : 0<=t<=1 -> 0<=t^n<=1.
Proof. intros T;induction n as[|n IH];cbn[pow];split;nra. Qed.

Lemma normal_log_series_range t n : 0<=t<=1 -> 0<=normal_atanh_series n t<=INR n.
Proof.
  intros T;induction n as[|n IH];[cbn;split;lra|].
  cbn[normal_atanh_series];rewrite S_INR.
  pose proof(normal_log_power_range t (2*n+1) T)as Power.
  assert (Den : 1<=INR(2*n+1)).
  { change 1 with(INR 1);apply le_INR;lia. }
  assert (Term : 0<=t^(2*n+1)/INR(2*n+1)<=1).
  { unfold Rdiv;split;[apply Rmult_le_pos;[lra|left;apply Rinv_0_lt_compat;lra]|].
    assert (0</INR(2*n+1)<=1).
    { split;[apply Rinv_0_lt_compat;lra|rewrite <-Rinv_1;apply Rinv_le_contravar;lra]. } nra. }
  split;lra.
Qed.

Definition normal_log_state t n power sum :=
  valid power /\ valid sum /\
  Rabs(qval power-t^(2*n-1))<=bpow radix2 (-246) /\
  Rabs(qval sum-normal_atanh_series n t)<=INR n*bpow radix2 (-244).

Lemma normal_log_sum_bound t n sum : 0<=t<=/3 -> (n<=100)%nat ->
  Rabs(qval sum-normal_atanh_series n t)<=INR n*bpow radix2 (-244) ->
  Rabs(qval sum)<=128.
Proof.
  intros T N Error;pose proof(normal_log_series_range t n ltac:(split;lra))as Range.
  assert (Index : 0<=INR n<=100).
  { split;[apply pos_INR|replace 100 with(INR 100)by(simpl;ring);apply le_INR;exact N]. }
  apply Rabs_le_inv in Error.
  assert (Small : 0<=bpow radix2 (-244)<=/100)by(split;[apply bpow_ge_0|interval with(i_prec 80)]).
  apply Rabs_le;split;nra.
Qed.

Theorem normal_q_log_series_step t n power sum square :
  0<=t<=/3 -> (1<=n<100)%nat -> normal_log_state t n power sum ->
  valid square -> Rabs(qval square-t*t)<=bpow radix2 (-248) ->
  let power':=mul power square in
  let term:=normal_q_log_term power' n in
  normal_log_state t (S n) power' (add sum term) /\ valid term /\
  Rabs(qval term-t^(2*n+1)/(2*INR n+1))<=bpow radix2 (-245).
Proof.
  intros T N [P [SumValid [Perror Serror]]] Z Zerror;cbv zeta.
  pose proof(normal_log_power_range t (2*n-1)ltac:(split;lra))as OldPower.
  assert (Product : t^(2*n-1)*(t*t)=t^(2*n+1)).
  { replace(t*t)with(t^2)by(cbn;ring);rewrite <-pow_add;f_equal;lia. }
  destruct(normal_q_log_power_step power square (t^(2*n-1)) t P Z
    ltac:(rewrite Rabs_pos_eq;lra) T Perror Zerror)as[P' Perror'].
  rewrite Product in Perror'.
  pose proof(normal_log_power_range t (2*n+1)ltac:(split;lra))as NewPower.
  destruct(normal_q_log_term_error _ (t^(2*n+1)) n P'
    ltac:(rewrite Rabs_pos_eq;lra) Perror' ltac:(lia))as[Term TermError].
  destruct(add_any _ _ SumValid Term)as[Sum AddError].
  assert (SumRange : Rabs(qval sum)<=128)by(exact(normal_log_sum_bound t n sum T ltac:(lia) Serror)).
  assert (TermRange : Rabs(qval(normal_q_log_term(mul power square)n))<=2).
  { assert (Den : 0</(2*INR n+1)<=1).
    { pose proof(pos_INR n);split;[apply Rinv_0_lt_compat;lra|rewrite <-Rinv_1;apply Rinv_le_contravar;lra]. }
    apply Rabs_le_inv in TermError;unfold Rdiv in TermError.
    assert(bpow radix2 (-245)<=1)by(interval with(i_prec 80));apply Rabs_le;split;nra. }
  assert (Addition : Rabs(qval(add sum(normal_q_log_term(mul power square)n))-
    (qval sum+qval(normal_q_log_term(mul power square)n)))<=bpow radix2 (-247)).
  { eapply Rle_trans;[exact AddError|].
    replace(bpow radix2 (-247))with(bpow radix2 (-254)*128)by(bpow_num;field).
    apply Rmult_le_compat_l;[apply bpow_ge_0|apply Rmax_lub;lra]. }
  split;[|split;assumption]. unfold normal_log_state;split;[exact P'|].
  split;[exact Sum|]. split.
  - replace(2*S n-1)%nat with(2*n+1)%nat by lia;exact Perror'.
  - cbn[normal_atanh_series];rewrite S_INR.
    assert (Denominator : INR(2*n+1)=2*INR n+1)by(rewrite plus_INR,mult_INR;reflexivity).
    rewrite Denominator.
    replace(qval(add sum(normal_q_log_term(mul power square)n))-
      (normal_atanh_series n t+t^(2*n+1)/(2*INR n+1)))with
      ((qval sum-normal_atanh_series n t)+
       (qval(normal_q_log_term(mul power square)n)-t^(2*n+1)/(2*INR n+1))+
       (qval(add sum(normal_q_log_term(mul power square)n))-
         (qval sum+qval(normal_q_log_term(mul power square)n))))by ring.
    eapply Rle_trans;[apply Rabs_triang|].
    eapply Rle_trans;[apply Rplus_le_compat_r,Rabs_triang|].
    assert (Budget : bpow radix2 (-245)+bpow radix2 (-247)<=bpow radix2 (-244))by(interval with(i_prec 300)).
    nra.
Qed.
