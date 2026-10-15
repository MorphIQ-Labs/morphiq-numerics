(** The accurate logarithm's (y-1)/(y+1) reduction. Subtraction is exact
    because y and one have the same integer-significand alignment grid. *)
From Coq Require Import Reals ZArith Lia Lra Psatz Bool.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Q Require Import QSpec Q256 Q256Real Limbs LimbScan.
Require Import StageGappa ErfcxAccurateTerms ErfcxAccurateSetup
  NormalResidualGrid NormalLogReduction NormalLogReciprocal NormalLogAnalytic.
Open Scope R_scope.

Lemma normal_q_ordered_same_grid big small :
  ok4(m big) -> ok4(m small) ->
  normalized 256(v(m big)) -> normalized 256(v(m small)) ->
  neg big<>neg small -> mag small<=mag big -> e big=e small ->
  qval(add_ordered big small)=qval big+qval small.
Proof.
  intros Ob Os Nb Ns Signs Order Exponents.
  assert (Sign : Bool.eqb(neg big)(neg small)=false)by(apply Bool.eqb_false_iff;exact Signs).
  pose proof(add_ordered_ok big small Ob Os Nb Ns Order)as Result.
  unfold add_m in Result;rewrite Sign in Result.
  replace(e big-e small)%Z with 0%Z in Result by lia.
  change(2^0)%Z with 1%Z in Result;rewrite Z.div_1_r in Result.
  assert (Difference : (0<=v(m big)-v(m small)<2^256)%Z).
  { assert (M : (v(m small)<=v(m big))%Z).
    { apply le_IZR;apply(Rmult_le_reg_r(bpow radix2(e big)));[apply bpow_gt_0|].
      unfold mag,F2R in Order;cbn in Order;rewrite <-Exponents in Order;exact Order. }
    unfold normalized in Nb,Ns;lia. }
  pose proof(norm_ok 256 ltac:(lia) (v(m big)-v(m small)) (e big) Difference)as Normal.
  destruct(norm 256 (v(m big)-v(m small)) (e big))as[mn en].
  cbv zeta in Result,Normal;destruct Result as[_ [_ Value]];destruct Normal as[_ Exact].
  rewrite Value,!normal_qval_signed;unfold val,mag,F2R in *;cbn in *.
  rewrite <-Exponents.
  destruct(neg big), (neg small);try congruence;
    cbn;rewrite ?opp_IZR in *;rewrite minus_IZR in Exact;nra.
Qed.

Theorem normal_q_same_grid_difference a b : valid a -> valid b ->
  neg a<>neg b -> e a=e b -> qval(add a b)=qval a+qval b.
Proof.
  intros[Oa Na][Ob Nb]Signs Exponents.
  unfold add;rewrite !is_zero_ok by(apply Oa||apply Ob).
  destruct(Z.eqb_spec(v(m a))0)as[Za|Za].
  - rewrite(qval_zero a Za);ring.
  - destruct(Z.eqb_spec(v(m b))0)as[Zb|Zb].
    + rewrite(qval_zero b Zb);ring.
    + destruct Na as[Na|Na];[contradiction|]. destruct Nb as[Nb|Nb];[contradiction|].
      pose proof(cmp_abs_ok a b Oa Ob Na Nb)as Order.
      destruct(cmp_abs a b).
      * apply normal_q_ordered_same_grid;assumption.
      * rewrite Rplus_comm;apply normal_q_ordered_same_grid;try assumption;try lra;congruence.
      * apply normal_q_ordered_same_grid;assumption.
Qed.

Lemma normal_q_unit_binade y : valid y -> 1<=qval y<2 -> e y=(-255)%Z.
Proof.
  intros Y Range;pose proof(normal_q_top_range y Y ltac:(lra))as[Lower Upper].
  rewrite Rabs_pos_eq in Lower,Upper by lra.
  assert (Top : top y=0%Z).
  { assert (L : (0<top y+1)%Z).
    { apply(lt_bpow radix2);change(bpow radix2 0)with 1;lra. }
    assert (U : (top y<1)%Z).
    { apply(lt_bpow radix2);change(bpow radix2 1)with 2;lra. } lia. }
  unfold top in Top;rewrite is_zero_ok in Top by apply Y.
  destruct(Z.eqb_spec(v(m y))0)as[Zero|Nonzero];[discriminate|lia].
Qed.

Definition normal_q_log_numerator y := add y (neg_q q_one).
Definition normal_q_log_denominator y := add y q_one.
Definition normal_q_log_argument y := mul (normal_q_log_numerator y) (q_recip(normal_q_log_denominator y)).

Theorem normal_q_log_numerator_exact y : valid y -> 1<=qval y<2 ->
  valid(normal_q_log_numerator y) /\ qval(normal_q_log_numerator y)=qval y-1.
Proof.
  intros Y Range;destruct q_one_ok as[One OneValue].
  destruct(neg_any _ One)as[NOne NValue];destruct(add_any _ _ Y NOne)as[Result _].
  split;[exact Result|]. unfold normal_q_log_numerator.
  rewrite normal_q_same_grid_difference;try assumption.
  - rewrite NValue,OneValue;ring.
  - rewrite(normal_positive_q_sign y Y ltac:(lra));vm_compute;congruence.
  - rewrite(normal_q_unit_binade y Y Range);reflexivity.
Qed.

Theorem normal_q_log_denominator_error y : valid y -> 1<=qval y<2 ->
  valid(normal_q_log_denominator y) /\
  1<=qval(normal_q_log_denominator y)<=4 /\
  exists d,Rabs d<=bpow radix2 (-254) /\
    qval(normal_q_log_denominator y)=(qval y+1)*(1+d).
Proof.
  intros Y Range;destruct q_one_ok as[One OneValue].
  destruct(add_any _ _ Y One)as[Result Error].
  fold(normal_q_log_denominator y)in Result,Error;rewrite OneValue in Error.
  assert (Inputs : Rmax(Rabs(qval y))(Rabs 1)<=2).
  { apply Rmax_lub;rewrite Rabs_pos_eq;lra. }
  assert (Absolute : Rabs(qval(normal_q_log_denominator y)-(qval y+1))<=bpow radix2 (-253)).
  { eapply Rle_trans;[exact Error|].
    replace(bpow radix2 (-253))with(bpow radix2 (-254)*2)by(bpow_num;field).
    apply Rmult_le_compat_l;[apply bpow_ge_0|exact Inputs]. }
  assert (Bounds : 1<=qval(normal_q_log_denominator y)<=4).
  { apply Rabs_le_inv in Absolute;assert(bpow radix2 (-253)<1)by(interval with(i_prec 80));split;lra. }
  split;[exact Result|]. split;[exact Bounds|].
  exists((qval(normal_q_log_denominator y)-(qval y+1))/(qval y+1));split.
  - unfold Rdiv;rewrite Rabs_mult,Rabs_Rinv,(Rabs_pos_eq(qval y+1))by lra.
    apply(Rmult_le_reg_r(qval y+1));[lra|].
    rewrite Rmult_assoc,Rinv_l,Rmult_1_r by lra.
    replace(bpow radix2 (-253))with(bpow radix2 (-254)*2)in Absolute by(bpow_num;field).
    pose proof(bpow_gt_0 radix2 (-254));nra.
  - field;lra.
Qed.

Lemma normal_log_quotient_product_error d r m :
  Rabs d<=bpow radix2 (-254) -> Rabs r<=bpow radix2 (-252) ->
  Rabs m<=bpow radix2 (-255) ->
  Rabs((1+r)*(1+m)/(1+d)-1)<=bpow radix2 (-250).
Proof.
  intros D R M;apply Rabs_le_inv in D,R,M.
  assert (Den : 1+d<>0)by(bpow_num_all;lra).
  replace((1+r)*(1+m)/(1+d)-1)with((r+m+r*m-d)/(1+d))by(field;exact Den).
  bpow_num_all;apply Rabs_le;split;interval with(i_prec 400).
Qed.

Theorem normal_q_log_argument_error y : valid y -> 1<=qval y<2 ->
  valid(normal_q_log_argument y) /\ exists e,Rabs e<=bpow radix2 (-250) /\
    qval(normal_q_log_argument y)=normal_atanh_argument(qval y)*(1+e).
Proof.
  intros Y Range;destruct(normal_q_log_numerator_exact y Y Range)as[N Nvalue].
  destruct(normal_q_log_denominator_error y Y Range)as[D [Domain [d [DE Dvalue]]]].
  assert (Upper : 4<=3*bpow radix2 1022).
  { assert (2<=bpow radix2 1022)by(change 2 with(bpow radix2 1);apply bpow_le;lia);lra. }
  destruct(normal_q_log_reciprocal_error _ D ltac:(split;lra))as[R [r [RE Rvalue]]].
  destruct(mul_relative _ _ N R)as[Result [m [ME Mvalue]]].
  split;[exact Result|]. exists((1+r)*(1+m)/(1+d)-1);split.
  - apply normal_log_quotient_product_error;assumption.
  - unfold normal_q_log_argument;rewrite Mvalue,Nvalue,Rvalue,Dvalue.
    unfold normal_atanh_argument;field;split;[apply Rabs_le_inv in DE;bpow_num_all;lra|lra].
Qed.

Theorem normal_q_log_argument_range y : valid y -> 1<=qval y<2 ->
  0<=qval(normal_q_log_argument y)<=17/50.
Proof.
  intros Y Range;destruct(normal_q_log_argument_error y Y Range)as[_ [e [E Value]]].
  destruct(normal_atanh_identity(qval y)ltac:(split;lra))as[T _].
  assert (Factor : 0<=1+e<=51/50).
  { apply Rabs_le_inv in E;bpow_num_all;split;interval with(i_prec 80). }
  rewrite Value;split;[apply Rmult_le_pos;lra|nra].
Qed.

