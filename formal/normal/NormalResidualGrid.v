(** Subtracting opposite-sign Q256 values preserves a power-of-two radius
    when that radius lies on the larger operand's alignment grid. This is
    stronger than the generic absolute-error bound at a table-cell endpoint. *)
From Coq Require Import Reals ZArith Lia Lra Psatz Bool.
From Flocq Require Import Core.
From Q Require Import QSpec Q256 Q256Real Limbs LimbScan.
From Binary64 Require Import IEEE64.
Require Import ErfcxAccurateInputs.
Open Scope R_scope.

Lemma normal_aligned_difference_bound ma ea mb eb k : (eb<=ea<=k)%Z ->
  IZR ma*bpow radix2 ea-IZR mb*bpow radix2 eb<=bpow radix2 k ->
  (ma-mb/2^(ea-eb)<=2^(k-ea))%Z.
Proof.
  intros Exponents Difference.
  assert (Scaled : (ma*2^(ea-eb)-mb<=2^(k-eb))%Z).
  { apply le_IZR.
    rewrite minus_IZR,mult_IZR,!IZR_pow2 by lia.
    apply(Rmult_le_reg_r(bpow radix2 eb));[apply bpow_gt_0|].
    rewrite Rmult_minus_distr_r,Rmult_assoc,<- !bpow_plus.
    replace(ea-eb+eb)%Z with ea by ring;replace(k-eb+eb)%Z with k by ring.
    exact Difference. }
  assert (Power : (2^(k-eb)=2^(k-ea)*2^(ea-eb))%Z).
  { rewrite <-Z.pow_add_r by lia;f_equal;lia. }
  rewrite Power in Scaled.
  assert (Lower : (ma-2^(k-ea)<=mb/2^(ea-eb))%Z).
  { apply Z.div_le_lower_bound;[apply Z.pow_pos_nonneg;lia|nia]. }
  lia.
Qed.

Lemma normal_qval_signed x : qval x=if neg x then -mag x else mag x.
Proof.
  unfold qval,mag,val,F2R;cbn;destruct(neg x);cbn;[rewrite opp_IZR;ring|reflexivity].
Qed.

Lemma normal_opposite_ordered_sum big small : neg big<>neg small -> mag small<=mag big ->
  Rabs(qval big+qval small)=mag big-mag small.
Proof.
  intros Signs Order. rewrite !normal_qval_signed.
  destruct(neg big), (neg small);try congruence.
  - rewrite Rabs_left1 by lra;ring.
  - rewrite Rabs_pos_eq by lra;ring.
Qed.

Theorem normal_q_ordered_difference_radius big small k :
  ok4(m big) -> ok4(m small) ->
  normalized 256 (v(m big)) -> normalized 256 (v(m small)) ->
  neg big<>neg small -> mag small<=mag big -> (e big<=k)%Z ->
  mag big-mag small<=bpow radix2 k ->
  Rabs(qval(add_ordered big small))<=bpow radix2 k.
Proof.
  intros Ob Os Nb Ns Signs Order K Difference.
  assert (Exponents : (e small<=e big)%Z).
  { destruct(Z_le_gt_dec (e small)(e big));[assumption|exfalso].
    destruct(mag_bounds big Nb)as[_ Upper],(mag_bounds small Ns)as[Lower _].
    assert(bpow radix2(e big+256)<=bpow radix2(e small+255))by(apply bpow_le;lia);lra. }
  assert (Sign : Bool.eqb(neg big)(neg small)=false).
  { apply Bool.eqb_false_iff;exact Signs. }
  pose proof(add_ordered_ok big small Ob Os Nb Ns Order)as Result.
  unfold add_m in Result;rewrite Sign in Result.
  set(mr:=(v(m big)-v(m small)/2^(e big-e small))%Z)in *.
  assert (Aligned : (0<=v(m small)/2^(e big-e small)<=v(m big))%Z).
  { split.
    - apply Z.div_pos;[apply v_nonneg,Os|apply Z.pow_pos_nonneg;lia].
    - apply Z.div_le_upper_bound;[apply Z.pow_pos_nonneg;lia|].
      apply le_IZR;rewrite mult_IZR,IZR_pow2 by lia.
      apply(Rmult_le_reg_r(bpow radix2(e small)));[apply bpow_gt_0|].
      rewrite(Rmult_comm(bpow radix2(e big-e small))(IZR(v(m big)))).
      rewrite Rmult_assoc,<-bpow_plus.
      replace(e big-e small+e small)%Z with(e big)by ring.
      exact Order. }
  assert (Mr : (0<=mr<2^256)%Z)by(unfold mr;unfold normalized in Nb;lia).
  pose proof(norm_ok 256 ltac:(lia) mr (e big) Mr)as Normal.
  destruct(norm 256 mr (e big))as[mn en]. cbv zeta in Result,Normal.
  destruct Result as[_ [_ Value]];destruct Normal as[_ Exact].
  assert (Mn : (0<=mn)%Z).
  { (* The value equality also gives nonnegativity, without depending on a
       particular normalized exponent or the zero representation. *)
    apply le_IZR. apply(Rmult_le_reg_r(bpow radix2 en));[apply bpow_gt_0|].
    rewrite Rmult_0_l. change(0<=F2R(Float radix2 mn en)).
    rewrite Exact. unfold F2R;cbn;apply Rmult_le_pos;[apply IZR_le;lia|apply bpow_ge_0]. }
  rewrite Value,val_abs by exact Mn;rewrite Exact.
  unfold F2R;cbn.
  assert (Bound : (mr<=2^(k-e big))%Z).
  { unfold mr;apply normal_aligned_difference_bound;[lia|exact Difference]. }
  eapply Rle_trans with(IZR(2^(k-e big))*bpow radix2(e big)).
  - apply Rmult_le_compat_r;[apply bpow_ge_0|apply IZR_le;exact Bound].
  - rewrite IZR_pow2,<-bpow_plus by lia.
    replace(k-e big+e big)%Z with k by ring;apply Rle_refl.
Qed.

Theorem normal_q_opposite_difference_radius a b k :
  ok4(m a) -> ok4(m b) ->
  normalized 256 (v(m a)) -> normalized 256 (v(m b)) ->
  neg a<>neg b -> (e a<=k)%Z -> (e b<=k)%Z ->
  Rabs(qval a+qval b)<=bpow radix2 k ->
  Rabs(qval(add a b))<=bpow radix2 k.
Proof.
  intros Oa Ob Na Nb Signs Ka Kb Radius.
  assert (Za : (v(m a)=?0)%Z=false).
  { apply Z.eqb_neq;unfold normalized in Na;pose proof(Z.pow_pos_nonneg 2 255 ltac:(lia));lia. }
  assert (Zb : (v(m b)=?0)%Z=false).
  { apply Z.eqb_neq;unfold normalized in Nb;pose proof(Z.pow_pos_nonneg 2 255 ltac:(lia));lia. }
  pose proof(cmp_abs_ok a b Oa Ob Na Nb)as Order.
  unfold add;rewrite !is_zero_ok by(apply Oa||apply Ob);rewrite Za,Zb.
  destruct(cmp_abs a b).
  - apply normal_q_ordered_difference_radius;try assumption.
    rewrite <-normal_opposite_ordered_sum by assumption;exact Radius.
  - apply normal_q_ordered_difference_radius;try assumption;try lra;try congruence.
    rewrite <-normal_opposite_ordered_sum by(congruence||lra).
    rewrite Rplus_comm;exact Radius.
  - apply normal_q_ordered_difference_radius;try assumption.
    rewrite <-normal_opposite_ordered_sum by assumption;exact Radius.
Qed.


Lemma normal_positive_q_sign x : valid x -> 0<qval x -> neg x=false.
Proof.
  intros [O _] Positive. pose proof(mag_abs x O)as Magnitude.
  pose proof(Rabs_pos(qval x)). rewrite normal_qval_signed in Positive.
  destruct(neg x);[lra|reflexivity].
Qed.

Lemma normal_negative_q_sign x : valid x -> qval x<0 -> neg x=true.
Proof.
  intros [O _] Negative. pose proof(mag_abs x O)as Magnitude.
  pose proof(Rabs_pos(qval x)). rewrite normal_qval_signed in Negative.
  destruct(neg x);[reflexivity|lra].
Qed.

Lemma normal_small_q_grid x : valid x -> qval x<>0 -> Rabs(qval x)<=16 ->
  normalized 256 (v(m x)) /\ (e x<= -251)%Z.
Proof.
  intros [O [Zero|Normal]] Nonzero Small.
  - exfalso;apply Nonzero,qval_zero;exact Zero.
  - split;[exact Normal|]. destruct(mag_bounds x Normal)as[Lower _].
    rewrite mag_abs in Lower by exact O.
    assert (Exponent : (e x+255<=4)%Z).
    { apply(le_bpow radix2). change(bpow radix2 4)with 16;lra. }
    lia.
Qed.

Theorem normal_extended_residual_radius x c : valid x -> 0<qval x<=16 ->
  finite c -> 0<B c<=16 -> Rabs(qval x-B c)<=/8 ->
  Rabs(qval(add x (neg_q(q_float c))))<=/8.
Proof.
  intros X Range Fc Center Radius.
  destruct(q_float_ok c Fc)as[C Cv]. destruct(neg_any _ C)as[NC NCv].
  assert (Xm : Rabs(qval x)<=16)by(rewrite Rabs_pos_eq;lra).
  assert (Nm : Rabs(qval(neg_q(q_float c)))<=16).
  { rewrite NCv,Cv,Rabs_Ropp,Rabs_pos_eq;lra. }
  destruct(normal_small_q_grid x X ltac:(lra) Xm)as[Nx Ex].
  destruct(normal_small_q_grid _ NC ltac:(rewrite NCv,Cv;lra) Nm)as[Nc Ec].
  change(/8)with(bpow radix2 (-3)).
  apply normal_q_opposite_difference_radius;try(apply X||apply NC);try assumption;try lia.
  - rewrite(normal_positive_q_sign x X ltac:(lra)),
      (normal_negative_q_sign _ NC ltac:(rewrite NCv,Cv;lra));discriminate.
  - rewrite NCv,Cv;exact Radius.
Qed.

Theorem normal_q_compare_abs a b : valid a -> valid b ->
  match cmp_abs a b with
  | Eq => Rabs(qval a)=Rabs(qval b)
  | Lt => Rabs(qval a)<Rabs(qval b)
  | Gt => Rabs(qval b)<Rabs(qval a)
  end.
Proof.
  intros [Oa Na] [Ob Nb]. unfold cmp_abs.
  rewrite !is_zero_ok by(apply Oa||apply Ob).
  destruct(Z.eqb_spec(v(m a))0)as[Za|Za];destruct(Z.eqb_spec(v(m b))0)as[Zb|Zb].
  - rewrite(qval_zero a Za),(qval_zero b Zb);reflexivity.
  - rewrite(qval_zero a Za),Rabs_R0,<-mag_abs by exact Ob.
    destruct Nb as[Nb|Nb];[contradiction|].
    destruct(mag_bounds b Nb)as[Lower _];pose proof(bpow_gt_0 radix2(e b+255));lra.
  - rewrite(qval_zero b Zb),Rabs_R0,<-mag_abs by exact Oa.
    destruct Na as[Na|Na];[contradiction|].
    destruct(mag_bounds a Na)as[Lower _];pose proof(bpow_gt_0 radix2(e a+255));lra.
  - destruct Na as[Na|Na];[contradiction|]. destruct Nb as[Nb|Nb];[contradiction|].
    rewrite <-!mag_abs by assumption.
    destruct(Z.compare_spec(e a)(e b))as[E|Less|Greater].
    + rewrite cmp_ok by(apply Oa||apply Ob).
      unfold mag,F2R;cbn;rewrite E.
      destruct(Z.compare_spec(v(m a))(v(m b)))as[Equal|Less|Greater].
      * rewrite Equal;reflexivity.
      * apply Rmult_lt_compat_r;[apply bpow_gt_0|apply IZR_lt;exact Less].
      * apply Rmult_lt_compat_r;[apply bpow_gt_0|apply IZR_lt;exact Greater].
    + destruct(mag_bounds a Na)as[_ Upper],(mag_bounds b Nb)as[Lower _].
      assert(bpow radix2(e a+256)<=bpow radix2(e b+255))by(apply bpow_le;lia);lra.
    + destruct(mag_bounds b Nb)as[_ Upper],(mag_bounds a Na)as[Lower _].
      assert(bpow radix2(e b+256)<=bpow radix2(e a+255))by(apply bpow_le;lia);lra.
Qed.

