(** Logarithm of a central double-word probability: the proved ln high-word
    kernel, one rounded low/high division, and a first-order correction. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add RoundingConstant.
Require Import StageGappa LnFastValue Ln1pApprox NormalLogSensitivity NormalCenterFastTail.
Open Scope R_scope.

Definition normal_log_dw64 h l :=
  let '(a,b):=lf_ln_fast_value h in add_f64_64 a b (fdiv l h).

Theorem normal_log_dw_ieee h l : finite h -> finite l ->
  /8<=B h<=7/8 -> Rabs(B l)<=bpow radix2 (-54) ->
  let '(a,b):=normal_log_dw64 h l in
  finite a /\ finite b /\ B a=rndF(B a+B b) /\
  Rabs((B a+B b)-ln(B h+B l))<=bpow radix2 (-64)*Rabs(ln(B h))+bpow radix2 (-100).
Proof.
  intros Fh Fl H L.
  set(q:=B l/B h).
  assert(Q : Rabs q<=bpow radix2 (-51)).
  { unfold q,Rdiv;rewrite Rabs_mult,Rabs_Rinv,(Rabs_pos_eq(B h)) by lra.
    assert(Inv : 0<=/B h<=8)by(split;interval with(i_prec 80)).
    pose proof(Rabs_pos(B l));bpow_num_all;nra. }
  assert(Domain : bnd 1 (-51) q)by(unfold bnd;rewrite Rmult_1_l;exact Q).
  destruct(fdiv_bnd 1 (-51) l h Fl ltac:(lra)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)Domain)as[Fq [Qvalue Qbound]].
  fold q in Qvalue;unfold bnd in Qbound;rewrite Rmult_1_l in Qbound.
  pose proof(rnd_err_below q (-51)ltac:(lia)Q)as Division.
  rewrite <-Qvalue in Division;change(-51-54)%Z with(-105)%Z in Division.
  assert(Taylor : Rabs(ln(1+q)-q)<=bpow radix2 (-101)).
  { pose proof(ln1p_linear q ltac:(bpow_num_all;lra))as Remainder.
    eapply Rle_trans;[exact Remainder|].
    assert(Qsquare : q*q<=bpow radix2 (-51)^2).
    { apply Rabs_le_inv in Q;bpow_num_all;nra. }
    apply(Rmult_le_reg_r(1-Rabs q));[bpow_num_all;lra|].
    unfold Rdiv;rewrite Rmult_assoc,Rinv_l,Rmult_1_r by(bpow_num_all;lra).
    bpow_num_all;nra. }
  assert(Identity : ln(B h+B l)=ln(B h)+ln(1+q)).
  { replace(B h+B l)with(B h*(1+q))by(unfold q;field;lra).
    rewrite ln_mult;[reflexivity|lra|apply Rabs_le_inv in Q;bpow_num_all;lra]. }
  pose proof(lf_ln_fast_value_ok h Fh ltac:(lra))as Log.
  unfold normal_log_dw64;destruct(lf_ln_fast_value h)as[u v].
  destruct Log as[Fu [Fv [Norm [U [V LogError]]]]].
  assert(LogRange : -3<=ln(B h)<= -/8)by(split;interval with(i_prec 80)).
  assert(SumRange : Rabs(B u+B v+B(fdiv l h))<=4).
  { pose proof(Rabs_triang_inv(B u+B v)(ln(B h)))as Words.
    pose proof(Rabs_triang(B u+B v)(B(fdiv l h)))as Sum.
    rewrite(Rabs_left1(ln(B h)))in * by lra;bpow_num_all;nra. }
  assert(Bound : forall w,Rabs(B w)<=2048 -> bnd 1 11 (B w)).
  { intros w W;unfold bnd;rewrite Rmult_1_l;change(bpow radix2 11)with 2048;exact W. }
  destruct(add_f64_64_ok 1 11 u v (fdiv l h) Fu Fv Fq
    (Bound u ltac:(lra))(Bound v V)(Bound (fdiv l h) ltac:(bpow_num_all;lra))
    ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia))as[Fa [Fb Value]].
  pose proof(add_f64_dw(B u)(B v)(B(fdiv l h))(B_fmt u)(B_fmt v)(B_fmt _)Norm)as Normalized.
  pose proof(add_f64_ieee u v (fdiv l h)Fu Fv Fq Norm
    ltac:(eapply Rle_trans;[exact U|interval with(i_prec 80)])
    ltac:(eapply Rle_trans;[exact V|interval with(i_prec 80)])
    ltac:(eapply Rle_trans;[exact Qbound|interval with(i_prec 80)]))as Relative.
  rewrite <-Value in Normalized;destruct(add_f64_64 u v (fdiv l h))as[a b];cbn[fst snd]in *.
  destruct Relative as[_ [_ Relative]].
  assert(Nonzero : B u+B v+B(fdiv l h)<>0).
  { apply Rabs_le_inv in LogError,Qbound;rewrite(Rabs_left1(ln(B h)))in LogError by lra;bpow_num_all;lra. }
  assert(Evaluation : Rabs((B a+B b)-(B u+B v+B(fdiv l h)))<=bpow radix2 (-103)).
  { replace((B a+B b)-(B u+B v+B(fdiv l h)))with
      ((((B a+B b)-(B u+B v+B(fdiv l h)))/(B u+B v+B(fdiv l h)))*(B u+B v+B(fdiv l h)))by(field;exact Nonzero).
    rewrite Rabs_mult;pose proof(Rabs_pos(B u+B v+B(fdiv l h))).
    pose proof(Rabs_pos(((B a+B b)-(B u+B v+B(fdiv l h)))/(B u+B v+B(fdiv l h)))).
    unfold prec in Relative;change(- (53))%Z with(-53)%Z in Relative;bpow_num_all;nra. }
  repeat split;try assumption.
  rewrite Identity;replace((B a+B b)-(ln(B h)+ln(1+q)))with
    (((B a+B b)-(B u+B v+B(fdiv l h)))+((B u+B v)-ln(B h))+
     ((B(fdiv l h)-q)-(ln(1+q)-q)))by ring.
  eapply Rle_trans;[apply Rabs_triang|].
  eapply Rle_trans;[apply Rplus_le_compat;[apply Rabs_triang|apply Rabs_triang]|].
  rewrite Rabs_Ropp;bpow_num_all;lra.
Qed.
