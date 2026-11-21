(** The accurate sine/cosine series, for either sign of the Q256 remainder. *)
From Coq Require Import Reals ZArith Lia Lra Psatz Bool List.
From Flocq Require Import Core IEEE754.Bits.
From Q Require Import Q256 Q256Real QSpec Limbs LimbScan.
From Interval Require Import Tactic.
Require Import AsinTables AsinKernel AsinSinCos AsinFacts.
Import ListNotations.
Open Scope R_scope.

Lemma trig_square_neg a : Q256.mul (Q256.neg_q a) (Q256.neg_q a)=Q256.mul a a.
Proof.
  unfold Q256.neg_q. destruct (is_zero (Q256.m a)); [reflexivity|].
  unfold Q256.mul. cbn [Q256.m Q256.neg Q256.e]. destruct (Q256.neg a); reflexivity.
Qed.

Lemma trig_mul_neg_m a b :
  Q256.m (Q256.mul (Q256.neg_q a) b)=Q256.m (Q256.mul a b).
Proof.
  unfold Q256.neg_q. destruct (is_zero (Q256.m a)); [reflexivity|].
  unfold Q256.mul. cbn [Q256.m Q256.neg Q256.e].
  destruct (is_zero (Q256.m a)||is_zero (Q256.m b)); [reflexivity|].
  cbn [orb]. cbv zeta. destruct (Z.shiftr (nth 7 (mul_limbs (Q256.m a) (Q256.m b)) 0) 63 =? 1)%Z; reflexivity.
Qed.

Lemma trig_mul_neg_value a b : qval (Q256.mul (Q256.neg_q a) b)= -qval (Q256.mul a b).
Proof.
  unfold Q256.neg_q. destruct (is_zero (Q256.m a)) eqn:A.
  - unfold Q256.mul. rewrite A. cbn [orb]; rewrite (qval_zero Q256.zero eq_refl); ring.
  - unfold Q256.mul. cbn [Q256.m Q256.neg Q256.e]. rewrite A.
    destruct (is_zero (Q256.m b)); [cbn [orb]; rewrite (qval_zero Q256.zero eq_refl); ring|].
    cbn [orb]. cbv zeta. destruct (Z.shiftr (nth 7 (mul_limbs (Q256.m a) (Q256.m b)) 0) 63 =? 1)%Z;
      unfold qval,val,F2R; cbn [Q256.m Q256.neg Q256.e Fnum Fexp];
      destruct (Q256.neg a), (Q256.neg b); cbn [xorb negb]; rewrite ?opp_IZR; ring.
Qed.

Lemma trig_series_neg r :
  qval (fst (q_sin_cos (Q256.neg_q r)))= -qval (fst (q_sin_cos r)) /\
  snd (q_sin_cos (Q256.neg_q r))=snd (q_sin_cos r) /\
  Q256.m (fst (q_sin_cos (Q256.neg_q r)))=Q256.m (fst (q_sin_cos r)).
Proof.
  unfold q_sin_cos. rewrite trig_square_neg. cbn [fst snd].
  split; [apply trig_mul_neg_value|]. split; [reflexivity|apply trig_mul_neg_m].
Qed.

Theorem trig_series_error r : valid r -> Rabs (qval r)<=0.7854 ->
  valid (fst (q_sin_cos r)) /\ valid (snd (q_sin_cos r)) /\
  Rabs (qval (fst (q_sin_cos r))-sin (qval r)) <= bpow radix2 (-200)*Rabs (sin (qval r)) /\
  Rabs (qval (snd (q_sin_cos r))-cos (qval r)) <= bpow radix2 (-200)*Rabs (cos (qval r)).
Proof.
  intros V D. destruct (Rle_lt_dec 0 (qval r)) as [Pos|Neg].
  - rewrite (Rabs_pos_eq _ Pos) in D.
    destruct (q_sin_cos_error_strong r V ltac:(lra)) as [S [C [Es Ec]]].
    split; [exact S|]. split; [exact C|]. split.
    + apply Rle_trans with (bpow radix2 (-200)*sin (qval r)); [exact Es|].
      apply Rmult_le_compat_l; [apply bpow_ge_0|apply Rle_abs].
    + apply Rle_trans with (bpow radix2 (-200)*cos (qval r)); [exact Ec|].
      apply Rmult_le_compat_l; [apply bpow_ge_0|apply Rle_abs].
  - destruct (neg_any r V) as [Vn N].
    rewrite (Rabs_left _ Neg) in D.
    destruct (q_sin_cos_error_strong (Q256.neg_q r) Vn ltac:(rewrite N; lra)) as [S [C [Es Ec]]].
    destruct (trig_series_neg r) as [Sn [Cn Mn]].
    unfold valid in S. rewrite Mn in S. rewrite Cn in C.
    rewrite N,sin_neg,Sn in Es. rewrite N,cos_neg,Cn in Ec.
    replace (-qval (fst (q_sin_cos r))- -sin (qval r)) with
      (-(qval (fst (q_sin_cos r))-sin (qval r))) in Es by ring.
    rewrite Rabs_Ropp in Es.
    split; [exact S|]. split; [exact C|]. split.
    + apply Rle_trans with (bpow radix2 (-200)*(-sin (qval r))); [exact Es|].
      apply Rmult_le_compat_l; [apply bpow_ge_0|].
      rewrite <- (Rabs_Ropp (sin (qval r))). apply Rle_abs.
    + apply Rle_trans with (bpow radix2 (-200)*cos (qval r)); [exact Ec|].
      apply Rmult_le_compat_l; [apply bpow_ge_0|apply Rle_abs].
Qed.

Lemma trig_small_bounds x : Rabs x<=0.7854 ->
  0.89*Rabs x<=Rabs(sin x) /\ 0.69<=cos x.
Proof.
  intro D. pose proof (Rabs_pos x) as P. pose proof (Rabs_le_inv x _ D) as X.
  assert (Sq : x*x<=0.6169) by nra.
  pose proof (sin_taylor x ltac:(lra)) as S.
  pose proof (cos_taylor x ltac:(lra)) as [C _].
  assert (Tail : x*x*Rabs x/6<=0.11*Rabs x) by nra.
  pose proof (Rabs_triang (x-sin x) (sin x)) as T.
  replace (x-sin x+sin x) with x in T by ring.
  rewrite Rabs_minus_sym in T. split; lra.
Qed.

Lemma trig_lipschitz f df :
  (forall x, derivable_pt_lim f x (df x)) ->
  (forall x, Rabs (df x)<=1) ->
  forall a b, Rabs(f a-f b)<=Rabs(a-b).
Proof.
  intros D Bound.
  assert (Step : forall a b, a<b -> Rabs(f b-f a)<=Rabs(b-a)).
  { intros a b Lt. destruct (MVT_cor2 f df a b Lt (fun c _ => D c)) as [c [E _]].
    rewrite E,Rabs_mult. pose proof (Bound c). pose proof (Rabs_pos (b-a)); nra. }
  intros a b. destruct (Rtotal_order a b) as [Lt|[Eq|Gt]].
  - rewrite (Rabs_minus_sym (f a)),(Rabs_minus_sym a). apply Step; exact Lt.
  - subst b. rewrite !Rminus_diag_eq,!Rabs_R0 by reflexivity. lra.
  - apply Step; exact Gt.
Qed.
Lemma trig_sin_lipschitz a b : Rabs(sin a-sin b)<=Rabs(a-b).
Proof. apply (trig_lipschitz sin cos); [apply derivable_pt_lim_sin|].
  intro x; apply Rabs_le; apply COS_bound. Qed.
Lemma trig_cos_lipschitz a b : Rabs(cos a-cos b)<=Rabs(a-b).
Proof. apply (trig_lipschitz cos (fun x=> -sin x)); [apply derivable_pt_lim_cos|].
  intro x; rewrite Rabs_Ropp; apply Rabs_le; apply SIN_bound. Qed.

(** Propagate the relative reduction budget through either series. The
    sine lower bound accounts for remainders arbitrarily close to zero. *)
Theorem trig_series_composed r t : valid r -> Rabs(qval r)<=0.7854 -> Rabs t<=0.7854 ->
  Rabs(qval r-t)<=bpow radix2 (-199)*Rabs t ->
  valid (fst (q_sin_cos r)) /\ valid (snd (q_sin_cos r)) /\
  Rabs(qval(fst(q_sin_cos r))-sin t)<=bpow radix2 (-198)*Rabs(sin t) /\
  Rabs(qval(snd(q_sin_cos r))-cos t)<=bpow radix2 (-198)*Rabs(cos t).
Proof.
  intros V D T Reduction.
  destruct (trig_series_error r V D) as [Vs [Vc [Es Ec]]].
  destruct (trig_small_bounds t T) as [Sin Cos].
  assert (CosAbs : 0.69<=Rabs(cos t)) by (pose proof (Rle_abs (cos t)); lra).
  pose proof (trig_sin_lipschitz (qval r) t) as Sl.
  pose proof (trig_cos_lipschitz (qval r) t) as Cl.
  set (eps := bpow radix2 (-200)) in *.
  assert (Ep : 0<eps) by apply bpow_gt_0.
  assert (Small : eps<=0.01) by (unfold eps; interval).
  assert (E199 : bpow radix2 (-199)=2*eps).
  { unfold eps. replace (-199)%Z with (1+(-200))%Z by lia. rewrite bpow_plus. reflexivity. }
  assert (E198 : bpow radix2 (-198)=4*eps).
  { unfold eps. replace (-198)%Z with (2+(-200))%Z by lia. rewrite bpow_plus. reflexivity. }
  rewrite E199 in Reduction. rewrite E198.
  assert (ST : Rabs(sin(qval r))<=Rabs(sin t)+2*eps*Rabs t).
  { pose proof (Rabs_triang (sin(qval r)-sin t) (sin t)) as H.
    replace (sin(qval r)-sin t+sin t) with (sin(qval r)) in H by ring. lra. }
  assert (CT : Rabs(cos(qval r))<=Rabs(cos t)+2*eps*Rabs t).
  { pose proof (Rabs_triang (cos(qval r)-cos t) (cos t)) as H.
    replace (cos(qval r)-cos t+cos t) with (cos(qval r)) in H by ring. lra. }
  assert (Scale : forall u, 0<=u ->
    eps*(u+2*eps*Rabs t)+2*eps*Rabs t<=4*eps*u ->
    forall z a, Rabs(z-a)<=eps*Rabs a -> Rabs a<=u+2*eps*Rabs t ->
    forall b, Rabs(a-b)<=2*eps*Rabs t -> Rabs(z-b)<=4*eps*u).
  { intros u U Budget z a Err Mag b Delta.
    pose proof (Rabs_triang (z-a) (a-b)) as H. replace (z-a+(a-b)) with (z-b) in H by ring.
    assert (Scaled : eps*Rabs a<=eps*(u+2*eps*Rabs t)) by nra. lra. }
  split; [exact Vs|]. split; [exact Vc|]. split.
  - apply (Scale (Rabs(sin t))) with (a:=sin(qval r)); try apply Rabs_pos; try assumption; try lra.
    assert (Cost : (2+2*eps)*Rabs t<=3*Rabs(sin t)).
    { assert (P : 0<=Rabs t) by apply Rabs_pos. nra. }
    nra.
  - apply (Scale (Rabs(cos t))) with (a:=cos(qval r)); try apply Rabs_pos; try assumption; try lra.
    assert (Cost : (2+2*eps)*Rabs t<=3*Rabs(cos t)).
    { assert (P : 0<=Rabs t) by apply Rabs_pos. nra. }
    nra.
Qed.

Require Import TrigReduction TrigWindow.
From Binary64 Require Import IEEE64 Encodings.

(** The actual binary64 reduction followed by the shared Q256 series. This
    theorem is before quadrant selection and the final binary64 rounding. *)
Theorem trig_reduced_series_correct x : finite x -> 0<=B x ->
  exists n q, trig_reduce64 (bits_of_b64 x)=((n mod 4)%Z,q) /\
    valid (fst(q_sin_cos q)) /\ valid (snd(q_sin_cos q)) /\
    Rabs(qval(fst(q_sin_cos q))-sin(B x-IZR n*(PI/2))) <=
      bpow radix2 (-198)*Rabs(sin(B x-IZR n*(PI/2))) /\
    Rabs(qval(snd(q_sin_cos q))-cos(B x-IZR n*(PI/2))) <=
      bpow radix2 (-198)*Rabs(cos(B x-IZR n*(PI/2))).
Proof.
  intros F X. destruct (trig_reduce_correct x F X) as [n [q [Eq [V [Q [Near Err]]]]]].
  exists n,q. split; [exact Eq|]. apply trig_series_composed; try exact V.
  - apply Rle_trans with (PI/4); [exact Q|apply quarter_pi_le].
  - assert (Pi : 0<PI) by exact PI_RGT_0.
    assert (Identity : B x-IZR n*(PI/2)=(B x*(2/PI)-IZR n)*(PI/2)) by (field; lra).
    rewrite Identity,Rabs_mult,(Rabs_pos_eq (PI/2)) by lra.
    assert (A : Rabs(B x*(2/PI)-IZR n)<=/2) by (apply Rabs_le; lra).
    pose proof quarter_pi_le. nra.
  - replace (bpow radix2 (-199)) with (/2^199) by (rewrite pow_IZR; reflexivity). exact Err.
Qed.
