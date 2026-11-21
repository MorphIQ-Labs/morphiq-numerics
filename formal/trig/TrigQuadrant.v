(** Analytic quadrant identities for nonnegative reduction indices. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
Open Scope R_scope.

Definition quadrant_sin (k:Z) r :=
  match k with 0%Z=>sin r | 1%Z=>cos r | 2%Z=> -sin r | _=> -cos r end.
Definition quadrant_cos (k:Z) r :=
  match k with 0%Z=>cos r | 1%Z=> -sin r | 2%Z=> -cos r | _=>sin r end.

Lemma trig_period_nonnegative (f:R->R) :
  (forall x k, f(x+2*INR k*PI)=f x) ->
  forall x k, (0<=k)%Z -> f(x+2*IZR k*PI)=f x.
Proof.
  intros Period x k K. replace (IZR k) with (INR (Z.to_nat k)).
  - apply Period.
  - rewrite INR_IZR_INZ,Z2Nat.id by exact K. reflexivity.
Qed.

Theorem trig_analytic_quadrant n r : (0<=n)%Z ->
  sin(r+IZR n*(PI/2))=quadrant_sin (n mod 4) r /\
  cos(r+IZR n*(PI/2))=quadrant_cos (n mod 4) r.
Proof.
  intro N. pose proof (Z.div_mod n 4 ltac:(lia)) as Div.
  assert (Q : (0<=n/4)%Z) by (apply Z.div_pos; lia).
  assert (Id : r+IZR n*(PI/2)=r+IZR(n mod 4)*(PI/2)+2*IZR(n/4)*PI).
  { replace n with (4*(n/4)+n mod 4)%Z at 1 by lia. rewrite plus_IZR,mult_IZR. change (IZR 4) with 4. field. }
  rewrite Id,(trig_period_nonnegative sin sin_period _ _ Q),
    (trig_period_nonnegative cos cos_period _ _ Q).
  pose proof (Z.mod_pos_bound n 4 ltac:(lia)) as K.
  assert (Cases : (n mod 4=0 \/ n mod 4=1 \/ n mod 4=2 \/ n mod 4=3)%Z) by lia.
  destruct Cases as [C|[C|[C|C]]]; rewrite C; cbn [quadrant_sin quadrant_cos].
  - replace (r+IZR 0*(PI/2)) with r by (simpl; field). auto.
  - replace (r+IZR 1*(PI/2)) with (r+PI/2) by (simpl; field).
    rewrite sin_plus,cos_plus,sin_PI2,cos_PI2. split; ring.
  - replace (r+IZR 2*(PI/2)) with (r+PI) by (simpl; field).
    rewrite sin_plus,cos_plus,sin_PI,cos_PI. split; ring.
  - replace (r+IZR 3*(PI/2)) with ((r+PI)+PI/2) by (simpl; field).
    rewrite !sin_plus,!cos_plus,!sin_plus,sin_PI2,cos_PI2,sin_PI,cos_PI. split; ring.
Qed.

Lemma trig_nearest_nonnegative x n : 0<=x ->
  -/2<x*(2/PI)-IZR n</2 -> (0<=n)%Z.
Proof.
  intros X Near. assert (Pi:0<PI) by exact PI_RGT_0.
  assert (Y:0<=x*(2/PI)).
  { apply Rmult_le_pos; [exact X|]. apply Rlt_le,Rdiv_lt_0_compat; lra. }
  destruct (Z_le_gt_dec 0 n); [assumption|].
  assert (Low:IZR n<= -1).
  { change (IZR n<=IZR (-1)). apply IZR_le; lia. }
  exfalso; lra.
Qed.

From Coq Require Import Bool.
From Q Require Import Q256 Q256Real.

(** Reduced::select: cosine shifts the quadrant by one; the original
    argument sign changes sine only. *)
Definition trig_selection (k:Z) (negative cosine:bool) : bool*bool :=
  let quadrant:=Z.land (k+if cosine then 1 else 0) 3 in
  (Z.odd quadrant,xorb (Z.geb quadrant 2) (andb (negb cosine) negative)).
Definition trig_selected k negative cosine s c :=
  let '(use_cos,negate):=trig_selection k negative cosine in
  let y:=if use_cos then c else s in if negate then Q256.neg_q y else y.
Definition trig_selected_real k negative cosine r :=
  let '(use_cos,negate):=trig_selection k negative cosine in
  let y:=if use_cos then cos r else sin r in if negate then -y else y.

Lemma trig_selected_bound k negative cosine s c r eps :
  valid s -> valid c ->
  Rabs(qval s-sin r)<=eps*Rabs(sin r) ->
  Rabs(qval c-cos r)<=eps*Rabs(cos r) ->
  valid(trig_selected k negative cosine s c) /\
  Rabs(qval(trig_selected k negative cosine s c)-trig_selected_real k negative cosine r) <=
    eps*Rabs(trig_selected_real k negative cosine r).
Proof.
  intros Vs Vc Es Ec. unfold trig_selected,trig_selected_real.
  destruct (trig_selection k negative cosine) as [choose negate].
  destruct choose,negate; cbn; try (split; assumption).
  - destruct (neg_any c Vc) as [V E]. split; [exact V|]. rewrite E.
    replace (-qval c- -cos r) with (-(qval c-cos r)) by ring.
    rewrite !Rabs_Ropp; exact Ec.
  - destruct (neg_any s Vs) as [V E]. split; [exact V|]. rewrite E.
    replace (-qval s- -sin r) with (-(qval s-sin r)) by ring.
    rewrite !Rabs_Ropp; exact Es.
Qed.

Lemma trig_selection_analytic n r negative cosine : (0<=n)%Z ->
  trig_selected_real (n mod 4) negative cosine r =
    let x:=r+IZR n*(PI/2) in
    if cosine then cos(if negative then -x else x) else sin(if negative then -x else x).
Proof.
  intro N. destruct (trig_analytic_quadrant n r N) as [S C]. cbv zeta.
  pose proof (Z.mod_pos_bound n 4 ltac:(lia)) as K.
  assert (Cases : (n mod 4=0 \/ n mod 4=1 \/ n mod 4=2 \/ n mod 4=3)%Z) by lia.
  destruct negative,cosine; rewrite ?sin_neg,?cos_neg,?S,?C;
    destruct Cases as [H|[H|[H|H]]]; rewrite H;
    unfold trig_selected_real;
    match goal with |- context[trig_selection ?k ?a ?b] =>
      let value := eval vm_compute in (trig_selection k a b) in
      change (trig_selection k a b) with value
    end;
    cbn [quadrant_sin quadrant_cos]; ring.
Qed.

From Flocq Require Import Core IEEE754.Bits.
Require Import AsinKernel AsinFacts TrigAccurate TrigReduction TrigWindow.
From Binary64 Require Import IEEE64.

Definition trig_accurate64 bits negative cosine :=
  let '(k,q):=trig_reduce64 bits in
  let '(s,c):=q_sin_cos q in trig_selected k negative cosine s c.

Theorem trig_accurate_value_correct x negative cosine : finite x -> 0<=B x ->
  let q:=trig_accurate64 (bits_of_b64 x) negative cosine in
  let v:=if cosine then cos(if negative then -B x else B x)
                    else sin(if negative then -B x else B x) in
  valid q /\ Rabs(qval q-v)<=bpow radix2 (-198)*Rabs v.
Proof.
  intros F X. cbv zeta.
  destruct (trig_reduce_correct x F X) as [n [q [Eq [V [Q [Near Err]]]]]].
  pose proof (trig_nearest_nonnegative (B x) n X Near) as N.
  set (t:=B x-IZR n*(PI/2)).
  assert (Range:Rabs t<=0.7854).
  { assert (Pi:0<PI) by exact PI_RGT_0.
    assert (Id:t=(B x*(2/PI)-IZR n)*(PI/2)) by (unfold t; field; lra).
    rewrite Id,Rabs_mult,(Rabs_pos_eq (PI/2)) by lra.
    assert (A:Rabs(B x*(2/PI)-IZR n)<=/2) by (apply Rabs_le; lra).
    pose proof quarter_pi_le; nra. }
  assert (E:Rabs(qval q-t)<=bpow radix2 (-199)*Rabs t).
  { replace (bpow radix2 (-199)) with (/2^199) by (rewrite pow_IZR; reflexivity). exact Err. }
  destruct (trig_series_composed q t V ltac:(pose proof quarter_pi_le; lra) Range E)
    as [Vs [Vc [Es Ec]]].
  unfold trig_accurate64. rewrite Eq.
  destruct (q_sin_cos q) as [s c] eqn:Pair. cbn [fst snd] in Vs,Vc,Es,Ec.
  pose proof (trig_selected_bound (n mod 4) negative cosine s c t
    (bpow radix2 (-198)) Vs Vc Es Ec) as Bound.
  rewrite (trig_selection_analytic n t negative cosine N) in Bound. cbv zeta in Bound.
  replace (t+IZR n*(PI/2)) with (B x) in Bound by (unfold t; ring).
  exact Bound.
Qed.
