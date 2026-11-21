(** Reduction, quotient and rounding decision for the scalar fast tangent. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Bits.
From Q Require Import Q256 Q256Real.
From Binary64 Require Import Binary64Add IEEE64 Encodings RoundingTest RoundingDecisionDomain.
From Interval Require Import Tactic.
Require Import TrigFast TrigTanFast TrigFastDomain TrigTanDomain TrigTanAccurate
 TrigAccurate TrigQuadrant TrigWindow TrigInputContract.
Open Scope R_scope.

Definition trig_tan_fast64 bits negative :=
 let '(k,q):=trig_reduce64 bits in trig_tan_fast q k negative.
Definition trig_tan_eps : f64 := b64_of_bits 4336966441157787652.
Lemma trig_tan_eps_finite : finite trig_tan_eps.
Proof. exact (bits_finite 4336966441157787652 _ _ _ eq_refl). Qed.
Lemma trig_tan_eps_value : B trig_tan_eps=4503599627370500/2^112.
Proof. exact (bits_val 4336966441157787652 false 4503599627370500 112 eq_refl). Qed.

Lemma trig_tan_reference_floor k negative t :
 bpow radix2 (-63)<=Rabs t<=0.785399 ->
 bpow radix2 (-64)<=Rabs(trig_tan_real k negative t).
Proof.
 intros [Lower Upper]. destruct (trig_small_bounds t ltac:(lra)) as [S C].
 assert (Sl:bpow radix2 (-64)<=Rabs(sin t)).
 { assert (Budget:bpow radix2 (-64)<=0.89*bpow radix2 (-63)) by interval. nra. }
 assert (Cl:bpow radix2 (-64)<=Rabs(cos t)).
 { assert (Budget:bpow radix2 (-64)<=0.69) by
     (apply Rle_trans with (bpow radix2 (-1));[apply bpow_le;lia|change (/2<=0.69);lra]). pose proof (Rle_abs (cos t));lra. }
 assert (Su:Rabs(sin t)<=1) by (apply Rabs_le;apply SIN_bound).
 assert (Cu:Rabs(cos t)<=1) by (apply Rabs_le;apply COS_bound).
 assert (Ratio:forall n d, bpow radix2 (-64)<=Rabs n -> bpow radix2 (-64)<=Rabs d<=1 ->
   bpow radix2 (-64)<=Rabs(n/d)).
 { intros n d N [D DU].
   assert (DP:0<Rabs d) by (pose proof (bpow_gt_0 radix2 (-64));lra).
   assert (DN:d<>0) by (intro Zero;rewrite Zero,Rabs_R0 in DP;lra).
   unfold Rdiv. rewrite Rabs_mult,Rabs_Rinv by exact DN.
   apply Rmult_le_reg_r with (Rabs d);[exact DP|].
   rewrite Rmult_assoc,Rinv_l,Rmult_1_r by lra.
   pose proof (bpow_gt_0 radix2 (-64));nra. }
 unfold trig_tan_real. destruct (xorb (Z.odd k) negative);rewrite ?Rabs_Ropp;
 unfold trig_tan_num,trig_tan_den;destruct (Z.odd k);apply Ratio;try assumption;split;assumption.
Qed.

Theorem trig_tan_fast64_correct x negative zh zl : finite x -> bpow radix2 (-63)<=B x ->
 trig_tan_fast64 (bits_of_b64 x) negative=Some(zh,zl) ->
 let v:=tan(if negative then -B x else B x) in
 finite zh /\ finite zl /\ Rabs(B zh)<=bpow radix2 926 /\ Rabs(B zl)<=bpow radix2 926 /\
 bpow radix2 (-64)<=Rabs v /\ Rabs(B zh+B zl-v)<=bpow radix2 (-60)*Rabs v.
Proof.
 intros F X. cbv zeta. unfold trig_tan_fast64.
 destruct (trig_reduce_fast_domain x F X) as [n [q [Eq [V [Q [T [Near Reduction]]]]]]].
 rewrite Eq. intro Accepted.
 set (t:=B x-IZR n*(PI/2)) in *.
 assert (NZ:t<>0) by (intro Zero;rewrite Zero,Rabs_R0 in T;pose proof (bpow_gt_0 radix2 (-63));lra).
 pose proof (trig_tan_fast_composed q (n mod 4) negative t zh zl V Q (proj2 T) NZ Reduction Accepted) as Fast.
 pose proof (trig_tan_reference_floor (n mod 4) negative t T) as Lower.
 assert (Xp:0<=B x) by (pose proof (bpow_gt_0 radix2 (-63));lra).
 pose proof (trig_nearest_nonnegative (B x) n Xp Near) as N.
 pose proof (trig_tan_denominator_bound x n F Xp Near) as Den.
 cbv zeta in Den. fold t in Den.
 assert (DN:trig_tan_den (n mod 4) (sin t) (cos t)<>0).
 { intro Zero;rewrite Zero,Rabs_R0 in Den;pose proof (bpow_gt_0 radix2 (-63));lra. }
 rewrite (trig_tan_analytic n t negative N DN) in Fast,Lower.
 replace (t+IZR n*(PI/2)) with (B x) in Fast,Lower by (unfold t;ring).
 destruct Fast as [H [L [Bh [Bl Error]]]].
 split;[exact H|]. split;[exact L|]. split;[exact Bh|]. split;[exact Bl|]. split;assumption.
Qed.

Theorem trig_tan_fast_decision_correct x negative h l y :
 finite x -> bpow radix2 (-63)<=B x ->
 trig_tan_fast64 (bits_of_b64 x) negative=Some(h,l) ->
 decide_with h l trig_tan_eps=Some y ->
 finite y /\ B y=rndF(tan(if negative then -B x else B x)).
Proof.
 intros F X Fast Decision.
 destruct (trig_tan_fast64_correct x negative h l F X Fast) as [H [L [Bh [Bl [Lower Error]]]]].
 assert (E:bpow radix2 (-80)<=bpow radix2 (-60)<=bpow radix2 (-60)) by (split;[apply bpow_le;lia|apply Rle_refl]).
 assert (EPS:bpow radix2 (-60)*(1+bpow radix2 (-50))<=B trig_tan_eps<=1).
 { rewrite trig_tan_eps_value. split;interval with (i_prec 220). }
 rewrite Rabs_minus_sym in Error.
 destruct (decision_quotient_ok h l trig_tan_eps _ (bpow radix2 (-60)) y
 H L trig_tan_eps_finite Bh Bl E EPS Lower Error Decision) as [Eq Round].
 subst y. split;[exact H|symmetry;exact Round].
Qed.
