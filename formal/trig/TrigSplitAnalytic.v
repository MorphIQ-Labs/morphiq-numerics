(** Effect of the proved Q256 split error on the exact sine and cosine.
    The allowance is the [er] input to the reconstruction certificates. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
Require Import TrigAccurate TrigError.
Open Scope R_scope.

Theorem trig_split_analytic_error r z : Rabs r<=0.785399 ->
 Rabs(z-r)<=(3/2)*bpow radix2 (-105)*Rabs r ->
 Rabs(sin z-sin r)<=bpow radix2 (-104)*Rabs(sin r) /\
 Rabs(cos z-cos r)<=bpow radix2 (-104)*Rabs(cos r).
Proof.
 intros R Split. destruct (trig_small_bounds r ltac:(lra)) as [Sin Cos].
 pose proof (trig_sin_lipschitz z r) as S.
 pose proof (trig_cos_lipschitz z r) as C.
 assert (Budget:bpow radix2 (-104)=2*bpow radix2 (-105)).
 { replace (-104)%Z with (1+(-105))%Z by lia;rewrite bpow_plus;reflexivity. }
 rewrite Budget. pose proof (bpow_ge_0 radix2 (-105)) as E.
 pose proof (Rabs_pos r) as P. pose proof (Rle_abs(cos r)) as CA.
 split;nra.
Qed.

Theorem trig_split_analytic_factors r z : Rabs r<=0.785399 ->
 Rabs(z-r)<=(3/2)*bpow radix2 (-105)*Rabs r ->
 (exists es, Rabs es<=bpow radix2 (-104) /\ sin z=sin r*(1+es)) /\
 (exists ec, Rabs ec<=bpow radix2 (-104) /\ cos z=cos r*(1+ec)).
Proof.
 intros R Split. destruct (trig_split_analytic_error r z R Split) as [S C].
 split;apply trig_relative_factor;try apply bpow_ge_0;assumption.
Qed.

Lemma trig_split_sine_nonzero r z : Rabs r<=0.785399 -> r<>0 ->
 Rabs(z-r)<=(3/2)*bpow radix2 (-105)*Rabs r -> sin z<>0.
Proof.
 intros R Nonzero Split Zero.
 destruct (trig_small_bounds r ltac:(lra)) as [Sin _].
 destruct (trig_split_analytic_error r z R Split) as [Error _].
 rewrite Zero,Rminus_0_l,Rabs_Ropp in Error.
 assert (Tiny:bpow radix2 (-104)<1) by interval.
 pose proof (Rabs_pos_lt r Nonzero). nra.
Qed.
