(** Correct rounding at the public entries. The published Lefevre--Muller
    midpoint-distance results are explicit hypotheses, not new axioms or
    conclusions inferred from sampled oracle data. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Bits.
From Q Require Import Q256 Q256Real.
From Binary64 Require Import Binary64Add IEEE64 RoundingTest.
From Interval Require Import Tactic.
Require Import ExpAccurate LnAccurate TrigQuadrant TrigRounding TrigInputContract
 TrigFastSelection TrigFastDecision TrigScreenConstants TrigSinScreen TrigCosScreen TrigEntry.
Open Scope R_scope.

Lemma trig_public_reference_floor x (cosine:bool) : finite x -> bpow radix2 (-63)<=Rabs(B x) ->
 bpow radix2 (-64)<=Rabs(if cosine then cos(B x) else sin(B x)).
Proof.
 intros F X.
 pose proof (trig_fast64_correct (b64_abs x) (trig_negative x) cosine
  (trig_abs_finite x F) ltac:(rewrite B_abs;exact X)) as Result.
 cbv zeta in Result. destruct (trig_fast64 (bits_of_b64(b64_abs x)) (trig_negative x) cosine) as [h l].
 destruct Result as [_ [_ [_ [_ Floor]]]].
 rewrite (trig_public_argument x F) in Floor;exact Floor.
Qed.

Theorem trig_public_finish_correct x (cosine:bool) d : finite x ->
 bpow radix2 (-63)<=Rabs(B x) -> bpow radix2 (-197)<d<=/2 ->
 midpoint_far (Rabs(if cosine then cos(B x) else sin(B x))) d ->
 finite(trig_public_finish x cosine) /\
 B(trig_public_finish x cosine)=rndF(if cosine then cos(B x) else sin(B x)).
Proof.
 intros F X D Far.
 assert (AbsFinite:finite(b64_abs x)) by (apply trig_abs_finite;exact F).
 assert (AbsFloor:bpow radix2 (-63)<=B(b64_abs x)) by (rewrite B_abs;exact X).
 unfold trig_public_finish,trig_finish.
 destruct (trig_fast_decision (bits_of_b64(b64_abs x)) (trig_negative x) cosine) as [y|] eqn:Decision.
 - pose proof (trig_fast_decision_correct (b64_abs x) (trig_negative x) cosine y AbsFinite AbsFloor Decision) as Result.
   rewrite (trig_public_argument x F) in Result;exact Result.
 - pose proof (trig_accurate_value_correct (b64_abs x) (trig_negative x) cosine AbsFinite
    ltac:(rewrite B_abs;apply Rabs_pos)) as Value.
   cbv zeta in Value. rewrite (trig_public_argument x F) in Value.
   set (q:=trig_accurate64 (bits_of_b64(b64_abs x)) (trig_negative x) cosine) in *.
   set (v:=if cosine then cos(B x) else sin(B x)) in *.
   destruct Value as [Valid Error].
   assert (Mag:Rabs v<=1) by (unfold v;destruct cosine;apply Rabs_le;[apply COS_bound|apply SIN_bound]).
   destruct (trig_accurate_round q v Valid Mag Error) as [Y Round].
   unfold trig_accurate_result;fold q;split;[exact Y|];rewrite Round.
   pose proof (trig_public_reference_floor x cosine F X) as Floor;fold v in Floor.
   assert (Positive:0<Rabs v) by (pose proof (bpow_gt_0 radix2 (-64));lra).
   apply rounds_as with d.
   + intro Zero;rewrite Zero,Rabs_R0 in Positive;lra.
   + pose proof (bpow_gt_0 radix2 (-197));lra.
   + exact Far.
   + apply Rle_lt_trans with (1:=Error).
     apply Rmult_lt_compat_r;[exact Positive|].
     assert (Half:bpow radix2 (-198)=bpow radix2 (-197)/2).
     { replace (-198)%Z with ((-197)+(-1))%Z by lia;rewrite bpow_plus;reflexivity. }
     rewrite Half;lra.
Qed.

Definition TrigSinLM : Prop := forall x,
 finite x -> bpow radix2 (-24)<=Rabs(B x)<=2+4675/8192 ->
 midpoint_far (Rabs(sin(B x))) (bpow radix2 (-126)).
Definition TrigCosLM : Prop := forall x,
 finite x -> bpow radix2 (-25)<=Rabs(B x)<=12867/8192 ->
 midpoint_far (Rabs(cos(B x))) (bpow radix2 (-142)).

Theorem trig_sin_entry_correct x : TrigSinLM -> finite x ->
 (Rabs(B x)<=B trig_sin_is_x \/ bpow radix2 (-24)<=Rabs(B x)<=2+4675/8192) ->
 finite(trig_sin_entry x) /\ B(trig_sin_entry x)=rndF(sin(B x)).
Proof.
 intros LM F Domain;unfold trig_sin_entry;rewrite F.
 destruct (trig_sin_identity x) eqn:Screen.
 - apply (proj1 (trig_sin_identity_correct x F)) in Screen.
   split;[exact F|symmetry;apply trig_sin_screen_round;[apply B_fmt|exact Screen]].
 - apply (proj2 (trig_sin_identity_correct x F)) in Screen.
   destruct Domain as [Small|Range];[exfalso;lra|].
   apply (trig_public_finish_correct x false (bpow radix2 (-126)) F).
   + apply Rle_trans with (bpow radix2 (-24));[apply bpow_le;lia|lra].
   + split;[apply bpow_lt;lia|interval].
   + apply LM;assumption.
Qed.
Theorem trig_cos_entry_correct x : TrigCosLM -> finite x -> Rabs(B x)<=12867/8192 ->
 finite(trig_cos_entry x) /\ B(trig_cos_entry x)=rndF(cos(B x)).
Proof.
 intros LM F Domain;unfold trig_cos_entry;rewrite F.
 destruct (trig_cos_screen x) eqn:Screen.
 - apply (proj1 (trig_cos_screen_correct x F)) in Screen.
   apply trig_cos_abs_small_correct;assumption.
 - apply (proj2 (trig_cos_screen_correct x F)) in Screen.
   apply (trig_public_finish_correct x true (bpow radix2 (-142)) F).
   + apply Rle_trans with (2:=Screen);apply bpow_le;lia.
   + split;[apply bpow_lt;lia|interval].
   + apply LM;[exact F|split;assumption].
Qed.

Theorem trig_public_finish_decided x (cosine:bool) y : finite x -> bpow radix2 (-63)<=Rabs(B x) ->
 trig_fast_decision (bits_of_b64(b64_abs x)) (trig_negative x) cosine=Some y ->
 trig_public_finish x cosine=y /\ finite y /\ B y=rndF(if cosine then cos(B x) else sin(B x)).
Proof.
 intros F X Decision.
 split;[unfold trig_public_finish,trig_finish;rewrite Decision;reflexivity|].
 pose proof (trig_fast_decision_correct (b64_abs x) (trig_negative x) cosine y
  (trig_abs_finite x F) ltac:(rewrite B_abs;exact X) Decision) as Result.
 rewrite (trig_public_argument x F) in Result;exact Result.
Qed.
