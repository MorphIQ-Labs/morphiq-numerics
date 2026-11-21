(** Public tangent correct rounding. The Lefevre--Muller separation result
    is retained as an explicit hypothesis: revised August 2003, page 18,
    mantissa distance 2^-122 on [2^-25, atan 2]. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Bits.
From Q Require Import Q256 Q256Real.
From Binary64 Require Import Binary64Add IEEE64 RoundingTest.
From Interval Require Import Tactic.
Require Import ExpAccurate LnAccurate TrigInputContract TrigEntry TrigCorrectRounding
 TrigTanScreenConstants TrigTanScreen TrigTanAccurate TrigTanRounding TrigTanEntry.
Open Scope R_scope.

Lemma trig_tan_public_reference_floor x : finite x -> bpow radix2 (-63)<=Rabs(B x) ->
 bpow radix2 (-64)<=Rabs(tan(B x)).
Proof.
 intros F X.
 pose proof (trig_public_reference_floor x false F X) as S.
 pose proof (trig_public_reference_floor x true F X) as C.
 change (bpow radix2 (-64)<=Rabs(sin(B x))) in S.
 change (bpow radix2 (-64)<=Rabs(cos(B x))) in C.
 assert (CP:0<Rabs(cos(B x))) by (pose proof (bpow_gt_0 radix2 (-64));lra).
 assert (CN:cos(B x)<>0) by (intro Zero;rewrite Zero,Rabs_R0 in CP;lra).
 assert (Cu:Rabs(cos(B x))<=1) by (apply Rabs_le;apply COS_bound).
 unfold tan,Rdiv;rewrite Rabs_mult,Rabs_Rinv by exact CN.
 apply Rmult_le_reg_r with (Rabs(cos(B x)));[exact CP|].
 rewrite Rmult_assoc,Rinv_l,Rmult_1_r by lra.
 pose proof (bpow_gt_0 radix2 (-64));nra.
Qed.

Theorem trig_tan_public_finish_correct x d : finite x ->
 bpow radix2 (-63)<=Rabs(B x) -> bpow radix2 (-195)<d<=/2 ->
 midpoint_far (Rabs(tan(B x))) d ->
 finite(trig_tan_public_finish x) /\ B(trig_tan_public_finish x)=rndF(tan(B x)).
Proof.
 intros F X D Far.
 assert (AbsFinite:finite(b64_abs x)) by (apply trig_abs_finite;exact F).
 assert (AbsFloor:bpow radix2 (-63)<=B(b64_abs x)) by (rewrite B_abs;exact X).
 unfold trig_tan_public_finish,trig_tan_finish.
 destruct (trig_tan_decision (bits_of_b64(b64_abs x)) (trig_negative x)) as [y|] eqn:Decision.
 - pose proof (trig_tan_decision_correct (b64_abs x) (trig_negative x) y AbsFinite AbsFloor Decision) as Result.
   rewrite (trig_public_argument x F) in Result;exact Result.
 - pose proof (trig_tan_accurate_value_correct (b64_abs x) (trig_negative x) AbsFinite
    ltac:(rewrite B_abs;apply Rabs_pos)) as Value.
   cbv zeta in Value;rewrite (trig_public_argument x F) in Value.
   set (q:=trig_tan_accurate64 (bits_of_b64(b64_abs x)) (trig_negative x)) in *.
   set (v:=tan(B x)) in *.
   destruct Value as [Valid Error].
   pose proof (trig_tan_magnitude (b64_abs x) (trig_negative x) AbsFinite
    ltac:(rewrite B_abs;apply Rabs_pos)) as Mag.
   rewrite (trig_public_argument x F) in Mag;fold v in Mag.
   destruct (trig_tan_round q v Valid Mag Error) as [Y Round].
   unfold trig_tan_accurate_result;fold q;split;[exact Y|];rewrite Round.
   pose proof (trig_tan_public_reference_floor x F X) as Floor;fold v in Floor.
   assert (Positive:0<Rabs v) by (pose proof (bpow_gt_0 radix2 (-64));lra).
   apply rounds_as with d.
   + intro Zero;rewrite Zero,Rabs_R0 in Positive;lra.
   + pose proof (bpow_gt_0 radix2 (-195));lra.
   + exact Far.
   + apply Rle_lt_trans with (1:=Error).
     apply Rmult_lt_compat_r;[exact Positive|].
     assert (Half:bpow radix2 (-196)=bpow radix2 (-195)/2).
     { replace (-196)%Z with ((-195)+(-1))%Z by lia;rewrite bpow_plus;reflexivity. }
     rewrite Half;lra.
Qed.

Definition TrigTanLM : Prop := forall x,
 finite x -> bpow radix2 (-25)<=Rabs(B x)<=atan 2 ->
 midpoint_far (Rabs(tan(B x))) (bpow radix2 (-122)).

Theorem trig_tan_entry_correct x : TrigTanLM -> finite x ->
 (Rabs(B x)<=B trig_tan_is_x \/ bpow radix2 (-25)<=Rabs(B x)<=atan 2) ->
 finite(trig_tan_entry x) /\ B(trig_tan_entry x)=rndF(tan(B x)).
Proof.
 intros LM F Domain;unfold trig_tan_entry;rewrite F.
 destruct (trig_tan_identity x) eqn:Screen.
 - apply (proj1 (trig_tan_identity_correct x F)) in Screen.
   split;[exact F|symmetry;apply trig_tan_screen_round;[apply B_fmt|exact Screen]].
 - apply (proj2 (trig_tan_identity_correct x F)) in Screen.
   destruct Domain as [Small|Range];[exfalso;lra|].
   apply (trig_tan_public_finish_correct x (bpow radix2 (-122)) F).
   + apply Rle_trans with (bpow radix2 (-25));[apply bpow_le;lia|lra].
   + split;[apply bpow_lt;lia|interval].
   + apply LM;assumption.
Qed.
