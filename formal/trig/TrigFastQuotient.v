(** Error composition for the fast tangent quotient. The two reconstructed
    functions have relative error 2^-62; checked division contributes the
    published 15u^2+56u^3. The resulting budget is 2^-60. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Binary64 Require Import Binary64Add IEEE64 CheckedDivision.
From Interval Require Import Tactic.
Require Import TrigError StageGappa.
Open Scope R_scope.

Lemma trig_fast_division_budget :
 15*bpow radix2 (-prec)^2+56*bpow radix2 (-prec)^3 <=970*bpow radix2 (-112).
Proof. unfold prec. bpow_num_all. interval with (i_prec 220). Qed.

Lemma trig_fast_quotient_budget a b d :
 Rabs a<=bpow radix2 (-62) -> Rabs b<=bpow radix2 (-62) ->
 Rabs d<=970*bpow radix2 (-112) ->
 Rabs((1+a)/(1+b)*(1+d)-1)<=bpow radix2 (-60).
Proof.
 intros A B D. apply Rabs_le_inv in A,B,D.
 bpow_num_all. apply Rabs_le;split;interval with (i_prec 220).
Qed.

Theorem trig_checked_quotient_error nh nl dh dl zh zl nv dv :
 nv<>0 -> dv<>0 ->
 Rabs(B nh+B nl-nv)<=bpow radix2 (-62)*Rabs nv ->
 Rabs(B dh+B dl-dv)<=bpow radix2 (-62)*Rabs dv ->
 checked_divide nh nl dh dl=Some(zh,zl) ->
 finite zh /\ finite zl /\ Rabs(B zh)<=bpow radix2 926 /\ Rabs(B zl)<=bpow radix2 926 /\
 Rabs(B zh+B zl-nv/dv)<=bpow radix2 (-60)*Rabs(nv/dv).
Proof.
 intros N D En Ed Accepted.
 destruct (checked_divide_sound _ _ _ _ _ _ Accepted) as [Fh [Fl [Div [Bh Bl]]]].
 destruct (trig_relative_factor (B nh+B nl) nv _ (bpow_ge_0 _ _) En) as [a [A Na]].
 destruct (trig_relative_factor (B dh+B dl) dv _ (bpow_ge_0 _ _) Ed) as [b [Eb Db]].
 assert (Small:bpow radix2 (-62)<1) by (change 1 with (bpow radix2 0);apply bpow_lt;lia).
 assert (Pa:0<1+a) by (pose proof (Rabs_le_inv _ _ A);lra).
 assert (Pb:0<1+b) by (pose proof (Rabs_le_inv _ _ Eb);lra).
 set (q:=(B nh+B nl)/(B dh+B dl)) in *.
 assert (Q:q<>0).
 { unfold q. rewrite Na,Db. apply Rmult_integral_contrapositive_currified.
   - apply Rmult_integral_contrapositive_currified;[exact N|lra].
   - apply Rinv_neq_0_compat. apply Rmult_integral_contrapositive_currified;[exact D|lra]. }
 set (d:=(B zh+B zl-q)/q) in *.
 assert (Result:B zh+B zl=q*(1+d)) by (unfold d;field;exact Q).
 assert (De:Rabs d<=970*bpow radix2 (-112)) by (eapply Rle_trans;[exact Div|exact trig_fast_division_budget]).
 split;[exact Fh|]. split;[exact Fl|]. split;[exact Bh|]. split;[exact Bl|].
 rewrite Result. unfold q. rewrite Na,Db.
 replace (nv*(1+a)/(dv*(1+b))*(1+d)-nv/dv) with
   ((nv/dv)*((1+a)/(1+b)*(1+d)-1)) by (field;split;lra).
 rewrite Rabs_mult. apply Rle_trans with (Rabs(nv/dv)*bpow radix2 (-60)).
 - apply Rmult_le_compat_l;[apply Rabs_pos|apply trig_fast_quotient_budget;assumption].
 - right;ring.
Qed.
