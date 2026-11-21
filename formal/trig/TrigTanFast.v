(** The actual scalar fast tangent: select numerator and denominator, call
    checked division, then apply the quadrant and original argument sign. *)
From Coq Require Import Reals ZArith Lia Lra Psatz Bool.
From Flocq Require Import Core IEEE754.Bits.
From Q Require Import Q256 Q256Real.
From Binary64 Require Import IEEE64 CheckedDivision.
Require Import TrigFast TrigFastQuotient TrigInputContract TrigTanDomain TrigTanAccurate TrigAccurate.
Open Scope R_scope.

Definition trig_signed_division negate nh nl dh dl : option(f64*f64) :=
 match checked_divide nh nl dh dl with
 | Some(h,l)=>Some(trig_flip negate h,trig_flip negate l)
 | None=>None
 end.
Definition trig_tan_fast_selected k negative s c : option(f64*f64) :=
 let '(nh,nl):=trig_tan_num k s c in
 let '(dh,dl):=trig_tan_den k s c in
 trig_signed_division (xorb (Z.odd k) negative) nh nl dh dl.
Definition trig_tan_fast r k negative :=
 let '(s,c):=trig_fast r in trig_tan_fast_selected k negative s c.

Lemma trig_signed_division_correct negate nh nl dh dl zh zl nv dv :
 nv<>0 -> dv<>0 ->
 Rabs(B nh+B nl-nv)<=bpow radix2 (-62)*Rabs nv ->
 Rabs(B dh+B dl-dv)<=bpow radix2 (-62)*Rabs dv ->
 trig_signed_division negate nh nl dh dl=Some(zh,zl) ->
 finite zh /\ finite zl /\ Rabs(B zh)<=bpow radix2 926 /\ Rabs(B zl)<=bpow radix2 926 /\
 Rabs(B zh+B zl-trig_sign negate (nv/dv))<=bpow radix2 (-60)*Rabs(trig_sign negate (nv/dv)).
Proof.
 intros N D En Ed. unfold trig_signed_division.
 destruct (checked_divide nh nl dh dl) as [[h l]|] eqn:Div;[|discriminate].
 intro Accepted. inversion Accepted;subst.
 destruct (trig_checked_quotient_error nh nl dh dl h l nv dv N D En Ed Div) as [Fh [Fl [Bh [Bl Err]]]].
 destruct (trig_flip_correct negate h Fh) as [H [Vh _]].
 destruct (trig_flip_correct negate l Fl) as [L [Vl _]].
 split;[exact H|]. split;[exact L|]. split.
 - rewrite Vh,trig_sign_abs;exact Bh.
 - split;[rewrite Vl,trig_sign_abs;exact Bl|].
   rewrite Vh,Vl. destruct negate;cbn [trig_sign];[|exact Err].
   replace (-B h+ -B l- -(nv/dv)) with (-(B h+B l-nv/dv)) by ring.
   rewrite !Rabs_Ropp;exact Err.
Qed.

Lemma trig_tan_fast_selected_correct k negative sh sl ch cl t zh zl :
 sin t<>0 -> cos t<>0 ->
 Rabs(B sh+B sl-sin t)<=bpow radix2 (-62)*Rabs(sin t) ->
 Rabs(B ch+B cl-cos t)<=bpow radix2 (-62)*Rabs(cos t) ->
 trig_tan_fast_selected k negative (sh,sl) (ch,cl)=Some(zh,zl) ->
 finite zh /\ finite zl /\ Rabs(B zh)<=bpow radix2 926 /\ Rabs(B zl)<=bpow radix2 926 /\
 Rabs(B zh+B zl-trig_tan_real k negative t)<=bpow radix2 (-60)*Rabs(trig_tan_real k negative t).
Proof.
 intros S C Es Ec. unfold trig_tan_fast_selected,trig_tan_real,trig_tan_num,trig_tan_den.
 destruct (Z.odd k);cbn [fst snd].
 - exact (trig_signed_division_correct (xorb true negative) ch cl sh sl zh zl (cos t) (sin t) C S Ec Es).
 - exact (trig_signed_division_correct (xorb false negative) sh sl ch cl zh zl (sin t) (cos t) S C Es Ec).
Qed.

Theorem trig_tan_fast_composed r k negative t zh zl : valid r ->
 bpow radix2 (-64)<=Rabs(qval r)<=0.785399 ->
 Rabs t<=0.785399 -> t<>0 ->
 Rabs(qval r-t)<=bpow radix2 (-199)*Rabs t ->
 trig_tan_fast r k negative=Some(zh,zl) ->
 finite zh /\ finite zl /\ Rabs(B zh)<=bpow radix2 926 /\ Rabs(B zl)<=bpow radix2 926 /\
 Rabs(B zh+B zl-trig_tan_real k negative t)<=bpow radix2 (-60)*Rabs(trig_tan_real k negative t).
Proof.
 intros V Range T NZ Reduction. unfold trig_tan_fast.
 pose proof (trig_fast_composed r t V Range T NZ Reduction) as Fast.
 destruct (trig_fast r) as [[sh sl] [ch cl]].
 destruct Fast as [_ [_ [_ [_ [_ [_ [Es Ec]]]]]]].
 destruct (trig_small_bounds t ltac:(lra)) as [S C].
 assert (Sn:sin t<>0).
 { intro Zero. rewrite Zero,Rabs_R0 in S. pose proof (Rabs_pos_lt t NZ);lra. }
 assert (Cn:cos t<>0) by lra.
 apply trig_tan_fast_selected_correct;try assumption.
 - replace (bpow radix2 (-62)) with (/2^62) by (rewrite pow_IZR;reflexivity). exact Es.
 - replace (bpow radix2 (-62)) with (/2^62) by (rewrite pow_IZR;reflexivity). exact Ec.
Qed.
