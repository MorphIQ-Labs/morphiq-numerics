(** Actual quadrant and argument-sign selection for the scalar fast pair. *)
From Coq Require Import Reals ZArith Lia Lra Psatz Bool.
From Flocq Require Import Core IEEE754.Bits.
From Q Require Import Q256 Q256Real.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add.
From Interval Require Import Tactic.
Require Import TrigFast TrigQuadrant TrigFastDomain TrigAccurate TrigInputContract TrigWindow.
Open Scope R_scope.

Definition trig_fast_selected k negative cosine s c :=
 let '(use_cos,negate):=trig_selection k negative cosine in
 let '(h,l):=if use_cos then c else s in
 (trig_flip negate h,trig_flip negate l).

Lemma trig_fast_flip_correct n h l v eps :
 finite h -> finite l -> B h=rndF(B h+B l) ->
 Rabs(B h+B l-v)<=eps*Rabs v ->
 finite(trig_flip n h) /\ finite(trig_flip n l) /\
 B(trig_flip n h)=rndF(B(trig_flip n h)+B(trig_flip n l)) /\
 Rabs(B(trig_flip n h)+B(trig_flip n l)-trig_sign n v)<=eps*Rabs(trig_sign n v).
Proof.
 intros H L N E.
 destruct (trig_flip_correct n h H) as [Fh [Vh _]].
 destruct (trig_flip_correct n l L) as [Fl [Vl _]].
 split;[exact Fh|]. split;[exact Fl|]. split.
 - apply trig_flip_normalized;assumption.
 - rewrite Vh,Vl. destruct n;cbn [trig_sign];[|exact E].
   replace (-B h+ -B l- -v) with (-(B h+B l-v)) by ring.
   rewrite !Rabs_Ropp;exact E.
Qed.

Lemma trig_fast_selected_correct k negative cosine sh sl ch cl r eps :
 finite sh -> finite sl -> B sh=rndF(B sh+B sl) ->
 finite ch -> finite cl -> B ch=rndF(B ch+B cl) ->
 Rabs(B sh+B sl-sin r)<=eps*Rabs(sin r) ->
 Rabs(B ch+B cl-cos r)<=eps*Rabs(cos r) ->
 let '(h,l):=trig_fast_selected k negative cosine (sh,sl) (ch,cl) in
 finite h /\ finite l /\ B h=rndF(B h+B l) /\
 Rabs(B h+B l-trig_selected_real k negative cosine r)<=
 eps*Rabs(trig_selected_real k negative cosine r).
Proof.
 intros Sh Sl Sn Ch Cl Cn Se Ce.
 unfold trig_fast_selected,trig_selected_real.
 destruct (trig_selection k negative cosine) as [choose negate].
 destruct choose;cbn.
 - change (finite(trig_flip negate ch) /\ finite(trig_flip negate cl) /\
   B(trig_flip negate ch)=rndF(B(trig_flip negate ch)+B(trig_flip negate cl)) /\
   Rabs(B(trig_flip negate ch)+B(trig_flip negate cl)-trig_sign negate (cos r))<=
   eps*Rabs(trig_sign negate (cos r))).
   apply trig_fast_flip_correct;assumption.
 - change (finite(trig_flip negate sh) /\ finite(trig_flip negate sl) /\
   B(trig_flip negate sh)=rndF(B(trig_flip negate sh)+B(trig_flip negate sl)) /\
   Rabs(B(trig_flip negate sh)+B(trig_flip negate sl)-trig_sign negate (sin r))<=
   eps*Rabs(trig_sign negate (sin r))).
   apply trig_fast_flip_correct;assumption.
Qed.

Lemma trig_fast_selected_floor k negative cosine r :
 bpow radix2 (-63)<=Rabs r<=0.785399 ->
 bpow radix2 (-64)<=Rabs(trig_selected_real k negative cosine r).
Proof.
 intros [Lo Hi]. destruct (trig_small_bounds r ltac:(lra)) as [S C].
 assert (Sin:bpow radix2 (-64)<=Rabs(sin r)).
 { assert (Half:bpow radix2 (-64)=(/2)*bpow radix2 (-63)) by (replace (-64)%Z with ((-1)+(-63))%Z by lia;rewrite bpow_plus;reflexivity).
   pose proof (Rabs_pos r);rewrite Half;nra. }
 assert (Cos:bpow radix2 (-64)<=Rabs(cos r)).
 { pose proof (Rle_abs(cos r));assert (bpow radix2 (-64)<=0.69) by (clear;interval);lra. }
 unfold trig_selected_real. destruct (trig_selection k negative cosine) as [choose negate].
 destruct choose,negate;rewrite ?Rabs_Ropp;assumption.
Qed.

Definition trig_fast64 bits negative cosine :=
 let '(k,q):=trig_reduce64 bits in
 let '(s,c):=trig_fast q in trig_fast_selected k negative cosine s c.

Theorem trig_fast64_correct x negative cosine : finite x -> bpow radix2 (-63)<=B x ->
 let '(h,l):=trig_fast64 (bits_of_b64 x) negative cosine in
 let v:=if cosine then cos(if negative then -B x else B x)
                   else sin(if negative then -B x else B x) in
 finite h /\ finite l /\ B h=rndF(B h+B l) /\
 Rabs(B h+B l-v)<=/2^62*Rabs v /\ bpow radix2 (-64)<=Rabs v.
Proof.
 intros F X. cbv zeta.
 destruct (trig_reduce_fast_domain x F X) as [n [q [Eq [V [Q [T [Near Err]]]]]]].
 assert (Xp:0<=B x) by (pose proof (bpow_gt_0 radix2 (-63));lra).
 pose proof (trig_nearest_nonnegative (B x) n Xp Near) as N.
 set (t:=B x-IZR n*(PI/2)) in *.
 assert (Nonzero:t<>0).
 { intro Zero;rewrite Zero,Rabs_R0 in T;pose proof (bpow_gt_0 radix2 (-63));lra. }
 pose proof (trig_fast_composed q t V Q (proj2 T) Nonzero Err) as Pair.
 unfold trig_fast64;rewrite Eq. destruct (trig_fast q) as [[sh sl][ch cl]].
 destruct Pair as [Sh [Sl [Sn [Ch [Cl [Cn [Se Ce]]]]]]].
 pose proof (trig_fast_selected_correct (n mod 4) negative cosine sh sl ch cl t (/2^62)
   Sh Sl Sn Ch Cl Cn Se Ce) as Selected.
 pose proof (trig_fast_selected_floor (n mod 4) negative cosine t T) as Floor.
 rewrite (trig_selection_analytic n t negative cosine N) in Selected,Floor.
 cbv zeta in Selected,Floor.
 replace (t+IZR n*(PI/2)) with (B x) in Selected,Floor by (unfold t;ring).
 unfold trig_fast_selected in Selected |- *.
 destruct (trig_selection (n mod 4) negative cosine) as [choose negate] in Selected |- *.
 destruct choose;cbn [fst snd] in Selected |- *;
 destruct Selected as [H [L [Normal Error]]];repeat split;assumption.
Qed.
