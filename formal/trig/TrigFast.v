(** Full scalar fast evaluation from a signed Q256 remainder. The existing
    integer-index decoder is shared with asin's proved table conversion. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Q Require Import Q256 Q256Real.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add.
From Interval Require Import Tactic.
Require Import StageGappa AsinKernel AsinSegment TrigInputContract TrigReconstruction.
Open Scope R_scope.

Definition trig_fast r :=
 let '(n,(i,(th,tl))):=trig_input r in
 let '((sh,sl),c):=trig_reconstruct (Z.to_nat(asin_index i)) th tl in
 ((trig_flip n sh,trig_flip n sl),c).

Lemma trig_sign_abs n x : Rabs(trig_sign n x)=Rabs x.
Proof. destruct n;cbn [trig_sign];[apply Rabs_Ropp|reflexivity]. Qed.

Lemma trig_flip_normalized n h l : finite h -> finite l -> B h=rndF(B h+B l) ->
 B(trig_flip n h)=rndF(B(trig_flip n h)+B(trig_flip n l)).
Proof.
 intros H L N.
 destruct (trig_flip_correct n h H) as [_ [Vh _]].
 destruct (trig_flip_correct n l L) as [_ [Vl _]].
 rewrite Vh,Vl. destruct n;cbn [trig_sign];[apply dw_opp|];exact N.
Qed.

Lemma trig_flip_sine_error n h l r eps :
 Rabs(h+l-sin(trig_sign n r))<=eps*Rabs(sin(trig_sign n r)) ->
 Rabs(trig_sign n h+trig_sign n l-sin r)<=eps*Rabs(sin r).
Proof.
 destruct n;cbn [trig_sign];intro E;[|exact E].
 rewrite sin_neg,Rabs_Ropp in E.
 replace (-h+ -l-sin r) with (-(h+l- -sin r)) by ring.
 rewrite Rabs_Ropp;exact E.
Qed.

Theorem trig_fast_correct r : valid r ->
 bpow radix2 (-64)<=Rabs(qval r)<=0.785399 ->
 let '((sh,sl),(ch,cl)):=trig_fast r in
 finite sh /\ finite sl /\ B sh=rndF(B sh+B sl) /\
 finite ch /\ finite cl /\ B ch=rndF(B ch+B cl) /\
 Rabs(B sh+B sl-sin(qval r))<=/2^62*Rabs(sin(qval r)) /\
 Rabs(B ch+B cl-cos(qval r))<=/2^62*Rabs(cos(qval r)).
Proof.
 intros V Range. pose proof (trig_input_correct r V Range) as Input.
 unfold trig_fast. destruct (trig_input r) as [n [i [th tl]]].
 destruct Input as [Fi [[k [K Index]] [Th [Tl [Normal [Upper [Full [Domain [Low [Grid Split]]]]]]]]]].
 rewrite (asin_index_ok i k Fi Index ltac:(lia)).
 assert (IK:Z.of_nat(Z.to_nat k)=k) by (apply Z2Nat.id;lia).
 assert (I:(Z.to_nat k<51)%nat) by lia.
 assert (R:Rabs(trig_sign n (qval r))<=0.785399) by (rewrite trig_sign_abs;exact (proj2 Range)).
 assert (Nonzero:trig_sign n (qval r)<>0).
 { intro Zero. pose proof (bpow_gt_0 radix2 (-64)) as Positive.
   pose proof (trig_sign_abs n (qval r)) as Abs.
   rewrite Zero,Rabs_R0 in Abs;lra. }
 assert (D:B th=0 \/ /2^320<=Rabs(B th)).
 { replace (/2^320) with (bpow radix2 (-320)) by (bpow_num;field);exact Domain. }
 assert (L:Rabs(B tl)<=/2^53*Rabs(B th)).
 { replace (/2^53) with (bpow radix2 (-53)) by (bpow_num;field);exact Low. }
 assert (E:Rabs(IZR(Z.of_nat(Z.to_nat k))/64+(B th+B tl)-trig_sign n (qval r))
   <=bpow radix2 (-105)*Rabs(trig_sign n (qval r))).
 { rewrite IK,<-Index,trig_sign_abs;exact Split. }
 pose proof (trig_reconstruct_correct (Z.to_nat k) th tl (trig_sign n (qval r))
   I Th Tl D Upper L Normal Grid Full R Nonzero E) as Result.
 destruct (trig_reconstruct (Z.to_nat k) th tl) as [[sh sl][ch cl]].
 destruct Result as [Sh [Sl [Sn [Ch [Cl [Cn [Se Ce]]]]]]].
 destruct (trig_flip_correct n sh Sh) as [Fsh [Vs _]].
 destruct (trig_flip_correct n sl Sl) as [Fsl [Vl _]].
 pose proof (trig_flip_normalized n sh sl Sh Sl Sn) as N.
 split;[exact Fsh|]. split;[exact Fsl|]. split;[exact N|].
 split;[exact Ch|]. split;[exact Cl|]. split;[exact Cn|]. split.
 - rewrite Vs,Vl;apply trig_flip_sine_error;exact Se.
 - assert (C:cos(trig_sign n (qval r))=cos(qval r)).
   { destruct n;cbn [trig_sign];[apply cos_neg|reflexivity]. }
   rewrite C in Ce;exact Ce.
Qed.
