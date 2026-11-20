(** Q256 reciprocal on its complete documented domain: either sign,
    magnitude at least 2^-1022, and finite binary64 conversion. The initial
    reciprocal may be subnormal. The actual three-step transcription is
    AsinKernel.q_recip; its signed Newton error theorem is shared with erfcx.
    No hypothesis restricts this result to the trig or asin input ranges. *)
From Coq Require Import Reals ZArith Lia Lra.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Q Require Import QSpec QRound Q256 Q256Real LimbScan.
From Binary64 Require Import Binary64Add IEEE64.
From Interval Require Import Tactic.
Open Scope R_scope.

(** A finite conversion excludes the overflow branch of normalization. *)
Lemma q_to_float_finite_value q : valid q -> finite (Q256.to_f64 q) ->
  B(Q256.to_f64 q)=rndF(qval q).
Proof.
  intros [O N] F. destruct N as [Zero|Normal].
  - unfold Q256.to_f64. rewrite is_zero_ok by apply O. rewrite Zero. cbn [Z.eqb].
    rewrite (qval_zero q Zero),round_0 by exact _. reflexivity.
  - rewrite Q256.to_f64_ok in F |- * by assumption. unfold QRound.bn in F |- *.
    pose proof (binary_normalize_correct 53 1024 eq_refl eq_refl mode_NE
      (QRound.signed (Q256.neg q) (Limbs.v (m q))) (Q256.e q) (Q256.neg q)) as C.
    match type of C with if ?b then _ else _ =>
      change b with (Rlt_bool (Rabs(rndF(qval q))) (bpow radix2 1024)) in C
    end.
    destruct (Rlt_bool (Rabs(rndF(qval q))) (bpow radix2 1024)) eqn:Range.
    + exact (proj1 C).
    + destruct (binary_normalize 53 1024 eq_refl eq_refl mode_NE
        (QRound.signed (Q256.neg q) (Limbs.v (m q))) (Q256.e q) (Q256.neg q)) in C,F;
        cbn in C,F; try discriminate.
Qed.

Require Import ErfcxReciprocal ErfcxAccurateReciprocal.
(** Division rounds even when its result is subnormal; the exact reciprocal
    remains at least 2^-1024 in magnitude. *)
Lemma reciprocal_seed_float x : finite x -> bpow radix2 (-1022)<=Rabs(B x) ->
  finite(fdiv one x) /\ Rabs(B x*B(fdiv one x)-1)<=bpow radix2 (-51).
Proof.
  intros F Lower. destruct one_ok as [F1 One].
  assert (Ax:0<Rabs(B x)) by (pose proof (bpow_gt_0 radix2 (-1022)); lra).
  assert (Nx:B x<>0) by (intro Z; rewrite Z,Rabs_R0 in Ax; lra).
  assert (Mag:Rabs(1/B x)=/Rabs(B x)).
  { unfold Rdiv. rewrite Rmult_1_l,Rabs_Rinv by exact Nx; reflexivity. }
  assert (Upper:Rabs(1/B x)<=bpow radix2 1022).
  { rewrite Mag. replace (bpow radix2 1022) with (/bpow radix2 (-1022)).
    - apply Rinv_le_contravar; [apply bpow_gt_0|exact Lower].
    - rewrite <-bpow_opp; reflexivity. }
  assert (Small:bpow radix2 (-1024)<=Rabs(1/B x)).
  { rewrite Mag. change (-1024)%Z with (- (1024))%Z. rewrite bpow_opp.
    apply Rinv_le_contravar; [exact Ax|].
    apply Rlt_le; exact (abs_B2R_lt_emax 53 1024 x). }
  destruct (fdiv_bnd 1 1022 one x F1 Nx ltac:(lia) ltac:(lia)
    ltac:(change (1<4)%Z; lia) ltac:(lia)
    ltac:(unfold bnd; rewrite One; change (IZR 1) with 1; rewrite Rmult_1_l; exact Upper))
    as [Fy [Value _]].
  rewrite One in Value. split; [exact Fy|].
  pose proof (binary64_round_large_reciprocal (1/B x) Small) as Error.
  rewrite <-Value in Error.
  replace (B x*B(fdiv one x)-1) with ((B(fdiv one x)-1/B x)*B x) by (field; exact Nx).
  rewrite Rabs_mult.
  replace (bpow radix2 (-51)) with ((bpow radix2 (-51)*Rabs(1/B x))*Rabs(B x)).
  - apply Rmult_le_compat_r; [apply Rabs_pos|exact Error].
  - rewrite Rmult_assoc,<-Rabs_mult.
    replace ((1/B x)*B x) with 1 by (field; exact Nx). rewrite Rabs_R1; ring.
Qed.

From Binary64 Require Import RoundingCore.
Require Import ErfcxAccurateInputs ErfcxAccurateNewton.
(** Compose conversion and division errors before the Newton iterations. *)
Lemma q_reciprocal_seed c : valid c -> bpow radix2 (-1022)<=Rabs(qval c) ->
  finite(Q256.to_f64 c) ->
  valid(q_float(fdiv one (Q256.to_f64 c))) /\
  Rabs(qval c*qval(q_float(fdiv one (Q256.to_f64 c)))-1)<=bpow radix2 (-50).
Proof.
  intros V Lower F. pose proof (q_to_float_finite_value c V F) as Value.
  set (x:=Q256.to_f64 c) in *.
  assert (X:bpow radix2 (-1022)<=Rabs(B x)).
  { rewrite Value,<-round_NE_abs by auto with typeclass_instances.
    apply round_ge_generic; [exact _|exact _| |exact Lower].
    apply generic_format_bpow; unfold FLT_exp,emin,prec; lia. }
  destruct (reciprocal_seed_float x F X) as [Fy Seed].
  destruct (q_float_ok (fdiv one x) Fy) as [Valid Float]. split; [exact Valid|]. rewrite Float.
  pose proof (RoundingCore.rnd_rel (qval c) Lower) as Error.
  change (Rabs(rndF(qval c)-qval c)<=bpow radix2 (-53)*Rabs(qval c)) in Error.
  rewrite <-Value in Error.
  set (a:=Rabs(qval c)). set (b:=Rabs(B x)). set (y:=B(fdiv one x)).
  set (u:=bpow radix2 (-53)) in *.
  set (s:=bpow radix2 (-51)) in *.
  assert (Constants:0<u<=/4 /\ 0<s /\ (3/2)*u*(1+s)+s<=bpow radix2 (-50)).
  { unfold u,s. repeat split; try apply bpow_gt_0; interval with (i_prec 300). }
  assert (A:0<=a) by apply Rabs_pos.
  assert (Bpos:0<=b) by apply Rabs_pos.
  assert (Ypos:0<=Rabs y) by apply Rabs_pos.
  assert (Ratio:a<=3/2*b).
  { pose proof (Rabs_triang (qval c-B x) (B x)) as T.
    replace (qval c-B x+B x) with (qval c) in T by ring.
    rewrite Rabs_minus_sym in T. fold a b in T. fold a in Error. nra. }
  assert (Product:b*Rabs y<=1+s).
  { pose proof (Rabs_triang (B x*y-1) 1) as T.
    replace (B x*y-1+1) with (B x*y) in T by ring.
    rewrite Rabs_R1,Rabs_mult in T. fold b in T. fold y in Seed. lra. }
  assert (First:Rabs(qval c-B x)*Rabs y<=u*a*Rabs y).
  { apply Rmult_le_compat_r; [exact Ypos|rewrite Rabs_minus_sym; exact Error]. }
  assert (Second:u*a*Rabs y<=(3/2)*u*(b*Rabs y)).
  { assert (u*a<=3/2*u*b) by nra. nra. }
  assert (Third:(3/2)*u*(b*Rabs y)<=(3/2)*u*(1+s)) by nra.
  change (Rabs(qval c*y-1)<=bpow radix2 (-50)).
  replace (qval c*y-1) with ((qval c-B x)*y+(B x*y-1)) by ring.
  eapply Rle_trans; [apply Rabs_triang|]. rewrite Rabs_mult. fold y in Seed; lra.
Qed.

Require Import AsinKernel.
Open Scope R_scope.
(** Definition-level equality, preserving every operation and its order. *)
Lemma q_reciprocal_transcription c : AsinKernel.q_recip c=
  q_refine3 c (q_float(fdiv one (Q256.to_f64 c))).
Proof.
  unfold AsinKernel.q_recip,q_refine3,q_newton.
  change AsinKernel.asin_one with one.
  change AsinKernel.qf with q_float.
  change AsinKernel.q_one with ErfcxAccurateTerms.q_one.
  unfold AsinKernel.q_sub. reflexivity.
Qed.

Theorem q_reciprocal_full_contract c : valid c ->
  bpow radix2 (-1022)<=Rabs(qval c) -> finite(Q256.to_f64 c) ->
  valid(AsinKernel.q_recip c) /\
  Rabs(qval(AsinKernel.q_recip c)-/qval c)<=bpow radix2 (-252)*Rabs(/qval c).
Proof.
  intros V Lower F. destruct (q_reciprocal_seed c V Lower F) as [Seed E].
  destruct (q_refine3_error c _ V Seed E) as [Valid Error].
  rewrite q_reciprocal_transcription. split; [exact Valid|].
  assert (Nonzero:qval c<>0).
  { intro Z. rewrite Z,Rabs_R0 in Lower. pose proof (bpow_gt_0 radix2 (-1022)); lra. }
  replace (qval(q_refine3 c (q_float(fdiv one (Q256.to_f64 c))))-/qval c) with
    ((qval c*qval(q_refine3 c (q_float(fdiv one (Q256.to_f64 c))))-1)* /qval c)
    by (field; exact Nonzero).
  rewrite Rabs_mult. apply Rmult_le_compat_r; [apply Rabs_pos|exact Error].
Qed.
