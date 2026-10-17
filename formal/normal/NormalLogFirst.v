(** Binary64 first stage for the moderate far tail, before the double-word
    candidate. Its wider interval includes all reconstruction errors. *)
From Coq Require Import Reals ZArith Lia Lra Psatz Classical.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Eft RoundingConstant.
Require Import StageGappa ErfcxReciprocal NormalLogReciprocalStage NormalLogTailPolynomial
  NormalLogTailSquare NormalLogMillsIdentity NormalConstants NormalCenterFastTail NormalTailAnalytic ErfcxTailIntegral Ln1pTest ErfcxDecision.
Require Import NormalLogTableCorrection NormalLogTailApprox.
From Binary64 Require Import Encodings.
Open Scope R_scope.

Lemma normal_log_first_square x : finite x -> 37<=B x<=64 ->
  let '(s,t):=normal_log_tail_square64 x in
  finite s /\ finite t /\ B s+B t= -B x*B x/2 /\
  -2049<=B s<= -684 /\ Rabs(B t)<=bpow radix2(-43).
Proof.
  intros F X;pose proof(normal_log_tail_square_exact x F
    ltac:(bpow_num_all;split;lra))as Square.
  destruct(normal_log_tail_square64 x)as[s t].
  destruct Square as[Fs [Ft [Norm [Value Magnitude]]]].
  assert(Range : Rabs(-B x*B x/2)<=bpow radix2 11).
  { apply Rabs_le;bpow_num_all;split;nra. }
  pose proof(rnd_err_below _ 11 ltac:(lia)Range)as Error.
  rewrite <-Value,<-Norm in Error.
  assert(T : Rabs(B t)<=bpow radix2(-43)).
  { replace(B t)with(- (B s-(B s+B t)))by ring;rewrite Rabs_Ropp;exact Error. }
  repeat split;try assumption;apply Rabs_le_inv in T;bpow_num_all;nra.
Qed.

Definition normal_log_first64 x :=
 let c:=normal_log_table_correction64 x in
 let '(s,t):=normal_log_tail_square64 x in
 let '(y,e):=fast_two_sum64 s (fneg c) in (y,fadd e t).

Theorem normal_log_first_words x : finite x -> 37<=B x<64 ->
 let '(h,l):=normal_log_first64 x in
 finite h /\ finite l /\ Rabs(B h)<=4096 /\ Rabs(B l)<=bpow radix2(-39) /\
 Rabs(ln(normal_tail(B x))-(B h+B l))<=11*bpow radix2(-53).
Proof.
 intros F X.
 destruct(normal_log_table_correction_words x F X)as[Fc [C Cerror]].
 set(c:=normal_log_table_correction64 x)in *.
 pose proof(normal_log_first_square x F ltac:(split;lra))as Square.
 unfold normal_log_first64;fold c.
  destruct(normal_log_tail_square64 x)as[s t].
  destruct Square as[Fs [Ft [Square [S T]]]].
  assert(Fneg : finite(fneg c))by(unfold fneg,b64_opp;rewrite is_finite_Bopp;exact Fc).
  assert(Neg : B(fneg c)= -B c)by(apply B2R_Bopp).
  assert(AbsS : Rabs(B s)<=2049)by(apply Rabs_le;lra).
  assert(AbsC : Rabs(B(fneg c))<=7)by(rewrite Neg;apply Rabs_le;lra).
  pose proof(fast_two_sum_ieee s (fneg c)Fs Fneg
    ltac:(apply Rle_trans with 2049;[exact AbsS|interval with(i_prec 80)])
    ltac:(apply Rle_trans with 7;[exact AbsC|interval with(i_prec 80)])
    ltac:(right;left;rewrite Neg,Rabs_left,Rabs_left by lra;lra))as Sum.
  destruct(fast_two_sum64 s (fneg c))as[y e].
  destruct Sum as[Fy [Fe [High Total]]].
  assert(SumBound : Rabs(B s+B(fneg c))<=bpow radix2 12).
  { eapply Rle_trans;[apply Rabs_triang|];bpow_num_all;lra. }
  assert(Y : Rabs(B y)<=4096).
  { rewrite High;change 4096 with(bpow radix2 12);apply normal_center_round_bound;assumption||lia. }
  pose proof(rnd_err_below _ 12 ltac:(lia)SumBound)as RoundError.
  rewrite <-High in RoundError.
  assert(E : Rabs(B e)<=bpow radix2(-40)).
  { replace(B e)with((B s+B(fneg c))-B y)by lra;rewrite Rabs_minus_sym.
    eapply Rle_trans;[exact RoundError|apply bpow_le;lia]. }
  destruct(fadd16 e t Fe Ft
    ltac:(eapply Rle_trans;[apply Rabs_triang|];bpow_num_all;lra))as[Fz Zvalue].

 assert(Small : Rabs(B e+B t)<=bpow radix2(-39)).
 { eapply Rle_trans;[apply Rabs_triang|];bpow_num_all;lra. }
 pose proof(rnd_err_below (B e+B t) (-39) ltac:(lia)Small)as LowError.
 assert(Z : Rabs(rn(B e+B t))<=bpow radix2(-39)).
 { apply normal_center_round_bound;assumption||lia. }
 assert(U : 0<=/(B x*B x)<=/1369)by(split;[left;apply Rinv_0_lt_compat;nra|apply Rinv_le_contravar;nra]).
 pose proof(normal_log_mills_approximation _ U)as Mills.
 repeat split;try assumption.
 - rewrite Zvalue;exact Z.
 - rewrite normal_log_mills_identity by lra.
   replace(1/B x*(1/B x))with(/(B x*B x))by(field;lra).
   rewrite Zvalue;rewrite Neg in Total.
   change(Rabs(rndF(B e+B t)-(B e+B t))<=bpow radix2(-93))in LowError.
   apply Rabs_le_inv in Cerror,Mills,LowError;apply Rabs_le;bpow_num_all.
   split;nra.
Qed.

Definition normal_log_first_guard := b64_of_bits 4384254237245177856.
Lemma normal_log_first_guard_ok : finite normal_log_first_guard /\
 B normal_log_first_guard=6*bpow radix2(-52).
Proof.
 split;[exact(bits_finite 4384254237245177856 false 6755399441055744 (-102) eq_refl)|].
 unfold normal_log_first_guard.
 rewrite(bits_val 4384254237245177856 false 6755399441055744 102 eq_refl);simpl;bpow_num;field.
Qed.
Definition normal_log_first_decide64 x :=
 let '(h,l):=normal_log_first64 x in Ln1pTest.decide h l normal_log_first_guard.
Theorem normal_log_first_decided x v : finite x -> 37<=B x<64 ->
 normal_log_first_decide64 x=Some v -> finite v /\ B v=rndF(ln(normal_tail(B x))).
Proof.
 intros F X;pose proof(normal_log_first_words x F X)as Words.
 unfold normal_log_first_decide64;destruct(normal_log_first64 x)as[h l].
 destruct Words as[Fh [Fl [H [L Error]]]].
 destruct normal_log_first_guard_ok as[Fe E].
 intros Decision;destruct(Ln1pTest.decide_ok h l normal_log_first_guard v Fh Fl Fe
  ltac:(rewrite E;pose proof(bpow_gt_0 radix2(-52));lra)
  ltac:(apply Rle_trans with 4096;[exact H|interval with(i_prec 80)])
  ltac:(rewrite E;bpow_num_all;lra)Decision)as[Fv Round].
 split;[exact Fv|symmetry;apply Round;rewrite E;bpow_num_all;nra].
Qed.
