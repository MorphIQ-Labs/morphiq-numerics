(** The tiny-probability log(1-q) branch. The square may underflow;
    its absolute rounding error is included before normalization. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Eft RoundingConstant RoundingCore.
Require Import StageGappa ErfcxDecision Ln1pReduction Ln1pLemmas Ln1pTest
  NormalLogComplementTinyAnalytic.
Open Scope R_scope.

Lemma normal_log_tiny_round v :
  Rabs(rndF v-v)<=bpow radix2 (-53)*Rabs v+bpow radix2 (-1075).
Proof.
  destruct(Rle_lt_dec(bpow radix2 (-1022))(Rabs v))as[Large|Small].
  - pose proof(rnd_rel v Large)as Error.
    change(Rabs(rndF v-v)<=bpow radix2 (-53)*Rabs v)in Error.
    pose proof(bpow_ge_0 radix2 (-1075));lra.
  - pose proof(rnd_err_below v (-1021)ltac:(lia)
      ltac:(eapply Rle_trans with(bpow radix2 (-1022));[lra|apply bpow_le;lia]))as Error.
    change(-1021-54)%Z with(-1075)%Z in Error.
    pose proof(bpow_ge_0 radix2 (-53));pose proof(Rabs_pos v);nra.
Qed.

Definition normal_log_complement_tiny64 h l :=
  two_sum64 (fneg h)(fsub(fneg l)(fmul(fmul(erfcx_pow2(-1))h)h)).

Theorem normal_log_complement_tiny_ieee h l : finite h -> finite l ->
  bpow radix2 (-1004)<=B h<=bpow radix2 (-54) ->
  Rabs(B l)<=B h*bpow radix2 (-51) ->
  let '(a,b):=normal_log_complement_tiny64 h l in
  finite a /\ finite b /\ B a=rndF(B a+B b) /\
  Rabs((B a+B b)-ln(1-B h-B l))<=B h*bpow radix2 (-69).
Proof.
  intros Fh Fl H L;destruct(erfcx_pow2_ok(-1)ltac:(lia))as[Fc C].
  assert(Nf : forall w,finite w -> finite(fneg w))by
    (intros w Fw;unfold fneg,b64_opp;rewrite is_finite_Bopp;exact Fw).
  assert(Nb : forall w,B(fneg w)= -B w)by(intros;apply B2R_Bopp).
  assert(Hpositive : 0<B h)by(pose proof(bpow_gt_0 radix2 (-1004));lra).
  destruct(fmul_s (erfcx_pow2(-1))h Fc Fh)as[Fu U].
  { rewrite C,Rabs_mult,(Rabs_pos_eq(B h))by lra.
    rewrite Rabs_pos_eq by apply bpow_ge_0;bpow_num_all;nra. }
  rewrite C,Rmult_comm in U.
  rewrite(rnd_scale(B h)(-1)(-1004)(B_fmt h)ltac:(right;rewrite Rabs_pos_eq by lra;exact(proj1 H))ltac:(lia))in U.
  assert(Urange : 0<=B(fmul(erfcx_pow2(-1))h)<=1)by(rewrite U;bpow_num_all;split;nra).
  destruct(fmul_s (fmul(erfcx_pow2(-1))h)h Fu Fh)as[Fp P].
  { rewrite U,Rabs_mult,Rabs_mult,(Rabs_pos_eq(B h))by lra.
    rewrite Rabs_pos_eq by apply bpow_ge_0;bpow_num_all;nra. }
  set(p:=fmul(fmul(erfcx_pow2(-1))h)h)in *.
  replace(B(fmul(erfcx_pow2(-1))h)*B h)with(B h*B h/2)in P by(rewrite U;change(bpow radix2(-1))with(/2);field).
  pose proof(normal_log_tiny_round(B h*B h/2))as Rounded.
  rewrite <-P,(Rabs_pos_eq(B h*B h/2))in Rounded by nra.
  assert(SquareError : Rabs(B p-B h*B h/2)<=B h*bpow radix2 (-70)).
  { assert(Square : B h*B h<=B h*bpow radix2 (-54))by nra;bpow_num_all;nra. }
  assert(Prange : 0<=B p<=B h*bpow radix2 (-54)).
  { split.
    - rewrite P;apply round_ge_generic;try exact _;[apply generic_format_0|nra].
    - apply Rabs_le_inv in SquareError;bpow_num_all;nra. }
  assert(Sum : Rabs(-B l-B p)<=B h*bpow radix2 (-50)).
  { pose proof(Rabs_triang(-B l)(-B p))as Bound.
    rewrite !Rabs_Ropp,(Rabs_pos_eq(B p))in Bound by lra;unfold Rminus;bpow_num_all;nra. }
  destruct(fsub_s(fneg l)p(Nf l Fl)Fp)as[Fd D].
  { rewrite Nb;eapply Rle_trans;[exact Sum|bpow_num_all;nra]. }
  rewrite Nb in D.
  pose proof(rnd_sum_err(-B l)(-B p)
    (generic_format_opp _ _ _ (B_fmt l))(generic_format_opp _ _ _ (B_fmt p)))as SubRounded.
  change(Rabs(rndF(-B l-B p)-(-B l-B p))<=bpow radix2 (-53)*Rabs(-B l-B p))in SubRounded.
  rewrite <-D in SubRounded.
  assert(SubError : Rabs(B(fsub(fneg l)p)-(-B l-B p))<=B h*bpow radix2 (-103))by(bpow_num_all;nra).
  assert(SubRange : Rabs(B(fsub(fneg l)p))<=1).
  { pose proof(Rabs_triang_inv(B(fsub(fneg l)p))(-B l-B p));bpow_num_all;nra. }
  pose proof(two_sum_ieee(fneg h)(fsub(fneg l)p)(Nf h Fh)Fd
    ltac:(rewrite Nb,Rabs_Ropp,Rabs_pos_eq by lra;bpow_num_all;lra)
    ltac:(eapply Rle_trans;[exact SubRange|interval with(i_prec 80)]))as Words.
  unfold normal_log_complement_tiny64;fold p.
  destruct(two_sum64(fneg h)(fsub(fneg l)p))as[a b].
  destruct Words as[Fa [Fb [Norm Value]]];rewrite Nb in Norm,Value.
  pose proof(normal_log_complement_tiny_analytic(B h)(B l)ltac:(split;lra)L)as Taylor.
  repeat split;try assumption.
  - rewrite Value;exact Norm.
  - rewrite Value.
    replace(-B h+B(fsub(fneg l)p)-ln(1-B h-B l))with
      ((B(fsub(fneg l)p)-(-B l-B p))-(B p-B h*B h/2)-
       (ln(1-B h-B l)-(-B h-B l-B h*B h/2)))by ring.
    eapply Rle_trans;[apply Rabs_triang|].
    eapply Rle_trans;[apply Rplus_le_compat;[apply Rabs_triang|apply Rle_refl]|].
    rewrite !Rabs_Ropp;bpow_num_all;lra.
Qed.
