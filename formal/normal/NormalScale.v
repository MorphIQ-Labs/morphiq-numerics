(** Final power-of-two scaling in the fast normal kernels. A leading word
    is scaled exactly; gradual underflow of a tiny trailing word is bounded
    relative to the external scale, rather than ignored. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core Mult_error.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Mul RoundingConstant.
Require Import StageGappa ErfcxDecision.
Open Scope R_scope.

Theorem normal_scaled_word_ieee x k : finite x -> Rabs(B x)<=8 -> (-1000<=k<=0)%Z ->
  let y:=fmul x (erfcx_pow2 k)in
  finite y /\ B y=rndF(B x*bpow radix2 k) /\ Rabs(B y)<=8 /\
  Rabs(B y-B x*bpow radix2 k)<=bpow radix2 (k-74) /\
  (bpow radix2 (-20)<=Rabs(B x) -> B y=B x*bpow radix2 k).
Proof.
  intros F X K y;destruct(erfcx_pow2_ok k ltac:(lia))as[Fk Scale].
  assert (Power : 0<bpow radix2 k<=1).
  { split;[apply bpow_gt_0|change 1 with(bpow radix2 0);apply bpow_le;lia]. }
  assert (Product : Rabs(B x*B(erfcx_pow2 k))<=8).
  { rewrite Scale,Rabs_mult,(Rabs_pos_eq(bpow radix2 k))by lra;pose proof(Rabs_pos(B x));nra. }
  destruct(fmul16 x (erfcx_pow2 k)F Fk ltac:(lra))as[Fy Value];fold y in Fy,Value;rewrite Scale in Value.
  assert (Exact : bpow radix2 (-20)<=Rabs(B x) -> B y=B x*bpow radix2 k).
  { intros Large;rewrite Value;apply round_generic;[exact _|].
    apply mult_bpow_exact_FLT;[apply B_fmt|].
    assert(M : (-19<=mag radix2 (B x))%Z)by(apply mag_ge_bpow;exact Large).
    unfold emin,prec;lia. }
  assert (Error : Rabs(B y-B x*bpow radix2 k)<=bpow radix2 (k-74)).
  { destruct(Rle_dec (bpow radix2 (-20))(Rabs(B x)))as[Large|Small].
    - rewrite(Exact Large),Rminus_diag_eq,Rabs_R0 by reflexivity;apply bpow_ge_0.
    - rewrite Value;replace(k-74)%Z with((k-20)-54)%Z by ring.
      apply rnd_err_below;[lia|].
      rewrite Rabs_mult,(Rabs_pos_eq(bpow radix2 k))by lra.
      replace(k-20)%Z with(-20+k)%Z by ring;rewrite bpow_plus.
      apply Rmult_le_compat_r;lra. }
  split;[exact Fy|];split;[exact Value|];split;[|split;assumption].
  rewrite Value;apply abs_round_le_generic;[exact _|exact _| |rewrite <-Scale;exact Product].
  change 8 with(bpow radix2 3);apply generic_format_bpow;unfold FLT_exp,emin,prec;lia.
Qed.
