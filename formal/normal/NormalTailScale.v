(** The normal tail's tighter exponent range gives a smaller absolute
    budget for gradual underflow of its scaled trailing word. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core Mult_error.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Mul RoundingConstant.
Require Import StageGappa ErfcxDecision NormalScale.
Open Scope R_scope.

Theorem normal_tail_scaled_word_ieee x k : finite x -> Rabs(B x)<=8 -> (-991<=k<=0)%Z ->
  let y:=fmul x (erfcx_pow2 k)in
  finite y /\ B y=rndF(B x*bpow radix2 k) /\ Rabs(B y)<=8 /\
  Rabs(B y-B x*bpow radix2 k)<=bpow radix2 (k-84) /\
  (bpow radix2 (-20)<=Rabs(B x) -> B y=B x*bpow radix2 k).
Proof.
  intros F X K y;pose proof(normal_scaled_word_ieee x k F X ltac:(lia))as Scaled.
  fold y in Scaled;destruct Scaled as[Fy [Value [Range [_ Exact]]]].
  repeat split;try assumption.
  destruct(Rle_dec (bpow radix2 (-30))(Rabs(B x)))as[Large|Small].
  - rewrite Value;assert(Format : fmtF(B x*bpow radix2 k)).
    { apply mult_bpow_exact_FLT;[apply B_fmt|].
      assert(M : (-29<=mag radix2(B x))%Z)by(apply mag_ge_bpow;exact Large).
      unfold emin,prec;lia. }
    rewrite round_generic by(auto with typeclass_instances || exact Format).
    rewrite Rminus_diag_eq,Rabs_R0 by reflexivity;apply bpow_ge_0.
  - rewrite Value;replace(k-84)%Z with((k-30)-54)%Z by ring.
    apply rnd_err_below;[lia|].
    rewrite Rabs_mult,(Rabs_pos_eq(bpow radix2 k))by apply bpow_ge_0.
    replace(k-30)%Z with(-30+k)%Z by ring;rewrite bpow_plus.
    apply Rmult_le_compat_r;[apply bpow_ge_0|lra].
Qed.
