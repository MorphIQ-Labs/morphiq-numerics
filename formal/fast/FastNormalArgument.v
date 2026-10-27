(** Actual binary64 argument formation for the bounded normal CDF. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core Mult_error IEEE754.Binary IEEE754.Bits.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add RoundingCore RoundingTest.
Require Import StageGappa ErfcxDecision ErfcxPublicModel NormalConstants.
Open Scope R_scope.

Definition fast_normal_argument64 a := fmul a normal_inv_sqrt2_hi.
Definition fast_normal_exponent64 a := fmul(fmul erfcx_negative_half a)a.

Theorem fast_normal_argument_ok a : finite a -> bpow radix2(-33)<=B a<=8 ->
  finite(fast_normal_argument64 a) /\
  bpow radix2(-34)<=B(fast_normal_argument64 a)<=8 /\
  Rabs(B(fast_normal_argument64 a)-B a/sqrt 2)<=
    3*bpow radix2(-53)*(B a/sqrt 2).
Proof.
  intros Fa A;destruct normal_inv_sqrt2_hi_ok as[Fc C].
  assert(Crange : /2<=B normal_inv_sqrt2_hi<=1)by(rewrite C;interval with(i_prec 80)).
  assert(Cerror : Rabs(B normal_inv_sqrt2_hi-/sqrt 2)<=bpow radix2(-53)/sqrt 2).
  { rewrite C;bpow_num;interval with(i_prec 160). }
  assert(Apos : 0<B a)by(pose proof(bpow_gt_0 radix2(-33));lra).
  assert(Product : bpow radix2(-34)<=B a*B normal_inv_sqrt2_hi<=8).
  { bpow_num_all;split;nra. }
  assert(Bound : bnd 1 3 (B a*B normal_inv_sqrt2_hi)).
  { unfold bnd;rewrite Rmult_1_l,Rabs_pos_eq by(pose proof(bpow_gt_0 radix2(-34));lra).
    change(bpow radix2 3)with 8;lra. }
  destruct(fmul_bnd 1 3 a normal_inv_sqrt2_hi Fa Fc ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)Bound)
    as[Fz [Z _]].
  fold(fast_normal_argument64 a)in Fz,Z.
  assert(Range : bpow radix2(-34)<=B(fast_normal_argument64 a)<=8).
  { rewrite Z;split.
    - apply round_ge_generic;[exact _|exact _| |exact(proj1 Product)].
      apply generic_format_bpow;unfold FLT_exp,emin,prec;lia.
    - change 8 with(bpow radix2 3);apply round_le_generic;[exact _|exact _| |exact(proj2 Product)].
      apply generic_format_bpow;unfold FLT_exp,emin,prec;lia. }
  assert(Normal : bpow radix2(-1022)<=Rabs(B a*B normal_inv_sqrt2_hi)).
  { rewrite Rabs_pos_eq by(pose proof(bpow_gt_0 radix2(-34));lra).
    eapply Rle_trans with(bpow radix2(-34));[apply bpow_le;lia|exact(proj1 Product)]. }
  pose proof(rnd_rel _ Normal)as Round.
  change(Rabs(rndF(B a*B normal_inv_sqrt2_hi)-B a*B normal_inv_sqrt2_hi)<=
    bpow radix2(-53)*Rabs(B a*B normal_inv_sqrt2_hi))in Round.
  rewrite <-Z,Rabs_mult,(Rabs_pos_eq(B a)),(Rabs_pos_eq(B normal_inv_sqrt2_hi))in Round by lra.
  assert(Error : Rabs(B(fast_normal_argument64 a)-B a/sqrt 2)<=3*bpow radix2(-53)*(B a/sqrt 2)).
  { replace(B(fast_normal_argument64 a)-B a/sqrt 2)with
      ((B(fast_normal_argument64 a)-B a*B normal_inv_sqrt2_hi)+B a*(B normal_inv_sqrt2_hi-/sqrt 2))by(unfold Rdiv;ring).
    eapply Rle_trans;[apply Rabs_triang|].
    rewrite Rabs_mult,(Rabs_pos_eq(B a))by lra.
    pose proof(Rabs_le_inv _ _ Cerror)as Cr.
    assert(Scaled : B a*Rabs(B normal_inv_sqrt2_hi-/sqrt 2)<=B a*(bpow radix2(-53)/sqrt 2)).
    { apply Rmult_le_compat_l;lra. }
    assert(High : B a*B normal_inv_sqrt2_hi<=B a*(1+bpow radix2(-53))/sqrt 2).
    { unfold Rdiv in *;nra. }
    assert(Ypos : 0<B a/sqrt 2)by(apply Rdiv_lt_0_compat;[lra|interval]).
    bpow_num_all;unfold Rdiv in *;nra. }
  repeat split;tauto.
Qed.

Theorem fast_normal_exponent_ok a : finite a -> bpow radix2(-33)<=B a<=8 ->
  finite(fast_normal_exponent64 a) /\ -32<=B(fast_normal_exponent64 a)<=0 /\
  B(fast_normal_exponent64 a)=rndF(-B a*B a/2) /\
  Rabs(B(fast_normal_exponent64 a)+B a*B a/2)<=bpow radix2(-53)*(B a*B a/2).
Proof.
  intros Fa A;destruct erfcx_negative_half_ok as[Fhalf Half].
  assert(Apos : 0<B a)by(pose proof(bpow_gt_0 radix2(-33));lra).
  assert(Mag : (-32<=mag radix2(B a))%Z).
  { apply mag_ge_bpow;change(bpow radix2(-33)<=Rabs(B a));rewrite Rabs_pos_eq by lra;exact(proj1 A). }
  assert(Format : fmtF(B erfcx_negative_half*B a)).
  { rewrite Half;replace(-/2*B a)with(-(B a*bpow radix2(-1)))by(bpow_num;ring).
    apply generic_format_opp,mult_bpow_exact_FLT;[apply B_fmt|unfold emin,prec;lia]. }
  destruct(fmul_exact erfcx_negative_half a Fhalf Fa Format)as[Fha Ha].
  - rewrite Half,Rabs_mult,(Rabs_pos_eq(B a))by lra.
    eapply Rle_lt_trans with 4;[rewrite Rabs_Ropp;rewrite Rabs_pos_eq by lra;nra|].
    change 4 with(bpow radix2 2);apply bpow_lt;lia.
  - rewrite Half in Ha.
    assert(Qrange : bpow radix2(-67)<=B a*B a/2<=32)by(bpow_num_all;split;nra).
    assert(Bound : bnd 1 5 (B(fmul erfcx_negative_half a)*B a)).
    { rewrite Ha;unfold bnd;rewrite Rmult_1_l.
      replace(-/2*B a*B a)with(-(B a*B a/2))by ring.
      rewrite Rabs_Ropp,Rabs_pos_eq by nra;change(bpow radix2 5)with 32;lra. }
    destruct(fmul_bnd 1 5 (fmul erfcx_negative_half a)a Fha Fa ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)Bound)
      as[Ft [T _]].
    fold(fast_normal_exponent64 a)in Ft,T;rewrite Ha in T.
    replace(-/2*B a*B a)with(-B a*B a/2)in T by ring.
    assert(Range : -32<=B(fast_normal_exponent64 a)<=0).
    { rewrite T;split.
      - change(-32)with(-bpow radix2 5);apply round_ge_generic;[exact _|exact _| |nra].
        apply generic_format_opp,generic_format_bpow;unfold FLT_exp,emin,prec;lia.
      - apply round_le_generic;[exact _|exact _|apply generic_format_0|nra]. }
    assert(Normal : bpow radix2(-1022)<=Rabs(-B a*B a/2)).
    { replace(-B a*B a/2)with(-(B a*B a/2))by ring;rewrite Rabs_Ropp,Rabs_pos_eq by nra.
      eapply Rle_trans with(bpow radix2(-67));[apply bpow_le;lia|exact(proj1 Qrange)]. }
    pose proof(rnd_rel _ Normal)as Error.
    change(Rabs(rndF(-B a*B a/2)-(-B a*B a/2))<=bpow radix2(-53)*Rabs(-B a*B a/2))in Error.
    rewrite <-T in Error.
    replace(-B a*B a/2)with(-(B a*B a/2))in Error by ring.
    rewrite Rabs_Ropp,(Rabs_pos_eq(B a*B a/2))in Error by nra.
    replace(B(fast_normal_exponent64 a)- -(B a*B a/2))with(B(fast_normal_exponent64 a)+B a*B a/2)in Error by ring.
    repeat split;tauto.
Qed.
