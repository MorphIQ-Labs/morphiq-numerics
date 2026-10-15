(** Power-of-two scaling of the fast tail, including gradual underflow
    of the trailing word and the final exact TwoSum normalization. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Eft RoundingConstant.
Require Import StageGappa ErfcxDecision NormalTailAnalytic NormalTailFastMantissa NormalTailScale.
Open Scope R_scope.

Definition normal_tail_fast64 x :=
  let '(h,l,k):=normal_tail_fast_mantissa64 x in
  let '(a,b):=two_sum64 (fmul h (erfcx_pow2 k))(fmul l (erfcx_pow2 k))in(a,b,k).

Theorem normal_tail_fast_ieee x : finite x -> /2<=B x<=37 ->
  let '(h,l,k):=normal_tail_fast64 x in
  finite h /\ finite l /\ (-991<=k<= -1)%Z /\ B h=rndF(B h+B l) /\
  0<=B h<=8*bpow radix2 k /\ Rabs(B l)<=bpow radix2 (k-51) /\
  bpow radix2 k/4096<=normal_tail(B x)<=6*bpow radix2 k /\
  Rabs((B h+B l)-normal_tail(B x))<=3*bpow radix2 (-67)*normal_tail(B x).
Proof.
  intros Fx X;pose proof(normal_tail_fast_mantissa_ieee x Fx X)as Mantissa.
  unfold normal_tail_fast64;destruct(normal_tail_fast_mantissa64 x)as[[a b]k].
  destruct Mantissa as[Fa [Fb [K [Anorm [A [Ratio Error]]]]]].
  assert(Lvalue : B b=(B b/B a)*B a)by(field;pose proof(bpow_gt_0 radix2 (-10));lra).
  assert(Low : Rabs(B b)<=bpow radix2 (-49)).
  { rewrite Lvalue,Rabs_mult,(Rabs_pos_eq(B a))by(pose proof(bpow_gt_0 radix2 (-10));lra).
    apply Rabs_le in Ratio;bpow_num_all;nra. }
  assert(Sum : bpow radix2 (-11)<=B a+B b<=5).
  { apply Rabs_le_inv in Low;bpow_num_all;split;lra. }
  set(s:=bpow radix2 k)in *;assert(S : 0<s<=1).
  { unfold s;split;[apply bpow_gt_0|change 1 with(bpow radix2 0);apply bpow_le;lia]. }
  set(t:=normal_tail(B x)/s)in *.
  assert(TargetMantissa : /4096<=t<=6).
  { apply Rabs_le_inv in Error;bpow_num_all;split;lra. }
  assert(Target : s/4096<=normal_tail(B x)<=6*s).
  { assert(Identity : normal_tail(B x)=t*s)by(unfold t;field;lra);rewrite Identity;split;nra. }
  destruct(normal_tail_scaled_word_ieee a k Fa
    ltac:(rewrite Rabs_pos_eq by(pose proof(bpow_gt_0 radix2 (-10));lra);lra)ltac:(lia))as[Fah [Av [Ah [Ae Exact]]]].
  destruct(normal_tail_scaled_word_ieee b k Fb
    ltac:(eapply Rle_trans;[exact Low|interval with(i_prec 80)])ltac:(lia))as[Fbl [Bv [Bh [Be _]]]].
  specialize(Exact ltac:(rewrite Rabs_pos_eq by(pose proof(bpow_gt_0 radix2 (-10));lra);eapply Rle_trans with(bpow radix2 (-10));[apply bpow_le;lia|exact(proj1 A)])).
  pose proof(two_sum_ieee (fmul a (erfcx_pow2 k))(fmul b (erfcx_pow2 k))Fah Fbl
    ltac:(eapply Rle_trans;[exact Ah|interval with(i_prec 80)])
    ltac:(eapply Rle_trans;[exact Bh|interval with(i_prec 80)]))as SumWords.
  destruct(two_sum64 (fmul a (erfcx_pow2 k))(fmul b (erfcx_pow2 k)))as[h l].
  destruct SumWords as[Fh [Fl [Norm Value]]].
  assert(Normalized : B h=rndF(B h+B l))by(rewrite Value;exact Norm).
  assert(Composition : Rabs((B h+B l)-normal_tail(B x))<=3*bpow radix2 (-67)*normal_tail(B x)).
  { rewrite Value,Exact;fold s;replace(B a*s+B(fmul b (erfcx_pow2 k))-normal_tail(B x))with
      ((B(fmul b (erfcx_pow2 k))-B b*s)+s*((B a+B b)-t))by(unfold t;field;lra).
    eapply Rle_trans;[apply Rabs_triang|];rewrite Rabs_mult,(Rabs_pos_eq s)by lra.
    replace(k-84)%Z with(k+ -84)%Z in Be by ring;rewrite bpow_plus in Be;fold s in Be.
    assert(ScaledError : s*Rabs((B a+B b)-t)<=(5*bpow radix2 (-68))*normal_tail(B x)).
    { apply(Rmult_le_compat_l s)in Error;[|lra].
      replace(s*((5*bpow radix2 (-68))*t))with((5*bpow radix2 (-68))*normal_tail(B x))in Error by(unfold t;field;lra);exact Error. }
    bpow_num_all;nra. }
  assert(ResultRange : 0<=B h+B l<=8*s).
  { apply Rabs_le_inv in Composition;bpow_num_all;split;nra. }
  assert(High : 0<=B h<=8*s).
  { rewrite Normalized;split.
    - replace 0 with(rndF 0)by(rewrite round_0 by apply valid_rnd_N;reflexivity).
      apply round_le;[exact _|exact _|exact(proj1 ResultRange)].
    - replace(8*s)with(bpow radix2 (k+3))by(unfold s;rewrite bpow_plus;change(bpow radix2 3)with 8;ring).
      apply round_le_generic;[exact _|exact _| |].
      + apply generic_format_bpow;unfold FLT_exp,emin,prec;lia.
      + rewrite bpow_plus;fold s;change(bpow radix2 3)with 8;lra. }
  pose proof(rnd_err_below(B h+B l)(k+3)ltac:(lia)
    ltac:(rewrite Rabs_pos_eq by lra;rewrite bpow_plus;fold s;change(bpow radix2 3)with 8;lra))as Rounded.
  rewrite <-Normalized in Rounded;replace(k+3-54)%Z with(k-51)%Z in Rounded by ring.
  assert(ResultLow : Rabs(B l)<=bpow radix2 (k-51)).
  { replace(B h-(B h+B l))with(-B l)in Rounded by ring;rewrite Rabs_Ropp in Rounded;exact Rounded. }
  repeat split;tauto.
Qed.
