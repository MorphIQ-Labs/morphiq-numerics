(** The binary64-only high-degree tail of the mixed-precision centered
    polynomial. Every multiplication and addition rounds separately. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64 RoundingConstant.
Require Import StageGappa NormalCenterFastConstants.
Open Scope R_scope.

Fixpoint normal_center_tail64 z count :=
  match count with
  | O => fst(normal_center_fast_word 12)
  | S n => fadd (fst(normal_center_fast_word (12-S n))) (fmul z (normal_center_tail64 z n))
  end.
Fixpoint normal_center_tail_polynomial z count : R :=
  match count with
  | O => normal_fast_center_coefficient 12
  | S n => normal_fast_center_coefficient (12-S n)+z*normal_center_tail_polynomial z n
  end.

Lemma normal_center_round_bound x e : Rabs x<=bpow radix2 e -> (-1074<=e)%Z ->
  Rabs(rndF x)<=bpow radix2 e.
Proof.
  intros X E;apply abs_round_le_generic;[exact _|exact _| |exact X].
  apply generic_format_bpow;unfold FLT_exp,emin,prec;lia.
Qed.

Theorem normal_center_tail_ieee z count : finite z -> Rabs(B z)<=/4 -> (count<=8)%nat ->
  finite(normal_center_tail64 z count) /\
  Rabs(B(normal_center_tail64 z count))<=bpow radix2 (-10) /\
  Rabs(B(normal_center_tail64 z count)-normal_center_tail_polynomial (B z) count)<=bpow radix2 (-62).
Proof.
  intros Fz Z;induction count as[|n IH];intros N.
  - cbn [normal_center_tail64 normal_center_tail_polynomial].
    destruct(normal_center_fast_tail_word 12 ltac:(lia))as[F [Range Error]].
    split;[exact F|];split;eapply Rle_trans;[exact Range|apply bpow_le;lia|exact Error|apply bpow_le;lia].
  - destruct(IH ltac:(lia))as[Fh [H Error]].
    destruct(normal_center_fast_tail_word (12-S n)ltac:(lia))as[Fc [C Coefficient]].
    set(h:=normal_center_tail64 z n)in *;set(c:=fst(normal_center_fast_word (12-S n)))in *.
    assert(ProductRange : Rabs(B z*B h)<=bpow radix2 (-12)).
    { rewrite Rabs_mult;pose proof(Rabs_pos(B z));pose proof(Rabs_pos(B h));bpow_num_all;nra. }
    destruct(fmul16 z h Fz Fh ltac:(eapply Rle_trans;[exact ProductRange|interval with(i_prec 80)]))as[Fp Product].
    assert(P : Rabs(B(fmul z h))<=bpow radix2 (-12)).
    { rewrite Product;apply normal_center_round_bound;[exact ProductRange|lia]. }
    pose proof(rnd_err_below _ (-12)ltac:(lia)ProductRange)as ProductError;rewrite <-Product in ProductError.
    assert(SumRange : Rabs(B c+B(fmul z h))<=bpow radix2 (-10)).
    { eapply Rle_trans;[apply Rabs_triang|];bpow_num_all;lra. }
    destruct(fadd16 c (fmul z h) Fc Fp ltac:(eapply Rle_trans;[exact SumRange|interval with(i_prec 80)]))as[Fs Sum].
    assert(ResultRange : Rabs(B(fadd c (fmul z h)))<=bpow radix2 (-10)).
    { rewrite Sum;apply normal_center_round_bound;[exact SumRange|lia]. }
    pose proof(rnd_err_below _ (-10)ltac:(lia)SumRange)as SumError;rewrite <-Sum in SumError.
    cbn [normal_center_tail64 normal_center_tail_polynomial];fold h c.
    split;[exact Fs|];split;[exact ResultRange|].
    replace(B(fadd c (fmul z h))-(normal_fast_center_coefficient(12-S n)+B z*normal_center_tail_polynomial(B z)n))with
      ((B(fadd c (fmul z h))-(B c+B(fmul z h)))+
       ((B c-normal_fast_center_coefficient(12-S n))+
        ((B(fmul z h)-B z*B h)+B z*(B h-normal_center_tail_polynomial(B z)n))))by ring.
    eapply Rle_trans;[apply Rabs_triang|].
    eapply Rle_trans;[apply Rplus_le_compat_l,Rabs_triang|].
    eapply Rle_trans;[apply Rplus_le_compat_l,Rplus_le_compat_l,Rabs_triang|].
    rewrite Rabs_mult.
    assert(Propagation : Rabs(B z)*Rabs(B h-normal_center_tail_polynomial(B z)n)<=/4*bpow radix2 (-62)).
    { apply Rmult_le_compat;[apply Rabs_pos|apply Rabs_pos|exact Z|exact Error]. }
    change(-12-54)%Z with(-66)%Z in ProductError;change(-10-54)%Z with(-64)%Z in SumError.
    bpow_num_all;lra.
Qed.
