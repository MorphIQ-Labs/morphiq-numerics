(** The normal kernels compare both rounded endpoints by their encodings.
    The guard must include the rounding of the endpoints' low words. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 RoundingConstant.
Require Import StageGappa.
Open Scope R_scope.

Definition normal_interval_decide64 h l e :=
  let low:=fadd h (fsub l e)in
  let high:=fadd h (fadd l e)in
  if Z.eqb(bits_of_b64 low)(bits_of_b64 high)then Some low else None.

Theorem normal_interval_decide_ok h l e target epsilon em v :
  finite h -> finite l -> finite e -> Rabs(B h)<=1024 ->
  (-1021<=em<=0)%Z -> 0<=B e -> Rabs(B l)+B e<=bpow radix2 em ->
  epsilon+bpow radix2 (em-54)<=B e -> Rabs(target-(B h+B l))<=epsilon ->
  normal_interval_decide64 h l e=Some v -> finite v /\ B v=rndF target.
Proof.
  intros Fh Fl Fe H Em E Low Budget Error Decision.
  assert (Power : bpow radix2 em<=1)by(change 1 with(bpow radix2 0);apply bpow_le;lia).
  destruct(fsub16 l e Fl Fe)as[Fminus Minus].
  { eapply Rle_trans;[apply Rabs_triang|];rewrite Rabs_Ropp,(Rabs_pos_eq(B e))by lra;lra. }
  destruct(fadd16 l e Fl Fe)as[Fplus Plus].
  { eapply Rle_trans;[apply Rabs_triang|];rewrite(Rabs_pos_eq(B e))by lra;lra. }
  assert (RoundBound : forall a,Rabs a<=1 -> Rabs(rndF a)<=1).
  { intros a A;apply abs_round_le_generic;[exact _|exact _| |exact A].
    change 1 with(bpow radix2 0);apply generic_format_bpow;unfold FLT_exp,emin,prec;lia. }
  assert (MinusBound : Rabs(B(fsub l e))<=1).
  { rewrite Minus;apply RoundBound;eapply Rle_trans;[apply Rabs_triang|];rewrite Rabs_Ropp,(Rabs_pos_eq(B e))by lra;lra. }
  assert (PlusBound : Rabs(B(fadd l e))<=1).
  { rewrite Plus;apply RoundBound;eapply Rle_trans;[apply Rabs_triang|];rewrite(Rabs_pos_eq(B e))by lra;lra. }
  assert (Add : forall a,finite a -> Rabs(B a)<=1 ->
    finite(fadd h a) /\ B(fadd h a)=rndF(B h+B a)).
  { intros a Fa A;apply(fadd_ok 1 11 h a Fh Fa ltac:(lia)ltac:(lia)ltac:(reflexivity)ltac:(lia)).
    unfold bnd;change(bpow radix2 11)with 2048;rewrite Rmult_1_l.
    eapply Rle_trans;[apply Rabs_triang|];lra. }
  destruct(Add _ Fminus MinusBound)as[Flow LowValue];destruct(Add _ Fplus PlusBound)as[Fhigh HighValue].
  unfold normal_interval_decide64 in Decision.
  destruct(Z.eqb(bits_of_b64(fadd h (fsub l e)))(bits_of_b64(fadd h (fadd l e))))eqn:Equal;[|discriminate].
  apply Z.eqb_eq in Equal;injection Decision as Value;subst v.
  assert (Roundtrip : forall a,b64_of_bits(bits_of_b64 a)=a).
  { intros a;unfold b64_of_bits,bits_of_b64;exact(binary_float_of_bits_of_binary_float 52 11 eq_refl eq_refl eq_refl a). }
  assert (Same : fadd h (fsub l e)=fadd h (fadd l e)).
  { rewrite <-(Roundtrip(fadd h (fsub l e))),<-(Roundtrip(fadd h (fadd l e)));rewrite Equal;reflexivity. }
  assert (Endpoints : rndF(B h+rndF(B l-B e))=rndF(B h+rndF(B l+B e))).
  { rewrite <-Minus,<-Plus,<-LowValue,<-HighValue,Same;reflexivity. }
  split;[exact Flow|];rewrite LowValue,Minus.
  symmetry;exact(const_test_real (B h)(B l)(B e)target epsilon em (proj1 Em)E Low Budget Error Endpoints).
Qed.
