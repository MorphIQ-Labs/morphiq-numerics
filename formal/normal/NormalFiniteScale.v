(** Keep the finite-tail expansion normal by scaling it to 2^600 times
    the final result. The residual word may underflow only when it is too
    small to affect the composition guard; its error is explicitly bounded. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core Mult_error.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Mul RoundingConstant RoundingCore RoundingGaps RoundingTest.
Require Import StageGappa ErfcxDecision.
Open Scope R_scope.

Theorem normal_finite_scaled_word_ieee x k : finite x -> Rabs(B x)<=8 -> (-501<=k<=0)%Z ->
  let y:=fmul x (erfcx_pow2 k)in
  finite y /\ B y=rndF(B x*bpow radix2 k) /\ Rabs(B y)<=8 /\
  Rabs(B y-B x*bpow radix2 k)<=bpow radix2 (k-554) /\
  (bpow radix2 (-500)<=Rabs(B x) -> B y=B x*bpow radix2 k).
Proof.
  intros F X K y;destruct(erfcx_pow2_ok k ltac:(lia))as[Fk Scale].
  assert (Power : 0<bpow radix2 k<=1).
  { split;[apply bpow_gt_0|change 1 with(bpow radix2 0);apply bpow_le;lia]. }
  assert (Product : Rabs(B x*B(erfcx_pow2 k))<=8).
  { rewrite Scale,Rabs_mult,(Rabs_pos_eq(bpow radix2 k))by lra;pose proof(Rabs_pos(B x));nra. }
  destruct(fmul16 x (erfcx_pow2 k)F Fk ltac:(lra))as[Fy Value];fold y in Fy,Value;rewrite Scale in Value.
  assert (Exact : bpow radix2 (-500)<=Rabs(B x) -> B y=B x*bpow radix2 k).
  { intros Large;rewrite Value;apply round_generic;[exact _|].
    apply mult_bpow_exact_FLT;[apply B_fmt|].
    assert(M : (-499<=mag radix2 (B x))%Z)by(apply mag_ge_bpow;exact Large).
    unfold emin,prec;lia. }
  assert (Error : Rabs(B y-B x*bpow radix2 k)<=bpow radix2 (k-554)).
  { destruct(Rle_dec (bpow radix2 (-500))(Rabs(B x)))as[Large|Small].
    - rewrite(Exact Large),Rminus_diag_eq,Rabs_R0 by reflexivity;apply bpow_ge_0.
    - rewrite Value;replace(k-554)%Z with((k-500)-54)%Z by ring.
      apply rnd_err_below;[lia|].
      rewrite Rabs_mult,(Rabs_pos_eq(bpow radix2 k))by lra.
      replace(k-500)%Z with(-500+k)%Z by ring;rewrite bpow_plus.
      apply Rmult_le_compat_r;lra. }
  split;[exact Fy|];split;[exact Value|];split;[|split;assumption].
  rewrite Value;apply abs_round_le_generic;[exact _|exact _| |rewrite <-Scale;exact Product].
  change 8 with(bpow radix2 3);apply generic_format_bpow;unfold FLT_exp,emin,prec;lia.
Qed.

Definition normal_finite_scaled64 h l k :=
  (fmul h (erfcx_pow2 k),fmul l (erfcx_pow2 k)).

Theorem normal_finite_scaled_ieee h l k z : finite h -> finite l ->
  bpow radix2 (-10)<=B h<=4 -> Rabs(B l)<=bpow radix2 (-52)*B h ->
  (-501<=k<=0)%Z ->
  Rabs(z-(B h+B l))<=11*bpow radix2 (-69)*B h ->
  let '(a,b):=normal_finite_scaled64 h l k in
  finite a /\ finite b /\ B a=B h*bpow radix2 k /\
  bpow radix2 (k-10)<=B a<=4*bpow radix2 k /\
  Rabs(B b)<=5*bpow radix2 (-54)*B a /\
  Rabs(z*bpow radix2 k-(B a+B b))<=3*bpow radix2 (-67)*B a.
Proof.
  intros Fh Fl H L K Error.
  pose proof(normal_finite_scaled_word_ieee h k Fh
    ltac:(rewrite Rabs_pos_eq;bpow_num_all;lra)K)as High.
  pose proof(normal_finite_scaled_word_ieee l k Fl
    ltac:(bpow_num_all;lra)K)as Low.
  cbv zeta in High,Low;destruct High as[Fa [A [Ar [Ae Exact]]]].
  destruct Low as[Fb [Bvalue [Br [Be _]]]].
  specialize(Exact ltac:(rewrite Rabs_pos_eq by(pose proof(bpow_gt_0 radix2(-10));lra);
    apply Rle_trans with(bpow radix2(-10));[apply bpow_le;lia|exact(proj1 H)])).
  unfold normal_finite_scaled64;rewrite Exact.
  replace(k-554)%Z with(k+ -554)%Z in Be by ring;rewrite bpow_plus in Be.
  set(s:=bpow radix2 k)in *;assert(S : 0<s)by(apply bpow_gt_0).
  assert(ScaledLow : Rabs(B(fmul l (erfcx_pow2 k)))<=5*bpow radix2 (-54)*(B h*s)).
  { replace(B(fmul l (erfcx_pow2 k)))with
      ((B(fmul l (erfcx_pow2 k))-B l*s)+B l*s)at 1 by ring.
    eapply Rle_trans;[apply Rabs_triang|];rewrite Rabs_mult,(Rabs_pos_eq s)by lra.
    assert(M : Rabs(B l)*s<=bpow radix2 (-52)*B h*s)by(apply Rmult_le_compat_r;lra).
    assert(Tiny : bpow radix2 (-554)<=bpow radix2 (-54)*B h).
    { eapply Rle_trans;[|apply Rmult_le_compat_l;[apply bpow_ge_0|exact(proj1 H)]].
      rewrite <-bpow_plus;apply bpow_le;lia. }
    assert(C : 5*bpow radix2 (-54)=bpow radix2 (-52)+bpow radix2 (-54))by(bpow_num;field).
    rewrite C;nra. }
  repeat split;try assumption.
  - replace(k-10)%Z with(-10+k)%Z by ring;rewrite bpow_plus;apply Rmult_le_compat_r;lra.
  - apply Rmult_le_compat_r;lra.
  - replace(z*s-(B h*s+B(fmul l (erfcx_pow2 k))))with
      ((z-(B h+B l))*s-(B(fmul l (erfcx_pow2 k))-B l*s))by ring.
    eapply Rle_trans;[apply Rabs_triang|];rewrite Rabs_Ropp,Rabs_mult,(Rabs_pos_eq s)by lra.
    assert(M : Rabs(z-(B h+B l))*s<=(11*bpow radix2 (-69)*B h)*s)by(apply Rmult_le_compat_r;lra).
    assert(Tiny : bpow radix2 (-554)<=bpow radix2 (-69)*B h).
    { eapply Rle_trans;[|apply Rmult_le_compat_l;[apply bpow_ge_0|exact(proj1 H)]].
      rewrite <-bpow_plus;apply bpow_le;lia. }
    assert(C : 3*bpow radix2 (-67)=12*bpow radix2 (-69))by(bpow_num;field).
    rewrite C;nra.
Qed.

Lemma normal_finite_normalized_low h l :
  bpow radix2 (-10)<=h<=4 -> Rabs l<=bpow radix2 (-51)*h -> h=rndF(h+l) ->
  Rabs l<=bpow radix2 (-52)*h.
Proof.
  intros H L Norm.
  assert(Sum : bpow radix2 (-11)<=h+l)by(apply Rabs_le_inv in L;bpow_num_all;lra).
  pose proof(rnd_rel(h+l)ltac:(rewrite Rabs_pos_eq by(pose proof(bpow_gt_0 radix2(-11));lra);
    apply Rle_trans with(bpow radix2(-11));[apply bpow_le;lia|exact Sum]))as Error.
  change(Rabs(rndF(h+l)-(h+l))<=bpow radix2(-53)*Rabs(h+l))in Error.
  rewrite <-Norm in Error;replace(h-(h+l))with(-l)in Error by ring.
  rewrite Rabs_Ropp in Error.
  pose proof(Rabs_triang h l)as Triangle;rewrite(Rabs_pos_eq h)in Triangle by(bpow_num_all;lra).
  bpow_num_all;nra.
Qed.

Theorem normal_finite_scaled_normalized h l k : finite h -> finite l ->
  bpow radix2 (-10)<=B h<=4 -> Rabs(B l)<=bpow radix2 (-52)*B h ->
  B h=rndF(B h+B l) -> (-501<=k<=0)%Z ->
  let '(a,b):=normal_finite_scaled64 h l k in B a=rndF(B a+B b).
Proof.
  intros Fh Fl H L Norm K.
  pose proof(normal_finite_scaled_word_ieee h k Fh
    ltac:(rewrite Rabs_pos_eq;bpow_num_all;lra)K)as High.
  pose proof(normal_finite_scaled_word_ieee l k Fl ltac:(bpow_num_all;lra)K)as Low.
  cbv zeta in High,Low;destruct High as[Fa [A [Ar [Ae Exact]]]].
  destruct Low as[Fb [Bvalue [Br [Be Lexact]]]].
  specialize(Exact ltac:(rewrite Rabs_pos_eq by(pose proof(bpow_gt_0 radix2(-10));lra);
    apply Rle_trans with(bpow radix2(-10));[apply bpow_le;lia|exact(proj1 H)])).
  unfold normal_finite_scaled64.
  destruct(Rle_dec(bpow radix2(-500))(Rabs(B l)))as[Large|Small].
  - rewrite Exact,(Lexact Large),<-Rmult_plus_distr_r.
    assert(Sum : bpow radix2(-11)<=B h+B l)by(apply Rabs_le_inv in L;bpow_num_all;lra).
    assert(M : (-10<=mag radix2(B h+B l))%Z).
    { apply mag_ge_bpow;rewrite Rabs_pos_eq;[exact Sum|pose proof(bpow_gt_0 radix2(-11));lra]. }
    rewrite round_scale by(pose proof(bpow_gt_0 radix2(-11));lra)||lia.
    rewrite <-Norm;reflexivity.
  - symmetry;apply round_relative_close;[apply B_fmt|rewrite Exact;pose proof(bpow_gt_0 radix2 k);bpow_num_all;nra|].
    replace(B(fmul h (erfcx_pow2 k))+B(fmul l (erfcx_pow2 k))-B(fmul h (erfcx_pow2 k)))with
      (B(fmul l (erfcx_pow2 k)))by ring.
    rewrite Exact,Rabs_mult,(Rabs_pos_eq(B h))by(bpow_num_all;lra).
    rewrite(Rabs_pos_eq(bpow radix2 k))by apply bpow_ge_0.
    assert(Bound : Rabs(B(fmul l (erfcx_pow2 k)))<=bpow radix2(k-500)).
    { rewrite Bvalue;apply abs_round_le_generic;[exact _|exact _| |].
      - apply generic_format_bpow;unfold FLT_exp,emin,prec;lia.
      - replace(k-500)%Z with(-500+k)%Z by ring;rewrite bpow_plus,Rabs_mult,
          (Rabs_pos_eq(bpow radix2 k))by apply bpow_ge_0.
        apply Rmult_le_compat_r;[apply bpow_ge_0|lra]. }
    apply Rle_lt_trans with(bpow radix2(k-500));[exact Bound|].
    replace(k-500)%Z with(-500+k)%Z by ring;rewrite bpow_plus.
    assert(Tiny : bpow radix2(-500)<B h/2^54)by(bpow_num_all;lra).
    pose proof(bpow_gt_0 radix2 k);nra.
Qed.
