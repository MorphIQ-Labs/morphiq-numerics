(** Candidate formation on the final uniform grid, including positive zero.
    Absolute value enforces the encoding invariant before adjacent-bit steps. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Mul Encodings RoundingTest.
Require Import StageGappa ErfcxDecision ErfcxSubnormalBits NormalUnderflowRound NormalComparisons.
Open Scope R_scope.

Lemma normal_small_bits n : (0<=n<2^53)%Z ->
  finite(b64_of_bits n) /\ B(b64_of_bits n)=IZR n*bpow radix2 (-1074).
Proof.
  intros N;destruct(Z.eq_dec n 0)as[Zero|Positive].
  - subst n;split;[reflexivity|change(0=0*bpow radix2 (-1074));ring].
  - apply small_bits_value;lia.
Qed.

Lemma normal_nonnegative_encoding c : finite c -> Bsign 53 1024 c=false ->
  0<=B c<bpow radix2 (-1021) ->
  (0<=bits_of_b64 c<2^53)%Z /\ B c=IZR(bits_of_b64 c)*bpow radix2 (-1074).
Proof.
  intros F Sign Range;destruct(Req_dec(B c)0)as[Zero|Positive].
  - assert(C : c=b64_of_bits 0).
    { apply(B2R_Bsign_inj 53 1024);[exact F|reflexivity|exact Zero|exact Sign]. }
    subst c;split;[change(0<=0<9007199254740992)%Z;lia|change(0=0*bpow radix2 (-1074));ring].
  - destruct(small_positive_encoding c F ltac:(split;lra))as[N V].
    split;[lia|exact V].
Qed.

Definition normal_underflow_initial64 h := b64_abs(fmul h (erfcx_pow2 (-600))).

Lemma normal_underflow_initial_ieee h : finite h -> 0<=B h<=3*bpow radix2 (-423) ->
  let c:=normal_underflow_initial64 h in
  finite c /\ Bsign 53 1024 c=false /\ 0<=B c<=7*bpow radix2 (-1024) /\
  Rabs(B c-B h*bpow radix2 (-600))<=bpow radix2 (-1075).
Proof.
  intros Fh H;destruct(erfcx_pow2_ok (-600)ltac:(lia))as[Fk K].
  assert(Range : 0<=B h*bpow radix2 (-600)<=3*bpow radix2 (-1023)).
  { replace(bpow radix2 (-1023))with(bpow radix2 (-423)*bpow radix2 (-600))by(rewrite <-bpow_plus;reflexivity).
    pose proof(bpow_gt_0 radix2 (-600));nra. }
  assert(Bound : bnd 3 (-1023)(B h*B(erfcx_pow2(-600)))).
  { unfold bnd;rewrite K,Rabs_pos_eq by lra;lra. }
  destruct(fmul_ok 3 (-1023)h (erfcx_pow2(-600))Fh Fk
    ltac:(lia)ltac:(lia)ltac:(reflexivity)ltac:(lia)Bound)as[Fc C].
  rewrite K in C.
  assert(Nonnegative : 0<=B(fmul h (erfcx_pow2(-600)))).
  { rewrite C;replace 0 with(rndF 0)by(apply round_0;apply valid_rnd_N).
    apply round_le;[exact _|exact _|lra]. }
  assert(Error : Rabs(B(fmul h (erfcx_pow2(-600)))-B h*bpow radix2 (-600))<=bpow radix2 (-1075)).
  { rewrite C;eapply Rle_trans;[apply error_le_half_ulp;exact _|].
    rewrite ulp_FLT_small;[|exact _|].
    - change(/2)with(bpow radix2 (-1));rewrite <-bpow_plus;apply Rle_refl.
    - rewrite Rabs_pos_eq by lra;change(emin+prec)%Z with(-1021)%Z;bpow_num_all;lra. }
  assert(Fabs : finite(normal_underflow_initial64 h)).
  { unfold normal_underflow_initial64,b64_abs;destruct(fmul h (erfcx_pow2(-600)));exact Fc. }
  assert(Sign : Bsign 53 1024 (normal_underflow_initial64 h)=false).
  { unfold normal_underflow_initial64,b64_abs;apply Bsign_Babs.
    destruct(fmul h (erfcx_pow2(-600)));try reflexivity;discriminate. }
  assert(Value : B(normal_underflow_initial64 h)=B(fmul h (erfcx_pow2(-600)))).
  { unfold normal_underflow_initial64;rewrite B_abs,Rabs_pos_eq;[reflexivity|exact Nonnegative]. }
  cbv zeta;split;[exact Fabs|];split;[exact Sign|];rewrite Value.
  split;[|exact Error];apply Rabs_le_inv in Error;bpow_num_all;split;lra.
Qed.

Lemma normal_underflow_adjacent c d : finite c -> Bsign 53 1024 c=false ->
  0<=B c<=7*bpow radix2 (-1024) -> (-1<=d<=1)%Z -> (0<=bits_of_b64 c+d)%Z ->
  let v:=b64_of_bits(bits_of_b64 c+d)in
  finite v /\ (B v=0 \/ bpow radix2 (-1074)<=B v) /\ B v<=bpow radix2 (-1021) /\
  Rabs(B v-B c)<=bpow radix2 (-1074).
Proof.
  intros Fc Sign C D Lower.
  destruct(normal_nonnegative_encoding c Fc Sign ltac:(bpow_num_all;split;lra))as[N V].
  assert(Upper : (bits_of_b64 c<=9007199254740990)%Z).
  { apply le_IZR;change(IZR(bits_of_b64 c)<=9007199254740990).
    rewrite V in C;bpow_num_all;lra. }
  assert(Index : (0<=bits_of_b64 c+d<2^53)%Z)by(change(0<=bits_of_b64 c+d<9007199254740992)%Z;lia).
  destruct(normal_small_bits _ Index)as[Fv Value].
  cbv zeta;split;[exact Fv|];rewrite Value;split.
  - destruct(Z.eq_dec(bits_of_b64 c+d)0)as[Zero|Positive].
    + left;rewrite Zero;change(0*bpow radix2 (-1074)=0);ring.
    + right;assert(1<=IZR(bits_of_b64 c+d))by(change(IZR 1<=IZR(bits_of_b64 c+d));apply IZR_le;lia).
      pose proof(bpow_gt_0 radix2 (-1074));nra.
  - split.
    + assert(IZR(bits_of_b64 c+d)<=IZR(2^53))by(apply IZR_le;lia).
      change(IZR(2^53))with(bpow radix2 53)in H.
      replace(bpow radix2 (-1021))with(bpow radix2 53*bpow radix2 (-1074))by(rewrite <-bpow_plus;reflexivity).
      apply Rmult_le_compat_r;[apply bpow_ge_0|exact H].
    + rewrite plus_IZR,V;replace((IZR(bits_of_b64 c)+IZR d)*bpow radix2 (-1074)-IZR(bits_of_b64 c)*bpow radix2 (-1074))with(IZR d*bpow radix2 (-1074))by ring.
      rewrite Rabs_mult,(Rabs_pos_eq(bpow radix2 (-1074)))by apply bpow_ge_0.
      replace(bpow radix2 (-1074))with(1*bpow radix2 (-1074))at 2 by ring.
      apply Rmult_le_compat_r;[apply bpow_ge_0|apply Rabs_le;change(IZR(-1)<=IZR d<=IZR 1);split;apply IZR_le;lia].
Qed.

Definition normal_underflow_candidate64 h l :=
  let c:=normal_underflow_initial64 h in
  let r:=ErfcxSubnormal.subnormal_residual64 h l c in
  match Bcompare 53 1024 r (erfcx_pow2 (-475))with
  | Some Gt=>b64_of_bits(bits_of_b64 c+1)
  | _=>match Bcompare 53 1024 r (fneg(erfcx_pow2(-475)))with
    | Some Lt=>if normal_lt normal_zero c then b64_of_bits(bits_of_b64 c-1)else c
    | _=>c end end.
Definition normal_underflow_fast64 h l := normal_underflow_accept64 h l (normal_underflow_candidate64 h l).

Lemma normal_underflow_candidate_ieee h l : finite h -> 0<=B h<=3*bpow radix2 (-423) ->
  let c:=normal_underflow_candidate64 h l in
  finite c /\ (B c=0 \/ bpow radix2 (-1074)<=B c) /\ B c<=bpow radix2 (-1021) /\
  Rabs(B h-B c*bpow radix2 600)<=bpow radix2 (-473).
Proof.
  intros Fh H;pose proof(normal_underflow_initial_ieee h Fh H)as Initial.
  cbv zeta in Initial;destruct Initial as[Fi [Sign [I Error]]].
  set(c:=normal_underflow_initial64 h)in *.
  destruct(normal_nonnegative_encoding c Fi Sign ltac:(bpow_num_all;split;lra))as[N V].
  assert(Step : forall d,(-1<=d<=1)%Z -> (0<=bits_of_b64 c+d)%Z ->
    let v:=b64_of_bits(bits_of_b64 c+d)in
    finite v /\ (B v=0 \/ bpow radix2 (-1074)<=B v) /\ B v<=bpow radix2 (-1021) /\
    Rabs(B h-B v*bpow radix2 600)<=bpow radix2 (-473)).
  { intros d D Lower;pose proof(normal_underflow_adjacent c d Fi Sign I D Lower)as Adj.
    cbv zeta in Adj|-*;destruct Adj as[Fv [Low [High Close]]];repeat split;try assumption.
    assert(Gap : Rabs(B h*bpow radix2 (-600)-B(b64_of_bits(bits_of_b64 c+d)))<=bpow radix2 (-1075)+bpow radix2 (-1074)).
    { replace(B h*bpow radix2 (-600)-B(b64_of_bits(bits_of_b64 c+d)))with
        ((B h*bpow radix2 (-600)-B c)+(B c-B(b64_of_bits(bits_of_b64 c+d))))by ring.
      eapply Rle_trans;[apply Rabs_triang|];rewrite Rabs_minus_sym in Error,Close;lra. }
    replace(B h-B(b64_of_bits(bits_of_b64 c+d))*bpow radix2 600)with
      ((B h*bpow radix2 (-600)-B(b64_of_bits(bits_of_b64 c+d)))*bpow radix2 600).
    - rewrite Rabs_mult,(Rabs_pos_eq(bpow radix2 600))by apply bpow_ge_0.
      apply Rle_trans with((bpow radix2 (-1075)+bpow radix2 (-1074))*bpow radix2 600).
      + apply Rmult_le_compat_r;[apply bpow_ge_0|exact Gap].
      + rewrite Rmult_plus_distr_r,<-!bpow_plus;change(-1075+600)%Z with(-475)%Z;change(-1074+600)%Z with(-474)%Z;bpow_num;lra.
    - rewrite Rmult_minus_distr_r,Rmult_assoc,<-bpow_plus;change(bpow radix2 (-600+600))with 1;ring. }
  pose proof(Step 0%Z ltac:(lia)ltac:(lia))as Stay.
  rewrite Z.add_0_r in Stay.
  assert(Roundtrip : b64_of_bits(bits_of_b64 c)=c).
  { unfold b64_of_bits,bits_of_b64;exact(binary_float_of_bits_of_binary_float 52 11 eq_refl eq_refl eq_refl c). }
  rewrite Roundtrip in Stay.
  pose proof(Step 1%Z ltac:(lia)ltac:(lia))as Up.
  assert(Down : normal_lt normal_zero c=true ->
    let v:=b64_of_bits(bits_of_b64 c-1)in
    finite v /\ (B v=0 \/ bpow radix2 (-1074)<=B v) /\ B v<=bpow radix2 (-1021) /\
    Rabs(B h-B v*bpow radix2 600)<=bpow radix2 (-473)).
  { intros Positive;apply normal_lt_true in Positive;[|reflexivity|exact Fi].
    change(0<B c)in Positive;rewrite V in Positive.
    assert(Index : (0<bits_of_b64 c)%Z).
    { destruct(Z_le_gt_dec(bits_of_b64 c)0);[assert(bits_of_b64 c=0)%Z by lia;rewrite H0 in Positive;change(0<0*bpow radix2 (-1074))in Positive;nra|lia]. }
    change(bits_of_b64 c-1)%Z with(bits_of_b64 c+ -1)%Z;apply Step;lia. }
  unfold normal_underflow_candidate64;fold c.
  destruct(Bcompare 53 1024 _ _)as[[| |]|];try exact Up;
    destruct(Bcompare 53 1024 _ _)as[[| |]|];try exact Stay;
    destruct(normal_lt normal_zero c)eqn:Positive;solve[exact(Down eq_refl)|exact Stay].
Qed.

Theorem normal_underflow_fast_ieee h l z v : finite h -> finite l ->
  0<=B h<=3*bpow radix2 (-423) -> Rabs(B l)<=bpow radix2 (-473) ->
  Rabs(z-(B h+B l))<=3*bpow radix2 (-67)*B h ->
  normal_underflow_fast64 h l=Some v -> finite v /\ B v=rndF(z*bpow radix2 (-600)).
Proof.
  intros Fh Fl H L Error Decision.
  pose proof(normal_underflow_candidate_ieee h l Fh H)as Candidate.
  cbv zeta in Candidate;destruct Candidate as[Fc [C [Upper Close]]].
  apply(normal_underflow_accept_ieee h l (normal_underflow_candidate64 h l)z v);try assumption.
  bpow_num_all;split;lra.
Qed.
