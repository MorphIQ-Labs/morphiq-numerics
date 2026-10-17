(** Absolute final-grid rounding, including zero. The extra absolute guard
    covers rounding the residual when its candidate is the smallest value. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 RoundingTest RoundingConstant.
Require Import StageGappa ErfcxSubnormal.
Open Scope R_scope.

Lemma normal_round_absolute_zero u z : fmtF u -> 0<=u ->
  Rabs(z-u)<bpow radix2 (-1075) -> rndF z=u.
Proof.
  intros Fu U Close;destruct(Req_dec u 0)as[Zero|Positive].
  2: apply binary64_round_absolute;assumption || lra.
  subst u;rewrite Rminus_0_r in Close.
  destruct(Req_dec z 0)as[Z|Z].
  - subst z;apply round_0;apply valid_rnd_N.
  - apply(round_N_small radix2 (FLT_exp emin prec) (fun n => negb (Z.even n)) z (mag radix2 z)).
    + split;[apply bpow_mag_le|apply bpow_mag_gt];exact Z.
    + assert(M : (mag radix2 z<= -1075)%Z)by(apply mag_le_bpow;assumption).
      unfold FLT_exp,emin,prec;lia.
Qed.

Definition normal_underflow_residual h l c := rndF(rndF(h-c*bpow radix2 600)+l).
Definition normal_underflow_guard h := rndF(rndF(h*bpow radix2 (-65))+bpow radix2 (-520)).

Lemma normal_underflow_residual_error h l c :
  Rabs l<=bpow radix2 (-473) -> Rabs(h-c*bpow radix2 600)<=bpow radix2 (-473) ->
  Rabs(normal_underflow_residual h l c-((h-c*bpow radix2 600)+l))<=bpow radix2 (-525).
Proof.
  intros L C.
  pose proof(rnd_err_below _ (-473)ltac:(lia)C)as First.
  assert(D : Rabs(rndF(h-c*bpow radix2 600))<=bpow radix2 (-473)).
  { apply abs_round_le_generic;[exact _|exact _| |exact C].
    apply generic_format_bpow;unfold FLT_exp,emin,prec;lia. }
  assert(S : Rabs(rndF(h-c*bpow radix2 600)+l)<=bpow radix2 (-472)).
  { eapply Rle_trans;[apply Rabs_triang|];bpow_num_all;lra. }
  pose proof(rnd_err_below _ (-472)ltac:(lia)S)as Second.
  change (-473-54)%Z with (-527)%Z in First.
  change (-472-54)%Z with (-526)%Z in Second.
  unfold normal_underflow_residual.
  replace(rndF(rndF(h-c*bpow radix2 600)+l)-(h-c*bpow radix2 600+l))with
    ((rndF(rndF(h-c*bpow radix2 600)+l)-(rndF(h-c*bpow radix2 600)+l))+
     (rndF(h-c*bpow radix2 600)-(h-c*bpow radix2 600)))by ring.
  eapply Rle_trans;[apply Rabs_triang|];bpow_num_all;lra.
Qed.

Lemma normal_underflow_guard_budget h : 0<=h<=bpow radix2 (-421) ->
  3*bpow radix2 (-67)*h+bpow radix2 (-525)<=normal_underflow_guard h.
Proof.
  intros H.
  assert(P : Rabs(h*bpow radix2 (-65))<=bpow radix2 (-486)).
  { rewrite Rabs_mult,!(Rabs_pos_eq _)by(pose proof(bpow_gt_0 radix2 (-65));lra).
    replace(bpow radix2 (-486))with(bpow radix2 (-421)*bpow radix2 (-65))by(rewrite <-bpow_plus;reflexivity).
    apply Rmult_le_compat_r;[apply bpow_ge_0|lra]. }
  pose proof(rnd_err_below _ (-486)ltac:(lia)P)as Mul.
  assert(M : Rabs(rndF(h*bpow radix2 (-65)))<=bpow radix2 (-486)).
  { apply abs_round_le_generic;[exact _|exact _| |exact P].
    apply generic_format_bpow;unfold FLT_exp,emin,prec;lia. }
  assert(S : Rabs(rndF(h*bpow radix2 (-65))+bpow radix2 (-520))<=bpow radix2 (-485)).
  { eapply Rle_trans;[apply Rabs_triang|];rewrite(Rabs_pos_eq(bpow radix2 (-520)))by apply bpow_ge_0;bpow_num_all;lra. }
  pose proof(rnd_err_below _ (-485)ltac:(lia)S)as Add.
  change (-486-54)%Z with (-540)%Z in Mul.
  change (-485-54)%Z with (-539)%Z in Add.
  unfold normal_underflow_guard;apply Rabs_le_inv in Mul,Add;bpow_num_all;nra.
Qed.

Theorem normal_underflow_guard_real h l c z :
  0<=h<=bpow radix2 (-421) ->
  Rabs l<=bpow radix2 (-473) -> Rabs(h-c*bpow radix2 600)<=bpow radix2 (-473) ->
  Rabs(z-(h+l))<=3*bpow radix2 (-67)*h ->
  rndF(Rabs(normal_underflow_residual h l c)+normal_underflow_guard h)<bpow radix2 (-475) ->
  Rabs(z*bpow radix2 (-600)-c)<bpow radix2 (-1075).
Proof.
  intros H L C E Guard.
  pose proof(normal_underflow_residual_error h l c L C)as Residual.
  pose proof(normal_underflow_guard_budget h H)as Budget.
  assert(Raw : Rabs(normal_underflow_residual h l c)+normal_underflow_guard h<bpow radix2 (-475)).
  { apply Rnot_le_lt;intros Contra.
    pose proof(round_le radix2 (FLT_exp emin prec) ZnearestE _ _ Contra)as Mono.
    assert(Half : rndF(bpow radix2 (-475))=bpow radix2 (-475)).
    { apply round_generic;[exact _|];apply generic_format_bpow;unfold FLT_exp,emin,prec;lia. }
    change(rndF(bpow radix2 (-475))<=rndF(Rabs(normal_underflow_residual h l c)+normal_underflow_guard h))in Mono.
    rewrite Half in Mono;lra. }
  assert(Close : Rabs(z-c*bpow radix2 600)<bpow radix2 (-475)).
  { replace(z-c*bpow radix2 600)with((z-(h+l))+
      (((h-c*bpow radix2 600)+l)-normal_underflow_residual h l c)+normal_underflow_residual h l c)by ring.
    eapply Rle_lt_trans;[apply Rabs_triang|].
    pose proof(Rabs_triang (z-(h+l)) (((h-c*bpow radix2 600)+l)-normal_underflow_residual h l c)).
    rewrite Rabs_minus_sym in Residual;lra. }
  replace(z*bpow radix2 (-600)-c)with((z-c*bpow radix2 600)*bpow radix2 (-600)).
  - rewrite Rabs_mult,(Rabs_pos_eq(bpow radix2 (-600)))by apply bpow_ge_0.
    replace(bpow radix2 (-1075))with(bpow radix2 (-475)*bpow radix2 (-600))by(rewrite <-bpow_plus;reflexivity).
    apply Rmult_lt_compat_r;[apply bpow_gt_0|exact Close].
  - rewrite Rmult_minus_distr_r,Rmult_assoc,<-bpow_plus;change(bpow radix2 (600+ -600))with 1;ring.
Qed.

Definition normal_underflow_guard64 h :=
  fadd (fmul h (ErfcxDecision.erfcx_pow2 (-65))) (ErfcxDecision.erfcx_pow2 (-520)).
Definition normal_underflow_accept64 h l c :=
  match Bcompare 53 1024
    (fadd (b64_abs (ErfcxSubnormal.subnormal_residual64 h l c)) (normal_underflow_guard64 h))
    (ErfcxDecision.erfcx_pow2 (-475)) with
  | Some Lt=>Some c | _=>None end.

Lemma normal_underflow_back c : finite c ->
  (B c=0 \/ bpow radix2 (-1074)<=B c) -> B c<=bpow radix2 (-1021) ->
  finite(fmul c (ErfcxDecision.erfcx_pow2 600)) /\
  B(fmul c (ErfcxDecision.erfcx_pow2 600))=B c*bpow radix2 600.
Proof.
  intros F C Upper;destruct C as[Zero|Positive].
  - destruct(ErfcxDecision.erfcx_pow2_ok 600 ltac:(lia))as[Fc C].
    destruct(fmul_exact c (ErfcxDecision.erfcx_pow2 600)F Fc)as[Fv V].
    + rewrite Zero,Rmult_0_l;apply generic_format_0.
    + rewrite Zero,Rmult_0_l,Rabs_R0;apply bpow_gt_0.
    + split;[exact Fv|rewrite V,C;reflexivity].
  - destruct(subnormal_candidate_back_ieee c F ltac:(split;assumption))as[Fv [V _]].
    split;assumption.
Qed.

Lemma normal_underflow_residual_ieee h l c : finite h -> finite l -> finite c ->
  Rabs(B l)<=bpow radix2 (-473) ->
  (B c=0 \/ bpow radix2 (-1074)<=B c) -> B c<=bpow radix2 (-1021) ->
  Rabs(B h-B c*bpow radix2 600)<=bpow radix2 (-473) ->
  finite(subnormal_residual64 h l c) /\
  B(subnormal_residual64 h l c)=normal_underflow_residual(B h)(B l)(B c) /\
  Rabs(B(subnormal_residual64 h l c))<=bpow radix2 (-472).
Proof.
  intros Fh Fl Fc L C Upper Close.
  destruct(normal_underflow_back c Fc C Upper)as[Fb Back].
  destruct(fsub_bnd 1 (-473) h (fmul c (ErfcxDecision.erfcx_pow2 600))Fh Fb
    ltac:(lia)ltac:(lia)ltac:(reflexivity)ltac:(lia)
    ltac:(unfold bnd;rewrite Rmult_1_l,Back;exact Close))as[Fd [D Bound]].
  unfold bnd in Bound;rewrite Rmult_1_l in Bound.
  assert(S : bnd 1 (-472)(B(fsub h (fmul c (ErfcxDecision.erfcx_pow2 600)))+B l)).
  { unfold bnd;rewrite Rmult_1_l;eapply Rle_trans;[apply Rabs_triang|];bpow_num_all;lra. }
  destruct(fadd_bnd 1 (-472) (fsub h (fmul c (ErfcxDecision.erfcx_pow2 600)))l Fd Fl
    ltac:(lia)ltac:(lia)ltac:(reflexivity)ltac:(lia)S)as[Fr [R Rbound]].
  unfold bnd in Rbound;rewrite Rmult_1_l in Rbound.
  unfold subnormal_residual64;repeat split;try assumption.
  rewrite R,D,Back;reflexivity.
Qed.

Lemma normal_underflow_guard_ieee h : finite h -> 0<=B h<=bpow radix2 (-421) ->
  finite(normal_underflow_guard64 h) /\
  B(normal_underflow_guard64 h)=normal_underflow_guard(B h) /\
  Rabs(B(normal_underflow_guard64 h))<=bpow radix2 (-485).
Proof.
  intros Fh H.
  destruct(ErfcxDecision.erfcx_pow2_ok (-65)ltac:(lia))as[Fc C].
  destruct(ErfcxDecision.erfcx_pow2_ok (-520)ltac:(lia))as[Fa A].
  assert(P : bnd 1 (-486)(B h*B(ErfcxDecision.erfcx_pow2(-65)))).
  { unfold bnd;rewrite Rmult_1_l,C,Rabs_mult,!(Rabs_pos_eq _)by(pose proof(bpow_gt_0 radix2 (-65));lra).
    replace(bpow radix2 (-486))with(bpow radix2 (-421)*bpow radix2 (-65))by(rewrite <-bpow_plus;reflexivity).
    apply Rmult_le_compat_r;[apply bpow_ge_0|lra]. }
  destruct(fmul_bnd 1 (-486)h (ErfcxDecision.erfcx_pow2(-65))Fh Fc
    ltac:(lia)ltac:(lia)ltac:(reflexivity)ltac:(lia)P)as[Fp [Product Bound]].
  unfold bnd in Bound;rewrite Rmult_1_l in Bound.
  assert(S : bnd 1 (-485)(B(fmul h (ErfcxDecision.erfcx_pow2(-65)))+B(ErfcxDecision.erfcx_pow2(-520)))).
  { unfold bnd;rewrite Rmult_1_l;eapply Rle_trans;[apply Rabs_triang|];rewrite A,(Rabs_pos_eq(bpow radix2 (-520)))by apply bpow_ge_0;bpow_num_all;lra. }
  destruct(fadd_bnd 1 (-485)(fmul h (ErfcxDecision.erfcx_pow2(-65)))(ErfcxDecision.erfcx_pow2(-520))Fp Fa
    ltac:(lia)ltac:(lia)ltac:(reflexivity)ltac:(lia)S)as[Fe [Value BoundE]].
  unfold bnd in BoundE;rewrite Rmult_1_l in BoundE.
  unfold normal_underflow_guard64;repeat split;try assumption.
  rewrite Value,Product,C,A;reflexivity.
Qed.

Local Opaque ErfcxDecision.erfcx_pow2 normal_underflow_guard64 subnormal_residual64 fadd fmul.

Theorem normal_underflow_accept_ieee h l c z v : finite h -> finite l -> finite c ->
  0<=B h<=bpow radix2 (-421) -> Rabs(B l)<=bpow radix2 (-473) ->
  (B c=0 \/ bpow radix2 (-1074)<=B c) -> B c<=bpow radix2 (-1021) ->
  Rabs(B h-B c*bpow radix2 600)<=bpow radix2 (-473) ->
  Rabs(z-(B h+B l))<=3*bpow radix2 (-67)*B h ->
  normal_underflow_accept64 h l c=Some v -> finite v /\ B v=rndF(z*bpow radix2 (-600)).
Proof.
  intros Fh Fl Fc H L C Upper Close Error Decision.
  destruct(normal_underflow_residual_ieee h l c Fh Fl Fc L C Upper Close)as[Fr [R Rbound]].
  destruct(normal_underflow_guard_ieee h Fh H)as[Fe [E Ebound]].
  destruct(ErfcxDecision.erfcx_pow2_ok (-475)ltac:(lia))as[Fhalf Half].
  assert(Fabs : finite(b64_abs(subnormal_residual64 h l c)))by(unfold b64_abs;destruct(subnormal_residual64 h l c);exact Fr).
  assert(S : bnd 1 (-471)(B(b64_abs(subnormal_residual64 h l c))+B(normal_underflow_guard64 h))).
  { unfold bnd;rewrite Rmult_1_l;eapply Rle_trans;[apply Rabs_triang|];rewrite B_abs,Rabs_Rabsolu;bpow_num_all;lra. }
  destruct(fadd_ok 1 (-471)(b64_abs(subnormal_residual64 h l c))(normal_underflow_guard64 h)Fabs Fe
    ltac:(lia)ltac:(lia)ltac:(reflexivity)ltac:(lia)S)as[Fs Sum].
  unfold normal_underflow_accept64 in Decision.
  destruct(Bcompare 53 1024 _ _)as[[| |]|]eqn:Cmp;try discriminate.
  injection Decision as <-;split;[exact Fc|].
  rewrite Bcompare_correct in Cmp by assumption;injection Cmp as Cmp;apply Rcompare_Lt_inv in Cmp.
  rewrite Sum,Half,B_abs,R,E in Cmp.
  symmetry;apply normal_round_absolute_zero;[apply B_fmt| |].
  - destruct C;pose proof(bpow_gt_0 radix2 (-1074));lra.
  - exact(normal_underflow_guard_real(B h)(B l)(B c)z H L Close Error Cmp).
Qed.
