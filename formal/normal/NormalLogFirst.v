(** Binary64 first stage for the moderate far tail, before the double-word
    candidate. Its wider interval includes all reconstruction errors. *)
From Coq Require Import Reals ZArith Lia Lra Psatz Classical.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Eft RoundingConstant.
Require Import StageGappa ErfcxReciprocal NormalLogReciprocalStage NormalLogTailPolynomial
  NormalLogTailSquare NormalLogMillsIdentity NormalConstants NormalCenterFastTail NormalTailAnalytic ErfcxTailIntegral Ln1pTest ErfcxDecision.
Require normal_log_tail_first.
Open Scope R_scope.

Definition normal_log_first_correction_r h l ch cl p :=
  rn(rn(h+ch)+rn(l+rn(cl+p))).

Lemma normal_log_first_model h l ch cl t e p :
  3<=h<=5 -> Rabs l<=bpow radix2(-12) -> 0.9<=ch<=1 ->
  Rabs cl<=bpow radix2(-54) -> Rabs t<=bpow radix2(-43) ->
  Rabs e<=bpow radix2(-40) -> 0<=p<=0.001 ->
  let c:=normal_log_first_correction_r h l ch cl p in
  Rabs(-(c-(h+l+ch+cl+p))+(rn(e+t)-(e+t)))<=5*bpow radix2(-52) /\
  Rabs(rn(e+t))<=bpow radix2(-39) /\ 3<=c<=7.
Proof.
  intros H L Ch Cl T E P;unfold normal_log_first_correction_r;cbv zeta.
  apply Rabs_le_inv in L,Cl,T,E.
  repeat split;try apply Rabs_le;try split;
    erfcx_goal(normal_log_tail_first.l1 h ch l cl p t e).
Qed.

Lemma normal_log_first_add k a b : finite a -> finite b ->
  Rabs(B a+B b)<=bpow radix2 k -> (-1074<=k<=4)%Z ->
  finite(fadd a b) /\ B(fadd a b)=rn(B a+B b) /\ Rabs(B(fadd a b))<=bpow radix2 k.
Proof.
  intros Fa Fb Range K;destruct(fadd16 a b Fa Fb)as[F V].
  - apply Rle_trans with(bpow radix2 k);[exact Range|change 16 with(bpow radix2 4);apply bpow_le;lia].
  - split;[exact F|];split;[exact V|rewrite V;apply normal_center_round_bound;assumption||lia].
Qed.

Definition normal_log_first_correction64 h l p :=
  fadd(fadd h normal_ln_sqrt_2pi_hi)(fadd l(fadd normal_ln_sqrt_2pi_lo p)).

Lemma normal_log_first_constant_bounds :
  finite normal_ln_sqrt_2pi_hi /\ finite normal_ln_sqrt_2pi_lo /\
  0.9<=B normal_ln_sqrt_2pi_hi<=1 /\
  Rabs(B normal_ln_sqrt_2pi_lo)<=bpow radix2(-54) /\
  Rabs(B normal_ln_sqrt_2pi_hi+B normal_ln_sqrt_2pi_lo-ln(2*PI)/2)<=bpow radix2(-105).
Proof.
  destruct normal_ln_sqrt_2pi_hi_ok as[Fh H],normal_ln_sqrt_2pi_lo_ok as[Fl L].
  repeat split;try assumption;rewrite ?H,?L;interval with(i_prec 200).
Qed.

Lemma normal_log_first_correction_ieee h l p : finite h -> finite l -> finite p ->
  3<=B h<=5 -> Rabs(B l)<=bpow radix2(-12) -> 0<=B p<=0.001 ->
  finite(normal_log_first_correction64 h l p) /\
  B(normal_log_first_correction64 h l p)=normal_log_first_correction_r
    (B h)(B l)(B normal_ln_sqrt_2pi_hi)(B normal_ln_sqrt_2pi_lo)(B p) /\
  3<=B(normal_log_first_correction64 h l p)<=7.
Proof.
  intros Fh Fl Fp H L P;destruct normal_log_first_constant_bounds as[Fch [Fcl [Ch [Cl Constant]]]].
  destruct(normal_log_first_add 0 normal_ln_sqrt_2pi_lo p Fcl Fp
    ltac:(apply Rabs_le_inv in Cl;apply Rabs_le;bpow_num_all;lra)ltac:(lia))as[Fcp [Vcp CP]].
  destruct(normal_log_first_add 1 l (fadd normal_ln_sqrt_2pi_lo p) Fl Fcp
    ltac:(eapply Rle_trans;[apply Rabs_triang|];bpow_num_all;lra)ltac:(lia))as[Flc [Vlc LC]].
  destruct(normal_log_first_add 3 h normal_ln_sqrt_2pi_hi Fh Fch
    ltac:(apply Rabs_le;bpow_num_all;lra)ltac:(lia))as[Fhc [Vhc HC]].
  destruct(normal_log_first_add 4 (fadd h normal_ln_sqrt_2pi_hi)
    (fadd l(fadd normal_ln_sqrt_2pi_lo p))Fhc Flc
    ltac:(eapply Rle_trans;[apply Rabs_triang|];bpow_num_all;lra)ltac:(lia))as[Fc [Vc C]].
  unfold normal_log_first_correction64;split;[exact Fc|].
  assert(Value : B(fadd(fadd h normal_ln_sqrt_2pi_hi)(fadd l(fadd normal_ln_sqrt_2pi_lo p)))=
    normal_log_first_correction_r (B h)(B l)(B normal_ln_sqrt_2pi_hi)(B normal_ln_sqrt_2pi_lo)(B p)).
  { rewrite Vc,Vhc,Vlc,Vcp;reflexivity. }
  split;[exact Value|rewrite Value].
  exact(proj2(proj2(normal_log_first_model _ _ _ _ 0 0 _ H L Ch Cl
    ltac:(rewrite Rabs_R0;apply bpow_ge_0)ltac:(rewrite Rabs_R0;apply bpow_ge_0)P))).
Qed.

Lemma normal_log_first_square x : finite x -> 37<=B x<=64 ->
  let '(s,t):=normal_log_tail_square64 x in
  finite s /\ finite t /\ B s+B t= -B x*B x/2 /\
  -2049<=B s<= -684 /\ Rabs(B t)<=bpow radix2(-43).
Proof.
  intros F X;pose proof(normal_log_tail_square_exact x F
    ltac:(bpow_num_all;split;lra))as Square.
  destruct(normal_log_tail_square64 x)as[s t].
  destruct Square as[Fs [Ft [Norm [Value Magnitude]]]].
  assert(Range : Rabs(-B x*B x/2)<=bpow radix2 11).
  { apply Rabs_le;bpow_num_all;split;nra. }
  pose proof(rnd_err_below _ 11 ltac:(lia)Range)as Error.
  rewrite <-Value,<-Norm in Error.
  assert(T : Rabs(B t)<=bpow radix2(-43)).
  { replace(B t)with(- (B s-(B s+B t)))by ring;rewrite Rabs_Ropp;exact Error. }
  repeat split;try assumption;apply Rabs_le_inv in T;bpow_num_all;nra.
Qed.

Definition normal_log_first64 x :=
  let '(h,l,_):=normal_log_reciprocal_parts64 x in
  let p:=normal_log_tail_value64 x in
  let c:=normal_log_first_correction64 h l p in
  let '(s,t):=normal_log_tail_square64 x in
  let '(y,e):=fast_two_sum64 s (fneg c) in
  (y,fadd e t).

Theorem normal_log_first_words x : finite x -> 37<=B x<=64 ->
  let '(h,l):=normal_log_first64 x in
  finite h /\ finite l /\ Rabs(B h)<=4096 /\ Rabs(B l)<=bpow radix2(-39) /\
  Rabs(ln(normal_tail(B x))-(B h+B l))<=6*bpow radix2(-52).
Proof.
  intros F X;pose proof(normal_log_first_parts_range x F X)as Log.
  destruct(normal_log_tail_value_ieee x F ltac:(bpow_num_all;split;lra))as[Fp Perror].
  pose proof(normal_log_first_polynomial_range x F X)as P.
  pose proof(normal_log_first_square x F X)as Square.
  unfold normal_log_first64;destruct(normal_log_reciprocal_parts64 x)as[[h l]eps].
  destruct Log as[Fh [Fl [H [L LogError]]]].
  set(p:=normal_log_tail_value64 x)in *.
  destruct(normal_log_first_correction_ieee h l p Fh Fl Fp H L P)as[Fc [Cvalue C]].
  set(c:=normal_log_first_correction64 h l p)in *.
  destruct(normal_log_tail_square64 x)as[s t].
  destruct Square as[Fs [Ft [Square [S T]]]].
  assert(Fneg : finite(fneg c))by(unfold fneg,b64_opp;rewrite is_finite_Bopp;exact Fc).
  assert(Neg : B(fneg c)= -B c)by(apply B2R_Bopp).
  assert(AbsS : Rabs(B s)<=2049)by(apply Rabs_le;lra).
  assert(AbsC : Rabs(B(fneg c))<=7)by(rewrite Neg;apply Rabs_le;lra).
  pose proof(fast_two_sum_ieee s (fneg c)Fs Fneg
    ltac:(apply Rle_trans with 2049;[exact AbsS|interval with(i_prec 80)])
    ltac:(apply Rle_trans with 7;[exact AbsC|interval with(i_prec 80)])
    ltac:(right;left;rewrite Neg,Rabs_left,Rabs_left by lra;lra))as Sum.
  destruct(fast_two_sum64 s (fneg c))as[y e].
  destruct Sum as[Fy [Fe [High Total]]].
  assert(SumBound : Rabs(B s+B(fneg c))<=bpow radix2 12).
  { eapply Rle_trans;[apply Rabs_triang|];bpow_num_all;lra. }
  assert(Y : Rabs(B y)<=4096).
  { rewrite High;change 4096 with(bpow radix2 12);apply normal_center_round_bound;assumption||lia. }
  pose proof(rnd_err_below _ 12 ltac:(lia)SumBound)as RoundError.
  rewrite <-High in RoundError.
  assert(E : Rabs(B e)<=bpow radix2(-40)).
  { replace(B e)with((B s+B(fneg c))-B y)by lra;rewrite Rabs_minus_sym.
    eapply Rle_trans;[exact RoundError|apply bpow_le;lia]. }
  destruct(fadd16 e t Fe Ft
    ltac:(eapply Rle_trans;[apply Rabs_triang|];bpow_num_all;lra))as[Fz Zvalue].
  destruct normal_log_first_constant_bounds as[Fch [Fcl [Ch [Cl Constant]]]].
  pose proof(normal_log_first_model (B h)(B l)(B normal_ln_sqrt_2pi_hi)
    (B normal_ln_sqrt_2pi_lo)(B t)(B e)(B p)H L Ch Cl T E P)as Model.
  destruct Model as[Model [Z Cmodel]].
  assert(Evaluation : Rabs((B y+B(fadd e t))-((B s+B t)-
    (B h+B l+B normal_ln_sqrt_2pi_hi+B normal_ln_sqrt_2pi_lo+B p)))<=5*bpow radix2(-52)).
  { replace((B y+B(fadd e t))-((B s+B t)-
      (B h+B l+B normal_ln_sqrt_2pi_hi+B normal_ln_sqrt_2pi_lo+B p)))with
      (-(B c-(B h+B l+B normal_ln_sqrt_2pi_hi+B normal_ln_sqrt_2pi_lo+B p))+
       (B(fadd e t)-(B e+B t)))by(rewrite Neg in Total;lra).
    rewrite Cvalue,Zvalue;exact Model. }
  repeat split;try assumption.
  - rewrite Zvalue;exact Z.
  - rewrite normal_log_mills_identity by lra.
    rewrite Square in Evaluation;apply Rabs_le_inv in Evaluation,LogError,Constant,Perror.
    apply Rabs_le;bpow_num_all;split;lra.
Qed.

Definition normal_log_first_decide64 x :=
  let '(h,l):=normal_log_first64 x in Ln1pTest.decide h l (erfcx_pow2(-49)).

Theorem normal_log_first_decided x v : finite x -> 37<=B x<=64 ->
  normal_log_first_decide64 x=Some v -> finite v /\ B v=rndF(ln(normal_tail(B x))).
Proof.
  intros F X;pose proof(normal_log_first_words x F X)as Words.
  unfold normal_log_first_decide64;destruct(normal_log_first64 x)as[h l].
  destruct Words as[Fh [Fl [H [L Error]]]].
  destruct(erfcx_pow2_ok(-49)ltac:(lia))as[Fe E].
  intros Decision;destruct(Ln1pTest.decide_ok h l (erfcx_pow2(-49)) v Fh Fl Fe
    ltac:(rewrite E;apply bpow_ge_0)
    ltac:(apply Rle_trans with 4096;[exact H|interval with(i_prec 80)])
    ltac:(rewrite E;bpow_num_all;lra)Decision)as[Fv Round].
  split;[exact Fv|symmetry;apply Round;rewrite E;bpow_num_all;nra].
Qed.
