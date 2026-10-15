(** Double-word reconstruction of the moderate far log-CDF tail. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Eft RoundingConstant.
Require Import StageGappa LnFastCompose LnFastValue NormalConstants
  NormalLogTailPolynomial NormalLogTailApprox NormalLogMillsIdentity NormalLogTailSquare
  NormalCenterFastTail ErfcxTailIntegral NormalTailAnalytic ErfcxDecision.
Open Scope R_scope.

Definition normal_log_tail_constant64 := two_sum64 normal_ln_sqrt_2pi_hi normal_ln_sqrt_2pi_lo.

Lemma normal_log_tail_constant_words :
  let '(h,l):=normal_log_tail_constant64 in
  finite h /\ finite l /\ B h=rndF(B h+B l) /\
  Rabs(B h)<=1 /\ Rabs(B l)<=2 /\ /2<=B h+B l<=1 /\
  Rabs(B h+B l-ln(2*PI)/2)<=bpow radix2 (-105).
Proof.
  destruct normal_ln_sqrt_2pi_hi_ok as[Fh H],normal_ln_sqrt_2pi_lo_ok as[Fl L].
  assert(A : Rabs(B normal_ln_sqrt_2pi_hi)<=1)by(rewrite H;interval with(i_prec 100)).
  assert(Bd : Rabs(B normal_ln_sqrt_2pi_lo)<=1)by(rewrite L;interval with(i_prec 120)).
  pose proof(two_sum_ieee _ _ Fh Fl
    ltac:(eapply Rle_trans;[exact A|interval with(i_prec 80)])
    ltac:(eapply Rle_trans;[exact Bd|interval with(i_prec 80)]))as Sum.
  unfold normal_log_tail_constant64;destruct(two_sum64 normal_ln_sqrt_2pi_hi normal_ln_sqrt_2pi_lo)as[h l].
  destruct Sum as[Fh' [Fl' [High Total]]].
  assert(Range : /2<=B h+B l<=1)by(rewrite Total,H,L;split;interval with(i_prec 120)).
  assert(Norm : B h=rndF(B h+B l))by(rewrite Total;exact High).
  assert(Hi : Rabs(B h)<=1).
  { rewrite Norm;change 1 with(bpow radix2 0);apply normal_center_round_bound;
      [change(bpow radix2 0)with 1;apply Rabs_le;lra|lia]. }
  assert(Lo : Rabs(B l)<=2).
  { pose proof(Rabs_le_inv _ _ Hi);apply Rabs_le;lra. }
  repeat split;try assumption;try tauto.
  rewrite Total,H,L;apply Rabs_le;split;interval with(i_prec 200).
Qed.

Definition normal_log_tail_base64 x :=
  let '(a,b):=lf_ln_fast_value x in
  let '(c,d):=normal_log_tail_constant64 in add64 a b c d.

Theorem normal_log_tail_base_words x : finite x -> 37<=B x<=bpow radix2 45 ->
  let '(h,l):=normal_log_tail_base64 x in
  finite h /\ finite l /\ B h=rndF(B h+B l) /\
  Rabs(B h)<=64 /\ Rabs(B l)<=128 /\ 3<=B h+B l<=34 /\
  Rabs(B h+B l-(ln(B x)+ln(2*PI)/2))<=bpow radix2 (-59)+bpow radix2 (-96).
Proof.
  intros Fx X;pose proof(lf_ln_fast_value_ok x Fx ltac:(lra))as Log.
  pose proof normal_log_tail_constant_words as Constant.
  unfold normal_log_tail_base64;destruct(lf_ln_fast_value x)as[a b].
  destruct(normal_log_tail_constant64)as[c d].
  destruct Log as[Fa [Fb [NormAB [A [Bv LogError]]]]].
  destruct Constant as[Fc [Fd [NormCD [C [D [RangeC ErrorC]]]]]].
  assert(LogRange : 3<=ln(B x)<=32)by(split;interval with(i_prec 100)).
  assert(RangeAB : 2<=B a+B b<=33).
  { apply Rabs_le_inv in LogError;rewrite(Rabs_pos_eq(ln(B x)))in LogError by lra;bpow_num_all;lra. }
  assert(Cancel : Rabs(B a+B b)+Rabs(B c+B d)<=4*Rabs(B a+B b+(B c+B d))).
  { rewrite !Rabs_pos_eq by lra;lra. }
  pose proof(lf_add_pair a b c d Fa Fb Fc Fd NormAB NormCD
    ltac:(eapply Rle_trans;[exact A|interval with(i_prec 120)])
    ltac:(eapply Rle_trans;[exact Bv|interval with(i_prec 120)])
    ltac:(eapply Rle_trans;[exact C|interval with(i_prec 120)])
    ltac:(eapply Rle_trans;[exact D|interval with(i_prec 120)])Cancel)as Sum.
  destruct(add64 a b c d)as[h l];destruct Sum as[Fh [Fl [Norm [e [E Value]]]]].
  assert(Evaluation : Rabs(B h+B l-(B a+B b+(B c+B d)))<=bpow radix2 (-98)).
  { rewrite Value;replace((B a+B b+(B c+B d))*(1+e)-(B a+B b+(B c+B d)))with
      ((B a+B b+(B c+B d))*e)by ring.
    rewrite Rabs_mult,Rabs_pos_eq by lra;pose proof(Rabs_pos e);bpow_num_all;nra. }
  assert(Error : Rabs(B h+B l-(ln(B x)+ln(2*PI)/2))<=bpow radix2 (-59)+bpow radix2 (-96)).
  { replace(B h+B l-(ln(B x)+ln(2*PI)/2))with
      ((B h+B l-(B a+B b+(B c+B d)))+((B a+B b-ln(B x))+(B c+B d-ln(2*PI)/2)))by ring.
    eapply Rle_trans;[apply Rabs_triang|].
    eapply Rle_trans;[apply Rplus_le_compat_l,Rabs_triang|].
    rewrite(Rabs_pos_eq(ln(B x)))in LogError by lra;bpow_num_all;nra. }
  assert(Range : 3<=B h+B l<=34).
  { assert(C0 : /2<=ln(2*PI)/2<=1)by(split;interval with(i_prec 100)).
    apply Rabs_le_inv in Error;bpow_num_all;lra. }
  assert(Hi : Rabs(B h)<=64).
  { rewrite Norm;change 64 with(bpow radix2 6);apply normal_center_round_bound;
      [change(bpow radix2 6)with 64;apply Rabs_le;lra|lia]. }
  assert(Lo : Rabs(B l)<=128).
  { pose proof(Rabs_le_inv _ _ Hi);apply Rabs_le;lra. }
  repeat split;tauto.
Qed.

Definition normal_log_tail_correction64 x :=
  let '(h,l):=normal_log_tail_base64 x in add_f64_64 h l (normal_log_tail_value64 x).

Theorem normal_log_tail_correction_words x : finite x -> 37<=B x<=bpow radix2 45 ->
  let '(h,l):=normal_log_tail_correction64 x in
  finite h /\ finite l /\ B h=rndF(B h+B l) /\
  Rabs(B h)<=64 /\ Rabs(B l)<=128 /\ 2<=B h+B l<=36 /\
  Rabs(B h+B l-(ln(B x)+ln(2*PI)/2-ln(tail_integral(2*((1/B x)*(1/B x))))))<=
    3*bpow radix2 (-60)+bpow radix2 (-95).
Proof.
  intros Fx X;pose proof(normal_log_tail_base_words x Fx X)as Base.
  destruct(normal_log_tail_value_ieee x Fx X)as[Fp ErrorP].
  assert(R : 0<=1/B x<=1/37).
  { split;[left;apply Rdiv_lt_0_compat;lra|unfold Rdiv;rewrite !Rmult_1_l;apply Rinv_le_contravar;lra]. }
  pose proof(tail_integral_correction (2*((1/B x)*(1/B x)))ltac:(nra))as Mills.
  assert(J : 99/100<=tail_integral(2*((1/B x)*(1/B x)))<=1)by nra.
  assert(LogJ : -1<=ln(tail_integral(2*((1/B x)*(1/B x))))<=0)by(split;interval with(i_prec 80)).
  set(p:=normal_log_tail_value64 x)in *.
  assert(P : Rabs(B p)<=2).
  { apply Rabs_le_inv in ErrorP;apply Rabs_le;bpow_num_all;lra. }
  unfold normal_log_tail_correction64;fold p;destruct(normal_log_tail_base64 x)as[a b].
  destruct Base as[Fa [Fb [Norm [A [Bv [Range BaseError]]]]]].
  assert(SumRange : 1<=B a+B b+B p<=36).
  { apply Rabs_le_inv in P;lra. }
  assert(Bound : forall w,Rabs(B w)<=128 -> bnd 1 7 (B w)).
  { intros w W;unfold bnd;rewrite Rmult_1_l;change(bpow radix2 7)with 128;exact W. }
  destruct(add_f64_64_ok 1 7 a b p Fa Fb Fp (Bound a ltac:(lra))(Bound b Bv)(Bound p ltac:(lra))
    ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia))as[Fh [Fl Value]].
  pose proof(add_f64_dw(B a)(B b)(B p)(B_fmt a)(B_fmt b)(B_fmt p)Norm)as Normalized.
  pose proof(add_f64_ieee a b p Fa Fb Fp Norm
    ltac:(eapply Rle_trans;[exact A|interval with(i_prec 80)])
    ltac:(eapply Rle_trans;[exact Bv|interval with(i_prec 80)])
    ltac:(eapply Rle_trans;[exact P|interval with(i_prec 80)]))as Relative.
  rewrite <-Value in Normalized;destruct(add_f64_64 a b p)as[h l];cbn[fst snd]in *.
  destruct Relative as[_ [_ Relative]].
  assert(Evaluation : Rabs(B h+B l-(B a+B b+B p))<=bpow radix2 (-99)).
  { replace(B h+B l-(B a+B b+B p))with
      (((B h+B l-(B a+B b+B p))/(B a+B b+B p))*(B a+B b+B p))by(field;lra).
    rewrite Rabs_mult,(Rabs_pos_eq(B a+B b+B p))by lra.
    pose proof(Rabs_pos((B h+B l-(B a+B b+B p))/(B a+B b+B p))).
    unfold prec in Relative;change(- (53))%Z with(-53)%Z in Relative;bpow_num_all;nra. }
  assert(Error : Rabs(B h+B l-(ln(B x)+ln(2*PI)/2-ln(tail_integral(2*((1/B x)*(1/B x))))))<=
    3*bpow radix2 (-60)+bpow radix2 (-95)).
  { replace(B h+B l-(ln(B x)+ln(2*PI)/2-ln(tail_integral(2*((1/B x)*(1/B x))))))with
      ((B h+B l-(B a+B b+B p))+((B a+B b-(ln(B x)+ln(2*PI)/2))+
       (B p+ln(tail_integral(2*((1/B x)*(1/B x)))))))by ring.
    eapply Rle_trans;[apply Rabs_triang|].
    eapply Rle_trans;[apply Rplus_le_compat_l,Rabs_triang|].
    bpow_num_all;lra. }
  assert(LogRange : 3<=ln(B x)<=32)by(split;interval with(i_prec 100)).
  assert(C : /2<=ln(2*PI)/2<=1)by(split;interval with(i_prec 100)).
  assert(RangeHL : 2<=B h+B l<=36).
  { apply Rabs_le_inv in Error;bpow_num_all;lra. }
  assert(Hi : Rabs(B h)<=64).
  { rewrite Normalized;change 64 with(bpow radix2 6);apply normal_center_round_bound;
      [change(bpow radix2 6)with 64;apply Rabs_le;lra|lia]. }
  assert(Lo : Rabs(B l)<=128).
  { pose proof(Rabs_le_inv _ _ Hi);apply Rabs_le;lra. }
  repeat split;tauto.
Qed.

Definition normal_log_tail_moderate64 x :=
  let '(a,b):=normal_log_tail_square64 x in
  let '(c,d):=normal_log_tail_correction64 x in sub64 a b c d.

Theorem normal_log_tail_moderate_words x : finite x -> 37<=B x<=bpow radix2 45 ->
  let '(h,l):=normal_log_tail_moderate64 x in
  finite h /\ finite l /\ B h=rndF(B h+B l) /\
  512<=Rabs(B h)<=bpow radix2 90 /\
  Rabs(ln(normal_tail(B x))-(B h+B l))<=bpow radix2 (-67)*Rabs(ln(normal_tail(B x))).
Proof.
  intros Fx X.
  pose proof(normal_log_tail_square_exact x Fx ltac:(split;[eapply Rle_trans;[|exact(proj1 X)];interval with(i_prec 100)|exact(proj2 X)]))as Square.
  pose proof(normal_log_tail_correction_words x Fx X)as Correction.
  unfold normal_log_tail_moderate64;destruct(normal_log_tail_square64 x)as[a b].
  destruct(normal_log_tail_correction64 x)as[c d].
  destruct Square as[Fa [Fb [NormAB [ValueAB A]]]].
  destruct Correction as[Fc [Fd [NormCD [C [D [RangeCD ErrorCD]]]]]].
  assert(SquareRange : -bpow radix2 89<=B a+B b<= -1369/2).
  { rewrite ValueAB;assert(P : 0<bpow radix2 45)by apply bpow_gt_0.
    replace(bpow radix2 89)with(bpow radix2 45*bpow radix2 45/2)by(bpow_num;field);split;nra. }
  assert(Bv : Rabs(B b)<=bpow radix2 90).
  { replace(B b)with((B a+B b)-B a)by ring.
    eapply Rle_trans;[apply Rabs_triang|];rewrite Rabs_Ropp,(Rabs_left1(B a+B b))by lra.
    bpow_num_all;lra. }
  assert(Nb : forall w,B(fneg w)= -B w)by(intros;apply B2R_Bopp).
  assert(Nf : forall w,finite w -> finite(fneg w))by(intros w Fw;unfold fneg,b64_opp;rewrite is_finite_Bopp;exact Fw).
  assert(NormNeg : B(fneg c)=rndF(B(fneg c)+B(fneg d))).
  { rewrite !Nb;apply dw_opp;exact NormCD. }
  assert(Cancel : Rabs(B a+B b)+Rabs(B(fneg c)+B(fneg d))<=4*Rabs(B a+B b+(B(fneg c)+B(fneg d)))).
  { rewrite !Nb,!Rabs_left1 by lra;lra. }
  pose proof(lf_add_pair a b (fneg c)(fneg d) Fa Fb (Nf c Fc)(Nf d Fd) NormAB NormNeg
    ltac:(eapply Rle_trans;[exact(proj2 A)|apply bpow_le;lia])
    ltac:(eapply Rle_trans;[exact Bv|apply bpow_le;lia])
    ltac:(rewrite Nb,Rabs_Ropp;eapply Rle_trans;[exact C|interval with(i_prec 120)])
    ltac:(rewrite Nb,Rabs_Ropp;eapply Rle_trans;[exact D|interval with(i_prec 120)])Cancel)as Sum.
  unfold sub64;destruct(add64 a b (fneg c)(fneg d))as[h l].
  destruct Sum as[Fh [Fl [Norm [e [E Value]]]]];rewrite !Nb in Value.
  assert(LogRange : 3<=ln(B x)<=32)by(split;interval with(i_prec 100)).
  assert(C0 : /2<=ln(2*PI)/2<=1)by(split;interval with(i_prec 100)).
  assert(R : 0<=1/B x<=1/37).
  { split;[left;apply Rdiv_lt_0_compat;lra|unfold Rdiv;rewrite !Rmult_1_l;apply Rinv_le_contravar;lra]. }
  pose proof(tail_integral_correction (2*((1/B x)*(1/B x)))ltac:(nra))as Mills.
  assert(J : 99/100<=tail_integral(2*((1/B x)*(1/B x)))<=1)by nra.
  assert(LogJ : -1<=ln(tail_integral(2*((1/B x)*(1/B x))))<=0)by(split;interval with(i_prec 80)).
  pose proof(normal_log_mills_identity (B x)(proj1 X))as Identity.
  assert(Target : 684<=Rabs(ln(normal_tail(B x)))<=bpow radix2 89+34).
  { rewrite Identity;rewrite Rabs_left1 by(rewrite ValueAB in SquareRange;nra).
    rewrite ValueAB in SquareRange;split;nra. }
  assert(PreError : Rabs((B a+B b+(-B c+-B d))-ln(normal_tail(B x)))<=
    (3/2^69)*Rabs(ln(normal_tail(B x)))).
  { replace((B a+B b+(-B c+-B d))-ln(normal_tail(B x)))with
      (-(B c+B d-(ln(B x)+ln(2*PI)/2-ln(tail_integral(2*((1/B x)*(1/B x)))))))
      by(rewrite ValueAB,Identity;ring).
    rewrite Rabs_Ropp;eapply Rle_trans;[exact ErrorCD|];bpow_num_all;lra. }
  pose proof(lf_rounded_sum _ _ _ (3/2^69) e ltac:(interval with(i_prec 100)) PreError E Value)as Error.
  assert(FinalError : Rabs(ln(normal_tail(B x))-(B h+B l))<=bpow radix2 (-67)*Rabs(ln(normal_tail(B x)))).
  { rewrite Rabs_minus_sym;eapply Rle_trans;[exact Error|].
    apply Rmult_le_compat_r;[apply Rabs_pos|interval with(i_prec 150)]. }
  assert(TotalRange : 512<=Rabs(B h+B l)<=bpow radix2 90).
  { pose proof(Rabs_triang_inv (ln(normal_tail(B x)))(B h+B l)).
    pose proof(Rabs_triang_inv (B h+B l)(ln(normal_tail(B x)))).
    rewrite Rabs_minus_sym in H0;bpow_num_all;split;nra. }
  assert(Abs : Rabs(B h)=rndF(Rabs(B h+B l)))by(rewrite Norm at 1;rewrite <-round_NE_abs by exact _;reflexivity).
  repeat split;try assumption.
  - rewrite Abs;change 512 with(bpow radix2 9);apply round_ge_generic;
      [exact _|exact _|apply generic_format_bpow;unfold FLT_exp,emin,prec;lia|exact(proj1 TotalRange)].
  - rewrite Abs;apply round_le_generic;
      [exact _|exact _|apply generic_format_bpow;unfold FLT_exp,emin,prec;lia|exact(proj2 TotalRange)].
Qed.

Definition normal_log_tail_moderate_decide64 x :=
  let '(h,l):=normal_log_tail_moderate64 x in erfcx_decide64 h l.

Theorem normal_log_tail_moderate_decided x v : finite x -> 37<=B x<=bpow radix2 45 ->
  normal_log_tail_moderate_decide64 x=Some v ->
  finite v /\ B v=rndF(ln(normal_tail(B x))).
Proof.
  intros Fx X;pose proof(normal_log_tail_moderate_words x Fx X)as Words.
  unfold normal_log_tail_moderate_decide64;destruct(normal_log_tail_moderate64 x)as[h l].
  destruct Words as[Fh [Fl [Norm [H Error]]]];intros Decision.
  destruct(erfcx_decide_ieee h l (ln(normal_tail(B x))) v Fh Fl
    ltac:(split;[eapply Rle_trans;[|exact(proj1 H)];interval with(i_prec 80)|
      eapply Rle_trans;[exact(proj2 H)|apply bpow_le;lia]])Norm Error Decision)as[Eq Value].
  subst v;split;assumption.
Qed.
