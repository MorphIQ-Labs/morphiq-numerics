(** The log-CDF guard is four times the ordinary normal-family guard.
    Its proof includes rounding the guard and both endpoint low words. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64 RoundingConstant RoundingTest.
Require Import StageGappa ErfcxDecision NormalFastDecision NormalLogCentralFast
  NormalCentered NormalAccurateCentralCdf.
Open Scope R_scope.

Definition normal_log_guard64 h := fmul (b64_abs h)(erfcx_pow2 (-62)).
Definition normal_log_decide64 h l := normal_interval_decide64 h l (normal_log_guard64 h).

Theorem normal_log_decide_ok h l target v : finite h -> finite l ->
  Rabs(B h)<=4 -> Rabs(B l)<=bpow radix2 (-52) -> /4<=Rabs target<=2 ->
  Rabs((B h+B l)-target)<=7*bpow radix2 (-65)*Rabs target ->
  normal_log_decide64 h l=Some v -> finite v /\ B v=rndF target.
Proof.
  intros Fh Fl H L Target Error Decision.
  assert(Fabs : finite(b64_abs h))by(unfold b64_abs;destruct h;simpl in *;congruence).
  destruct(erfcx_pow2_ok (-62)ltac:(lia))as[Fc C].
  assert(Product : Rabs(B(b64_abs h)*B(erfcx_pow2(-62)))<=bpow radix2 (-20)).
  { rewrite B_abs,C,Rabs_mult,Rabs_Rabsolu,(Rabs_pos_eq(bpow radix2 (-62)))by apply bpow_ge_0.
    pose proof(Rabs_pos(B h));bpow_num_all;nra. }
  destruct(fmul16 (b64_abs h)(erfcx_pow2(-62))Fabs Fc
    ltac:(eapply Rle_trans;[exact Product|interval with(i_prec 80)]))as[Fe Value].
  fold(normal_log_guard64 h)in Fe,Value.
  pose proof(rnd_err_below _ (-20)ltac:(lia)Product)as Rounded.
  rewrite <-Value,B_abs,C in Rounded;change(-20-54)%Z with(-74)%Z in Rounded.
  apply Rabs_le_inv in Rounded.
  assert(HighTarget : Rabs target<=Rabs(B h)+7*bpow radix2 (-65)*Rabs target+bpow radix2 (-52)).
  { pose proof(Rabs_triang_inv target (B h+B l))as Difference.
    rewrite Rabs_minus_sym in Difference.
    pose proof(Rabs_triang(B h)(B l));lra. }
  assert(Guard : 0<=B(normal_log_guard64 h) /\
    7*bpow radix2 (-65)*Rabs target+bpow radix2 (-74)<=B(normal_log_guard64 h) /\
    B(normal_log_guard64 h)<=bpow radix2 (-59)).
  { pose proof(Rabs_pos(B h));bpow_num_all;repeat split;nra. }
  destruct Guard as[E [Budget Upper]].
  unfold normal_log_decide64 in Decision.
  apply(normal_interval_decide_ok h l (normal_log_guard64 h)target
    (7*bpow radix2 (-65)*Rabs target)(-20)v);try assumption.
  - lra.
  - lia.
  - bpow_num_all;lra.
  - rewrite Rabs_minus_sym;exact Error.
Qed.

Definition normal_log_central_decide64 x :=
  let '(h,l):=normal_log_central_fast64 x in normal_log_decide64 h l.

Local Opaque normal_log_central_fast64 normal_log_decide64.

Theorem normal_log_central_decided x v : finite x -> bpow radix2 (-450)<=Rabs(B x)<=/2 ->
  normal_log_central_decide64 x=Some v -> finite v /\ B v=rndF(ln(normal_cdf(B x))).
Proof.
  intros Fx X Decision;pose proof(normal_log_central_fast_ieee x Fx X)as Log.
  unfold normal_log_central_decide64 in Decision;destruct(normal_log_central_fast64 x)as[h l].
  destruct Log as[Fh [Fl [_ [H [L Error]]]]].
  apply(normal_log_decide_ok h l (ln(normal_cdf(B x)))v);try assumption.
  pose proof(normal_central_cdf_range(B x)(proj2 X))as Cdf.
  assert(-2<=ln(normal_cdf(B x))<= -/4)by(split;interval with(i_prec 80)).
  rewrite Rabs_left1 by lra;split;lra.
Qed.
