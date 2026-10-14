(** Relative low-word and absolute high-word bounds for the fast tail,
    used by both branches of the log-complement composition. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Binary64 Require Import Binary64Add IEEE64 RoundingCore.
Require Import StageGappa Ln1pStageB NormalTailAnalytic NormalTailFast NormalOuterFastRange.
Open Scope R_scope.

Theorem normal_log_tail_words x : finite x -> /2<=B x<=37 ->
  let '(h,l,k):=normal_tail_fast64 x in
  bpow radix2 (-1004)<=B h<=/3 /\
  Rabs(B l)<=B h*bpow radix2 (-51) /\
  B h<=2*normal_tail(B x).
Proof.
  intros Fx X;pose proof(normal_tail_fast_ieee x Fx X)as Tail.
  pose proof(normal_outer_tail_tight(B x)ltac:(lra))as Tight.
  destruct(normal_tail_fast64 x)as[[h l]k].
  destruct Tail as[Fh [Fl [K [Norm [H [L [Target Error]]]]]]].
  set(s:=bpow radix2 k)in *;assert(S : 0<s)by apply bpow_gt_0.
  assert(Sum : s/8192<=B h+B l<=21/64).
  { apply Rabs_le_inv in Error;bpow_num_all;split;nra. }
  assert(Lower : bpow radix2 (k-13)<=B h).
  { rewrite Norm;apply round_ge_generic;try exact _.
    - apply generic_format_bpow;unfold FLT_exp,emin,prec;lia.
    - replace(k-13)%Z with(k+ -13)%Z by ring;rewrite bpow_plus;fold s;change(bpow radix2(-13))with(/8192);lra. }
  assert(Upper : B h<=21/64).
  { rewrite Norm;apply round_le_generic;try exact _;[|exact(proj2 Sum)].
    replace(21/64)with(IZR 21*bpow radix2(-6))by(bpow_num;field).
    apply fmt_int;lia. }
  assert(High : bpow radix2(-1004)<=B h<=/3).
  { split;[eapply Rle_trans;[|exact Lower];apply bpow_le;lia|lra]. }
  assert(SumNormal : bpow radix2(-1022)<=Rabs(B h+B l)).
  { rewrite Rabs_pos_eq by lra.
    eapply Rle_trans with(bpow radix2(k-13)).
    - apply bpow_le;lia.
    - replace(k-13)%Z with(k+ -13)%Z by ring;rewrite bpow_plus;fold s;change(bpow radix2(-13))with(/8192);lra. }
  pose proof(rnd_rel(B h+B l)SumNormal)as Rounded.
  change(Rabs(rndF(B h+B l)-(B h+B l))<=bpow radix2(-53)*Rabs(B h+B l))in Rounded.
  rewrite <-Norm in Rounded;replace(B h-(B h+B l))with(-B l)in Rounded by ring.
  rewrite Rabs_Ropp,(Rabs_pos_eq(B h+B l))in Rounded by lra.
  assert(Low : Rabs(B l)<=B h*bpow radix2(-51)).
  { pose proof(Rle_abs(B l));bpow_num_all;nra. }
  repeat split;try tauto.
  apply Rabs_le_inv in Low,Error;bpow_num_all;nra.
Qed.
