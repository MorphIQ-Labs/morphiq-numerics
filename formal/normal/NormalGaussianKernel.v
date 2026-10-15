(** Normal density's exact negative half-square and shared double-word
    exponential. This component retains the original binary64 argument. *)
From Coq Require Import Reals ZArith Lia Lra Psatz Classical.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add Binary64Mul IEEE64 IEEE64Add IEEE64Mul IEEE64Eft Grid RoundingConstant RoundingTest.
From Interval Require Import Tactic.
From Gappa Require Import Gappa_library.
Require Import StageGappa Ln1pLemmas ExpReduction ErfcxEntryTables ErfcxReflectionExp.
Open Scope R_scope.

Definition normal_half_square64 x := two_prod64 x (fmul neg_half x).

Lemma normal_negative_half x : finite x -> bpow radix2 (-400)<=B x<=39 ->
  finite(fmul neg_half x) /\ B(fmul neg_half x)= - B x/2.
Proof.
  intros F X.
  destruct neg_half_ok as [Fc [Value Range]].
  assert (C : B neg_half= -/2).
  { rewrite Value;change(-1*/2= -/2);ring. }
  assert (Grid : on_grid (-452) (B x)).
  { change (-452)%Z with (-400-52)%Z.
    apply (grid_fmt_bound (FLT_exp emin prec) (-400));[unfold FLT_exp,prec;lia|apply B_fmt|].
    right;rewrite Rabs_pos_eq;[exact(proj1 X)|pose proof(bpow_gt_0 radix2 (-400));lra]. }
  destruct(fmul_exact neg_half x Fc F) as [Product Exact].
  - rewrite C. replace (-/2*B x) with (-(B x*bpow radix2 (-1)))
      by (change(bpow radix2 (-1))with(/2);ring).
    apply generic_format_opp. apply(scaled_fmt_grid _ (-452));[apply B_fmt|exact Grid|lia].
  - rewrite C. assert (A : Rabs(-/2*B x)<=20).
    { pose proof(bpow_gt_0 radix2 (-400));rewrite Rabs_left;[nra|nra]. }
    apply Rle_lt_trans with 20;[exact A|interval with(i_prec 64)].
  - split;[exact Product|rewrite Exact,C;field].
Qed.

Theorem normal_half_square_exact x : finite x -> bpow radix2 (-400)<=B x<=39 ->
  let '(h,l):=normal_half_square64 x in
  finite h /\ finite l /\ B h+B l= - B x*B x/2 /\
  Rabs(B h)<=761 /\ Rabs(B l)<=bpow radix2 (-44).
Proof.
  intros F X.
  destruct(normal_negative_half x F X) as [Fhalf Half].
  assert (Xp : 0<B x) by (pose proof(bpow_gt_0 radix2 (-400));lra).
  assert (Domain : in_two_prod_domain (B x) (B(fmul neg_half x))).
  { right;rewrite Half,Rabs_mult,(Rabs_pos_eq(B x)) by lra.
    rewrite Rabs_left by lra.
    apply Rle_trans with (bpow radix2 (-801)).
    - apply bpow_le;lia.
    - replace (bpow radix2 (-801)) with (bpow radix2 (-400)*bpow radix2 (-400)/2).
      + pose proof(bpow_gt_0 radix2 (-400));nra.
      + unfold Rdiv;change(/2)with(bpow radix2 (-1));rewrite <- !bpow_plus;reflexivity. }
  pose proof(two_prod_ieee 6 5 x (fmul neg_half x) F Fhalf
    ltac:(change(bpow radix2 6)with 64;rewrite Rabs_pos_eq;lra)
    ltac:(rewrite Half;change(bpow radix2 5)with 32;rewrite Rabs_left;lra)
    ltac:(lia) ltac:(lia) ltac:(lia) Domain) as Product.
  unfold normal_half_square64;destruct(two_prod64 x (fmul neg_half x)) as [h l].
  destruct Product as [Fh [Fl [High Exact]]]. rewrite Half in High,Exact.
  assert (Magnitude : Rabs(B x*(- B x/2))<1024).
  { rewrite Rabs_left;[nra|nra]. }
  assert (H : Rabs(B h)<=761).
  { rewrite High. apply rnd_bound.
    - replace 761 with (IZR 761*bpow radix2 0) by (change(bpow radix2 0)with 1;change(IZR 761)with 761;ring).
      apply ExpReduction.fmt_int;lia.
    - rewrite Rabs_left;[nra|nra]. }
  pose proof(rnd_err_below (B x*(- B x/2)) 10 ltac:(lia)
    ltac:(change(bpow radix2 10)with 1024;lra)) as Error.
  rewrite <- High in Error.
  assert (L : Rabs(B l)<=bpow radix2 (-44)).
  { replace (B l) with (-(B h-B x*(- B x/2))) by lra.
    rewrite Rabs_Ropp;exact Error. }
  repeat split;try assumption. nra.
Qed.

Definition normal_gaussian64 x :=
  let '(h,l):=normal_half_square64 x in
  let '(yh,yl,k):=reflection_exp64 h l in
  let '(a,b):=two_sum64 yh yl in (a,b,k).

Theorem normal_gaussian_regular_ieee x : finite x -> bpow radix2 (-33)<=B x<=37 ->
  let '(yh,yl,k):=normal_gaussian64 x in
  finite yh /\ finite yl /\ (-1025<=k<=1025)%Z /\
  B yh=rndF(B yh+B yl) /\
  Rabs(exp(- B x*B x/2)/bpow radix2 k-(B yh+B yl))<=209*bpow radix2 (-78).
Proof.
  intros F X. assert (Domain : bpow radix2 (-400)<=B x<=39).
  { split;[apply Rle_trans with(bpow radix2 (-33));[apply bpow_le;lia|lra]|lra]. }
  pose proof(normal_half_square_exact x F Domain) as Square.
  unfold normal_gaussian64;destruct(normal_half_square64 x) as [h l].
  destruct Square as [Fh [Fl [Exact [H L]]]].
  assert (Small : Rabs(B h)<710).
  { assert (Low : Rabs(B l)<=/2).
    { apply Rle_trans with(bpow radix2 (-44));[exact L|change(/2)with(bpow radix2 (-1));apply bpow_le;lia]. }
    apply Rabs_le_inv in Low. pose proof(bpow_gt_0 radix2 (-33)).
    apply Rabs_lt;split;nra. }
  pose proof(reflection_exp_ieee h l Fh Small Fl L) as Exp.
  destruct(reflection_exp64 h l) as [[yh yl]k].
  destruct Exp as [Fyh [Fyl [K [Yh [Yl [Norm Error]]]]]].
  rewrite Exact in Error.
  pose proof(two_sum_ieee yh yl Fyh Fyl
    ltac:(apply Rle_trans with 3;[rewrite Rabs_pos_eq;lra|interval with(i_prec 64)])
    ltac:(apply Rle_trans with(bpow radix2 (-52));[exact Yl|apply bpow_le;lia])) as Sum.
  destruct(two_sum64 yh yl) as [a b]. destruct Sum as [Fa [Fb [Value Total]]].
  split;[exact Fa|]. split;[exact Fb|]. split;[exact K|].
  split;rewrite Total;assumption.
Qed.

Theorem normal_gaussian_extended_ieee x : finite x -> bpow radix2 (-33)<=B x<=39 ->
  let '(yh,yl,k):=normal_gaussian64 x in
  finite yh /\ finite yl /\ (-1100<=k<=1100)%Z /\
  B yh=rndF(B yh+B yl) /\
  Rabs(exp(- B x*B x/2)/bpow radix2 k-(B yh+B yl))<=209*bpow radix2 (-78).
Proof.
  intros F X. assert (Domain : bpow radix2 (-400)<=B x<=39).
  { split;[apply Rle_trans with(bpow radix2 (-33));[apply bpow_le;lia|lra]|lra]. }
  pose proof(normal_half_square_exact x F Domain) as Square.
  unfold normal_gaussian64;destruct(normal_half_square64 x) as [h l].
  destruct Square as [Fh [Fl [Exact [H L]]]].
  assert (Small : Rabs(B h)<762).
  { assert (Low : Rabs(B l)<=/2).
    { apply Rle_trans with(bpow radix2 (-44));[exact L|change(/2)with(bpow radix2 (-1));apply bpow_le;lia]. }
    apply Rabs_le_inv in Low. pose proof(bpow_gt_0 radix2 (-33)).
    apply Rabs_lt;split;nra. }
  pose proof(reflection_exp_wide_ieee h l Fh Small Fl L) as Exp.
  destruct(reflection_exp64 h l) as [[yh yl]k].
  destruct Exp as [Fyh [Fyl [K [Yh [Yl [Norm Error]]]]]].
  rewrite Exact in Error.
  pose proof(two_sum_ieee yh yl Fyh Fyl
    ltac:(apply Rle_trans with 3;[rewrite Rabs_pos_eq;lra|interval with(i_prec 64)])
    ltac:(apply Rle_trans with(bpow radix2 (-52));[exact Yl|apply bpow_le;lia])) as Sum.
  destruct(two_sum64 yh yl) as [a b]. destruct Sum as [Fa [Fb [Value Total]]].
  split;[exact Fa|]. split;[exact Fb|]. split;[exact K|].
  split;rewrite Total;assumption.
Qed.

Theorem normal_gaussian_small_error x : Rabs x<=bpow radix2 (-33) ->
  0<=1-exp(-x*x/2)<=bpow radix2 (-67).
Proof.
  intros X. pose proof(exp_ineq1_le (-x*x/2)) as Lower.
  assert (Upper : exp(-x*x/2)<=1).
  { destruct(Req_dec x 0) as [Zero|Nonzero].
    - rewrite Zero;replace(-0*0/2)with 0 by field;rewrite exp_0;lra.
    - rewrite <- exp_0;apply Rlt_le,exp_increasing;nra. }
  assert (Square : x*x<=bpow radix2 (-33)*bpow radix2 (-33)).
  { apply Rabs_le_inv in X;pose proof(bpow_gt_0 radix2 (-33));nra. }
  replace (bpow radix2 (-67)) with (bpow radix2 (-33)*bpow radix2 (-33)/2).
  - split;nra.
  - unfold Rdiv;change(/2)with(bpow radix2 (-1));rewrite <- !bpow_plus;reflexivity.
Qed.
