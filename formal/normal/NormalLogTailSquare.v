(** Exact half-squares across both far-tail reduction domains. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add Binary64Mul IEEE64 IEEE64Mul IEEE64Eft
  RoundingTest Grid.
Require Import StageGappa ErfcxEntryTables.
Open Scope R_scope.

Definition normal_log_tail_square64 x := two_prod64 x (fmul neg_half x).

Theorem normal_log_tail_square_exact x : finite x ->
  bpow radix2 (-435)<=B x<=bpow radix2 45 ->
  let '(h,l):=normal_log_tail_square64 x in
  finite h /\ finite l /\ B h=rndF(B h+B l) /\
  B h+B l= -B x*B x/2 /\
  bpow radix2 (-871)<=Rabs(B h)<=bpow radix2 89.
Proof.
  intros Fx X;destruct neg_half_ok as[Fc [C _]].
  assert(Cv : B neg_half= -/2)by(rewrite C;change(-1*/2= -/2);ring).
  assert(Xp : 0<B x)by(pose proof(bpow_gt_0 radix2 (-435));lra).
  assert(Grid : on_grid (-487) (B x)).
  { change(-487)%Z with(-435-52)%Z.
    apply(grid_fmt_bound (FLT_exp emin prec) (-435));
      [unfold FLT_exp,prec;lia|apply B_fmt|right;rewrite Rabs_pos_eq;lra]. }
  destruct(fmul_exact neg_half x Fc Fx)as[Fhalf Half].
  - rewrite Cv;replace(-/2*B x)with(-(B x*bpow radix2 (-1)))by(change(bpow radix2 (-1))with(/2);ring).
    apply generic_format_opp;apply(scaled_fmt_grid _ (-487));[apply B_fmt|exact Grid|lia].
  - rewrite Cv,Rabs_mult,Rabs_Ropp,(Rabs_pos_eq(/2)),(Rabs_pos_eq(B x))by lra.
    eapply Rle_lt_trans;[|apply(bpow_lt radix2 45 1024);lia].
    bpow_num_all;lra.
  - assert(HalfValue : B(fmul neg_half x)= -B x/2)by(rewrite Half,Cv;field).
    assert(Magnitude : bpow radix2 (-871)<=B x*B x/2<=bpow radix2 89).
    { replace(bpow radix2 (-871))with(bpow radix2 (-435)*bpow radix2 (-435)/2)by(bpow_num;field).
      replace(bpow radix2 89)with(bpow radix2 45*bpow radix2 45/2)by(bpow_num;field).
      pose proof(bpow_gt_0 radix2 (-435));pose proof(bpow_gt_0 radix2 45);split;nra. }
    assert(Domain : in_two_prod_domain (B x) (B(fmul neg_half x))).
    { right;rewrite HalfValue,Rabs_left by nra.
      eapply Rle_trans;[apply(bpow_le radix2 (-969) (-871));lia|nra]. }
    pose proof(two_prod_ieee 45 44 x (fmul neg_half x) Fx Fhalf
      ltac:(rewrite Rabs_pos_eq;lra)
      ltac:(rewrite HalfValue,Rabs_left by lra;bpow_num_all;lra)
      ltac:(lia)ltac:(lia)ltac:(lia) Domain)as Square.
    unfold normal_log_tail_square64;destruct(two_prod64 x (fmul neg_half x))as[h l].
    destruct Square as[Fh [Fl [High Exact]]];rewrite HalfValue in High,Exact.
    assert(Value : B h+B l= -B x*B x/2)by nra.
    assert(Norm : B h=rndF(B h+B l))by(rewrite Exact;exact High).
    assert(Abs : Rabs(B h)=rndF(B x*B x/2)).
    { rewrite High,<-round_NE_abs by exact _.
      replace(Rabs(B x*(-B x/2)))with(B x*B x/2)by(rewrite Rabs_left by nra;field).
      reflexivity. }
    repeat split;try assumption;rewrite Abs.
    + apply round_ge_generic;[exact _|exact _|apply generic_format_bpow;unfold FLT_exp,emin,prec;lia|exact(proj1 Magnitude)].
    + apply round_le_generic;[exact _|exact _|apply generic_format_bpow;unfold FLT_exp,emin,prec;lia|exact(proj2 Magnitude)].
Qed.
