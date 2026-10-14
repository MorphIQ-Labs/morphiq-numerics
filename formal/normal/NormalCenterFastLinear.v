(** Density-times-argument for the regular central branch. Its low word's
    spacing keeps the final double-word product inside its proved domain. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add Binary64Grid IEEE64 IEEE64Mul IEEE64Grid RoundingConstant.
Require Import StageGappa NormalConstants NormalCentered NormalCenterSmall NormalCenterFastProduct NormalCenterFastTail.
Open Scope R_scope.

Theorem normal_center_linear_regular_ieee x : finite x -> bpow radix2 (-33)<=Rabs(B x)<=/2 ->
  let '(h,l):=normal_center_small64 x in
  finite h /\ finite l /\ B h=rndF(B h+B l) /\
  bpow radix2 (-36)<=Rabs(B h)<=1 /\ Rabs(B l)<=bpow radix2 (-54) /\
  binary_grid (-88)(B h) /\ binary_grid (-193)(B l) /\
  Rabs((B h+B l)-normal_density_constant*B x)<=normal_density_constant*Rabs(B x)*bpow radix2 (-103).
Proof.
  intros Fx X;pose proof(normal_center_linear_ieee x Fx
    ltac:(split;[eapply Rle_trans with(bpow radix2 (-33));[apply bpow_le;lia|exact(proj1 X)]|lra]))as Linear.
  destruct normal_density_hi_ok as[Fdh Dh],normal_density_lo_ok as[Fdl Dl].
  assert(Gdh : binary_grid (-54)(B normal_density_hi)).
  { apply(binary_grid_binary64 _ (-2));rewrite Dh;bpow_num;interval with(i_prec 120). }
  assert(Gdl : binary_grid (-108)(B normal_density_lo)).
  { apply(binary_grid_binary64 _ (-56));rewrite Dl;bpow_num;interval with(i_prec 120). }
  assert(Gx : binary_grid (-85)(B x))by(apply(binary_grid_binary64 x (-33));exact(proj1 X)).
  assert(Leading : binary_grid (-193)(B normal_density_hi*B x)).
  { eapply binary_grid_finer;[|exact(binary_grid_mul (-54)(-85)(B normal_density_hi)(B x)Gdh Gx)];lia. }
  assert(Cross : binary_grid (-193)(B normal_density_lo*B x)).
  { exact(binary_grid_mul (-108)(-85)(B normal_density_lo)(B x)Gdl Gx). }
  pose proof(normal_center_grid_domain (-193)(B normal_density_hi)(B x)ltac:(lia)Leading)as Domain.
  pose proof(mul_f64_grid_ieee (-193)normal_density_hi normal_density_lo x Fdh Fdl Fx
    ltac:(rewrite Dh;interval with(i_prec 120))ltac:(rewrite Dl;interval with(i_prec 120))
    ltac:(eapply Rle_trans;[exact(proj2 X)|interval with(i_prec 80)])Domain Leading Cross)as Grid.
  unfold normal_center_small64 in *;rewrite normal_density_constant_exact in *.
  destruct(mul_f64_64 normal_density_hi normal_density_lo x)as[h l].
  destruct Linear as[Fh [Fl [Norm Error]]];destruct Grid as[_ Gl].
  assert(C : 3/8<=normal_density_constant<=/2)by(unfold normal_density_constant;split;interval with(i_prec 100)).
  assert(Target : Rabs(normal_density_constant*B x)=normal_density_constant*Rabs(B x)).
  { rewrite Rabs_mult,(Rabs_pos_eq normal_density_constant)by lra;reflexivity. }
  assert(SumRange : bpow radix2 (-36)<=Rabs(B h+B l)<=1).
  { pose proof(Rabs_triang_inv (B h+B l)(normal_density_constant*B x))as A.
    pose proof(Rabs_triang_inv (normal_density_constant*B x)(B h+B l))as D.
    rewrite Rabs_minus_sym in D;rewrite Target in A,D;bpow_num_all;split;nra. }
  assert(High : bpow radix2 (-36)<=Rabs(B h)<=1).
  { rewrite Norm;split.
    - apply abs_round_ge_generic;[exact _|exact _| |exact(proj1 SumRange)].
      apply generic_format_bpow;unfold FLT_exp,emin,prec;lia.
    - change 1 with(bpow radix2 0);apply normal_center_round_bound;[exact(proj2 SumRange)|lia]. }
  pose proof(rnd_err_below (B h+B l)0 ltac:(lia)(proj2 SumRange))as Rounded;rewrite <-Norm in Rounded.
  change(0-54)%Z with(-54)%Z in Rounded.
  assert(Low : Rabs(B l)<=bpow radix2 (-54)).
  { replace(B h-(B h+B l))with(-B l)in Rounded by ring;rewrite Rabs_Ropp in Rounded;exact Rounded. }
  assert(Gh : binary_grid (-88)(B h))by(apply(binary_grid_binary64 h (-36));exact(proj1 High)).
  repeat split;tauto.
Qed.
