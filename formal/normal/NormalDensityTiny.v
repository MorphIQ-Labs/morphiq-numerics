(** Tiny arguments round to the generated density constant. This bypasses
    the Gaussian reduction altogether, for scalar and homogeneous SIMD. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64 RoundingGaps.
Require Import StageGappa NormalConstants NormalCentered NormalGaussianKernel NormalAccurateDensity.
Open Scope R_scope.

Theorem normal_density_tiny_correct x : Rabs x<=bpow radix2 (-33) ->
  rndF(normal_density x)=B normal_density_hi.
Proof.
  intros X;destruct normal_density_hi_ok as[F Value].
  assert (Positive : 0<B normal_density_hi)by(rewrite Value;interval with(i_prec 80)).
  assert (Magnitude : (mag radix2 (B normal_density_hi) : Z)=(-1)%Z).
  { apply mag_unique;rewrite Rabs_pos_eq by lra;rewrite Value;bpow_num;split;interval with(i_prec 80). }
  assert (Ulp : ulp radix2 (FLT_exp (-1074)53)(B normal_density_hi)=bpow radix2 (-54)).
  { rewrite ulp_neq_0 by lra;unfold cexp;rewrite Magnitude;reflexivity. }
  destruct(gap_below (B normal_density_hi)(B_fmt normal_density_hi)Positive)as[_ Below].
  specialize(Below ltac:(rewrite Magnitude,Value;bpow_num;interval with(i_prec 80))).
  rewrite Ulp in Below.
  pose proof(normal_gaussian_small_error x X)as Gaussian.
  assert (Density : 0<normal_density_constant)by(unfold normal_density_constant;interval with(i_prec 80)).
  assert (Bounds : normal_density_constant*(1-bpow radix2 (-67))<=normal_density x<=normal_density_constant).
  { unfold normal_density;split;nra. }
  assert (Cell : B normal_density_hi-bpow radix2 (-55)<normal_density_constant*(1-bpow radix2 (-67)) /\
    normal_density_constant<B normal_density_hi+bpow radix2 (-55)).
  { rewrite Value;unfold normal_density_constant;bpow_num;split;interval with(i_prec 200). }
  apply(round_within (B normal_density_hi)(normal_density x)(bpow radix2 (-54))).
  - apply B_fmt.
  - exact Positive.
  - rewrite Ulp;lra.
  - lra.
  - replace(bpow radix2 (-54)/2)with(bpow radix2 (-55))by(bpow_num;field).
    apply Rabs_lt;split;lra.
Qed.
