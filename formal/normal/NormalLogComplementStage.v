(** A relative bound for the existing ln1p stage-B result on negative
    probability arguments. The rounded guard bounds both its evaluation
    error and the low word used by the normal log-CDF correction. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Mul IEEE64Eft Binary64Mul Grid RoundingConstant RoundingTest.
Require Import StageGappa Ln1pStageB Ln1pLemmas Ln1pReduction NormalComplementAnalytic.
Open Scope R_scope.

Lemma normal_log_stage_small_guard x : finite x ->
  bpow radix2 (-54)<=Rabs(B x)<bpow radix2 (-9) ->
  let '(_,_,e):=stage_b_small_parts x in B e<=Rabs(B x)*bpow radix2 (-68).
Proof.
  intros Fx X.
  assert(Domain : in_two_prod_domain(B x)(B x)).
  { right;rewrite Rabs_mult.
    eapply Rle_trans with(bpow radix2 (-54)*bpow radix2 (-54)).
    - rewrite <-bpow_plus;apply bpow_le;lia.
    - apply Rmult_le_compat;try apply bpow_ge_0;lra. }
  pose proof(two_prod_ieee 0 0 x x Fx Fx
    ltac:(change(bpow radix2 0)with 1;bpow_num_all;lra)
    ltac:(change(bpow radix2 0)with 1;bpow_num_all;lra)
    ltac:(lia)ltac:(lia)ltac:(lia)Domain)as Product.
  unfold stage_b_small_parts;destruct(two_prod64 x x)as[p pl].
  destruct Product as[Fp [Fpl [Pvalue Psum]]];cbv zeta.
  assert(P : 0<=B p<=bpow radix2 (-18)).
  { rewrite Pvalue;split.
    - apply round_ge_generic;try exact _;[apply generic_format_0|nra].
    - apply round_le_generic;try exact _;[apply(fmt_pow(-18));lia|].
      pose proof(Rabs_le_inv (B x)(bpow radix2 (-9))ltac:(lra)); bpow_num_all;nra. }
  destruct c_kb_ok as[Fc C];destruct c_ebr_ok as[Fd D].
  destruct(fmul_s p c_kb Fp Fc)as[Fm M].
  { rewrite C,Rabs_mult,(Rabs_pos_eq(B p))by lra.
    rewrite Rabs_pos_eq by apply bpow_ge_0;bpow_num_all;interval with(i_prec 80). }
  assert(Mrange : 0<=B(fmul p c_kb)<=bpow radix2 (-69)).
  { rewrite M,C;split.
    - apply round_ge_generic;try exact _;[apply generic_format_0|bpow_num_all;nra].
    - apply round_le_generic;try exact _;[apply(fmt_pow(-69));lia|bpow_num_all;nra]. }
  destruct(fadd_s (fmul p c_kb)c_ebr Fm Fd)as[Fi I].
  { rewrite D;apply Rabs_le; bpow_num_all;split;lra. }
  assert(Irange : 0<=B(fadd(fmul p c_kb)c_ebr)<=bpow radix2 (-68)).
  { rewrite I,D;split.
    - apply round_ge_generic;try exact _;[apply generic_format_0|bpow_num_all;lra].
    - apply round_le_generic;try exact _;[apply(fmt_pow(-68));lia|bpow_num_all;lra]. }
  assert(Fabs : finite(b64_abs x))by(unfold b64_abs;destruct x;exact Fx).
  destruct(fmul_s (b64_abs x)(fadd(fmul p c_kb)c_ebr)Fabs Fi)as[Fe E].
  { rewrite B_abs,Rabs_mult,(Rabs_pos_eq(Rabs(B x)))by apply Rabs_pos.
    rewrite(Rabs_pos_eq(B(fadd(fmul p c_kb)c_ebr)))by lra;pose proof(Rabs_pos(B x));bpow_num_all;nra. }
  rewrite E,B_abs.
  assert(Exact : rndF(Rabs(B x)*bpow radix2 (-68))=Rabs(B x)*bpow radix2 (-68)).
  { apply rnd_scale with(m:=(-54)%Z);try lia.
    - rewrite <-B_abs;apply B_fmt.
    - right;rewrite Rabs_Rabsolu;exact(proj1 X). }
  rewrite <-Exact;apply round_le;try exact _.
  apply Rmult_le_compat_l;[apply Rabs_pos|exact(proj2 Irange)].
Qed.

Theorem normal_log_stage_guard x : finite x ->
  bpow radix2 (-54)<=Rabs(B x) ->
  let '(_,_,e):=stage_b_parts x in B e<=Rabs(B x)*bpow radix2 (-68).
Proof.
  intros Fx X;unfold stage_b_parts.
  destruct c_two_m9_ok as[Fc C].
  assert(Fabs : finite(b64_abs x))by(unfold b64_abs;destruct x;exact Fx).
  rewrite(Bcompare_correct 53 1024 (b64_abs x)c_two_m9 Fabs Fc),B_abs,C.
  destruct(Rcompare_spec(Rabs(B x))(bpow radix2 (-9)))as[L|E|G];cbv beta iota.
  - apply normal_log_stage_small_guard;[exact Fx|split;assumption].
  - unfold stage_b_table_parts,stage_b_core.
    destruct(two_prod64 _ _)as[p pl];cbv zeta;rewrite(proj2 c_eb_ok),E;bpow_num_all;lra.
  - unfold stage_b_table_parts,stage_b_core.
    destruct(two_prod64 _ _)as[p pl];cbv zeta;rewrite(proj2 c_eb_ok);bpow_num_all;nra.
Qed.

Theorem normal_log_complement_stage_ieee x : finite x ->
  -/3<=B x<= -bpow radix2 (-54) ->
  let '(h,l,_):=stage_b_parts x in finite h /\ finite l /\
  Rabs(B h)<=3*Rabs(B x) /\ Rabs(B l)<=Rabs(B x)*bpow radix2 (-15) /\
  Rabs((B h+B l)-ln(1+B x))<=Rabs(B x)*bpow radix2 (-68).
Proof.
  intros Fx X.
  assert(Abs : Rabs(B x)= -B x)by(apply Rabs_left1;bpow_num_all;lra).
  pose proof(normal_log_stage_guard x Fx ltac:(rewrite Abs;lra))as Guard.
  pose proof(stage_b_eval x Fx ltac:(rewrite Abs;lra)
    ltac:(bpow_num_all;split;lra))as Stage.
  pose proof(normal_complement_target_range (-B x)ltac:(bpow_num_all;split;lra))as Target.
  replace(1- -B x)with(1+B x)in Target by ring.
  destruct(stage_b_parts x)as[[h l]e].
  destruct Stage as[Fh [Fl [Fe [E [H [L Error]]]]]].
  specialize(Error (ln(1+B x))ltac:(rewrite Rminus_diag_eq,Rabs_R0 by reflexivity;apply Rmult_le_pos;[left;apply Rinv_0_lt_compat;apply pow_lt;lra|apply Rabs_pos])).
  assert(Low : Rabs(B l)<=Rabs(B x)*bpow radix2 (-15)).
  { pose proof(Rabs_pos(ln(1+B x)-(B h+B l)));bpow_num_all;nra. }
  assert(Err : Rabs((B h+B l)-ln(1+B x))<=Rabs(B x)*bpow radix2 (-68)).
  { rewrite Rabs_minus_sym;pose proof(Rabs_pos(B l));bpow_num_all;nra. }
  repeat split;try assumption.
  pose proof(Rabs_triang_inv(B h)(ln(1+B x)))as Diff.
  replace(B h-ln(1+B x))with(((B h+B l)-ln(1+B x))-B l)in Diff by ring.
  pose proof(Rabs_triang((B h+B l)-ln(1+B x))(-B l))as Sum.
  rewrite Rabs_Ropp in Sum.
  rewrite(Rabs_left1(ln(1+B x)))in Diff by lra.
  change(Rabs((B h+B l)-ln(1+B x)-B l)<=Rabs((B h+B l)-ln(1+B x))+Rabs(B l))in Sum.
  rewrite Abs in *;bpow_num_all;nra.
Qed.
