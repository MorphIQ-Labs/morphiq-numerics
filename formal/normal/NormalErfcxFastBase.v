(** The two erfcx kernels used at the high word of x/sqrt(2), with their
    analytic bounds attached before the low-word argument correction. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64 RoundingConstant.
Require Import StageGappa ErfcxDecision ErfcxConstants ErfcxGaussianTarget
  ErfcxTableEntry ErfcxTableBound ErfcxTableFast ErfcxTableAnalyticEntry
  ErfcxMiddleValue ErfcxMiddleAnalytic ErfcxTailIntegral ErfcxScaledAnalytic
  NormalErfcxIdentity NormalErfcxLinear.
Open Scope R_scope.

Definition normal_erfcx_table_input x :=
  match Bcompare 53 1024 x (erfcx_pow2 4)with Some Lt=>true | _=>false end.
Definition normal_erfcx_fast_base64 x :=
  if normal_erfcx_table_input x then table_eval64 x else middle64 x.

Lemma normal_erfcx_table_input_spec x : finite x ->
  if normal_erfcx_table_input x then B x<16 else 16<=B x.
Proof.
  intros Fx;destruct(erfcx_pow2_ok 4 ltac:(lia))as[Fc C].
  unfold normal_erfcx_table_input;rewrite(Bcompare_correct 53 1024 _ _ Fx Fc),C.
  change(bpow radix2 4)with 16;destruct(Rcompare_spec(B x)16);cbn;lra.
Qed.

Theorem normal_erfcx_fast_base_ieee x : finite x -> /4<=B x<=32 ->
  let '(h,l):=normal_erfcx_fast_base64 x in
  finite h /\ finite l /\ B h=rndF(B h+B l) /\ 0<B h<=8 /\
  Rabs((B h+B l)-gaussian_erfcx(B x))<=3*bpow radix2 (-68)*gaussian_erfcx(B x).
Proof.
  intros Fx X;pose proof(normal_erfcx_table_input_spec x Fx)as Screen.
  unfold normal_erfcx_fast_base64;destruct(normal_erfcx_table_input x).
  - destruct(table_approximation_ieee x Fx ltac:(split;lra))as[Positive Approx].
    pose proof(table_evaluation_error x Fx ltac:(split;lra))as Eval.
    pose proof(table_eval_normalized_ieee x Fx ltac:(split;lra))as Words.
    destruct(table_eval64 x)as[h l].
    destruct Words as[Fh [Fl [Value [Norm H]]]];destruct Eval as[_ [_ Eval]].
    pose proof(table_composed_error (B h+B l)(table_exact x)(gaussian_erfcx(B x))Positive Approx Eval)as Error.
    rewrite Rabs_minus_sym,(Rabs_pos_eq(gaussian_erfcx(B x)))in Error by lra.
    repeat split;try assumption;pose proof(bpow_gt_0 radix2 (-9));lra.
  - assert(Y : /512<=1/B x<=/16).
    { unfold Rdiv;rewrite Rmult_1_l;split;apply Rinv_le_contravar;lra. }
    assert(T : /2^18<=(1/B x)*(1/B x)<=/2^8)by(simpl;nra).
    destruct(middle_integral_contract _ T)as[Range Approx].
    pose proof(Rabs_le_inv _ _ cs_split_bound)as Constant.
    pose proof(middle_normalized_ieee x inv_sqrt_pi (tail_integral((1/B x)*(1/B x)))
      Fx ltac:(split;lra)inv_sqrt_pi_positive Constant Range Approx)as Middle.
    destruct(middle64 x)as[h l];destruct Middle as[Fh [Fl [Relative [Norm H]]]].
    assert(Target : (inv_sqrt_pi/B x)*tail_integral((1/B x)*(1/B x))=gaussian_erfcx(B x)).
    { rewrite <-positive_erfcx_gaussian by lra;unfold positive_erfcx;replace(1/B x)with(/B x)by(unfold Rdiv;ring);reflexivity. }
    rewrite Target in Relative.
    pose proof(normal_erfcx_compact_range(B x)ltac:(split;lra))as Positive.
    assert(Error : Rabs((B h+B l)-gaussian_erfcx(B x))<=3*bpow radix2 (-68)*gaussian_erfcx(B x)).
    { replace((B h+B l)-gaussian_erfcx(B x))with
        ((((B h+B l)-gaussian_erfcx(B x))/gaussian_erfcx(B x))*gaussian_erfcx(B x))by(field;lra).
      rewrite Rabs_mult,(Rabs_pos_eq(gaussian_erfcx(B x)))by lra.
      apply Rabs_le in Relative;bpow_num_all;nra. }
    repeat split;try assumption;assert(0</2^21)by(interval with(i_prec 80));lra.
Qed.

Theorem normal_erfcx_fast_base_low x : finite x -> /4<=B x<=32 ->
  let '(h,l):=normal_erfcx_fast_base64 x in Rabs(B l)<=bpow radix2 (-50).
Proof.
  intros Fx X;pose proof(normal_erfcx_fast_base_ieee x Fx X)as Base.
  destruct(normal_erfcx_fast_base64 x)as[h l];destruct Base as[_ [_ [Norm [_ Error]]]].
  pose proof(normal_erfcx_compact_range(B x)ltac:(split;lra))as Target.
  assert(Sum : Rabs(B h+B l)<=16).
  { pose proof(Rabs_triang_inv(B h+B l)(gaussian_erfcx(B x)));rewrite(Rabs_pos_eq(gaussian_erfcx(B x)))in H by lra;bpow_num_all;nra. }
  pose proof(rnd_err_below(B h+B l)4 ltac:(lia)Sum)as Rounded;rewrite <-Norm in Rounded.
  change(4-54)%Z with(-50)%Z in Rounded;replace(B h-(B h+B l))with(-B l)in Rounded by ring.
  rewrite Rabs_Ropp in Rounded;exact Rounded.
Qed.
