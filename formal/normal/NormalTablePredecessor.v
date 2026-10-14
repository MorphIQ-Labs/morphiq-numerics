(** The predecessor lookup repairs a rounded crossing of a last-binade
    cell boundary without increasing the Taylor residual radius. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add Encodings.
From Q Require Import Q256 Q256Real.
Require Import StageGappa ErfcxTableReduction ErfcxAccurateInputs
  NormalResidualGrid NormalTableLookup NormalLastTableCell NormalErfcxTaylor.
Open Scope R_scope.

Definition normal_previous64 h := b64_of_bits(bits_of_b64 h-1).

Lemma normal_table_previous h : finite h -> 8<=B h<16 ->
  finite(normal_previous64 h) /\
  B h-bpow radix2 (-49)<=B(normal_previous64 h)<B h.
Proof.
  intros F H.
  assert (Normal : bpow radix2 (-1021)<=B h).
  { eapply Rle_trans;[|exact(proj1 H)]. change 8 with(bpow radix2 3);apply bpow_le;lia. }
  destruct(bits_down h F Normal)as[Previous Value]. split;[exact Previous|].
  unfold normal_previous64;rewrite Value,pred_eq_pos by lra;unfold pred_pos.
  assert (Magnitude : (Raux.mag radix2(B h):Z)=4%Z).
  { assert(Lower : (4<=Raux.mag radix2(B h))%Z).
    { apply mag_ge_bpow;change(bpow radix2(4-1))with 8;rewrite Rabs_pos_eq;lra. }
    assert(Upper : (Raux.mag radix2(B h)<=4)%Z).
    { apply mag_le_bpow;[lra|change(bpow radix2 4)with 16;rewrite Rabs_pos_eq;lra]. } lia. }
  rewrite Magnitude. rewrite ulp_neq_0 by lra;unfold cexp;rewrite Magnitude.
  unfold FLT_exp.
  change(Z.max(4-1-53)(-1074))with(-50)%Z.
  change(Z.max(4-53)(-1074))with(-49)%Z.
  destruct(Req_bool(B h)(bpow radix2(4-1)));
    bpow_num;split;lra.
Qed.

Lemma normal_previous_cell h : finite h -> 8<=B h<16 ->
  let '(i,c,r,e):=table_binade64 h in
  B h=B c-/8 ->
  let '(ip,cp,rp,ep):=table_reduce64(normal_previous64 h) in
  (0<=ip<177)%Z /\ finite cp /\
  B cp=ErfcxAccurateCenterModel.accurate_center(Z.to_nat ip) /\
  0<B cp<=16 /\
  (B h=8 /\ Rabs(B(normal_previous64 h)-B cp)<=/16 \/ B cp=B h-/8).
Proof.
  intros F H. pose proof(normal_last_cell h F H)as Cell.
  destruct(table_binade64 h)as[[[i c]r]e];cbv zeta in Cell.
  destruct Cell as[j [J [_ [_ [Fc [Center Lookup]]]]]]. intros AtBoundary.
  destruct(normal_table_previous h F H)as[Fp Previous].
  assert (Boundary : B h=8+IZR j/4)by(rewrite Center in AtBoundary;lra).
  assert (Small : bpow radix2 (-49)<1/16)by(interval with(i_prec 80)).
  destruct(Z.eq_dec j 0)as[Zero|Nonzero].
  - subst j;change(IZR 0)with 0 in Boundary.
    pose proof(normal_table_reduce_small _ Fp ltac:(split;lra))as Reduction.
    destruct(table_reduce64(normal_previous64 h))as[[[ip cp]rp]ep];cbv zeta in Reduction.
    destruct Reduction as[I [Fcp [Ccp [Cr Radius]]]].
    split;[exact I|]. split;[exact Fcp|]. split;[exact Ccp|]. split;[exact Cr|]. left;split;lra.
  - assert (Jpos : 1<=IZR j).
    { change 1 with(IZR 1);apply IZR_le;lia. }
    assert (Hp : 8<=B(normal_previous64 h)<16)by(split;lra).
    destruct ErfcxReciprocal.one_ok as[Fo Bo]. unfold table_reduce64.
    rewrite (Bcompare_correct 53 1024 (normal_previous64 h) ErfcxReciprocal.one Fp Fo),Bo.
    destruct(Rcompare_spec(B(normal_previous64 h))1)as[Low|Equal|High];try lra.
    pose proof(normal_last_cell _ Fp Hp)as Cellp.
    pose proof(ErfcxAccurateTaylorReduction.accurate_table_reduce_ieee _ Fp ltac:(split;lra))as Basic.
    unfold table_reduce64 in Basic.
    rewrite (Bcompare_correct 53 1024 (normal_previous64 h) ErfcxReciprocal.one Fp Fo),Bo in Basic.
    destruct(Rcompare_spec(B(normal_previous64 h))1)as[Low2|Equal2|High2];try lra.
    destruct(table_binade64(normal_previous64 h))as[[[ip cp]rp]ep];cbv zeta in Cellp,Basic.
    destruct Cellp as[k [K [_ [_ [Fcp [Cp Where]]]]]].
    destruct Basic as[I [_ [_ [Ccp _]]]].
    assert (Before : (k<j)%Z).
    { apply lt_IZR;lra. }
    assert (After : (j<k+2)%Z).
    { apply lt_IZR;rewrite plus_IZR;change(IZR 2)with 2;lra. }
    assert (Index : k=(j-1)%Z)by lia;subst k.
    split;[exact I|]. split;[exact Fcp|]. split;[exact Ccp|]. split.
    + rewrite Cp,minus_IZR;split;lra.
    + right;rewrite Cp,minus_IZR,Boundary;field.
Qed.

Theorem normal_extended_previous_radius x : valid x -> /4<=qval x<16 ->
  8<=B(Q256.to_f64 x)<16 ->
  let '(i,c,r,e):=table_binade64(Q256.to_f64 x) in
  /8<Rabs(qval(normal_q_erfcx_residual x c)) ->
  let '(ip,cp,rp,ep):=table_reduce64(normal_previous64(Q256.to_f64 x)) in
  (0<=ip<177)%Z /\ finite cp /\
  B cp=ErfcxAccurateCenterModel.accurate_center(Z.to_nat ip) /\
  Rabs(qval(normal_q_erfcx_residual x cp))<=/8.
Proof.
  intros X Range High.
  destruct(normal_table_input_round x X ltac:(split;lra))as[Fh [_ [_ Difference]]].
  pose proof(normal_extended_last_cell_miss x X Range High)as Crossing.
  pose proof(normal_previous_cell _ Fh High)as Repair.
  destruct(table_binade64(Q256.to_f64 x))as[[[i c]r]e];cbv zeta in Crossing,Repair.
  intros Miss;specialize(Crossing Miss);destruct Crossing as[Boundary Below].
  specialize(Repair Boundary).
  destruct(table_reduce64(normal_previous64(Q256.to_f64 x)))as[[[ip cp]rp]ep];cbv zeta in Repair.
  destruct Repair as[I [Fcp [Ccp [Cp Cases]]]].
  split;[exact I|]. split;[exact Fcp|]. split;[exact Ccp|].
  apply normal_extended_residual_radius;try assumption;[split;lra|].
  apply Rabs_le_inv in Difference.
  assert (Small : bpow radix2 (-49)<=/16)by(interval with(i_prec 80)).
  destruct Cases as[[AtEight Radius]|Center].
  - destruct(normal_table_previous _ Fh High)as[_ Previous].
    assert (Gap : Rabs(qval x-B(normal_previous64(Q256.to_f64 x)))<=bpow radix2 (-49)).
    { apply Rabs_le;split;lra. }
    replace(qval x-B cp)with((qval x-B(normal_previous64(Q256.to_f64 x)))+
      (B(normal_previous64(Q256.to_f64 x))-B cp))by ring.
    eapply Rle_trans;[apply Rabs_triang|];lra.
  - rewrite Center;apply Rabs_le;split;lra.
Qed.

Definition normal_q_erfcx_previous_table x :=
  let '(i,c,r,e):=table_reduce64(normal_previous64(Q256.to_f64 x)) in
  normal_q_erfcx_taylor_at x c (Z.to_nat i).

Theorem normal_q_erfcx_previous_table_error x : valid x -> /4<=qval x<16 ->
  8<=B(Q256.to_f64 x)<16 ->
  let '(i,c,r,e):=table_binade64(Q256.to_f64 x) in
  /8<Rabs(qval(normal_q_erfcx_residual x c)) ->
  valid(normal_q_erfcx_previous_table x) /\
  Rabs(qval(normal_q_erfcx_previous_table x)-ErfcxGaussianTarget.gaussian_erfcx(qval x))<=bpow radix2 (-123).
Proof.
  intros X Range High;pose proof(normal_extended_previous_radius x X Range High)as Repair.
  destruct(table_binade64(Q256.to_f64 x))as[[[i c]r]e];cbv zeta in Repair.
  intros Miss;specialize(Repair Miss).
  unfold normal_q_erfcx_previous_table.
  destruct(table_reduce64(normal_previous64(Q256.to_f64 x)))as[[[ip cp]rp]ep];cbv zeta in Repair.
  destruct Repair as[I [Fcp [Center Radius]]].
  apply normal_q_erfcx_taylor_at_error;try assumption;[split;lra|lia].
Qed.

