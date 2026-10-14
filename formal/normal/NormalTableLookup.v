(** Rounding and table-cell bounds for an extended erfcx argument. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core Relative.
From Interval Require Import Tactic.
From Q Require Import Q256 Q256Real.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add RoundingCore.
Require Import StageGappa ExpReduction ErfcxAccurateInputs ErfcxTableReduction
  ErfcxAccurateTaylorReduction ErfcxAccurateCenterModel NormalResidualGrid
  NormalErfcxTaylor ErfcxGaussianTarget.
Open Scope R_scope.

Theorem normal_table_input_round x : valid x -> /4<=qval x<=16 ->
  finite(Q256.to_f64 x) /\ /4<=B(Q256.to_f64 x)<=16 /\
  B(Q256.to_f64 x)=rndF(qval x) /\
  Rabs(B(Q256.to_f64 x)-qval x)<=bpow radix2 (-49).
Proof.
  intros X Range.
  assert (Low : /4<=rndF(qval x)).
  { change(/4)with(bpow radix2 (-2));apply round_ge_generic;[exact _|exact _| |exact(proj1 Range)].
    apply generic_format_bpow;unfold FLT_exp,emin,prec;lia. }
  assert (High : Rabs(rndF(qval x))<=16).
  { apply abs_round_le_generic;[exact _|exact _| |rewrite Rabs_pos_eq;lra].
    change 16 with(bpow radix2 4);apply generic_format_bpow;unfold FLT_exp,emin,prec;lia. }
  assert (NoOverflow : Rabs(rndF(qval x))<bpow radix2 1024).
  { eapply Rle_lt_trans;[exact High|change 16 with(bpow radix2 4);apply bpow_lt;lia]. }
  destruct(q_to_float_round _ X NoOverflow)as[F Value].
  assert (Normal : bpow radix2 (-1022)<=Rabs(qval x)).
  { rewrite Rabs_pos_eq by lra;eapply Rle_trans;[|exact(proj1 Range)].
    change(/4)with(bpow radix2 (-2));apply bpow_le;lia. }
  destruct(relative_error_N_FLT_ex radix2 emin prec ltac:(unfold prec;lia) ne (qval x) Normal)
    as[d [D Dvalue]].
  replace(/2*bpow radix2 (-prec+1))with(bpow radix2 (-53))in D
    by(unfold prec;change(/2)with(bpow radix2 (-1));rewrite <-bpow_plus;reflexivity).
  split;[exact F|]. rewrite Value;split;[apply Rabs_le_inv in High;split;lra|].
  split;[reflexivity|]. rewrite Dvalue.
  replace(qval x*(1+d)-qval x)with(qval x*d)by ring.
  rewrite Rabs_mult,(Rabs_pos_eq(qval x))by lra.
  replace(bpow radix2 (-49))with(16*bpow radix2 (-53))by(bpow_num;field).
  apply Rmult_le_compat;[lra|apply Rabs_pos|lra|exact D].
Qed.

Lemma normal_table_binade_small h : finite h -> 1<=B h<8 ->
  let '(i,c,r,e):=table_binade64 h in
  (0<=i<177)%Z /\ finite c /\ B c=accurate_center(Z.to_nat i) /\
  0<B c<=16 /\ Rabs(B h-B c)<=/16.
Proof.
  intros F H. pose proof(table_binade_ieee h F ltac:(split;lra))as Reduction.
  destruct(table_binade64 h)as[[[i c]r]e];cbv zeta in Reduction.
  destruct Reduction as[E [I [Fc [Fr [Exact [Center Radius]]]]]].
  assert (SmallExponent : (e<=2)%Z).
  { destruct(Z_le_gt_dec e 2);[assumption|]. assert(e=3)%Z by lia;subst e.
    assert (Index : 0<=IZR(i-49-32*3))by(apply IZR_le;lia).
    change(bpow radix2 3)with 8 in Center;change(bpow radix2(3-6))with(/8)in Radius.
    apply Rabs_le_inv in Radius;lra. }
  assert (Cb : 0<B c<=16).
  { assert (Index : 0<=IZR(i-49-32*e)<=31).
    { split;[apply IZR_le;lia|change 31 with(IZR 31);apply IZR_le;lia]. }
    assert (Power : 1<=bpow radix2 e<=4).
    { split;[change 1 with(bpow radix2 0)|change 4 with(bpow radix2 2)];apply bpow_le;lia. }
    rewrite Center;split;interval with(i_prec 80). }
  split;[lia|]. split;[exact Fc|]. split.
  - rewrite accurate_binade_center with(e:=e)by assumption;exact Center.
  - split;[exact Cb|]. replace(B h-B c)with(B r)by lra.
    eapply Rle_trans;[exact Radius|]. change(/16)with(bpow radix2 (-4));apply bpow_le;lia.
Qed.

Theorem normal_table_reduce_small h : finite h -> /4<=B h<8 ->
  let '(i,c,r,e):=table_reduce64 h in
  (0<=i<177)%Z /\ finite c /\ B c=accurate_center(Z.to_nat i) /\
  0<B c<=16 /\ Rabs(B h-B c)<=/16.
Proof.
  intros F H. destruct ErfcxReciprocal.one_ok as[Fo Bo].
  unfold table_reduce64.
  rewrite (Binary.Bcompare_correct 53 1024 h ErfcxReciprocal.one F Fo),Bo.
  destruct(Rcompare_spec(B h)1)as[Low|Equal|High].
  - pose proof(table_uniform_ieee h F ltac:(split;lra))as Reduction.
    destruct(table_uniform64 h)as[[i c]r];cbv zeta in Reduction.
    destruct Reduction as[I [Fc [Fr [Center [Exact [Radius _]]]]]].
    split;[lia|]. split;[exact Fc|]. split.
    + rewrite accurate_uniform_center by exact I;exact Center.
    + apply Rabs_le_inv in Radius;split;[split;lra|].
      replace(B h-B c)with(B r)by lra;apply Rabs_le;split;lra.
  - apply normal_table_binade_small;[exact F|split;lra].
  - apply normal_table_binade_small;[exact F|split;lra].
Qed.

Theorem normal_extended_small_cell_radius x h : valid x -> /4<=qval x<=16 ->
  finite h -> /4<=B h<8 -> Rabs(qval x-B h)<=bpow radix2 (-48) ->
  let '(i,c,r,e):=table_reduce64 h in
  (0<=i<177)%Z /\ finite c /\ B c=accurate_center(Z.to_nat i) /\
  Rabs(qval(normal_q_erfcx_residual x c))<=/8.
Proof.
  intros X Range Fh H Near.
  pose proof(normal_table_reduce_small h Fh H)as Reduction.
  destruct(table_reduce64 h)as[[[i c]r]e];cbv zeta in Reduction.
  destruct Reduction as[I [Fc [Center [Cb Radius]]]].
  split;[exact I|]. split;[exact Fc|]. split;[exact Center|].
  apply normal_extended_residual_radius;try assumption;[split;lra|].
  replace(qval x-B c)with((qval x-B h)+(B h-B c))by ring.
  eapply Rle_trans;[apply Rabs_triang|].
  assert (Budget : bpow radix2 (-48)+/16<=/8)by(interval with(i_prec 80));lra.
Qed.

Definition normal_q_erfcx_small_table x :=
  let '(i,c,r,e):=table_reduce64(Q256.to_f64 x) in
  normal_q_erfcx_taylor_at x c (Z.to_nat i).

Theorem normal_q_erfcx_small_table_error x : valid x -> /4<=qval x<=16 ->
  B(Q256.to_f64 x)<8 ->
  valid(normal_q_erfcx_small_table x) /\
  Rabs(qval(normal_q_erfcx_small_table x)-gaussian_erfcx(qval x))<=bpow radix2 (-123).
Proof.
  intros X Range Small.
  destruct(normal_table_input_round x X Range)as[Fh [H [Value Difference]]].
  assert (Near : Rabs(qval x-B(Q256.to_f64 x))<=bpow radix2 (-48)).
  { rewrite Rabs_minus_sym;eapply Rle_trans;[exact Difference|apply bpow_le;lia]. }
  pose proof(normal_extended_small_cell_radius x _ X Range Fh ltac:(split;lra) Near)as Reduction.
  unfold normal_q_erfcx_small_table.
  destruct(table_reduce64(Q256.to_f64 x))as[[[i c]r]e];cbv zeta in Reduction.
  destruct Reduction as[I [Fc [Center Radius]]].
  apply normal_q_erfcx_taylor_at_error;try assumption;lia.
Qed.

