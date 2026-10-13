(** The reflected subtraction and its final normalization, with explicit
    approximation hypotheses and IEEE scaling including gradual underflow. *)
From Coq Require Import Reals ZArith Lia Lra Psatz Classical.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Mul IEEE64Eft RoundingConstant.
Require Import ExpStageReduction StageGappa ErfcxReciprocal ErfcxReflectionScale.
Require erfcx_reflection_composition.
Require ErfcxReflectionExp ErfcxTableEntry.
Open Scope R_scope.

Lemma reflection_subtract_model eh el gh gl sc ds de dg :
  0.999 <= rn eh <= 2.001 -> Rabs (rn el) <= bpow radix2 (-52) ->
  0 <= rn gh <= 0.617 -> Rabs (rn gl) <= bpow radix2 (-53) ->
  0 <= sc <= /2 -> Rabs ds <= bpow radix2 (-800) ->
  Rabs de <= IZR 209 * bpow radix2 (-78) -> Rabs dg <= bpow radix2 (-67) ->
  let dh := rn (rn eh - rn gh * sc) in
  let dl := rn eh - rn gh * sc - dh in
  let l := rn (dl + rn (rn el - (rn gl * sc + ds))) in
  let F := (rn eh + rn el - de) - (rn gh + rn gl - dg)*sc in
  Rabs ((dh+l-F)/F) <= bpow radix2 (-67) /\
  0.69 <= dh <= 2.01 /\ Rabs l <= bpow radix2 (-50).
Proof.
  intros E L G U S Ds De Dg. cbv zeta.
  apply Rabs_le_inv in L. apply Rabs_le_inv in U.
  apply Rabs_le_inv in Ds. apply Rabs_le_inv in De. apply Rabs_le_inv in Dg.
  split; [apply Rabs_le | split; [ | apply Rabs_le]];
    erfcx_goal (erfcx_reflection_composition.l1 eh gh sc el gl ds de dg).
Qed.

Definition reflection_subtract64 eh el gh gl k : f64 * f64 :=
  let sc := reflection_scale64 k in
  let '(dh,dl) := two_sum64 eh (fneg (fmul gh sc)) in
  fast_two_sum64 dh (fadd dl (fsub el (fmul gl sc))).

Theorem reflection_subtract_ieee eh el gh gl k de dg :
  finite eh -> finite el -> finite gh -> finite gl ->
  0.999 <= B eh <= 2.001 -> Rabs (B el) <= bpow radix2 (-52) ->
  /32 <= B gh <= 0.617 -> Rabs (B gl) <= bpow radix2 (-53) -> (0 <= k <= 104)%Z ->
  Rabs de <= IZR 209 * bpow radix2 (-78) -> Rabs dg <= bpow radix2 (-67) ->
  let '(h,l) := reflection_subtract64 eh el gh gl k in
  let F := (B eh + B el - de) - (B gh + B gl - dg)*bpow radix2 (-k-1) in
  finite h /\ finite l /\ B h = rndF (B h+B l) /\
  Rabs ((B h+B l-F)/F) <= bpow radix2 (-67).
Proof.
  intros Feh Fel Fgh Fgl E L G U K De Dg. unfold reflection_subtract64.
  set (sc := reflection_scale64 k).
  destruct (reflection_scale_ok k K) as [Fsc [Bsc S]]. fold sc in Fsc, Bsc, S.
  assert (Gh : Rabs (B gh) <= 1) by (rewrite Rabs_pos_eq; lra).
  assert (Gl : Rabs (B gl) <= 1)
    by (apply Rle_trans with (1 := U); change 1 with (bpow radix2 0); apply bpow_le; lia).
  destruct (reflection_scaled_word_ieee gh k Fgh Gh K) as [Fph [Bph [Ph [_ Exact]]]].
  fold sc in Fph, Bph, Ph, Exact.
  assert (Ghbig : bpow radix2 (-746) <= Rabs (B gh)).
  { apply Rle_trans with (bpow radix2 (-5)); [apply bpow_le; lia | ].
    change (bpow radix2 (-5)) with (/32). rewrite Rabs_pos_eq; lra. }
  specialize (Exact Ghbig).
  destruct (reflection_scaled_word_ieee gl k Fgl Gl K) as [Fpl [Bpl [Pl [Low _]]]].
  fold sc in Fpl, Bpl, Pl, Low.
  assert (Nb : forall v, B (fneg v) = - B v) by (intros v; apply B2R_Bopp).
  assert (Fn : finite (fneg (fmul gh sc)))
    by (unfold fneg, b64_opp; rewrite is_finite_Bopp; exact Fph).
  assert (Bn : B (fneg (fmul gh sc)) = -(B gh*bpow radix2 (-k-1)))
    by (rewrite Nb, Exact; reflexivity).
  assert (Eh : Rabs (B eh) <= bpow radix2 1020).
  { rewrite Rabs_pos_eq by lra. apply Rle_trans with (bpow radix2 2);
      [change (bpow radix2 2) with 4; lra | apply bpow_le; lia]. }
  assert (Nh : Rabs (B (fneg (fmul gh sc))) <= bpow radix2 1020).
  { rewrite Nb, Rabs_Ropp. apply Rle_trans with (1 := Ph).
    change 1 with (bpow radix2 0). apply bpow_le. lia. }
  pose proof (two_sum_ieee eh (fneg (fmul gh sc)) Feh Fn Eh Nh) as TS.
  revert TS. generalize (two_sum64 eh (fneg (fmul gh sc))). intros [dh dl] TS.
  destruct TS as [Fdh [Fdl [Bdh Sum]]]. rewrite Bn, rndF_rn in Bdh.
  change (B dh = rn (B eh - B gh*bpow radix2 (-k-1))) in Bdh.
  assert (Bdl : B dl = B eh - B gh*bpow radix2 (-k-1) - B dh) by (rewrite Bn in Sum; lra).
  set (ds := B (fmul gl sc) - B gl*bpow radix2 (-k-1)).
  pose proof (reflection_subtract_model (B eh) (B el) (B gh) (B gl)
    (bpow radix2 (-k-1)) ds de dg) as Model.
  assert (RN : forall v : f64, rn (B v) = B v)
    by (intros v; apply round_generic; [exact _ | apply B_fmt]).
  repeat rewrite RN in Model.
  specialize (Model E L ltac:(lra) U ltac:(rewrite <- Bsc; lra) Low De Dg).
  cbv zeta in Model. rewrite <- Bdh in Model.
  replace (B gl*bpow radix2 (-k-1)+ds) with (B (fmul gl sc)) in Model by (unfold ds; ring).
  rewrite <- Bdl in Model.
  assert (El : Rabs (B el) <= 1)
    by (apply Rle_trans with (1 := L); change 1 with (bpow radix2 0); apply bpow_le; lia).
  destruct (fsub16 el (fmul gl sc) Fel Fpl) as [Fl0 Bl0].
  { unfold Rminus. apply Rle_trans with (1 := Rabs_triang _ _). rewrite Rabs_Ropp. lra. }
  rewrite rndF_rn in Bl0. rewrite <- Bl0 in Model.
  assert (L0 : Rabs (B (fsub el (fmul gl sc))) <= 2).
  { rewrite Bl0. apply abs_round_le_generic; [exact _ | exact _ | | ].
    - change 2 with (bpow radix2 1). apply generic_format_bpow. unfold FLT_exp, emin, prec. lia.
    - unfold Rminus. apply Rle_trans with (1 := Rabs_triang _ _). rewrite Rabs_Ropp. lra. }
  assert (Dl : Rabs (B dl) <= 1).
  { assert (A : Rabs (B eh-B gh*bpow radix2 (-k-1)) <= bpow radix2 2).
    { rewrite <- Bsc. change (bpow radix2 2) with 4.
      pose proof (Rabs_le_inv _ _ Ph) as Phr. rewrite Exact, <- Bsc in Phr.
      apply Rabs_le; lra. }
    pose proof (rnd_err_below _ 2 ltac:(lia) A) as Round.
    rewrite rndF_rn, <- Bdh in Round. rewrite Bdl, <- Rabs_Ropp, Ropp_minus_distr.
    apply Rle_trans with (1 := Round). change 1 with (bpow radix2 0). apply bpow_le. lia. }
  destruct (fadd16 dl (fsub el (fmul gl sc)) Fdl Fl0) as [Fr Br].
  { apply Rle_trans with (1 := Rabs_triang _ _). lra. }
  rewrite rndF_rn in Br. rewrite <- Br in Model.
  destruct Model as [Err [Dh Rest]].
  set (rest := fadd dl (fsub el (fmul gl sc))) in *.
  assert (Dhbig : Rabs (B dh) <= bpow radix2 1021).
  { rewrite Rabs_pos_eq by lra. apply Rle_trans with (bpow radix2 2);
      [change (bpow radix2 2) with 4; lra | apply bpow_le; lia]. }
  assert (Rbig : Rabs (B rest) <= bpow radix2 1021)
    by (apply Rle_trans with (1 := Rest); apply bpow_le; lia).
  assert (Dom : Rabs (B rest) <= Rabs (B dh)).
  { change (bpow radix2 (-50)) with (/1125899906842624) in Rest.
    rewrite (Rabs_pos_eq (B dh)); lra. }
  pose proof (fast_two_sum_ieee dh rest Fdh Fr Dhbig Rbig (or_intror (or_introl Dom))) as FS.
  revert FS. generalize (fast_two_sum64 dh rest). intros [h l] FS.
  destruct FS as [Fh [Fl [High Total]]]. cbv zeta.
  split; [exact Fh | split; [exact Fl | split]].
  - rewrite Total. exact High.
  - rewrite Total. exact Err.
Qed.

(** The operation sequence of erfcx::n_eval. *)
Definition reflection_value64 x : f64 * f64 * Z :=
  let '(s,se) := two_prod64 x x in
  let '(eh,el,k) := ErfcxReflectionExp.reflection_exp64 s se in
  if (104 <? k)%Z then (eh,el,(k+1)%Z) else
  let '(gh,gl) := ErfcxTableEntry.table_eval64 (fneg x) in
  let '(h,l) := reflection_subtract64 eh el gh gl k in
  (h,l,(k+1)%Z).
