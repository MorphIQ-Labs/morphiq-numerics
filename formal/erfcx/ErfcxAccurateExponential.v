(** The complete Q256 exponential factor used by accurate negative reflection. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Binary64 Require Import Binary64Add IEEE64.
From Q Require Import Q256 Q256Real.
Require Import StageGappa ErfcxAccurateTranscendentals ErfcxAccurateHorner
  ErfcxAccurateExpSeries ErfcxAccurateReduction ErfcxAccurateIndex.
Require ExpFast.
Open Scope R_scope.

Lemma accurate_exp_perturbation d : Rabs d<=bpow radix2 (-241) ->
  Rabs (exp d-1)<=bpow radix2 (-240).
Proof.
  intros D. apply Rabs_le_inv in D. bpow_num_all.
  apply Rabs_le; split; interval with (i_prec 400).
Qed.

Lemma q_exp_horner_target r target : valid r -> Rabs (qval r)<=/256 ->
  Rabs target<=/256 -> Rabs (qval r-target)<=bpow radix2 (-241) ->
  valid (q_exp_horner r 24) /\ exists e, Rabs e<=bpow radix2 (-239) /\
    qval (q_exp_horner r 24)=exp target*(1+e).
Proof.
  intros R Range T Difference. destruct (q_exp_horner_exp r R Range) as [Q Error].
  pose proof (accurate_exp_perturbation _ Difference) as Perturbation.
  assert (ExpRange : 0.99<=exp target<=1.01).
  { apply Rabs_le_inv in T. split; interval with (i_prec 80). }
  assert (Split : exp (qval r)=exp target*exp (qval r-target)).
  { rewrite <- exp_plus. f_equal. ring. }
  split; [exact Q | ]. exists (qval (q_exp_horner r 24)/exp target-1). split.
  - apply Rabs_le_inv in Error,Perturbation. rewrite Split in Error.
    assert (Bound : -bpow radix2 (-239)*exp target<=qval (q_exp_horner r 24)-exp target<=
      bpow radix2 (-239)*exp target).
    { bpow_num_all. split; nra. }
    assert (Id : (qval (q_exp_horner r 24)/exp target-1)*exp target=
      qval (q_exp_horner r 24)-exp target) by (field; lra).
    apply Rabs_le. split; nra.
  - field; lra.
Qed.

Lemma accurate_exp_product_error e t m :
  Rabs e<=bpow radix2 (-239) -> Rabs t<=bpow radix2 (-255) -> Rabs m<=bpow radix2 (-255) ->
  Rabs ((1+t)*(1+e)*(1+m)-1)<=bpow radix2 (-238).
Proof.
  intros E T M. apply Rabs_le_inv in E,T,M.
  replace ((1+t)*(1+e)*(1+m)-1) with (t+(1+t)*(e+(1+e)*m)) by ring.
  bpow_num_all. apply Rabs_le; split; interval with (i_prec 300).
Qed.

Definition q_exp_scaled r j k := mul_pow2 (mul (q_exp_table j) (q_exp_horner r 24)) (k+1).

Theorem q_exp_scaled_error r target j k : valid r -> Rabs (qval r)<=/256 ->
  Rabs target<=/256 -> Rabs (qval r-target)<=bpow radix2 (-241) -> (j<128)%nat ->
  valid (q_exp_scaled r j k) /\ exists e, Rabs e<=bpow radix2 (-238) /\
  qval (q_exp_scaled r j k)=2*exp (IZR (128*k+Z.of_nat j)*(ln 2/128)+target)*(1+e).
Proof.
  intros R Range T Difference J.
  destruct (q_exp_horner_target r target R Range T Difference) as [H [eh [Eh Hvalue]]].
  destruct (q_exp_table_ok j J) as [Table Terror].
  set (et := qval (q_exp_table j)/exp (INR j*ln 2/128)-1) in *.
  assert (Tablevalue : qval (q_exp_table j)=exp (INR j*ln 2/128)*(1+et)).
  { unfold et. field. apply Rgt_not_eq,exp_pos. }
  destruct (mul_relative _ _ Table H) as [P [m [M Pvalue]]].
  destruct (mul_pow2_any _ (k+1) P) as [Result Value].
  split; [exact Result | ]. exists ((1+et)*(1+eh)*(1+m)-1). split.
  - apply accurate_exp_product_error; assumption.
  - unfold q_exp_scaled. rewrite Value,Pvalue,Tablevalue,Hvalue,ExpFast.exp_split,bpow_plus.
    change (bpow radix2 1) with 2. ring.
Qed.

Definition q_reflection_exponential s se :=
  let ni := accurate_index s in
  q_exp_scaled (accurate_residual s se (accurate_n s)) (Z.to_nat (ni mod 128)) (ni/128).

Theorem q_reflection_exponential_error s se : finite s -> finite se ->
  /4<=B s<=709.79 -> Rabs (B se)<=bpow radix2 (-44) ->
  valid (q_reflection_exponential s se) /\ exists e, Rabs e<=bpow radix2 (-238) /\
  qval (q_reflection_exponential s se)=2*exp (B s+B se)*(1+e).
Proof.
  intros Fs Fse S Se. destruct (accurate_index_ok s Fs S) as [N [Nvalue [Ni Reduced]]].
  destruct (accurate_residual_error s se (accurate_n s) (accurate_index s) Fs Fse N
    ltac:(apply Rabs_le; lra) Se Nvalue Ni) as [R Error].
  set (target := B s+B se-IZR (accurate_index s)*(ln 2/128)) in *.
  assert (T : Rabs target<=/256).
  { unfold target. replace (B s+B se-IZR (accurate_index s)*(ln 2/128)) with
      ((B s-IZR (accurate_index s)*(ln 2/128))+B se) by ring.
    eapply Rle_trans; [apply Rabs_triang | ]. bpow_num_all. lra. }
  assert (Range : Rabs (qval (accurate_residual s se (accurate_n s)))<=/256).
  { assert (Tighter : Rabs target<=0.002709).
    { unfold target. replace (B s+B se-IZR (accurate_index s)*(ln 2/128)) with
        ((B s-IZR (accurate_index s)*(ln 2/128))+B se) by ring.
      eapply Rle_trans; [apply Rabs_triang | ]. bpow_num_all. lra. }
    apply Rabs_le_inv in Tighter,Error. apply Rabs_le. bpow_num_all. lra. }
  set (ni := accurate_index s) in *.
  assert (J : (0<=ni mod 128<128)%Z) by (apply Z.mod_pos_bound; lia).
  assert (Index : (ni=128*(ni/128)+Z.of_nat (Z.to_nat (ni mod 128)))%Z).
  { rewrite Z2Nat.id by lia. pose proof (Z.div_mod ni 128 ltac:(lia)); lia. }
  destruct (q_exp_scaled_error _ target (Z.to_nat (ni mod 128)) (ni/128) R Range T Error
    ltac:(lia)) as [Result [e [E Value]]].
  unfold q_reflection_exponential. fold ni. split; [exact Result | ]. exists e.
  split; [exact E | ]. rewrite Value, <- Index. unfold target. fold ni.
  replace (IZR ni*(ln 2/128)+(B s+B se-IZR ni*(ln 2/128))) with (B s+B se) by ring.
  reflexivity.
Qed.

From Binary64 Require Import IEEE64Eft IEEE64Mul.
Require Import ErfcxReflectionSquare.
Definition q_reflection_big x :=
  let '(s,se) := two_prod64 x x in q_reflection_exponential s se.

Theorem q_reflection_big_error x : finite x -> B reflection_limit < B x < - /2 ->
  valid (q_reflection_big x) /\ exists e, Rabs e<=bpow radix2 (-238) /\
  qval (q_reflection_big x)=2*exp (B x*B x)*(1+e).
Proof.
  intros F X. pose proof (reflection_square_ieee x F X) as Square.
  unfold q_reflection_big. destruct (two_prod64 x x) as [s se].
  destruct Square as [S [Se [Exact [Srange Serange]]]].
  assert (Sbound : /4<=B s<=709.79).
  { pose proof reflection_limit_value as Limit.
    apply Rabs_le_inv in Serange. bpow_num_all. split; nra. }
  destruct (q_reflection_exponential_error s se S Se Sbound Serange) as [Q [e [E Value]]].
  split; [exact Q | ]. exists e. split; [exact E | rewrite <- Exact; exact Value].
Qed.
