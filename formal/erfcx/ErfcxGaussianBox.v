(** Fixed-point interval replay of the Gaussian polynomial. Every division
    is outward rounded; the checker uses only bounded-size binary integers. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
Require Import ErfcxGaussianSeries.
Open Scope R_scope.

Lemma integer_division_bounds a b : (0<b)%Z ->
  IZR(a/b)<=IZR a/IZR b<IZR(a/b)+1.
Proof.
  intros B. pose proof(Z.div_mod a b ltac:(lia)) as Eq.
  pose proof(Z.mod_pos_bound a b B) as Rem.
  apply (f_equal IZR) in Eq. rewrite plus_IZR,mult_IZR in Eq.
  assert (Pos : 0<IZR b) by (apply IZR_lt; exact B).
  assert (Low : 0<=IZR(a mod b)) by (apply IZR_le; lia).
  assert (High : IZR(a mod b)<IZR b) by (apply IZR_lt; lia).
  split; apply (Rmult_le_reg_r (IZR b)) || apply (Rmult_lt_reg_r (IZR b));
    try exact Pos; replace (IZR a/IZR b*IZR b) with (IZR a) by (field; lra); nra.
Qed.

Record gaussian_box := box { term_lo : Z; term_hi : Z; sum_lo : Z; sum_hi : Z }.
Definition ratio_num cn n := (cn*cn*Z.of_nat(S(2*n)))%Z.
Definition ratio_den cd n := (cd*cd*Z.of_nat(S n)*Z.of_nat(S(2*S n)))%Z.
Definition box_step cn cd n b :=
  let a:=ratio_num cn n in let d:=ratio_den cd n in
  let lo:=(-((term_hi b*a)/d)-1)%Z in
  let hi:=(-((term_lo b*a)/d))%Z in
  box lo hi (sum_lo b+lo) (sum_hi b+hi).
Fixpoint gaussian_boxes cn cd scale n :=
  match n with O => box scale scale scale scale
  | S k => box_step cn cd k (gaussian_boxes cn cd scale k) end.
Definition contains scale lo hi value := IZR lo<=IZR scale*value<=IZR hi.

Lemma ratio_signs cn cd n : (0<cd)%Z ->
  (0<=ratio_num cn n /\ 0<ratio_den cd n)%Z.
Proof.
  intros D. unfold ratio_num,ratio_den.
  assert (0<Z.of_nat(S n))%Z by lia.
  assert (0<Z.of_nat(S(2*n)))%Z by lia.
  assert (0<Z.of_nat(S(2*S n)))%Z by lia. nia.
Qed.
Lemma ratio_real cn cd n : (0<cd)%Z ->
  IZR(ratio_num cn n)/IZR(ratio_den cd n)=
    (IZR cn/IZR cd)*(IZR cn/IZR cd)*
      (INR(S(2*n))/(INR(S n)*INR(S(2*S n)))).
Proof.
  intros D. unfold ratio_num,ratio_den. rewrite !mult_IZR,<- !INR_IZR_INZ.
  assert (Dz : IZR cd<>0) by (apply not_0_IZR; lia).
  assert (N : INR(S n)<>0) by (apply not_0_INR; lia).
  assert (K : INR(S(2*S n))<>0) by (apply not_0_INR; lia).
  field; auto.
Qed.

Lemma box_step_contains cn cd scale n b t s : (0<cd)%Z ->
  contains scale (term_lo b) (term_hi b) t ->
  contains scale (sum_lo b) (sum_hi b) s ->
  let next:= -(IZR(ratio_num cn n)/IZR(ratio_den cd n))*t in
  contains scale (term_lo(box_step cn cd n b)) (term_hi(box_step cn cd n b)) next /\
  contains scale (sum_lo(box_step cn cd n b)) (sum_hi(box_step cn cd n b)) (s+next).
Proof.
  intros Cd Term Sum. cbn zeta. destruct (ratio_signs cn cd n Cd) as [A D].
  pose proof (integer_division_bounds (term_hi b*ratio_num cn n) (ratio_den cd n) D) as Hi.
  pose proof (integer_division_bounds (term_lo b*ratio_num cn n) (ratio_den cd n) D) as Lo.
  rewrite mult_IZR in Hi,Lo.
  assert (Pos : 0<IZR(ratio_den cd n)) by (apply IZR_lt; exact D).
  assert (Nonneg : 0<=IZR(ratio_num cn n)/IZR(ratio_den cd n)).
  { unfold Rdiv. apply Rmult_le_pos; [apply IZR_le; exact A|apply Rlt_le,Rinv_0_lt_compat; exact Pos]. }
  assert (T : contains scale
    (-((term_hi b*ratio_num cn n)/ratio_den cd n)-1)
    (-((term_lo b*ratio_num cn n)/ratio_den cd n))
    (-(IZR(ratio_num cn n)/IZR(ratio_den cd n))*t)).
  { unfold contains in Term |- *. rewrite minus_IZR,!opp_IZR.
    replace (IZR(term_hi b)*IZR(ratio_num cn n)/IZR(ratio_den cd n)) with
      (IZR(term_hi b)*(IZR(ratio_num cn n)/IZR(ratio_den cd n))) in Hi by (unfold Rdiv; ring).
    replace (IZR(term_lo b)*IZR(ratio_num cn n)/IZR(ratio_den cd n)) with
      (IZR(term_lo b)*(IZR(ratio_num cn n)/IZR(ratio_den cd n))) in Lo by (unfold Rdiv; ring).
    split; nra. }
  split; [exact T|].
  unfold box_step; cbn [sum_lo sum_hi]. unfold contains in Sum,T |- *.
  rewrite !plus_IZR. nra.
Qed.

Theorem gaussian_boxes_correct cn cd scale n : (0<cd)%Z ->
  contains scale (term_lo(gaussian_boxes cn cd scale n))
    (term_hi(gaussian_boxes cn cd scale n)) (gaussian_term n (IZR cn/IZR cd)) /\
  contains scale (sum_lo(gaussian_boxes cn cd scale n))
    (sum_hi(gaussian_boxes cn cd scale n)) (gaussian_sum n (IZR cn/IZR cd)).
Proof.
  intros Cd. induction n as [|n [Term Sum]].
  - split; change (IZR scale<=IZR scale*(1/(1*1))<=IZR scale); split; right; field.
  - pose proof (box_step_contains cn cd scale n (gaussian_boxes cn cd scale n)
      (gaussian_term n (IZR cn/IZR cd)) (gaussian_sum n (IZR cn/IZR cd)) Cd Term Sum) as Step.
    cbn zeta in Step. rewrite ratio_real in Step by exact Cd.
    assert (Next : - (IZR cn/IZR cd*(IZR cn/IZR cd)*
      (INR(S(2*n))/(INR(S n)*INR(S(2*S n)))))*gaussian_term n (IZR cn/IZR cd)=
      gaussian_term (S n) (IZR cn/IZR cd)).
    { rewrite gaussian_term_step. ring. }
    rewrite Next in Step. exact Step.
Qed.

Lemma contains_divide scale lo hi value : (0<scale)%Z -> contains scale lo hi value ->
  IZR lo/IZR scale<=value<=IZR hi/IZR scale.
Proof.
  intros S [Lo Hi]. assert (Pos : 0<IZR scale) by (apply IZR_lt; exact S).
  split; apply (Rmult_le_reg_r (IZR scale)); try exact Pos;
    replace (IZR lo/IZR scale*IZR scale) with (IZR lo) by (field; lra);
    replace (IZR hi/IZR scale*IZR scale) with (IZR hi) by (field; lra); nra.
Qed.
