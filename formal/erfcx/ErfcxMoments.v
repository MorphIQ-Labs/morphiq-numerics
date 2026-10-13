(** Exponential moments used to integrate the signed tail remainder. *)
From Coq Require Import Reals Lia Lra Psatz.
From Coquelicot Require Import Coquelicot.
Require Import Expm1Series.
Open Scope R_scope.

Definition exponential_moment n x := x^n*exp(-x).
Lemma exponential_moment_continuous n x : continuous (exponential_moment n) x.
Proof.
  unfold exponential_moment. apply (@ex_derive_continuous R_AbsRing R_CompleteNormedModule).
  eexists. auto_derive; trivial.
Qed.
Lemma exponential_moment_integrable n a b : ex_RInt (exponential_moment n) a b.
Proof.
  apply (@ex_RInt_continuous R_CompleteNormedModule). intros. apply exponential_moment_continuous.
Qed.

Fixpoint moment_primitive n x :=
  match n with
  | O => -exp(-x)
  | S m => -(x^S m*exp(-x))+INR(S m)*moment_primitive m x
  end.

Lemma moment_primitive_derivative n x :
  is_derive (moment_primitive n) x (exponential_moment n x).
Proof.
  induction n as [ | n IH].
  - unfold moment_primitive, exponential_moment. auto_derive; simpl; try trivial; ring.
  - change (is_derive (fun u => -(u^S n*exp(-u))+INR(S n)*moment_primitive n u)
      x (exponential_moment (S n) x)).
    assert (D : is_derive (fun u => -(u^S n*exp(-u))) x
      (x^S n*exp(-x)-INR(S n)*x^n*exp(-x))).
    { auto_derive; simpl; try trivial; ring. }
    unfold exponential_moment in *.
    pose proof (is_derive_scal (moment_primitive n) x (INR(S n))
      (x^n*exp(-x)) IH) as Scaled.
    pose proof (is_derive_plus _ _ x _ _ D Scaled) as Sum.
    change (is_derive (fun u => -(u^S n*exp(-u))+INR(S n)*moment_primitive n u) x
      ((x^S n*exp(-x)-INR(S n)*x^n*exp(-x))+INR(S n)*(x^n*exp(-x)))) in Sum.
    replace ((x^S n*exp(-x)-INR(S n)*x^n*exp(-x))+INR(S n)*(x^n*exp(-x)))
      with (x^S n*exp(-x)) in Sum by ring.
    exact Sum.
Qed.

Lemma moment_primitive_zero n : moment_primitive n 0= -INR(fact n).
Proof.
  induction n as [ | n IH].
  - change (-exp(-0)= -1). replace (-0) with 0 by ring. rewrite exp_0. reflexivity.
  - change (-(0^S n*exp(-0))+INR(S n)*moment_primitive n 0= -INR(fact(S n))).
    rewrite IH, INR_fact_succ. simpl pow. ring.
Qed.

Lemma moment_primitive_nonpositive n x : 0<=x -> moment_primitive n x<=0.
Proof.
  intros X. induction n as [ | n IH].
  - change (-exp(-x)<=0). pose proof (exp_pos (-x)); lra.
  - change (-(x^S n*exp(-x))+INR(S n)*moment_primitive n x<=0).
    pose proof (pow_le x (S n) X). pose proof (exp_pos (-x)). pose proof (pos_INR (S n)). nra.
Qed.

Theorem exponential_moment_integral n b :
  RInt (exponential_moment n) 0 b=moment_primitive n b+INR(fact n).
Proof.
  pose proof (is_RInt_derive (moment_primitive n) (exponential_moment n) 0 b
    ltac:(intros; apply moment_primitive_derivative)
    ltac:(intros; apply exponential_moment_continuous)) as Integral.
  apply is_RInt_unique in Integral. change (RInt (exponential_moment n) 0 b=
    moment_primitive n b-moment_primitive n 0) in Integral.
  rewrite moment_primitive_zero in Integral. lra.
Qed.

Lemma positive_exponential_series n x : 0<=x -> 0<=esum n x.
Proof.
  intros X. unfold esum. induction n as [ | n IH].
  - simpl. lra.
  - change (0<=sum_f_R0 (fun k => x^k/INR(fact k)) n+x^S n/INR(fact(S n))).
    assert (0<=x^S n/INR(fact(S n))).
    { apply Rdiv_le_0_compat; [apply pow_le; exact X | apply lt_0_INR, lt_O_fact]. } lra.
Qed.

Lemma exponential_single_term n x : 0<=x -> x^n/INR(fact n)<=exp x.
Proof.
  intros X. pose proof (exp_ge_taylor x n X) as Taylor.
  destruct n as [ | n].
  - exact Taylor.
  - change (esum n x+x^S n/INR(fact(S n))<=exp x) in Taylor.
    pose proof (positive_exponential_series n x X). lra.
Qed.

Lemma exponential_moment_bound n x : 0<x ->
  0<=exponential_moment n x<=INR(fact(S n))/x.
Proof.
  intros X. pose proof (exp_pos x) as Epos.
  pose proof (lt_0_INR _ (lt_O_fact (S n))) as Fpos.
  pose proof (exponential_single_term (S n) x ltac:(lra)) as Bound.
  assert (Pow : x^S n<=exp x*INR(fact(S n))).
  { apply Rmult_le_reg_r with (/INR(fact(S n))); [apply Rinv_0_lt_compat; exact Fpos | ].
    replace (exp x*INR(fact(S n))*/INR(fact(S n))) with (exp x) by (field; lra).
    exact Bound. }
  unfold exponential_moment. rewrite exp_Ropp. split.
  - apply Rmult_le_pos; [apply pow_le; lra | apply Rlt_le,Rinv_0_lt_compat; exact Epos].
  - apply Rmult_le_reg_r with (x*exp x); [nra | ].
    replace (x^n*/exp x*(x*exp x)) with (x^S n) by (simpl pow; field; lra).
    replace (INR(fact(S n))/x*(x*exp x)) with (exp x*INR(fact(S n))) by (field; lra).
    exact Pow.
Qed.

Theorem exponential_moment_limit n :
  is_lim_seq (fun k => exponential_moment n (INR k)) 0.
Proof.
  apply (is_lim_seq_le_le_loc (fun _ => 0) _ (fun k => INR(fact(S n))/INR k)).
  - exists 1%nat. intros k K. apply exponential_moment_bound. apply lt_0_INR. lia.
  - apply is_lim_seq_const.
  - apply (is_lim_seq_div _ _ (INR(fact(S n))) p_infty 0).
    + apply is_lim_seq_const.
    + apply is_lim_seq_INR.
    + discriminate.
    + unfold is_Rbar_div, is_Rbar_mult. simpl. rewrite Rmult_0_r. reflexivity.
Qed.


Theorem moment_primitive_limit n :
  is_lim_seq (fun k => moment_primitive n (INR k)) 0.
Proof.
  assert (Neg : forall m, is_lim_seq (fun k => -exponential_moment m (INR k)) 0).
  { intros m. pose proof (proj1 (is_lim_seq_opp _ 0) (exponential_moment_limit m)) as N.
    change (is_lim_seq (fun k => -exponential_moment m (INR k)) (-0)) in N.
    rewrite Ropp_0 in N. exact N. }
  induction n as [ | n IH].
  - eapply is_lim_seq_ext; [ | exact (Neg 0%nat)]. intros k.
    unfold exponential_moment. change (- (1*exp(-INR k))= -exp(-INR k)). ring.
  - change (is_lim_seq (fun k => -exponential_moment (S n) (INR k)+INR(S n)*moment_primitive n (INR k)) 0).
    replace 0 with (0+INR(S n)*0) by ring. apply is_lim_seq_plus'.
    + exact (Neg (S n)).
    + apply is_lim_seq_mult'; [apply is_lim_seq_const | exact IH].
Qed.

Theorem exponential_moment_integral_limit n :
  is_lim_seq (fun k => RInt (exponential_moment n) 0 (INR k)) (INR(fact n)).
Proof.
  eapply is_lim_seq_ext.
  - intros k. symmetry. apply exponential_moment_integral.
  - pose proof (is_lim_seq_plus' (fun k => moment_primitive n (INR k))
      (fun _ => INR(fact n)) 0 (INR(fact n)) (moment_primitive_limit n)
      (is_lim_seq_const (INR(fact n)))) as Limit.
    rewrite Rplus_0_l in Limit. exact Limit.
Qed.
