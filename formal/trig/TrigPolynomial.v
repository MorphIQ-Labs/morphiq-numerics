(** Analytic tails against the actual fast polynomial coefficients. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Binary64 Require Import IEEE64.
From Interval Require Import Tactic.
From Coq Require Import Rtrigo_calc.
Require Import TrigTables TrigError Expm1Series AsinFacts.
Open Scope R_scope.
Definition trig_ps z := B trig_s0+z*(B trig_s1+z*B trig_s2).
Definition trig_pc z := B trig_c0+z*(B trig_c1+z*B trig_c2).
Definition sin_tail_hi z := -/6+z*(/120+z*(-/5040+z*/362880)).
Definition sin_tail_lo z := sin_tail_hi z-z^4/39916800.
Definition cos_tail_hi z := /24+z*(-/720+z*(/40320+z*(-/3628800+z*/479001600))).
Definition cos_tail_lo z := cos_tail_hi z-z^5/87178291200.
Definition trig_poly_error := 518/2^63.
Lemma sin_tail_polynomial_bound z : 0<=z<=0.0078126^2 ->
 Rabs(sin_tail_lo z-trig_ps z)<=trig_poly_error*Rabs(trig_ps z) /\
 Rabs(sin_tail_hi z-trig_ps z)<=trig_poly_error*Rabs(trig_ps z).
Proof.
 intro Z. assert (Neg:trig_ps z<0).
 { unfold trig_ps. rewrite trig_s0_val,trig_s1_val,trig_s2_val. interval. }
 rewrite (Rabs_left _ Neg). unfold sin_tail_lo,sin_tail_hi,trig_ps,trig_poly_error.
 rewrite trig_s0_val,trig_s1_val,trig_s2_val.
 split; apply Rabs_le; split;
 match goal with |- ?a <= ?b =>
  assert (Bound:a-b<=0) by (interval with (i_taylor z,i_degree 6,i_bisect z,i_prec 180,i_depth 8)); lra
 end.
Qed.
Lemma cos_tail_polynomial_bound z : 0<=z<=0.0078126^2 ->
 Rabs(cos_tail_lo z-trig_pc z)<=trig_poly_error*Rabs(trig_pc z) /\
 Rabs(cos_tail_hi z-trig_pc z)<=trig_poly_error*Rabs(trig_pc z).
Proof.
 intro Z. assert (Pos:0<=trig_pc z).
 { unfold trig_pc. rewrite trig_c0_val,trig_c1_val,trig_c2_val. interval. }
 rewrite (Rabs_pos_eq _ Pos). unfold cos_tail_lo,cos_tail_hi,trig_pc,trig_poly_error.
 rewrite trig_c0_val,trig_c1_val,trig_c2_val.
 split; apply Rabs_le; split;
 match goal with |- ?a <= ?b =>
  assert (Bound:a-b<=0) by (interval with (i_taylor z,i_degree 6,i_bisect z,i_prec 180,i_depth 8)); lra
 end.
Qed.

Lemma sin_tail_enclosure t : 0<=t<=0.0078126 ->
 t+t^3*sin_tail_lo (t*t)<=sin t<=t+t^3*sin_tail_hi (t*t).
Proof.
 intros T. pose proof PI_RGT_0 as Pi.
 assert (Range:t<=PI) by (pose proof one_le_half_pi; lra).
 destruct (sin_bound t 2 ltac:(lra) Range) as [Lower _].
 destruct (sin_bound t 1 ltac:(lra) Range) as [_ Upper].
 split.
 - replace (t+t^3*sin_tail_lo (t*t)) with (sin_approx t 5); [exact Lower|].
   unfold sin_approx. cbn [sum_f_R0]. unfold sin_term,sin_tail_lo,sin_tail_hi.
   cbn [Nat.mul Nat.add]. factorial_reals. field.
 - replace (t+t^3*sin_tail_hi (t*t)) with (sin_approx t 4); [exact Upper|].
   unfold sin_approx. cbn [sum_f_R0]. unfold sin_term,sin_tail_hi.
   cbn [Nat.mul Nat.add]. factorial_reals. field.
Qed.
Lemma cos_tail_enclosure t : Rabs t<=0.0078126 ->
 1-t*t/2+t^4*cos_tail_lo (t*t)<=cos t<=1-t*t/2+t^4*cos_tail_hi (t*t).
Proof.
 intro T. apply abs_le_inv in T.
 assert (L:-PI/2<=t) by (pose proof one_le_half_pi; lra).
 assert (U:t<=PI/2) by (pose proof one_le_half_pi; lra).
 destruct (cos_bound t 3 L U) as [Lower _].
 destruct (cos_bound t 2 L U) as [_ Upper].
 split.
 - replace (1-t*t/2+t^4*cos_tail_lo (t*t)) with (cos_approx t 7); [exact Lower|].
   unfold cos_approx. cbn [sum_f_R0]. unfold cos_term,cos_tail_lo,cos_tail_hi.
   cbn [Nat.mul Nat.add]. factorial_reals. field.
 - replace (1-t*t/2+t^4*cos_tail_hi (t*t)) with (cos_approx t 6); [exact Upper|].
   unfold cos_approx. cbn [sum_f_R0]. unfold cos_term,cos_tail_hi.
   cbn [Nat.mul Nat.add]. factorial_reals. field.
Qed.

Lemma trig_sin_polynomial_error_pos t : 0<=t<=0.0078126 ->
 Rabs(sin t-(t+t^3*trig_ps (t*t)))<=trig_poly_error*Rabs(t^3*trig_ps (t*t)).
Proof.
 intro T. pose proof (sin_tail_enclosure t T) as Range.
 destruct (sin_tail_polynomial_bound (t*t) ltac:(nra)) as [Lo Hi].
 exact (trig_scaled_enclosure (sin t) t (t^3) (sin_tail_lo(t*t)) (sin_tail_hi(t*t))
   (trig_ps(t*t)) trig_poly_error ltac:(apply pow_le; lra) Range Lo Hi).
Qed.
Lemma trig_cos_polynomial_error t : Rabs t<=0.0078126 ->
 Rabs(cos t-(1-t*t/2+t^4*trig_pc (t*t)))<=trig_poly_error*Rabs(t^4*trig_pc (t*t)).
Proof.
 intro T. pose proof (cos_tail_enclosure t T) as Range.
 pose proof (abs_le_inv _ _ T) as A.
 destruct (cos_tail_polynomial_bound (t*t) ltac:(nra)) as [Lo Hi].
 exact (trig_scaled_enclosure (cos t) (1-t*t/2) (t^4) (cos_tail_lo(t*t)) (cos_tail_hi(t*t))
   (trig_pc(t*t)) trig_poly_error ltac:(pose proof (Rle_0_sqr (t*t)); unfold Rsqr in *; nra) Range Lo Hi).
Qed.
Lemma trig_sin_polynomial_error t : Rabs t<=0.0078126 ->
 Rabs(sin t-(t+t^3*trig_ps (t*t)))<=trig_poly_error*Rabs(t^3*trig_ps (t*t)).
Proof.
 intro T. destruct (Rle_lt_dec 0 t) as [Pos|Neg].
 - apply trig_sin_polynomial_error_pos. rewrite (Rabs_pos_eq _ Pos) in T; lra.
 - rewrite (Rabs_left _ Neg) in T.
   pose proof (trig_sin_polynomial_error_pos (-t) ltac:(lra)) as Error.
   rewrite sin_neg in Error. replace ((-t)*(-t)) with (t*t) in Error by ring.
   replace ((-t)^3) with (-(t^3)) in Error by ring.
   replace (-sin t-(-t+ -(t^3)*trig_ps(t*t))) with (-(sin t-(t+t^3*trig_ps(t*t)))) in Error by ring.
   replace (-(t^3)*trig_ps(t*t)) with (-(t^3*trig_ps(t*t))) in Error by ring.
   rewrite !Rabs_Ropp in Error; exact Error.
Qed.

Lemma trig_sin_polynomial_model t : Rabs t<=0.0078126 ->
 exists al, Rabs al<=trig_poly_error /\
 sin t=t+t^3*trig_ps(t*t)*(1+al).
Proof.
 intro T. pose proof (trig_sin_polynomial_error t T) as Error.
 replace (sin t-(t+t^3*trig_ps(t*t))) with ((sin t-t)-t^3*trig_ps(t*t)) in Error by ring.
 destruct (trig_relative_factor (sin t-t) (t^3*trig_ps(t*t)) trig_poly_error
   ltac:(unfold trig_poly_error; interval) Error) as [al [A Value]].
 exists al. split; [exact A|lra].
Qed.
Lemma trig_cos_polynomial_model t : Rabs t<=0.0078126 ->
 exists al, Rabs al<=trig_poly_error /\
 cos t=1-t*t/2+t^4*trig_pc(t*t)*(1+al).
Proof.
 intro T. pose proof (trig_cos_polynomial_error t T) as Error.
 replace (cos t-(1-t*t/2+t^4*trig_pc(t*t))) with
   ((cos t-(1-t*t/2))-t^4*trig_pc(t*t)) in Error by ring.
 destruct (trig_relative_factor (cos t-(1-t*t/2)) (t^4*trig_pc(t*t)) trig_poly_error
   ltac:(unfold trig_poly_error; interval) Error) as [al [A Value]].
 exists al. split; [exact A|lra].
Qed.
