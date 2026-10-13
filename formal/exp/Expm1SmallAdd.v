(** A scalar as the left operand of the existing double-word addition.
    Its zero low word makes the last renormalization an identity. *)
From Coq Require Import Reals ZArith Lia Lra.
From Flocq Require Import Core.
From Double Require Import DWPlus.
From Binary64 Require Import Binary64Add.
Open Scope R_scope.
Lemma em_two_sum_value a b : fmtF a -> fmtF b ->
 two_sum a b = (rndF (a+b), a+b-rndF (a+b)).
Proof.
 intros Fa Fb. rewrite two_sum_eq by assumption.
 pose proof (@TwoSum_correct prec ltac:(unfold prec; lia) ne eq_refl a b
   (fmtF_fmtX a Fa) (fmtF_fmtX b Fb)) as E.
 assert (S : TwoSum_sum prec ne a b = rndF (a+b)).
 { unfold TwoSum_sum, TwoSum. cbn [fst]. rewrite <- sum_round by assumption. reflexivity. }
 rewrite S in E |- *. f_equal. lra.
Qed.
Lemma em_fast_two_sum_identity h l : fmtF h -> fmtF l -> h = rndF (h+l) ->
 fast_two_sum h l = (h,l).
Proof.
 intros Fh Fl D. unfold fast_two_sum. rewrite <- D. replace (h-h) with 0 by ring.
 rewrite round_0, Rminus_0_r, round_generic by auto with typeclass_instances.
 reflexivity.
Qed.
Theorem em_add_scalar_left x yh yl : fmtF x -> fmtF yh -> fmtF yl -> yh = rndF (yh+yl) ->
 add x 0 yh yl = add_f64 yh yl x.
Proof.
 intros Fx Fh Fl D.
 pose proof (add_f64_dw yh yl x Fh Fl Fx D) as DW.
 unfold add, add_f64 in *.
 rewrite (em_two_sum_value x yh Fx Fh), (em_two_sum_value yh x Fh Fx) in *.
 rewrite (em_two_sum_value 0 yl (generic_format_0 _ _) Fl).
 rewrite Rplus_0_l.
 assert (Y : rndF yl = yl) by (apply round_generic; auto with typeclass_instances). rewrite Y.
 replace (yl-yl) with 0 by ring.
 replace (yh+x) with (x+yh) in * by ring.
 replace (yl+(x+yh-rndF (x+yh))) with (x+yh-rndF (x+yh)+yl) in * by ring.
 set (v := fast_two_sum (rndF (x+yh)) (rndF (x+yh-rndF (x+yh)+yl))) in *.
 assert (Fv : fmtF (fst v) /\ fmtF (snd v)).
 { unfold v, fast_two_sum. cbn [fst snd]. split; apply fmtF_rnd. }
 destruct v as [h l]. cbn [fst snd] in Fv. rewrite Rplus_0_l.
 assert (L : rndF l = l) by (apply round_generic; auto with typeclass_instances; tauto). rewrite L.
 apply em_fast_two_sum_identity; tauto.
Qed.
