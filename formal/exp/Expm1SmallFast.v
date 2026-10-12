(** The executable small fast path, its total error, and its rounding test. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Eft RoundingTest.
From Interval Require Import Tactic.
Require Import Expm1Tables ExpFast Expm1SmallSum Expm1SmallPoly Expm1SmallApprox Expm1SmallCertificates
 Expm1GeneralFast Expm1Series Ln1pLemmas StageGappa.
Open Scope R_scope.
Definition em_small_fast_value x := let '(h,l) := em_small_sum x in add_f64_64 h l (em_tail x).
Theorem em_small_fast_bound x : finite x -> /2^54 <= Rabs (B x) <= /32 ->
 let '(h,l) := em_small_fast_value x in
 finite h /\ finite l /\ B h = rndF (B h+B l) /\
 bpow radix2 (-900) <= Rabs (B h) < bpow radix2 1024 /\
 Rabs (B h+B l-(exp (B x)-1)) <= /2^62*Rabs (exp (B x)-1).
Proof.
 intros Fx X. pose proof (em_small_sum_ok x Fx X) as S.
 unfold em_small_fast_value. destruct (em_small_sum x) as [a b].
 destruct S as [Fa [Fb [Dw [Aa [Ab [d1 [Ed1 V1]]]]]]].
 destruct (em_tail_ok x Fx (proj2 X)) as [Ft [Vt At]].
 assert (Rx : rn (B x) = B x) by (change (rndF (B x) = B x); apply round_generic; auto with typeclass_instances; apply B_fmt).
 assert (XA : /2^54 <= Rabs (B x) <= 0.0312501) by lra.
 pose proof (em_tail_certificate (B x) Rx XA) as Et.
 pose proof (em_small_polynomial_bound (B x) (proj2 XA)) as Ep.
 pose proof (em_w_range (B x) (proj2 XA)) as W.
 set (T := B x*B x*B x*em_w (B x)) in *.
 assert (X0 : B x <> 0) by (intros Z; rewrite Z,Rabs_R0 in X; assert (0 < /2^54) by interval with (i_prec 80); lra).
 assert (T0 : T <> 0) by (unfold T; repeat apply Rmult_integral_contrapositive_currified; try exact X0; lra).
 set (et := (B (em_tail x)-T)/T).
 assert (ET : Rabs et <= /2^50) by (unfold et; rewrite Vt; exact Et).
 assert (VT : B (em_tail x) = T*(1+et)) by (unfold et; field; exact T0).
 set (al := (exp (B x)-1-B x-B x*B x/2-T)/T).
 assert (AL : Rabs al <= 518/2^63) by (apply ratio_bound; [apply Rabs_pos_lt; exact T0 | exact Ep]).
 assert (VL : exp (B x)-1 = B x+B x*B x/2+T*(1+al)) by (unfold al; field; exact T0).
 assert (XR : -/32 <= B x <= /32) by (apply Rabs_le_inv; lra).
 assert (D1 : -0.001 <= d1 <= 0.001).
 { apply Rabs_le_inv in Ed1. assert (776/2^114 <= 0.001) by interval with (i_prec 140). lra. }
 assert (TE : -0.001 <= et <= 0.001).
 { apply Rabs_le_inv in ET. assert (/2^50 <= 0.001) by interval with (i_prec 80). lra. }
 assert (N : B a+B b+B (em_tail x) <> 0).
 { rewrite V1,VT. unfold T. replace ((B x+B x*B x/2)*(1+d1)+B x*B x*B x*em_w (B x)*(1+et))
     with (B x*((1+B x/2)*(1+d1)+B x*B x*em_w (B x)*(1+et))) by field.
   apply Rmult_integral_contrapositive_currified; [exact X0 | ].
   assert (P1 : 0 < (1+B x/2)*(1+d1)) by (apply Rmult_lt_0_compat; lra).
   assert (P2 : 0 <= B x*B x*em_w (B x)*(1+et)) by (apply Rmult_le_pos; [apply Rmult_le_pos; [apply Rle_0_sqr | lra] | lra]).
   lra. }
 assert (Big : forall v, Rabs v <= 2 -> Rabs v <= bpow radix2 1018).
 { intros v Hv. apply Rle_trans with 2; [exact Hv | interval with (i_prec 80)]. }
 pose proof (add_f64_ieee a b (em_tail x) Fa Fb Ft Dw (Big (B a) ltac:(lra)) (Big (B b) Ab) (Big (B (em_tail x)) ltac:(lra))) as A.
 destruct (add_f64_64_ok 2 0 a b (em_tail x) Fa Fb Ft
   ltac:(unfold bnd; change (IZR 2*bpow radix2 0) with (2*1); lra)
   ltac:(unfold bnd; change (IZR 2*bpow radix2 0) with (2*1); lra)
   ltac:(unfold bnd; change (IZR 2*bpow radix2 0) with (2*1); lra)
   ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [_ [_ Eq]].
 pose proof (add_f64_dw (B a) (B b) (B (em_tail x)) (B_fmt a) (B_fmt b) (B_fmt _) Dw) as Dh.
 rewrite <-Eq in Dh. destruct (add_f64_64 a b (em_tail x)) as [h l]. cbn [fst snd] in Dh.
 destruct A as [Fh [Fl E2]].
 set (d2 := (B h+B l-(B a+B b+B (em_tail x)))/(B a+B b+B (em_tail x))).
 assert (ED2 : Rabs d2 <= /2^105).
 { apply Rle_trans with (1:=E2). unfold prec. interval with (i_prec 140). }
 assert (V2 : B h+B l = (B a+B b+B (em_tail x))*(1+d2)) by (unfold d2; field; exact N).
 pose proof (em_p_certificate (B x) al d1 et d2 XA AL Ed1 ET ED2) as C. cbv zeta in C. fold T in C.
 rewrite <-VL, <-V1, <-VT, <-V2 in C.
 assert (WN : exp (B x)-1 <> 0).
 { pose proof (expm1_ratio_small (B x) (proj2 XA) X0). intros Z. rewrite Z in H. unfold Rdiv in H. rewrite Rmult_0_l in H. lra. }
 assert (E : Rabs (B h+B l-(exp (B x)-1)) <= /2^62*Rabs (exp (B x)-1)).
 { replace (B h+B l-(exp (B x)-1)) with (((B h+B l-(exp (B x)-1))/(exp (B x)-1))*(exp (B x)-1)) by (field; exact WN).
   rewrite Rabs_mult. apply Rmult_le_compat_r; [apply Rabs_pos | ].
   apply Rle_trans with (1:=C). interval with (i_prec 100). }
 assert (Wr : 0.98*Rabs (B x) <= Rabs (exp (B x)-1) <= 1.02*Rabs (B x)).
 { pose proof (expm1_ratio_small (B x) (proj2 XA) X0) as G.
   replace (exp (B x)-1) with (B x*((exp (B x)-1)/B x)) by (field; exact X0).
   rewrite Rabs_mult, (Rabs_pos_eq ((exp (B x)-1)/B x)) by lra. pose proof (Rabs_pos (B x)); split; nra. }
 assert (Sb : bpow radix2 (-55) <= Rabs (B h+B l) /\ Rabs (B h+B l) <= 1).
 { pose proof (Rabs_triang_inv (B h+B l) (exp (B x)-1)) as U.
   pose proof (Rabs_triang_inv (exp (B x)-1) (B h+B l)) as L. rewrite (Rabs_minus_sym (exp (B x)-1) (B h+B l)) in L.
   assert (eps : /2^62 <= 0.001) by interval with (i_prec 100).
   assert (Ew : Rabs (B h+B l-(exp (B x)-1)) <= 0.001*Rabs (exp (B x)-1))
     by (apply Rle_trans with (1:=E); apply Rmult_le_compat_r; [apply Rabs_pos | exact eps]).
   assert (Tiny : 0 < /2^54) by interval with (i_prec 100).
   split.
   - apply Rle_trans with (0.97*(/2^54)); [interval with (i_prec 100) | ]. lra.
   - lra. }
 assert (Hlo : bpow radix2 (-900) <= Rabs (B h)).
 { rewrite Dh. apply Rle_trans with (bpow radix2 (-55)); [apply bpow_le; lia | apply em_rnd_lower; [lia | tauto]]. }
 assert (Hhi : Rabs (B h) < bpow radix2 1024).
 { rewrite Dh. apply Rle_lt_trans with 1; [apply rnd_bound; [apply (fmt_pow 0); lia | tauto] | interval]. }
 repeat split; assumption.
Qed.
Definition em_small_fast x := let '(h,l) := em_small_fast_value x in decide_with h l em_eps.
Theorem em_small_fast_ok x v : finite x -> /2^54 <= Rabs (B x) <= /32 ->
 em_small_fast x = Some v -> finite v /\ B v = rndF (exp (B x)-1).
Proof.
 intros Fx X. pose proof (em_small_fast_bound x Fx X) as F.
 unfold em_small_fast. destruct (em_small_fast_value x) as [h l].
 destruct F as [Fh [Fl [Dw [H E]]]]; intros D.
 destruct em_eps_ok as [Fe Be].
 assert (Prod : B em_eps*Rabs (B h) <= bpow radix2 1020).
 { rewrite Be. apply Rle_trans with ((/2^62*(1+bpow radix2 (-50)))*bpow radix2 1024).
   - apply Rmult_le_compat_l; [interval with (i_prec 64) | lra].
   - interval with (i_prec 128). }
 destruct (decide_with_bounded_ok h l em_eps (exp (B x)-1) (/2^62) v Fh Fl Fe H Prod Dw) as [V R].
 - split; interval with (i_prec 64).
 - rewrite Be. split; [lra | interval with (i_prec 128)].
 - rewrite Rabs_minus_sym. exact E.
 - exact D.
 - subst v. split; [exact Fh | symmetry; exact R].
Qed.
