(** Normalization of the shared additions when cancellation is bounded.
    Every rounding is a sum of binary64 values, so gradual underflow is exact. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core Plus_error Mult_error Relative.
From Double Require Import DWPlus F2Sum F2SumFLX.
From Binary64 Require Import Binary64Add.
Open Scope R_scope.
Definition lf_u : R := /9007199254740992.
Lemma lf_sum_error a b : fmtF a -> fmtF b ->
 Rabs (rndF(a+b)-(a+b)) <= lf_u*Rabs(a+b).
Proof.
 intros A B. rewrite sum_round by assumption.
 pose proof (relative_error_N_FLX radix2 prec ltac:(unfold prec; lia) ne (a+b)) as E.
 replace (/2*bpow radix2 (-prec+1)) with lf_u in E by (unfold prec,lf_u; simpl; lra). exact E.
Qed.
Lemma lf_low_bound h l : fmtF h -> fmtF l -> h=rndF(h+l) -> Rabs l <= 2*lf_u*Rabs h.
Proof.
 intros H L D. pose proof (lf_sum_error h l H L) as E. rewrite <-D in E.
 replace (h-(h+l)) with (-l) in E by ring. rewrite Rabs_Ropp in E.
 pose proof (Rabs_triang h l). pose proof (Rabs_pos h). unfold lf_u in *. lra.
Qed.
Lemma lf_two_sum a b : fmtF a -> fmtF b ->
 let '(h,l):=two_sum a b in fmtF h /\ fmtF l /\ h=rndF(a+b) /\ h+l=a+b.
Proof.
 intros A B. rewrite two_sum_eq by assumption.
 destruct (two_sum_fmt a b A B) as [H L]. repeat split; try assumption.
 - rewrite TwoSum_sumE, sum_round by assumption. reflexivity.
 - rewrite (@TwoSum_correct prec ltac:(unfold prec; lia) ne eq_refl a b (fmtF_fmtX _ A) (fmtF_fmtX _ B)). ring.
Qed.
Lemma lf_fast_sum a b : fmtF a -> fmtF b -> Rabs b <= Rabs a ->
 let '(h,l):=fast_two_sum a b in fmtF h /\ fmtF l /\ h=rndF(a+b) /\ h+l=a+b.
Proof.
 intros A B Ab.
 pose proof (@F2Sum.F2Sum_correct_abs prec ltac:(unfold prec; lia) ne
  ltac:(intros; apply round_NE_opp) ltac:(simpl; lia) a b (fmtF_fmtX _ A) (fmtF_fmtX _ B) Ab) as C.
 destruct (fast_two_sum_fmt a b A B) as [H L].
 rewrite fast_two_sum_eq by assumption. destruct (F2Sum.Fast2Sum prec ne a b) as [h l] eqn:E.
 cbn [fst snd] in H,L. unfold F2Sum.Fast2Sum_correct in C. rewrite E in C. cbn [fst snd] in C.
 repeat split; try assumption.
 - unfold F2Sum.Fast2Sum,F2SumFLX.Fast2Sum in E. injection E as Eh El.
   rewrite <-Eh, sum_round by assumption. reflexivity.
 - lra.
Qed.
Theorem lf_add_normalized xh xl yh yl :
 fmtF xh -> fmtF xl -> xh=rndF(xh+xl) ->
 fmtF yh -> fmtF yl -> yh=rndF(yh+yl) ->
 Rabs xh+Rabs yh <= 8*Rabs(xh+yh) ->
 let '(h,l):=add xh xl yh yl in h=rndF(h+l).
Proof.
 intros Xh Xl Dx Yh Yl Dy C.
 pose proof (lf_low_bound xh xl Xh Xl Dx) as Lx.
 pose proof (lf_low_bound yh yl Yh Yl Dy) as Ly.
 pose proof (lf_two_sum xh yh Xh Yh) as S.
 pose proof (lf_two_sum xl yl Xl Yl) as T.
 unfold add. destruct (two_sum xh yh) as [sh sl]. destruct (two_sum xl yl) as [th tl].
 destruct S as [Sh [Sl [Vs Es]]]. destruct T as [Th [Tl [Vt Et]]].
 pose proof (lf_sum_error xh yh Xh Yh) as Eh. rewrite <-Vs in Eh.
 pose proof (lf_sum_error xl yl Xl Yl) as El. rewrite <-Vt in El.
 assert (Asl : Rabs sl <= lf_u*Rabs(xh+yh)).
 { replace sl with (-(sh-(xh+yh))) by lra. rewrite Rabs_Ropp. exact Eh. }
 assert (Atl : Rabs tl <= lf_u*Rabs(xl+yl)).
 { replace tl with (-(th-(xl+yl))) by lra. rewrite Rabs_Ropp. exact El. }
 pose proof (Rabs_triang xl yl) as L.
 pose proof (Rabs_triang_inv th (xl+yl)) as Tbound.
 pose proof (Rabs_triang_inv sh (xh+yh)) as Sbound.
 pose proof (Rabs_triang_inv (xh+yh) sh) as Sbelow. rewrite Rabs_minus_sym in Sbelow.
 set (s:=Rabs(xh+yh)) in *. assert (Ps : 0<=s) by apply Rabs_pos.
 assert (At : Rabs th <= 17*lf_u*s) by (unfold lf_u in *; lra).
 assert (Ac : Rabs (rndF(sl+th)) <= 19*lf_u*s).
 { pose proof (lf_sum_error sl th Sl Th). pose proof (Rabs_triang sl th).
   pose proof (Rabs_triang_inv (rndF(sl+th)) (sl+th)). unfold lf_u in *; lra. }
 assert (Cc : Rabs (rndF(sl+th)) <= Rabs sh) by (unfold lf_u in *; lra).
 pose proof (lf_fast_sum sh (rndF(sl+th)) Sh (fmtF_rnd _) Cc) as V.
 pose proof (lf_sum_error sh (rndF(sl+th)) Sh (fmtF_rnd _)) as Ev.
 destruct (fast_two_sum sh (rndF(sl+th))) as [vh vl]. destruct V as [Vh [Vl [Vv Vsum]]].
 rewrite <-Vv in Ev.
 assert (Avl : Rabs vl <= lf_u*Rabs(sh+rndF(sl+th))).
 { replace vl with (-(vh-(sh+rndF(sl+th)))) by lra. rewrite Rabs_Ropp. exact Ev. }
 pose proof (Rabs_triang sh (rndF(sl+th))) as Sc.
 pose proof (Rabs_triang_inv sh (sh+rndF(sl+th))) as Sc0.
 replace (sh-(sh+rndF(sl+th))) with (-rndF(sl+th)) in Sc0 by ring. rewrite Rabs_Ropp in Sc0.
 pose proof (Rabs_triang_inv (sh+rndF(sl+th)) vh) as Vbelow. rewrite Rabs_minus_sym in Vbelow.
 assert (Av : s/2 <= Rabs vh) by (unfold lf_u in *; lra).
 assert (Avl' : Rabs vl <= 2*lf_u*s) by (unfold lf_u in *; lra).
 assert (Aw : Rabs (rndF(tl+vl)) <= Rabs vh).
 { pose proof (lf_sum_error tl vl Tl Vl). pose proof (Rabs_triang tl vl).
   pose proof (Rabs_triang_inv (rndF(tl+vl)) (tl+vl)). unfold lf_u in *; lra. }
 apply fast_two_sum_dw; auto using fmtF_rnd.
Qed.
