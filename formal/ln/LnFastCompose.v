(** Normalized binary64 addition with a checked cancellation bound. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add.
From Interval Require Import Tactic.
Require Import LnFastAdd Ln1pLemmas StageGappa.
Open Scope R_scope.
Lemma lf_sum_cancellation xh xl yh yl : fmtF xh -> fmtF xl -> xh=rndF(xh+xl) ->
 fmtF yh -> fmtF yl -> yh=rndF(yh+yl) ->
 Rabs(xh+xl)+Rabs(yh+yl)<=4*Rabs(xh+xl+(yh+yl)) ->
 Rabs xh+Rabs yh<=8*Rabs(xh+yh).
Proof.
 intros Xh Xl Dx Yh Yl Dy C.
 pose proof (lf_low_bound xh xl Xh Xl Dx) as Lx.
 pose proof (lf_low_bound yh yl Yh Yl Dy) as Ly.
 pose proof (Rabs_triang_inv xh (xh+xl)) as Ax. replace (xh-(xh+xl)) with (-xl) in Ax by ring. rewrite Rabs_Ropp in Ax.
 pose proof (Rabs_triang_inv yh (yh+yl)) as Ay. replace (yh-(yh+yl)) with (-yl) in Ay by ring. rewrite Rabs_Ropp in Ay.
 assert (S : Rabs(xh+xl+(yh+yl))<=Rabs(xh+yh)+Rabs xl+Rabs yl).
 { replace (xh+xl+(yh+yl)) with ((xh+yh)+xl+yl) by ring.
   apply Rle_trans with (1:=Rabs_triang _ _). pose proof (Rabs_triang (xh+yh) xl); lra. }
 pose proof (Rabs_pos xh). pose proof (Rabs_pos yh). unfold lf_u in Lx,Ly; lra.
Qed.
Theorem lf_add_pair a b c d : finite a -> finite b -> finite c -> finite d ->
 B a=rndF(B a+B b) -> B c=rndF(B c+B d) ->
 Rabs(B a)<=bpow radix2 100 -> Rabs(B b)<=bpow radix2 100 ->
 Rabs(B c)<=bpow radix2 100 -> Rabs(B d)<=bpow radix2 100 ->
 Rabs(B a+B b)+Rabs(B c+B d)<=4*Rabs(B a+B b+(B c+B d)) ->
 let '(h,l):=add64 a b c d in
 finite h /\ finite l /\ B h=rndF(B h+B l) /\
 exists e, Rabs e<=776/2^114 /\ B h+B l=(B a+B b+(B c+B d))*(1+e).
Proof.
 intros Fa Fb Fc Fd Da Dc Aa Ab Ac Ad C.
 assert (Bd : forall v, Rabs v<=bpow radix2 100 -> bnd 1 100 v) by (intros v V; unfold bnd; lra).
 destruct (add64_ok 1 100 a b c d Fa Fb Fc Fd (Bd _ Aa) (Bd _ Ab) (Bd _ Ac) (Bd _ Ad)
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [Fh [Fl Eq]].
 pose proof (lf_sum_cancellation (B a) (B b) (B c) (B d) (B_fmt a) (B_fmt b) Da (B_fmt c) (B_fmt d) Dc C) as Ca.
 pose proof (lf_add_normalized (B a) (B b) (B c) (B d) (B_fmt a) (B_fmt b) Da (B_fmt c) (B_fmt d) Dc Ca) as Dh.
 rewrite <-Eq in Dh. destruct (add64 a b c d) as [h l]; cbn [fst snd] in *.
 repeat split; try assumption.
 destruct (Req_dec (B a+B b+(B c+B d)) 0) as [Z | N].
 - rewrite Z,Rabs_R0,Rmult_0_r in C.
   pose proof (Rabs_pos (B a+B b)). pose proof (Rabs_pos (B c+B d)).
   assert (AB : B a+B b=0) by (assert (A: Rabs(B a+B b)<=0) by lra; apply Rabs_le_inv in A; lra).
   assert (CD : B c+B d=0) by (assert (A: Rabs(B c+B d)<=0) by lra; apply Rabs_le_inv in A; lra).
   rewrite AB,round_0 in Da by exact _. rewrite CD,round_0 in Dc by exact _.
   assert (Bb : B b=0) by lra. assert (Dd : B d=0) by lra.
   rewrite Da,Bb,Dc,Dd in Eq.
   assert (AZ : add 0 0 0 0=(0,0)).
   { unfold add,two_sum,fast_two_sum. repeat (rewrite ?Rplus_0_l,?Rminus_0_l,?Ropp_0,?round_0). all: try reflexivity; exact _. }
   rewrite AZ in Eq. injection Eq as Zh Zl. exists 0. rewrite Z,Zh,Zl,Rabs_R0. split; [interval with (i_prec 140) | ring].
 - pose proof (add_bound (B a) (B b) (B c) (B d) (B_fmt a) (B_fmt b) Da (B_fmt c) (B_fmt d) Dc N) as E.
   rewrite <-Eq in E.
   exists ((B h+B l-(B a+B b+(B c+B d)))/(B a+B b+(B c+B d))). split.
   + apply Rle_trans with (1:=E). unfold prec; interval with (i_prec 140).
   + field; exact N.
Qed.

Lemma lf_perturbed_sum a b A B T eps : A+B=T -> 0<=eps<=/100 ->
 Rabs A+Rabs B<=7/2*Rabs T ->
 Rabs(a-A)+Rabs(b-B)<=eps*Rabs T ->
 Rabs a+Rabs b<=4*Rabs(a+b) /\ Rabs(a+b-T)<=eps*Rabs T.
Proof.
 intros Sum Ep Size Err.
 assert (D : Rabs(a+b-T)<=eps*Rabs T).
 { replace (a+b-T) with ((a-A)+(b-B)) by lra. apply Rle_trans with (1:=Rabs_triang _ _); exact Err. }
 pose proof (Rabs_triang_inv a A). pose proof (Rabs_triang_inv b B).
 pose proof (Rabs_triang_inv T (a+b)). rewrite (Rabs_minus_sym T (a+b)) in H1.
 pose proof (Rabs_pos T). split; [nra | exact D].
Qed.
Lemma lf_rounded_sum S T v eps d : 0<=eps -> Rabs(S-T)<=eps*Rabs T ->
 Rabs d<=776/2^114 -> v=S*(1+d) ->
 Rabs(v-T)<=(eps+(776/2^114)*(1+eps))*Rabs T.
Proof.
 intros Ep E D V. rewrite V. replace (S*(1+d)-T) with ((S-T)+S*d) by ring.
 apply Rle_trans with (1:=Rabs_triang _ _). rewrite Rabs_mult.
 pose proof (Rabs_triang_inv S T). pose proof (Rabs_pos S). pose proof (Rabs_pos T).
 assert (P : 0<=776/2^114) by interval with (i_prec 140). nra.
Qed.
