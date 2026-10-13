(** The two double-word additions in the small fast path. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add IEEE64Eft RoundingTest.
From Interval Require Import Tactic.
Require Import ExpFast Expm1SmallSquare Expm1SmallAdd Ln1pLemmas StageGappa.
Open Scope R_scope.
Definition em_small_sum x := let '(h,l) := em_half_square x in add64 x c_zero h l.
Theorem em_small_sum_ok x : finite x -> /2^54 <= Rabs (B x) <= /32 ->
 let '(h,l) := em_small_sum x in
 finite h /\ finite l /\ B h = rndF (B h+B l) /\ Rabs (B h) <= 1 /\ Rabs (B l) <= 2 /\
 exists d1, Rabs d1 <= 776/2^114 /\ B h+B l = (B x+B x*B x/2)*(1+d1).
Proof.
 intros Fx X. pose proof (em_half_square_ok x Fx X) as S.
 unfold em_small_sum. destruct (em_half_square x) as [a b]. destruct S as [Fa [Fb [D [V [Aa Ab]]]]].
 assert (Bx : bnd 1 0 (B x)) by (unfold bnd; change (IZR 1*bpow radix2 0) with (1*1); lra).
 assert (Ba : bnd 1 0 (B a)) by (unfold bnd; change (IZR 1*bpow radix2 0) with (1*1); lra).
 assert (Bb : bnd 1 0 (B b)) by (unfold bnd; change (IZR 1*bpow radix2 0) with (1*1); lra).
 assert (Bz : bnd 1 0 (B c_zero)) by (rewrite c_zero_val; unfold bnd; rewrite Rabs_R0; simpl; lra).
 destruct (add64_ok 1 0 x c_zero a b Fx c_zero_finite Fa Fb Bx Bz Ba Bb ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [Fh [Fl Eq]].
 rewrite c_zero_val, (em_add_scalar_left (B x) (B a) (B b) (B_fmt x) (B_fmt a) (B_fmt b) D) in Eq.
 pose proof (add_f64_bound (B a) (B b) (B x) (B_fmt a) (B_fmt b) (B_fmt x) D) as E.
 pose proof (add_f64_dw (B a) (B b) (B x) (B_fmt a) (B_fmt b) (B_fmt x) D) as Dw.
 rewrite <-Eq in E,Dw. destruct (add64 x c_zero a b) as [h l]. cbn [fst snd] in *.
 rewrite V in E. set (d1 := (B h+B l-(B x+B x*B x/2))/(B x+B x*B x/2)).
 assert (Ed : Rabs d1 <= 776/2^114).
 { unfold d1. replace (B x+B x*B x/2) with (B x*B x/2+B x) by ring.
   apply Rle_trans with (1:=E). unfold prec. interval with (i_prec 140). }
 assert (X0 : B x <> 0) by (intros Z; rewrite Z,Rabs_R0 in X; assert (0 < /2^54) by interval with (i_prec 80); lra).
 assert (XR : -/32 <= B x <= /32) by (apply Rabs_le_inv; lra).
 assert (N : B x+B x*B x/2 <> 0).
 { replace (B x+B x*B x/2) with (B x*(1+B x/2)) by field.
   apply Rmult_integral_contrapositive_currified; [exact X0 | lra]. }
 assert (Id : B h+B l = (B x+B x*B x/2)*(1+d1)) by (unfold d1; field; intros Z; apply N; nra).
 assert (Small : Rabs (B h+B l) <= 1).
 { rewrite Id,Rabs_mult. assert (U : Rabs (B x+B x*B x/2) <= /16).
   { apply Rle_trans with (1:=Rabs_triang _ _). unfold Rdiv; rewrite !Rabs_mult, (Rabs_pos_eq (/2)) by lra. nra. }
   assert (Db : Rabs (1+d1) <= 2).
   { apply Rle_trans with (1:=Rabs_triang _ _). rewrite Rabs_R1.
     apply Rle_trans with (1+776/2^114); [lra | interval with (i_prec 140)]. }
   pose proof (Rabs_pos (B x+B x*B x/2)). pose proof (Rabs_pos (1+d1)). nra. }
 assert (H : Rabs (B h) <= 1) by (rewrite Dw; apply rnd_bound; [apply (fmt_pow 0); lia | exact Small]).
 assert (L : Rabs (B l) <= 2).
 { replace (B l) with ((B h+B l)-B h) by ring. apply Rle_trans with (1:=Rabs_triang _ _). rewrite Rabs_Ropp. lra. }
 repeat split; try assumption. exists d1. split; assumption.
Qed.
