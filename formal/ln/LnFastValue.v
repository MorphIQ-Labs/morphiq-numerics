(** Full double-word ln reconstruction, including exponent cancellation. *)
From Coq Require Import Reals ZArith Lia Lra Psatz.
From Flocq Require Import Core.
From Binary64 Require Import Binary64Add IEEE64 IEEE64Add Grid.
From Interval Require Import Tactic.
Require Import LnTables LnTableCheck LnReduction LnAccurate LnFastY LnFastLn2 LnFastCompose Ln1pLemmas.
Open Scope R_scope.
Definition lf_value e y i := let '(a,b):=lf_e_ln2 e in let '(c,d):=lf_ln_y y i in add64 a b c d.
Theorem lf_value_ok e y i : (Z.abs e<=1074)%Z -> (i<128)%nat -> finite y ->
 ln_lo i<=B y<ln_hi i -> on_grid (-53) (B y) ->
 let '(h,l):=lf_value e y i in finite h /\ finite l /\ B h=rndF(B h+B l) /\
 Rabs(B h)<=1024 /\ Rabs(B l)<=2048 /\
 Rabs(B h+B l-(IZR e*ln 2+ln(B y)))<=/2^64*Rabs(IZR e*ln 2+ln(B y)).
Proof.
 intros E I Fy Y Gy.
 destruct (ratios_ok i (B y) I ltac:(assert (0</2^52) by interval with (i_prec 80); lra)) as [Py [Pr [RB RC]]].
 set (v:=IZR e*ln 2+ln(B y)).
 assert (Rat : Rabs(IZR e*ln 2)<=k1c*Rabs v /\ Rabs(ln(B y))<=(k2c+k3c)*Rabs v).
 { destruct (Z.eq_dec e 0) as [Z | NZ].
   - subst e. unfold v,k1c,k2c,k3c. cbn [IZR]. rewrite Rmult_0_l,Rplus_0_l,Rabs_R0.
     pose proof (Rabs_pos (ln(B y))); split; lra.
   - specialize (RC e NZ). cbv zeta in RC. fold v in RC. destruct RC as [R1 [R2 R3]]. split; [exact R3 | ].
     replace (ln(B y)) with (ln(B y*B (ln_r i))-ln(B (ln_r i))) by (rewrite ln_mult by lra; ring).
     apply Rle_trans with (1:=Rabs_triang _ _); rewrite Rabs_Ropp; nra. }
 destruct Rat as [R1 R2].
 pose proof (lf_e_ln2_ok e E) as EP. pose proof (lf_ln_y_ok y i I Fy Y Gy) as YP.
 unfold lf_value. destruct (lf_e_ln2 e) as [a b]. destruct (lf_ln_y y i) as [c d].
 destruct EP as [Fa [Fb [Da [Aa [Ab Ea]]]]]. destruct YP as [Fc [Fd [Dc [Ac [Ad Ec]]]]].
 set (eps:=(745/2^106)*k1c+(7/2^67)*(k2c+k3c)).
 assert (Ep : 0<=eps<=/100) by (unfold eps,k1c,k2c,k3c; split; interval with (i_prec 180)).
 assert (Err : Rabs(B a+B b-IZR e*ln 2)+Rabs(B c+B d-ln(B y))<=eps*Rabs v).
 { assert (0<=745/2^106) by interval with (i_prec 180). assert (0<=7/2^67) by interval with (i_prec 100). unfold eps; nra. }
 destruct (lf_perturbed_sum (B a+B b) (B c+B d) (IZR e*ln 2) (ln(B y)) v eps eq_refl Ep
  ltac:(unfold k1c,k2c,k3c in R1,R2; pose proof (Rabs_pos v); lra) Err) as [C ES].
 assert (Big : forall v, Rabs v<=4096 -> Rabs v<=bpow radix2 100).
 { intros t T; apply Rle_trans with 4096; [exact T | interval with (i_prec 100)]. }
 pose proof (lf_add_pair a b c d Fa Fb Fc Fd Da Dc (Big (B a) ltac:(lra)) (Big (B b) Ab)
  (Big (B c) ltac:(lra)) (Big (B d) ltac:(lra)) C) as A.
 destruct (add64 a b c d) as [h l]. destruct A as [Fh [Fl [Dw [er [Er Vr]]]]].
 pose proof (lf_rounded_sum _ _ _ eps er (proj1 Ep) ES Er Vr) as Bnd.
 assert (Bound : Rabs(B h+B l-v)<=/2^64*Rabs v).
 { apply Rle_trans with (1:=Bnd). apply Rmult_le_compat_r; [apply Rabs_pos | unfold eps,k1c,k2c,k3c; interval with (i_prec 200)]. }
 assert (Av : Rabs v<=800).
 { unfold v. apply Rle_trans with (1:=Rabs_triang _ _). rewrite Rabs_mult.
   assert (Ae : Rabs(IZR e)<=1074) by (rewrite <-abs_IZR; apply IZR_le; exact E).
   destruct (ln_range i I) as [Lo [Hi _]]. assert (Yb : 0.7<=B y<=1.42) by lra.
   assert (Rabs(ln(B y))<=/2) by interval with (i_prec 100).
   assert (Rabs(ln 2)<=0.7) by interval with (i_prec 100). pose proof (Rabs_pos (IZR e)); nra. }
 assert (Small : Rabs(B h+B l)<=1024).
 { pose proof (Rabs_triang_inv (B h+B l) v). assert (/2^64<=/100) by interval with (i_prec 100). pose proof (Rabs_pos v); nra. }
 assert (H : Rabs(B h)<=1024) by (rewrite Dw; apply rnd_bound; [apply (fmt_pow 10); lia | exact Small]).
 assert (L : Rabs(B l)<=2048).
 { replace (B l) with ((B h+B l)-B h) by ring. apply Rle_trans with (1:=Rabs_triang _ _); rewrite Rabs_Ropp; lra. }
 repeat split; assumption.
Qed.
Definition lf_ln_fast_value x := let '(e,i,y,r):=reduce x in lf_value e y i.
Theorem lf_ln_fast_value_ok x : finite x -> 0<B x ->
 let '(h,l):=lf_ln_fast_value x in finite h /\ finite l /\ B h=rndF(B h+B l) /\
 Rabs(B h)<=1024 /\ Rabs(B l)<=2048 /\ Rabs(B h+B l-ln(B x))<=/2^64*Rabs(ln(B x)).
Proof.
 intros Fx Px. pose proof (reduce_ok x Fx Px) as R. unfold lf_ln_fast_value.
 destruct (reduce x) as [[[e i] y] r]. destruct R as [I [R [Fy [Y [Gy [V E]]]]]].
 pose proof (lf_value_ok e y i ltac:(lia) I Fy Y Gy) as F.
 assert (L : ln(B x)=IZR e*ln 2+ln(B y)).
 { rewrite V. apply ln_pow2. destruct (ln_range i I) as [Lo [Hi _]]; lra. }
 rewrite <-L in F. exact F.
Qed.
